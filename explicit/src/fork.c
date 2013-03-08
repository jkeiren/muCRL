/* $Id: fork.c,v 1.10 2007/06/29 13:30:57 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#define FORK_C

#ifdef LINUX
#include <unistd.h>
#include <stdio.h>
#include <limits.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/select.h>
#include <sys/types.h> 
#include "param0.h"
#include "utl.h"
#include "mgr.h"
#include "fifo.h"
#include "vector_db.h"
#include "tree_db.h"
#include "mgr_fork.h"
#include "inst_fork.h"


#define DBSIZE 80
#define MAXFDS 256

typedef struct {
   file_t src, act, dest;
   }  transfile_t;
   
static transfile_t *transfile = NULL;
static elm_t dest_pair[2], src_pair[2], act_pair[2];

static int seg,  line = 0;
static unsigned int nseg, explored =0, naccept = 0;
   
static env_t *env;
static char **dest, **host, *mcrlArgs, *pattern, *reject,
   *sselect, *priority, *deadlock_action;
   

static vdb_t srcvdb = NULL, vdb;

static trdb_t trdb = NULL;

static char fulldirname[100];

static info_t *info = NULL;

typedef struct {
   elm_t *x;
   elm_t idx;
   elm_t act;
   elm_t *dest;
   } trans_t;
   
     
typedef struct {
   elm_t idx;
   int level;
   } adbval_t; 

static file_t inst[2], mgr[2], *inputs;
static ad_t *ad;
static report_t report;
static visited_t *visited;
static unexplored_t *unexplored;
static elm_t deadlock_state[]={0, DEADLOCK};

static void AddExtraOK(int code) {  
   if (code>=0) return; 
   errormsg("Fork %d:VDBaddExtra out of memory: code = %d", seg, code); 
   } 
   
static idx_t PutOK(idx_t idx) {   
  if (idx>=0) return idx;
  else errormsg("Fork %d: VDBput out of memory: code = %d", seg, idx);
  return -1;
  }
         
static void Mgr(char *mgrhost, int mgrport, file_t *mgr) {
    int sd = clientSocket(mgrhost, mgrport,0);
    if (sd<0) 
        errormsg("Cannot open client socket (%s, %d)", mgrhost, mgrport);
    mgr[0] =  fdopen(sd,"r"); mgr[1] = fdopen(sd,"w");
    C_fork2mgr_seg(mgr[1], &seg);
    C_mgr2fork_env(mgr[0], env);
    dest = (char**) calloc(nseg, sizeof(char*));
    C_mgr2fork_dest(mgr[0], dest, nseg);
    host = (char**) calloc(nseg, sizeof(char*));
    C_mgr2fork_dest(mgr[0], host, nseg);
    C_mgr2fork_string(mgr[0], &mcrlArgs); 
    C_mgr2fork_string(mgr[0], &pattern);
    C_mgr2fork_string(mgr[0], &reject);
    C_mgr2fork_string(mgr[0], &sselect);
     C_mgr2fork_string(mgr[0], &priority);
    C_mgr2fork_string(mgr[0], &deadlock_action);
    }

static void WriteEndLevelMarker() {  
   int i;
   static elm_t endl[] = {ENDLEVELMARKER, 0};
   for (i=0;i<nseg;i++) {
     writeBinary(transfile[i].src, endl, 2);
     writeBinary(transfile[i].act, endl, 2);
     writeBinary(transfile[i].dest, endl, 2);
     }
   } 
   
static void WriteTransition(int l, elm_t *src, elm_t *act, elm_t *dest) {  
   if (writeBinary(transfile[l].src, src, 2)<0) 
                                       errormsg("writeBinary src");
   if (writeBinary(transfile[l].act, act, 2)<0)
                                       errormsg("writeBinary act");
   if (writeBinary(transfile[l].dest, dest, 2)<0)
                                       errormsg("writeBinary dest");
   }
   
static void RestoreOpen1(transfile_t *t, char *mode) {
    int j;
    for (j=0;j<nseg;j++) {
       t[j].src = UTLopen(dest[j], mode, "/src/stepper.%d", seg);
       // t[j].src = UTLopen(env->dir, mode, "/src/stepper.%d", j);
       t[j].act = UTLopen(env->dir, mode, "/act/stepper.%d", j);
       t[j].dest = UTLopen(env->dir, mode, "/dest/stepper.%d", j);
       }
    }

static void RestoreOpen2(transfile_t *t, char *mode) {
    int j;
    for (j=0;j<nseg;j++) {
       t[j].src = UTLopen(env->dir, mode, "/src/stepper.%d", j);
       t[j].act = UTLopen(dest[j], mode, "/act/stepper.%d", seg);
       t[j].dest = UTLopen(dest[j], mode, "/dest/stepper.%d", seg);
       rewind(t[j].src);
       }
    }
    
static void RestoreClose2(transfile_t *t) {
    int j;
    for (j=0;j<nseg;j++) {
       fclose(t[j].src); 
       fclose(t[j].act); 
       fclose(t[j].dest); 
       }
    }
    
static void endlevel(int explored, int transitions) {
    unexplored->src[0] = explored;
    /* fprintf(stderr,"%d %d: Fork explored endlevel %d\n", seg, 
                  report.level, explored); */
    unexplored->src[1] = transitions;
    unexplored->c.idx = ENDLEVELMARKER;
    // fprintf(stderr,"End Level %d\n", transitions);
    }
         
static void DumpFiles(char *dir,  file_t *vdbf, char *mode) {
    vdbf[0] = UTLopen(dir, mode, "/vdb/keys");
    vdbf[1] = UTLopen(dir, mode, "/vdb/vals");
    } 

static void SendReport() {
	strcpy(report.hostname, env->host);
	C_fork2mgr_report(mgr[1], &report);
        fflush(mgr[1]);
    } 
          
static void SendVisitedToMgr(file_t mgr, vdb_t vdb) {
    int tag = CLIENT_VISITED;
    C_fork2mgr_segtag(mgr, &seg, &tag);
    ad->visited = VDBgetCount(vdb);
    if (trdb) ad->closedvByteSize = TRDBgetByteSize(trdb);
    ad->closedByteSize = VDBgetByteSize(vdb);
    C_fork2mgr_ad(mgr, ad);
    // fprintf(stderr,"SendVisited To Manager seg = %d\n", seg);
    }
    
static void Maccept(int s, file_t *sockets, int *segments, vdb_t vdb) {
    int client = Accept(Fileno(sockets[0])), segment, tag;
    sockets[s] = fdopen(client,"r");
    C_inst2fork_seg(sockets[s], &segment);
    if (segment == seg) {
       inst[0] = sockets[s];
       inst[1] = fdopen(client,"w");
       C_fork2inst_env(inst[1], env);
       C_fork2inst_dest(inst[1], dest, nseg);
       C_fork2inst_dest(inst[1], host, nseg);
       C_fork2inst_string(inst[1], &mcrlArgs);
       C_fork2inst_string(inst[1], &pattern);
       C_fork2inst_string(inst[1], &reject);
       C_fork2inst_string(inst[1], &sselect);
       C_fork2inst_string(inst[1], &priority);
       C_fork2inst_string(inst[1], &deadlock_action);
       C_inst2fork_tag(inst[0], &tag);
       SendReport();
       }
    segments[s] = segment;
    inputs[segment]=sockets[s];
    // fprintf(stderr,"Exit Maccepts %d\n", seg);
    }
    
static int PutFifo(int from, visited_t *visited, vdb_t vdb, fifo_t output) {
    vdbval_t vdbval;  
    int new;
    elm_t *elm = trdb?(visited->dest[1]==DEADLOCK?deadlock_state:
                 TRDBput(trdb, visited->dest)):visited->dest;
    idx_t idx = PutOK(VDBput(vdb, elm , &new));
    if (transfile) {
        if (env->K==2 && env->old==1) {
          dest_pair[0] = visited->dest[0]; dest_pair[1] = visited->dest[1];
          src_pair[0] = visited->c.src[0]; src_pair[1] = visited->c.src[1];
        } else {
          dest_pair[1] = idx; src_pair[0] = from; src_pair[1]=visited->c.idx;
          }
        act_pair[0] = visited->c.act; act_pair[1] = 0;
        WriteTransition(from, src_pair, act_pair, dest_pair);
	}
    if (new) {
         // elm_t *v = TRDBget(trdb, elm);
         // fprintf(stderr,"[%d %d]\n", elm[0], elm[1]);
         vdbval.seg = from;vdbval.idx=visited->c.idx;
         vdbval.act = visited->c.act;
         /* fprintf(stderr,"Store (%d %d %d)\n", vdbval.seg, vdbval.idx,
         vdbval.act); */
         AddExtraOK(VDBaddExtra(vdb, &vdbval));  
	 memcpy((char*) &(unexplored->c)+sizeof(u_context_t), elm,
         (trdb?2:env->K)*sizeof(elm_t));
         unexplored->c.idx = idx;unexplored->c.w = visited->c.w;
         ad->var[visited->c.w].f++;
         if (visited->c.w>ad->max) ad->max = visited->c.w;
         if (visited->c.w<ad->min) ad->min = visited->c.w;
         FIFOput(output, &(unexplored->c));
	 }
    else if (visited->c.forceParent
      && idx>= explored) { 
         vdbval.seg = from;vdbval.idx=visited->c.idx;
         vdbval.act = visited->c.act;
         VDBputExtra(vdb, idx, &vdbval);
         }
    return new;
    }
 
 static void PutDeadlock(vdb_t vdb) {   
    vdbval_t vdbval = {UNDEF, UNDEF, UNDEF};
    PutOK(VDBput(vdb, deadlock_state, NULL)); 
    AddExtraOK(VDBaddExtra(vdb,  &vdbval));
    }

static void Synchronize() {
     int tag = CLIENT_SYNC;
     C_fork2mgr_segtag(mgr[1],  &seg, &tag);
     fgetc(mgr[0]);
     }
      
static void FirstState(fifo_t output,   visited_t *visited) {
    vdbval_t vdbval = {UNDEF, UNDEF, UNDEF};
    PutDeadlock(vdb);
    if (visited->dest[0]!=UNDEF) {
       int new;
       elm_t *elm = trdb?TRDBput(trdb, visited->dest):visited->dest;
       idx_t idx = VDBput(vdb, elm , &new);
       // elm_t *v = TRDBget(trdb, elm);
       // fprintf(stderr,"[%d %d]\n", elm[0], elm[1]);
       if (transfile) {
           if (env->K==2 && env->old) {
             dest_pair[0] = visited->dest[0];dest_pair[1] = visited->dest[1];
             } else dest_pair[1] = idx;
           src_pair[0] = UNDEF; src_pair[1]=UNDEF;
           act_pair[0] = UNDEF; act_pair[1] = UNDEF;
           WriteTransition(seg, src_pair, act_pair, dest_pair);
	   }
       if (new) {
          VDBaddExtra(vdb, &vdbval);
          ad->var[visited->c.w].f++;
          if (visited->c.w>ad->max) ad->max = visited->c.w;
          if (visited->c.w<ad->min) ad->min = visited->c.w;
          unexplored->c.idx = idx;
          unexplored->c.w = visited->c.w;
          memcpy((char*) &(unexplored->c)+sizeof(u_context_t), elm,
          (trdb?2:env->K)*sizeof(elm_t));
          FIFOput(output, &(unexplored->c));
          } 

       }
    report.level++;
    endlevel(0,0);
    FIFOput(output, &(unexplored->c));
    }
    
static int ReadTransition(trans_t *t, transfile_t *tf) {
    if (!readBinary(tf->src, unexplored->src, env->K)) return 0;
    t->x = unexplored->src;
    readBinary(tf->act, visited->dest, env->K);
    t->idx = unexplored->src[1]; t->act = unexplored->src[0];
    readBinary(tf->dest, visited->dest, env->K);
    t->dest = visited->dest;
    return 1;
    }
   
static int SelectTheExploredStates(vdb_t vdb, transfile_t *tf, int minlevels) {
    int width = getRecordSize();
    long ofs, level = 0;
// fprintf(stderr, "Begin of Select ExploredStates %d n = %d ofs = %d\n", 
// seg, n, ofs/width);   
    for (ofs=0;level<minlevels && readBinary(tf->src, unexplored->src, env->K)&&
         (unexplored->src[0]<0 
     || VDBgetIdx(vdb, unexplored->src)>=0
//   || unexplored->src[1]<VDBgetCount(vdb)
         );
         ofs+=width) {
         if (unexplored->src[0]==-1) level++;
         }
    rewind(tf->src);rewind(tf->act); rewind(tf->dest);
    Ftruncate(tf->src, ofs);
    Ftruncate(tf->act, ofs);
    Ftruncate(tf->dest, ofs);
// fprintf(stderr, "End of Select ExploredStates %d ofs = %d\n", seg, ofs/width);
    return level;
    }

static void closeTransfiles(transfile_t *tf) {    
    fclose(tf->src);fclose(tf->act);fclose(tf->dest);  
    }

static int minLevels(int *levels) {
    int i, m = INT_MAX;
    for (i=0;i<nseg;i++)
    if (levels[i]<m) m = levels[i]; 
    return m;
    }
               
static int RestoreStates(fifo_t output, fifo_t frek, vdb_t vdb) {
    transfile_t *transfile = calloc(nseg, sizeof(transfile_t)); 
    int eof = 0, transitions = 0, j, explored = 0, 
    transitions0 = transitions, explored0 = explored;
    fifo_t nextlevel = FIFOcreateMemo(100, sizeof(u_context_t)+env->K*sizeof(elm_t), NULL, NULL);
    vdbval_t vdbval;trans_t trans;
    // elm_t elm[2];
    int *levels = malloc(sizeof(int)*nseg), minlevels = -1;
    // elm[0] = elm[1] = -1;
    RestoreOpen2(transfile, "a+");
    fprintf(stdout,"Segment %d #levels:", seg);
    for (j=0;j<nseg;j++) {
        levels[j] = SelectTheExploredStates(vdb, transfile+j, INT_MAX);
        fprintf(stdout, "%d ", levels[j]);
        }   
    minlevels = minLevels(levels);
    fprintf(stdout,"min = %d", minlevels);
    fprintf(stdout,"tl: %d", seg);
    for (j=0;j<nseg;j++) 
    if (levels[j]>minlevels) {
        levels[j] = SelectTheExploredStates(vdb, transfile+j, minlevels);
        fprintf(stdout, "%d=%d ", j, levels[j]);
        }
    fprintf(stdout,"\n");
    RestoreClose2(transfile);
    if (minlevels==0) return 0;
    Synchronize();
    RestoreOpen1(transfile, "r");
    int eofbit = 0;
    do {
      /* fprintf(stderr, "Begin Restore States %d j = %d cnt = %d\n", seg, j,
      FIFOgetCount(nextlevel)); */
      FIFOget(frek, &explored);
      if (report.level+1<minlevels) memset(ad->var, 0, env->spectrum*sizeof(weight_t));
      for (eof = 0, j=0;j<nseg;j++) {
         int new0 = 0;
         eofbit = 0;
         do {
            if (!ReadTransition(&trans, transfile+j)) {
               eof++; eofbit = 1; break;
               }
            if (trans.dest[0]!=ENDLEVELMARKER) {
               int new;
               PutOK(VDBput(vdb, trans.dest, &new));
               if (new) {
                  new0 = new;
	          vdbval.seg = j; vdbval.idx=trans.idx; vdbval.act=trans.act;
	          AddExtraOK(VDBaddExtra(vdb, &vdbval));
                  /* if (new) fprintf(stderr,"Level: %d seg: %d (%d %d)\n",
                  report.level, seg, trans.dest[0], trans.dest[1]); */
                  }
               if (!new0  || report.level+1>=minlevels) {
                  if (new) {
	             unexplored->c.idx = trans.idx;
	             memcpy((char*) &(unexplored->c)+sizeof(u_context_t),
                     trans.dest, env->K*sizeof(elm_t));
                     FIFOput(nextlevel, &(unexplored->c));
                     ad->var[0].f++;
                     if (0>ad->max) ad->max = 0;
                     if (0<ad->min) ad->min = 0;
                     /* fprintf(stderr,"FIFOput seg = %d level = %d (%d %d)\n", seg, 
                     level, unexplored->src[0], unexplored->src[1]); */
                     }
                  transitions++;
                  }  
               }
           } while (trans.dest[0]!=ENDLEVELMARKER); 
           // fprintf(stderr, "End Restore States %d j = %d transitions = %d\n", seg, j, transitions); 
         }
       /* fprintf(stderr,"%d: explored = %d (%d)\n", 
       seg, explored, FIFOgetCount(frek)); */
       endlevel(explored-explored0,transitions-transitions0);
       FIFOput(output, &(unexplored->c));
       line++;
       transitions0 = transitions;explored0 = explored;
       while (FIFOget(nextlevel, &(unexplored->c))>=0) {
           FIFOput(output, &(unexplored->c)); 
           if (!eofbit) line++;
           } 
       report.level++;      
      } while (eof<nseg);  
      for (j=0;j<nseg;j++) closeTransfiles(transfile+j);
      fprintf(stdout, "Segment %d: %d transitions restored levels = %d\n", 
      seg, transitions, report.level); fflush(stdout);
      return 1;
    }
// Initial state must be fold 

static int lcb(int id, VDBload_t kind, int count, elm_t *elm) {
     static int cnt = 0, r = 0;
     if (srcvdb && elm[0]>=0 && elm[1]!=DEADLOCK && VDBgetIdx(srcvdb, elm)<0)
          r = -1; 
     else   
     if (elm[0]<0 || elm[0]>= env->nLeft) r = -1;
     else
     if (elm[1]!=DEADLOCK &&(elm[1]<0 || elm[1]>= env->nRight)) r = -1;
     cnt++;
     /* if (r<0) fprintf(stderr, "Truncated seg = %d (%d, %d) cnt = %d\n", 
	 	seg, elm[0], elm[1], cnt); */
     return r;
     } 

static void SendValueToMgr(file_t *mgr, vdb_t vdb) { 
     idx_t idx; vdbval_t val;    
     C_mgr2fork_idx(mgr[0], &idx);
// fprintf(stderr,"Fork received %d\n", idx);
     VDBgetExtra(vdb, &val, idx);
// fprintf(stderr,"Fork send (%d %d)\n", val.idx, val.seg);
     C_fork2mgr_val(mgr[1], &val); 
     }

static void Report(fifo_t output, vdb_t vdb, int from, size_t msgSize) {
     int client_read = CLIENT_READ;
     static int n  = 0;
     if ((++n) == nseg) {
        SendVisitedToMgr(mgr[1], vdb); 
        endlevel(0, 0);
        if (output) {
            FIFOput(output, &(unexplored->c));
            if (transfile) WriteEndLevelMarker();
            if (env->file) VDBflush(vdb, explored-1);
            }
	n = 0;
	}
     else {
       C_fork2mgr_segtag(mgr[1], &seg, &client_read);
     }
     C_fork2mgr_int(mgr[1], &from);
     C_fork2mgr_long(mgr[1], (long*) &msgSize);
   }
    
static void SelectUnexplored(int from, vdb_t vdb, fifo_t output) {
     file_t f = inputs[from]; 
     size_t msgSize = 0;
     explored = VDBgetCount(vdb);
/* fprintf(stderr,"Begin selectUnexplored   %d->%d\n", from, seg); */
     do {
        msgSize += C_inst2fork_visited(f, visited);
/*
        fprintf(stderr,"QQB:idx = %d seg %d from = %d (%d %d)\n", 
        visited->c.idx, seg, from, visited->dest[0], visited->dest[1]);
*/
	if (visited->c.idx>=0) PutFifo(from, visited, vdb,  output);
        } while (visited->c.idx!=ENDLEVELMARKER);
     if (env->restore && line>0) output = NULL;
     Report(output, vdb, from, msgSize);
// fprintf(stderr,"End selectUnexplored   %d->%d\n", from, seg); 
     } 

static void AppendOpen(transfile_t *t, char *mode) {
    int j;
    for (j=0;j<nseg;j++) {
       t[j].src = UTLopen(dest[j], mode, "/src/stepper.%d", seg);
       t[j].act = UTLopen(env->dir, mode, "/act/stepper.%d", j);          
       t[j].dest = UTLopen(env->dir, mode, "/dest/stepper.%d", j);
       }
    } 
    
static file_t StartInstantiator(file_t mgr[2], char *mgrhost, char *insthost) { 
   char cmd[256]; int tag;
   file_t f;
   cmd[0]='\0';
   if (env->global) sprintf(cmd,SSH, insthost);
   sprintf(cmd+strlen(cmd),
     "%s/dinstantiate %s %d %d %d",EXECDIR,  env->global?mgrhost:env->host,
     env->port+seg+1, seg, env->sleep);
   C_mgr2fork_tag(mgr[0], &tag); 
   if (tag != MGR_START) errormsg("Tag %c unequal %c", tag, MGR_START);
   f = Popen(cmd, "r");
   if (!f) errormsg("Cannot open %s", cmd); 
   fgets(cmd, 256, f);
   sscanf(cmd, "%d", &report.pid);
   if (env->file) {
        transfile = calloc(nseg, sizeof(transfile_t));
        AppendOpen(transfile, "a");
        }
   dest_pair[0] = seg;
   return f;
   }
   
static int RedirectOutput(file_t f) {
   char output[1024], *r = fgets(output, 1024, f);
   if (r) {
      fputs(output, stdout);fflush(stdout);
      return 1;
      }
   return 0;
   }  

static void Mpclose(file_t f) {
   errorreset();printmsg("%d exits",seg);
   // fflush(stdout); 
   if (f) pclose(f);
   // fcloseall();
   } 

static void Acknowledge() {  
    fputc('a', stdout); fflush(stdout); 
    }

static void printArgs(int argc, char *argv[]) {
    int i;
    fprintf(stderr,"F:");
    for (i=0;i<argc;i++) fprintf(stderr,"%s ",argv[i]);
    fprintf(stderr,"\n");
    }
    
static void SendNewUnexploredStates(fifo_t output, long threshold) {
    int cnt = 0;
// fprintf(stderr,"QQQQ %d\n", threshold);
    C_fork2inst_long(inst[1], &threshold);
    do {
      elm_t *elm;
      FIFOget(output, &(unexplored->c));
      if (unexplored->c.idx!=ENDLEVELMARKER) {
         elm = trdb?TRDBget(trdb, unexplored->src):unexplored->src;
         memcpy(unexplored->src, elm, env->K*sizeof(elm_t));
         }
      if (line>=0) line--;
      /*
      {int i; for (i=0;i<env->K;i++)
      fprintf(stderr,"QQB: SenUnexplor %d (%d)\n", unexplored->c.idx, unexplored->src[i]); 
      }
      */
      C_fork2inst_unexplored(inst[1], unexplored);
      cnt++;
      }
    while (unexplored->c.idx!=ENDLEVELMARKER);
// fprintf(stderr,"Send seg %d cnt = %d\n" , seg, cnt);
    fflush(inst[1]);
    }
  

static int ReadSrc(vdb_t vdb, vdb_t srcvdb, transfile_t *tf, int *f) {
    elm_t *elm = unexplored->src;
    int end = 0;
    // fprintf(stderr,"Begin ReadSrc\n");
    do {
       if (!readBinary(tf->src, elm, env->K)) {
              end = 1; 
	      fclose(tf->src);fclose(tf->act);fclose(tf->dest);
	      break;  
              }
       if (elm[0]>=0) {
	 if (VDBgetIdx(vdb, elm)<0) {
	     end = 1; 
             fclose(tf->src);fclose(tf->act);fclose(tf->dest);
	     break;
	     }
	 PutOK(VDBput(srcvdb, elm, NULL)); 
	 } 
     } while (elm[0]!=ENDLEVELMARKER);
    *f = VDBgetCount(srcvdb);
    // fprintf(stderr,"%d: End readsrc %d\n", seg, *f);
    return end;
    }
    
static vdb_t ReadSrcVDB(fifo_t frek) {
   int j, neof = 0, f;
   DECLA(int, eof, nseg);
   file_t  vdbf[2];
   memset(eof, 0, nseg*sizeof(int));
   DumpFiles(env->dir, vdbf, "r");
   {
   vdb_t vdb = VDBcreate(seg, env->K, vdbf[0], NULL, NULL, NULL, NULL, NULL, NULL),
      srcvdb = VDBcreate(seg, env->K, NULL, NULL, NULL, NULL, NULL, NULL, NULL);
   transfile_t *transfile = calloc(nseg, sizeof(transfile_t)); 
   RestoreOpen2(transfile, "r");
   do {
     for (j=0;j<nseg;j++) {
        if (!eof[j]) {
          eof[j] = ReadSrc(vdb, srcvdb, transfile+j, &f);
	  if (eof[j]) neof++;
	  }
	}
     FIFOput(frek, &f);
     /* fprintf(stderr,"%d:End ReadSrcVDB cnt = %d f = %d\n", 
     seg, FIFOgetCount(frek), f); */
     } while (neof < nseg);
   VDBdestroy(vdb);
   return srcvdb;
   }
   }

static void OpenInfo() {
    sprintf(fulldirname,"%s", env->logdir);
    /*
    if (CreateEmptyDir(fulldirname, DELETE_NONE)!=0)
                    errormsg("At Creating empty directory %s", fulldirname); 
    */
    sprintf(fulldirname+strlen(fulldirname),"/%d", seg);
    {
    char *tail = fulldirname+strlen(fulldirname);
    if (CreateEmptyDir(fulldirname, DELETE_NONE)!=0)
                    errormsg("At Creating empty directory %s", fulldirname);
    info = (info_t*) malloc(sizeof(info_t));
    sprintf(tail,"/closed"); info->closed = fopen(fulldirname,"w");
    sprintf(tail,"/closed_tree"); info->closed_tree = fopen(fulldirname,"w");
    sprintf(tail,"/closed_entries"); info->closed_entries = fopen(fulldirname,"w");
    }
    } 
                            
int main(int argc, char *argv[]) {
    char *mgrhost = argv[1], *insthost = argv[5];
    int mgrport = atoi(argv[2]), socket, s = 0, 
          r, i, k, *segments,  tag,  to;
    long threshold = LONG_MAX;
    file_t  vdbf[2],  *sockets;
    fd_set rfds; 
    act_t act;
    fifo_t output, frek = NULL;
    seg = atoi(argv[3]);
    DYNcalloc(env, env_t, char, PRIOWIDTH, priority);
    env->nseg = nseg = atoi(argv[4]);
    report.level = 0;
    UTLinit(NULL, NULL, NULL, "fork");
// Contacts manager and fetches information
    Acknowledge();
    // if (env->local) setLocal();
     if (getenv("MCRL_LOCAL")) {
         setLocal();
         }
    Mgr(mgrhost, mgrport, mgr);
    DYNcalloc(visited, visited_t, elm_t, env->K, dest);
    DYNcalloc(unexplored, unexplored_t, elm_t, env->K, src);
// Fetches file pointers  
    sockets = (file_t*) calloc(nseg+3, sizeof(file_t));
    inputs = (file_t*) calloc(nseg, sizeof(file_t));
    segments = (int*) calloc(nseg+3, sizeof(int));
    if (env->file) DumpFiles(env->dir, vdbf, env->restore?"a+":"w");
// Creates databases
    if (env->restore) { 
      frek = FIFOcreateMemo(100, sizeof(int), NULL, NULL);
      srcvdb = ReadSrcVDB(frek);
      }
    if (env->tree) {
       // fprintf(stderr,"Tree CREATED\n");
       trdb = TRDBcreate(seg, env->K);
       }
    vdb = VDBcreateExtra(seg, trdb?2:env->K, sizeof(vdbval_t), env->file?vdbf:NULL , lcb);
// fprintf(stderr, "vdb %d: Number of records %d\n", seg, VDBgetCount(vdb));
    // fflush(stdout);
    output = FIFOcreateMemo(100, sizeof(u_context_t)+(trdb?2:env->K)*sizeof(elm_t), NULL, NULL);
    if (srcvdb) VDBdestroy(srcvdb);
    DYNcalloc(ad, ad_t, weight_t, env->spectrum, var);
    if (env->restore) 
         {if (!RestoreStates(output, frek, vdb)) env->restore = 0;}
    if (env->log) OpenInfo();  
    if (!env->restore) Synchronize();
 // printmsg("Server socket %d %d", env->port, seg);
    socket = serverSocket(env->port+1+seg,0);
 // printmsg("Server socket done %d %d", env->port, seg);
    sockets[s++]= fdopen(socket,"r");
    sockets[s++]= mgr[0];
    // fprintf(stderr, "Start Instantiator\n");
    sockets[s++]= StartInstantiator(mgr, mgrhost, insthost); 
    while (1) {
       FD_ZERO(&rfds);
       if (naccept==nseg) {
           for (i=0;i<s;i++) 
              if (sockets[i]) FD_SET(Fileno(sockets[i]), &rfds);
           } else FD_SET(Fileno(sockets[0]), &rfds);
       if ((r=select(MAXFDS, &rfds, NULL, NULL, NULL))<0) errormsg("Fork select");
       for (i=0,k=0;k<r && i<s;i++) 
         if (sockets[i] && FD_ISSET(Fileno(sockets[i]), &rfds)) {
	  switch (i) {
	    case 0: 
	    Maccept(s, sockets, segments, vdb);s++; naccept++; break;
	    case 1: C_mgr2fork_tag(mgr[0], &tag);
                    // fprintf(stderr, "Fork %d tag? %d from mgr\n", seg, tag);
                    switch (tag) {
                        case MGR_TICK:
                        case MGR_BACKUP:
                    	case MGR_CONTINUE:
                            memset(ad->var, 0, env->spectrum*sizeof(weight_t));
                            ad->max = -1;ad->min = env->spectrum;
                            C_mgr2fork_long(mgr[0], &threshold);
                            C_fork2inst_tag(inst[1], &tag); 
                            break;
	                case MGR_WRITE:
	                     C_fork2inst_tag(inst[1], &tag);
	                     C_mgr2fork_seg(mgr[0], &to);
	                     C_fork2inst_seg(inst[1], &to);
	                     break;
                        case MGR_PARENT: SendValueToMgr(mgr, vdb); break;
                        case MGR_EXIT: 
			   C_fork2inst_tag(inst[1], &tag);
                           Mpclose(sockets[2]); 
			   exit(0);
                        default: errormsg("Fork Mgr %d Illegal tag  %d", seg, tag); 
                        }
                    break;
	    case 2: if (!RedirectOutput(sockets[2])) { 
	    	        sockets[2] = NULL; break;
	                }
	    default:  {
              C_inst2fork_tag(sockets[i], &tag);
              // fprintf(stderr, "Fork %d from %d %c\n", seg, segments[i], tag);
              switch (tag) {
                case CLIENT_FINISHED:
                // fprintf(stderr,"Fork %d Client Finished\n", seg);
                  ad->closedvByteSize = trdb?TRDBgetByteSize(trdb):0;
                  ad->closedEntries = trdb?TRDBgetEntrieCount(trdb):0;
                  ad->closedByteSize = VDBgetByteSize(vdb);
                  if (info) {
                      fprintf(info->closed, "%10d\n", ad->closedByteSize);
                      fprintf(info->closed_tree, "%10d\n", ad->closedvByteSize);
                      fprintf(info->closed_entries, "%10d\n", ad->closedEntries);
                      }
                case CLIENT_PROGRESS: {
		  C_inst2fork_ad(sockets[i], ad);
                  ad->visited = VDBgetCount(vdb);
                  C_fork2mgr_segtag(mgr[1],  &seg, &tag);
                  C_fork2mgr_ad(mgr[1], ad);
                  break;
                  }
		case CLIENT_READ:
                  SelectUnexplored(segments[i], vdb,  output);
                  break;
                case CLIENT_ACTION:
		 C_inst2fork_act(inst[0], &act);
		 C_fork2inst_tag(inst[1], &tag);
		 // fprintf(stderr,"Found action (%d %d)\n", act.lab, act.smd);
		 C_fork2mgr_segtag(mgr[1], &seg, &tag);
		 C_fork2mgr_act(mgr[1], &act);
		 C_mgr2fork_tag(mgr[0], &tag);
		 break;
                case INST_INITSTATE: 
		     {
                     int tag = MGR_CONTINUE;
/* fprintf(stderr,"Fork receive?  C_inst2fork_visited\n"); */
                     C_inst2fork_visited(sockets[i], visited);
/* fprintf(stderr,"Fork receive!  C_inst2fork_visited\n"); */
                     if (!env->restore) FirstState(output,  visited); 
		     if (transfile) WriteEndLevelMarker();
                     report.level++;
                     SendReport();
                     ad->visited = VDBgetCount(vdb);
                     C_fork2mgr_ad(mgr[1], ad);
                     C_mgr2fork_tag(mgr[0], &tag);
                     }
                case INST_CONTINUE: 
		 SendNewUnexploredStates(output, threshold);
                 break;
                case -1: sockets[i]=NULL; 
#ifndef NDEBUG
                         printmsg("%d:Segment[%d] eof", seg, segments[i]);
#endif 
                         break;
                default: errormsg("Fork client %d illegal tag %d", seg, tag);
	      }
	    }
          }
        k++; 
        }
    }
  }
#endif
