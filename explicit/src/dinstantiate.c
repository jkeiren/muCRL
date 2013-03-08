/* $Id: dinstantiate.c,v 1.10 2008/04/28 14:14:10 bertl Exp $ */
#define _GNU_SOURCE
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#define DINSTANTIATE_C
#include <stdio.h>
#include <limits.h>
#include "param0.h"
#include "utl.h"
#include "fifo.h"
#include "label.h"
#include "rw.h"
#include <string.h>
#include "seglts.h"
#include "discover.h"
#include "mgr.h"
#include "discover.h"
#include "vector_db.h"
#include "term_db.h"
#include "inst_fork.h"
typedef struct {
   int n, b1, b2;
} bound_t;

static bound_t bound;

typedef struct {
	bfile_t *f;
	char *ptr;
	size_t size;
   } next_t;

static next_t next;

void FoldVector(elm_t *dest, elm_t *src);
void UnfoldVector(elm_t *dest, elm_t *src);

typedef struct {
     FILE *r, *w;
     } rw_t;
     
static tdb_t leafs, labels;
static vdb_t *nodes;
static elm_t *init_state = NULL;
 
static rw_t vork, dbs;

static elm_t endlevel[] = {ENDLEVELMARKER, 0};

static file_t *output;

static char fulldirname[100];

static FILE *log = NULL;

static int seg, level = 0,  eof; 
static long threshold = LONG_MAX;
static long level_transitions = 0, level_backup = 0;

static info_t *info = NULL;
                  
env_t *env;
static ad_t *ad;
static char **dest, **host, *mcrlArgs, *pattern, *reject, *sselect,
*spriority, *deadlock_action;
static preg_t action_reg = NULL, reject_reg = NULL, select_reg = NULL, 
priority_reg=NULL, action_deadlock = NULL;
static step_t st;

static visited_t *visited;
static unexplored_t *unexplored;

static unsigned int nseg;

#include "sede_dinstantiate.h"
  
static void ExploreOK(int code) {  
   if (code>=0) return; 
   errormsg("INST %d:Explore error: code = %d", seg, code); 
   }

     
static int String2Act(char *act) {
    ATerm t = (ATerm) ATmakeAppl0(ATmakeAFun(act, 0, ATtrue));
    int new;
    return TDBput(labels, t,  &new);
    }

static char *Act2String(int act) {
      return ATgetName(ATgetAFun(TDBget(labels, act)));
      }
           
static void WarningHandler(const char *format, va_list args) {
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }

static void ErrorHandler(const char *format, va_list args) {
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n"); 
     exit(1);
     }
   
 static void Match(act_t *act) {  
   static int cnt = 0;
   if (action_reg) {
   	     char *lab = Act2String(act->lab);
	     if (RegMatch(action_reg, lab) && (env->all||
                  (getlabelindex(lab, 1)==cnt))) {
		     int tag = CLIENT_ACTION;
		     // fprintf(stderr,"Matched %s\n", lab);
		     C_inst2fork_tag(vork.w,  &tag);
		     C_inst2fork_act(vork.w,  act);
		     C_fork2inst_tag(vork.r, &tag);
		     cnt++;
		     }
         }
    }
            


static void EndLevels(void *context) {
   int i;
   visited->dest[0]=ENDLEVELMARKER;
   visited->dest[1]=UNDEF;
   SEDE_DATA(contextWrite, context).c.idx = ENDLEVELMARKER;
   // SEDE_DATA(contextWrite, context).c.act = UNDEF;
   for (i=0;i<nseg;i++) {
      SEDE_DATA(contextWrite, context).seg = i;
      SEDEwrite(visited->dest, context);   
      }
   }

static void Evaluate(char *priority, void *context) { 
#ifdef MCRL
    long k =  DISevaluate(priority);
    if (k<0) k = 0;
    if (k>=env->spectrum) k = env->spectrum-1; 
    SEDE_DATA(contextWrite, context).c.w = k;
#else
    SEDE_DATA(contextWrite, context).c.w = 0;
#endif
    }

static int ecb(elm_t *src, act_t *act, elm_t *dest) {  
// fprintf(stderr,"ecb [%d %d] %d\n", dest[0], dest[1], dest[2]);
	bfwrite(src, sizeof(elm_t), nodes?2:env->K, next.f);
	bfwrite(act, sizeof(act_t), 1, next.f);
	bfwrite(dest, sizeof(elm_t), nodes?3:env->K, next.f); 
        // 3 because of checksum      
	return 0;
    }
             
static int ecb_delayed(elm_t *src, act_t *act, elm_t *dest) {
    int l = nodes?dest[2]:DISsegment(st, dest); 
        // CheckSum computed and stored By Fold */
    Match(act);
    if (env->tick&&!strcmp(Act2String(act->lab), env->tickstring)) {
        if (env->priority) Evaluate(env->priority, ticks);
        SEDE_DATA(contextWrite, ticks).seg = l;
        SEDE_DATA(contextWrite, ticks).c.act = act->lab;
        SEDE_DATA(contextWrite, ticks).c.idx = act->smd;
        SEDE_DATA(contextWrite, ticks).c.src[0] = src[0];
        SEDE_DATA(contextWrite, ticks).c.src[1] = src[1];
        SEDEwrite(dest, &ticks);
        ad->ticks++;
	 }
    else {
	 // fprintf(stderr, "%s==%s\n", spriority,  Act2String(act->lab));
         if (!priority_reg || RegMatch(priority_reg, Act2String(act->lab))) {
                // fprintf(stderr,"YES\n");
		 if (env ->priority) Evaluate(env->priority, visits);
		 SEDE_DATA(contextWrite, visits).seg = l;
		 SEDE_DATA(contextWrite, visits).c.act = act->lab;
		 SEDE_DATA(contextWrite, visits).c.idx = act->smd;
		 SEDE_DATA(contextWrite, visits).c.src[0] = src[0];
		 SEDE_DATA(contextWrite, visits).c.src[1] = src[1];
	// fprintf(stderr,"[%5d %5d %5d]\n", dest[0], dest[1], dest[2]);
		 SEDEwrite(dest, &visits);
                 level_transitions++; ad->transitions++;
         } else
         /*if (priority_reg)*/ {
	     if (env->priority) Evaluate(env->priority, backups);
	      SEDE_DATA(contextWrite, backups).seg = l;
	      SEDE_DATA(contextWrite, backups).c.act = act->lab;
	      SEDE_DATA(contextWrite, backups).c.idx = act->smd;
	      SEDE_DATA(contextWrite, backups).c.src[0] = src[0];
	      SEDE_DATA(contextWrite, backups).c.src[1] = src[1];
              SEDEwrite(dest, &backups);
              level_backup++;
              // ad->backup++;
              }
         } 
    return 0;
    }

static int nextCompare(const char *p, const char *q) {
	char *pp = Act2String(*(int*) (p+bound.b1)), *qq = Act2String(*(int*)(q+bound.b1)), 
	*pt = NULL, *qt = NULL;
	if (!(pt=strchr(pp,'(')) && !(qt=strchr(qq,'('))) return strcmp(pp, qq);
	if (!pt  && qt) return 1; 
	if (pt && !qt) return -1; 
	return strcmp(pt, qt);
}

static void printLog(int begin, int end) {
       int i;
       for (i=begin;i<end;i+=bound.n) {
          char *buf = next.ptr+i;
	  char *pp = Act2String(*(int*) (buf+bound.b1));
          fprintf(log,"%s\n", pp);
          }
    }
    
static void selectNext(int *begin, int *end) {
	int i;
	char last[512];
	int ignore = 0, b=0;
	*begin = b; *end = next.size;
	last[0]='\0';
        if (next.size==0) return;
	for (i=0;i<next.size;i+=bound.n) {
  	  char *buf = next.ptr+i;
	  char *pp = Act2String(*(int*) (buf+bound.b1));
	  char *pt = strchr(pp,'(');
	  if (!pt) break;
	  {
	  char *qt = strpbrk(pt, ",)");
	  int v = qt-pt;
	  if (strncmp(last, pt, v)) {  // first argument 
	  	  if (last[0]!='\0') {
	  	  	if (log) fprintf(log, "%d:%s  %d-%d=%d\n", ignore, last, i/bound.n,
			i/bound.n,(i-b)/bound.n);
			if (!ignore) {
	  	  	if ((i-b) < (*end-*begin)) { // The smallest
	  	  	      *end = i; *begin = b;
                              if (log) printLog(*begin, *end);
	  	  	      }
			} else ignore = 0;
	  	    }
                  b = i;
	  	  strncpy(last, pt, v); last[v]='\0';      
	      }	
          // fprintf(stderr,"ignore:%d b=%d e=%d size=%d\n",ignore, b, i, next.size);       
	  } 
	  if ((reject_reg && RegMatch(reject_reg, pp)) ||
                 (select_reg && !RegMatch(select_reg, pp))) ignore = 1;    
	}
        if (!ignore) {
	      if (log) fprintf(log, "%d Last:%s  %d-%d=%d [%d %d)\n", ignore, 
              last, i/bound.n, b/bound.n,(i-b)/bound.n, *begin, *end);
              // fprintf(stderr,"b end not ignore b=%d e=%d size=%d\n",b, i, next.size);
	      if ((i-b) < (*end-*begin)) { // The smallest
	  	    *end = i; *begin = b;
                   if (log) printLog(*begin, *end);
	           }
	      }
	if (*begin==*end) {*begin = 0;*end = next.size;}
	if (log) fprintf(log, "Chosen %d %d %d<%d\n", (*begin)/bound.n,
	(*end)/bound.n,
        (*end-*begin)/bound.n, next.size/bound.n);
}

static int fecb(unexplored_t *unexplored,  int n_transitions) { 
  int i, begin, end;
  bfflush(next.f);
  if (reject_reg || select_reg) {
     qsort(next.ptr, n_transitions, bound.n,  (int(*)(const void *, const void *)) nextCompare);
     selectNext(&begin, &end);
  }
  else {
    begin = 0; end = next.size;
  }
  ad->enabled += ((next.size/*-begin*/)/bound.n);
  for (i=begin;i<end;i+=bound.n) {
  	  char *buf = next.ptr+i;
// fprintf(stderr,"ecb_delayed bound.n %d\n", bound.n);
  	  ecb_delayed((elm_t*) buf, (act_t*) (buf+bound.b1), (elm_t*) (buf+bound.b2));
      }
  brewind(next.f);
  if (n_transitions==0) {   
     act_t  act;
     // fprintf(stderr,"DEADLOCK %s\n", env->deadlockstring);
     int l = seg, deadlock = String2Act(env->deadlockstring);
     act.lab = deadlock; act.smd = unexplored->c.idx;
     Match(&act);
     visited->dest[0] = 0; visited->dest[1] = DEADLOCK;
     visited->c.act =  deadlock; visited->c.idx = unexplored->c.idx;
     visited->c.forceParent = 0; 
     SEDE_DATA(contextWrite, visits).seg = l;
     SEDE_DATA(contextWrite, visits).c.idx = unexplored->c.idx;
     SEDE_DATA(contextWrite, visits).c.act = deadlock;
     SEDE_DATA(contextWrite, visits).c.w = 0;
     SEDEwrite(visited->dest, &visits);
     ad->deadlocks++;
     }
  // fprintf(stderr,"QQ:%d\n", ad->ticks);
  return 0;
  }
      
static void Report(int idx, int tag) {  
	ad->idx = idx; 
    int i;
    unsigned long d = 0, cnt = 0;
    if (nodes) for (i=2;i<env->npars;i++) {
         d += VDBgetByteSize(nodes[i]);
         cnt += VDBgetCount(nodes[i]);
         }
    ad->openvByteSize = d;
    ad->openEntries = cnt;
    ad->termByteSize = AT_calcAllocatedSize();
    for (d=0, i=0;i<env->nseg;i++) {
       out_t out = SEDE_DATA(contextWrite, &visits).out[i];
       // d += out.bsize;
       d += out.size;
       }
    for (i=0;i<env->nseg;i++) {
       out_t out = SEDE_DATA(contextWrite, &ticks).out[i];
       d += out.size;
       }
    // d+= n;
    ad->queueByteSize = d;
    C_inst2fork_tag(vork.w, &tag);
 // fprintf(stderr,"Report:(%d,%d,%d)\n", ad->termByteSize, ad->openvByteSize,
 //   ad->openByteSize);

    ad->msgCount = TDBgetMsgCount(leafs);
    ad->msgTime = TDBgetMsgTime(leafs);
    if (TDBgetMsgMinTime(leafs)<ad->minMsgTime) ad->minMsgTime = TDBgetMsgMinTime(leafs);
    if (TDBgetMsgMaxTime(leafs)>ad->maxMsgTime) ad->maxMsgTime = TDBgetMsgMaxTime(leafs);
    ad->msgCount += TDBgetMsgCount(labels);
    ad->msgTime += TDBgetMsgTime(labels);
    if (TDBgetMsgMinTime(labels)<ad->minMsgTime)
         ad->minMsgTime = TDBgetMsgMinTime(labels);
    if (TDBgetMsgMaxTime(labels)>ad->maxMsgTime)
         ad->maxMsgTime = TDBgetMsgMaxTime(labels);
    for (i=env->K;i<env->npars;i++) {
         if (nodes) {
	    ad->msgCount += VDBgetMsgCount(nodes[i]);
             ad->msgTime += VDBgetMsgTime(nodes[i]);
            if (VDBgetMsgMinTime(nodes[i])<ad->minMsgTime) 
                   ad->minMsgTime = VDBgetMsgMinTime(nodes[i]);
            if (VDBgetMsgMaxTime(nodes[i])>ad->maxMsgTime) 
                   ad->maxMsgTime = VDBgetMsgMaxTime(nodes[i]);
	    }
         }
    C_inst2fork_ad(vork.w, ad);
    /*
    fprintf(stdout,"segment %d explored %d transitions %d\n",
        seg, ad->explored, ad->transitions);
    fflush(stdout);
    */
    if (info && tag==CLIENT_FINISHED) {
 fprintf(info->explored,"%10d\n", ad->explored); fflush(info->explored);
 fprintf(info->transitions,"%10d\n",ad->transitions);fflush(info->transitions);
 fprintf(info->messages,"%10d\n", ad->msgCount);fflush(info->messages);
 fprintf(info->queue, "%10d\n", ad->queueByteSize);
 fprintf(info->open_entries, "%10d\n", ad->openEntries);
 fprintf(info->open, "%10d\n", ad->openByteSize);
 fprintf(info->open_tree, "%10d\n", ad->openvByteSize);
 fflush(info->open); 
 // GZflush(info->message_times);   
        }
    }

static int compare(const void *p, const void *q) {
    if (((u_context_t*)p)->w<((u_context_t*)q)->w) return -1; 
    if (((u_context_t*)p)->w>((u_context_t*)q)->w) return 1;
    return 0;  
    }

static void RegistrateWeightFrek(u_context_t *x) { 
    long k = x->w; 
    if (k<0) k = 0; if (k>=env->spectrum) k = env->spectrum-1;
    ad->var[k].w++;
    if (k>ad->wmax) ad->wmax = k; 
    if (k<ad->wmin) ad->wmin = k;
    // fprintf(stderr,"Registrate: k = %d f = %d\n", k, ad->w[k]);
    }
        
static void NodesReset() {
       int i;
       if (nodes && env->K>2)
       for (i=env->npars-1;i>=2;i--) 
       VDBreset(nodes[i]);  
       }

static int DinstantiateLevel(cnt) {
 int i = 0, idx = -1, tag, j = 0;
 u_context_t *fifo = (u_context_t*) 
      FIFOgetArray(SEDE_DATA(contextRead, input).fifo);
 char *ptr = (char*) fifo;
 long n = FIFOgetCount(SEDE_DATA(contextRead, input).fifo);
 int step = sizeof(u_context_t)+(nodes?2:env->K)*sizeof(elm_t);
 level_transitions = 0; 
 ad->openByteSize = FIFOgetByteSize(SEDE_DATA(contextRead, input).fifo);
 if (env->priority) qsort(fifo, n, step , compare);
 if (threshold<n) n = threshold;
 // fprintf(stderr,"Start\n");
 // fprintf(stderr,"Help %d %d\n", ad->wmin, ad->wmax);
 if (ad->wmax>=ad->wmin)
    memset(ad->var+ad->wmin, 0, (ad->wmax-ad->wmin+1)*sizeof(weight_t));
 // memset(ad->w, 0, env->spectrum*sizeof(long));
 ad->max = 0; ad->min = env->spectrum;
 ad->wmax = 0; ad->wmin = env->spectrum;
 /*fprintf(stderr,"DinstantiateLevel: %d n = %d step = %d (%d %d)\n", seg, n, step, 
      nodes, env->K); */
 for (i=0;i<n;i++, ptr += step) { 
     u_context_t *x = (u_context_t*) ptr;
     if (eof==0) eof = 1; 
     unexplored->c = *x;
     memcpy(unexplored->src, ptr+sizeof(u_context_t), (nodes?2:env->K)*sizeof(elm_t));
//fprintf(stderr,"%d:Explore: (%d %d)\n",seg,  unexplored->src[0], unexplored->src[1]);
     ExploreOK(DISexplore(st, unexplored));
     RegistrateWeightFrek(x);
     idx = x->idx; ad->explored++;
     if (i>0 && i%env->progress==0) {
	 Report(idx, CLIENT_PROGRESS);
	 C_fork2inst_tag(vork.r, &tag);
	 if (tag != MGR_CONTINUE) {
	   if (tag==MGR_EXIT) {
	      Report(idx, tag);
	      exit(0);
	      }
	   errormsg("tag = %c!=%c", tag, MGR_CONTINUE);
	   }
	 }   
     }
     FIFOreset(SEDE_DATA(contextRead, input).fifo);
     /*
     {int k;
     for (k=ad->wmin; k<=ad->wmax;k++)
        fprintf(stderr,"Registrate: k = %d f = %d\n", k, ad->w[k]);
     }
     */
     if (log) fflush(log);
     /*fprintf(stderr,"DinstantiateLevel Finished\n"); */
     return idx;     
 }

static void PrintQ(elm_t *src, elm_t *dest) {
 int i;
 
 for (i=0;i<env->K;i++) fprintf(stderr,"%d ", dest[i]);
 fprintf(stderr,":%d: [%d %d]:", seg, src[0], src[1]);
 fprintf(stderr,"\n");
 }
 
    
static void SendToDataBase(void *context) {
     int to, client_read = CLIENT_READ; 
     C_fork2inst_seg(vork.r, &to);
     C_inst2fork_tag(output[to], &client_read);
     // MemClose(to, context);
     {
     out_t out = SEDE_DATA(contextWrite, context).out[to];
     v_context_t *data = (v_context_t*) out.d;
     ssize_t n = out.cnt, i;
     char *ptr = (char*) data;
     int step = sizeof(v_context_t)+(nodes?2:env->K)*sizeof(elm_t);
// fprintf(stderr,"Begin SendToDataBase %d->%d n = %d %lx\n", seg, to, n, context);
     for (i = 0; i < n; i++, ptr += step) {
        data = (v_context_t*) ptr;
        visited->c= *data;
	if (env->K==2 || !env->tree)
           memcpy(visited->dest, ptr+sizeof(v_context_t), env->K*sizeof(elm_t));
	else {
	 // fprintf(stderr,"Begin unfold %d\n", seg);
	  UnfoldVector(visited->dest, (elm_t*) (ptr+sizeof(v_context_t)));
          // PrintQ((elm_t*) (ptr+sizeof(v_context_t)), visited->dest);
	  // fprintf(stderr,"End unfold %d\n", seg);
	  }
        if (action_deadlock) {
           elm_t act = data->act;
             if (act>=0) {
             char *lab = Act2String(act);
             visited->c.forceParent = (action_deadlock && 
                 RegMatch(action_deadlock, lab))?1:0;
             }
           }
/*
fprintf(stderr,"[%d, %d] %d\n", visited->dest[0], visited->dest[1],
                    visited->c.idx); 
*/
        C_inst2fork_visited(output[to], visited);
        } 
     fflush(output[to]);
// fprintf(stderr,"End SendToDataBase %d->%d n = %d\n", seg, to, n); 
     }
     }
      
static int ReadInput() {
     static void *src = NULL;
     int cnt  = 0;
// fprintf(stderr,"Input STDread %lx\n", src);
     C_fork2inst_long(SEDE_DATA(contextRead, input).input, &threshold);
// fprintf(stderr,"Threshold %d\n", threshold);
     while (SEDEread(&src, input)!=EOF) cnt++;
     ad->explored += SEDE_DATA(contextRead, input).explored;
     // fprintf(stderr,"%d:ad->explored %d\n", seg, ad->explored);
     ad->transitions += SEDE_DATA(contextRead, input).transitions;
     return cnt;
     }

          
static void Dinstantiate(visited_t *visited) {
    int tag, tick_state = 0, backup_state = 0;
    do {
       int idx, inst_continue = INST_CONTINUE, inst_initstate = INST_INITSTATE,
       cnt;
       // fprintf(stderr,"Inst %d Before Tag\n", seg);
       C_fork2inst_tag(vork.r, &tag);
       // fprintf(stderr,"Inst %d After Tag %c\n", seg, tag);
       switch (tag) {
         case MGR_CONTINUE: tick_state = 0; 
	 case MGR_TICK: backup_state=0;
	 case MGR_BACKUP:
                         if (init_state) {
			    // fprintf(stderr, "Send init %d\n", seg);
                            C_inst2fork_tag(vork.w, &inst_initstate);
                            C_inst2fork_visited(vork.w, visited);
                            fflush(vork.w);
                            init_state = NULL;
                            }
                         else {
                            // fprintf(stderr,"dinst:Send Continue\n");
                            C_inst2fork_tag(vork.w, &inst_continue); 
                            fflush(vork.w);
                            }
                         // fprintf(stderr,"Inst %d Before Input Read\n", seg);
                         NodesReset();
                         cnt = ReadInput(); 
                         if (tag!=MGR_BACKUP) {
                                   EndLevels(&backups);
                                   level_backup = 0;
                                   }
			 idx = DinstantiateLevel(cnt);
	                 if (tag==MGR_TICK) {
                            tick_state = 1; 
                            }
	                 if (tag==MGR_BACKUP) {
                            backup_state = 1; 
                            ad->backup += level_backup;
                            // ad->enabled = ad->backup + ad->transitions;
                  // fprintf(stderr,"level_backup = %d\n", level_backup);
                            }
                         EndLevels(tick_state?&ticks:&visits);
                         Report(idx, CLIENT_FINISHED);
                         if (backup_state) {
                                 EndLevels(&backups);
                                 level_backup = 0;
                                 }
                         level++;
			 // fprintf(stderr,"Inst %d End Input Read\n", seg);
                         break;     
         case MGR_WRITE: {
         	         if (backup_state) SendToDataBase(&backups);
                         else
         	         SendToDataBase(tick_state?&ticks:&visits);
                         break;
                         }
         case MGR_EXIT: 
                         break;
         default: errormsg("Inst %d: Illegal tex %c", seg, tag);
         }
       } while (tag != MGR_EXIT);
  }
  
    

static void OpenFork(char *mgrhost, int mgrport) {
	int socket = clientSocket(mgrhost, mgrport,0);
	vork.r = fdopen(socket,"r");
	vork.w = fdopen(socket,"w");
    }
        
static void OpenConnections(char *mgrhost) {
    int i;
    for (i=0;i<nseg;i++) {
       if (i==seg) output[i] = vork.w;
       else {
         int socket = clientSocket((env->global?mgrhost:host[i]), env->port+1+i,0);
         output[i] = fdopen(socket,"w");
        C_inst2fork_seg(output[i], &seg);
        }
      }
     }
    
static void ShutStop(void) {
    errorreset();printmsg("%d:exits", seg);
    writeintUTF(dbs.w, -1); fflush(dbs.w);
    if (info) GZclose(info->message_times);
    }
    
static void Init(char *mgrhost) { 
     int i, socket = clientSocket(env->dbsHost, env->dbsPort,1000000), n;
     if (socket<0) errormsg("Cannot open dbs");
     dbs.r = fdopen(socket,"r"); dbs.w = fdopen(socket,"w");
     leafs = TDBcreate((int) env->npars, NULL, (channel_t) &dbs); 
     labels = TDBcreate((int) env->npars+1,  NULL, (channel_t) &dbs); 
     if (env->tree)  {
        nodes =  (vdb_t*) calloc(env->npars, sizeof(vdb_t));
       for (i=env->npars-1;i>=2;i--) 
          nodes[i] = 
       VDBcreate(i, 2, NULL, NULL,  (env->K==2?(channel_t) &dbs: NULL ),
           NULL, NULL, NULL, NULL);  
        }
     st = DIScreateMCRL(seg, (int) nseg, (nodes?2:env->K), env->K>2, labels, leafs, nodes, ecb, fecb);
     OpenConnections(mgrhost);
     if (atexit(ShutStop)<0) {fprintf(stderr,"atexit\n");exit(1);}
     /* fprintf(stderr,"Start dinstantiate %d (%s %d)\n",
         seg, env->dbsHost, env->dbsPort); */
     DYNcalloc(ad, ad_t, weight_t, env->spectrum, var);
     ad->max = env->spectrum-1; ad->min = 0;
     ad->wmax = env->spectrum-1; ad->wmin = 0;
     next.f = bopen_memstream(0, &next.ptr, &next.size);
     n = nodes?2:env->K;
     bound.n = 2*n*sizeof(elm_t)+sizeof(act_t)+
           (nodes?sizeof(elm_t):0); // For stored checksum
     bound.b1 = n*sizeof(elm_t);
     bound.b2 = n*sizeof(elm_t) + sizeof(act_t);
     }
     
static void Mgr() {
    int client_ready = CLIENT_READY;
    C_inst2fork_seg(vork.w, &seg);
    C_fork2inst_env(vork.r, env);
    nseg = env->nseg;
    
    dest = (char**) calloc(nseg, sizeof(char*));
    host = (char**) calloc(nseg, sizeof(char*));
    C_fork2inst_dest(vork.r, dest, nseg);
    C_fork2inst_dest(vork.r, host, nseg);  
    C_fork2inst_string(vork.r, &mcrlArgs);
    C_fork2inst_string(vork.r, &pattern); 
    C_fork2inst_string(vork.r, &reject); 
    C_fork2inst_string(vork.r, &sselect); 
    C_fork2inst_string(vork.r, &spriority); 
    C_fork2inst_string(vork.r, &deadlock_action); 
    // fprintf(stderr,"QQB %s\n", deadlock_action); 
    C_inst2fork_tag(vork.w, &client_ready);
    fflush(vork.w);
    }
    
static FILE *OpenLog(int seg) {
    char logname[100]; 
    FILE *f;
    sprintf(logname,"log.%d", seg);
    if (!(f=fopen(logname,"w"))) errormsg(logname);
    return f;
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
    sprintf(tail,"/explored"); info->explored= fopen(fulldirname,"w");
    sprintf(tail,"/transitions"); info->transitions= fopen(fulldirname,"w");
    sprintf(tail,"/messages"); info->messages = fopen(fulldirname,"w");
    sprintf(tail,"/message_times.gz"); info->message_times = GZopen(fulldirname,"w");
    sprintf(tail,"/open"); info->open = fopen(fulldirname,"w");
    sprintf(tail,"/open_tree"); info->open_tree = fopen(fulldirname,"w");
    sprintf(tail,"/queue"); info->queue = fopen(fulldirname,"w");
    sprintf(tail,"/open_entries"); info->open_entries = fopen(fulldirname,"w");
    // fprintf(stderr,"tail= %s\n", fulldirname);
    }
    TDBsetMsgTimes(leafs, info->message_times);
    TDBsetMsgTimes(labels, info->message_times);
    if (nodes) {
       int i = 2;
       for (;i<env->npars;i++) VDBsetMsgTimes(nodes[i], info->message_times);
       }
    } 
                                  
int main(int argc, char *argv[]) {
    char *mgrhost = argv[1];
    int mgrport = atoi(argv[2]), j = 0;
    char **newargv = (char**) calloc((size_t) argc, sizeof(char*)); 
    newargv[j++] = argv[0]; 
    seg = atoi(argv[3]);
    UTLinit(NULL, NULL, NULL, "dinstantiate");
    if (getenv("MCRL_LOCAL")) {
         setLocal();
         }
    DYNcalloc(env, env_t, char, PRIOWIDTH, priority);
    fprintf(stdout,"%d\n",getpid());fflush(stdout);
    OpenFork(mgrhost, mgrport);
    // sleep(atoi(argv[4])+seg);
    Mgr();
    DYNcalloc(visited, visited_t, elm_t, env->K, dest);
    DYNcalloc(unexplored, unexplored_t, elm_t, env->K, src);
    visited->dest[0] = visited->dest[1] = visited->c.act = visited->c.idx = UNDEF;
    visited->c.w = 0;
    // fprintf(stderr,"QQQQ pattern = %s\n", pattern);
    if (strlen(pattern)>0 && !(action_reg = RegCompile(pattern))) 
        { perror("Compile action pattern"); exit(1);}
    if (strlen(reject)>0 && !(reject_reg = RegCompile(reject))) 
        { perror("Compile reject pattern"); exit(1);}
    if (strlen(sselect)>0 && !(select_reg = RegCompile(sselect))) 
        { perror("Compile select pattern"); exit(1);}
    if (strlen(spriority)>0 && !(priority_reg = RegCompile(spriority))) 
        { perror("Compile priority pattern"); exit(1);}
    if (strlen(deadlock_action)>0 && !(action_deadlock = 
         RegCompile(deadlock_action))) 
        { perror("Compile action_deadlock pattern"); exit(1);}
    eof = env->restore?0:1;
    DISsetArgumentsMCRL(mcrlArgs, &j, &newargv, &argc);
    
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    if (!MCRLinitRW(j, newargv)) exit(1);
    output = calloc(nseg, sizeof(file_t));
    contextInitWrite(&SEDE_DATA(contextWrite, ticks), nseg);
    contextInitWrite(&SEDE_DATA(contextWrite, visits), nseg);
    contextInitWrite(&SEDE_DATA(contextWrite, backups), nseg);
    contextInitRead(&SEDE_DATA(contextRead ,input), vork.r);
    Init(mgrhost);
//    if (select_reg) log = OpenLog(seg);
    if (env->log) OpenInfo();
    init_state = DISexploreInitialState(st);
/* fprintf(stderr, "InitState [%d %d](%d) %d %d \n", init_state[0], init_state[1],
     init_state[2], env->K, env->tree); */
    int l = nodes?((int) init_state[2]):DISsegment(st, init_state);
    if (l==seg) {
       if (env->K==2 || !env->tree)
          memcpy(visited->dest, init_state, env->K*sizeof(elm_t));
       else UnfoldVector(visited->dest, init_state);
       init_state[0] = init_state[1] = UNDEF;
       }
    if (!eof) level = 1;
    Dinstantiate(visited);
    exit(EXIT_SUCCESS);
    }
    
