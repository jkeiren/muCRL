/* $Id: explore.c,v 1.32 2006/01/12 10:17:22 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#ifdef USE_BCG
#include "bcg_user.h"
#endif
#include "param0.h"
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include "utl.h"
#include <string.h>
#include "fifo.h"
#include "vector_db.h"
#include "term_db.h"
#include "mcrl.h"
#include "step.h"
#include "xlts.h"
#include <assert.h>
#define ACTSIZE 50000
#define INITSIZE 100
#define MAXFDS 100
#define MAXFILELENGTH 100000000

typedef int (*expl_cbt)(void *tag, act_t *act, elm_t *dest);
typedef int (*init_cbt)(void *tag, elm_t *elm);
typedef int (*fininit_cbt)(void *tag, int count);
typedef int (*finexpl_cbt)(void *tag, int count);
typedef void (*log_cbt)(FILE *user, elm_t *src, act_t *act, elm_t *dest);
typedef void (*read_cbt)(void *tag, elm_t *src);

typedef struct {
     int nseg, segment, write;
     expl_cbt  ecb;
     init_cbt  icb;
     finexpl_cbt fecb;
     fininit_cbt ficb;
     log_cbt  lcb;
     int width, n, *destsize, *rdesteof, *desteof;
     const char *srcdir;
     char *id;
     tdb_t labels, leafs;
     vdb_t *nodes;
     FILE **src, **rsrc, **dest,  **rdest, **act, **ract, **channel;
     fifo_t  *fifo, *fifo2, *src2;
     char **sname, **dname, **aname, **rsname, **rdname, **raname;
     FILE  *tmp;
     lts_t lts;
     int tickstring, deadlockstring;
     } step_r, *step_t;

elm_t deadlock_state[2];
     
static FILE *tty;
     
static elm_t *currentTo = NULL, *currentFrom; 

static int *pbce = NULL;
       
static act_t currentLabel;
       
static ATerm *src, *dest, label;

static fifo_t act_fifo, dest_fifo;

static step_t st;

static void* currentTag;
static int String2Act(step_t step, char *act) {
      ATerm t = (ATerm) ATmakeAppl0(ATmakeAFun(act, 0, ATtrue));
      return TDBput(step->labels, t,  NULL);
      }


static void swap(int *r, int p, int q) {
    int aux = r[p];
    r[p]=r[q];
    r[q]=aux;
    }
    
static int *Balance(int n) {
      int  m = 1, i, n2 = 2*n,
      *r = (int*) malloc(sizeof(int)*n2);
      for (i=0;i<n2;i++) r[i] = i; 
      for (m=1;m<n2;m*=2);
      m/=2;
      swap(r, m-1, n-1);
      return r;
      }
            
static void FoldNode(elm_t *dest) {
	int i;
	for (i=st->n-1;i>=2;i--) {
            int new;
            if ((dest[pbce[i]]=VDBput(st->nodes[i], dest+2*i, &new))<0)
               errormsg("FoldNode i = %d (%d, %d) r = %d", 
               i, dest[2*i], dest[2*i+1], dest[i]);
            /* printmsg("pbce[%d]= %d dest[%d]=%d  dest[%d=%d",
            i, pbce[i], 2*i, dest[2*i], 2*i+1, dest[2*i+1]); */
	    }
        /* fprintf(stderr, "DBSfold (%d, %d) n = %d\n",
         dest[2], dest[3], n); */
        }
               
static void UnfoldNode(elm_t *src) {
	int i;
	for(i=2;i<st->n;i++) {
          if (VDBget(st->nodes[i], src+2*i, src[pbce[i]])<0) {
              errormsg("Unfold node %d (%d>%d)",i, src[i],
              VDBgetCount(st->nodes[i]));
              }
	}
       /* fprintf(stderr, "QQ: DBSunfold (%d %d)\n", src[2], src[3]); */
}

static void Fold(ATerm *v, elm_t *dest) {
         int i, new, n= st->n;
         if (n>1) {
           for (i=0;i<n;i++) {
               TDBsetId(st->leafs,n+i+2);
               dest[pbce[n+i]] = TDBput(st->leafs, v[i], &new);
               }
           FoldNode(dest);
           }
         else {
            TDBsetId(st->leafs,n+2);
            dest[2] = TDBput(st->leafs, v[0], &new);
            }
         } 

static void Unfold(elm_t *dest, ATerm *v) {
         int i, n = st->n;
         if (n>1) {
           UnfoldNode(dest);
           for (i=0;i<n;i++) v[i] = TDBget(st->leafs, dest[pbce[n+i]]);
           }
         else v[0] = TDBget(st->leafs, dest[2]);
         }          
       
int STmapNodeId(int id, int pos, int n) {
      if (!pbce) pbce = Balance(n);
      return (2*id+pos<2*n?pbce[2*id+pos]:0); /* n<npars Node n>=npars Leaf */;
      } 
                                  
static void callback() {
     int new;
     Fold(dest, currentTo);
     currentLabel.lab = TDBput(st->labels, label, &new);
     currentLabel.smd = STgetSmdIndex();
     // printmsg("callback");
     if (st->ecb && currentLabel.lab != st->tickstring) 
                  st->ecb(currentTag, &currentLabel, currentTo+2);
     if (st->nseg>0) {
       FIFOput(dest_fifo, currentTo+2); 
       FIFOput(act_fifo, &currentLabel);
       }
     }

static FILE *LogOpen(char *dir, char *name, char *mod, char **outname) {
   FILE *file = NULL;
   char fname[256];
   if (CreateEmptyDir(dir, DELETE_NONE)<0)
     errormsg("Cannot create directory %s", dir);
   sprintf(fname,"%s/%s", dir, name);
   if (mod) {
      if ((file = fopen(fname,mod))==NULL) errormsg("file \"%s\"", fname);
      // fprintf(stderr,"Open name = %s file = %lx\n", fname, file); 
      rewind(file);
      }
   if (outname) *outname = strdup(fname);
   if (getenv("MCRL_BUFSIZE")) {
       int bsize = atoi(getenv("MCRL_BUFSIZE"));
       char *bb = malloc(bsize);
       if (!bb) errormsg("IO buffer: size %d", bsize);
       setbuffer(file, bb, bsize);
       }
   return file;
   }  

/*   
static int lastExplored(FILE *file, int length) {
    int  pos, pos0 = 0;
    elm_t elm[2], elm0[2];
    elm0[0] = elm0[0] = -1;
    rewind(file);
    while (((pos=ftell(file)),readPair(file,elm))) {
        if (ftell(file)>=length) break;
        // printmsg("(%d %d) (%d %d)",  elm0[0], elm0[1], elm[0], elm[1]);
        if (elm0[0]!=elm[0] || elm0[1] != elm[1]) {
            elm0[0] =elm[0]; elm0[1] = elm[1];
            pos0 = pos;
            }
        }
    return pos0;
    }
*/
     
int *STtruncateEqual(step_t st, FILE **f) {
    int i, nseg = st->nseg, rec_size = getRecordSize();
    if (!st->src) return 0;
    for (i=0;i<nseg;i++) {
       int siz[4], len = 1000000000, j, trunc; 
       siz[0] = FileLen(st->src[i]);
       siz[1] = FileLen(st->act[i]);
       siz[2] = FileLen(st->dest[i]);
       siz[3]=(f&&f[i])?FileLen(f[i]):len;
       for (j=0;j<4;j++) len = siz[j]<len?siz[j]:len;
       trunc = len/rec_size; trunc = trunc*rec_size;
/* printmsg("TruncateEqual seg = %d (%d %d %d %d) %d -> %d)",
       i, siz[0], siz[1], siz[2],siz[3], len, trunc); */
     /* printmsg("TruncateEqual seg = %d rec_size = %d)",
       i,  rec_size); */
       Ftruncate(st->dest[i], trunc);
       Ftruncate(st->src[i], trunc);
       Ftruncate(st->act[i], trunc); 
       st->desteof[i] = trunc;
       if (f) {
          int m = FileLen(f[i]);
          if (m>=trunc) Ftruncate(f[i], trunc);
          }
       }
    return st->desteof;
    }
    
 int *STdefineRdesteof(step_t step) { 
    int i, nseg = step->nseg;  
    if (!step->rdest) return 0;        
    for (i=0;i<nseg;i++) {
    // printmsg("QQQ %d: %lx", i, step->rdest[i]);
    if (step->rdest[i]) {
         // printmsg("QQQ %d:", FileLen(step->rdest[i]));
         step->rdesteof[i]=FileLen(step->rdest[i]);
	 }
    }
    return step->rdesteof;
    }
      
int STreset(step_t st) {
    int i;
    for (i=0;i<st->nseg;i++) {
       Truncate(st->sname[i], 0);
       Truncate(st->dname[i], 0);
       Truncate(st->aname[i], 0);
       }
    return 0;
    }
    
static int EndReached(FILE *f) {
     elm_t elm[2];
     elm[0]=elm[1]=-2;
     if (FileLen(f)==ftell(f)) return ftell(f);  
     // printmsg("1: End reached %d", ftell(f));
     while (readPair(f, elm) && elm[0]!=-1);
     return ((elm[0]==-2 && elm[1]==-2) || (elm[0]>=0 && elm[1]>=0))?
         ftell(f):-1;
     }

static int convert2Argv(char *args, char ***argv) {
     char *arg;
     int cnt=0, i;
     if (!args) return 0;
     args = strdup(args);
     for (arg=strtok(args," ");arg;arg=strtok(NULL," ")) 
        if (strlen(arg)>0) {
             cnt++;
             }
     *argv = (char**) malloc((cnt)*sizeof(char*));
     for (i=0;i<cnt;args+=(strlen(args)+1), i++) {
        if (args[0]=='\b'&&i==(cnt-1)) {
             /* (cnt-1) is file name */
             args[0]='\0';
             (*argv)[i] = args;
             }
         else
            if (strlen(args)>0) (*argv)[i] = args;
        }
     return cnt;
     } 
     
void STsetArgumentsMCRL(char *args, int *nargs, char ***argv) {
     if (args) *nargs = convert2Argv(args, argv);
     if (*nargs>0) {
         STsetArguments(nargs, argv);
	 }
     } 

static void AllocMem(step_t step) {
     if (step->nseg>0) {
         int nseg = step->nseg;
         if (!step->src) step->src = (FILE**) malloc(nseg*sizeof(FILE*));
         if (!step->rsrc) step->rsrc = (FILE**) malloc(nseg*sizeof(FILE*));
         if (!step->dest) step->dest = (FILE**) malloc(nseg*sizeof(FILE*));
         if (!step->rdest) step->rdest = (FILE**) malloc(nseg*sizeof(FILE*)); 
         if (!step->act) step->act = (FILE**) malloc(nseg*sizeof(FILE*));
         if (!step->ract) step->ract = (FILE**) malloc(nseg*sizeof(FILE*));
         if (!step->sname) step->sname = (char**) malloc(nseg*sizeof(char*));
         if (!step->aname) step->aname = (char**) malloc(nseg*sizeof(char*));
         if (!step->dname)step->dname = (char**) malloc(nseg*sizeof(char*));
         if (!step->rdname) step->rdname = (char**) malloc(nseg*sizeof(char*));
         if (!step->rsname) step->rsname = (char**) malloc(nseg*sizeof(char*));
         if (!step->raname) step->raname = (char**) malloc(nseg*sizeof(char*));
         if (!step->destsize) step->destsize = (int*) calloc(nseg, sizeof(int));
         if (!step->rdesteof) step->rdesteof = (int*) calloc(nseg, sizeof(int));
         if (!step->desteof) step->desteof = (int*) calloc(nseg, sizeof(int));
         }
     }
                                 
step_t STcreateMCRL(int segment, dir_t  srcdir, int state_size,  tdb_t labels, tdb_t leafs, vdb_t *nodes,
     expl_cbt ecb, init_cbt icb, finexpl_cbt fecb, fininit_cbt ficb, log_cbt
     lcb, int nseg, dir_t *destdir, char *args) {
     step_t step;
     int n = MCRLgetNumberOfPars(), i;
     char dname[256];
     deadlock_state[0]=0; deadlock_state[1]=DEADLOCK;
     tty = fopen("/dev/tty", "w");
     if (!(step = (step_t) calloc(1, sizeof(step_r)))) {
        mkerror(ERR_NULL, "Cannot allocate dbs (size = %d)",
        sizeof(step_r)); return NULL;}
     st = step;
     step->nseg = nseg;
     step->segment = segment;
     if (!pbce) pbce = Balance(n);
     step->n = n;
     step->ecb = ecb; step->icb = icb; 
     step->fecb = fecb; step->ficb = ficb;
     step->lcb = lcb;
     step->width = state_size;
     step->labels = labels; step->leafs = leafs; 
     step->nodes = nodes;
     if (srcdir) {
       char **ids = nseg>0?(char**) malloc(nseg*sizeof(char*)):(char**) NULL;
       sprintf(dname, "%s/%s", srcdir, "src");
       step->srcdir = strdup(dname);
       
       step->id = strrchr(srcdir,'/')+1; 
       if (destdir) {
         AllocMem(step);
         step->write = 1;
         for (i=0;i<nseg;i++) {
             dir_t path = destdir[i];
             /* .../<home>.i/dest/<from>.id */
             sprintf(dname, "%s/%s", path, "dest");
             step->dest[i] = LogOpen(dname, step->id, "a+", step->dname+i);
	     /*
             sprintf(dname, "%s/%s", path, "src");
             step->rsrc[i] = LogOpen(dname, step->id,"a+", step->rsname+i);
	     */
             sprintf(dname, "%s/%s", path, "act");
             step->act[i] = LogOpen(dname, step->id, "a+", step->aname+i);
             ids[i] = strrchr(path,'/')+1;
             if (segment==-1 && !strcmp(ids[i], step->id)) {
                 step->segment = i;
                 // printmsg("segment = %d (%s)", i, ids[i]);
                 }
             }
          /* .../<home>.id/src/<to>.i */
          sprintf(dname, "%s/%s", srcdir, "src");
          for (i=0;i<nseg;i++) {
             step->src[i] = LogOpen(dname, ids[i],"a+", step->sname+i);
             } 
	  /*
          sprintf(dname, "%s/%s", srcdir, "act");
          for (i=0;i<nseg;i++) {
             step->ract[i] = LogOpen(dname, ids[i],"a+", step->raname+i);
             }
	  */
          sprintf(dname, "%s/%s", srcdir, "dest");
          for (i=0;i<nseg;i++) {
             /* char buf[80]; */
             step->rdest[i] = LogOpen(dname, ids[i], "a+", step->rdname+i);
             step->rdesteof[i]=FileLen(step->rdest[i]);
             }
           }
            
        } else {
	    sprintf(dname,"stepper.%d", step->segment);
	    step->id=strdup(dname);
	    }
     if (!currentTo) {
        if (!(currentTo = (elm_t*) calloc(2*n, sizeof(elm_t)))) {
           mkerror(ERR_NULL, "Cannot allocate currentTo (size = %d)",
           2*n); return NULL;}
        if (!(currentFrom = (elm_t*) calloc(2*n, sizeof(elm_t)))) {
           mkerror(ERR_NULL, "Cannot allocate currentFrom (size = %d)",
           2*n); return NULL;}
        if (!(src = (ATerm*) calloc(n, sizeof(ATerm)))) {
           mkerror(ERR_NULL, "Cannot allocate src (size = %d)",
           n); return NULL;}
        if (!(dest = (ATerm*) calloc(n, sizeof(ATerm)))) {
           mkerror(ERR_NULL, "Cannot allocate dest (size = %d)",
           n); return NULL;}
        ATprotect(&label); ATprotectArray(src, n); ATprotectArray(dest, n);  
        STinitialize(enumOccurrenceOrdering, &label, dest, callback);
        dest_fifo = FIFOcreateMemo(INITSIZE, 2*sizeof(elm_t), NULL, NULL);
        act_fifo = FIFOcreateMemo(INITSIZE, sizeof(act_t), NULL, NULL);
        }
     if (step->nseg>0 && !step->fifo) 
         step->fifo = (fifo_t*) calloc(step->nseg, sizeof(fifo_t));
     for (i=0;i<step->nseg;i++)
     if (!step->fifo[i])
            step->fifo[i]= FIFOcreateMemo(100, 2*sizeof(elm_t), NULL, NULL);
     step->tickstring = -1;
     return step;
     }

int STcreateTickLevel(step_t step) {  
     int i;  
     if (!step->fifo2) step->fifo2 = (fifo_t*) calloc(step->nseg, sizeof(fifo_t));
     if (!step->src2) step->src2 = (fifo_t*) calloc(step->nseg, sizeof(fifo_t));
     for (i=0;i<step->nseg;i++) {
          if (!step->fifo2[i])
            step->fifo2[i]= FIFOcreateMemo(100, 2*sizeof(elm_t), NULL, NULL);
	  if (!step->src2[i])
             step->src2[i]= FIFOcreateMemo(100, 2*sizeof(elm_t), NULL, NULL);
	  }
     return step->tickstring = String2Act(step, "tick");
     }

int STgetCountTickBuffers(step_t step) {
     int k, r = 0;
     if (!step->fifo2)  return 0;
     for (k=0;k<step->nseg;k++) {
        int m = FIFOgetCount(step->fifo2[k]);
        // fprintf(stderr, "%d ", m);
        r += m;
        }
     // fprintf(stderr,"\n");
     return r;
     }
          
step_t STcreateAUT(char *filename, tdb_t labels,  
expl_cbt ecb, init_cbt icb, finexpl_cbt fecb, fininit_cbt ficb) {
     step_t step;
     tty = fopen("/dev/tty", "w");
     if (!(step = (step_t) calloc(1, sizeof(step_r)))) {
        mkerror(ERR_NULL, "Cannot allocate dbs (size = %d)",
        sizeof(step_r)); return NULL;}
     step->ecb = ecb; step->icb = icb; 
     step->fecb = fecb; step->ficb = ficb;
     step->labels = labels;
#ifdef USE_BCG
     BCG_INIT();
#endif
     step->lts=lts_create();
     lts_read(LTS_AUTO, filename,step->lts);
     lts_bfs_reorder(step->lts);
     lts_set_type(step->lts,LTS_LIST);
     ATprotect(&label); 
     return step;
     }
    
static int Segment(step_t st, elm_t *dest) {
     int i, s = 0;
     for (i=0;i<st->width;i++) s+=dest[i];
     return (s>0?s:-s)%st->nseg;
     } 
     
int STsegment(step_t st, elm_t *dest) {
     return Segment(st, dest);
     } 
         
int STsend(step_t step, int stepno) { 
     FILE *channel = step->channel[2*stepno+1];
     if (channel) {
        elm_t elm[2];
        while (FIFOget(step->fifo[stepno], elm)>=0) {
            writePair(channel, elm);
            /* printmsg("STsend segment %d=> %d: (%d, %d)", 
            st->segment, stepno, elm[0], elm[1]); */
            if (elm[0]==-1) break;
            }
        fflush(channel);
        }
     return 0;
     }
     
int IsTick(act_t act) {
     return act.lab==st->tickstring; 
     }

static void PutCandidateForExploration(step_t step, elm_t *src, act_t *act, elm_t *dst) { 
     int seg = Segment(step, dst); 
     // printmsg("Put %d (%d %d)", seg, elm[0], elm[1]);
     FIFOput(step->fifo[seg], dst);
     if (step->write) {
             writePair(step->src[seg], src);
             // fflush(step->src[seg]);
             // printmsg("id: %s seg:%d ftell: %d", step->id, seg,
             // ftell(step->dest[seg]));
             step->destsize[seg]+=writePair(step->dest[seg], dst);
             // fflush(step->dest[seg]);

             writePair(step->act[seg], (elm_t*) act);
             // fflush(step->act[seg]);
             // if (step->rdest) step->rdest[seg]=NULL;
             }
     }

int STdiscover(step_t step, void *tag, elm_t *elm) {
     int count; 
     st = step;
     currentFrom[2] = elm[0]; currentFrom[3] = elm[1];
     Unfold(currentFrom, src);
     /* ATfprintf(tty,"STexplore befor (%t, %t)\n", src[0], src[1]); */
     count = STstep(src);
     /* ATfprintf(tty, "STexplore: cnt = %d (%t, %t)\n", count, src[0], src[1]); */
     if (count<0) return mkerror(ERR_NULL,"Error found during exploration");
     }  
                           
int STexplore(step_t step, void *tag, elm_t *elm) {
     int count = 0, count1 = 0;
     static int first = 0;
     currentTag = tag;
     if (step->lts==NULL) {
        st = step;
        currentFrom[2] = elm[0]; currentFrom[3] = elm[1];
        Unfold(currentFrom, src);
        /* ATfprintf(tty,"STexplore befor (%t, %t)\n", src[0], src[1]); */
        count = STstep(src);
        /* ATfprintf(tty, "STexplore: cnt = %d (%t, %t)\n", count, src[0], src[1]); */
        if (count<0) return mkerror(ERR_NULL,"Error found during exploration");
        }
     else {
        lts_t lts = step->lts;
        int src = *((int*) tag), transitions = lts->transitions;
        for (;first<transitions && lts->src[first]==src;first++) {
            currentLabel.lab = String2Act(step, lts->label_string[lts->label[first]]);
            currentLabel.smd = first;   
            step->ecb(currentTag, &currentLabel, (elm_t*) lts->dest+first);
            count++;
            }
        }
     if (step->nseg>0) {
        int i;
          for (i=0;i<count;i++) {
          elm_t dest[2]; act_t act;
          FIFOget(dest_fifo, &dest); FIFOget(act_fifo, &act);
          if (step->fifo2) { 
             if (IsTick(act)) {
                 int seg = Segment(step, dest);
                 FIFOput(step->fifo2[seg], dest);
                 FIFOput(step->src2[seg], elm);
                 /* No deadlock: tick is encountered */
                 tag = NULL;
	       }
             else {
                  PutCandidateForExploration(step, elm, &act, dest);
                  count1++;
                  }
             }
	   else {
/* if (step->segment==0) printmsg("Explore seg = %d %d width = %d (%d,%d)", seg, st->nseg, 
          st->width, dest[0], dest[1]); */
            count1++;
            PutCandidateForExploration(step, elm, &act, dest);
            }
	   }
          if (count==0) {
              if (!step->deadlockstring) 
                    step->deadlockstring = String2Act(step, "#deadlock#");
              {
              act_t act = {DEADLOCK, 0};
              int seg = step->segment;
	      if (step->write) {
                writePair(step->src[seg], elm);
                writePair(step->act[seg], (elm_t*) &act);
                step->destsize[seg]+=writePair(step->dest[seg], deadlock_state);
	        }
              FIFOput(step->fifo[seg], deadlock_state);
              /* Added transition "deadlock" to deadlock_state */
              }
              }
          } else count1 = count;
     return step->fecb?step->fecb(tag, count1):0;  
     }

int STinRdestFile(step_t step) {
     int nseg = step->nseg, r = 0, i;
     for (i=0;i<nseg;i++) {
       FILE *rdest = step->rdest?step->rdest[i]:NULL;
       int rdesteof = step->rdesteof?step->rdesteof[i]:0;
       r |= rdest && ftell(rdest)>=0 && ftell(rdest)<rdesteof;
       }
     return r;
     }
        
int STread(step_t step, step_t *sta, void *tag, read_cbt read_cb,  int stepno) {
     int  cnt = 0, segment = step->segment;
     step_t stepfrom = sta?sta[stepno]:step;
     st = step;
     /* printmsg("STread start"); */
        {
        FILE *channel = st->channel?st->channel[2*stepno]:NULL, 
        *rdest = step->rdest?step->rdest[stepno]:NULL;
        int rdesteof = step->rdesteof?step->rdesteof[stepno]:0;
        int fromfile = rdest && ftell(rdest)>=0 && ftell(rdest)<rdesteof,
        fromfile0 = fromfile;
        elm_t elm[2]; elm[0]=-2;
/* if (rdest) fprintf(stderr, "seg %d from %d STread1 %d < %d=%d\n", 
segment, stepno, ftell(rdest), FileLen(rdest), rdesteof); 
else fprintf(stderr,"rdest = NULL\n"); */
        if (rdest) {
        for (;fromfile && (readPair(rdest, elm), elm[0])!=-1;
               fromfile = ftell(rdest)>=0&&ftell(rdest)<rdesteof) {
             // fprintf(stderr, "STread2 %d < %d\n", ftell(rdest), rdesteof);
             if (read_cb) read_cb(tag, elm); 
             if (elm[1]>=0) cnt++;
             }
	  if (ftell(rdest)>=rdesteof) {
/* fprintf(stderr, "Close by %d: from %d %d>=%d\n", segment, stepno,
               ftell(rdest), rdesteof); */
               fclose(rdest);step->rdest[stepno]=NULL;
               }
	  }
/* if (rdest) fprintf(stderr, "STread3  %d %d (%d)\n", 
          ftell(rdest), rdesteof, elm[0]); */
        if (elm[0]!=-1) {
        if (channel) {
             while ((readPair(channel, elm),elm[0])>=0) {
// fprintf(stderr,"channel(%d, %d)\n", elm[0], elm[1]);
               if (read_cb) read_cb(tag, elm);
               /* if (elm[1]!=deadlock_state[1]) cnt++; */
               }
           }
        else {
          /* printmsg("segment = %d stopne = %d (%d %d counmt = %d)", 
          segment, stepno, stepfrom, stepfrom->fifo, 
          FIFOgetCount(stepfrom->fifo[segment])); */ 
          while ((FIFOget(stepfrom->fifo[segment], elm), elm[0])>=0) {
             if (read_cb) read_cb(tag, elm);
             /* if (elm[1]!=deadlock_state[1]) cnt++; */
             if (elm[0]==-1) break;
             }
          /* printmsg("segment3 = %d stopne = %d (%d)", 
             segment, stepno, stepfrom); */
          /* if (elm[0]!=-1) 
            errormsg("System error (%s, %d) elm[0]!=%d ! -1",step->id, i, elm[0]);
          */
          }
        } 
     /* printmsg("STread end"); */
     return fromfile0?cnt:0; 
     } 
     }

         
int STendLevel(step_t step) {
     static int marker[]={-1,-1}; int i, r = 0; 
     st = step;
     for (i=0;i<step->nseg;i++) {
        if (!step->write || EndReached(step->dest[i])>=0) {
	  // printmsg("Ffoput %d (%d)", i, FIFOgetCount(step->fifo[i]));
          FIFOput(step->fifo[i], marker); 
          if (step->write) {
            step->destsize[i]+=writePair(step->dest[i], marker);
            writePair(step->src[i], marker);
            writePair(step->act[i], marker);
            // fflush(step->src[i]);fflush(step->dest[i]);fflush(step->act[i]);
	    r = 1;
            }
          }
       }
       return r;
       }
       
char *STid(step_t step) {
     return step->id;
     }

lts_t STgetLTS(step_t step) {
     return step->lts;
     }
     
int STproceedNextTickLevel(step_t step) {
     int i, cnt = 0;
     elm_t src[2], dst[2];
     act_t act;
     act.lab = step->tickstring; act.smd = 0;
     if (!step->fifo2) return 0;
     for (i=0;i<step->nseg;i++) {
        FIFOreset(step->fifo[i]);
        while (FIFOget(step->src2[i], src)>=0
              && FIFOget(step->fifo2[i], dst)>=0) {
	   if (step->ecb) step->ecb(src, &act, dst);
           PutCandidateForExploration(step, src, &act, dst);
	   cnt++;
           }
        }
     return cnt;
     }
               
int STexploreInitialState(step_t step, void *tag) {
     int seg  = 0;
     if (step->lts==NULL) {
       st = step;
       STsetInitialState();
       // fprintf(stderr,"Fold\n");
       Fold(dest, currentTo);
       // fprintf(stderr,"End Fold\n");
       if (step->nseg>0) {
          elm_t elm[] =  {-2,-2};
          PutCandidateForExploration(step, elm, (act_t*) &elm, currentTo+2);
          }
       if (step->icb)
       if (step->icb(tag, currentTo+2)<0) errormsg("StexploreInitialState");
       }
     else {
       lts_t lts = step->lts;
       if (step->icb)
       if (step->icb(tag, (elm_t*) &(lts->root))<0) errormsg("StexploreInitialState");
       }  
     return step->ficb?step->ficb(tag, 1):seg;
     }
     
elm_t *STfold(step_t step, term_t *data) {
     st = step;
     Fold(data, currentTo);
     return currentTo+2;
     } 
     
term_t *STunfold(step_t step, elm_t *data) {
     st = step;
     memcpy(currentTo+2, data, sizeof(elm_t)*2);
     Unfold(currentTo, dest);
     return dest;
     } 
     
int STconnect(step_t step, FILE** channel) { 
     step->channel = channel;
     return 0;
     }
     
FILE *STgetChannel(step_t step, int idx) {
     return step->channel[idx];
     }
     
int STgetWidth(step_t step) {return step->width;}

int STgetDestFiles(step_t step, dir_t **dirs, int *siz) {
     int n = step->nseg, i;
     dir_t *r;
     *siz = 3*n;
     if (step->sname) {
     *dirs= r = (dir_t*) calloc(*siz, sizeof(dir_t));
     for  (i=0;i<n;i++) {
        r[3*i]=step->sname[i];
        r[3*i+1]=step->aname[i];
        r[3*i+2]=step->dname[i];
        }
     } else *dirs = NULL;
     return 0;
     }

int STgetSrcFiles(step_t step, dir_t **dirs, int *siz) {
     int n = step->nseg, i;
     dir_t *r;
     *siz = 3*n;
     *dirs= r = (dir_t*) calloc(*siz, sizeof(dir_t));
     if (step->rsname) {
     for  (i=0;i<n;i++) {
        r[3*i]=step->rsname[i];
        r[3*i+1]=step->raname[i];
        r[3*i+2]=step->rdname[i];
        }
     } else dirs = NULL;
     return 0;
     }

FILE *STgetActFile(step_t step, int dest_segment) {
     return step->act[dest_segment];
     }
     
FILE *STgetDestFile(step_t step, int dest_segment) {
     return step->dest[dest_segment];
     }
     
const char *STgetSrcDir(step_t step) {return step->srcdir;}
          
void SThelpMCRL(void) {SThelp();}

int STgetSegment(step_t step) {return step->segment;}
/*
int STdestroy(step_t st);
*/
