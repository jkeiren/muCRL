/* $Id: discover.c,v 1.9 2007/11/22 12:39:46 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#define DISCOVER_C
#ifdef USE_BCG
#include "bcg_user.h"
#endif
#include "param0.h"
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <assert.h>
#include <libgen.h>
#include "utl.h"
#include <string.h>
#include "fifo.h"
#include "vector_db.h"
#include "term_db.h"
#include "step.h"
#include "mgr.h"
#include "rw.h"
#include "xlts.h"

#define ACTSIZE 50000
#define INITSIZE 100
#define MAXFDS 100
#define MAXFILELENGTH 100000000

/* @file
    Implementation of SEDEread and SEDEwrite.
*/
typedef int (*expl_cbt)(elm_t *src, act_t *act, elm_t *dest);
typedef int (*finexpl_cbt)(unexplored_t *src, int count);

typedef struct {
     int nseg, segment, width, npars, local;
     expl_cbt  ecb;
     finexpl_cbt fecb;
     tdb_t labels, leafs;
     vdb_t *nodes;
     } step_r, *step_t;
 
static AFun times, mod, divv, minus, plus, min;

static int K;

static size_t size;
        
static FILE *tty;
     
static elm_t *currentTo = NULL, *currentFrom, currentIdx; 

static int *pbce = NULL;
       
static act_t currentLabel;
       
static ATerm *src, *dest, label;

static step_t st;

static void* currentTag;

static tdb_t *pardb;

#include "sede.h"

typedef elm_t *state_t;

/* 
    Writes a state by calling @c callback which is a member of 
    @c contextWrite_t.
    @param state *visited_t
    @param wc   .data contextWrite_t
*/    
int SEDEwrite(void *state_p, void *wc) {
   state_t state = (state_t) state_p;
   int val = SEDE_CALLBACK(wc)(size, state, wc);
   // fprintf(stderr,"SedeWrite size = %d\n", size);
      if (val==size) return 0;
      if (val==0) return EOF; 
      errormsg("SEDEwrite:Illegal write val = %d", val);
      return 0;
   }
   
/*
    Reads a state by calling @c callback which is a member of 
    @c contextRead_t.
    @param state **unexplored_t
    @param rc  .data contextRead_t
*/    
int SEDEread(void **state_p, void *rc) { 
   state_t *state = (state_t*) state_p;
   int val;
   // if (!(*state)) *(state) = (state_t*) malloc(sizeof(state_t));
   val = SEDE_CALLBACK(rc)(size, *state, rc);
   if (val == size) return 0;
   if (val == 0)  return EOF; 
   errormsg("SEDEread:Illegal read val = %d", val);
   return 0;
   } 
   
/* End of implementation */
  
static int String2Act(step_t step, char *act) {
      int new;
      ATerm t = (ATerm) ATmakeAppl0(ATmakeAFun(act, 0, ATtrue));
      return TDBput(step->labels, t,  &new);
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
      if (K>2 || n<=2) return r; 
      for (m=1;m<n2;m*=2);
      m/=2;
      swap(r, m-1, n-1);
      return r;
      }

static int Segment(step_t st, elm_t *dest) {
     int i, s = 0;
     for (i=0;i<st->width;i++) s+=dest[i];
     return (s>0?s:-s)%st->nseg;
     }
     
static int SegmentLocal(step_t st, elm_t *dest) {
     int i, s = 0, n = st->npars;
     for (i=0;i<n;i++) s+=dest[pbce[n+i]];
     return (s>0?s:-s)%st->nseg;
     }
                 
static void FoldNode(elm_t *dest) {
	int i;
	for (i=st->npars-1;i>=K;i--) {
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
	for(i=K;i<st->npars;i++) {
          if (VDBget(st->nodes[i], src+2*i, src[pbce[i]])<0) {
              errormsg("Unfold node %d (%d>%d)",i, src[pbce[i]],
              VDBgetCount(st->nodes[i]));
              }
	}
       /* fprintf(stderr, "QQ: DBSunfold (%d %d)\n", src[2], src[3]); */
}

void UnfoldVector(elm_t *dest, elm_t *src) {
      int i, n = st->npars;
      DECLA(elm_t, a, 2*n);
      if (src[0]<0 || src[1]<0) {
          dest[0] =src[0];
	  dest[1] = src[1];
	  return;
	  }
      memcpy(a+2, src, 2*sizeof(elm_t));
      UnfoldNode(a);
      for (i=0;i<n;i++) {
         dest[i] = a[pbce[n+i]];
	 }
      }

void FoldVector(elm_t *dest, elm_t *src) {
      int i, n = st->npars;
      // fprintf(stderr,"Fold Vector\n");
      for (i=0;i<n;i++) {
         // fprintf(stderr,"%d ", src[i]);
         dest[pbce[n+i]] = src[i];
	 }
      FoldNode(dest);
      // fprintf(stderr,"[%d %d]\n", dest[2], dest[3]);
      }

      
static void Fold(ATerm *v, elm_t *dest) {
         int i, new, n= st->npars, checksum;
         if (n>1) {
           for (i=0;i<n;i++) {
               /* int idx = TDBput(st->leafs, v[i], &new);
               if (idx<0) errormsg("TDBput"); */
               TDBsetId(st->leafs,n+i+2);
               assert(v[i]!=NULL);
               if ((dest[pbce[n+i]] = TDBput(st->leafs, v[i], &new))<0)
                  errormsg("TDBput");
		// fprintf(stderr,"End TDBput %d\n", st->segment);
/*
               TDBput(pardb[i], v[i], &new);
               if ((dest[pbce[n+i]] = TDBput(st->leafs, v[i], new?NULL:&new))<0)
                  errormsg("TDBput");
*/
               }
	   // fprintf(stderr,"Start FoldNode");
           if (st->local) checksum = SegmentLocal(st, dest);
           FoldNode(dest);
           if (!st->local) checksum = Segment(st, dest+2);
           dest[4] = checksum;
	   /* fprintf(stderr,"End FoldNode %d [%d %d] %d", 
              st->segment, dest[2], dest[3], dest[4]); */
           }
         else {
            TDBsetId(st->leafs,n+2);
            dest[2] = TDBput(st->leafs, v[0], &new);
            }
         // for (i=K;i<2*K;i++) fprintf(stderr,"%d ", dest[i]);
         // fprintf(stderr,"End Fold\n");
         } 

static void Unfold(elm_t *dest, ATerm *v) {
         int i, n = st->npars;
         if (n>1) {
           UnfoldNode(dest);
           for (i=0;i<n;i++) {
               // fprintf(stderr,"QQB Unfold %d dest[%d]= %d\n", i, pbce[n+i], dest[pbce[n+i]]);
	       // fprintf(stderr,"Start TDBget\n");
               v[i] = TDBget(st->leafs, dest[pbce[n+i]]);
	       // fprintf(stderr,"End TDBget\n");
               // ATfprintf(stderr,"QQB Value = %t\n", v[i]);
               }
           }
         else v[0] = TDBget(st->leafs, dest[2]);
         } 
         
#ifdef MCRL
static int Cdub(ATerm arg) {
         return ATisEqual(arg, MCRLterm_true)?1:0;
         }
                 
static int processNat(ATerm arg) {
        int result;
        DECLA(char, name, 6);
        strncpy(name, MCRLgetName(arg), 5); name[5]='\0';
        if (!strncmp(name, "x2p0", 5))
                result = 2*processNat(ATgetArgument((ATermAppl)arg, 0));
        else if (!strncmp(name, "x2p1", 5) )
                result = 2*processNat(ATgetArgument((ATermAppl)arg, 0))+1;
        else if (!strncmp(name, "x2p2", 5))
                result = 2*processNat(ATgetArgument((ATermAppl)arg, 0))+2;
        else if (!strncmp(name, "S", 1) || !strncmp(name, "succ", 4))
                result = processNat(ATgetArgument((ATermAppl)arg, 0))+1;
        else if (!strncmp(name, "-cdub", 5))  
               processNat(ATgetArgument((ATermAppl)arg, 1))
                       + Cdub(ATgetArgument((ATermAppl)arg, 0));
        else if (!strncmp(name, "one", 3)) result = 1;
        else if (!strncmp(name, "-c1", 3)) result = 1;
        else result = atoi(name);
        return result;
        }

static int Evaluate(ATerm t) { 
        if (ATgetType(t)==AT_APPL) {
          if (ATisQuoted(ATgetAFun(t))) return processNat(RWrewrite(t));
          else {
             AFun s = ATgetAFun(t);
             if (s==min) return -Evaluate(ATgetArgument((ATermAppl) t, 0));
             if (s==plus) return Evaluate(ATgetArgument((ATermAppl) t, 0))
                        +Evaluate(ATgetArgument((ATermAppl) t, 1));
             if (s==minus) return Evaluate(ATgetArgument((ATermAppl) t, 0))
                        -Evaluate(ATgetArgument((ATermAppl) t, 1));
             if (s==times) return Evaluate(ATgetArgument((ATermAppl) t, 0))
                        *Evaluate(ATgetArgument((ATermAppl) t, 1));
             if (s==divv) return Evaluate(ATgetArgument((ATermAppl) t, 0))
                        /Evaluate(ATgetArgument((ATermAppl) t, 1));
             if (s==mod) return Evaluate(ATgetArgument((ATermAppl) t, 0))
                        %Evaluate(ATgetArgument((ATermAppl) t, 1));
             return 0;
             } 
         } 
         else return ATgetInt((ATermInt) t);
        }  
                        
int DISevaluate(char *e) {
         ATerm t = ATreadFromString(e);
         int r =  Evaluate(t);
         return r;
         }
#endif
                
int DISmapNodeId(int id, int pos, int n) {
      if (!pbce) pbce = Balance(n);
      return (2*id+pos<2*n?pbce[2*id+pos]:0); /* n<npars Node n>=npars Leaf */;
      } 
                                  
static void callback() {
     int new;
     // fprintf(stderr,"callback Befor Fold %d\n", st->segment);
     Fold(dest, currentTo);
     // fprintf(stderr,"callback AFter Fold %d\n", st->segment);
     currentLabel.lab = TDBput(st->labels, label, &new);
     // fprintf(stderr,"callback AFter TDBput\n");
     currentLabel.smd = currentIdx;
     if (st->ecb) st->ecb(currentTag, &currentLabel, currentTo+K);
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
        if (args[0]=='.'&&i==(cnt-1)) {
             /* (cnt-1) is file name */
             args[0]='\0';
             (*argv)[i] = args;
             }
         else
            if (strlen(args)>0) (*argv)[i] = args;
        }
     return cnt;
     } 
         
char *DISsetArgumentsMCRL(char *args, int *nargs, char ***argv, void *topStack) {
      char *r = NULL;
      if (topStack) {
        *nargs = convert2Argv(args, argv);
         ATinit(*nargs, *argv, (ATerm*) topStack);
         }
     if (*nargs>0) {
         char *ch;
         r = strdup(basename(strdup(((*argv)[*nargs-1])+1)));
         if ((ch=strrchr(r,'.'))) *ch='\0';
         STsetArguments(nargs, argv);
         // fprintf(stderr,"r=%s\n", r);
	 }
     return r;   
     } 
                                 
step_t  DIScreateMCRL(int segment, int nseg, int k, int local, tdb_t labels, tdb_t leafs, vdb_t *nodes,
     expl_cbt ecb, finexpl_cbt fecb) {
     int n, i;
     step_t step;
     K = k;
     size = K*sizeof(elm_t);
     tty = fopen("/dev/tty", "w");
     if (!(step = (step_t) calloc(1, sizeof(step_r)))) {
        mkerror(ERR_NULL, "Cannot allocate dbs (size = %d)",
        sizeof(step_r)); return NULL;}
     st = step;
     step->nseg = nseg;
     step->local = local;
     step->segment = segment;
     step->npars  = n = MCRLgetNumberOfPars();
     if (!pbce) pbce = Balance(step->npars);
     step->ecb = ecb; 
     step->fecb = fecb; 
     step->width = K;
     step->labels = labels; step->leafs = leafs; 
     step->nodes = nodes;
     pardb = (tdb_t*)  calloc(n, sizeof(tdb_t));
     for (i=0;i<n;i++) pardb[i] = TDBcreate(i, NULL, NULL);
     if (!currentTo) {
        if (!(currentTo = (elm_t*) calloc((size_t)(2*n), sizeof(elm_t)))) {
           mkerror(ERR_NULL, "Cannot allocate currentTo (size = %d)",
           2*n); return NULL;}
        if (!(currentFrom = (elm_t*) calloc((size_t)(2*n), sizeof(elm_t)))) {
           mkerror(ERR_NULL, "Cannot allocate currentFrom (size = %d)",
           2*n); return NULL;}
        if (!(src = (ATerm*) calloc((size_t) n, sizeof(ATerm)))) {
           mkerror(ERR_NULL, "Cannot allocate src (size = %d)",
           n); return NULL;}
        if (!(dest = (ATerm*) calloc((size_t) n, sizeof(ATerm)))) {
           mkerror(ERR_NULL, "Cannot allocate dest (size = %d)",
           n); return NULL;}
        ATprotect(&label); ATprotectArray(src, n); ATprotectArray(dest, n);  
        }
     STinitialize(enumOccurrenceOrdering, &label, dest, callback);
     plus = ATmakeAFun("plus", 2, ATfalse);ATprotectSymbol(plus);
     minus = ATmakeAFun("minus", 2, ATfalse);ATprotectSymbol(minus);
     times = ATmakeAFun("times", 2, ATfalse);ATprotectSymbol(times);
     divv = ATmakeAFun("div", 2, ATfalse);ATprotectSymbol(divv);
     mod = ATmakeAFun("mod", 2, ATfalse);ATprotectSymbol(mod);
     min = ATmakeAFun("min", 1, ATfalse);ATprotectSymbol(min);
     return step;
     }
    
      
          
int DISsegment(step_t st, elm_t *dest) {
     return Segment(st, dest);
     } 
        

int DISexplore(step_t step, unexplored_t *elm) {
     int count; 
     st = step;
     memcpy(currentFrom+K, elm->src, K*sizeof(elm_t));
     currentIdx = elm->c.idx;
     currentTag = elm->src;
     Unfold(currentFrom, src);
     /*ATfprintf(stderr, "DISexplore %d [%d %d] [%t %t] K=%d\n", 
     step->segment, currentFrom[2],currentFrom[3], src[0], src[45], K);*/
     count = STstep(src);
     if (count<0) return mkerror(ERR_NULL,"Error found during exploration");
     return step->fecb?step->fecb(elm, count):0;  
     }  
                        
     
elm_t *DISfold(step_t step, term_t *data) {
     st = step;
     Fold(data, currentTo);
     return currentTo+K;
     } 
     
term_t *DISunfold(step_t step, elm_t *data) {
     st = step;
     memcpy(currentTo+K, data, sizeof(elm_t)*K);
     Unfold(currentTo, dest);
     return dest;
     } 

elm_t *DISexploreInitialState(step_t step) {
     st = step;
     STsetInitialState();
     Fold(dest, currentTo); 
     return currentTo+K;
     }   
          
void DIShelpMCRL(void) {SThelp();}

int DISgetSegment(step_t step) {return step->segment;}
/*
int STdestroy(step_t st);
*/
