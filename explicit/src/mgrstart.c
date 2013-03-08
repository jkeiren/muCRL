/* $Id: mgrstart.c,v 1.38 2008/02/04 14:52:49 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#define MGRSTART_C
#include <string.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/select.h>
#include <sys/types.h>
#include <dirent.h>
#include <libgen.h>
#include <stdio.h>
#include <errno.h>
#include "param0.h"
#include <string.h>
#include <limits.h>
#include <assert.h>
#include "utl.h"
#include "fifo.h"
#include "mgr.h"
#include "term_db.h"
#include "db.h"
#include "label.h"
#include "sys/time.h"
#include "mgr_db.h"
#include "mgr_fork.h"


long int lroundf(float x);
#define MAXFDS 1024
#define INITSIZE 50
#define DBSIZE 256
/* #define E(X) if ((err=X)<0) (err=X, printmsg(""#X), err) */

#define NEWCONNECT 0
#define PORTAL  1
#define CONTACT 2
#define DBS 3

typedef struct {
    int r, w;
    } lnk_t;
         
typedef struct {
   int pt, *busy;
   lnk_t *lnk;
   unsigned int nseg, nlnk;
   } bag_s, *bag_t;


static channel_r db;

static fifo_t act_fifo;

static info_t *info;

static int layer = 0, tick_layer = 0;

typedef struct {
     long s, *c;
     int *b;
     int weak;
     } frek_t;


     
typedef struct {
     unsigned long msgCount;
     double exchMsgSize;
     float msgTime, maxMsgTime;
     float exchMsgTime;
     } total_t;

static total_t total;

static char fulldirname[100];

typedef struct {
     float startMsgTime, msgTime;
     double msgSize;
     } exch_t; /* report of exchange of the data */
     
static exch_t **exch; 
    
static frek_t frek; 
      
static int Bag(bag_t bag, int n) {
   bag->nlnk = n*n;
   bag->nseg = n;
   bag->pt = 0;
   bag->busy=(int*) calloc(bag->nseg, sizeof(int));
   bag->lnk = (lnk_t*) calloc(bag->nlnk,sizeof(lnk_t));
   return 0;
   }

typedef int (*process_cbt)(int w, int r);
static fd_set rfds;
static unsigned int nseg;

static void BagSubscribe(bag_t bag, int seg) {
   int i;
// printmsg("Bag subscribe %d seg = %d nseg = %d", bag->pt, seg, bag->nseg);
   for (i=0;i<bag->nseg;i++) {
      if (bag->pt >= bag->nlnk) {
          printmsg("Danger of overflow %d", bag->pt);
          abort();
          }
      bag->lnk[bag->pt].w = seg;
      bag->lnk[bag->pt].r = i;
      bag->pt++;
      }
   bag->busy[seg] = 0;
// printmsg("End Bag subscribe %d", bag->pt);
   }

static int BagProcess(bag_t bag, process_cbt process) {
   int i;
   // fprintf(stderr,"BagProcess pt = %d\n", bag->pt);
   if (bag->pt==0) {
        for (i=0;i<bag->nseg;i++) 
	if (bag->busy[i]) return 1;
        return 0;
	}
   for (i=0;i<bag->pt;i++) {
      int j;
      if (bag->busy[bag->lnk[i].r] || bag->busy[bag->lnk[i].w]) continue;
      process(bag->lnk[i].w, bag->lnk[i].r);
      bag->busy[bag->lnk[i].r]= bag->busy[bag->lnk[i].w]=1;
      for (j=i+1;j<bag->pt;j++) bag->lnk[j-1]=bag->lnk[j];
      bag->pt--; i--;
      }
   return 1;
   }
      
static void BagSetBusy(bag_t bag, int seg, int val) {
 // fprintf(stderr,"BagBusy seg %d: val = %d\n", seg, val);
   bag->busy[seg]=val;
   }
   
static bag_s bag[1];

static char *mcrlArgs, *pattern = NULL, *reject= NULL, *sselect = NULL, 
             *sfirst = NULL, *jid = NULL, *deadlock_action = NULL;   
static preg_t action_deadlock = NULL;  
static int stop  = 0, s  = 0,
nprogress = 0, *barrier, nbar = 0,
nvis = 0, verbose  = 0,   level = 0,
starttime = 0, nsockets = 0,
nskip = 0, nlevels = 0; 

static char dmpdir[DBSIZE], outputfile[DBSIZE],
     thisHost[256];
    
static file_t *sockets,  in = NULL, out = NULL;
       
static mytimer_t timer = NULL;

typedef struct {
   file_t r, w, o;
   int segment;
   char *hostname;
   int pid;
   } rw_t;
   
static rw_t  *vork, control; 

typedef struct {
    char *host, *dir;
    } dest_t;
    
static dest_t *dest;

static ad_t *current, *last, **ad;

static env_t *env;

typedef struct {
    long line, level, explored, visited, transitions, enabled, tick_transitions,
      deadlocks, ticks, backup, time;
    } logd_t;
 
typedef struct {
    logd_t *d;
    size_t s;
    bfile_t *f;
    int last, n;
    }  log_t; 

static log_t log;

typedef enum {MSGhello, MSGinfo, MSGdisconnect, MSGexit, 
MSGabort, MSGfinished, MSGhosts, MSGpid, MSGalive, MSGprogress, 
MSGsize, MSGweight, MSGlog} msg_t;

static void ControlInit(void) {
   getlabelindex("hello", 1);
   getlabelindex("info", 1);
   getlabelindex("disconnect", 1);
   getlabelindex("exit", 1);
   getlabelindex("abort", 1);
   getlabelindex("finished", 1);
   getlabelindex("hosts", 1);
   getlabelindex("pid", 1);
   getlabelindex("alive", 1);
   getlabelindex("progress", 1);
   getlabelindex("size", 1);
   getlabelindex("weight", 1);
   getlabelindex("log", 1);
   }

static char *finish = "#";

static void Hello() {
    if (control.w) {
       printUTF(control.w, getlabelstring(MSGhello));
       printUTF(control.w, jid);
       printUTF(control.w, outputfile);
       writeintUTF(control.w, nseg);
       writeintUTF(control.w, env->npars);
       writeintUTF(control.w, starttime);
       writeintUTF(control.w, GetTimeOfDay());
       printUTF(control.w, finish);
       fflush(control.w);
       }
    } 

static void Alive() {
    if (control.w) {
       printUTF(control.w, getlabelstring(MSGalive));
       writeintUTF(control.w, GetTimeOfDay());
       printUTF(control.w, finish);
       fflush(control.w);
       }
    }

static void WriteDirSize() {
  static char *cmd = NULL;
  if (!cmd) {
      cmd = (char*) malloc(100*sizeof(char));
      sprintf(cmd,"du -s -h -L %s",dmpdir);
      }
  {
  FILE *from = popen(cmd,"r");
  if (from) {
     char dirsize[80];
     if (fscanf(from,"%s", dirsize)>0) {
        printUTF(control.w, dirsize);
        }
     else printUTF(control.w, "??");
     fclose(from);  
     }
  else printUTF(control.w, "?");
  }
  }
  
static void DirSize() {
    if (control.w) {
       printUTF(control.w, getlabelstring(MSGsize));
       WriteDirSize();
       printUTF(control.w, finish);
       fflush(control.w);
       }
    } 
           
static void Exitted() {
    if (control.w) {
       // printmsg("Exitted control.w %d", control.w);
       printUTF(control.w, getlabelstring(MSGexit));
       printUTF(control.w, finish);
       fflush(control.w);
       }
    }
          
static void Finished(int segment) {
    if (control.w) {
       printUTF(control.w, getlabelstring(MSGfinished));
       if (segment>=0) writeintUTF(control.w, segment);
       printUTF(control.w, finish);
       fflush(control.w);
       }
    }

static void Hosts(void) {
    int i;
    if (control.w) {
       printUTF(control.w, getlabelstring(MSGhosts));
       for (i=0;i<nseg;i++) printUTF(control.w, vork[i].hostname); 
       printUTF(control.w, finish);
       printUTF(control.w, getlabelstring(MSGpid));
       for (i=0;i<nseg;i++) writeintUTF(control.w, vork[i].pid); 
       printUTF(control.w, finish);
       fflush(control.w);
       }
    }

static void Log(void) {  
     if (control.w) {
       int i; 
       bfflush(log.f);
       for (i=log.last;i<log.n;i++) {  
         printUTF(control.w, getlabelstring(MSGlog));
         writelongUTF(control.w,log.d[i].line);
         writelongUTF(control.w,log.d[i].level);
         writelongUTF(control.w,log.d[i].explored);
         writelongUTF(control.w,log.d[i].visited);
	 writelongUTF(control.w,log.d[i].enabled);
         writelongUTF(control.w,log.d[i].transitions);
         writelongUTF(control.w,log.d[i].tick_transitions);
         writelongUTF(control.w,log.d[i].deadlocks);
         writelongUTF(control.w,log.d[i].ticks);
         writelongUTF(control.w,log.d[i].time);
         printUTF(control.w,finish); 
         fflush(control.w);
         }
       log.last = log.n;
       }
     }
     
static void Info(void) {  
     if (control.w) {   
      static long last_explored = 0;
      if (current->explored>last->explored) last_explored = 
                  current->explored-last->explored;
       printUTF(control.w, getlabelstring(MSGinfo));
       writelongUTF(control.w,current->level);
       writelongUTF(control.w, last_explored);
       writelongUTF(control.w, current->visited-last->visited);
       writelongUTF(control.w,current->enabled-last->enabled);
       writelongUTF(control.w,current->transitions-last->transitions +
                      current->backup-last->backup);
       writelongUTF(control.w,layer+tick_layer);
       writelongUTF(control.w,current->explored );
       writelongUTF(control.w,current->visited);
       writelongUTF(control.w,current->enabled);
       writelongUTF(control.w,current->transitions+current->backup);
       printUTF(control.w,finish); 
       fflush(control.w);
       }
     }    
static void Finished2(int seg1, int seg2) {
    if (control.w) {
       printUTF(control.w, getlabelstring(MSGfinished));
       writeintUTF(control.w, seg1);
       writeintUTF(control.w, seg2);
       printUTF(control.w, finish);
       fflush(control.w);
       }
    }

static void UpdateTotal() {
   int i, j;
   total.msgTime=current->msgTime;
   total.msgCount=current->msgCount;
   total.maxMsgTime = current->maxMsgTime;
   for (i=0;i<nseg;i++) {
      for (j=0;j<nseg;j++) {
      // fprintf(stdout, "%ld ", exch[i][j].msgSize);
        total.exchMsgSize += exch[i][j].msgSize;
        total.exchMsgTime += exch[i][j].msgTime;
        exch[i][j].msgSize = 0;
        exch[i][j].msgTime = 0;
       }
    // fprintf(stdout,"\n");
    }   
   }
 
static void UpdateCurrent() {
        int i, j;
	memset(current, 0, sizeof(ad_t));
	current->visited-=nseg;
        current->minMsgTime=1000.0;
        current->maxMsgTime=0.0;
	for (i=0;i<nseg;i++) {
            current->explored+=ad[i]->explored;
	    current->enabled+=ad[i]->enabled;
            current->transitions+=ad[i]->transitions;
            current->ticks+=ad[i]->ticks;
            current->backup+=ad[i]->backup;
            current->deadlocks+=ad[i]->deadlocks;
            current->visited+=ad[i]->visited;
            current->termByteSize+=ad[i]->termByteSize;
            current->openvByteSize+=ad[i]->openvByteSize;
            current->openByteSize+=ad[i]->openByteSize;
            current->closedByteSize+=ad[i]->closedByteSize;
            current->closedvByteSize+=ad[i]->closedvByteSize;
            current->msgCount+=ad[i]->msgCount;
            current->msgTime+=ad[i]->msgTime;
            if (ad[i]->minMsgTime<current->minMsgTime) current->minMsgTime = 
                                ad[i]->minMsgTime;
            if (ad[i]->maxMsgTime>current->maxMsgTime) current->maxMsgTime = 
                                ad[i]->maxMsgTime;
	    }
	current->level = level;
// fprintf(stderr,"QQQQ HELP %8.5f\n", current->msgTime);
      } 
                
static int SelectAction(int idx) {
   switch (idx) {
      case MSGhello: UpdateCurrent();Hello(); Hosts(); Info(); Log(); return 1;
      case MSGinfo:  return 1;
      case MSGalive:  Alive(); return 1;
      case MSGsize:   DirSize(); return 1;
      case MSGlog:   Log(); return 1;
      case MSGdisconnect:
         log.last = 0;
         if (out) {
              fputc(MGR_DISCONNECT, out); fflush(out);
              sockets[PORTAL] = in;
	      }
         return 0;
      case MSGexit: stop = 1;
                    errorreset();printmsg("Manager %s exitted",dmpdir);
                    return 1;
      case MSGabort: stop = 1;
                    errorreset();printmsg("Manager %s aborted",dmpdir);
                    return 0;
      default: errormsg("Illegal tag: %d", idx);
      }
   return 0;
   }
   
static void HandleMessage(void) {
   char msg[256];
   int idx, go;
   if (!control.r) return;
   readUTF(control.r, msg, 256);
   // printmsg("HandleMessage %s", msg);
   idx = getlabelindex(msg, 0);
   go = SelectAction(idx);
   readUTF(control.r, msg, 256);
   // printmsg("HandleMessage2 %s", msg);
   if (!go) {
       FD_CLR(Fileno(control.r), &rfds);
       fclose(control.r);
       control.w = control.r = NULL; 
       sockets[CONTACT] = NULL;
       }
   if (strcmp(msg,finish)) errormsg("Msg %s not equal to expected %s",
   msg, finish);
   } 
   

      
static void KillForks() {
      int tag = MGR_EXIT, i;
      if (control.w) {fclose(control.w);control.r = NULL;}
      for (i=0;i<nseg;i++) {
         if (vork[i].r) FD_CLR(Fileno(vork[i].r), &rfds);
         vork[i].r = sockets[s+i]=sockets[s+nseg+i] = NULL;
         }
      for (i=0;i<nseg;i++) {
          if (vork[i].w) {
              C_mgr2fork_tag(vork[i].w, &tag);
              }
          }
      for (i=0;i<nseg;i++) {
         // fprintf(stderr,"Waiting for fork %d\n", i); 
         if (vork[i].o) pclose(vork[i].o);
         }
      // fprintf(stderr,"Waiting for data Base\n");
      if (sockets[nsockets-2]) pclose(sockets[nsockets-2]);
      sockets[nsockets-1] = sockets[nsockets-2] = NULL;
      if (out) {
         fputc(MGR_EXIT, out); 
	 fflush(out);
	 }
         // fprintf(stderr,"Waiting for mgrd\n");
      if (sockets[nsockets-1]) pclose(sockets[nsockets-1]);
      // fprintf(stderr,"Exitted\n");    
      }

static void PutContinue(int segment) {
   int tag = MGR_CONTINUE; 
   long v = LONG_MAX;
   C_mgr2fork_taglong(vork[segment].w, &tag, frek.c?&frek.c[segment]:&v);
   }

static char *Human(char *buf, double bytes) {
       // System.err.println("Human:"+b);
       unsigned long kilo = 1024;
       unsigned long mega = kilo*kilo;
       unsigned long giga = mega*kilo;
       unsigned long gigaBytes = bytes / giga;
       bytes = bytes - (gigaBytes * giga);
       unsigned long megaBytes = bytes / mega;
       bytes = bytes - (megaBytes * mega);
       unsigned long kiloBytes = bytes / kilo;
       bytes = bytes - (kiloBytes * kilo);
 if (gigaBytes>0) sprintf(buf,"%3ld.%ldG", gigaBytes, (10*megaBytes)/kilo); 
 else
 if (megaBytes>0) sprintf(buf,"%3ld.%ldM", megaBytes, (10*kiloBytes)/kilo); 
 else
       sprintf(buf,"%5ldK", kiloBytes); 
       return buf;
       } 
                
static void EndMessage(void) {
     char b[20];
     int timeval;
     printmsg("Levels %ld Explored %ld Visited %ld Transitions %ld", 
     layer+tick_layer, 
     current->explored, 
     current->visited, 
     current->transitions+current->backup+current->ticks);
     printmsg("DBS(la=%7.4fs cnt=%ld  max=%8.4f) OPEN SETS(time=%10.3fs size=%s)", 
     total.msgTime/total.msgCount,
     total.msgCount, total.maxMsgTime, total.exchMsgTime, Human(b, total.exchMsgSize));
     stopTimer(timer);
     timeval = timerReal(timer);
/*
     if (info) {
            fprintf(info->wallclock, "%10d\n", timeval);
            fprintf(info->exch_time, "%10d\n", (int) (total.exchMsgTime));
            fprintf(info->exch_size, "%15.0f\n", total.exchMsgSize);
            }
*/
     } 

static void MonitorMessage();
           
static void Stop() {  
      UpdateCurrent();
      Info();    
      KillForks();
      EndMessage();
      } 
        
static void ShutStop(void) {
    fprintf(stderr, "Shutdown mgrstart\n");
    Exitted();
    Stop();
    sleep(1);
    printmsg("Manager stopped");
    }


static void Progress(int segment) {  
     if (control.r) { 
       /*
       long latency = ad[segment]->msgCount>0?
             lroundf(ad[segment]->msgTime*10000)/ad[segment]->msgCount:0,
       maxMsgTime = lroundf(ad[segment]->maxMsgTime*10000),
            minMsgTime = lroundf(ad[segment]->minMsgTime*10000);
       */
       // fprintf(stderr,"Seg %d %s\n",segment, getlabelstring(MSGprogress));  
       printUTF(control.w, getlabelstring(MSGprogress));
       writeintUTF(control.w, segment);
       writelongUTF(control.w,ad[segment]->explored );
       writelongUTF(control.w,ad[segment]->visited);
       writelongUTF(control.w,ad[segment]->enabled);
       writelongUTF(control.w,ad[segment]->transitions+ad[segment]->backup);
       writelongUTF(control.w,ad[segment]->deadlocks);
       writelongUTF(control.w,ad[segment]->ticks);
       /*
       writelongUTF(control.w,ad[segment]->termByteSize);
       writelongUTF(control.w,ad[segment]->openByteSize);
       writelongUTF(control.w,ad[segment]->closedByteSize);
       writelongUTF(control.w,latency);
       writelongUTF(control.w,ad[segment]->msgCount);
       writelongUTF(control.w, minMsgTime);
       writelongUTF(control.w, maxMsgTime);
       */
       printUTF(control.w,finish); 
       fflush(control.w);
       }
     }             

static void Weight(int segment) {  
     if (control.r) {
       static long wmin = -10, wmax = 0; 
       int i; 
       if (wmin==-10) wmin = env->spectrum-1;
       printUTF(control.w, getlabelstring(MSGweight));
       writeintUTF(control.w, segment);
       if (segment>=0) {
       // fprintf(stderr,"Check %d %d\n", ad[segment]->wmin, ad[segment]->wmax);
       if (ad[segment]->wmax>wmax) wmax = ad[segment]->wmax;
       if (ad[segment]->wmin<wmin) wmin = ad[segment]->wmin;
       for (i=wmin;i<=wmax;i++) {
           writelongUTF(control.w,i);
           writelongUTF(control.w,ad[segment]->var[i].w);
           // fprintf(stderr,"i= %d w = %d\n", i, ad[segment]->w[i]);
           }
        } else {
          int k;
          for (k=0;k<nseg;k++) {
             if (ad[k]->wmax>wmax) wmax = ad[k]->wmax;
             if (ad[k]->wmin<wmin) wmin = ad[k]->wmin;
             }
          for (i=wmin;i<=wmax;i++) {
             long s = 0;
             for (k=0;k<nseg;k++) {
                 s+=ad[k]->var[i].w;
                 ad[k]->var[i].w=0;
                 }
             writelongUTF(control.w, i);
             writelongUTF(control.w,s);
             }
          }
       printUTF(control.w,finish); 
       fflush(control.w);
       }
     }           
    
static void Frek() {
     int i, j, n  = nseg;
     int max  = 0, min = env->spectrum;
     if (!frek.c) {
         frek.c = calloc(nseg, sizeof(long));
         frek.b = calloc(nseg, sizeof(int));
         }
     else {
       memset(frek.c, 0, nseg*sizeof(long));
       memset(frek.b, 0, nseg*sizeof(int));
       }
     frek.s = 0;
     for (i=0;i<nseg;i++)
     if (ad[i]->max>max) max = ad[i]->max;
     for (i=0;i<nseg;i++)
     if (ad[i]->min<min) min = ad[i]->min;
     /* Priority to smaller weights */
     // fprintf(stderr,"Frek:min=%d max=%d ad.f=%d\n", min, max,ad[0]->f[0]);
     if (frek.weak==3) {
        for (i=min;i<=max && frek.s<env->threshold;i++) {
           for (j=0;j<nseg;j++) frek.s += ad[j]->var[i].f;
           for (j=0;j<nseg;j++) frek.c[j] += ad[j]->var[i].f;
           }
        if (frek.s < env->threshold) {
           for (j=0;j<nseg;j++) frek.c[j] = LONG_MAX;
        }
        return;
        }
     for (i=min;i<=max;i++) {
        for (j=0;j<nseg;j++) frek.s += ad[j]->var[i].f;
        if (frek.s > env->threshold) {
            for (j=0;j<nseg;j++) frek.s -= ad[j]->var[i].f;
            break;
            }
        for (j=0;j<nseg;j++) frek.c[j] += ad[j]->var[i].f;
        }
        
     if (i<=max) {
        int t = env->threshold-frek.s, k = 1; 
        for (;n>0 && k>0;t = env->threshold-frek.s, n-=k) {
           k = 0;
           /* Use all segments with frek <= adjusted threshold */
           for (j=0;j<nseg;j++) 
           if (!frek.b[j])
           if (ad[j]->var[i].f<t/n) {
                frek.c[j] += ad[j]->var[i].f;
                frek.b[j] = 1;
                frek.s+= ad[j]->var[i].f;
                k++;
                }
        }
        /* Cut on equal weights */
        if (n>0) {
          int k=0;
          for (j=0;j<nseg;j++) {
              if (!frek.b[j]) {
                  int f = t/n;
                  /* There are (t%n) cells bigger then f */
                  if (ad[j]->var[i].f>f && (k<(t%n))) {
                        f++;
                        k++;
                        }
                  frek.c[j] += f; 
                  frek.s += f;
                  }
                  }
              }
        }
     /* fprintf(stderr,"frek.s %d:", frek.s);
     for (j=0;j<nseg;j++) fprintf(stderr,"%d ", frek.c[j]);
     fprintf(stderr,"\n");
     */
     if (frek.weak==2) {
        long m = -1;
        for (j=0;j<nseg;j++) 
        if (frek.c[j]>m) m = frek.c[j];
        for (j=0;j<nseg;j++)  {
           frek.c[j] = m;
           frek.s += (m - frek.c[j]);
           }
  /*
        for (j=0;j<nseg;j++) fprintf(stderr,"%d ", frek.c[j]);
        fprintf(stderr,"\n");
*/
        }
     if (frek.s < env->threshold) {
        for (j=0;j<nseg;j++) frek.c[j] = LONG_MAX;
        }
     }




static void printLine(long layer, int timeval, long levelexplored, long levelvisited, 
       char *trans, long leveltransitions, long explored, long visited, long transitions) 
       {
       static int first = 1;
       char te[20], da[20], op[20], cl[20]; 
       if (first) {
fprintf(stderr,"ex=explored vi=visited tr=transitions ba=backup'tr ti=ticks\n");
                first=0;
                }
fprintf(stderr, 
 "%3ld (%4dm%3ds): ex %8ld vi %8ld %s %8ld  (%ld %ld %ld)\n", 
          layer, timeval/60, timeval%60, 
          levelexplored, levelvisited, trans,  leveltransitions,  
          explored, visited, transitions);
     }
                        
static void MonitorMessage() {
     UpdateCurrent();
     Info(); 
     {
     static long last_explored;
     long leveltransitions = current->transitions-last->transitions
                             +current->backup-last->backup;
     long levelenabled = current->enabled-last->enabled;
     int timeval;
     static long levelticks = 0;
     static int tick_state = 0;
     static int backup_state = 0;
     logd_t data;
     memset(&data, 0, sizeof(logd_t));
     if (env->tick) levelticks += (current->ticks-last->ticks);
     data.visited  = current->visited-last->visited;
     data.explored = current->explored-last->explored;
     if (data.explored>0) last_explored = data.explored;
     data.enabled = current->enabled-last->enabled;
     data.deadlocks  = current->deadlocks-last->deadlocks;
     data.ticks  = current->ticks-last->ticks;
     data.backup  = current->backup-last->backup;
     data.line = log.n;
     errorreset();
     stopTimer(timer);
     timeval = timerReal(timer);
     startTimer(timer);
     // fprintf(stderr,"Help last vis: %d\n",last->visited); 
      if (!tick_state) {
        if (level==0 || leveltransitions>0 || current->ticks>last->ticks) {
          data.level = layer+tick_layer;
          printLine(layer+tick_layer, timeval, backup_state?last_explored:data.explored, 
             data.visited,
            backup_state?"ba":"tr",
            leveltransitions, current->explored, current->visited, 
            current->backup+current->transitions+current->ticks);
          layer++;
          data.transitions = leveltransitions;
          data.enabled = levelenabled;
          data.time = timeval;
          if (info) {
             fprintf(info->wallclock, "%10d\n", timeval);
             fprintf(info->exch_time, "%10d\n", (int) (total.exchMsgTime));
             fprintf(info->exch_size, "%15.0f\n", total.exchMsgSize);
             }
          bfwrite(&data, sizeof(logd_t), 1, log.f);log.n++;
          if (backup_state) backup_state = 0;
          Log();
          }
       if (level>0 && leveltransitions==0) { 
          if (strlen(sfirst)>0 && backup_state==0) 
                  backup_state = 1;       
               else
                  if (env->tick && levelticks != 0) tick_state=1;
          }
        }
      else {      
        data.level = layer+tick_layer;
          printLine(layer+tick_layer, timeval, data.explored, data.visited,"ti",
            levelticks, current->explored, current->visited, 
            current->ticks+current->transitions);
        tick_layer++;
        data.tick_transitions = levelticks;
        // fprintf(stderr, "Help %d\n", levelticks);
        data.time = timeval;
        if (info) {
            fprintf(info->wallclock, "%10d\n", timeval);
            fprintf(info->exch_time, "%10d\n", (int) (total.exchMsgTime));
            fprintf(info->exch_size, "%15.0f\n", total.exchMsgSize);
            }
        levelticks = 0; tick_state = 0; backup_state = 0;
        bfwrite(&data, sizeof(logd_t), 1, log.f);log.n++;
        Log();
        }
     }
     Frek();
     level++;
     } 
      
static void PutTick(int segment) {
   int tag = MGR_TICK; 
   long v = LONG_MAX;
   C_mgr2fork_taglong(vork[segment].w, &tag, frek.c?&frek.c[segment]:&v);
   }

static void PutBackup(int segment) {
   int tag = MGR_BACKUP; 
   long v = LONG_MAX;
   C_mgr2fork_taglong(vork[segment].w, &tag, frek.c?&frek.c[segment]:&v);
   }
   
      
static int PutWrite(FILE *from, int to) {
   int tag = MGR_WRITE;
   C_mgr2fork_tagseg(from, &tag, &to);
   return 0;
   }
                
static int SendData(int from, int to) {
    // fprintf(stderr, "SendData %d=>%d\n", from ,to);
    Finished2(from, to);
    stopTimer(timer);
    exch[from][to].startMsgTime = timerReal(timer);
    startTimer(timer);
    PutWrite(vork[from].w, to);
    return 0;
    }

static void InitDest() {
    char *destname = strdup(getenv("MCRL_DEST"));int i;
    for (strtok(destname," "),i=0; destname && i<nseg;
         destname = strtok(NULL," "), i++) {
         dest[i].host = strdup(basename(strdup(destname)));
         dest[i].dir =  strdup(dirname(strdup(destname)));
         }
    }

static void ReadEnvironment() {
    if (getenv("MCRL_OUTPUT")) {
         printmsg("Labeled Transition System will be written");
         env->file=1;
         }
    else printmsg("Labeled Transition System will not be written");
    env->npars = atoi(getenv("MCRL_NPARS"));
    if (getenv("MCRL_VERBOSE"))  env->verbose=1;
    if (getenv("MCRL_LOG"))  env->log=1;
    if (getenv("MCRL_LOCAL"))  {env->local=1;setLocal();} 
    if (getenv("MCRL_GLOBAL"))  env->global=1; 
    if (!strcmp(getenv("MCRL_MEMORY"),"global-tree")) env->K = 2;
         else  env->K=env->npars; 
    if (!strcmp(getenv("MCRL_MEMORY"),"vector")) env->tree= 0;
         else  env->tree=1; 
    if (getenv("MCRL_RESTORE"))  env->restore=1;
    if (getenv("MCRL_TRACE"))  env->trace=1;
    if (getenv("MCRL_ALL"))  env->all=1;
    if (getenv("MCRL_OLD"))  env->old=1;
    if (getenv("MCRL_STOP"))  env->stop=1;
    if (getenv("MCRL_TICK"))  env->tick=1;
    if (getenv("MCRL_DEADLOCK"))  env->deadlock=1;
    if (getenv("MCRL_PROGRESS")) env->progress=atoi(getenv("MCRL_PROGRESS"));
    else env->progress=2500;
    if (getenv("MCRL_DETAILED")) env->detailed=atoi(getenv("MCRL_DETAILED"));
    if (getenv("MCRL_SPECTRUM")) env->spectrum=atoi(getenv("MCRL_SPECTRUM"));
    else env->spectrum=10000;
    if (getenv("MCRL_SLEEP")) env->sleep=atoi(getenv("MCRL_SLEEP"));
    else env->sleep=3;
    if (getenv("MCRL_BEAMWIDTH")) {
         char *s = getenv("MCRL_BEAMWIDTH");
         int i;
         frek.weak = env->detailed;
         if (s[0]=='~') frek.weak=2; /* Portability */
         env->threshold=atoi((s[0]=='~')?s+1:s);
         fprintf(stderr, "Beamsearch: beam-width");
         for (i=1;i<frek.weak;i++) fprintf(stderr,"+");
         fprintf(stderr,"=%ld\n", env->threshold);
         }
    else env->threshold=LONG_MAX;
    if (getenv("MCRL_NSEGMENTS")) nseg=env->nseg = atoi(getenv("MCRL_NSEGMENTS"));
    if (getenv("MCRL_ACTION"))  pattern = getenv("MCRL_ACTION");
    if (getenv("MCRL_ACTION_DEADLOCK")) {
        deadlock_action = getenv("MCRL_ACTION_DEADLOCK");
        action_deadlock = RegCompile(deadlock_action);
        }
    if (getenv("MCRL_REJECT"))  reject = getenv("MCRL_REJECT");
    if (getenv("MCRL_SELECT"))  sselect = getenv("MCRL_SELECT");
    if (getenv("MCRL_FIRST"))  sfirst = getenv("MCRL_FIRST");
    timer = createTimer();
    strcpy(env->tickstring,"tick");
    if (getenv("MCRL_DEADLOCKSTRING")) 
         strcpy(env->deadlockstring,getenv("MCRL_DEADLOCKSTRING"));
    else strcpy(env->deadlockstring,"#deadlock#");
    gethostname(env->host,100);
    env->port = atoi(getenv("MCRL_MGRPORT"));
    env->mgrdPort = atoi(getenv("MCRL_MGRDPORT"));
    env->contactPort = env->mgrdPort+10000;
    strncpy(env->mgrdHost, getenv("MCRL_MGRDHOST"), 100);
    jid = getenv("MCRL_JID");
    if (getenv("MCRL_PRIORITY")) 
        strncpy(env->priority,getenv("MCRL_PRIORITY"), 1000);
    else env->priority=NULL;
    mcrlArgs = getenv("MCRL_ARGS");
    if (!mcrlArgs) mcrlArgs="";
    if (!pattern) pattern="";
    if (!reject) reject="";
    if (!sselect) sselect="";
    if (!sfirst) sfirst="";
    if (!deadlock_action) deadlock_action="";
    
    nskip = atoi(getenv("NSKIP")?getenv("NSKIP"):"0");
    dest = (dest_t*) calloc(nseg, sizeof(dest_t));
    InitDest();
    }

static void OpenInfo() {
    sprintf(env->logdir, "%s.log", (getenv("PBS_JOBNAME")!=NULL &&
    strchr(getenv("PBS_JOBNAME"),'/')==NULL &&
    strchr(getenv("PBS_JOBNAME"),'~')==NULL)?
    getenv("PBS_JOBNAME"): basename(strdup(outputfile)));
 // fprintf(stderr,"Test CreateEmptDir %s\n", env->logdir);
    if (CreateEmptyDir(env->logdir, DELETE_ALL)!=0)
                    errormsg("At Creating empty directory %s", env->logdir);
    {
    char *tail = env->logdir+strlen(env->logdir);
    info = (info_t*) malloc(sizeof(info_t));
    sprintf(tail,"/wallclock"); info->wallclock= fopen(env->logdir,"w");
    sprintf(tail,"/exch_time"); info->exch_time= fopen(env->logdir,"w");
    sprintf(tail,"/exch_size"); info->exch_size= fopen(env->logdir,"w");
    *tail = '\0';
    }
    }
                  
static void Init(int argc, char *argv[]) {  
     char *ptr; int i, j;
     UTLinit(NULL, NULL, NULL, "mgrstart");
     DYNcalloc(env, env_t, char, PRIOWIDTH, priority);
     gethostname(thisHost,256);
     ControlInit();  
     ReadEnvironment();
     strncpy(outputfile, argv[argc-1], DBSIZE);
     barrier = (int*) calloc(nseg, sizeof(int));
     if ((ptr=strrchr(outputfile,'.')) && !strcmp(ptr,".tbf"))
     *ptr = '\0';
     if (env->log) OpenInfo();  
     sprintf(dmpdir,"%s.dmp", outputfile);
     nsockets = 4 + 2*nseg+2;
     sockets = (file_t*) calloc(nsockets, sizeof(file_t));
     vork = (rw_t*) calloc(nseg, sizeof(rw_t));
     memset(&control, 0, sizeof(rw_t));  
     if (atexit(ShutStop)<0) {fprintf(stderr,"atexit\n");exit(1);}
     starttime = GetTimeOfDay();
     startTimer(timer);
     Bag(bag, nseg);
     act_fifo = FIFOcreateMemo(100, sizeof(vdbval_t), NULL, NULL);
     DYNcalloc(last, ad_t, weight_t, env->spectrum, var);
     DYNcalloc(current, ad_t, weight_t, env->spectrum, var);
     ad = (ad_t**) calloc(nseg, sizeof(ad_t*));
     for (i=0;i<nseg;i++) {
        DYNcalloc(ad[i], ad_t, weight_t, env->spectrum, var);
        for (j=0;j<env->spectrum;j++) ad[i]->var[j].f = LONG_MAX;
        ad[i]->max = 0;
        }
     frek.c = NULL;
     memset(&log, 0, sizeof(log_t));
     log.f = bopen_memstream(0, (char**) &log.d, &log.s);
     memset(&total, 0, sizeof(total_t));
     exch = (exch_t**) malloc(nseg*sizeof(exch_t*));
     for (i=0;i<nseg;i++) exch[i] = malloc(nseg*sizeof(exch_t));
     }

static void ReadReport(int i) {
    report_t report;
    C_fork2mgr_report(vork[i].r, &report);
    vork[i].hostname = strdup(report.hostname); 
    vork[i].pid = report.pid; 
    if (i==0) nlevels = report.level;
    }
     
                  
static void GetFork(file_t f, int segment, int client) {
     int i;
     DECLA(char*, desta, nseg);
     // fprintf(stderr,"GetFork %d\n", segment);
     vork[segment].r = sockets[s+segment]=f; 
     vork[segment].segment = segment;
     if (!(vork[segment].w = fdopen(client, "w")))
         errormsg("Illegal wr channel %d", client);
     strncpy(env->dir, dest[segment].dir, 100);
     strncpy(env->host, dest[segment].host, 100);
     C_mgr2fork_env(vork[segment].w, env);
     for (i=0;i<nseg;i++) desta[i] = dest[i].dir;
     C_mgr2fork_dest(vork[segment].w, desta, nseg);
     for (i=0;i<nseg;i++) desta[i] = dest[i].host;
     C_mgr2fork_dest(vork[segment].w, desta, nseg);
     C_mgr2fork_string(vork[segment].w, &mcrlArgs);
     C_mgr2fork_string(vork[segment].w, &pattern);
     C_mgr2fork_string(vork[segment].w, &reject);
     C_mgr2fork_string(vork[segment].w, &sselect);
     C_mgr2fork_string(vork[segment].w, &sfirst);
     C_mgr2fork_string(vork[segment].w, &deadlock_action);
     // fprintf(stderr,"1: GetFork finished %s\n", mcrlArgs);
     }
    
static void ConnectToPortal() {     
     int mgrd = contactSocket(env->mgrdHost, env->mgrdPort, 2);
     sockets[PORTAL]= in = fdopen(mgrd, "r");
     out = fdopen(mgrd,"w");
     }
      
static void SendInfoToContact() {
      char contactname[256];  int i, contact, tag = MGR_CONTACT;
// fprintf(stderr,"MGR:SendInfoToContact waiting for receive\n");
      fgets(contactname, 256, in);
      contactname[strlen(contactname)-1]='\0';  
// fprintf(stderr,"MGR:Received contactname %s\n", contactname);        
      contact = contactSocket(contactname, env->contactPort, 5);
      if (contact<0) {
         printmsg("Cannot connect with (%s, %d)",contactname, env->contactPort);
         return;
         }             
      sockets[CONTACT] = control.r = fdopen(contact,"r");
// fprintf(stderr, "Mgr: get %c\n", fgetc(control.r));
      if (!(control.w = fdopen(contact, "w")))
          errormsg("Illegal wr channel %d", contact);
      /* Needed for startup on each client: mgrd */
      fputc(MGR_REPORT, out);
      writeintUTF(out, nseg);
      for (i=0;i<nseg;i++) printUTF(out, vork[i].hostname);
      fflush(out); 
      sockets[PORTAL] = NULL;
      /* Forward info to DBS */
      C_mgr2db_tag(db.w, &tag);
      fprintf(db.w, "%s\n", contactname); fflush(db.w);
      }
      
            
static void TryToStop(int segment) {
      if ((nprogress+nbar)==nseg) { 
         exit(0);
         }
      }
      
static void Tick() {
      int k;
// fprintf(stderr,"Tick\n");
      for (k=0;k<nseg;k++) BagSetBusy(bag, k, 1);
      for (k=0;k<nseg;k++) PutTick(k);
      // printmsg("--- next level is tick level ---");
      } 

static void Backup() {
      int k;
// fprintf(stderr,"Backup\n");
      for (k=0;k<nseg;k++) BagSetBusy(bag, k, 1);
      for (k=0;k<nseg;k++) PutBackup(k);
      // printmsg("--- next level is tick level ---");
      }

static int ConnectToDBS(int port) { 
     int client = clientSocket(thisHost, port,1000000);
     sockets[DBS]= db.r =fdopen(client, "r"); 
     db.w = fdopen(client,"w");
     return client; 
     }

static file_t Mpopen(char *cmd) {
      file_t f;
      errno = 0; 
      if (!(f=Popen(cmd, "r")) || errno || fgetc(f)==EOF) {
           perror(cmd); exit(EXIT_FAILURE);
           }
      return f;
      } 
          
static file_t StartDbs(int port) {
      file_t f; int tag = MGR_DBSTART;
      char cmd[256];
      sprintf(cmd,"%s/dbstart %s %s -npars %d -port %d %s", 
            EXECDIR, env->restore?"-restore":"",
            env->file?"-dmp":"",
            env->npars, port, outputfile);
      f = Mpopen(cmd);
      ConnectToDBS(port);
      C_mgr2db_tag(db.w, &tag);fflush(db.w);
      C_db2mgr_leftright(db.r, &env->nLeft, &env->nRight);
      env->dbsPort = port; strncpy(env->dbsHost, thisHost,100); 
      return f;
      } 
      
static void StartFork(void) {
      char  cmd[256]; 
      int i, bound = nsockets - (nseg+2);
      cmd[0]='\0';
 // fprintf(stderr, "mgr: StartFork nseg = %d thisHost = %s\n", nseg, thisHost);
      for (i=0;i<nseg; i++) {
         cmd[0]='\0'; 
         if (!env->local && !env->global) sprintf(cmd, SSH, dest[i].host);
         sprintf(cmd+strlen(cmd),"%s/fork %s %d %d %d %s",EXECDIR, 
                      thisHost, env->port, i, nseg, dest[i].host);
         sockets[bound+i]= vork[i].o = Mpopen(cmd);
         // fprintf(stderr,"StartFork:Popen %s  %d\n", cmd, nseg);
         }
      }

static file_t StartMgrd(void) {
      file_t f;
      char cmd[256]; cmd[0]='\0';
      // if (!env->local && strcmp(env->mgrdHost, thisHost)) sprintf(cmd, SSH, env->mgrdHost);
      sprintf(cmd+strlen(cmd),"%s/mgrd gate%c %s %d %s %d",EXECDIR, 
      env->local?'L':'N',
      env->mgrdHost,
      env->mgrdPort, 
      getenv("PBS_O_HOST")?getenv("PBS_O_HOST"):env->mgrdHost,
      env->contactPort);
      // fprintf(stderr, "StartMgrd: %s\n", cmd);
      f = Mpopen(cmd);
      ConnectToPortal();
      return f;
      }
      
static void AskToFork(int segment, int idx, vdbval_t *parent) {
      file_t f = vork[segment].w; int tag = MGR_PARENT;
      /* fprintf(stderr,"Ask2Fork segment = %d tag = %c idx = %d f = %d\n", 
      segment, tag, idx, f); */
      C_mgr2fork_tag(f, &tag);
      C_mgr2fork_idx(f, &idx);
      C_fork2mgr_val(vork[segment].r, parent);
      }

static char *AskToDBS(int act, int *new) {
      int tag = MGR_INSPECT;
      static int asize = 0;
      static char **a = NULL, *s;
      while (act>=asize) {
         int asize0 = asize, i;
         asize= 2*asize+10;
         a = (char**) realloc((char**) a, asize*sizeof(char*));
         for (i=asize0;i<asize;i++) a[i] = NULL;
         }
      s  = a[act];
      if (new) *new = 0;
      if (s) return s;
      C_mgr2db_tag(db.w, &tag);
      C_mgr2db_act(db.w, &act);
      C_db2mgr_string(db.r, &s);
      a[act] = strdup(s);
      if (new) *new = 1;
      return s;
      }
          
static void PrintTrace(int segment, int idx, int deadlock) {      
     vdbval_t parent;
     char *act;
     do {
        // fprintf(stderr,"AskToFork %d %d\n", segment, idx);
        AskToFork(segment, idx, &parent);
        /* fprintf(stderr,"AskToFork rec parent (%d seg=%d act = %d)\n", 
           parent.idx, parent.seg, parent.act); */
	idx = parent.idx; 
	if (idx>=0) {  
          act = AskToDBS(parent.act, NULL);
          segment = parent.seg;
          fprintf(stdout,"<%s", act);
          /*
          fprintf(stderr,"PrintTrace QQB: %s %d match = %d\n",
          act, deadlock, action_deadlock?RegMatch(action_deadlock,
          act):0);
          */
          if (action_deadlock && deadlock) 
               if (!RegMatch(action_deadlock, act)) {
               fprintf(stdout,"...");
               return;
               }
          deadlock = 0;
          } 
           
	} while (idx>=0);
     }
     
static void StoreAction(int segment) {
      act_t act;
      int tag = CLIENT_ACTION_DONE;
      vdbval_t val;
      C_fork2mgr_act(vork[segment].r, &act);
      val.idx = act.smd; val.seg = segment; val.act = act.lab;
/* fprintf(stderr,"Before StoreAction %d segment = %d\n", act.lab,
      val.seg); */
      {
      int new;
      char *s = AskToDBS(act.lab, &new);
// fprintf(stderr,"After StoreAction %s\n", s);
      if (env->all || new) {
         FIFOput(act_fifo, &val);
      }
      }
      C_mgr2fork_tag(vork[segment].w, &tag); 
    }
      
static int PrintAction(int trace) {
    vdbval_t val;
    int r = FIFOget(act_fifo, &val);
    if (r>=0) {
      char *s = AskToDBS(val.act, NULL);
      fprintf(stdout, "level %d: %s",   current->level, s);
      if (trace) PrintTrace(val.seg, val.idx, 
            action_deadlock && !strcmp(s,env->deadlockstring)); 
      fprintf(stdout, "\n");
      fflush(stdout);
      } 
    return r;
    }
    
static void Continue() {      
      int k;
// fprintf(stderr,"Continue\n");
      for (k=0;k<nseg;k++) BagSetBusy(bag, k, 1);
      while (PrintAction(env->trace)>=0) {
         if (!env->all && env->stop) stop = 1;
         } 
      nprogress = 0;
      for (k=0;k<nseg;k++) {
          barrier[k] = 0;
          PutContinue(k);
	  }
      Finished(-1);  
      nbar = 0;
      }

static  void SendContinue() { 
      int i;  
      if (nbar+nprogress == nseg) {
        if (nprogress==nseg) while (PrintAction(env->trace)>=0);
        for (i=0;i<nseg;i++) 
        if (!barrier[i]) PutContinue(i);
        nprogress = 0;
        } 
       }
                
static void HandleProgress(int segment) { 
      C_fork2mgr_ad(vork[segment].r, ad[segment]);
      Progress(segment);
      Weight(segment);
      // Weight(-1);
      nprogress++; 
      if (stop) {
          TryToStop(segment);
          return;
          } 
      /* fprintf(stderr,"HandleProgress %d+%d=%d<=%d\n", 
        nbar, nprogress, nbar+nprogress, nseg); */ 
      if (FIFOgetCount(act_fifo)>0) {
           SendContinue();
	   } else {
	      nprogress--;
              PutContinue(segment);
	      }
      }
      
static void HandleReady(int segment, int from) {
      Finished(segment); 
      if (from>=0) {
      	  Finished(from);
      	  BagSetBusy(bag, from, 0);
          stopTimer(timer);
          exch[from][segment].msgTime = timerReal(timer)-exch[from][segment].startMsgTime;
          startTimer(timer);
          } 
      BagSetBusy(bag, segment, 0);
      BagProcess(bag, SendData); 
      }
                  
 static void HandleFinished(int segment) { 
      barrier[segment]=1; nbar++;
      C_fork2mgr_ad(vork[segment].r, ad[segment]);
      if (stop) TryToStop(segment);
      BagSubscribe(bag, segment);
      HandleReady(segment, -1);
      if (FIFOgetCount(act_fifo)>0) SendContinue(); // Update 10-4-2007 Bert Lisser
      }

static void ExitLevel() {
     static int nmsg = 0, anmsg =0, tick_state = 0, backup_state = 0;
     static int last_ticks = 0;
// fprintf(stderr,"tick_state: %d\n", tick_state);
     if (!anmsg) anmsg =nseg*nseg;
     nmsg++;
     if (level==0 || nmsg==anmsg) {
/*
     fprintf(stderr,"Exit Level %d<%d %d %d %d %d %d %d %d %d %d %d (%d)\n", nmsg, anmsg, 
                    current->transitions, last->transitions, 
                    current->backup, last->backup, current->level, nlevels,
                     last->visited, current->visited, last_ticks, current->ticks, tick_state);
*/
	      if (last->backup == current->backup &&
                  last->transitions==current->transitions 
              && level>0) {
                      if (tick_state == 1)  {
                         if (last_ticks == current->ticks) {
                               exit(0);
                               }
                         else  {
                               last_ticks = current->ticks;
                               }
                         }
                      else
                      if (backup_state==1  && !env->tick) exit(0); 
                 if (env->tick && (strlen(sfirst)==0||backup_state ==1)) {
                            if (tick_state==0) {
                                Tick();
                                tick_state = 1;
                                } 
                            else {
                                Continue();
                                tick_state = 0; 
                                }
                                backup_state = 0;
                       } else {
                       if (strlen(sfirst)>0 &&  tick_state==0) {
                         if (backup_state==0) {
                                Backup();
                                backup_state = 1;
                                }
                         else {
                               Continue();
                               backup_state= 0;
                               tick_state = 0;
                           }
                       } 
                       else {
                         if (tick_state) {
                         Continue();
                         tick_state = 0;
                         backup_state = 0;
                            } else exit(0);
                         }
                       }
	      } else {
                  Continue();
                  tick_state = 0; backup_state = 0;
                  } 
	      nmsg=0;
	      if (level>0) {
	         UpdateCurrent();
	         *last = *current;
	         nvis = 0;
		 }
              }
}
      
static void HandleVisited(file_t f, int segment) { 
      int from;  
      unsigned long msgSize;   
      C_fork2mgr_ad(f, ad[segment]);
      C_fork2mgr_int(f, &from);
      C_fork2mgr_long(vork[segment].r, (long*) &msgSize);
      exch[from][segment].msgSize = msgSize;
      Progress(segment);
      Weight(segment);
      // Weight(-1);
      if ((++nvis) == nseg) {
              Weight(-1);
              UpdateTotal();
	      MonitorMessage();
	      }
    if (level>0) HandleReady(segment, from);
    /* else  pid vork[segment].pid = from; */
  }
   
static void Synchronize() {
    int i, mgr_start= MGR_START,tag = MGR_CONTINUE;
    static int naccept =0;
    if ((++naccept)==nseg) {
         for (i=0;i<nseg;i++) C_mgr2fork_tag(vork[i].w, &mgr_start);
         for (i=0;i<nseg;i++) {
	      ReadReport(i);
              }
         ExitLevel();
         for (i=0;i<nseg;i++)  {
            ReadReport(i);
            C_fork2mgr_ad(vork[i].r, ad[i]);
            C_mgr2fork_tag(vork[i].w, &tag);
            }
         MonitorMessage();
	 *last = *current;
         level++;
         }
     }
                        
static void StartClients(int client) { 
      int segment;
      static int naccept = 0;
      if (client<0) errormsg("Illegal accept"); 
      {
      file_t f = fdopen(client,"r"); 
      // fprintf(stderr,"StartClients %d\n", naccept);
      C_fork2mgr_seg(f, &segment);
      GetFork(f, segment, client);
      if ((++naccept) == nseg) {
       int i;
       for (i=0;i<nseg;i++) {
          fputc(CLIENT_SYNC, vork[i].w); fflush(vork[i].w);
          }
       if (!sockets[nsockets-1]) sockets[nsockets-1] = StartMgrd();
       }
       }
     } 
       
static void MsgFromFork(int segment, int tag) {
     int from;
     unsigned long msgSize;
     switch (tag) {
        case CLIENT_VISITED: 
           HandleVisited(vork[segment].r, segment); ExitLevel(); break;
        case CLIENT_READ:
           C_fork2mgr_int(vork[segment].r, &from);
           C_fork2mgr_long(vork[segment].r, (long*) &msgSize);
           exch[from][segment].msgSize = msgSize;
           HandleReady(segment, from);  
	   ExitLevel();
	   break;
        case CLIENT_PROGRESS: HandleProgress(segment); break;
        case CLIENT_FINISHED: HandleFinished(segment); break;
        case CLIENT_ACTION: StoreAction(segment); break;
	case CLIENT_SYNC:  Synchronize(); break; 
       default: errormsg("%c %d: Illegal tag read:", tag, tag);
       }
     }

static void MsgFrom(int i) {
     int segment, tag;
     C_fork2mgr_segtag(sockets[i], &segment, &tag);
     // fprintf(stderr,"Arrived from %d: %c\n", segment, tag);
     MsgFromFork(segment, tag);
     }
     
static void Message(int i) {
     char buf[512], *ptr;
     if ((ptr = fgets(buf, 512, sockets[i]))) {
           fprintf(stderr,"%s", ptr);
           }
     else {
       errormsg("Channel %d corrupted", i); 
       }
     }
                                           
int main(int argc, char *argv[]) {
     int socket, i, k; 
     // fprintf(stderr,"MGRSTART started\n");
     Init(argc, argv);
     if ((socket= serverSocket(env->port,0))<0) errormsg("Server socket not open");
        printmsg("Manager uses port %d", env->port);
        sockets[s++] = fdopen(socket,"r");
	sockets[nsockets-2] = StartDbs(env->port-1);
	s+=3;
        StartFork(); 
        while (1) {
           int r; 
	   FD_ZERO(&rfds);
           for (i=0;i<nsockets;i++) 
           if (sockets[i]) {
               FD_SET(Fileno(sockets[i]), &rfds);
               }
           // fprintf(stderr,"MGR:Wait\n");
           if ((r=select(MAXFDS, &rfds, NULL, NULL, NULL))>0) {
           for (i=0, k=0;k<r && i<nsockets;i++) 
             if (sockets[i] && FD_ISSET(Fileno(sockets[i]), &rfds)) {
           // fprintf(stderr, "MGR:received %d\n", i);
           switch (i) {
            case NEWCONNECT: StartClients(Accept(socket));
                 break;
            case PORTAL: SendInfoToContact(); break;
            case CONTACT: HandleMessage(); break;
            case DBS: break;  
            default: {
	          if (i<nseg+s)  MsgFrom(i);
		      else Message(i);
              } /* default */
             } /* switch */
             k++;
             } /* if */
             } 
             } /* while */
             exit(EXIT_SUCCESS);
           }

