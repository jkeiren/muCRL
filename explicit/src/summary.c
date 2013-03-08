/* $Id: summary.c,v 1.2 2007/10/09 09:46:26 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "param0.h"
#include "mgr.h"

typedef struct {
   unsigned long explored, transitions, messages, open,
   open_tree, closed, closed_tree, queue, open_entries, closed_entries;
   } data_t;

static data_t **d;
static int verbose = 0;

static char dirname[100]; 
static int nseg, nlev;
static info_t info[1];
static unsigned long nmsg = 0;
static double closedset=0, closedset_tree=0,
open_entries = 0, closed_entries =0;

typedef struct {
  unsigned long n, pt;
  float *t, s, max;
  } msg_times_t;

typedef struct {
  unsigned long n, exch_time;
  float s, max;
  double exch_size;
  int  wallclock;
  } summary_t;

typedef struct {
  unsigned long msg_nr;
  float msg_time, bound, part;
  } part_t;
 
#define ISIZE 50
static part_t part[1000/25];
/*
   {
   {0,0.0, 0.0, 0.05}, {0,0.0,0.0, 0.10},{0,0.0,0.0, 0.15}, {0,0.0, 0.0, 0.20},
   {0,0.0, 0.0, 0.25}, {0,0.0,0.0, 0.30},{0,0.0,0.0, 0.35}, {0,0.0, 0.0, 0.40},
   {0,0.0, 0.0, 0.45}, {0,0.0,0.0, 0.50},{0,0.0,0.0, 0.55}, {0,0.0, 0.0, 0.60},
   {0,0.0, 0.0, 0.65}, {0,0.0,0.0, 0.70},{0,0.0,0.0, 0.75}, {0,0.0, 0.0, 0.80},
   {0,0.0, 0.0, 0.85}, {0,0.0,0.0, 0.90},{0,0.0,0.0, 0.95}, {0,0.0, 0.0, 1.00}
   };
*/

static int n_part;

static summary_t summary;
static double maxOpenset = 0, maxOpenset_tree = 0, maxQueue = 0,
maxOpen_entries=0;
  
static msg_times_t *msg_times;
static int maxLevel, maxLevelQueue, maxLevelTree;

static unsigned long n_msg_times = 0;

static float *all_times;


static char *Human(char *buf, double bytes) {
       // System.err.println("Human:"+b);
       unsigned long kilo = 1024;
       unsigned long mega = kilo*kilo;
       unsigned long giga = mega*kilo;
       unsigned long gigaBytes = bytes / giga;
       double aux = giga;
       bytes = bytes - aux*gigaBytes;
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

static int OpenMgr() {  
       char *last = dirname+strlen(dirname), cmd[80]; 
       int nlev;  
       sprintf(last,"/wallclock"); info->wallclock = fopen(dirname,"r");
       sprintf(cmd,"wc -l %s", dirname);
       {
       FILE *f = popen(cmd, "r");
       fscanf(f,"%d", &nlev);
       pclose(f);
       }
       sprintf(last,"/exch_size"); info->exch_size = fopen(dirname,"r");
       sprintf(last,"/exch_time"); info->exch_time = fopen(dirname,"r");
       *last='\0';
       return nlev;
       }
 
static FILE *Fopen(char *name, char *ext) {
       FILE *f = fopen(name, ext);
       if (!f) {
          fprintf(stderr,"Cannot open %s for %s\n", name, ext);
          exit(1);
          }
       return f; 
       }  
           
static void OpenInfo (int seg, int mode) {
    char *last = dirname+strlen(dirname);
    sprintf(dirname+strlen(dirname),"/%d", seg);
    {
    char *tail = dirname+strlen(dirname);
    FILE *f;
    if (mode==0) {
    sprintf(tail,"/explored"); 
    info->explored= Fopen(dirname,"r");
    sprintf(tail,"/transitions"); info->transitions= Fopen(dirname,"r");
    sprintf(tail,"/messages"); info->messages = Fopen(dirname,"r");
    sprintf(tail,"/open"); info->open = Fopen(dirname,"r");
    sprintf(tail,"/open_tree"); info->open_tree = Fopen(dirname,"r");
    sprintf(tail,"/closed"); info->closed = Fopen(dirname,"r");
    sprintf(tail,"/closed_tree"); info->closed_tree = Fopen(dirname,"r");
    sprintf(tail,"/queue"); info->queue = Fopen(dirname,"r");
    sprintf(tail,"/open_entries"); info->open_entries = Fopen(dirname,"r");
    sprintf(tail,"/closed_entries"); info->closed_entries = Fopen(dirname,"r");
    // fprintf(stderr,"tail= %s\n", fulldirname);
    } else
    sprintf(tail,"/message_times.gz"); info->message_times = GZopen(dirname,"r");
    }
    *last='\0';
    }
    
static void CloseInfo(int mode) {
   if (mode==0) {
   fclose(info->explored);
   fclose(info->transitions);
   fclose(info->messages);
   fclose(info->open);
   fclose(info->open_tree);
   fclose(info->closed);
   fclose(info->closed_tree);
   }
   else GZclose(info->message_times); 
   }
   
static void Allocate() {
    int i;
    d = (data_t**) malloc(nlev*sizeof(data_t*));
    for (i=0;i<nlev;i++) {
       int j;
       d[i] = (data_t*) malloc((nseg+1)*sizeof(data_t));  
    }
    }

static unsigned long ReadInMemory(int seg) {
    int i;
    for (i=0;i<nlev;i++) {
        fscanf(info->explored,"%d", &(d[i][seg].explored));
        fscanf(info->transitions,"%d", &(d[i][seg].transitions));
        fscanf(info->messages,"%d", &(d[i][seg].messages));
        fscanf(info->open,"%d", &(d[i][seg].open));
        fscanf(info->open_tree,"%d", &(d[i][seg].open_tree));
        fscanf(info->closed,"%d", &(d[i][seg].closed));
        fscanf(info->closed_tree,"%d", &(d[i][seg].closed_tree));
        fscanf(info->queue,"%d", &(d[i][seg].queue));
        fscanf(info->open_entries,"%d", &(d[i][seg].open_entries));
        fscanf(info->closed_entries,"%d", &(d[i][seg].closed_entries));
        }
    return d[nlev-1][seg].messages;
    }

static void ReadMsgTimes(int seg) {
    int i;
    for (i=0;i<msg_times[seg].n;i++) GZscanf(info->message_times,"%f",
             &(msg_times[seg].t[i]));
    }
    
static void PrintHeader(int level) {
    fprintf(stdout,"\n\t\t\tlevel %d\n",level);
    }

static void PrintDashed(int n) {
    int i;
    for (i=0;i<n;i++) fputc('-', stdout);
    putc('\n', stdout);
    }

static void Sum(data_t *e, data_t *s, double *openset, double *openset_tree,
    double *closedset, double *closedset_tree, double *queue, double
       *open_entries, double *closed_entries) {
    s->explored+=e->explored;
    s->transitions+=e->transitions;
    s->messages+=e->messages;
    *openset+=e->open;
    *openset_tree+=e->open_tree;
    *closedset+=e->closed;
    *closedset_tree+=e->closed_tree;
    *queue+=e->queue;
    *open_entries+=e->open_entries;
    *closed_entries+=e->closed_entries;
    }

static void SumTimes(data_t *e) {
    int i;
    for (summary.s=0, summary.n=0, i=0, summary.max = 0; i<nseg;i++) {
        summary.n+=e[i].messages;
        summary.s+=msg_times[i].s; 
        if (msg_times[i].max > summary.max) summary.max = msg_times[i].max;      
        }   
    } 
          
static void Print() {
   int i;
   char buf1[40], buf2[40], buf3[40], buf4[40];
   for (i=0;i<nlev;i++) {
      int j;
      double openset = 0, openset_tree = 0, queue =0;
      closedset = 0; closedset_tree = 0, open_entries = 0,  
           closed_entries = 0; 
      if (verbose) {
          PrintHeader(i);
          fprintf(stdout,"%10s%10s%10s%10s%10s%10s%12s%12s\n", 
      "seg.", "expl.", "trans.", "msg.","M lat","Max lat","open","closed");
          PrintDashed(84);
          }
      for (j=0;j<nseg;j++) {
         while (msg_times[j].pt<d[i][j].messages) {
            msg_times[j].s+=msg_times[j].t[msg_times[j].pt]; 
            if (msg_times[j].t[msg_times[j].pt]>msg_times[j].max)
               msg_times[j].max = msg_times[j].t[msg_times[j].pt];
            msg_times[j].pt++;
            }
         if (verbose) fprintf(stdout,"%10d%10d%10d%10d%10.6f%10.6f%6s%6s%6s%6s\n", j, d[i][j].explored,d[i][j].transitions,
             d[i][j].messages,msg_times[j].s/d[i][j].messages,
                 msg_times[j].max, 
                 Human (buf1, (double) (d[i][j].open)),
                 Human (buf2, (double) (d[i][j].open_tree)),
                 Human (buf3, (double) (d[i][j].closed)),
                 Human (buf4, (double) (d[i][j].closed_tree))
                 );
         Sum(d[i]+j, d[i]+nseg, &openset, &openset_tree, &closedset,
             &closedset_tree, &queue, &open_entries, &closed_entries); 
         if (openset>maxOpenset) {
             maxOpenset = openset;
             maxLevel = i;
             }
         if (queue>maxQueue) {
             maxQueue = queue;
             maxLevelQueue = i;
             }    
         }
         if (openset_tree>maxOpenset_tree) {
            maxOpenset_tree = openset_tree;
            maxOpen_entries = open_entries;
            maxLevelTree = i;
            }
      SumTimes(d[i]);
      
      fscanf(info->wallclock,"%d", &summary.wallclock);
      fscanf(info->exch_size,"%lf", &summary.exch_size);
      fscanf(info->exch_time,"%d", &summary.exch_time);
      if (verbose) {
          PrintDashed(84);
          fprintf(stdout,"%6dm%2ds%10d%10d%10d%10.6f%10.6f%6s%-6s%6s%-6s\n",  
          summary.wallclock/60, summary.wallclock%60, 
          d[i][nseg].explored,d[i][nseg].transitions,
          d[i][nseg].messages, summary.s/summary.n, summary.max,
          Human(buf1, openset), Human(buf2, openset_tree),
          Human(buf3, closedset), Human(buf4, closedset_tree)
          );
          }
      }
   }

int compare(const void* a, const void *b) {
   return (*((float*) a) > *((float*) b))?1:-1;
   }

static void PrintSummary(float median) {
   int timeVal = (int) summary.s, i;
   char buf[40];
   fprintf(stdout,"\n%s\n",dirname);
   PrintDashed(35);
   fprintf(stdout,"%25s%6dm%2ds\n","Wallclock time:",
               summary.wallclock/60, summary.wallclock%60);
   fprintf(stdout,"%25s%10d\n","Number of Levels:",  nlev);
   fprintf(stdout,"%25s%10d\n","Explored:",  d[nlev-1][nseg].explored);
   fprintf(stdout,"%25s%10d\n","Transitions:",  d[nlev-1][nseg].transitions);
   fprintf(stdout,"%25s%6dm%2ds\n","Total Msg Time (DB):",  timeVal/60, timeVal%60);
   fprintf(stdout,"%25s%10d\n","Number of Msg (DB):",  summary.n);
   fprintf(stdout,"%25s%9.5fs\n","Avarage Msg T (DB):", summary.s/summary.n);
   fprintf(stdout,"%25s%9.5fs\n","Median Msg T (DB):",  median);
   fprintf(stdout,"%25s%9.5fs\n","Max. Msg T (DB):",  summary.max);
   fprintf(stdout,"%25s%10s (at level:%d)\n","Max Size Open Set:", 
             Human(buf, maxOpenset), maxLevel);
   fprintf(stdout,"%25s%10s (at level:%d)\n","Max Size Queue:", 
             Human(buf, maxQueue), maxLevelQueue);
   fprintf(stdout,"%25s%10s (#entries:%1.0f at level:%d)\n","Size Open Set Tree:",
   Human(buf, maxOpenset_tree), maxOpen_entries, maxLevelTree);
   fprintf(stdout,"%25s%10s\n","Size Closed Set:", Human(buf, closedset));
   fprintf(stdout,"%25s%10s (#entries:%1.0f)\n","Size Closed Set Tree:", Human(buf,
   closedset_tree), closed_entries);
   fprintf(stdout,"%25s%10s\n","Transfer Size:", Human(buf, summary.exch_size));
   fprintf(stdout,"%25s%6dm%2ds\n","Transfer Time:",  summary.exch_time/60, 
                   summary.exch_time%60);
   PrintDashed(35);
   for (i=0;i<n_part;i++) {
       fprintf(stdout,"%-13s%4.3f%-15s%7d(%7d)%-10s%6.4fs(%6.4fs)\n",
       "Part of Area:",
       part[i].part,
       " N of Messages:", 
              part[i].msg_nr, summary.n-part[i].msg_nr,
       " Avarage T:", 
       (part[i].msg_nr>0?part[i].msg_time/part[i].msg_nr:9.9), 
       (summary.n-part[i].msg_nr>0?
           ((summary.s-part[i].msg_time)/(summary.n-part[i].msg_nr)):9.9));
       }
   } 

static void Histogram() {
   FILE *fp = Fopen(strcat(dirname,".his"),"w");
   float t; unsigned long i=0;
   for (t=0.025;t<0.8;t+=0.025) {
      int cnt = 0;
      for (;i<n_msg_times && all_times[i]<t;i++) cnt++;
      fprintf(fp,"%f %d\n", t, cnt);
      } 
   } 

static int PartArea() {
   unsigned long i, k = 0;
   float step = ISIZE;
   int n =sizeof(part)/sizeof(part_t), j;
   float s = 0, t;
   step = step/1000;
   for (t=step, i=0;i<n;i++, t+=step) {
      memset(part+i, sizeof(part_t), 0);
      part[i].part = t;
      }
   for (i=0;i<n;i++) part[i].bound = part[i].part*summary.s;
   for (i=0;i<n_msg_times;s+=all_times[i], i++) { 
      for (j=0;j<n;j++) 
      if (part[j].msg_nr==0 && s>part[j].bound) {
          part[j].msg_nr = i;
          part[j].msg_time = s;
          k++;
          }
      if (k==n) break;
      } 
   for (j=0;j<n;j++)
   if (part[j].msg_nr==0) {
          part[j].msg_nr = i;
          part[j].msg_time = s;
          }   
   return n; 
   }
               
int main(int argc, char *argv[]) {
    char *tail;
    int i = 0;
    float median;
    sprintf(dirname, argv[argc-1]);
    tail = strrchr(dirname,'.');
    if (!tail || strcmp(tail,".log")) strcat(dirname,".log");
    if (argc>2) verbose = 1;
    nseg = ForEachDirInDir(dirname, NULL);
    if (nseg<0) {
       fprintf(stderr,"Directory %s not found\n", dirname);
       exit(1);
       }
    msg_times = calloc(nseg, sizeof(msg_times_t));
    nlev = OpenMgr();
    // fprintf(stderr,"nlev = %d\n", nlev);
    Allocate();
    for (i=0;i<nseg;i++) {
      OpenInfo(i, 0);
      msg_times[i].n = ReadInMemory(i);
      n_msg_times+= msg_times[i].n;
      CloseInfo(0);  
      }
     all_times = malloc(sizeof(float)*n_msg_times);
     for (i=0;i<nseg;i++) {
       OpenInfo(i, 1);
       msg_times[i].t = i>0?msg_times[i-1].t+ msg_times[i-1].n:all_times;
       ReadMsgTimes(i);
       CloseInfo(1); 
       }   
     Print();
     qsort(all_times, n_msg_times, sizeof(float), compare);
     n_part = PartArea();
     if (n_msg_times%2) median = all_times[n_msg_times/2+1];
     else median = (all_times[n_msg_times/2]+all_times[n_msg_times/2+1])/2;
     // for (i=0;i<n_msg_times;i++) fprintf(stdout, "%d:%f\n", i, all_times[i]);
     // median = all_times[n_msg_times-1];
     PrintSummary(median);
     dirname[strlen(dirname)-4]='\0';
     Histogram();
}
