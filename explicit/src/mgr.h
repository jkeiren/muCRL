/* $Id: mgr.h,v 1.16 2007/06/29 13:30:57 bertl Exp $ */

#ifndef MGR_H
#define MGR_H
#define MGR_CONTINUE 'c'
#define MGR_CONTACT 'k'
#define MGR_START 's'
#define MGR_STOP 'q'
#define MGR_EXIT 'e'
#define MGR_ABORT 'a'
#define MGR_REPORT 'b'
#define MGR_DISCONNECT 'd'
#define MGR_PARENT 'p'
#define MGR_WRITE 'w'
#define MGR_READ 'r'
#define MGR_TICK 't'
#define MGR_BACKUP 'u'
#define END 'e'
#define INST_CONTINUE 'c'
#define INST_INITSTATE 'i'
#define CLIENT_FINISHED 'f'
#define CLIENT_SYNC 'z'
#define CLIENT_VISITED 'v'
#define CLIENT_PROGRESS 'p'
#define CLIENT_READ 'r'
#define CLIENT_WRITE 'w'
#define CLIENT_START 's'
#define CLIENT_WRITESCRIPTS 'w'
#define CLIENT_ACTION 'l'
#define CLIENT_ACTION_DONE 'd'
#define CLIENT_TRACE 't'
#define CLIENT_DEADLOCK 'k'
#define CLIENT_READY 'y'
#define FORK_READY 'y'

#define ENDLEVELMARKER -1
#define ENDFILE -2
#define UNDEF -3

#define SSH "ssh -x -T %s "

/* dynstruct.h */

typedef struct {
   size_t bsize, rsize, tsize;
   void *next, *ptr;
   } DYNrec, *DYNptr;

#define DYNcalloc(name, type, memb_type, nmemb, memb) { \
   size_t N = sizeof(type)+ nmemb*sizeof(memb_type); \
   name = (type*) malloc(N); \
   memset(name, 0, sizeof(type)); \
   name->bsize = N; \
   name->tsize = sizeof(type); \
   if (nmemb>0) { \
      name->next = name->memb = (memb_type*)(name+1); \
      } \
   name->rsize = N-sizeof(DYNrec); \
   }
   
// (nmemb>0?sizeof(void*):0)+

static size_t DYNwrite(FILE *f, DYNptr name) {
   if (name->ptr) {
       fputc('A', f); 
       fwrite(name+1, name->rsize, 1, f);
       return name->rsize;
       }
   else {
       fputc('B', f);
       fwrite(name+1, name->tsize, 1, f);
       return name->tsize;
       } 
   return 0;
   }
   
static size_t DYNread(FILE *f, DYNptr name) { 
   char c = fgetc(f);
   if (c=='B') {
       name->ptr = NULL;
       fread(name+1, name->tsize, 1, f);
       return name->tsize;
       }
   else {
       name->ptr = name->next;
       fread(name+1, name->rsize, 1, f);
       return name->rsize;
       }
   return 0;
   }

static void Dynfree(void *name)  {free(name);}

/* end dynstruct.h */

typedef struct {
   size_t bsize, rsize, tsize;
   char *next, *priority;
   long threshold;
   unsigned int nseg, npars, spectrum, K;
   int restore, file, tick, local, progress, all, trace, 
        deadlock, global, old, tree;
   int nLeft, nRight, sleep;
   int  port, dbsPort, mgrdPort, contactPort;
   int verbose, stop, detailed, log;
   char host[100], dir[100], dbsHost[100], mgrdHost[100],
      logdir[100];
   char tickstring[10], deadlockstring[15];
   } env_t;

typedef struct {
   int pid, level;
   char hostname[100];
   } report_t;
   
typedef struct {
   int seg;
   elm_t idx;
   elm_t act;
   }  vdbval_t;
   
typedef struct {
  elm_t idx, w;
  } u_context_t;
  
typedef struct {
  size_t bsize, rsize, tsize;
  elm_t *next, *src;
  u_context_t c;
  }  unexplored_t;  

typedef struct {
  elm_t idx, act, w;
  elm_t forceParent;
  elm_t src[2];
  }  v_context_t;
  
typedef struct {
  size_t bsize, rsize, tsize;
  elm_t *next, *dest;
  v_context_t c;
  } visited_t; 
  
typedef struct {
  long f, w;
  } weight_t;
    
typedef struct {
   size_t bsize, rsize, tsize;
   weight_t *next, *var;
   long level, explored, transitions, enabled, visited, ticks, backup, 
   deadlocks, idx, max, min, wmax, wmin;
   unsigned long openvByteSize, termByteSize, openByteSize, closedByteSize,
               closedvByteSize, queueByteSize, openEntries, closedEntries;
   unsigned long msgCount;
   float msgTime, minMsgTime, maxMsgTime;
   } ad_t;

typedef struct {
   FILE *explored, *transitions, *messages,  *open, *open_tree, 
            *closed, *closed_tree, *queue, *open_entries, *closed_entries,
            *wallclock, *exch_time, *exch_size;
   GZfile message_times;
   } info_t;
#endif
#undef DEBUG
