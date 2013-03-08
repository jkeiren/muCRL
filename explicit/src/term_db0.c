/* $Id: term_db0.c,v 1.15 2007/06/29 13:30:57 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "db.h"
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "param0.h"
#include "utl.h"
#define tdb_size 200
#define MAXFDS 128
// #define E(X) if ((X)<0) errormsg(""#X);else printmsg("%s %d",""#X,tdb->client_id)
#define E(X) if ((X)<0) errormsg(""#X)
#define GO_AHEAD 1953

typedef int (*tdb_cb)(char *name);

typedef enum {CLIENT, SERVER} role_t;

typedef struct {
     FILE *r, *w;
     } rw_t;
     
typedef struct { 
   db_et type;
   ATermIndexedSet db;
   FILE *file;
   GZfile gzfile, msg_times;
   void *dir;
   int id, count, last, client_id;
   role_t role;
   rw_t channel;
   float msgTime, minMsgTime, maxMsgTime;
   unsigned long msgCount;
   } tdb_r, *tdb_t;

static mytimer_t timer = NULL;

idx_t TDBput(tdb_t tdb, term_t term, int *new);
term_t TDBget(tdb_t tdb, idx_t idx);
 
static int ParseFile(GZfile, tdb_t, int);

static int TDBread(tdb_t tdb) {
    rewind(tdb->file);
    if (ReadOnly(tdb->file)) {
        tdb->gzfile = GZdopen(dup(fileno(tdb->file)), "r");
        ParseFile(tdb->gzfile, tdb, 1000000);
        GZclose(tdb->gzfile);
        tdb->gzfile = NULL;
        }
    else {
         int i;
         tdb->gzfile = GZdopen(dup(fileno(tdb->file)),"r");
         ParseFile(tdb->gzfile, tdb, 1000000);
         GZclose(tdb->gzfile);
         tdb->gzfile = GZdopen(dup(fileno(tdb->file)), "w");
         for (i=0;i<tdb->count;i++) {
            int new;
            TDBput(tdb, TDBget(tdb, i), &new);
            }
         }
    fclose(tdb->file);
    tdb->file =  NULL;
    return 0; 
    }      
        
tdb_t TDBcreate(int id, file_t file, channel_t channel) {
      tdb_t tdb = (tdb_t) calloc(1, sizeof(tdb_r));
      if (tdb==NULL) { 
           mkerror(ERR_NULL,"failed calloc(size = %d)",sizeof(tdb_r));
           return NULL;
           }
      timer = createTimer();
      // printmsg("TDBcreate: %d %lx %s", id, file, dir);
      tdb->type = TDB; tdb->role = SERVER;
      tdb->db = ATindexedSetCreate(tdb_size, 75);
      if (tdb->db==NULL) { 
          mkerror(ERR_NULL,
          "failed indexedSetCreate(size = %d)", tdb_size); 
          return NULL;
          } 
      tdb->file = file;
      tdb->count = tdb->last = 0; 
      tdb->minMsgTime = 1000.0;
      tdb->id = id;
#ifdef LINUX
      if (channel) {
          if (!tdb->file) tdb->role = CLIENT;
          tdb->channel.r = channel->r;
          tdb->channel.w = channel->w;
          }
#endif
      if (tdb->file) TDBread(tdb);
      return tdb;              
      }

void TDBsetId(tdb_t tdb, int id) {
      tdb->id = id;
      }

void TDBsetMsgTimes(tdb_t tdb, GZfile f) {
      tdb->msg_times = f;
      }
                    
int TDBdestroy(tdb_t tdb) {
      ATindexedSetDestroy(tdb->db); 
      if (tdb->gzfile) GZclose(tdb->gzfile);
      free(tdb);
      return 0;
      }

/*      
int TDBreset(tdb_t tdb) {
      ATindexedSetReset(tdb->db);
      tdb->count = 0;
      if (tdb->file) return Ftruncate(tdb->file, 0);
      return 0;
      } 
*/

   
int TDBgetCount(tdb_t tdb) {
      return tdb->count;
      }
            
static idx_t DBput(tdb_t tdb, term_t term, int *new) {
      ATbool nw;
      int r  = ATindexedSetPut(tdb->db, term, &nw);
      if (nw==ATtrue) tdb->count++;
      if (new) *new=(nw==ATtrue?1:0); 
      return r;
      }
                  
static term_t PutServer(tdb_t tdb, int *idx, int *nw) {
      /* Server */
      char *data;
      int  start, n, i;
      term_t r;
      FILE *rd = tdb->channel.r, *wr = tdb->channel.w;
      E(readintUTF(rd, &start));
      assert(start>=0);
      if (!(data=readstringUTF32(rd))) errormsg("PutServer");
      if ((r = ATparse(data))==NULL) errormsg("PutServer ATparse");
      *idx = DBput(tdb, r, nw);
      n = *idx-start+1;
      E(writeintUTF(wr, n));
      if (start>=0) {
            // n = TDBgetCount(tdb)-start;      
            E(writeintUTF(wr, *idx));
            for (i=0;i<n;i++) {
              char *s = ATwriteToString(ATindexedSetGetElem(tdb->db, start+i));
              E(writeUTF32(wr, s, (int) strlen(s)));
              }   
         }
      E(fflush(wr));
      return r;
      }
      
static idx_t PutClient(tdb_t tdb, term_t term, int *new) {
      int n=-1, i;idx_t idx;
      char *data, *s;
      if ((idx=ATindexedSetGetIndex(tdb->db, term))>=0) {
        if (new) new = 0;  
        return idx;
        }
        E(writeintUTF(tdb->channel.w, tdb->id));
        E(fputc(PUT, tdb->channel.w)); 
        E(writeintUTF(tdb->channel.w, tdb->count));
         s = ATwriteToString(term);
      // fprintf(stderr,"PutClient tdb writeUTF %d s=%s\n",tdb->id, s); 
        E(writeUTF32(tdb->channel.w, s, strlen(s)));
        E(fflush(tdb->channel.w));
        resetTimer(timer);
        startTimer(timer);
        E(readintUTF(tdb->channel.r, &n));
        tdb->msgCount++;
        stopTimer(timer);
        {
        float t = timerReal(timer); 
        if (tdb->msg_times) GZprintf(tdb->msg_times, "%10.6f\n", t);
        tdb->msgTime+= t;
        if (t>tdb->maxMsgTime) tdb->maxMsgTime = t;
        if (t<tdb->minMsgTime) tdb->minMsgTime = t;
        }
        E(readintUTF(tdb->channel.r, &idx));
        for (i=0;i<n;i++) {
            if (!(data=readstringUTF32(tdb->channel.r))) errormsg("PutClient");
            DBput(tdb, ATparse(data), new);
            }
      return idx;
      }
      
static term_t GetClient(tdb_t tdb,  idx_t idx, int *count) {
      int i, new, n; 
      term_t r=NULL, result = NULL;
      char *data;
      E(writeintUTF(tdb->channel.w, tdb->id));
      E(fputc(GET, tdb->channel.w)); 
      E(writeintUTF(tdb->channel.w, tdb->count));
      E(writeintUTF(tdb->channel.w, idx));
      E(fflush(tdb->channel.w));
      resetTimer(timer);
      startTimer(timer);
      E(readintUTF(tdb->channel.r, &n));
      stopTimer(timer);
      tdb->msgCount++;
        {
        float t = timerReal(timer);
        if (tdb->msg_times) GZprintf(tdb->msg_times, "%10.6f\n", t); 
        tdb->msgTime+= t;
        if (t>tdb->maxMsgTime) tdb->maxMsgTime = t;
        if (t<tdb->minMsgTime) tdb->minMsgTime = t;
        }
      if (n==0) return NULL;
      for (i=0;i<n;i++) {
         if (!(data=readstringUTF32(tdb->channel.r))) errormsg("GetClient");
         if (!(r = ATparse(data))) errormsg("GetClient ATparse");
         if (DBput(tdb, r , &new)==idx) result = r;
         }
      if (count) *count = n;
      return result;
      }

float TDBgetMsgTime(tdb_t tdb) {
           // fprintf(stderr,"msgTime: %15.9f\n", tdb->msgTime);
           return tdb->msgTime;
           }
float TDBgetMsgMinTime(tdb_t tdb) {return tdb->minMsgTime;}
float TDBgetMsgMaxTime(tdb_t tdb) {return tdb->maxMsgTime;}

void TDBsetNewLevel(tdb_t tdb) {
         tdb->minMsgTime=1000.0; 
         tdb->maxMsgTime=0.0;
         tdb->msgTime = 0.0;
         tdb->msgCount = 0;
         }

unsigned long TDBgetMsgCount(tdb_t tdb) {
   // fprintf(stderr,"msgCount: %6ld\n", tdb->msgCount);
   return tdb->msgCount;
  }
      
static term_t GetServer(tdb_t tdb, int all) {
      /* Server */
      int start, i, idx, n;
      term_t r = NULL, result = NULL;
      FILE *rd = tdb->channel.r, *wr = tdb->channel.w;
      E(readintUTF(rd, &start));
      E(readintUTF(rd, &idx));
      // printmsg("tdb Get server %d idx %d", all, idx);
      if (idx>=TDBgetCount(tdb)) n=0;
      else
      n = all>0?TDBgetCount(tdb)-start:idx-start+1;
      E(writeintUTF(wr,n));
      if (all<2) {
      for (i=0;i<n;i++) {
        if ((r = ATindexedSetGetElem(tdb->db, start+i))==NULL)
           errormsg("Getserver ATindexedGetElm (%d,%d)", start, i);
        if (start+i==idx) result = r;
            {
            char *s = ATwriteToString(r);
            E(writeUTF32(wr,s, strlen(s)));
            }
        }
      }
      E(fflush(wr));
      return result;
      }                 
      
idx_t TDBput(tdb_t tdb, term_t term, int *new) {
      int nw, idx;
      if (tdb->role == CLIENT) 
                       return PutClient(tdb, term, new);
      if (!term) term = PutServer(tdb, &idx, &nw);
      else
      idx = DBput(tdb, term, &nw);
      if (tdb->gzfile && nw) {
            char *s = ATwriteToString(term);
            if (GZputs(tdb->gzfile, s)<0 || GZputs(tdb->gzfile, "\n")<0)
               return mkerror(ERR_WRITE, "TDBput");
             }
      if (new) *new = nw;  
      return idx;
      }
                       
term_t TDBget(tdb_t tdb, idx_t idx) {
     if (idx >= tdb->count) 
         return (tdb->role == CLIENT) ? GetClient(tdb, idx, NULL):NULL;
     if (idx>=0) return ATindexedSetGetElem(tdb->db, idx);
     if (tdb->role == SERVER) return GetServer(tdb, 0); 
     return NULL;
     }

int TDBsetChannel(tdb_t tdb, channel_t channel) {
    return 0;
    }
   
#ifdef LINUX     
static int GetTag(tdb_t tdb, channel_t channel) {
     tdb->channel.r = channel->r;
     tdb->channel.w = channel->w;
     return fgetc(tdb->channel.r);
     } 
#endif 
#ifdef LINUX    
int TDBreact(tdb_t tdb, channel_t channel) {
      int tag = GetTag(tdb, channel), new;
      idx_t idx;
      // printmsg("tag = %c", tag);
      switch (tag) {
       case PUT: idx = TDBput(tdb, NULL, &new); 
                 /* return new?idx:-1; */ return idx;
       case GET: TDBget(tdb, -1); break;
       default: errormsg("TDBreact:Illegal tag %d", tag);
       }
      return -1;
      }      
#else
      int TDBreact(tdb_t tdb) {
      printmsg("TDBreact not implemented"); return 0;}
#endif      

#include "term_parse.h"

int TDBrunThrough(tdb_t tdb, tdb_cb cb) {
    ATermList names = ATindexedSetElements(tdb->db);
    int n = ATgetLength(names), i;
    for (i=0;i<n;i++) {
       if (cb(ATgetName(ATgetAFun(ATindexedSetGetElem(tdb->db, i))))<0) return 1;
       }
    return 0;
    }


