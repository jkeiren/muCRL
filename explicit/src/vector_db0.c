/* $Id: vector_db0.c,v 1.15 2007/06/29 13:30:57 bertl Exp $ */
#define VECTOR_DB_C
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdlib.h>
#include <string.h>
#include "param0.h"
#include "db.h"
#include <stdio.h>
#include "utl.h"
#include "fifo.h"


#define INITSIZE 100
#define BLOCKSIZE 65536
#define INIT_HASH_SIZE 65536
#define INIT_HASH_MASK 0x0ffff
#define INTERVAL 10000000
#define SETMARKER(x) ((x)->n=-((x)->n)-1)
#define ISMARKER(x) (x->n<0)
/*#define MALLOC_CHECK_ 2 */
#define MAXDBSIZE 100000000
#define MAXFDS 128

// #define E(X) if ((X)<0) errormsg(""#X);else printmsg("%s %d",""#X,vdb->client_id)
#define E(X) if ((X)<0) errormsg(""#X)
// #define EMPTY 255
typedef enum {VDBdata, VDBbarrier} VDBload_t;

typedef int (*range_cbt)(int id,  idx_t ofs, int len);

typedef int (*barrier_cbt)(int id,  void *tag);

typedef int (*load_cbt)(int id, VDBload_t kind, int count, elm_t *elm);

typedef void (*get_cbt)(int id, void *tag, idx_t idx);
 
static unsigned int prime[] = {236487217, 677435677};

// typedef entry_t int;       
     
typedef struct {
     int n;
     void *tag;
     } range_r, *range_t;
     
static unsigned int HashValue(int width, elm_t *e) {
     unsigned int r =  (width--,e[width]*prime[width%2]);
     for (width--;width>=0;r+= e[width]*prime[width%2], width--);
     return r;
     }

static FILE *tty =NULL;

        
#define ENTRY_MAX INT_MAX 

typedef enum {CLIENT, SERVER} role_t;
typedef enum {VDBall, VDBuntilMark, VDBoneMark} VDBforcemode_t;    
typedef struct {
     elm_t *data;
     int width;
     unsigned int size, blocksize;
     int *next;
     } entries_t;

/* socket -> [read, write] */


typedef struct {
     FILE *r, *w;
     } rw_t; 
              
typedef struct {
    db_et type;
    int id, client_id;
    unsigned int mask, hashsize, first;
    entries_t e;
    int *hash;
    get_cbt gcb;
    range_cbt rcb;
    barrier_cbt bcb;
    load_cbt lcb;
    fifo_t fifo;
    FILE *file;
    char *dir;
    char *home;
    void *tag;
    role_t role;
    rw_t channel;
    void *array;
    float msgTime, minMsgTime, maxMsgTime;
    unsigned long msgCount;
    GZfile msg_times;
} vdb_r, *vdb_t; 

static mytimer_t timer = NULL;

#include "array.h"

static vdb_t c_vdb;

int VDBput(vdb_t vdb, elm_t *elm, int *new);

unsigned long VDBgetByteSize(vdb_t vdb) {
    return vdb->hashsize*sizeof(int)
          +vdb->e.size*vdb->e.width*sizeof(elm_t);
    }

void VDBsetMsgTimes(vdb_t vdb, GZfile f) {
      vdb->msg_times = f;
      }
      
int VDBsetBarrier(vdb_t vdb, void *tag);

int VDBgetCount(vdb_t vdb);

void DBSdeleteHashtable(vdb_t vdb) {
     if (vdb->hash) {
         free(vdb->hash);
         vdb->hashsize = 0;
         vdb->mask = 0;
         vdb->hash = NULL;
         }
     } 
    
static int DBSreallocHashtable(vdb_t vdb) {
    // fprintf(tty, "QQ:Realloc HashTable %d %d %d\n", vdb->hashsize, vdb->e.size, 
    //  vdb->e.blocksize);
    int width = vdb->e.width;
    if (vdb->hash && vdb->hashsize>vdb->e.size) return 0; 
    { 
    int i;
    unsigned int  n = vdb->e.size, vdbmask = vdb->hash?vdb->mask:INIT_HASH_MASK, 
              hashsize = vdb->hash?vdb->hashsize:INIT_HASH_SIZE; 
        DBSdeleteHashtable(vdb);
        for(;hashsize <= n;hashsize *=2,vdbmask =(vdbmask<<1)|1);
        if (!(vdb->hash = (int*) calloc((size_t) hashsize, sizeof(int)))) 
             return mkerror(ERR_NULL, "Cannot allocate hash table"); 
	for (i=hashsize-1;i>=0;i--) vdb->hash[i] = -1; 
	for (i=0;i<n;i++) {
	   unsigned int hash= HashValue(vdb->e.width, 
                      vdb->e.data+i*width)&vdbmask;
	   vdb->e.next[i] = vdb->hash[hash];
	   vdb->hash[hash]=i;
	   }
        vdb->mask = vdbmask; vdb->hashsize = hashsize; 
        // printmsg("rehash of %d: size %d succesful",
        // vdb->id, vdb->hashsize);
        // fprintf(tty,"Finish hashTable\n");
        return 0;
    }
    }
    
static int DBSreallocBuckettable(entries_t *es) {
    int i, widthbytes = es->width*sizeof(elm_t);
    unsigned int size0 = es->blocksize, n = BLOCKSIZE/widthbytes;
    es->blocksize = (es->size/n+1)*n;
   //  fprintf(tty, "QQ:Realloc BucketT %d %d %d\n", size0, es->size, 
   //   es->blocksize);
    if (!(es->data = 
          (elm_t*) realloc(es->data, es->blocksize*((size_t)widthbytes))))
    return mkerror(ERR_NULL, "Cannot reallocate bucket");
    if (!(es->next = 
          (int*) realloc(es->next, es->blocksize*sizeof(int)))) 
    return mkerror(ERR_NULL, "Cannot reallocate next"); 
   // printmsg("Clear size0 = %d end = %d", size0, es->blocksize);
   for (i=size0;i<es->blocksize;i++) es->next[i] = -1;
   // fprintf(tty,"Finish bucket table\n");
   return 1;
   }
      
static int DBSresetBuckettable(entries_t *es) {
   int i;
   es->size = 0;
   for (i=0;i<es->blocksize;i++) es->next[i] = -1;
   }

static int DBSresetHashtable(vdb_t vdb) {
    int i;
    for (i=vdb->hashsize-1;i>=0;i--) vdb->hash[i] = -1; 
    }

void VDBreset(vdb_t vdb) {
    DBSresetBuckettable(&(vdb->e));
    DBSresetHashtable(vdb);
    }

static int DBput(vdb_t vdb, elm_t *elm, idx_t *idx, int *new);

#ifdef LINUX
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
  

#endif
    
static int VDBread(vdb_t vdb, FILE *file) {
    elm_t elm[2]; long pos = 0;
    // printmsg("VDBread %d", FileLen(file));
    if (!file) return mkerror(ERR_NULL,"VDBread file = NULL");
    if (WriteOnly(file)) {
        return 0;
        }
    while (((pos=ftell(file)),readPair(file, elm))) {
       int r  = 0;
       VDBload_t kind;
       elm_t *e = NULL;
       switch (elm[0]) {
          case -1: kind = VDBbarrier; break;
          default: e = elm; kind = VDBdata;
          }
 // if (vdb->id==0) fprintf(stderr, "pos = %d id = %d\n", pos, vdb->id);
       if (vdb->lcb) r = vdb->lcb(vdb->id, kind, VDBgetCount(vdb), e);
       if (r<0) break; 
       if (r==0 && kind==VDBdata) {int n; 
       if (elm[0]>=0) DBput(vdb, elm, NULL, &n);}
       }
 // printmsg("Loaded vdb %d  count = %d", vdb->id, VDBgetCount(vdb)); 
     vdb->first = VDBgetCount(vdb); 
     if (ReadOnly(file)) {
        file = NULL; 
        }
      else {
 // printmsg("before fseek %d", FileLen(file));
        fseek(file, pos, SEEK_SET);
 // printmsg("after fseek truncated? bytes %d", pos);
        Ftruncate(file, pos); 
        // printmsg("after ftruncate");
        errno = 0;
        }
     return 0;
     }

static int eachFile(char *fname) {
     FILE *f =  fopen(fname, "r");
     rewind(f);
     // printmsg("Filename %s len = %d", fname, FileLen(f));
     VDBread(c_vdb, f);
     fclose(f);
     return 0;
     }
             
int VDBdir(vdb_t vdb) {
     c_vdb = vdb;
     if (vdb->dir) ForEachFileInDir(vdb->dir, eachFile);
     return VDBgetCount(vdb);
     } 

int VDBgetWidth(vdb_t vdb) {
     return vdb->e.width;
     }
     
vdb_t VDBcreate(int id, int width, file_t file, dir_t dir, channel_t channel,  get_cbt gcb, 
    range_cbt rcb, barrier_cbt bcb, load_cbt lcb) {    
      vdb_t vdb = (vdb_t) calloc(1, sizeof(vdb_r));
      // if (!tty) tty = fopen("/dev/tty","w");
      if (vdb==NULL) { 
    mkerror(ERR_NULL,"failed calloc(size = %d)",sizeof(vdb_r));return NULL;}
      timer = createTimer();
      vdb->type = VDB;  vdb->id = id; vdb->role = SERVER;
      vdb->gcb = gcb; vdb->rcb = rcb; vdb->bcb = bcb; vdb->lcb = lcb;
      vdb->e.width = width;  vdb->file = file; vdb->dir = dir;
      if (DBSreallocBuckettable(&(vdb->e))<0) return NULL;
      if (DBSreallocHashtable(vdb)<0) return NULL;
      if (rcb || bcb) {
       vdb->fifo = FIFOcreateMemo(INITSIZE, sizeof(range_r), NULL, NULL);
       if (rcb) {
          range_r relm[1];
          relm->n = 0; relm->tag = 0;
          if (FIFOput(vdb->fifo, relm)<0) errormsg("VDBcreate");
          }
       }
       if (channel) {
          if (!vdb->file) vdb->role = CLIENT;
          vdb->channel.r = channel->r;
          vdb->channel.w = channel->w;
          }
      if (!vdb->dir && vdb->file) VDBread(vdb, vdb->file); 
      // printmsg("VDBcreate %d  %d", vdb->id, vdb->role);
      return vdb;              
      }


     
               
int VDBdestroy(vdb_t vdb) { 
    entries_t *es = &(vdb->e);
    if (es->data) free(es->data);
    if (vdb->array) ALdestroy(vdb->array);
    DBSdeleteHashtable(vdb);
    /*
    if (vdb->role == CLIENT && vdb->channel)
         close(fileno(vdb->channel));
    */
    free(vdb);
    return 0;
    }
            
static idx_t FindEntry(idx_t result, entries_t *es, elm_t *d, int *new) {
     // printmsg("Findentry 0");
     int width = es->width;
     size_t widthbytes = width*sizeof(elm_t);
     if (new) *new = 0;
     while(result >= 0) {
        elm_t *e = es->data + result*width;
        if (memcmp(e, d, widthbytes)==0) {
             // printmsg("Findentry return %d", result);
             return result;
             }
        // printmsg("Findentry 1 %d %d", result, es->next[result]);
        result=es->next[result];
	}
     if (es->size > es->blocksize) 
        return mkerror(ERR_NULL, "Fatal %d > %d", es->size, es->blocksize);
     if (es->size == es->blocksize) {
        int err = DBSreallocBuckettable(es);
        if (err<0) return err;
        }
     if (!new) return es->size;
     *new = 1;
     result = (es->size++);
     memcpy(es->data+result*width, d, widthbytes);
     // printmsg("Findentry 3");
     return result;
     }
     
idx_t VDBgetIdx(vdb_t vdb, elm_t *key) {
     unsigned int hash=HashValue(vdb->e.width, key)&vdb->mask;
     int ptr = vdb->hash[hash];
     idx_t result = FindEntry(ptr, &(vdb->e), key, NULL);
     return result==vdb->e.size?-1:result;
     }
          
static int DBput(vdb_t vdb, elm_t *elm, idx_t *idx, int *new) {
     unsigned int hash=HashValue(vdb->e.width, elm)&vdb->mask;
     int ptr = vdb->hash[hash], err = 0;
     idx_t result = FindEntry(ptr, &(vdb->e), elm, new);
     // if (vdb->id==0) printmsg("VDPut 0 ptr = %d result = %d", ptr, result);
     if ((new && *new) || (!new && result==vdb->e.size)) {
       vdb->e.next[result] = ptr;
       vdb->hash[hash] = result;
       if (vdb->hashsize<=vdb->e.size) {
          if ((err = DBSreallocHashtable(vdb))!=0) return err;  
          }
       err = 1;
       }
       if (idx) idx[0] = result;
       return result<0?result:err;
     // printmsg("VDPut 1"); 
     }
     
static void Get(vdb_t vdb, elm_t *elm, idx_t idx) {
    memcpy(elm, vdb->e.data+idx*vdb->e.width, vdb->e.width*sizeof(elm_t));
    } 
    
static int PutServer(vdb_t vdb, elm_t *elm, int *idx, int *nw) {
      /* Server */
      int start, i, n;
      FILE *rd = vdb->channel.r,
           *wr = vdb->channel.w;
      // printmsg("PutServer %d id = %d tos = %d", vdb->id,id, vdb->tos[id]);
      E(readintUTF(rd , &start));
      E(readintUTF(rd, elm));
      E(readintUTF(rd, elm+1));
      DBput(vdb, elm, idx, nw);
      if (*idx<start) errormsg("Server: Something wrong idx=%d<start=%d", 
          *idx, start);
      n = *idx-start+1;
      E(writeintUTF(wr, n));
      E(writeintUTF(wr, *idx));
      for (i=0;i<n;i++) {
        Get(vdb, elm, start+i);
        E(writeintUTF(wr,elm[0]));
        E(writeintUTF(wr,elm[1]));
        }
      fflush(wr);
      return 0;
      }
      
static idx_t PutClient(vdb_t vdb, elm_t *elm, int *new) {
      int i, n=-1;idx_t idx;
      if ((idx=VDBgetIdx(vdb, elm))>=0) {new = 0; return idx;} 
      // fprintf(stderr,"PutClient writeint %d\n",vdb->id); 
      E(writeintUTF(vdb->channel.w, vdb->id));
      // fflush(vdb->channel.w);
      E(fputc(PUT, vdb->channel.w));  
      E(writeintUTF(vdb->channel.w, (int) vdb->e.size));
      E(writeintUTF(vdb->channel.w, elm[0]));
      E(writeintUTF(vdb->channel.w, elm[1]));
      fflush(vdb->channel.w);
      resetTimer(timer);
      startTimer(timer);
      E(readintUTF(vdb->channel.r, &n));
      stopTimer(timer);
      vdb->msgCount++;
        {
        float t = timerReal(timer);
        if (vdb->msg_times) GZprintf(vdb->msg_times, "%10.6f\n", t); 
        vdb->msgTime+= t;
        if (t>vdb->maxMsgTime) vdb->maxMsgTime = t;
        if (t<vdb->minMsgTime) vdb->minMsgTime = t;
        }
      E(readintUTF(vdb->channel.r, &idx));
      for (i=0;i<n;i++) {
         E(readintUTF(vdb->channel.r, elm));
         E(readintUTF(vdb->channel.r, elm+1));
         DBput(vdb, elm, NULL, new);
         // printmsg("Client:id = %d idx = %d", vdb->id, idx);
         }
      return idx;
      }
      
         
static int GetClient(vdb_t vdb, elm_t *elm, idx_t idx, int *count) {
      int i, new, n; 
      E(writeintUTF(vdb->channel.w, vdb->id));
      E(fputc(GET, vdb->channel.w));
      E(writeintUTF(vdb->channel.w, (int) vdb->e.size));
      E(writeintUTF(vdb->channel.w, idx));
      fflush(vdb->channel.w);
      // printmsg("GetClient %d: start=%d idx=%d", vdb->id, vdb->e.size, idx);
      resetTimer(timer);
      startTimer(timer);
      E(readintUTF(vdb->channel.r, &n));
      stopTimer(timer);
      vdb->msgCount++;
        {
        float t = timerReal(timer);
        if (vdb->msg_times) GZprintf(vdb->msg_times, "%10.6f\n", t);
        vdb->msgTime+= t;
        if (t>vdb->maxMsgTime) vdb->maxMsgTime = t;
        if (t<vdb->minMsgTime) vdb->minMsgTime = t;
        }
      if (n==0) return -1;
      if (idx>=-1)
      for (i=0;i<n;i++) {
         elm_t aux[2]; idx_t id;
         E(readintUTF(vdb->channel.r, aux));
         E(readintUTF(vdb->channel.r, aux+1));
         DBput(vdb, aux, &id, &new);
         if (elm && id == idx) {elm[0]=aux[0]; elm[1]=aux[1];}
         // printmsg("Client:id = %d idx = %d", vdb->id, idx);
         }
      if (count) *count = n;
      return 0;
      }
      
static int GetServer(vdb_t vdb, elm_t *elm, int all) {
      /* Server */
      int start, i, idx, n;
      FILE *rd = vdb->channel.r, *wr = vdb->channel.w;
      E(readintUTF(rd, &start));
      E(readintUTF(rd, &idx));
      // printmsg("VDB Get server %d idx = %d", all, idx);
      if (idx>=VDBgetCount(vdb)) n=0;
      else
      n = all>0? VDBgetCount(vdb)-start:idx-start+1;
      
      E(writeintUTF(wr,n));
      /* 
      if (all==1 && n>0) printmsg("Synchronize id = %d channel = %d: n = %d", 
      vdb->id, vdb->channel.r, n);
      */
      if (all<2) { 
      for (i=0;i<n;i++) {
        elm_t aux[2];
        Get(vdb, aux, start+i);
        E(writeintUTF(wr,aux[0]));
        E(writeintUTF(wr,aux[1]));
        if (elm && start+i==idx) { elm[0]=aux[0];elm[1]=aux[1];}
        }
        }
      fflush(wr);
      return 0;
      }      
           
int VDBput(vdb_t vdb, elm_t *elm,  int *new) {
     int nw, idx;
     elm_t data[2];
     if (vdb->role == CLIENT) return PutClient(vdb, elm, new?new:&nw);
     // printmsg("id: %d role =%d", vdb->id, vdb->role);
     if (!elm) {
          if (PutServer(vdb, data, &idx, &nw)<0) return -1;
          elm = data;
          }
     else
       DBput(vdb, elm, &idx, &nw);
     // if (vdb->role==SERVER) printmsg("QQQ %d (%d)", vdb->file, nw);
     if (!vdb->array && vdb->file && nw) {
        writePair(vdb->file, elm);
        // if (VDBgetCount(vdb)<100) fflush(vdb->file);
        }
     if (new) *new = nw;
     return idx;
     }
          
int VDBtruncate(vdb_t vdb, int count) {
    entries_t *es = &(vdb->e);
    int hashsize = vdb->hashsize, i, width = es->width, err;
    if (count > es->size) return -1;
    if (count == es->size) return 0;
    // printmsg("VDBtruncate count = %d < %d = size",
    // count, es->size);
    for (i=hashsize-1;i>=0;i--) vdb->hash[i] = -1;
    for (i=es->size-1;i>=0;i--) es->next[i] = -1;
    es->size = 0;
    if (count>0) {
        for (i=0;i<count;i++) {
            if (DBput(vdb, (elm_t*) (es->data+i*width), NULL, NULL))
              es->size++;
            }
        } 
    vdb->first = es->size; 
    if (vdb->file) 
       if ((err = Ftruncate(vdb->file, (long) (es->size*getRecordSize())))<0) 
           return err;
    return 0;
    }
                
int VDBget(vdb_t vdb, elm_t *elm, idx_t idx) {
     if (idx >= vdb->e.size && vdb->role == CLIENT) {
         return GetClient(vdb, elm, idx, NULL);
         }
     if (vdb->role == SERVER && idx<0) {
         return GetServer(vdb, elm, 0);
         }
     if (idx >=vdb->e.size) return -1;
     if (elm) Get(vdb, elm, idx);
     return 0;
     }
     
     
#ifdef LINUX     
static int GetTag(vdb_t vdb, channel_t channel) {
     vdb->channel.r = channel->r;
     vdb->channel.w = channel->w;
     return fgetc(vdb->channel.r);
     }         
#endif
    
int VDBgetCount(vdb_t vdb) {
     return vdb->e.size;
     }
     
void *VDBgetTag(vdb_t vdb) {
     return vdb->tag;
     }
     
int VDBgetId(vdb_t vdb) {
     return vdb->id;
     }
                    
int VDBrequestPut(vdb_t vdb, void *tag, elm_t *elm) {
     idx_t idx;
     if ((idx=VDBput(vdb, elm, NULL))<0) errormsg("VDBrequestPut");
     // printmsg("elm = (%d, %d), idx = %d", elm[0], elm[1], idx);
     if (tag && vdb->gcb) vdb->gcb(vdb->id, tag, idx);
     return 0;
     }

int VDBrequestGetIdx(vdb_t vdb, void *tag, elm_t *elm) {
     unsigned int hash=HashValue(vdb->e.width, elm)&vdb->mask;
     int ptr = vdb->hash[hash];
     idx_t idx = FindEntry(ptr, &(vdb->e), elm, NULL);
     if (idx>=vdb->e.size) idx = -1;
     if (tag && vdb->gcb) vdb->gcb(vdb->id, tag, idx);
     return 0;
     }

int VDBsetBarrier(vdb_t vdb, void *tag) {
     range_r relm[1];
     unsigned int  ofs = vdb->first, n = VDBgetCount(vdb);
     // if (tag==NULL) errormsg("Tag must be unequal to NULL");
     for (ofs+=INTERVAL; ofs<n; ofs += INTERVAL) {
          relm->n = ofs; relm->tag = NULL;
          if (FIFOput(vdb->fifo, relm)<0) errormsg("VDBsetMarker");
          }
     relm->n = n; relm->tag = NULL;
     if (FIFOput(vdb->fifo, relm)<0) errormsg("VDBsetMarker");
     relm->tag = tag; SETMARKER(relm);
     if (FIFOput(vdb->fifo, relm)<0) errormsg("VDBsetMarker"); 
     return 0;
     }
          
int VDBforceSome(vdb_t vdb, VDBforcemode_t mode) {
     int done = 0, len, first = 1;
     range_r relm[1];
     while (FIFOget(vdb->fifo, relm)>=0) {
          if (ISMARKER(relm)) {
          if (mode == VDBuntilMark) {
              FIFOunget(vdb->fifo); return done;
              }
           if (first==0) {
              vdb->rcb(vdb->id, vdb->first, 0);
              if (mode == VDBoneMark) { 
              FIFOunget(vdb->fifo);return done;}
              }
          first = 0;
          if (vdb->bcb) {
               int r =  vdb->bcb(vdb->id, relm->tag);
               vdb->tag = relm->tag; 
               if (r<0) return done;
               }
               }
          else {
             len = relm->n-vdb->first;
             // printmsg("What now len = %d done = %d", len, done);
             if (len>0 && vdb->rcb) {
             vdb->rcb(vdb->id, vdb->first, len);
             vdb->first += len;
             done = 1;
             return done;
             }
          }
      }
    // printmsg("Alway range callback");
    len = VDBgetCount(vdb) - vdb->first;
    if (/* len>0 && */ vdb->rcb) {    // Always range callback
        vdb->rcb(vdb->id, vdb->first, len);
        vdb->first = VDBgetCount(vdb); 
        if (len>0) done = 1;
        } 
    return done;
    }    

int VDBsetChannel(vdb_t vdb, channel_t channel) {
    vdb->channel.r = channel->r;
    vdb->channel.w = channel->w;
    return 0;
    }

file_t VDBgetFile(vdb_t vdb) {return vdb->file;}

#ifdef LINUX
    
int VDBreact(vdb_t vdb, channel_t channel) { 
    int tag = GetTag(vdb, channel);
    elm_t elm[2];
      // printmsg("Start react %c", tag);
      switch (tag) {
        case PUT: E(VDBput(vdb, NULL, NULL)); break;
        case GET: E(VDBget(vdb, elm, -1));  break;
        default: errormsg("VDBreact:Illegal tag %d", tag);
      }
    // printmsg("End react %d", tag);
    return 0;           
    }   
#else
    int VDBreact(vdb_t vdb) {
      printmsg("VDBreact not implemented"); return 0;}  
#endif   

int VDBupdateFile(vdb_t vdb) {
  if (vdb->file) {
    int i, n = VDBgetCount(vdb),
    width = VDBgetWidth(vdb);
    DECLA(elm_t, elm, width);
    Ftruncate(vdb->file, 0);
    for (i=0;i<n;i++) {
        VDBget(vdb, elm, i);
        // printmsg("Test id = %d n = %d (%d %d)", vdb->id, n, elm[0], elm[1]);
        if (width==2) writePair(vdb->file, elm);
        else fwrite(elm, sizeof(elm_t), (size_t) width, vdb->file);
        }
    fflush(vdb->file);
    }
   return 0;
  }

/*
array_t VDBgetArray(vdb_t vdb) {return vdb->array;}

void VDBsetArray(vdb_t vdb, array_t array) {vdb->array = array;}
*/

vdb_t VDBcreateExtra(int id, int keylength, int valwidth, file_t *file, 
load_cbt lcb) {
     vdb_t vdb = VDBcreate(id, keylength, (file?file[0]:NULL), NULL, NULL, NULL, NULL, NULL, lcb);
     vdb->array = ALcreate(10, valwidth, (file?file[1]:NULL), vdb);
     return vdb;
     }
      
void VDBputExtra(vdb_t vdb, idx_t idx, void *obj) {
     ALupdate(vdb->array, idx, obj);
     } 

int VDBaddExtra(vdb_t vdb,  void *obj) {
     return ALadd(vdb->array, obj);
     } 

void VDBgetExtra(vdb_t vdb,  void *obj, idx_t idx) {
     ALget(vdb->array, idx, obj);
     }
     
void VDBflush(vdb_t vdb, idx_t idx) {
     if (!vdb->array) return;
     {
     int i, widthv = VDBgetWidth(vdb), widtha = ALgetWidth(vdb->array);
     FILE *file = vdb->file, *file2 = ALgetFile(vdb->array);
     DECLA(elm_t, elm, widthv);
     DECLA(char, elma, widtha);
     if (!file || !file2) errormsg("VDBflush: No files available");
     for (i=vdb->first;i<=idx;i++) {
        if (VDBget(vdb, elm, i)<0) errormsg("VDBflush: Illegal index %d", i);
        // printmsg("Test id = %d n = %d (%d %d)", vdb->id, n, elm[0], elm[1]);
        fwrite(elm, widthv*sizeof(elm_t), 1, file);
        VDBgetExtra(vdb, elma, i);
        /* printmsg("%d VDBflush  (%d %d %d)", 
       ftell(file2), *((int*) elma), *((int*) (elma+4)), *((int*)
       (elma+8))); */
        fwrite(elma, (size_t) widtha, 1, file2);
        }
     vdb->first = i;
     // fflush(file);fflush(file2); 
     }
     }

float VDBgetMsgTime(vdb_t vdb) {
           // fprintf(stderr,"msgTime: %15.9f\n", tdb->msgTime);
           return vdb->msgTime;
           }
float VDBgetMsgMinTime(vdb_t vdb) {return vdb->minMsgTime;}
float VDBgetMsgMaxTime(vdb_t vdb) {return vdb->maxMsgTime;}

void VDBsetNewLevel(vdb_t vdb) {
         vdb->minMsgTime=1000.0;
         vdb->maxMsgTime=0.0;
         vdb->msgTime = 0.0;
         vdb->msgCount = 0;
         }

unsigned long VDBgetMsgCount(vdb_t vdb) {
   return vdb->msgCount;
  }

