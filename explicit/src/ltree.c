/* $Id: ltree.c,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

/* #define E(X) if ((err=X)<0) errormsg(""#X) */
#define E(X) if ((err=X)<0) abort()
#include <stdio.h>
#include "param0.h"
#include "utl.h"
#include "fifo.h"
#include <string.h>
#include <assert.h>

#define VALUE(x) ((x)&mask)
#define SETLEAF(x) (x)|=~mask_leaf
#define CLEARLEAF(x) (x)&=mask_leaf
#define ISLEAF(x) (((x)&~mask_leaf)?1:0)

#define SETMARK(x) (x)|=~mask_mark
#define CLEARMARK(x) (x)&=mask_mark
#define ISMARK(x) (((x)&~mask_mark)?1:0)

static FILE *tty;

// static unsigned int mask = 0x04fff

#define mask 0x3fffffff 
#define mask_leaf 0x7fffffff 
#define mask_mark 0xbfffffff
#define LTRSIZE 100000
#define INITSIZE 300
typedef int (*object_cb)(int idx, void *rec);
typedef int (*parent_cb)(void *rec, idx_t current, int leaf, int marked);
typedef int (*join_cb) (void *trans, int join, idx_t current, int length, int
leaf, int marked);
typedef int (*mark_cb) (int idx, int join, idx_t endpoint);

typedef int (*trace_cb)(void *rec, idx_t current);

typedef struct {
      int width, lv_pt, bf_pt, lf_pt, nlv_pt, mk_pt;
      /*lv_pt level pointer, nlv_pt next level_pt, 
        bf_pt buffer pointer lf_pt leaf pointer */
      file_t file, bf_fp, lf_fp, lv_fp, mk_fp;
      dir_t dir;
      fifo_t bf, lf, lv, mk;
      char *object; /* Auxilary array for temporary storing an object */
      } ltr_r, *ltr_t;

typedef struct {
      idx_t endpoint, leaf;
      int length;
      } leaf_r;

typedef struct {
      idx_t endpoint, leaf;
      int length, depth, id;
      } mark_r;
            
typedef struct {
      int current;
      int end, end_join, end_mark;
      int nstates;
      } level_r;
            
static FILE *CheckpointOpen(dir_t dir, char *name) {
      char buf[256];
      FILE *fp;
      sprintf(buf,"%s/fifo1", dir);
      fp = fopen(buf,"r+");
      if (fp==NULL) {
        errno = 0;
        fp = fopen(buf,"w");} 
      if (fp==NULL) errormsg("file \"%s\"", buf);
      return fp;
      }
       
static int PushLevels(ltr_t ltr) {
     int err = ERR_EMPTY;
     while ((err=FIFOunpop(ltr->lv))==0) {FIFOunpop(ltr->bf);
          FIFOunpop(ltr->lf);FIFOunpop(ltr->mk);} 
     FIFOunpop(ltr->bf);FIFOunpop(ltr->lf);FIFOunpop(ltr->mk);
     return err==ERR_EMPTY?1:err;
     }
          
int LTRgetBounds(ltr_t ltr, idx_t *start, idx_t *end, int *start_join,
int *end_join, int *start_mark, int *end_mark) {
     int err=0;
     level_r level1 = {0,0,0,0,0}, level2 = {0,0,0,0,0};
     level2.end = FIFOgetCount (ltr->bf);
     level2.end_join = FIFOgetCount(ltr->lf); 
     level2.end_mark=  FIFOgetCount(ltr->mk); 
     if (ltr->lv_pt>0 && (start || start_join || start_mark)) {
        E(FIFOgetElm(ltr->lv, ltr->lv_pt-1, &level1));
        }
     if (start) *start = level1.end;
     if (start_join) *start_join = level1.end_join;
     if (start_mark) *start_mark = level1.end_mark;
     if (err>=0) {
        if (ltr->lv_pt<FIFOgetCount(ltr->lv) && (end || end_join || end_mark)) {
           E(FIFOgetElm(ltr->lv, ltr->lv_pt, &level2));}
        if (end) *end = level2.end;
        if (end_join) *end_join = level2.end_join;
        if (end_mark) {
           *end_mark = level2.end_mark;
           }
        }
     return err;
     }
     
static int NewLevel(ltr_t ltr) {
      level_r level = {-1, 0, 0, 0};
      // fprintf(tty, "Highest Level1 lv_pt %d < %d nlevels\n",
      // ltr->lv_pt, FIFOgetCount(ltr->lv)-1);
      if (ltr->lv_pt<FIFOgetCount(ltr->lv)-1) return 1;
      level.end = FIFOgetCount(ltr->bf);
      level.end_join = FIFOgetCount(ltr->lf);
      level.end_mark = FIFOgetCount(ltr->mk);
      ltr->nlv_pt =FIFOgetCount(ltr->lv);
      if (FIFOput(ltr->lv, &level)<0) errormsg("LTRnewlevel");
      // fprintf(tty, "Highest Level2 lv_pt %d < %d nlevels\n",
      // ltr->lv_pt, FIFOgetCount(ltr->lv)-1);
      return 0;
      }

int LTRnewLevel(ltr_t ltr) {
    ltr->lv_pt++; ltr->nlv_pt = ltr->lv_pt+1;
    // fprintf(stderr,"NewLevel %d\n", ltr->lv_pt);
    return NewLevel(ltr);
    }  
                                    
ltr_t LTRcreateMemo(int width, file_t file, dir_t dir) {
      ltr_t ltr;
      tty = fopen("/dev/tty", "w"); 
      // fprintf(tty,"mask_mark = %lx\n", mask_mark);
      if (!(ltr = (ltr_t) calloc(1, sizeof(ltr_r)))) {
        mkerror(ERR_NULL, "Cannot allocate dbs (size = %d)",
        sizeof(ltr_r)); return NULL;}
      ltr->file = file; ltr->dir = dir;
      ltr->width = width;
      ltr->bf_pt = ltr->lf_pt = -1;  ltr->nlv_pt = ltr->lv_pt = -1;
      ltr->object = malloc(width+sizeof(int)+1000);
      if (dir!=NULL) {
          ltr->bf_fp = CheckpointOpen(dir, "fifo1");
          ltr->lf_fp = CheckpointOpen(dir, "fifo2");
          ltr->lv_fp = CheckpointOpen(dir, "fifo3");
          ltr->mk_fp = CheckpointOpen(dir, "fifo4");
          }
      ltr->bf = FIFOcreateMemo(LTRSIZE, width+sizeof(int), ltr->bf_fp, NULL);
      ltr->lf = FIFOcreateMemo(LTRSIZE, width+sizeof(leaf_r), ltr->lf_fp, NULL);
      ltr->lv = FIFOcreateMemo(INITSIZE, sizeof(level_r), ltr->lv_fp, NULL);
      ltr->mk = FIFOcreateMemo(INITSIZE, width+sizeof(mark_r), ltr->mk_fp, NULL);
      if (NewLevel(ltr)<0) return NULL;
      return ltr;
      }

int LTRdestroy(ltr_t ltr) {
      free(ltr->object);
      FIFOdestroy(ltr->bf); FIFOdestroy(ltr->lf); 
      FIFOdestroy(ltr->lv); FIFOdestroy(ltr->mk); 
      free(ltr);
      return 0;
      }
      

            
int LTRreset(ltr_t ltr) {
      FIFOreset(ltr->bf); FIFOreset(ltr->lf);
      FIFOreset(ltr->lv); FIFOreset(ltr->mk);
      ltr->bf_pt = ltr->lf_pt = ltr->lv_pt = 
      ltr->nlv_pt = ltr->mk_pt= -1;
      return NewLevel(ltr);
      }

int LTRgetLevel(ltr_t ltr, idx_t idx) {
      int l = ltr->lv_pt, start;
      ltr->lv_pt = ltr->lv_pt<FIFOgetCount(ltr->lv)-1?ltr->lv_pt+1:
      ltr->lv_pt; 
      for (LTRgetBounds(ltr, &start, NULL, NULL, NULL, NULL, NULL); 
           ltr->lv_pt>0 && idx < start; ltr->lv_pt--,
           LTRgetBounds(ltr, &start, NULL, NULL, NULL, NULL, NULL));
      start = ltr->lv_pt; ltr->lv_pt = l;
      return start;
      }
                 
static int SetLevelCurrent(ltr_t ltr) {
      int err, start, end, start_join, end_join, start_mark, end_mark;
      PushLevels(ltr);
      ltr->lv_pt=ltr->nlv_pt = FIFOgetCount(ltr->lv)-1;
      LTRgetBounds(ltr, &start, &end, &start_join, &end_join, &start_mark,
          &end_mark);
      // fprintf(tty, "SetLevelCurrent lv_pt = %d start = %d end = %d pt = %d\n",
      // ltr->lv_pt, start, end, ltr->bf_pt);
      for (;ltr->lv_pt>0 && ltr->bf_pt < start; 
         ltr->lv_pt--,LTRgetBounds(ltr, &start, &end, &start_join, &end_join,
         &start_mark, &end_mark)) {
         E(FIFOpop(ltr->lv,1)); 
         E(FIFOpop(ltr->bf, FIFOgetCount(ltr->bf)-start));
         E(FIFOpop(ltr->lf, FIFOgetCount(ltr->lf)-start_join));
         E(FIFOpop(ltr->mk, FIFOgetCount(ltr->mk)-start_mark));
         }
      // fprintf(tty, "SetLevelCurrent lv_pt = %d==%d? start = %d end = %d pt = %d\n",
      // ltr->lv_pt, FIFOgetCount(ltr->lv)-1, start, end, ltr->bf_pt);
      if (ltr->lv_pt == FIFOgetCount(ltr->lv)-1) { 
         if (FIFOunpop(ltr->lv)>=0) {
            FIFOunpop(ltr->bf);
            FIFOunpop(ltr->lf);
            FIFOunpop(ltr->mk);
            }  
         /* Bert */
         else if (ltr->lv_pt == FIFOgetAllCount(ltr->lv)-1) {
            NewLevel(ltr);
            }
         }
      // fprintf(tty,
      //  "SetLevelCurrent pop: lv %d: start =%d end=%d N= %d start_join = %d\n",
      //   ltr->lv_pt, start, end, FIFOgetCount(ltr->lf)-start_join, start_join); 
      assert(ltr->lv_pt<FIFOgetCount(ltr->lv));
      if (ltr->bf_pt<start || ltr->bf_pt>=end) {
           fprintf(tty, "%d<=%d<%d\n", start, ltr->bf_pt, end);
           abort();
           }
      assert(ltr->bf_pt==-1 || (ltr->bf_pt>= start && ltr->bf_pt<end));
      return ltr->lv_pt<1?1:0;
      }
                  
int LTRtruncate(ltr_t ltr) {
      int start, end, i;
      LTRgetBounds(ltr, NULL, &start, NULL, NULL, NULL, NULL);
      FIFOput(ltr->lv, NULL); FIFOput(ltr->bf, NULL);
      FIFOput(ltr->lf, NULL);  FIFOput(ltr->mk, NULL);
      end = FIFOgetCount(ltr->bf);
      // fprintf(tty,"level = %d current %d start=%d end = %d\n", 
      //    ltr->lv_pt, ltr->bf_pt, start, end);
      for (i=start;i<end;i++) {
           FIFOgetElm(ltr->bf, i, ltr->object);
           SETLEAF(*((int*)ltr->object));
           FIFOupdateElm(ltr->bf, i, ltr->object);
           }
      if (ltr->lv_pt<=FIFOgetCount(ltr->lv)-2) {
          level_r level;
          FIFOgetElm(ltr->lv, ltr->lv_pt+1, &level);
          level.nstates = 0;
          FIFOupdateElm(ltr->lv, ltr->lv_pt+1, &level);
          }
      return 0;
      }
      
int LTRgetNumberOfMarks(ltr_t ltr);

static void UpdatePointers(ltr_t ltr, int bf_pt) {
      int  start_join, start_mark, end_join = FIFOgetAllCount(ltr->lf),
      end_mark = FIFOgetAllCount(ltr->mk), i;
      LTRgetBounds(ltr, NULL, NULL,  &start_join, NULL, &start_mark, NULL);
      for (i=start_join;i<end_join;i++) {
        leaf_r r;
        FIFOgetElm(ltr->lf, i, &r);
        if (r.leaf>bf_pt || VALUE(r.endpoint)>bf_pt) {
           // fprintf(tty, "update leaf: (endpoint,leaf) (%d,%d) > pt=%d\n", 
           // r.endpoint, r.leaf, bf_pt);
           if (r.leaf>bf_pt) r.leaf++; 
           if (r.endpoint>bf_pt) r.endpoint++;
           FIFOupdateElm(ltr->lf, i, &r);
           }
        }
      for (i=start_mark;i<end_mark;i++) {
        mark_r r;
        FIFOgetElm(ltr->mk, i, &r);
        if (r.leaf>bf_pt || r.endpoint>bf_pt) {
          // fprintf(tty, "update mark: (endpoint,leaf) (%d,%d) > pt=%d\n", 
          //  r.endpoint, r.leaf, bf_pt);
          if (r.leaf>bf_pt) r.leaf++; 
          if (r.id>bf_pt) r.id++; 
          if (r.endpoint>bf_pt) r.endpoint++;
          FIFOupdateElm(ltr->mk, i, &r);
          }
        }
      }
                            
int LTRput(ltr_t ltr, idx_t parent, void *obj, idx_t *idx) { 
      level_r level; int i, end,  err;
      LTRgetBounds(ltr, NULL, &end,  NULL, NULL, NULL, NULL);
      // fprintf(tty, "QQQ lv_pt = %d end = %d\n", ltr->lv_pt, end);
      
      // Reorder Level
      SETLEAF(parent);
      memcpy(ltr->object, &parent, sizeof(int));
      memcpy(ltr->object+sizeof(int), obj, ltr->width);
      CLEARLEAF(parent);
      err = FIFOput(ltr->bf, ltr->object);
      for (i= FIFOgetCount(ltr->bf)-1; i>end;i--) {
          FIFOgetElm(ltr->bf, i-1, ltr->object);
          if (VALUE(*(int*) ltr->object)<=parent) break;
          FIFOupdateElm(ltr->bf, i, ltr->object);
          }
      // i==end || parent0 > parent increasing parents
      if (i<FIFOgetCount(ltr->bf)-1) { 
        SETLEAF(parent);
        memcpy(ltr->object, &parent, sizeof(int));
        memcpy(ltr->object+sizeof(int), obj, ltr->width);
        FIFOupdateElm(ltr->bf, i, ltr->object);
        UpdatePointers(ltr, i);
        err = 1;
        }
      if (idx) *idx = i;
      if (ltr->lv_pt<FIFOgetCount(ltr->lv)-1) ltr->nlv_pt = ltr->lv_pt + 1;
      FIFOgetElm(ltr->lv, ltr->nlv_pt, &level);
      level.current =  (ltr->lv_pt==-1?i:-1);
      level.end = FIFOgetCount(ltr->bf); 
      // fprintf(tty,"Hallo lv_pt %d count %d (N=%d\n", 
      // ltr->lv_pt, FIFOgetCount(ltr->lv), FIFOgetCount(ltr->bf)); 
      assert(FIFOgetCount(ltr->bf)==1 || 
           ltr->lv_pt == FIFOgetCount(ltr->lv)-2);
      for (i=FIFOgetAllCount(ltr->lv)-1;i>=ltr->nlv_pt;i--)
          FIFOupdateElm(ltr->lv, i, &level);
      return err;
      }

int LTRget(ltr_t ltr, void *obj) {
      int err;
      if ((err=FIFOgetElm(ltr->bf, ltr->bf_pt, ltr->object))<0) return mkerror(err,"LTRget");
      memcpy(obj, ltr->object+sizeof(int), ltr->width);
      return err;
      }
      
int LTRgetElm(ltr_t ltr, idx_t idx, void *obj) {
      int err;
      if ((err=FIFOgetElm(ltr->bf, idx, ltr->object))<0) return mkerror(err,"LTRget");
      memcpy(obj, ltr->object+sizeof(int), ltr->width);
      return err;
      }
      
idx_t LTRgetCurrent(ltr_t ltr) {return ltr->bf_pt;}

int LTRsetCurrent(ltr_t ltr, idx_t current) {
    level_r level;
    ltr->bf_pt = current;
    SetLevelCurrent(ltr);
    if (ltr->lv_pt>=0) {
       FIFOgetElm(ltr->lv, ltr->lv_pt, &level);
       level.current =  ltr->bf_pt;
       FIFOupdateElm(ltr->lv, ltr->lv_pt, &level);
       }
    // fprintf(tty,"LTRsetCurrent %d\n", ltr->lv_pt);
    return ltr->lv_pt==0?1:(ltr->lv_pt>=FIFOgetAllCount(ltr->lv)-2?2:0);
    }

int LTRfinishState(ltr_t ltr, idx_t current) {
    if (current>=0) {
        level_r level;
        FIFOgetElm(ltr->lv, ltr->lv_pt, &level);
        level.nstates++;
        FIFOupdateElm(ltr->lv, ltr->lv_pt, &level);
        FIFOgetElm(ltr->bf, current, ltr->object);
        if (ISLEAF(*((int*)ltr->object))) {
            CLEARLEAF((*(int*) ltr->object));
            FIFOupdateElm(ltr->bf, current, ltr->object);
            FIFOgetElm(ltr->lv, ltr->lv_pt, &level);
            }
       }
    return 0;
    }

int LTRgetLevelInfo(ltr_t ltr, int level_pt, int *nstates, int *visited,
int *ntransitions) {
    level_r lev;
    if (level_pt>=0) {
        FIFOgetElm(ltr->lv, level_pt, &lev);
        if (nstates) *nstates = lev.nstates;
        if (visited) *visited = lev.end;
        if (ntransitions) *ntransitions = lev.end + lev.end_join;
        } else {
          if (nstates) *nstates = 0;
          if (visited) *visited = 0;
          if (ntransitions) *ntransitions = 0;
        }
    if (ltr->lv_pt<FIFOgetCount(ltr->lv)-1) {
        FIFOgetElm(ltr->lv, level_pt+1, &lev);
        if (visited) *visited = lev.end-(*visited);
        if (ntransitions) *ntransitions = lev.end+lev.end_join-(*ntransitions);
        }
     else {
        if (visited) *visited =FIFOgetCount(ltr->bf)-(*visited);
        if (ntransitions) *ntransitions = FIFOgetCount(ltr->bf)+ 
                    FIFOgetCount(ltr->lf)-(*ntransitions);
        }
    return 0;
    }

int LTRgetCumLevelInfo(ltr_t ltr, int level_pt, int *nstates, int *visited,
int *ntransitions) 
    {
    level_r lev;
    FIFOgetElm(ltr->lv, level_pt, &lev);
    if (ltr->lv_pt<FIFOgetCount(ltr->lv)-1) 
        FIFOgetElm(ltr->lv, level_pt+1, &lev);
    else
        FIFOgetElm(ltr->lv, level_pt, &lev);
    if (ntransitions) *ntransitions =  lev.end + lev.end_join;
    if (visited) *visited = lev.end;
    if (nstates) {
         int i;
         level_r lev; 
        *nstates = 0;
         for (i=0;i<=level_pt;i++) {
           FIFOgetElm(ltr->lv, i, &lev);
           *nstates += lev.nstates;
           } 
         }
    return 0;
    }
         
int LTRgetTotalLevelInfo(ltr_t ltr, int *nstates, int *visited,
int *ntransitions) 
    {
    level_r lev;
    if (visited) *visited = FIFOgetAllCount(ltr->bf);
    if (ntransitions) *ntransitions =  FIFOgetAllCount(ltr->bf)+
      FIFOgetAllCount(ltr->lf);
    if (nstates) {
        int i; 
        *nstates = 0;
        for (i=FIFOgetAllCount(ltr->lv)-1;i>=0;i--) {
           FIFOgetElm(ltr->lv, i, &lev);
           *nstates += lev.nstates;
           }
        }
    return 0;
    }
            
idx_t LTRgetParent(ltr_t ltr, int child) {
     int parent;
     FIFOgetElm(ltr->bf, child, ltr->object);
     memcpy(&parent, ltr->object, sizeof(int));
     return VALUE(parent);
     }
     
int LTRisLeaf(ltr_t ltr, idx_t idx) {
     FIFOgetElm(ltr->bf, idx, ltr->object);
     return ISLEAF(*((int*)ltr->object));
     }
          
int LTRgetNumberOfObjects(ltr_t ltr) {return FIFOgetCount(ltr->bf) ;}        
 
int LTRgetNumberOfLevels(ltr_t ltr) {return FIFOgetCount(ltr->lv);}
 
int LTRgetNumberOfAllLevels(ltr_t ltr) {return FIFOgetAllCount(ltr->lv);}

int LTRdumpCheckpoint(ltr_t ltr, int cid) {return 0;}

int LTRrestoreCheckPoint(ltr_t ltr, int cid) {return 0;}

static void UpdateLeafs(ltr_t ltr, int ptr) {
    int end_mark = FIFOgetCount(ltr->mk), i, start_mark;
    LTRgetBounds(ltr, NULL, NULL,  NULL, NULL, &start_mark, NULL);
    for (i=start_mark;i<end_mark;i++) {
        mark_r r;
        FIFOgetElm(ltr->mk, i, &r);
        if (-r.id-2>ptr) {r.id--;}
        FIFOupdateElm(ltr->mk, i, &r);
        }
    }
    
int LTRmakeJoin(ltr_t ltr, idx_t join, idx_t endpoint, void *obj, idx_t *idx) {
      /*printmsg("Put leaf bf %d lf %d", join, FIFOgetCount(ltr->lf));*/
      leaf_r r; level_r level; 
      int end_join = 0, err, i;
      FIFOgetElm(ltr->bf, endpoint, ltr->object);
      CLEARLEAF((*(int*) ltr->object));
      FIFOupdateElm(ltr->bf, endpoint, ltr->object);
      if (ltr->lv_pt>1) {
        FIFOgetElm(ltr->lv, ltr->lv_pt-1, &level);
        end_join = level.end_join;
        }
      r.leaf = join; r.length = ltr->lv_pt;
      r.endpoint = endpoint;
      memcpy(ltr->object, &r, sizeof(leaf_r));
      memcpy(ltr->object+sizeof(leaf_r), obj, ltr->width); 
      err =   FIFOput(ltr->lf, ltr->object);
      // Reorder
      for (i= FIFOgetCount(ltr->lf)-1; i>end_join;i--) {
          FIFOgetElm(ltr->lf, i-1, ltr->object);
          memcpy(&r, ltr->object, sizeof(leaf_r));
          if (VALUE(r.endpoint)<=endpoint) break;
          FIFOupdateElm(ltr->lf, i, ltr->object);
          }
      if (i<FIFOgetCount(ltr->lf)-1) {
         r.leaf = join; r.length = ltr->lv_pt;
         r.endpoint = endpoint; 
         memcpy(ltr->object, &r, sizeof(leaf_r));
         memcpy(ltr->object+sizeof(leaf_r), obj, ltr->width);
         FIFOupdateElm(ltr->lf, i, ltr->object);
         UpdateLeafs(ltr, i);
         err = 1;
         }
      if (idx) *idx = i;
      FIFOgetElm(ltr->lv, ltr->lv_pt+1, &level);
      level.end_join = FIFOgetCount(ltr->lf);
      for (i=FIFOgetAllCount(ltr->lv)-1;i>ltr->lv_pt;i--)
         FIFOupdateElm(ltr->lv, i, &level);
      return err;
      }
      
int LTRgetNumberOfJoins(ltr_t ltr) {return FIFOgetCount(ltr->lf);}

int LTRsetJoinCurrent(ltr_t ltr, int index) { 
      ltr->lf_pt = index;
      return 0;
      }
      
int LTRgetJoinElm(ltr_t ltr, int idx, void *obj) {
      int err;
      if ((err=FIFOgetElm(ltr->lf, idx, ltr->object))<0) 
          return mkerror(err,"LTRget");
      memcpy(obj, ltr->object+sizeof(leaf_r), ltr->width);
      return 0;
      }
      
int LTRgetJoin(ltr_t ltr, void *obj) {
      int err;
      if ((err=FIFOgetElm(ltr->lf, ltr->lf_pt, ltr->object))<0) return mkerror(err,"LTRget");
      memcpy(obj, ltr->object+sizeof(leaf_r), ltr->width);
      return 0;
      }

int LTRgetJoinLength(ltr_t ltr, int idx) {
      leaf_r r; int err;
      if ((err=FIFOgetElm(ltr->lf, idx, ltr->object))<0) 
          errormsg("LTRsetParent pointer = %d error = %d", 
              idx, err);
      memcpy(&r, ltr->object, sizeof(leaf_r));
      return r.length;
      }
       
idx_t LTRgetJoinSource(ltr_t ltr, int leaf) {
      leaf_r r; int err;
      if ((err=FIFOgetElm(ltr->lf, leaf, ltr->object))<0) 
          errormsg("LTRsetParent pointer = %d error = %d", 
              ltr->lf_pt, err);
      memcpy(&r, ltr->object, sizeof(leaf_r));
      return VALUE(r.endpoint);
      }
      
idx_t LTRgetJoinDestination(ltr_t ltr, int leaf) {
      leaf_r r; int err;
      if ((err=FIFOgetElm(ltr->lf, leaf, ltr->object))<0) 
          errormsg("LTRsetParent pointer = %d error = %d", 
              ltr->lf_pt, err);
      memcpy(&r, ltr->object, sizeof(leaf_r));
      return r.leaf;
      }
        
idx_t LTRgetJoinCurrent(ltr_t ltr) {return ltr->lf_pt;}

int LTRgetCurrentLevel(ltr_t ltr) {return ltr->lv_pt;}

void LTRsetCurrentLevel(ltr_t ltr, int level) {ltr->lv_pt = level;}

void *LTRgetArray(ltr_t ltr) {return FIFOgetArray(ltr->bf);}

static int compare(const void *key, const void *r) {
      return *((int*) key) - VALUE(*((int*) r));
      }
      
int LTRrunFromParent(ltr_t ltr, idx_t parent, parent_cb f) {
      int val = parent, start, end, ofs, width = ltr->width+sizeof(int),
      start_mark, end_mark, ofs0;
      char *obj, *bf = (char*) FIFOgetArray(ltr->bf);
      // if (parent<0)  return -1;
      LTRgetBounds(ltr, &start, &end, NULL, NULL, &start_mark, &end_mark);
      // fprintf(tty, "LTRrunFromParent1 %d < %d < %d pt = %d cnt = %d\n", 
      // start, parent, end, ltr->lv_pt, FIFOgetCount(ltr->lv));
      if (parent>=0) {
         if (start<=parent && parent<end) {
         if (ltr->lv_pt+1<FIFOgetCount(ltr->lv)) {
            level_r level;
            FIFOgetElm(ltr->lv, ltr->lv_pt, &level);
            start = level.end; // start_mark = level.end_mark; 
            FIFOgetElm(ltr->lv, ltr->lv_pt+1, &level);
            end = level.end; // end_mark = level.end_mark;
            }
         else
            return 0;
         } else {
            LTRsetCurrentLevel(ltr, LTRgetCurrentLevel(ltr)-1);
            LTRgetBounds(ltr, NULL, NULL, NULL, NULL, &start_mark, &end_mark);
            LTRsetCurrentLevel(ltr, LTRgetCurrentLevel(ltr)+1);
            }
      }
      // fprintf(tty, "LTRrunFromParent2 %d < %d < %d (val = %d)\n", 
      // start, parent, end, val); 
      if (start >= end) return 0;
      if (parent>=0) {
      if ((obj = (char*) bsearch(&val, bf+start*width , end-start,
            width, compare))==NULL) return 0;
      for (ofs = (obj-bf)/width; ofs>=start; ofs--, obj-=width) {
          if (VALUE(*((int*) obj))!=parent) break;
          }
         ofs++; obj+=width;
         }
      else {ofs = start;}
      for (ofs0 = ofs;ofs<end;ofs++) {
          obj = bf+ofs*width;
          if (parent>=0 && VALUE(*((int*) obj))!=parent) break;
          // fprintf(tty,"%d<%d %lx <%lx (%d)\n", ofs, end, obj, bf+end*width, 
          // end);
          // fprintf(tty,"QQQ %d\n", *obj);
          if (f && f((void*) (obj+sizeof(int)), ofs, ISLEAF(*((int*) obj)), 
             ISMARK(*((int*) obj)))<0) break;
          bf = (char*) FIFOgetArray(ltr->bf);
          }
      return ofs-ofs0;
      }

static int compareLeaf(const void *key, const void *r) {
      return *((int*) key)- VALUE(((leaf_r*)r)->endpoint);
      }
      
int LTRrunJoinsFromParent(ltr_t ltr, idx_t parent, join_cb f) {
      int val = parent, start, end, start_join, end_join,
      ofs, width = ltr->width+sizeof(leaf_r);
      char *obj, *lf = (char*) FIFOgetArray(ltr->lf);
      // if (parent<0) return -1;
      LTRgetBounds(ltr, &start, &end, &start_join, &end_join, NULL, NULL);
      // fprintf(tty,"PrintLeaves start = %d end = %d parent = %d\n",
      // start_join, end_join, parent);
      if (parent>=0) {
         if (start<=parent && parent<end) {
         if (ltr->lv_pt+1<FIFOgetCount(ltr->lv)) {
            level_r level;
            FIFOgetElm(ltr->lv, ltr->lv_pt, &level);
            start_join = level.end_join;
            FIFOgetElm(ltr->lv, ltr->lv_pt+1, &level);
            end_join = level.end_join;
            }
         else
            return 0;
         }
         // fprintf(tty,"PrintLeaves parent = %d level = %d\n", parent,
         //        ltr->lv_pt);
         // fprintf(tty,"PrintLeaves start = %d end = %d parent = %d\n",
         // start_join, end_join, parent);

            if ((obj = (char*) bsearch(&val, lf+start_join*width , end_join-start_join,
                  width, compareLeaf))==NULL) return 0;
            for (ofs = (obj-lf)/width; ofs>=start_join; ofs--, obj-=width) {
                if (VALUE(((leaf_r*) obj)->endpoint)!=parent) break;
                }
         ofs++; obj+=width;
         // fprintf(tty,"Found %d<%d<%d %d=?=%d\n", start_join, ofs, end_join,
         // VALUE(((leaf_r*) obj)->endpoint), parent);
         } 
      else {ofs = start_join; obj = lf+start_join*width;}
      for (start_join = ofs;ofs<end_join;ofs++) {
          int  marked = 0, leaf = 0, join;
          obj = lf+ofs*width;
          if (parent>=0 && VALUE(((leaf_r*) obj)->endpoint)!=parent) break;
          join = ((leaf_r*) obj)->leaf;
          marked = ISMARK(((leaf_r*) obj)->endpoint)?1:0;
          leaf = LTRisLeaf(ltr, join);
          if (f((void*) (obj+sizeof(leaf_r)), ofs, join, 
              ((leaf_r*) obj)->length, leaf, marked)<0) break;
          lf = (char*) FIFOgetArray(ltr->lf);
          }
      return ofs-start_join;
      }

int LTRrunThroughObjects(ltr_t ltr, object_cb cb) {
      int i, n = FIFOgetAllCount(ltr->bf), width = ltr->width+sizeof(int);
      char *bf = ((char*) FIFOgetArray(ltr->bf))+sizeof(int),
           *lf = ((char*) FIFOgetArray(ltr->lf))+sizeof(leaf_r);
      for (i=0;i<n;i++,bf+=width) {
         if (cb(i, bf)<0) return 1;
         }
      width = ltr->width+sizeof(leaf_r);
      n = FIFOgetAllCount(ltr->lf);
      for (i=0;i<n;i++,lf+=width) {
         if (cb(-i-2, lf)<0) return 1;
         }
      return 0;
      }

int LTRgetJoinOfMark(ltr_t ltr, int idx) {
      mark_r r; int err;
      if ((err=FIFOgetElm(ltr->mk, idx, ltr->object))<0) 
          errormsg("LTRsetParent pointer = %d error = %d", 
              idx, err);
      memcpy(&r, ltr->object, sizeof(mark_r));
      return r.id;
      } 
                  
idx_t LTRgetStartOfMark(ltr_t ltr, int idx) {
      mark_r r; int err;
      if ((err=FIFOgetElm(ltr->mk, idx, ltr->object))<0) 
          errormsg("LTRsetParent pointer = %d error = %d", 
              idx, err);
      memcpy(&r, ltr->object, sizeof(mark_r));
      return r.endpoint;
      }
      
int LTRrunThroughMarks(ltr_t ltr, mark_cb cb) {
      int i, n = FIFOgetAllCount(ltr->mk);
      for (i=0;i<n;i++) {
         idx_t endpoint = LTRgetStartOfMark(ltr, i);
         int join = LTRgetJoinOfMark(ltr, i);
         if (cb(i, join, endpoint)<0) return 1;
         }
      return 0;
      } 
          
int LTRrunThroughTrace(ltr_t ltr, trace_cb f) {
      int current, len = 0, i;
      static fifo_t stack = NULL;
      if (stack== NULL) stack = 
            FIFOcreateMemo(INITSIZE, ltr->width+sizeof(int), NULL, NULL);
      else FIFOreset(stack);
      for (current = LTRgetCurrent(ltr);current != LTRgetParent(ltr, current);
           current = LTRgetParent(ltr, current),len++) {
          LTRgetElm(ltr, current, ltr->object);
          memcpy(((char*) ltr->object)+ltr->width, &current, sizeof(int));
          FIFOput(stack, ltr->object);
          }
      for (i=FIFOgetCount(stack)-1;i>=0;i--) {
          FIFOgetElm(stack, i, ltr->object);
          f(ltr->object, *((int*)((char*)ltr->object+ltr->width)));
          }
      return len;
      }
      
static int makeMark(ltr_t ltr, int id, idx_t join, idx_t endpoint, void *obj, idx_t *idx) {
      /*printmsg("Put leaf bf %d lf %d", join, FIFOgetCount(ltr->lf));*/
      mark_r r; level_r level; 
      int end_mark = 0, err, i, j, start_mark;
      LTRgetBounds(ltr, NULL, NULL, NULL, NULL, &start_mark, &end_mark);
      for (i=start_mark;i<end_mark;i++) {
         FIFOgetElm(ltr->mk, i, ltr->object);
         memcpy(&r, ltr->object, sizeof(mark_r));
         if (r.id==id) break;
         }
      if (i<end_mark) return 1;
      FIFOpop(ltr->mk, FIFOgetCount(ltr->mk)- end_mark);
      err =   FIFOput(ltr->mk, ltr->object);
      // Reorder
      // fprintf(tty,"QQQ start_mark %d < i < %d\n", start_mark,
      // FIFOgetCount(ltr->mk));
      for (i= FIFOgetCount(ltr->mk)-1; i>start_mark;i--) {
          FIFOgetElm(ltr->mk, i-1, ltr->object);
          memcpy(&r, ltr->object, sizeof(mark_r));
          if (r.endpoint<=endpoint) break;
          FIFOupdateElm(ltr->mk, i, ltr->object);
          }
      r.leaf = join; r.length = LTRgetLevel(ltr, endpoint);
      r.endpoint = endpoint; r.depth = LTRgetLevel(ltr, join);
      r.id = id;
      // fprintf(tty, "join = %d depth = %d endpoint = %d\n", join, r.depth,
      // r.endpoint);
      memcpy(ltr->object, &r, sizeof(mark_r));
      memcpy(ltr->object+sizeof(mark_r), obj, ltr->width);
      FIFOupdateElm(ltr->mk, i, ltr->object);
      if (idx) *idx = i;
      FIFOgetElm(ltr->lv, ltr->lv_pt, &level);
      level.end_mark = FIFOgetCount(ltr->mk);
      FIFOupdateElm(ltr->lv, ltr->lv_pt, &level);
      FIFOunpop(ltr->mk);
      for (i=0;FIFOunpop(ltr->lv)>=0;i++);
      for (j=ltr->lv_pt+1;j<FIFOgetAllCount(ltr->lv);j++) {
          level_r level;
          FIFOgetElm(ltr->lv, j, &level);
          level.end_mark++;
          FIFOupdateElm(ltr->lv, j, &level);
          }
      for (i=i-1;i>=0;i--) FIFOpop(ltr->lv, 1);
      if (id<0) {
          leaf_r r;
          id = -id-2;
          FIFOgetElm(ltr->lf, id, &r);
          SETMARK(r.endpoint);
          FIFOupdateElm(ltr->lf, id, &r); 
          }
      else {
          FIFOgetElm(ltr->bf, id, ltr->object);
          SETMARK(*((int*) ltr->object));
          FIFOupdateElm(ltr->bf, id, ltr->object); 
          }
      return err;
      }

int LTRresetMarks(ltr_t ltr) {
      fifo_t bf = ltr->bf, lf = ltr->lf, lv = ltr->lv;
      int i, n = FIFOgetAllCount(bf), m = FIFOgetAllCount(lf),
      k = FIFOgetAllCount(lv);
      FIFOreset(ltr->mk);ltr->mk_pt= -1;
      for (i=0;i<n;i++) {
          FIFOgetElm(bf, i, ltr->object);
          // fprintf(tty,"reset %d\n", i);
          CLEARMARK(*((int*) ltr->object));
          FIFOupdateElm(bf, i, ltr->object);
          }
      for (i=0;i<m;i++) {
          FIFOgetElm(lf, i, ltr->object);
          CLEARMARK(((leaf_r*) ltr->object)->endpoint);
          FIFOupdateElm(lf, i, ltr->object);
          }
      for (i=0;i<k;i++) {
          level_r level;
          FIFOgetElm(lv, i, &level);
          level.end_mark = 0;
          FIFOupdateElm(lv, i, &level);
          }
      return 0;
      } 
           
int LTRmakeMark(ltr_t ltr, idx_t join, idx_t *idx) {
     idx_t endpoint;
     int leaf;
     DECLA(char, obj, ltr->width);
     if (join>=0) {
         endpoint = LTRgetParent(ltr, join);
         leaf = join;
         LTRgetElm(ltr, leaf, obj);
         }
     else {
         leaf = -join-2;
         LTRgetJoinElm(ltr, leaf, obj);
         endpoint = LTRgetJoinSource(ltr, leaf);
         leaf = LTRgetJoinDestination(ltr, leaf);
         }
     return makeMark(ltr, join, leaf, endpoint, obj, idx);
     }
           
int LTRgetMarkElm(ltr_t ltr, int idx, void *obj) {
      FIFOgetElm(ltr->mk, idx, ltr->object);
      memcpy(obj, ltr->object+sizeof(mark_r), ltr->width);
      return 0;
      } 
      
int LTRgetLengthOfMark(ltr_t ltr, int idx) {
      mark_r r; int err;
      if ((err=FIFOgetElm(ltr->mk, idx, ltr->object))<0) 
          errormsg("LTRsetParent pointer = %d error = %d", 
              idx, err);
      memcpy(&r, ltr->object, sizeof(mark_r));
      return r.length;
      }
      
int LTRgetDepthOfMark(ltr_t ltr, int idx) {
      mark_r r; int err;
      if ((err=FIFOgetElm(ltr->mk, idx, ltr->object))<0) 
          errormsg("LTRsetParent pointer = %d error = %d", 
              idx, err);
      memcpy(&r, ltr->object, sizeof(mark_r));
      return r.depth;
      }


      
idx_t LTRgetEndOfMark(ltr_t ltr, int idx) {
      mark_r r; int err;
      if ((err=FIFOgetElm(ltr->mk, idx, ltr->object))<0) 
          errormsg("LTRsetParent pointer = %d error = %d", 
              idx, err);
      memcpy(&r, ltr->object, sizeof(mark_r));
      return r.leaf;
      }
                 
int LTRgetNumberOfMarks(ltr_t ltr) {return FIFOgetAllCount(ltr->mk);}
