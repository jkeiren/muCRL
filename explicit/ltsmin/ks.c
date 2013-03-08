/* $Id: ks.c,v 1.3 2007/10/09 09:46:26 bertl Exp $ */
/* Kanellakis-Smolka Algorithm */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdlib.h>
#include <unistd.h>
#include "xlts.h"
#include "messages.h"
#include "ks.h"
#include "param0.h"
#include "fifo.h"
#include "assert.h"


#define EMPTY 4294967295U /* UINT_MAX limits.h */

typedef struct {
     uint32_t  start, end, idx;
     int new;
   } block_t;

static fifo_t *stable, *unstable;

static int *set;

static uint32_t *phi, *idx, idx_pt = 0;

static lts_t lts;
static int round  = 0;

#define START(i) lts->begin[phi[i]]
#define END(i) lts->begin[phi[i]+1]

static void BubbleSort(block_t *block) {
     uint32_t i, m, k, tmp, tmp1;
     // fprintf(stderr, "Entry BubbleSort %d %d\n", block->start, block->end);
     if (round==0)
     for(i=block->start;i<block->end;i++){
          for(m=START(i);m<END(i);m++){
            for(k=m;k>START(i);k--) {
                if(lts->label[k]>lts->label[k-1]) break;   
                tmp=lts->label[k];
                lts->label[k]=lts->label[k-1];
                lts->label[k-1]=tmp;
                assert(lts->label[k]>=lts->label[k-1]);
                tmp=lts->dest[k];
                lts->dest[k]=lts->dest[k-1];
                lts->dest[k-1]=tmp;
                assert(idx[lts->dest[k]]>=idx[lts->dest[k-1]]);
              }
        }
        }
        else
        for(i=block->start;i<block->end;i++){
          for(m=START(i);m<END(i);m++){
            for(k=m;k>START(i);k--) {
                if(lts->label[k]>lts->label[k-1]) break;
                if (idx[lts->dest[k]]>=idx[lts->dest[k-1]]) break;        
                tmp=lts->dest[k];
                lts->dest[k]=lts->dest[k-1];
                lts->dest[k-1]=tmp;
                assert(idx[lts->dest[k]]>=idx[lts->dest[k-1]]);
              }
        }
     }
    // fprintf(stderr, "End BubbleSort %d %d\n", block->start, block->end);
    // BubbleSortCheck(block);
    }

static int CmpSig (const void *p1, const void *p2) {
      uint32_t s1 = (*(uint32_t *) p1), s2 = (*(uint32_t *) p2);
      cell_t i1=lts->begin[s1], end1=lts->begin[s1+1],
	     i2=lts->begin[s2], end2=lts->begin[s2+1];
        if (round==0)
	for(;;){
		if(i1==end1) return i2==end2?0:-1;
		if(i2==end2) return  1;
		if( lts->label[i1]!=lts->label[i2]) return 
                    lts->label[i1]<lts->label[i2]?-1:1;
		i1++;
		while((i1<end1) && (lts->label[i1]==lts->label[i1-1])) i1++;
		i2++;
		while((i2<end2) && (lts->label[i2]==lts->label[i2-1])) i2++;
	}
        else
        for(;;){
		if(i1==end1) return i2==end2?0:-1;
		if(i2==end2) return  1;
                if(idx[lts->dest[i1]]!=idx[lts->dest[i2]]) return 
                    idx[lts->dest[i1]]<idx[lts->dest[i2]]?-1:1;
		i1++;
		while((i1<end1) 
                  && (idx[lts->dest[i1]]==idx[lts->dest[i1-1]])
                ) i1++;
		i2++;
		while((i2<end2)
                  && (idx[lts->dest[i2]]==idx[lts->dest[i2-1]])
                ) i2++;
	}
      }
      
      
static int SameSig(int s1,int s2) {
	cell_t i1= START(s1), end1 = END(s1),
	       i2= START(s2), end2 = END(s2);
        if (round==0)
	for(;;){
		if(i1==end1) return (i2==end2);
		if(i2==end2) return 0;
		if (lts->label[i1]!=lts->label[i2]) return 0;
		i1++;
		while((i1<end1) && 
                  (lts->label[i1]==lts->label[i1-1]) 
                ) i1++;
		i2++;
		while((i2<end2) && 
                 (lts->label[i2]==lts->label[i2-1]) 
                 ) i2++;
                }
        else
        for(;;){
		if(i1==end1) return (i2==end2);
		if(i2==end2) return 0;
		if (idx[lts->dest[i1]]!=idx[lts->dest[i2]]) 
                   return 0;
		i1++;
		while((i1<end1) &&  
                  (idx[lts->dest[i1]]==idx[lts->dest[i1-1]])
                ) i1++;
		i2++;
		while((i2<end2) && 
                  (idx[lts->dest[i2]]==idx[lts->dest[i2-1]])
                 ) i2++;
              }            
}


static void MarkSourceStates(block_t *block, uint32_t v) {
   uint32_t i;
   for (i=block->start;i<block->end;i++) {
         idx[phi[i]] = v; /* Source states in block v */
         }
   }

static int OutDegree(block_t *block) {
   return END(block->start)-START(block->start);
   }
   
static uint32_t NumberOfBlocks() {
      block_t **data= (block_t**) FIFOgetArray(stable);
      uint32_t i = 0, n = FIFOgetCount(stable), cnt = 0;
      for (i=0;i<n;i++) {
         if (data[i]) cnt++;
         }
      return cnt;
      }
 
 static cell_t NumberOfTransitions() {
      block_t **data= (block_t**) FIFOgetArray(stable);
      uint32_t i = 0, n = FIFOgetCount(stable);
      cell_t cnt = 0;
      for (i=0;i<n;i++) {
         if (data[i]) cnt+=OutDegree(data[i]);
         }
      return cnt;
      } 
             
static void PushRoot() {
   uint32_t i = 0, n = lts->states;
   block_t *block = malloc(sizeof(block_t));
   block->start = 0;
   block->end =   n; block->idx = idx_pt;
   block->new = 1;
   for (i=0;i<n;i++) {phi[i] = i;idx[i] = 0;}
   FIFOput(stable, &block);
   idx_pt++;
   }
  
static int SplitBlock(block_t *block) {
   uint32_t i = block->start, n = block->end-block->start, idx_pt0 = idx_pt;
   /*
fprintf(stderr,"Begin SplitBlock %d  stab = %d unstab= %d reduce=%d [%d %d)\n", 
 block->idx, FIFOgetCount(stable),FIFOgetCount(unstable),
          NumberOfBlocks(), block->start, block->end); 
  */
   BubbleSort(block);
   qsort(phi+i, n, sizeof(uint32_t), CmpSig);
   
   if (SameSig(i, block->end-1)) {
       block->new =  0;
       FIFOupdateElm(stable, block->idx, &block);
       // fprintf(stderr,"FULL\n");
       return 1;
       }
   while (i<block->end) {
      uint32_t first = i;
      for (i++;i<block->end && SameSig(first, i);i++);
        {
        block_t *newblock = malloc(sizeof(block_t));
        newblock->start = first;
        newblock->end =   i; newblock->idx = idx_pt;
        newblock->new = 1;
        /*
        fprintf(stderr,"Put New Block %d %d\n", 
           newblock->start, newblock->end);
        */
        FIFOput(stable, &newblock);
        idx_pt++;
        }
      }
      for (i=idx_pt0;i<idx_pt;i++) {
         block_t *newblock;
         FIFOgetElm(stable, i, &newblock);
         MarkSourceStates(newblock, i); 
         }
      {
      /*
      block_t *tmp;
      FIFOgetElm(stable, block->idx, &tmp);
      assert(tmp==NULL);
      */
      free(block);
      return 0;
      }
   }
   
static void CheckBlocks() {
   uint32_t n = FIFOgetCount(unstable), i, j, cnt = 0;
   Warning(1,"CheckBlocks #unstable = %d", n);
   for (i=0;i<n;i++) {
      block_t *block; cell_t k;
      uint32_t m;
      FIFOgetElm(unstable, i, &block);
      m = (block->end-block->start);
      Warning(1,"Block %d size %d", i, m);
      for (j=0;j<m;j++) { 
        Warning(1,"From size %d", END(block->start+j)-START(block->start+j));
        for (k=START(block->start+j);k<END(block->start+j);k++)
          Warning(1,"Dest %d Label %d cnt = %d", lts->dest[k], lts->label[k],
          cnt++);
          }
      }
   }
   
static void UnstableBlocksFound() {
      uint32_t i, n = lts->states;
      int m = FIFOgetCount(stable);
      block_t **data = FIFOgetArray(stable);
      // fprintf(stderr,"Start UnStableBlocksFound\n");
      for (i=0;i<n && m>0;i++) {  
      // Through sources :one dest in new block -> source unstable
        cell_t j; 
        if (data[idx[i]]==NULL) continue;
        for (j=lts->begin[i];j<lts->begin[i+1];j++) {
            block_t *dest = data[idx[lts->dest[j]]];
            if (!dest || dest->new) {
                FIFOput(unstable, &(data[idx[i]]));
                data[idx[i]] = NULL;
                m--;
                break;
                }
        }
      }
      n = FIFOgetCount(stable);
      if (m>0)
      for (i=0;i<n;i++)  
         if (data[i] != NULL) data[i]->new=0; 
     /*
      fprintf(stderr,"End UnStableBlocksFound stable=%d (marked=%d)\n", 
      NumberOfBlocks(), cnt); 
      */
      } 

static void CheckUnstable() {
      int *a = calloc(FIFOgetCount(stable), sizeof(int)), i = 0;
      for (i=0;i<FIFOgetCount(unstable);i++) {
          block_t *ptr;
          FIFOgetElm(unstable, i, &ptr);
          if (a[ptr->idx]) {
             fprintf(stderr,"Double block %d\n", (a[ptr->idx]));
             exit(1);
             }
          else a[ptr->idx]=1;
          }
      free(a);
      }

static void CreateLTS(uint32_t states) {
      int n = FIFOgetCount(stable), i;
      cell_t m;
      block_t **data = FIFOgetArray(stable);
      uint32_t *a = (uint32_t*) malloc(sizeof(uint32_t)*n), count = 0;
      memset(a, EMPTY, sizeof(uint32_t)*n);
      for (i=0;i<n;i++) {
          if (data[i] && a[data[i]->idx]==EMPTY) {
              a[data[i]->idx] = count++;
              }
          }
      lts_set_type(lts,LTS_LIST);
      lts->states=states;
      lts->root=a[idx[lts->root]];
      if (lts->root2>=0) lts->root2=a[idx[lts->root2]];
      for(m=0;m<lts->transitions;m++){
		lts->src[m]=a[idx[lts->src[m]]];
		lts->dest[m]=a[idx[lts->dest[m]]];
	}
      free(a);
      lts_uniq(lts);
      }
                        
void ks(lts_t lts1) {
    uint32_t count = 0, n, states = 1;
    lts = lts1;
    unstable = FIFOcreateMemo(100, sizeof(block_t*), NULL, NULL);
    stable = FIFOcreateMemo(100, sizeof(block_t*), NULL, NULL);
    phi = malloc(lts->states*sizeof(uint32_t));
    idx = malloc(lts->states*sizeof(uint32_t));  
    lts_set_type(lts,LTS_BLOCK);
    PushRoot();
       
    do {
      Warning(2,"Start Round %d: number of blocks: %d", round, states);
      UnstableBlocksFound();
    // CheckUnstable();
      count = 0;
      n = FIFOgetCount(unstable);
      Warning(2,"Round %d: number of unstable blocks: %d", 
                  round, states);
      while (FIFOgetCount(unstable)>0) {
         block_t *block;
         /* Warning(1, "Split unstable %d blocks = %d", 
           FIFOgetCount(unstable), NumberOfBlocks()); */
         FIFOget(unstable, &block);
         count += SplitBlock(block);
         }
       states =  NumberOfBlocks();
       Warning(2,"End Round %d: number of blocks: %d", round, states);
       round++;
       } while (count != n);
      /*
      Warning(1,"Reduced number of states %d transitions %d", 
         states , NumberOfTransitions());
      */
      CreateLTS(states);
      FIFOdestroy(stable);
      FIFOdestroy(unstable);
      free(phi);
      free(idx);
    }
