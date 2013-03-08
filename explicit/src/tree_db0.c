/* $Id: tree_db0.c,v 1.14 2006/09/19 13:42:58 bertl Exp $ */

/* Folds a vector of integers into a pair of integers */

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


// #define E(X) if ((X)<0) errormsg(""#X);else printmsg("%s %d",""#X,vdb->client_id)
#define E(X) if ((X)<0) errormsg(""#X)
// #define EMPTY 255

#include "array.h"
#include "vector_db.h"

typedef struct {
  int width, id, swap1, swap2;
  vdb_t *vdb;
  elm_t *elm;
  int *pbce;
} trdb_r, *trdb_t;

static void Fold(trdb_t trdb) {
	int i;
	for (i=trdb->width-1;i>=2;i--) {
            int new;
            if ((trdb->elm[trdb->pbce[i]]=VDBput(trdb->vdb[i], trdb->elm+2*i, &new))<0)
               errormsg("FoldNode i = %d (%d, %d) r = %d", 
               i, trdb->elm[2*i], trdb->elm[2*i+1], trdb->elm[i]);
            /* printmsg("pbce[%d]= %d dest[%d]=%d  dest[%d=%d",
            i, pbce[i], 2*i, dest[2*i], 2*i+1, dest[2*i+1]); */
	    }
        /* fprintf(stderr, "DBSfold (%d, %d) n = %d\n",
         dest[2], dest[3], n); */
        }

static void swap(int *r, int p, int q) {
    int aux = r[p];
    r[p]=r[q];
    r[q]=aux;
    }
 
 static void Swap(trdb_t trdb, int *r) {
    int aux = r[trdb->swap1];
    r[trdb->swap1]=r[trdb->swap2];
    r[trdb->swap2]=aux;
    }  
             
 static void Unfold(trdb_t trdb) {
	int i;
	for(i=2;i<trdb->width;i++) {
          // fprintf(stderr,"QQQ: %d %d\n", trdb->pbce[i], trdb->elm[trdb->pbce[i]]);
          if (VDBget(trdb->vdb[i], trdb->elm+2*i, trdb->elm[trdb->pbce[i]])<0) {
              errormsg("Unfold node %d (%d>%d)",i, trdb->elm[i],
              VDBgetCount(trdb->vdb[i]));
              }
	}
        }
        
static void Balance(trdb_t trdb) {
      int  n = trdb->width, m = 1, i, n2 = 2*n;
      trdb->pbce = (int*) malloc(sizeof(int)*n2);
      for (i=0;i<n2;i++) trdb->pbce[i] = i;
      if (n>2) { 
      for (m=1;m<n2;m*=2);
      m/=2;
      // fprintf(stderr,"Swap %d<-> %d", m-1, n-1);
      trdb->swap1 = m-1; trdb->swap2=n-1;
      swap(trdb->pbce, m-1, n-1);
      }
      }
      
trdb_t TRDBcreate(int id, int width) {
  int i;
  trdb_t trdb = (trdb_t) calloc(1, sizeof(trdb_r));
  trdb->id = id; trdb->width = width;
  trdb->vdb = (vdb_t*) calloc(width, sizeof(vdb_t));
  for (i=2;i<width;i++) trdb->vdb[i] = 
      VDBcreate(i, 2, NULL, NULL, NULL, NULL, NULL, NULL, NULL);
  trdb->elm = (elm_t*) calloc(2*width, sizeof(elm_t));
  Balance(trdb);
  return trdb;
  }
  
elm_t *TRDBput(trdb_t trdb, elm_t *dest) {
  int i = 0, n = trdb->width;
  for (i=0;i<n;i++) trdb->elm[trdb->pbce[n+i]] = dest[i];
  Fold(trdb);
  return trdb->elm+2;
  }
  
elm_t *TRDBget(trdb_t trdb, elm_t *src) {
  int i = 0, n = trdb->width;
  memcpy(trdb->elm+2, src, 2*sizeof(elm_t));
  Unfold(trdb);
  Swap(trdb, trdb->elm);
  /*
  for (i=0;i<n;i++) {
           trdb->v[i] = trdb->elm[trdb->pbce[n+i]];
           // ATfprintf(stderr,"QQB Value = %t\n", v[i]);
           }
  */
  return trdb->elm+n;
  }

unsigned long  TRDBgetByteSize(trdb_t trdb) {
 int i;
 unsigned long d = 0;
 for (i=2;i<trdb->width;i++) d += VDBgetByteSize(trdb->vdb[i]);
 return d;
 }
 
 unsigned long  TRDBgetEntrieCount(trdb_t trdb) {
 int i;
 unsigned long d = 0;
 for (i=2;i<trdb->width;i++) d += VDBgetCount(trdb->vdb[i]);
 return d;
 }
