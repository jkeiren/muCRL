/* $Id: sede_dinstantiate.h,v 1.3 2007/06/29 13:30:57 bertl Exp $ */
/* @file
    Implementation of the callback functions.
*/
#include "sede.h"

typedef struct {
    char *d;
    size_t size, bsize;
    ssize_t cnt;
    int flushed;
    } out_t;

typedef struct { 
    v_context_t c;
    bfile_t /* *f, */ **output;
    out_t *out;
    int nseg, seg;
    } contextWrite_t;

SEDE_TYPEDEF(contextWrite)

typedef struct {
    fifo_t *fifo;
    FILE *input;
    elm_t idx, explored, transitions;
    } contextRead_t;
      
SEDE_TYPEDEF(contextRead)

/* 
    Write callback.
    @param size
    @param state_vec state vector of size bytes
    @param wc  write context
*/
ssize_t Write_c(size_t size, void *state_vec, void *wc) {
   int seg = SEDE_DATA(contextWrite, wc).seg;
   out_t **out = &(SEDE_DATA(contextWrite, wc).out);
   bfile_t ***output =  &(SEDE_DATA(contextWrite, wc).output), 
        *f = (*output)[seg];
   if (!f) {
        (*out)[seg].d = NULL;
         f = (*output)[seg] = 
             bopen_memstream(20000, &((*out)[seg].d), &((*out)[seg].size));
             (*out)[seg].flushed = 1;
        } 
    if ((*out)[seg].flushed) {
       (*out)[seg].cnt = 0;(*out)[seg].flushed = 0;
       brewind(f);
       }
    if (bfwrite(&(SEDE_DATA(contextWrite, wc).c), sizeof(v_context_t), 1, f)
       !=1) return -1;
    if (bfwrite(state_vec, size, 1, f)!=1) return -1;
    if (SEDE_DATA(contextWrite, wc).c.idx<0) {
        bfflush(f); (*out)[seg].flushed = 1;
        size = 0;
        } 
    (*out)[seg].cnt++;
    (*out)[seg].bsize = blength(f);
    return size;
    }   


SEDE_DECLARE(contextWrite, Write_c, visits)
SEDE_DECLARE(contextWrite, Write_c, ticks)
SEDE_DECLARE(contextWrite, Write_c, backups)


/*
    Read callback.
    @param size
    @param state_vec state vector of @c size bytes
    @param rc read context
*/
ssize_t Read_c(size_t size, void *state_vec, void *rc) {
    FILE *input =  SEDE_DATA(contextRead, rc).input;
    fifo_t  fifo =  SEDE_DATA(contextRead, rc).fifo;
    if (!fifo) { 
           SEDE_DATA(contextRead, rc).fifo = fifo = 
           FIFOcreateMemo(10000, sizeof(u_context_t)+(nodes?2:env->K)
	                 *sizeof(elm_t), NULL, NULL); 
           }
    C_fork2inst_unexplored(input, unexplored);
    if (unexplored->c.idx>=0) {
      if (state_vec) memcpy(state_vec, unexplored->src, size);
      else state_vec = unexplored->src;
      if (env->K>2 && env->tree) {
          DECLA(elm_t, a, 2*env->K);
	  FoldVector(a, state_vec);
	  unexplored->src[0] = a[2]; unexplored->src[1]=a[3];
          }
      FIFOput(fifo, &(unexplored->c));
      } else {
      SEDE_DATA(contextRead, rc).explored = unexplored->src[0];
      SEDE_DATA(contextRead, rc).transitions = unexplored->src[1];
      size = 0;
      }
/* fprintf(stderr,"Read_c: %d (%d %d)\n", unexplored->c.idx, unexplored->src[0],
      unexplored->src[1]); */
    return size;
    }

SEDE_DECLARE(contextRead, Read_c, input)   

static void contextInitWrite(contextWrite_t *context, int n) {
    memset(context, 0, sizeof(contextWrite_t));
    context->out = calloc(n, sizeof(out_t));
    context->output = calloc(n, sizeof(FILE*));
    context->nseg = n;
    }
     
static void contextInitRead(contextRead_t *context, FILE *from) {
    memset(context, 0, sizeof(contextRead_t));
    context->input = from;
    } 



