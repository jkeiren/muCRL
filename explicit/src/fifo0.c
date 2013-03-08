/* $Id: fifo0.c,v 1.3 2006/11/16 14:55:04 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <string.h>
#include "param0.h"
#include <stdio.h>
#include "utl.h"
#include "fifo0_p.h"
#define INITSIZE 100

static int EnlargeStack(fifo_t fifo) {
    if (fifo->top*sizeof(int)<fifo->ssize) return 0; 
    fifo->ssize *= 2; 
    if (!(fifo->s = realloc(fifo->s, fifo->ssize)))
       return mkerror(ERR_NULL, "Cannot realloc stack (%d)",fifo->ssize);
    return 0;
    }
    
static int Enlarge(fifo_t fifo) {
    size_t bsize = fifo->bsize;
    if (!((fifo->l==0 && fifo->r == fifo->bsize-fifo->width) || 
         fifo->r == fifo->l-fifo->width)) return 0;
    fifo->bsize *= 2;  
/*
    printmsg("Enlarge old %ld new = %ld (%ld %ld==%ld)", 
     bsize, fifo->bsize, fifo->l, fifo->r, fifo->pop); 
*/
    // printmsg("Enlarge old %d new %d", bsize, fifo->bsize); 
    if (!(fifo->b = realloc(fifo->b, fifo->bsize)))
       return mkerror(ERR_NULL, "Cannot realloc (%d)",fifo->bsize);
    if (fifo->r<fifo->l) {
        if (fifo->pop<=fifo->r) fifo->pop+=bsize;
        memcpy(fifo->b+bsize, fifo->b, fifo->r);
        fifo->r += bsize;
        }
    return 0;
    }

static fifo_t FIFOcreateMemo(int initsize, int width, file_t file, dir_t dir) {
      fifo_t r = (fifo_t) malloc(sizeof(fifo_r));
      UTLinit(stderr, NULL, NULL, "Library fifo");
      if (r==NULL) {
           mkerror(ERR_NULL,"failed malloc(size = %d)", sizeof(fifo_r));
           return NULL;
           }
      r->bsize = width*initsize; r->ssize = INITSIZE*sizeof(int);
      r->width = width;
      r->b = malloc(r->bsize); r->s = malloc(r->ssize);
      // fprintf(stderr,"width = %d\n", width);
      r->top = r->l = r->r =  r->pop = 0;
      r->file = file; r->dir = dir?strdup(dir):NULL;
      return r;
      }
      
static int FIFOdestroy(fifo_t fifo) {
      free(fifo->b);free(fifo);
      return 0;
      }
      
static int FIFOreset(fifo_t fifo) {
      fifo->top = fifo->l = fifo->r = fifo->pop = 0;
      return 0;
      } 
                 
static int  FIFOput(fifo_t fifo, void *obj) {
     int err;
     if (obj) {
       long i, n = fifo->r-fifo->pop, k;
       n = (n>=0?n:(fifo->bsize+n))/fifo->width;
       if ((err=Enlarge(fifo))<0) return mkerror(err,"FIFOput");
       for (k=0, i=fifo->r+fifo->bsize;k<n;i-=fifo->width,k++)
           memcpy(fifo->b+(i%fifo->bsize), 
             fifo->b+((i-fifo->width)%fifo->bsize), fifo->width); 
       memcpy(fifo->b+fifo->pop, obj, fifo->width);
       /* printmsg("put:r = %d (%d) %d\n", fifo->r, fifo->width, 
         ((int*) obj)[0]); */
       fifo->r+=fifo->width;
       fifo->r %= fifo->bsize;
       fifo->pop += fifo->width;
       fifo->pop %= fifo->bsize;
       }
     else {
        fifo->top = 0; // Empties the undo stack
        fifo->r = fifo->pop;
        }
     return 0;
     }     
                
static int FIFOget(fifo_t fifo, void *obj) {
     if (fifo->l == fifo->r) return ERR_EMPTY;
     if (obj) memcpy(obj ,fifo->b+fifo->l, fifo->width);
     fifo->l+=fifo->width;
     fifo->l %= fifo->bsize;
     /* fprintf(stderr,"l = %d %d %d\n", fifo->l, fifo->width, 
       ((int*) obj)[0]); */
     if (fifo->l == fifo->r) return 1;
     return 0;
     }
     
static int FIFOgetElm(fifo_t fifo, int idx, void *obj) {
     int ofs = idx*fifo->width;
     if (fifo->l == fifo->r) return ERR_EMPTY;
     memcpy(obj ,fifo->b+(fifo->l+ofs>=fifo->bsize?
     fifo->l+ofs-fifo->bsize:fifo->l+ofs), fifo->width);
     return 0;
     }
      
static int FIFOupdateElm(fifo_t fifo, int idx, void *obj) {
     int ofs = idx*fifo->width;
     if (fifo->l == fifo->r) return ERR_EMPTY;
     memcpy(fifo->b+(fifo->l+ofs>=fifo->bsize?fifo->l+ofs-fifo->bsize
           :fifo->l+ofs), obj, fifo->width);
     return 0;
     } 
              
static int FIFOunget(fifo_t fifo) {
     int err;
     if ((err=Enlarge(fifo))<0) return mkerror(err,"FIFOunget");
     fifo->l+= fifo->bsize;
     fifo->l-=fifo->width;
     fifo->l %= fifo->bsize;
     /* (memcpy(obj ,fifo->b+fifo->l, fifo->width); */
     return 0;
     }
         
static int FIFOgetAllCount(fifo_t fifo) {
     long size = fifo->r-fifo->l;
     return (int) ((size>=0?size:fifo->bsize+size)/fifo->width); 
     }
         
static int FIFOgetCount(fifo_t fifo) {
     long size = fifo->pop-fifo->l;
     return (int) ((size>=0?size:fifo->bsize+size)/fifo->width);
     }
             
static int FIFOpop(fifo_t fifo, int n) {
     int  err;
     if ((err=EnlargeStack(fifo))<0) return mkerror(err, "FIFOpop");
     // printmsg("FIFOpop1 n= %d top = %d l = %d pop = %d width = %d", 
     // n, fifo->top, fifo->l, fifo->pop, fifo->width);
     if (fifo->pop == fifo->l && n>0) return mkerror(ERR_EMPTY,"FIFOpop"); 
     if (n>=0) fifo->s[fifo->top++] = n;
     if (n>0) {
        fifo->pop-=n*fifo->width; 
        fifo->pop+=fifo->bsize;
        fifo->pop%=fifo->bsize;
        }
     else if (n<0) {
        fifo->l-=n*fifo->width; 
        fifo->l+=fifo->bsize;
        fifo->l%=fifo->bsize;
        }
     // printmsg("FIFOpop1 n= %d top = %d l = %d pop = %d", 
     // n, fifo->top, fifo->l, fifo->pop);
     return fifo->pop == fifo->l?1:0;
     }
     
static int FIFOunpop(fifo_t fifo) {
     int n, pop=fifo->pop;
     if (fifo->top == 0) return ERR_EMPTY;
     n = fifo->s[--(fifo->top)];
     // printmsg("FIFOunpop %d fifo->top %d pop = %d", n, fifo->top,
     // fifo->pop);
     fifo->pop+=n*fifo->width;
     fifo->pop%=fifo->bsize;
     if ((pop<=fifo->r && fifo->pop>fifo->r) 
         || (pop>fifo->r && fifo->pop<pop && fifo->pop>fifo->r))
        return ERR_FULL;
     /*  
     for (i=0;i<n;i++) {
        if (fifo->pop == fifo->r) 
            return ERR_FULL;
        fifo->pop += fifo->width;
        fifo->pop %= fifo->bsize;
        }
     */
     return fifo->pop == fifo->r?1:0;
     }
          
          
static void *FIFOgetArray(fifo_t fifo) {
    return (void*) (fifo->b);
    }

static unsigned long FIFOgetByteSize(fifo_t fifo) {
   return FIFOgetCount(fifo)*fifo->width;
   // return fifo->bsize;
   }  

fifo_p_r fifo0 = {FIFOcreateMemo, FIFOdestroy, FIFOreset, FIFOput,
FIFOget, FIFOgetElm, FIFOupdateElm, FIFOunget, FIFOgetCount, FIFOgetAllCount,
FIFOpop, FIFOunpop,  FIFOgetArray, FIFOgetByteSize};
