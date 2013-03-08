/* $Id: fifo1.c,v 1.2 2006/05/17 08:08:42 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#ifdef LINUX
#include <string.h>
#include "param0.h"
#include <stdio.h>
#include "utl.h"
#include "fifo1_p.h"

static fifo_t FIFOcreateFile(int size, int width, file_t file, dir_t dir) {
      fifo_t r = (fifo_t) malloc(sizeof(fifo_r));
      UTLinit(stderr, NULL, NULL, "Library fifo");
      r->width = width;
      r->file = file;
      r->l  = 0;
      fseek(file, 0, SEEK_END);
      r->r = ftell(file);
      return r;
      }
      
FILE* getFile(fifo_t fifo) {
      return fifo->file;
      } 
           
static int FIFOdestroy(fifo_t fifo) {
      ftruncate(fileno(fifo->file), 0);
      fifo->l = fifo->r = 0;
      return 0;
      }
      
static int FIFOreset(fifo_t fifo) {
      fifo->l = fifo->r = 0;
      return ftruncate(fileno(fifo->file), 0);
      } 
                 
static int  FIFOput(fifo_t fifo, void *obj) {
     if (fseek(fifo->file, (long) fifo->r, SEEK_SET)<0) return -1;
     return fwrite(obj, fifo->width, 1, fifo->file)==1?
        ((fifo->r+=fifo->width),fflush(fifo->file)):-1;
     }     
                
static int FIFOget(fifo_t fifo, void *obj) {
     if (fseek(fifo->file, (long) fifo->l, SEEK_SET)<0)  return -1;
     return fread(obj, fifo->width, 1, fifo->file)==1?
          ((fifo->l+=fifo->width),0): -1;
     }
     
static int FIFOgetElm(fifo_t fifo, int idx, void *obj) {
     if (fseek(fifo->file, ((long) (fifo->width))*idx, SEEK_SET)<0) return -1;
     return fread(obj, fifo->width, 1, fifo->file)==1? 0:-1;
     }
      
static int FIFOupdateElm(fifo_t fifo, int idx, void *obj) {
     if (fseek(fifo->file, ((long) fifo->width)*idx, SEEK_SET)<0) return -1;
     return fwrite(obj, fifo->width, 1, fifo->file)==1? 0:-1;
     } 
     
static int FIFOunget(fifo_t fifo) {
     fprintf(stderr,"Not yet implemented\n");
     return -1;
     }
                            
static int FIFOgetAllCount(fifo_t fifo) {
     return fifo->r/fifo->width; 
     }
         
static int FIFOgetCount(fifo_t fifo) {
     return fifo->r/fifo->width; 
     }
             
static int FIFOpop(fifo_t fifo, int n) {
     fprintf(stderr,"Not yet implemented\n");
     return -1;
     }
     
static int FIFOunpop(fifo_t fifo) {
     fprintf(stderr,"Not yet implemented\n");
     return -1;
     }
          
          
static void *FIFOgetArray(fifo_t fifo) {
    char *a = (char*) malloc(fifo->r*fifo->width);
    if (fread(a, fifo->width, fifo->r, fifo->file)!=1) return NULL;
    return (void*) a;
    }

static unsigned long FIFOgetByteSize(fifo_t fifo) {return 0;}
  
fifo_p_r fifo1 = {FIFOcreateFile, FIFOdestroy, FIFOreset, FIFOput,
FIFOget, FIFOgetElm, FIFOupdateElm, FIFOunget, FIFOgetCount, FIFOgetAllCount,
FIFOpop, FIFOunpop, FIFOgetArray, FIFOgetByteSize};
#endif
