/* $Id: array.c,v 1.5 2006/05/17 08:08:42 bertl Exp $ */
#define ARRAY_C
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <string.h>
#include "param0.h"
#include <stdio.h>
#include "utl.h"

#define INITSIZE 100

typedef struct {
   char *b /* buffer */;
   unsigned int width, count;
   size_t bsize, pt;
   FILE *file;
   void *vdb;
   } array_r, *array_t;
   
#include "vector_db.h"

static int Enlarge(array_t array) { 
   size_t oldsize  = 0;
   size_t  n = (size_t) (VDBgetCount(array->vdb)*(size_t) array->width);
    if (array->b) {
	if (array->bsize>=n) return 0; 
	oldsize = array->bsize;
        while (array->bsize<n) array->bsize *= 2; 
        }  
    // fprintf(stderr,"Enlarge1 array b = %lx: n = %d size = %d\n", 
    // array->b, n , array->bsize);
    if (!(array->b = realloc(array->b, array->bsize)))
       return mkerror(ERR_NULL, "Cannot realloc (%d)",array->bsize);
    // fprintf(stderr,"Enlarge2 array b = %lx\n",  array->b);
    memset(array->b+oldsize, 0, array->bsize - oldsize);
    return 0;
    } 
      
static int KeyInVDB(vdb_t vdb, FILE *f) {
    elm_t elm[2];
    readPair(f, elm);
    // printmsg("id = %d (%d %d) %d", vdb->id, elm[0], elm[1], 
    return VDBgetIdx(vdb, elm);
    }
    
static int ALread(array_t array) {
    vdb_t vdb = array->vdb;
    FILE *f = vdb?VDBgetFile(vdb):NULL;
    if (!array->file || !f) return 0;
    {
    int i,width=array->width, err, n = VDBgetCount(array->vdb),
    m = FileLen(array->file)/width, k = FileLen(f)/getRecordSize(),
    mm = m<k?m:k;
    char *obj = malloc((size_t) width);
    rewind(array->file); rewind(f);
    Enlarge(array);
    for (i=0;i<mm;i++) {
       idx_t idx;
       if (fread(obj, (size_t) width, 1, array->file)!=1)
           return mkerror(ERR_WRITE,"ALread");
       idx = KeyInVDB(vdb, f);
       /* printmsg("%d AL read idx = %d (%d %d %d)", 
       ftell(array->file), idx, *((int*) obj), *((int*) (obj+4)), *((int*)
       (obj+8))); */
       if (idx>=0) memcpy(array->b+idx*width, obj, (size_t) width); 
       }
    array->pt = n*width; 
    array->count = n;
    Ftruncate(array->file, 0);
    if (n>0) {
      fwrite(array->b, (size_t) width, (size_t) n, array->file);
      fflush(array->file);
      }
    /* printmsg("ALread n = %d width = %d, len = %d", n, width,
        FileLen(array->file)); */
    } 
    return 0;
    }
    
array_t ALcreate(int initsize, int width, file_t file, vdb_t vdb) {
      array_t r; 
      UTLinit(stderr, NULL, NULL, "Library array");
      if (!(r = (array_t) calloc(1, sizeof(array_r))))
 return (mkerror(ERR_NULL, "Cannot calloc (%d)",sizeof(array_r)), NULL);
      r->width = width; r->file = file; r->vdb = vdb;
      r->bsize = width*initsize; 
      if (Enlarge(r)<0) 
 return (mkerror(ERR_NULL, "Cannot calloc (%d)",r->bsize), NULL);
      if (ALread(r)<0)
 return (mkerror(ERR_NULL, "Cannot read"), NULL);      
      return r;
      }
      
int ALgetWidth(array_t r) {    
      return r->width;
      }
      
int ALdestroy(array_t array) {
      free(array->b);free(array);
      return 0;
      }
                      
int ALadd(array_t array, void *obj) {
     if (obj) {
       int err;
       if ((err=Enlarge(array))<0) return mkerror(err,"arrayput"); 
       memcpy(array->b+array->pt, obj, (size_t) array->width);
       array->pt+=array->width;
       /* printmsg("%d AL add  (%d %d %d)", 
       array->count, *((int*) obj), *((int*) (obj+4)), *((int*)
       (obj+8))); */
       array->count++;
       if (!array->vdb && array->file) {  
          if (fwrite(obj, (size_t) array->width, 1, array->file)!=1)
          return mkerror(ERR_WRITE,"arrayput");
          // fflush(array->file);
          }
       }
     return 0;
     }     

FILE *ALgetFile(array_t array) {return array->file;}               
     
int ALget(array_t array, int idx, void *obj) {
     size_t ofs = idx*array->width;
     if (ofs>=array->pt) 
     return mkerror(ERR_NULL, "Out of range %d>=%d",ofs, array->pt);
     memcpy(obj ,array->b+ofs, (size_t) array->width);
     return 0;
     }

int ALisEmpty(array_t array, int idx) { 
     int width = array->width; 
     size_t ofs = idx*width, i;
     if (ofs>=array->pt) return 1;
     for (i=0;i<width;i++) 
       if (array->b[ofs+i]) return 0;
     return 1;
     }
           
int ALupdate(array_t array, int idx, void *obj) {
     size_t ofs = idx*array->width;
     if (ofs>=array->pt) 
     return mkerror(ERR_NULL, "ALupdate: out of range %d>=%d",ofs, array->pt);
     memcpy(array->b+ofs, obj, (size_t) array->width);
     return 0;
     }              
                  
int ALgetCount(array_t array) {
     return array->count;
     }
                      
void *ALgetArray(array_t array) {
    return (void*) (array->b);
    }
   
