/* $Id: fifo.c,v 1.2 2006/05/17 08:08:42 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

typedef struct {
    struct fifo_p_s *obj;
    } *fifo_t;
     
#include "param0.h"
#include "fifo_p.h"

fifo_t FIFOcreateMemo(int size, int width, file_t file, dir_t dir) {
     fifo_t fifo = fifo0.create(size, width, file, dir);
     fifo->obj = &fifo0;
     return fifo;
     }
     
#ifdef LINUX     
fifo_t FIFOcreateFile(int width, file_t file) {
     fifo_t fifo = fifo1.create(0, width, file, NULL);
     fifo->obj = &fifo1;
     return fifo;
     } 
#endif
        
int FIFOdestroy(fifo_t fifo) {
     return fifo->obj->destroy(fifo);
     }
     
int FIFOreset(fifo_t fifo) {
     return fifo->obj->reset(fifo);
     }
          
int FIFOput(fifo_t fifo, void *obj) {
    return fifo->obj->put(fifo, obj);
    }

int FIFOget(fifo_t fifo, void *obj) {
    return fifo->obj->get(fifo, obj);
    }
        
int FIFOgetElm(fifo_t fifo, int n, void *obj) {
    return fifo->obj->getElm(fifo, n, obj);
    }
    
int FIFOupdateElm(fifo_t fifo, int n, void *obj) {
    return fifo->obj->updateElm(fifo, n, obj);
    }
        
int FIFOunget(fifo_t fifo) {
    return fifo->obj->unget(fifo);
    }
    
int FIFOgetCount(fifo_t fifo) {
    return fifo->obj->getCount(fifo);
    }
    
int FIFOgetAllCount(fifo_t fifo) {
    return fifo->obj->getAllCount(fifo);
    }
        
int FIFOpop(fifo_t fifo, int number) {
    return fifo->obj->pop(fifo, number);
    }; 

int FIFOunpop(fifo_t fifo) {
    return fifo->obj->unpop(fifo);
    }
          
void *FIFOgetArray(fifo_t fifo) {
    return fifo->obj->getArray(fifo);
    }
    
unsigned long FIFOgetByteSize(fifo_t fifo) {
    return fifo->obj->getByteSize(fifo);
    }
