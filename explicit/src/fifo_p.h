/* $Id: fifo_p.h,v 1.2 2006/05/17 08:08:42 bertl Exp $ */
#ifndef FIFO_P_H
#define FIFO_P_H

typedef struct fifo_p_s {
    fifo_t (*create)(int size, int width, file_t, dir_t);
    int (*destroy)(fifo_t fifo);
    int (*reset)(fifo_t fifo);
    int (*put)(fifo_t fifo, void *obj);
    int (*get)(fifo_t fifo, void *obj);
    int (*getElm)(fifo_t fifo, int idx, void *obj);
    int (*updateElm)(fifo_t fifo, int idx, void *obj);
    int (*unget)(fifo_t fifo);
    int (*getCount)(fifo_t fifo);
    int (*getAllCount)(fifo_t fifo);
    int (*pop)(fifo_t fifo, int n);
    int (*unpop)(fifo_t fifo);
    void* (*getArray)(fifo_t fifo);
    unsigned long (*getByteSize)(fifo_t fifo);
    } fifo_p_r, *fifo_p_t;
    
extern fifo_p_r fifo0
#ifdef LINUX
, fifo1
#endif
;
     
#endif
