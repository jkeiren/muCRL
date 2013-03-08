/* $Id: fifo0_p.h,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */
#ifndef FIFO0_P_H
#define FIFO0_P_H

typedef struct {
   struct fifo_p_s *obj; 
   char *b /* buffer */;
   size_t *s /* stack */;
   size_t r, l, rsize, bsize, pop, ssize, top;
   unsigned int width;
   FILE *file;
   void *dir;
   } fifo_r, *fifo_t;

#include "fifo_p.h" 
       
#endif
