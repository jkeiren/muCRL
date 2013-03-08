/* $Id: fifo1_p.h,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */
#ifndef FIFO1_P_H
#define FIFO1_P_H

typedef struct {
   struct fifo_p_s *obj; // Obliged
   FILE *file;
   unsigned int width;
   size_t l, r;
   } fifo_r, *fifo_t;

#include "fifo_p.h" 
       
#endif
