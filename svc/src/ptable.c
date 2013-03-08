/*
   SVC -- the SVC (Systems Validation Centre) file format library

   Copyright (C) 2000  Stichting Mathematisch Centrum, Amsterdam,
                       The  Netherlands

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

   $Id: ptable.c,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */

#include "ptable.h"
#include <stdio.h>



static void PTexpand(PTable *, long);



void PTinit(PTable *table){

   table->size=PT_INITIALSIZE;
   table->nodes=(void **)malloc(PT_INITIALSIZE*sizeof(void *));

}



void PTput(PTable *table, long index, void *ptr){

   if(table->size<index+1){
      PTexpand(table, index+1);
   }

   table->nodes[index]=ptr;

}

void *PTget(PTable *table, long index){

   return table->nodes[index];

}

void PTfree(PTable *table){

   free(table->nodes);

}


void PTexpand(PTable *table, long size){

   while(table->size<size){
      table->size=table->size<<2;
   } 

   table->nodes=(void **)realloc(table->nodes,table->size*sizeof(void *));

}

