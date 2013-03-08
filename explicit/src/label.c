/* $Id: label.c,v 1.2 2004/11/23 12:36:17 uid523 Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "label.h"
#include "stringindex.h"
#include "messages.h"
#include <stdlib.h>
#include <string.h>


static string_index_t db = NULL;

int getlabelindex(char *label, int create) {
   int idx;
   if (create) {
       if (db==NULL && SIcreate(&db)) 
          Fatal(1,0,"Out of memory in getlabelindex");
       if (SIput(db, label, &idx)) Fatal(1,0,"SIput %s", label);
       }
   else 
      idx=SIlookup(db, label);
   return idx;
   }
   

char *getlabelstring(int label){
	return SIget(db, label);
}

int getlabelcount(){
	return (!db?0:SIgetCount(db)); 
}

