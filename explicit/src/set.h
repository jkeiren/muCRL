/* $Id: set.h,v 1.1 2004/01/29 13:17:32 bertl Exp $ */

#ifndef SET_H
#define SET_H

#include <stdio.h>

#define EMPTY_SET 0

#define UNDEFINED_SET (-1)

extern void SetPrint(FILE *f,int set);

extern void SetPrintIndex(FILE *f,int set,char **index);

extern void SetClear(int tag);

extern void SetFree();

extern int SetInsert(int set,int label,int dest);

extern int SetUnion(int set1,int set2);

extern int SetGetTag(int set);

extern void SetSetTag(int set,int tag);

extern int SetGetSize(int set);

extern void SetGetSet(int set,int*data);

extern int SetGetLabel(int set);

extern int SetGetDest(int set);

extern int SetGetParent(int set);

extern unsigned int SetGetHash(int set);

#endif

