/* $Id: at_stack.c,v 1.1 2004/01/22 15:43:13 bertl Exp $ 
   Author and Copyright: Jaco van de Pol, CWI, Amsterdam, vdpol@cwi.nl
   tera version 2.0.c: a satisfiability checker for term algebra formulas. */

#include "at_stack.h"

ATermStack ATstackCreate(int size) {
  ATermStack stack;
  stack = (ATermStack)malloc(sizeof(struct ATermStack));
  if (!stack) ATerror("No memory to create stack");
  if (size==0) size++;
  stack->size = size;
  stack->free = 0;
  stack->array = (ATerm*)calloc(size,sizeof(ATerm));
  if (!stack->array) ATerror("No memory to create stack");
  ATprotectArray(stack->array,size);
  return stack;
}

void ATstackDestroy(ATermStack S) {
  ATunprotect(S->array);
  free(S->array);
  free(S);
}

void ATstackReset(ATermStack S) {
  int i;
  for (i=S->free-1;i>=0;i--)
    S->array[i]=NULL;
  S->free=0;
}

void ATstackPush(ATermStack S,ATerm t) {
  int size = S->size;
  if (S->free==size) {
    int i, newsize = 2*size;
    ATunprotect(S->array);
    S->array = (ATerm*)realloc(S->array,newsize*sizeof(ATerm));
    if (!S->array) ATerror("No memory to resize stack");
    for (i=size; i<newsize; i++)
      S->array[i] = NULL;
    S->size = newsize;
    ATprotectArray(S->array,newsize);
  }
  S->array[S->free++] = t;
}

void ATstackSet(ATermStack S, int i,ATerm t) {
  int size = S->size, newsize;
  for (newsize=size; newsize <= i; newsize *= 2);
  if (newsize != size) {
    int j;
    ATunprotect(S->array);
    S->array = (ATerm*)realloc(S->array,newsize*sizeof(ATerm));
    if (!S->array) ATerror("No memory to resize stack");
    for (j=size; j<newsize; j++)
      S->array[j]=NULL;
    S->size = newsize;
    ATprotectArray(S->array,newsize);
  }
  S->array[i]=t;
  if (i+1>S->free) S->free = i+1;
}

ATerm ATstackPop(ATermStack S) {
  ATerm t;
  int n = --S->free;
  assert(n>=0);
  t = S->array[n];
  S->array[n]=NULL;
  return t;
}

void ATstackPrint(FILE* fp, ATermStack S) {
  int size = S->size;
  int free = S->free;
  int i;
  fprintf(fp,"filled %d out of %d:\n",free,size);
  for (i=0;i<free;i++) {
    ATerm t = ATstackGet(S,i);
    if (t) 
      ATfprintf(fp,"%d: %t\n",i,t);
    else
      fprintf(fp,"NULL\n");
} }
