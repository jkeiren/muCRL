/* 
   $Id: at_stack.h,v 1.1 2004/01/22 15:43:13 bertl Exp $  
   Author and Copyright: Jaco van de Pol, CWI, Amsterdam, vdpol@cwi.nl
   tera version 2.0.c: a satisfiability checker for term algebra formulas. */

#ifndef AT_STACK_H
#define AT_STACK_H

#include <stdlib.h>
#include <assert.h>
#include "aterm2.h"

/* A stack is a protected, scalable array, with entries 0..depth-1.
   Entries are NULL or contain an ATerm.
   Push/Top/Pop behave like a stack 
   -> push enlarges array; top/pop from empty is illegal).
   Get/Set implement random access write/read, in such a way 
   -> set may enlarge array with NULLs, get may return NULL
 */

typedef struct ATermStack {
  ATerm* array; /* contents of the stack */
  int size;     /* allocated space */
  int free;     /* first free position */
}* ATermStack;

ATermStack ATstackCreate(int size); /* create array at an initial size */
void ATstackDestroy(ATermStack S);  /* destroy array; reclaim memory   */
void ATstackReset(ATermStack S);    /* clear array; no memory reclaim  */
void ATstackPrint(FILE* fp, ATermStack S); /* for testing purpose only */

/* int ATstackDepth(ATermStack S); */
#define ATstackDepth(S) ((S)->free)

/* int ATstackSize(ATermStack S); */
#define ATstackSize(S) ((S)->size)

void ATstackPush(ATermStack S,ATerm t);
ATerm ATstackPop(ATermStack S);
/* ATerm ATstackTop(ATermStack S); */
#define ATstackTop(S) (assert(0<(S)->free),(S)->array[(S)->free-1])

void ATstackSet(ATermStack S, int i, ATerm t);
/* if i<free: 
   - assign S[i] = t
   - otherwise: extends S by pushing NULL, then push t at location i,
   free = i+1
*/

/* ATerm ATstackGet(ATermStack S, int i); */
#define ATstackGet(S,i) (((i)<(S)->free ? (S)->array[(i)] : NULL))

/* possible future extensions: 
   - ATermStack ATarrayToStack(ATerm* array, int size);
   - ATermStack ATstackCopy(ATermStack S);
*/

#endif
