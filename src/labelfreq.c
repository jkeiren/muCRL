/* $Id: labelfreq.c,v 1.1 2002/01/29 15:33:03 bertl Exp $ */

#include <stdio.h>
#include "aterm2.h"

/* An example of linking of user defined call backs to the instantiator.
   Generating a frequency table of the actions occurring in the LTS */

static ATermIndexedSet db;
static int *freq, size, max = -1;

static void EnlargeTable(int n) {
   int i = size;
   if (n < size) return;
   while (n >= size) size *= 2;
   if (!(freq = (int*) realloc(freq,
          size*sizeof(int))))
     ATerror("Cannot reallocate freq array (%d)", size);
   for (;i<size;i++) freq[i]=0;
   }

void Open(int root, char *name) {
    /* This will be called before generation of the LTS. 
       root is de state number of the initial state
       name is the name of the output file (input file name minus .tbf,
       or the name behind -o flag)
    */
    db = ATindexedSetCreate(10000, 70);
    size = 1000;
    freq = (int*) calloc(size, sizeof(int));
    if (!freq) ATerror("Cannot allocate array freq");
    ATwarning("Open %s", name);
    }
    
void Close(int states, int transitions) {
    /* This will be called after generation of the LTS.
    states: number of generated states transitions: number of generated 
       transitions */
    int i;
    for (i=0;i<=max;i++) 
    ATfprintf(stderr, "%t: %d\n", ATindexedSetGetElem(db, i), freq[i]);
    ATwarning("Close: states %d transitions %d\n", states, transitions);
    }

void WriteTrans(int src, ATerm label, int dest) {
   /* This will be called at each generation of a transition.
      src: state number from which the transition departs
      label: label of the transition
      dest: destination of the transition
   */
   ATbool new;
   int k = ATindexedSetPut(db, label, &new);
   if (k>max) max = k;
   EnlargeTable(k);
   freq[k]++;
   }

void WriteState(int src, int cnt) {
   /* This will be called after exploration of each state.
      src: state number of the expored state
      cnt: number of transitions which departs from that state
   */
   if (src%1000==0) 
   ATwarning("State %d is explored (start of %d transition%c)", 
              src, cnt, cnt<=1?' ':'s');
}
