#ifndef LTS_H
#define LTS_H

#include <stdlib.h>
#include "aterm2.h"
#include "rw.h"
#include "step.h" 

typedef void (*LTScallback)(int src, ATerm label, int dest);
/* The function of the sort "LTScallback" will be automatically invoked when a 
   new transition is computed. "src" and "dest" stand for indices 
   in the data base of respectively the start vector and the end vector 
   of a generated transition */

void LTSsetArguments(int *argc, char ***argv);

void LTShelp(void);

void LTSinitialize(LTScallback callback);
/* 
This functions calls STinitialize to install the proper call-back. 
Parameter "order" determines how the sum variable in a summand must be ordered 
before enumeration. 
*/

void LTSfinish(int explored);
/* Advised to place this at the end of state space generation.
   It prints some messages. "explored" is the number of explored states
*/

void LTSsetCallback(LTScallback callback);
/* Replaces the current callback function, which is invoked at each 
generation of a transition, by the new callback function "callback". */

int LTSgetInitialState();
/* Returns the index in the data base of the initial state */

int LTSstep(int state);
/* Computes the transitions from the state stored in variable "state".
Returns the number of transitions from that state. 
If -1 is returned an error occurred. 
*/

/* Database interface */

ATerm LTSgetState(int state);
/* Get the state as a list which belongs to state number "state"  or
the term "terminated" */

ATerm LTSgetPrintState(int state);
/* Get the state as a list which belongs to state number "state"  or
the term "terminated" in printable format */

int LTSputState(ATermList state);
/* Puts the state in the data base end returns its index */

int LTSgetSmdIndex(void);
/* To be used in CallBack Functions to enquire the current sequence number 
of the summand in the LPE */

int LTSnumberOfUsedSummands(void);
/* Returns the cumulative number of summands used by LTSstep since
the call of LTSinitialize */

ATermList LTSgetUsedSummands(void);
int LTSgetStateNo(ATermList statevector);
ATermList LTSgetTrace(char *filename, int *current);
/* Reads trace from file  */
ATbool LTSsaveTrace(char *filename, ATermList transitions, int current);

/* Saves trace */
char *LTSgetVersion(void);
/* Returns version of the trace format */
#ifdef INSTRUMENTED
void LTSreport(void); 
#endif

#endif
