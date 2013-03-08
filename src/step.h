
/* Stepper interface */
#ifndef ST_H
#define ST_H

#include <stdlib.h>
#include "aterm2.h"

/* Ordering of sum variables 
   noOrdering:            No reordering of sum variables
   enumOccurrenceOrdering: Variables of enumeration sort first. 
                            The more the sum variable occurs in condition, 
                            the earlier he will be enumerated.
   levelOrdering:         The lower of level of occurrence of the sum 
                            variable, the earlier he will be enumerated.
   occurrenceOrdering:    The more the sum variable occurs in the condition, 
                            the earlier he will be enumerated. */

typedef enum {noOrdering, enumOccurrenceOrdering, levelOrdering,
              occurrenceOrdering} ST_ORDER;
              
typedef enum {noReducing, tarjanReducing, newReducing} ST_REDUCING;
/* Low Level stepper interface */

typedef void (*STcallback)();
/* The function of the sort "STcallback" will be automatically invoked when a 
   new transition is computed. There are no argements. The variables which 
   contain source, label, resp. dest are defined outside the stepper. 
   They are available inside the callback function and will be used 
   in the stepper. */
   

typedef ATbool (*STmemberFunction)(ATerm label);
/* During a call to STstepSubset, this function will be called for
   every summand with the label of that summand as argument. If the
   functions returns true then the summand will be stepped otherwise
   it will be skipped.
*/

void STsetArguments(int *argc, char ***argv); 
/* Reads the arguments for the stepper. STsetArguments must be called before 
STinitialize.
 */

void STinitialize(ST_ORDER order, ATerm* label,ATerm* dest, 
      STcallback callback);
/* Initializes the stepper. 
STinitialize must be called after RWinitialiseRewriter.
Routine "callback" must be provided by the programmer.
Parameter "order" determines how the sum variable in a summand must be ordered 
before enumeration. The programmer must provide addresses of two variables.
The label of the transition will be assigned to variable "label" and 
the destination of the transition will be assigned to variable "dest" 
during state space generation . 
*/

void STsetCallback(STcallback callback);
/* Replaces the current callback function, which is invoked at each 
generation of a transition, by the new callback function "callback". */

void SThelp(void);
 
void STsetLabelAddress(ATerm* label);
/* Replaces the address for storing the label by the new address "label". */

void STsetDestAddress(ATerm* dest);
/* Replaces the address for storing the destination by the new address "dest". 
*/

void STsetInitialState();
/* The initial state will be put in the variable "dest". */

int STstep(ATerm* src);
/* Computes the transitions from the state stored in variable "src".
Returns the number of transitions from that state. 
If -1 is returned an error occurred. 
*/

int STstepSubset(ATerm* src, STmemberFunction member);
/* Computes a subset of the transitions from the state stored in variable 
"src". */

int STstepSmd(ATerm* src, int *smds, int nsmd);
int STstepSubsetSmd(ATerm* src, int *smds, int nsmd, STmemberFunction member);

int STnumberOfUsedSummands(void);

ATermList STgetUsedSummands(void);
/* Returns the cumulative used summands by the stepper */

int STgetSmdIndex(void);
/* To be used in CallBack Functions to enquire the current sequence number 
of the summand in the LPE */

ATerm STcurrentSummand(void);
float STgetNumberOfSummands(void);

/* The following functions are used for symbolic reachability. */
ATerm STgetLabel(int smd);
int STgetProjection(int *proj,int smd);
int STgetSummandCount(void);

#endif

