/* abbreviations of predefined strategies */
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "aterm2.h"

#define INNERMOST 1
#define JUSTINTIME 2


void JIT_init(ATermList functions, ATermList rules, ATermList strategy,
	      int default_strat, char with_hashing);
/* Initialize JIT rewriter with 
 * - signature         e.g. [f(1),g(3)]
 * - rules             e.g. [alpha([x,y],g(x,y,y),f(y))]
 * - strategy          e.g. [ g([2,3,alpha,1]) ]
 * - default strategy  e.g. JUSTINTIME, or INNERMOST
 * - with_hashing      e.g. 0 (false) or 1 (true)
 */

void JIT_cond_init(ATermList functions, ATermList rules, ATermList strategy,
	      ATerm True, int default_strat, char with_hashing);
/* Initialize JIT rewriter, with True term used for conditional rewriting.
 * - true_value        e.g. MCRLterm_true for conditional rewriting, or NULL for normal rewriting
 */

ATerm JIT_normalize(ATerm t);
 /* JIT_normalize(t) fully normalizes term t in the 
  * global environment, according to the strategy
  */

void JIT_assign(Symbol v, ATerm t);
/* assign t to v in the current block, changing the global environment
 * ASSUMPTION: t is normal
 */

void JIT_enter(void);
/* enter an new block, without modifying the global environment */

void JIT_leave(void);
/* return to the previous environment, restoring the global environment */

void JIT_clear(void);
/* restore the global environment, stay in the same block */

 int JIT_level(void);
/* return the current level (block) */

void JIT_flush(void);
/* This function makes the hash table of previous results empty.
 * Functional behaviour is not changed by JIT_flush.
 */

void RWstatistics(void);
void JITsetVerbose(void);
void JITsetLimit(int n);

