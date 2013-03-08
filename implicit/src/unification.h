/* 
   $Id: unification.h,v 1.1 2004/01/22 15:43:13 bertl Exp $  
   Author and Copyright: Jaco van de Pol, CWI, Amsterdam, vdpol@cwi.nl
   tera version 2.0.c: a satisfiability checker for term algebra formulas. */

#ifndef UNIFY_H
#define UNIFY_H

#ifdef MASTER
#define NAIVE 0
#define LINEAR 1
extern char UNIF;  /* linear unification by default */
#endif

#include "aterm2.h"
#include "at_stack.h"

typedef ATermStack ATermSubst;

ATbool ATisVariable(ATerm t);
/* checks if t is a variable */

ATbool AToccurs(ATerm var, ATerm t);
/* check if var occurs in t; can also be used as subterm check */

ATerm ATsubstVar(ATerm t, ATerm var, ATerm s); 
/* replace var in t by s */

ATerm ATsubstitute(ATerm t, const ATermSubst sigma);
/* apply substitution sigma to t */

/* recall: mgu = most general unifier */

ATbool ATunify(ATerm t1, ATerm t2, ATermSubst sigma);
/* The equation t1=t2 is solved. Either:
   - returns 0: t1=t2 is not unifiable; sigma is reset.
   - returns 1: sigma represents the mgu {X1->t1,..,Xn->tn}
     The mgu is guaranteed to be idempotent, and without X->X.
   Precondition: sigma is empty.
   Note: sigma=NULL is allowed: only a check is done.
*/

ATbool ATunifySystem(ATermStack system, ATermSubst sigma);
/* Similar to ATunify, but now the starting problem is
   system[0]=system[1] AND ... AND system[2n-2]=system[2n-1]
   - system is reset.
*/

void ATsubstToStack(ATermSubst sigma, ATermStack stack); 
/* pushes substitution sigma of the form 
   {X1->t1,..,Xn->tn} to the stack as [tn,Xn,..,t1,X1 (top of stack)]
   Precondition: stack should be empty stack.
*/

#endif
