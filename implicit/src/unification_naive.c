/* 
   $Id: unification_naive.c,v 1.3 2004/02/02 15:38:47 bertl Exp $  
   Author and Copyright: Jaco van de Pol, CWI, Amsterdam, vdpol@cwi.nl
   tera version 2.0.c: a satisfiability checker for term algebra formulas. */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "unification.h"

/******************************/
/* Unification: naive variant */
/******************************/

#ifdef MASTER
#define ATisVariable ATisVariableNAIVE
#define AToccurs AToccursNAIVE
#define ATsubstVar ATsubstVarNAIVE
#define ATsubstitute ATsubstituteNAIVE
#define ATunifySystem ATunifySystemNAIVE
#define ATunify ATunifyNAIVE
#define ATsubstToStack ATsubstToStackNAIVE
#endif

ATbool ATisVariable(ATerm t) {
  /* internally, variables are represented by integers */
  return ATgetType(t)==AT_INT;
}

ATbool AToccurs(ATerm var, ATerm t) {
  if (var==t) return ATtrue;
  else if (ATisVariable(t)) return ATfalse;
  else {
    int i;
    for (i=ATgetArity(ATgetSymbol(t))-1;i>=0;i--)
      if (AToccurs(var,ATgetArgument(t,i))) return ATtrue;
  }
  return ATfalse;
}

ATerm ATsubstVar(ATerm t, ATerm var, ATerm s) {
  if (var == t) return s;
  else if (ATisVariable(t)) 
    return t;
  else {
    Symbol sym = ATgetSymbol(t);
    int i,n=ATgetArity(sym);
    ATerm* args = (ATerm*)alloca(n*sizeof(ATerm));
    for (i=0;i<n;i++)
      args[i]=ATsubstVar(ATgetArgument(t,i),var,s);
    return (ATerm)ATmakeApplArray(sym,args);
} }

ATerm ATsubstitute(ATerm t, ATermSubst sigma) {
  if (ATisVariable(t)) {
    ATerm s=ATstackGet(sigma,ATgetInt((ATermInt)t));
    return (s ? s : t);
  }
  else {
    Symbol sym = ATgetSymbol(t);
    int i,n=ATgetArity(sym);
    ATerm* args = (ATerm*)alloca(n*sizeof(ATerm));
    for (i=0;i<n;i++)
      args[i]=ATsubstitute(ATgetArgument(t,i),sigma);
    return (ATerm)ATmakeApplArray(sym,args);
} }

static void unfold_substitution(ATermStack sub, ATermSubst sigma) {
  /* sub is a replacement list, [..ti,Xi...tj,Xj...(top of stack)],
     such that Xi doesn't occur in tj (for i<= j)
     - the result is the idempotent substitution.
     - sub is made empty
  */
  assert(ATstackDepth(sigma)==0);
  while (ATstackDepth(sub)>0) {
    ATerm t1 = ATstackPop(sub);
    ATerm t2 = ATsubstitute(ATstackPop(sub),sigma);
    ATstackSet(sigma,ATgetInt((ATermInt)t1),t2);
} }

ATbool ATunifySystem(ATermStack system, ATermSubst sigma) {
  /* Solves {system[0]=system[1], ...,system[2n-2]=system[2n-1]}
     invariant: either result is a replacement list of the form 
     [..ti,Xi...tj,Xj...(top of stack)], such that 
     Xj doesn't occur in ti (for i<= j),
     or it is NULL, and the system is not unifiable.
     system is made empty.
  */
  static char first_call = 1;
  static ATermStack solution; /* static to save on allocation */
  char unifiable = 1;
  if (first_call) {
    first_call=0;
    solution =  ATstackCreate(40);
  }
  assert(ATstackDepth(solution)==0);
  while (ATstackDepth(system)>0) {
    ATerm t1=ATstackPop(system);
    ATerm t2=ATstackPop(system);
    Symbol s1,s2;
    int i,n;
    if (t1==t2) continue;
    if (ATisVariable(t2))
      { ATerm t3=t1; t1=t2; t2=t3; }
    if (ATisVariable(t1)) {
      if (AToccurs(t1,t2)) {
	unifiable=0;
	break;
      }
      else {
	int n = ATstackDepth(system);
	ATstackPush(solution,t2);
	ATstackPush(solution,t1);
	for (i=0;i<n;i++) 
	  ATstackSet(system,i,ATsubstVar(ATstackGet(system,i),t1,t2));
    } }
    else { /* neither t1 nor t2 is a variable. */
      s1 = ATgetSymbol(t1);
      s2 = ATgetSymbol(t2);
      if (s1!=s2) {
	unifiable=0;
	break;
      }
      else {
	n = ATgetArity(s1);
	for (i=0;i<n;i++) {
	  ATstackPush(system,ATgetArgument(t1,i));
	  ATstackPush(system,ATgetArgument(t2,i));
  } } } }
  if (unifiable) {
    if (sigma) unfold_substitution(solution,sigma);
    return ATtrue;
  }
  else {
    ATstackReset(system);
    ATstackReset(solution);
    return ATfalse;
} }

ATbool ATunify(ATerm t1, ATerm t2, ATermSubst sigma) {
  static char first = 1;
  static ATermStack system; /* static to avoid allocation */
  if (first) {
    first=0;
    system = ATstackCreate(40);
  }
  assert(ATstackDepth(system)==0);
  ATstackPush(system,t1);
  ATstackPush(system,t2);
  return ATunifySystem(system,sigma);
}

void ATsubstToStack(ATermSubst sigma, ATermStack stack) {
  int i;
  assert(ATstackDepth(stack)==0);
  for (i=ATstackDepth(sigma)-1;i>=0;i--) {
    ATerm t = ATstackGet(sigma,i);
    if (t) {
      ATstackPush(stack,t);
      ATstackPush(stack,(ATerm)ATmakeInt(i));
} } }
