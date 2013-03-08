/* 
   $Id: unification_linear.c,v 1.3 2004/02/02 15:38:47 bertl Exp $  
   Author and Copyright: Jaco van de Pol, CWI, Amsterdam, vdpol@cwi.nl
   tera version 2.0.c: a satisfiability checker for term algebra formulas. */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "unification.h"

/********************************/
/* Unification: hashing variant */
/********************************/

#ifdef MASTER
#define ATisVariable ATisVariableLINEAR
#define AToccurs AToccursLINEAR
#define ATsubstVar ATsubstVarLINEAR
#define ATsubstitute ATsubstituteLINEAR
#define ATunifySystem ATunifySystemLINEAR
#define ATunify ATunifyLINEAR
#define ATsubstToStack ATsubstToStackLINEAR
#endif

ATbool ATisVariable(ATerm t) {
  /* internally, variables are represented by integers */
  return ATgetType(t)==AT_INT;
}

static ATermIndexedSet No_occurs; /* used by occurs */
static ATermTable Subst;          /* used by substVar,substitute */

static ATbool occurs_rec(ATerm var, ATerm t, ATbool *nonempty) {
  /* invariants: 
     - var doesn't occur in terms in No_occurs 
     - nonempty iff No_occurs is not empty
  */
  ATbool b;
  if (var==t) return ATtrue;
  else if (ATisVariable(t)) return ATfalse;
  else if (*nonempty && ATindexedSetGetIndex(No_occurs,t)>=0) return ATfalse;
  else {
    int i;
    for (i=ATgetArity(ATgetSymbol(t))-1;i>=0;i--)
      if (occurs_rec(var, ATgetArgument(t,i),nonempty)) return ATtrue;
  }
  *nonempty = ATtrue;
  ATindexedSetPut(No_occurs,t,&b);
  return ATfalse;
}

ATbool AToccurs(ATerm var, ATerm t) {
  static char first_call=1;
  ATbool set_nonempty=ATfalse;
  ATbool occurs;
  if (first_call) {
    first_call=0;
    No_occurs=ATindexedSetCreate(16,40);
  }
  occurs = occurs_rec(var,t,&set_nonempty);
  if (set_nonempty) ATindexedSetReset(No_occurs);
  return occurs;
}

static ATerm substVar_rec(ATerm t, ATerm var, ATerm s, ATbool *nonempty) {
  /* invariants: 
     - Subst contains pairs (r , r[var := s]) 
     - *nonempty iff Subst is not empty 
  */
  ATerm r;
  if (var == t) return s;
  else if (ATisVariable(t)) return t;
  else if (*nonempty && (r=ATtableGet(Subst,t))) return r;
  else {
    Symbol sym = ATgetSymbol(t);
    int i,n=ATgetArity(sym);
    ATerm* args = (ATerm*)alloca(n*sizeof(ATerm));
    for (i=0;i<n;i++)
      args[i]=substVar_rec(ATgetArgument(t,i),var,s,nonempty);
    r = (ATerm)ATmakeApplArray(sym,args);
    *nonempty=ATtrue;
    ATtablePut(Subst,t,r);
    return r;
  }
}

static char first_subst_call=1;

ATerm ATsubstVar(ATerm t, ATerm var, ATerm s) {
  ATerm result;
  ATbool table_nonempty=ATfalse;
  if (first_subst_call) {
    first_subst_call=0;
    Subst=ATtableCreate(16,40);
  }
  result = substVar_rec(t,var,s,&table_nonempty);
  if (table_nonempty) ATtableReset(Subst);
  return result;
}

static ATerm substitute_rec(ATerm t, ATermSubst sigma, ATbool *nonempty) {
  /* invariants: 
     - Subst contains pairs (r , r^sigma)
     - *nonempty iff Subst is not empty 
  */
  ATerm s;
  if (ATisVariable(t)) {
    s=ATstackGet(sigma,ATgetInt((ATermInt)t));
    return (s ? s : t);
  }
  else if (*nonempty && (s=ATtableGet(Subst,t))) 
    return s;
  else {
    Symbol sym = ATgetSymbol(t);
    int i,n=ATgetArity(sym);
    ATerm* args = (ATerm*)alloca(n*sizeof(ATerm));
    for (i=0;i<n;i++)
      args[i]=substitute_rec(ATgetArgument(t,i),sigma,nonempty);
    s = (ATerm)ATmakeApplArray(sym,args);
    *nonempty=ATtrue;
    ATtablePut(Subst,t,s);
    return s;
} }

ATerm ATsubstitute(ATerm t, ATermSubst sigma) {
  ATerm result;
  ATbool table_nonempty=ATfalse;
  if (first_subst_call) {
    first_subst_call=0;
    Subst=ATtableCreate(16,40);
  }
  result = substitute_rec(t,sigma,&table_nonempty);
  if (table_nonempty) ATtableReset(Subst);
  return result;
}

static ATermStack      assigned       = NULL;  /* owned by ATunifySystem */
static ATermTable      equivalence    = NULL;  /* owned by ATunifySystem */
static ATermIndexedSet loop_detection = NULL;  /* owned by unfold_solution */
static ATermTable      solution       = NULL;  /* owned by unfold_solution */

static ATerm find(ATerm t) {
  /* returns representative in 'equivalence', 
     shortening find-paths along the way (as in Union/Find) */
  ATerm s = ATtableGet(equivalence,t);
  if (s) {
    ATerm r = find(s);
    if (r != s) ATtablePut(equivalence,t,r);
    return r;
  }
  return t;
}

static ATerm unfold_rec(ATerm t) {
  /* Completely unfolds t according to equivalence.
     invariants: 
     - loop_detection contains "ancestors" of t
     - t is end point of find
     - solution contains correct results [t -> s]
     returns NULL: loop detected
     returns s: s is unfolding of t.
  */
  ATerm s;
  ATbool no_loop;
  char unifiable=1;
  if (ATisVariable(t)) return t;
  if ((s=ATtableGet(solution,t))) return s;
  ATindexedSetPut(loop_detection,t,&no_loop);
  if (no_loop) {
    Symbol sym = ATgetSymbol(t);
    int i,n=ATgetArity(sym);
    ATerm *args = (ATerm*)alloca(n*sizeof(ATerm));
    for (i=0;i<n;i++)
      if (!(args[i] = unfold_rec(find(ATgetArgument(t,i))))) {
	unifiable=0;
	break;
      }
    ATindexedSetRemove(loop_detection,t);
    if (unifiable) {
      s=(ATerm)ATmakeApplArray(sym,args);
      ATtablePut(solution,t,s);
      return s;
  } }
  /* here either !no_loop, or !unifiable holds */
  return NULL;
}

static char unfold_solution(ATermSubst sigma) {
  /* - makes assigned, solution and equivalence empty
     - doesn't alter equivalence, except shortening find paths
     - returns 1: unifiable; sigma contains solution (except when NULL)
     - returns 0: not unifiable; sigma is empty
     Note: unfolding is also needed if sigma=NULL to detect loops.
  */
  int i;
  ATerm t;
  char unifiable=1;
  static char first_call=1;
  if (first_call) {
    first_call = 0;
    loop_detection=ATindexedSetCreate(64,50);
    solution = ATtableCreate(64,50);
  }
  assert(ATisEmpty(ATtableKeys(solution)));
  for (i=ATstackDepth(assigned)-1;i>=0;i--) {
    ATerm x = ATstackPop(assigned);
    assert(ATisEmpty(ATindexedSetElements(loop_detection)));
    t = unfold_rec(find(x));
    if (t && sigma) 
      ATstackSet(sigma,ATgetInt((ATermInt)x),t);
    else {
      unifiable=0;
      break;
  } }
  ATtableReset(solution);
  ATtableReset(equivalence);
  if (unifiable)
    return ATtrue;
  else {
    ATstackReset(assigned);
    if (sigma) ATstackReset(sigma);
    return ATfalse;
} }

ATbool ATunifySystem(ATermStack system,ATermSubst sigma) {
/* Solves {system[0]=system[1], ...,system[2n-2]=system[2n-1]}
   - returns 0: t1=t2 is not unifiable; sigma is reset.
   - returns 1: ATermSubst represents the mgu {X1->t1,..,Xn->tn}
   This implements the Pascal version of Baader/Nipkow.
   (Linear space, nearly linear time)
   - ATermTable equivalence contains the Union/Find structure
   - ATermStack assigned contains the domain of the solution
   First, the system is solved without occur-check
   Subsequently, a substitution is computed, with loop detection.
*/
  static char first_call = 1;
  char unifiable = 1;
  if (first_call) {
    first_call=0;
    assigned    =  ATstackCreate(40);
    equivalence = ATtableCreate(40,40);
  }
  assert((!sigma) || (ATstackDepth(sigma)==0));
  assert(ATstackDepth(assigned)==0);
  assert(ATisEmpty(ATtableKeys(equivalence)));
  while (ATstackDepth(system)>0) {
    ATerm t1=find(ATstackPop(system));
    ATerm t2=find(ATstackPop(system));
    int i,n;
    if (t1==t2) continue;
    if (ATisVariable(t2))
      { ATerm t3=t1; t1=t2; t2=t3; }
    if (ATisVariable(t1)) {
      ATstackPush(assigned,t1);
      ATtablePut(equivalence,t1,t2);
      /* ATprintf("%t->%t\n",t1,t2); */
    }
    else { /* both t1 and t2 start with function symbol. */
      Symbol s1 = ATgetSymbol(t1);
      Symbol s2 = ATgetSymbol(t2);
      if (s1!=s2) {
	unifiable=0;
	break;
      }
      else {
	n = ATgetArity(s1);
	ATtablePut(equivalence,t1,t2); /* note: forget about cardinality */
	for (i=0;i<n;i++) {
	  ATstackPush(system,ATgetArgument(t1,i));
	  ATstackPush(system,ATgetArgument(t2,i));
  } } } }
  if (unifiable) return unfold_solution(sigma);
  else {
    ATstackReset(system);
    ATstackReset(assigned);
    ATtableReset(equivalence);
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
