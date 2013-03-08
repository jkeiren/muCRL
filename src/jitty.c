/* Implementation of JITty, a rewriter using strategy annotations
 * Author: Jaco.van.de.Pol@cwi.nl
 *
 * For the used strategy annotations, see the paper
 * "Just-in-Time: on strategy annotations", Jaco van de Pol, ENTCS volume 57.
 *
 * The strategy annotation for a function can be either:
 * - predefined (innermost or justintime)
 * - user defined; in this case it is checked if the strategy is
 *   . full (rewrites all arguments and tries all rules)
 *   . in-time (rewrites arguments before trying rules that need them)
 *
 * Date: 25 january 2002
 */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "jitty.h"
#include <assert.h>

int STEPS=0;
int TotalSteps=0;
int CALLS=0;
int DEPTH=0;
int MAX_DEPTH=0;
int limit=0;
char verbose=0;

/* maximal matching depth of rules; see match_depth() for definition.
   Computed by distribute_rules(), and used to bound the
   stack during matching */
static int Max_Match_Depth=0; 

/* maximal number of vars in rules. Computed by distribute_rules() */
static int Max_Vars=0; 

void RWstatistics(void) {
  fprintf(stderr,"Total #rewrite calls: %d\n",CALLS);
  fprintf(stderr,"Total #rewrite steps: %d\n",TotalSteps);
  fprintf(stderr,"Max. condition-depth: %d\n",MAX_DEPTH);
}

/* maximal sizes for arrays etc. */

#define SYMTABLE 40000  /* max. number used by ATerms for representing function symbols */
#define MAXLEVEL 9      /* max. number of levels for substitution */
#define PERLEVEL 2400   /* max. number of substitutions per level */

static ATbool hash = ATtrue; 
/* indicates computed results are put in a hash table for future use. */


/* Four parts will follow:
 * I. Actual rewrite engine 
 * II. Substitution mechanism.
 * III. Initialization of rewriter, mainly concerned with computing/checking strategies.
 */


/* PART I
 * Acutal rewrite engine
 */

static Symbol normal;  /* symbol to denote a normal term: normal(term) */
static Symbol e;       /* symbol used to denote an equation: e(lhs,rhs) */
static Symbol Var;     /* symbol used for variables in rules */
static ATerm jitTRUE=NULL;/* true term, used to test conditions */

static ATerm  *subs_table; /* contains current global substitution (environment) */
static ATerm *binding;     /* contains current local substitution (during matching) */
static int *filled;        /* contains the domain of the local substitution */
static int here;           /* pointer to current position in filled */

static ATermTable normalized; /* table of previously computed results
			       * this is defined iff (hash == ATtrue)
			       */
static ATermList *strategy_table; /* array of strategy annotations for function symbols */


static void reset_binding() {
  /* resets the local substitution to the empty one; 
   * used between rewrite steps or after failing match
   */
  while (here >0) {
    here--;
    binding[filled[here]]=NULL;
  }
}

static char match(int arity, ATerm lhs, ATerm args[],
		  char norms[]) {
  /* matches arguments of lhs with array of terms args,
   * taking into acount the "normal" symbol in args[i] iff norms[i]
   *
   * precondition: arity = lengths of args and norms = # direct subterms of lhs.
   * returns 1 plus a local substitution binding[] if match is possible
   * returns 0 otherwise
   */

  char candidate=1;
  int cp,n;  /* cp = current position; n = number of subterms in current position */
  int i,j;
  ATerm t1=NULL, t2=NULL,q=NULL;
  //ATerm* terms = alloca(Max_Match_Depth*sizeof(ATerm)); 
  //ATerm* lhss  = alloca(Max_Match_Depth*sizeof(ATerm)); 
  DECLA(ATerm,terms,Max_Match_Depth); /* subterms of args[cp] still to be checked */
  DECLA(ATerm,lhss,Max_Match_Depth);  /* subterms of lhs still to be checked */

  Symbol f;

  /* This loop is not needed, if the ATerm gc is correct
  for (i=0;i<Max_Match_Depth;i++)
    terms[i] = lhss[i] = 0;
  */

  for (cp=0;candidate && cp<arity; cp++) {
    n=1;
    terms[0]=args[cp];
    lhss[0] = ATgetArgument(lhs,cp);
    while ((n>0) && candidate) {
      n--;
      t1 = lhss[n];
      t2 = terms[n];
      f = ATgetSymbol(t1);

      if (f==Var) {
	i = ATgetInt((ATermInt)ATgetArgument(t1,0));
	if (norms[cp])
	  t2 = (ATerm)ATmakeAppl1(normal,t2);
	q = binding[i];
	if (q) 
	  candidate = (q==t2);   /* check for non-linear occurrence;
				  * Note: non-linear arguments always under normal */
	else { /* make binding */
	  binding[i] = t2;
	  filled[here++]=i;
	}
      }
      else { /* function symbol */ 
	if (f == ATgetSymbol(t2)) {
	  i = ATgetArity(f);
	  assert(n+i<=Max_Match_Depth);
	  for (j=0; j<i; j++) {
	    lhss[n] = ATgetArgument(t1,j);
	    terms[n]  = ATgetArgument(t2,j);
	    n++;
	  }
	}
	else /* no match */
	  candidate = 0;
      }
    } /* while */
  } /* for */
  if (candidate) 
    return 1;
  else {
    reset_binding();
    return 0;
  }
}

static ATerm build(ATerm rhs) {
  /* recursively builds rhs, taking into account local substitution in binding[]
   */
  Symbol f = ATgetSymbol((ATermAppl)rhs);
  
  if (f==Var)
    return binding[ATgetInt((ATermInt)ATgetArgument(rhs,0))];
  else {
    /* rhs starts with function symbol */
    int i,arity = ATgetArity(f);
    // ATerm* args = alloca(arity*sizeof(ATerm));
    DECLA(ATerm,args,arity);
    /* This loop is not needed, if the ATerm gc is correct.
    for (i=0;i<arity;i++) 
      args[i] = NULL; */
    for (i=0;i<arity;i++) 
      args[i] = build(ATgetArgument(rhs,i));
    return (ATerm)ATmakeApplArray(f,args);
  }
}

/* mutual recursion:
 * normalize(t) fully normalizes term t according to strategy_table by applying "steps"
 * step(s,t,l) applies rewrite steps to t according strategy l, normalizing arguments.
 */

static ATerm normalize(ATerm t);

static ATerm step(int symbol, ATerm t, ATermList annotation) {
  /* annotation is of the form [ i,j, e(lhs,rhs), m, e(..), etc ]
   * t is a term to be rewritten, with head symbol 'symbol'
   * returns the normal form of t according to the strategy annotation
   */
  
  ATerm lhs=NULL, cond=NULL, rhs=NULL, next=NULL;
  int i,n = ATgetArity(symbol);
  // char* norms = alloca(n*sizeof(char));
  // ATerm* args = alloca(n*sizeof(ATerm));
  DECLA(char,norms,n); /* administration of already normalized arguments */
  DECLA(ATerm,args,n);

  for (i=0;i<n;i++) {
    norms[i]=0;
    args[i]=ATgetArgument(t,i);
  }
  
  while (!ATisEmpty(annotation)) {
    next = ATgetFirst(annotation);
    annotation = ATgetNext(annotation);
    if (ATgetSymbol(next)==e) { /* it is a rule */
      lhs = ATgetArgument(next,1);
      if (match(n,lhs,args,norms)) {
	/* ATprintf("redex: %t\n",lhs); */
	rhs = build(ATgetArgument(next,2));
	cond = build(ATgetArgument(next,0));
	reset_binding();
	if (cond==jitTRUE) { /* only to optimize non-conditional rules */
	  STEPS++;
	  return normalize(rhs);
	}
	else {
	  DEPTH++;
	  if (DEPTH > MAX_DEPTH) 
	    MAX_DEPTH=DEPTH;
	  cond = normalize(cond);
	  DEPTH--;
	  if (cond==jitTRUE) {
	    STEPS++;
	    return normalize(rhs);
	  }
	}
      }
    }
    else { /* normalize argument */
	i=ATgetInt((ATermInt)next);
	args[i] = normalize(args[i]);
	norms[i] = 1;
    }
  }
  next=  (ATerm)ATmakeApplArray(symbol,args);
  return next;
}

static ATerm removeNormalTag(ATerm t) {
   if (ATgetType(t)!=AT_APPL) return t;
   {
   int s = ATgetSymbol(t), n = ATgetArity(s), i;
   DECLA(ATerm, a, n);
   if (s==normal) return ATgetArgument(t, 0);
   for (i=0;i<n;i++) 
      a[i]=removeNormalTag(ATgetArgument(t, i));
   return ATmakeApplArray(s, a);
   }
   }

static ATerm normalize(ATerm t) {
 /* normalize(t) fully normalizes term t in the global environment,
  * according to strategy_table by applying "steps"
  */
  int n;
  ATermList l=NULL;
  ATerm result=NULL;
  /* ATfprintf(stderr,"Normalize: %t\n",t); */
  
  n = ATgetSymbol(t);
  
  if (n>=SYMTABLE) { /* assume that t is an unknown variable */
    ATwarning("Symbol index too high (%d > %d)\n",n,SYMTABLE);
    return removeNormalTag(t);
  }
  
  if (n==normal)  /* assume terms with normal() mark to be normal */
    return ATgetArgument(t,0); 
  
  if (hash) { /* previously computed terms */
    result = ATtableGet(normalized,t);
    if (result) return result;
  } 
  else { /* only normal terms are assigned in the global environment */
    result = subs_table[n];
    if (result) return result;
  }

  if (limit && (STEPS > limit))
    if (verbose) {
      ATwarning("rewrite limit reached:");
      return t;
    }


  l = strategy_table[n];
  if (!l) { /* unknown symbol, assume it to be a variable */
    /* ATfprintf(stderr,"Unknown symbol: %s\n",ATgetName(n)); */ 
    return removeNormalTag(t);
  }

  /* OK, nothing special, so GO AHEAD */

  result = step(n,t,l);
  if (hash) /* store if required */
    ATtablePut(normalized,t,result);
  return result;
}

static ATerm subst(ATerm t);

ATerm JIT_normalize(ATerm t) {
  CALLS++;
  STEPS=0;
  if (hash)
    t= normalize(subst(t));
  else
    t= normalize(t);
  TotalSteps += STEPS;
  return t;
}

void JIT_flush(void) {
  if (hash) {
    ATtableDestroy(normalized);
    normalized = ATtableCreate(1024,60);
  }
}

/* PART II: SUBSTITUTION MECHANISM */

static int cardinality[MAXLEVEL];
static Symbol variable[MAXLEVEL][PERLEVEL];
static ATerm old_value[MAXLEVEL][PERLEVEL];
static int level;
static char SUBST=0;

static void assign(Symbol v, ATerm t) {
  /* assign t to v in the current level
   * ASSUMPTION: t is normal
   */
  int i;
  SUBST=1;

  for (i=0; i<cardinality[level]; i++)
    if (variable[level][i]==v) {
      subs_table[v]=t;
      return;
    }
  
  /* new variable */
  i=cardinality[level]++;
  if (i>=PERLEVEL)
    ATerror("Too many substitutions (>%d) at level %d\n",PERLEVEL,level);
  if (v>=SYMTABLE)
    ATerror("Symbol index too high (%d > %d)\n",v,SYMTABLE);
  
  old_value[level][i]= subs_table[v];
  variable[level][i] = v;
  subs_table[v] = t;
}

void JIT_assign(Symbol v, ATerm t) {
  if (hash)
    assign(v,(ATerm)ATmakeAppl1(normal,t));
  else
    assign(v,t);
}

void JIT_enter(void) {
  /* Enter a new level; the current substitution is not changed */
  if (level==MAXLEVEL)
    ATerror("Max number of levels exceeded (%d)",MAXLEVEL);
  level++;
  cardinality[level]=0;
}

void JIT_clear(void) {
  /* Undo all variable bindings of the current level */
  int i;
  for (i=0; i<cardinality[level]; i++)
    subs_table[variable[level][i]] = old_value[level][i];
  cardinality[level]=0;

  /* reset SUBST if all levels are empty */

  for (i=0; i<level; i++)
    if (cardinality[i]>0) return;
  SUBST=0;
  return;
}

void JIT_leave(void) {
  /* Return to the previous level, undoing all variable bindings of the current one */
  if (level==0)
    ATerror("Try to leave level 0");
  JIT_clear();
  level--;
}

int JIT_level(void) {
  /* return the current level */
  return level;
}

static void init_substitution(void) {
  /* initialize the substitution variables */
  int i,j;
  level=0;

  for (i=0; i<MAXLEVEL; i++)
    for (j=0; j<PERLEVEL; j++)
      old_value[i][j]=NULL;
  ATprotectArray((ATerm*)old_value,MAXLEVEL*PERLEVEL);
}

static ATermTable substituted=NULL;

static ATerm subst_rec(ATerm t) {
  /* Apply the global substitution to t */
  Symbol f;
  ATerm s=NULL;
  
  f=ATgetSymbol(t);
  if (f>=SYMTABLE)
    ATerror("Symbol index too high (%d > %d)\n",f,SYMTABLE);
  s = subs_table[f];
  if (s) return s;
  else {
    s = ATtableGet(substituted,t);
    if (s) return s;
    else {
      int i,n = ATgetArity(f);
      // ATerm* args = alloca(n*sizeof(ATerm));
      DECLA(ATerm,args,n);
      /* This loop is not needed, if the ATerm gc is correct.
      for (i=0;i<n;i++) 
        args[i] = NULL;
      */
      for (i=0;i<n;i++)
	args[i] = subst_rec(ATgetArgument(t,i));
      s = (ATerm)ATmakeApplArray(f,args);
      ATtablePut(substituted,t,s);
      return s;
    }
  }
}

static ATerm subst(ATerm t) {
  /* Apply the global substitution to t, if needed */
  if (SUBST) {
    if (!substituted) substituted = ATtableCreate(512,75);
    t = subst_rec(t);
    ATtableReset(substituted);
    return t;
  }
  else
    return t;  /* empty substitution is identity */
}


/* PART III: INITIALIZATION AND STRATEGY COMPUTATION
 *
 * This consists of:
 * III a -- define innermost and justintime strategies
 * III b -- translate and check user-defined strategies 
 * III c -- initialization and interpretation of input 
 */

/* PART III a -- define innermost and justintime strategies */

static ATermList innermost(ATermList rules,int arity) {
  /* computes the innermost strategy for 'rules' and 'arity' arguments */
  int j;
  for (j=arity;j>0;j--) 
    rules = ATinsert(rules,(ATerm)ATmakeInt(j-1));
  return rules;
}

static char occurs(ATerm t, ATerm s) {
  /* decides whether t is a subterm of s */
  ATermList l=NULL;

  if (s==t) return 1;

  for (l=ATgetArguments((ATermAppl)(s)) ; !ATisEmpty(l) ; l=ATgetNext(l))
    if (occurs(t,ATgetFirst(l))) return 1;

  return 0;
}

static char occurs_list(ATerm t, ATermList l) {
  /* decides whether t is a subterm of a term in l */
  for ( ; !ATisEmpty(l) ; l=ATgetNext(l))
    if (occurs(t,ATgetFirst(l))) return 1;
return 0;
}

static ATermList needed(ATerm rule) {
  /* returns the set of argument positions needed by the rewrite rule */
  /* precondition: rule is a rewrite rule in internal format e(cond,lhs,rhs)*/
  ATerm t=NULL, cond=NULL, lhs=NULL, rhs=NULL;
  ATermList args=NULL,l=NULL,needs=ATempty;
  int i=0;
  if (!ATmatch(rule,"e(<term>,<term>,<term>)",&cond,&lhs,&rhs)) 
    ATerror("Rule e(cond,lhs,rhs) expected\n");
  args = l = ATgetArguments((ATermAppl)lhs);
  while (!ATisEmpty(l)) {
    t = ATgetFirst(l);
    l = ATgetNext(l);
    if (ATgetSymbol(t)==Var) {
      if (occurs_list(t,ATremoveElementAt(args,i))) 
	needs=ATinsert(needs,(ATerm)ATmakeInt(i));
    }
    else
      needs=ATinsert(needs,(ATerm)ATmakeInt(i));
    i++;
  }
  return needs;
}
      
static char smaller(ATermList l,int i) {
  /* check whether all elements in l are strictly smaller than i */
  /* precondition: l is a list of ATerm integers */
  int j;
  while (!ATisEmpty(l)) {
    j = ATgetInt((ATermInt)ATgetFirst(l));
    if (j>=i) return 0;
    l = ATgetNext(l);
  }
  return 1;
}

static void divide(ATermList rules, int i,
		   ATermList* small_ones, ATermList* big_ones) {
  /* given a list of rules, and argument position i:
   * small_ones becomes the rules from l whose needed arguments are smaller than i.
   * big_ones becomes the remaining rules
   * NOTE: the small_ones will be in reversed order.
   */

  ATerm rule=NULL;
  *small_ones=ATempty;
  *big_ones=ATempty;
  
  while (!ATisEmpty(rules)) {
    rule = ATgetFirst(rules);
    rules = ATgetNext(rules);
    if (smaller(needed(rule),i))
      *small_ones = ATinsert(*small_ones,rule);
    else
      *big_ones = ATinsert(*big_ones,rule);
  }
  *big_ones = ATreverse(*big_ones);
}

static ATermList justintime(ATermList rules, int arity) {
  /* computes the justintime strategy for rules and 'arity' arguments */
  int i;
  ATermList current=NULL,result=NULL,small_ones=NULL;

  current=ATempty;

  divide(rules,0,&result,&rules);

  for (i=0;i<arity;i++) {
    divide(rules,i+1,&small_ones,&rules);
    result = ATconcat(small_ones,ATinsert(result,(ATerm)ATmakeInt(i)));
  }

  return ATreverse(result);
}


/* PART III b -- translate and check user-defined strategies */

static ATerm translate_term(ATerm t, ATermList vars) {
  /* translates term to "De Bruijn" notation
   * e.g.  f(y,z,x) [x,y,z]   becomes   f(Var(1),Var(2),Var(0))
   */

  int i;
  i = ATindexOf(vars,t,0);
  if (i>=0)
    return (ATerm)ATmakeAppl1(Var,(ATerm)ATmakeInt(i));
  else {
    Symbol f=ATgetSymbol(t);
    int n = ATgetArity(f);
    // ATerm* args = alloca(n*sizeof(ATerm));
    DECLA(ATerm,args,n);
    /* This loop is not needed, if the ATerm gc is correct.
    for (i=0;i<n;i++) 
      args[i] = NULL;
    */
    for (i=0;i<n;i++)
      args[i]=translate_term(ATgetArgument(t,i),vars);
    return (ATerm)ATmakeApplArray(f,args);
  }
}

ATermList translate_strategy(ATermList l) {
  /* translate strategy annotation, by:
   * 1. arguments are shifted  from 1..n to 0..n-1
   * 2. rules are translated to 'De Bruijn' notation
   * 3. rule labels are replaced by "e"
   * 4. conditions "T" are added where needed.
   * e.g.: [4,p0([x,y],cond(x),lhs(y,x),rhs(x))] becomes 
   *       [3,e(cond(Var(0)),lhs(Var(1),Var(0)),rhs(Var(0)))]
   * and: [rule([x],lhs(x),rhs(x))] becomes
   *      [e([x],jitTRUE,lhs(x),rhs(x))]
   * 5. reversing the list of rules 
   *   (example above should be modified)
   */
  
  ATermList result=ATmakeList0();
  while (!ATisEmpty(l)) {
    int i;
    ATerm first = ATgetFirst(l);
    l=ATgetNext(l);
    
    if (ATmatch(first,"<int>",&i))
      result = ATinsert(result,(ATerm)ATmakeInt(i-1));
    
    else { /* translate rule to 'De Bruijn' notation */
      ATerm lhs=NULL, rhs=NULL, cond=NULL;
      ATermList vars=NULL;
      vars = (ATermList)ATgetArgument(first,0);
      if (ATgetArity(ATgetSymbol(first))==4) {
	cond = ATgetArgument(first,1);
	lhs = ATgetArgument(first,2);
	rhs = ATgetArgument(first,3);
      } 
      else {
	cond = jitTRUE;
	lhs = ATgetArgument(first,1);
	rhs = ATgetArgument(first,2);
      }
      result=ATinsert(result, 
		      (ATerm)ATmakeAppl(e,translate_term(cond,vars),
					translate_term(lhs,vars),
					translate_term(rhs,vars)));
    }
  }
  return result;
}

ATermList check_and_translate_strategy(ATermList rules, ATermList strategy, Symbol n) {
  /* check for fullness (1a, 1b) and in-time (2)
   * translate strategy to internal format, 
   * also the order will be reversed.
   */
  ATermList l=NULL;
  int i;
  
  /* 1a: check if strategy is full w.r.t. arity */
  /* NOTE: THIS TEST IS NEEDED FOR CORRECT REWRITE RESULTS */
  
  for (i=1; i<=ATgetArity(n); i++)
    if (ATindexOf(strategy,(ATerm)ATmakeInt(i),0)==-1)
      ATerror("Annotation of '%s' is not full (argument '%d' is missing)\n",
	      ATgetName(n),i);
  
  /* 1b: check if strategy is full w.r.t. rules */
  for (l=rules; !ATisEmpty(l); l=ATgetNext(l)) 
    if (ATindexOf(strategy,ATgetFirst(l),0)==-1)
      ATerror("Annotation of %s is not full (rewrite rule '%s' missing)\n",
	      ATgetName(n),ATgetName(ATgetSymbol(ATgetFirst(l))));
  
  strategy = translate_strategy(strategy);
  
  /* 2: check for in-time */
  { 
    ATermList args = ATmakeList0();
    for (l=strategy; !ATisEmpty(l); l=ATgetNext(l)) {
      ATerm annotation = ATgetFirst(l);
      if (ATmatch(annotation,"<int>",NULL)) /* accumulate normalized arguments */
	args = ATinsert(args,annotation);
      else {
	ATermList needs = needed(annotation);
	for (;!ATisEmpty(needs);needs=ATgetNext(needs)) {
	  ATerm arg = ATgetFirst(needs);
	  if (ATindexOf(args,arg,0)==-1)
	    ATerror("Strategy for '%s' not in-time " 
                    "(arg '%d' needed earlier)\n",
		    ATgetName(n),ATgetInt((ATermInt)arg)+1);
	}
      }
    }
  }
  return strategy;
}

/* PART III c: Initialization */

static ATermList *rule_table;  
/* to store the rewrite rules during initialization */

static int match_depth(ATerm lhs) {
  /* max_depth(c) = 1
   *  max_depth(f(t1,..tn)) = arity(f) + max match_depth(ti)
   */
  Symbol n = ATgetArity(ATgetSymbol(lhs));
  int i,max=1;
  for (i=0; i<n; i++) {
    int arg = match_depth(ATgetArgument(lhs,i));
    if (arg > max) max=arg;
  }
  return max + n;
}

static void distribute_rules(ATermList trs) {
  /* puts rules from trs in rule_table, indexed by top symbol of lhs.
   * Also defines Max_Match_Depth and Max_Vars
   * Note: the rules are distributed in REVERSE order
   */
  Symbol n;
  int i;
  ATerm lhs=NULL, rule=NULL;
  Max_Match_Depth = 0;
  while (!ATisEmpty(trs)) {
    rule = ATgetFirst(trs);
    trs = ATgetNext(trs);
    if (ATgetArity(ATgetSymbol(rule))==4)
      lhs = ATgetArgument(rule,2);
    else
      lhs = ATgetArgument(rule,1);
    n = ATgetSymbol(lhs);
    if (n>=SYMTABLE) 
      ATerror("Symbol index too high (%d > %d)\n",n,SYMTABLE);
    rule_table[n] = ATinsert(rule_table[n],rule);
    i = match_depth(lhs);
    if (i>Max_Match_Depth) Max_Match_Depth=i;
    i = ATgetLength(ATgetArgument(rule,0));
    if (i>Max_Vars) Max_Vars = i;
  }
}

static Symbol fun2symbol(ATerm t) {
  /* converts term f(3) to symbol f(,,) */

  Symbol i=ATgetSymbol(t);
  i = ATmakeSymbol(ATgetName(i),
		   ATgetInt((ATermInt)ATgetArgument(t,0)),
		   ATisQuoted(i));
  if (i>=SYMTABLE)
    ATerror("Symbol index too high (%d > %d)\n",i,SYMTABLE);
  return i;
}

static ATermList funs2symbols(ATermList funs) {
  /* transforms list of funs in user format to list of funs in internal format */
  ATerm t=NULL;
  int i;
  if (ATisEmpty(funs)) return funs;
  t = ATgetFirst(funs);
  i = fun2symbol(t);
  return ATinsert(funs2symbols(ATgetNext(funs)),
		  (ATerm)ATmakeInt(i));
}

static ATermList distribute_strategy(ATermList funs, ATermList strategy) {
  /* Puts the strategy annotations in user format in strategy_table.
   * funs should be a list of funs in user format, i.e. [f(3),g(2), ..]
   * returns a list of function symbols that have a user strategy.
   * i.e.  f(3) -->  integer representation of f(,,)
   */
  
  ATermList result=ATmakeList0();

  /* first distribute  */
  for ( ; !ATisEmpty(strategy) ; strategy=ATgetNext(strategy)) {
    ATerm s = ATgetFirst(strategy);
    ATermList l=NULL;
    char found=0;
    for (l=funs ; !ATisEmpty(l); l=ATgetNext(l)) {
      Symbol g = ATgetSymbol(ATgetFirst(l));
      if (g == ATgetSymbol(s)) {
	Symbol f = fun2symbol(ATgetFirst(l));
	ATerm  ft = (ATerm)ATmakeInt(f);

	if (ATindexOf(result,ft,0)>=0)
	  ATerror("More than one annotation for symbol '%s'\n",ATgetName(f));

	ATprotectSymbol(f);
	strategy_table[f] = (ATermList)s;
	result = ATinsert(result,ft);
	found=1;
	break;
      }
    }
    if (!found) ATerror("annotation for unknown function symbol '%s'\n",
			ATgetName(ATgetSymbol(s)));
  }
  return result;
}

static void decode_user_strategy(ATermList funs) {
  /* funs is the list of symbols that have a user strategy */

  for (; !ATisEmpty(funs);funs=ATgetNext(funs)) {
    Symbol f = ATgetInt((ATermInt)ATgetFirst(funs));
    ATermList strategy = (ATermList)ATgetArgument(strategy_table[f],0);
    ATermList rules = rule_table[f];
    ATermList frules=ATempty;
    
    while (!ATisEmpty(strategy)) {
      ATerm annotation = ATgetFirst(strategy);
      ATermList k=rules;
      char found=0;
      int i;
      if (ATmatch(annotation,"<int>",&i)) {
	if (i>ATgetArity(f))
	  ATerror("Strategy annotation for '%s' exceeds arity\n",ATgetName(f));
	frules= ATinsert(frules,annotation);
	found=1;
      }
      while (!found && !ATisEmpty(k)) {
	ATerm rule = ATgetFirst(k);
	if (ATgetSymbol(rule) ==
	    ATmakeSymbol(ATgetName(ATgetSymbol(annotation)),
			 3,ATfalse)) {
	  frules = ATinsert(frules, rule);
	  found=1;
	}
	else
	  k=ATgetNext(k);
      }
      if (!found)
	ATerror("Strategy annotation for '%s' refers to wrong rule '%s'\n",
		ATgetName(f),ATgetName(ATgetSymbol(annotation)));
      strategy=ATgetNext(strategy);
    }
    /* NOTE: now frules is in the reversed order */
    frules = check_and_translate_strategy(rules,frules,f);
    strategy_table[f] = frules;
  }
}

static void default_strategy(ATermList defined,char plan) {
  while (!ATisEmpty(defined)) {
    int n = ATgetInt((ATermInt)ATgetFirst(defined));
    defined = ATgetNext(defined);
    if (!strategy_table[n]) {
      ATermList rules = translate_strategy(rule_table[n]);
      switch (plan) {
      case INNERMOST:
	strategy_table[n] = innermost(rules,ATgetArity(n));
	break;
      case JUSTINTIME:
	strategy_table[n] = justintime(rules,ATgetArity(n));
	break;
      }
    }
    /* ATfprintf(stderr,"Strategy for %s: %t\n", ATgetName(n),strategy_table[n]); */
  }
}

void JIT_cond_init(ATermList funs, ATermList rules, ATermList strategy,
		   ATerm True_value, int default_strat, char withhash) {
  /* Initialize JIT rewriter with 
   * - signature         e.g. [f(1),g(3)]
   * - rules             e.g. [alpha([x,y],g(x,y,y),f(y))]
   * - strategy          e.g. [ g([2,3,alpha,1]) ]
   * - true_value        e.g. MCRLterm_true for conditional rewriting, or NULL for normal rewriting
   * - default strategy  e.g. JUSTINTIME, or INNERMOST
   * - withhash          e.g. 0 (false) or 1 (true)
   */
  ATermList stratfuns=NULL,l=NULL,funsymbols=NULL;
  int i;
  static ATbool first =  ATtrue;

  hash = withhash;

  if (first) { /* on first call to JIT_init: allocate global arrays */
    normal = ATmakeAFun("normal",1,ATfalse);
    ATprotectSymbol(normal);
    ATprotect(&jitTRUE);
    e = ATmakeAFun("e",3,ATfalse);
    ATprotectSymbol(e);
    Var = ATmakeAFun("Var",1,ATfalse);
    ATprotectSymbol(Var);
    strategy_table = calloc(SYMTABLE,sizeof(ATerm));
    ATprotectArray((ATerm*)strategy_table,SYMTABLE);
    subs_table = calloc(SYMTABLE,sizeof(ATerm));
    ATprotectArray(subs_table,SYMTABLE);
    binding = calloc(1,sizeof(ATerm)); /* resized when Max_Vars known */
    ATprotectArray(binding, 1);
    filled = calloc(1,sizeof(int));    /* resized when Max_Vars known */
    if (hash) normalized = ATtableCreate(1024,60);
    first = ATfalse; 
  }
  else { /* on reinitialization: reset global tables */
    if (hash) ATtableReset(normalized);
    memset(strategy_table, 0, sizeof(ATerm)*SYMTABLE);
    memset(subs_table, 0, sizeof(ATerm)*SYMTABLE);
  }     

  if (True_value) 
    jitTRUE = True_value;
  else { /* introduce new constant Tjitty */
    jitTRUE = ATmake("Tjitty");
    funs = (ATermList)ATmake("[Tjitty(0),<list>]",funs);
  }

  init_substitution();

  rule_table = calloc(SYMTABLE,sizeof(ATerm));
  ATprotectArray((ATerm*)rule_table,SYMTABLE);
  
  funsymbols=l=funs2symbols(funs);
  
  while (ATmatch((ATerm)l,"[<int>,<list>]",&i,&l)) {
    rule_table[i] = ATempty;
  }
  
  distribute_rules(rules);
  /* now Max_Match_Depth and Max_Vars are defined */

  ATunprotectArray(binding);
  binding = (ATerm*)realloc(binding,Max_Vars*sizeof(ATerm));
  filled  = (int*)realloc(filled,Max_Vars*sizeof(int));
  here=0;
  memset(binding, 0, Max_Vars*sizeof(ATerm));
  ATprotectArray(binding,Max_Vars);
  
  stratfuns = distribute_strategy(funs,strategy);
  
  decode_user_strategy(stratfuns);
  
  default_strategy(funsymbols,default_strat);
  
  ATunprotectArray((ATerm*)rule_table);
  free(rule_table);
  
  ATwarning("JITty %sRewriter initialised %s hashing (strategy %s)%s",
            (True_value ? "conditional " : ""),
	    (hash ? "with" : "without"),
	    (default_strat==INNERMOST ? "innermost" : "strictleft"),
            (limit ? " (limited)" : ""));
}

void JIT_init(ATermList funs, ATermList rules, ATermList strategy,
	      int default_strat, char withhash) {
  JIT_cond_init(funs,rules,strategy,NULL,default_strat,withhash);
}

void JITsetVerbose(void) {verbose=1;}
void JITsetLimit(int n) {limit=n;}
