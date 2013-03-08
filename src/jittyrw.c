/* jittyrw.c : This implements the mcrl interface of the jitty rewriter.
 *
 * There are three parts:
 *  I : Convert 2nd generation LPO format to rewriter format
 *  II: Implement mCRL tool set interface functions
 *  III: Provide TASK array with function pointers 
 *
 * Actually, two rewriter TASKS are provided:
 * - INNERMOSTtasks
 * - STRICTLEFTtasks
 * NOTE: STRICTLEFT is the old name for JUSTINTIME 
 */


#include "jitty.h"
#include "mcrl.h"

static char conditional = 0;
static char statistics = 0;
static char verbose = 0;

/* PART I:  convert 2nd generation LPO format to rewriter format */

static ATerm sig(ATerm t) {
  char* name;
  ATermList sorts;

  ATmatch(t,"f(<str>,<term>,<term>)",&name,&sorts,NULL);
  return ATmake("<str(<int>)>",name,ATgetLength(sorts));
}

static ATermList siglist(ATermList s) {
  ATerm t;
  if (ATisEmpty(s)) return s;
  ATmatch((ATerm)s,"[<term>,<list>])",&t,&s);
  return ATinsert(siglist(s),sig(t));
}

static ATermList signature(ATerm funcs, ATerm maps) {
  return ATconcat(siglist((ATermList)funcs),siglist((ATermList)maps));
}

static ATermList Vars(ATermList t) {
  ATerm v;
  if (ATisEmpty(t)) return t;
  ATmatch((ATerm)t,"[v(<term>,<term>),<list>]",&v,NULL,&t);
  return ATinsert(Vars(t),v);
}

static char check_vars(ATermList vars, ATerm lhs, ATerm rhs) {
  return 1; /* todo: check if vars rhs occur in lhs */
}

static ATermList some_rules(ATerm t) {
  ATermList vars;
  ATerm lhs,rhs;
  ATmatch(t,"e(<term>,<term>,<term>)",&vars,&lhs,&rhs);
  if (!check_vars(vars,lhs,rhs)) {
    ATwarning("rhs introduces variables: %t=t\n",
	      MCRLprint(lhs),MCRLprint(rhs));
    return ATempty;
  }
  if (conditional && 
      MCRLputIfFunction((ATerm)ATmakeAppl0(MCRLgetSort(lhs)),NULL)
      ==ATgetSymbol(rhs)) {
    ATerm cond = ATgetArgument(rhs,0);
    ATerm rhs1 = ATgetArgument(rhs,1);
    ATerm rhs2 = ATgetArgument(rhs,2);
    ATermList result = ATempty;
    if (lhs != rhs1) {
      if (verbose)
	ATwarning("cond.rule: %t ==> %t = %t",
		  MCRLprint(cond),MCRLprint(lhs),MCRLprint(rhs1));
      result = ATinsert(result,ATmake("e(<term>,<term>,<term>,<term>)",
				      Vars(vars),cond,lhs,rhs1));
    }
    if (lhs != rhs2) {
      cond = (ATerm)ATmakeAppl1(MCRLsym_not,cond);
      if (verbose)
	ATwarning("cond.rule: %t ==> %t = %t",
		  MCRLprint(cond),MCRLprint(lhs),MCRLprint(rhs2));
      result = ATinsert(result,ATmake("e(<term>,<term>,<term>,<term>)",
				      Vars(vars),cond,lhs,rhs2));
    }
    return result;
  }
  else 
    return (ATermList)ATmake("[e(<term>,<term>,<term>)]",
			     Vars(vars),lhs,rhs);
}

static ATermList rules(ATermList l) {
  ATerm t;
  if (ATisEmpty(l)) return (ATermList)l;
  ATmatch((ATerm)l,"[<term>,<list>]",&t,&l);
  return ATconcat(some_rules(t),rules(l));
}

static void get_data(ATerm t,ATerm* funcs, ATerm* maps, ATerm* rules) {
  if (!ATmatch(t,"d(s(<term>,<term>,<term>),<term>)",
	       NULL,funcs,maps,rules))
    ATerror("datatype d(s(_,funcs,maps),EQNS) expected\n");
}


/* PART II: Implement mCRL tool set interface functions */

static int plan = JUSTINTIME;
static ATbool hash = ATtrue; 

static void RWsetArguments(int *argc, char ***argv) {
     int i, j=0;
     char **newargv = (char**) calloc(*argc + 1, sizeof(char*));

     if (!newargv) ATerror("Cannot allocate array argv");
     newargv[j++] = (*argv) [0];
     for(i=1;i<*argc;i++) {
       if (!strcmp((*argv)[i],"-no-hash")) {
	 hash = ATfalse;
	 continue;
       }
       if (!strcmp((*argv)[i],"-hash")) {
	 hash = ATtrue;
	 continue;
       }
       if (!strcmp((*argv)[i],"-conditional")) {
	 conditional = 1;
	 continue;
       }
       if (!strcmp((*argv)[i],"-rw-verbose")) {
	 verbose = 1;
	 JITsetVerbose();
	 continue;
       }
       if (!strcmp((*argv)[i],"-rw-statistics")) {
	 statistics = 1;
	 continue;
       }
       if (!strcmp((*argv)[i],"-rw-limit")) {
	 if ((++i < *argc) && strncmp((*argv)[i],"-",1)) {
	   JITsetLimit(atoi((*argv)[i]));
	   continue;
	 }
	 else ATerror("-rw-limit needs argument");
       }
       if (!strcmp((*argv)[i],"-strictleft")) {
	 plan = JUSTINTIME;
	 continue;
       }
       if (!strcmp((*argv)[i],"-innermost")) {
	 plan = INNERMOST;
	 continue;
       }
       newargv[j++] = (*argv)[i];
     }
     *argc = j;  *argv = newargv;
}

static ATbool RWinitialize(ATerm datatype) {
  ATerm funcs, maps, equations;
  get_data(datatype,&funcs,&maps,&equations);
  if (conditional)
    JIT_cond_init(signature(funcs,maps),rules((ATermList)equations),
	     ATempty,MCRLterm_true,plan,hash);
  else
    JIT_init(signature(funcs,maps),rules((ATermList)equations),
	     ATempty,plan,hash);
  if (statistics) atexit(RWstatistics);
  return 1;
}

static ATerm RWrewrite(ATerm t) {
  ATerm result;
  /* ATfprintf(stderr,"Rewrite: %t\n",MCRLprint(t)); */

  result = JIT_normalize(t);
  
  /* ATfprintf(stderr,"= %t\n",MCRLprint(result)); */
  return result;
}

static void RWassignVariable(AFun var, ATerm t, ATerm tsort, int lev) {
  /*  ATfprintf(stderr,"Level: %d; Assign %s := %t (level: %d)\n",
      JIT_level(),ATgetName(var),t,lev); */

  if (lev==JIT_level()+1)
    JIT_enter();
  else if (lev+1 == JIT_level())
    JIT_leave();

  if (lev != JIT_level())
    ATerror("RWassignVariable at unexpected level %d",lev);
  
  JIT_assign(var,t);
}

static void RWresetVariables(int lev) {
  /* ATfprintf(stderr,"Reset: %d\n",level); */
  //  fprintf(stderr,"Level: %d; Reset  at level: %d\n",JIT_level(),lev);
  if (lev==JIT_level())
    JIT_leave();
  else if (lev==JIT_level()+1)
    ;
  else if (lev+1==JIT_level())
    JIT_leave();
  else
    ATerror("RWresetVariables at unexpected level %d",lev);
}

static ATermList RWrewriteList(ATermList ts) {
  ATermList newts = ATmakeList0();
  for (;!ATisEmpty(ts);ts=ATgetNext(ts)) {
    ATerm t = ATgetFirst(ts);
    if (!(t = RWrewrite(t))) return NULL;
    newts = ATinsert(newts,t);
  }
  return ATreverse(newts);
}

static void RWdeclareVariables(ATermList vars) {
  /* ATfprintf(stderr,"Declare: %t\n",vars); */
}

static ATerm RWgetAssignedVariable(Symbol var) {
  return JIT_normalize((ATerm)ATmakeAppl0(var));
}

static void RWflush() {
  JIT_flush();
}


static void RWhelp(void) {
  Pr("Extra Options of JITty are:");
  Pr("\tStrategies:");
  Pr("\t\t-innermost:   Innermost rewriting");
  Pr("\t\t-strictleft:  Strictleft rewriting (default)");
  Pr("\tHash options:");
  Pr("\t\t-hash:        Use hashing during rewriting (default)"); 
  Pr("\t\t-no-hash:     No hashing during rewriting");
  Pr("\tVariations:");
  Pr("\t\t-conditional:  view rule l->if(c,r1,r2) as conditional");
  Pr("\t\t-rw-limit <n>: maximal n rewrite steps per term");
  Pr("\tMessages:");
  Pr("\t\t-rw-verbose:    print some rewrite messages");
  Pr("\t\t-rw-statistics: print some rewrite statistics");
}

/*  PART III: Provide TASK array with function pointers */


#include "tasks.h"

TASKS JITTYtasks ={RWsetArguments, RWinitialize, RWassignVariable, 
		   RWgetAssignedVariable, RWresetVariables, RWdeclareVariables,
		   RWrewrite, RWrewriteList, NULL, RWflush, RWhelp};
