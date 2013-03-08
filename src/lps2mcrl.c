/* Author: Jaco van de Pol, FMT, Universiteit Twente, 3 november 2008
 * Nice feature: doesn't need mcrl2, nor muCRL toolset; just ATerms.
 * Issues: 
 * - higher-order sorts are not supported (excludes whr, bags, sets)
 * - timed specifications are not supported
 * - multi-actions are not supported
 * - overlapping name spaces are not supported (maps/vars/actions should be disjoint)
 */

/* $Id: $ */

#include <stdlib.h>
#include <string.h>
#include "aterm2.h"

static char str[1024];

void at2underscore(char* str) {
  int i=0;
  while (str[i]!=0) {
    if (str[i]=='@') str[i]='_';
    i++;
  }
}

void mcrl_id(ATerm sym, ATerm sort) {
  sprintf(str,"%s",ATgetName(ATgetSymbol(sym)));
  at2underscore(str);
  if (!strcmp(str,"true"))
    printf("T");
  else if (!strcmp(str,"false"))
    printf("F");
  else if (!strcmp(str,"=="))
    printf("eq");
  else if (!strcmp(str,"!="))
    printf("neq");
  else if (!strcmp(str,"!"))
    printf("not");
  else if (!strcmp(str,"&&"))
    printf("and");
  else if (!strcmp(str,"||"))
    printf("or");
  else if (!strcmp(str,"=>"))
    printf("implies");
  else if (!strcmp(str,"<="))
    printf("le");
  else if (!strcmp(str,"<"))
    printf("lt");
  else if (!strcmp(str,">="))
    printf("ge");
  else if (!strcmp(str,">"))
    printf("gt");
  else if (!strcmp(str,"+"))
    printf("plus");
  else if (!strcmp(str,"*"))
    printf("times");
  else if (!strcmp(str,"-"))
    printf("minus");
  else if (!strcmp(str,"[]")) {
    if (ATmatch(sort,"SortId(<term>)",&sort)) {
      printf("empty_list_"); 
      mcrl_id(sort,NULL);
    }
    else
      ATerror("Sorry, list with higher-order sorts are not supported: %t.\n",sort);
  }
  else if (!strcmp(str,"{}")) {
    if (ATmatch(sort,"SortId(<term>)",&sort)) {
      printf("empty_set_"); 
      mcrl_id(sort,NULL);
    }
    else
      ATerror("Sorry, set with higher-order sorts are not supported: %t.\n",sort);
  }
  else if (!strcmp(str,"|>"))
    printf("cons");
  else if (!strcmp(str,"<|"))
    printf("snoc");
  else if (!strcmp(str,"++"))
    printf("append");
  else if (!strcmp(str,"."))
    printf("at");
  else if (!strcmp(str,"#"))
    printf("length");
  else
    printf("%s",str);
}

void mcrl_sorts(ATerm sorts, char* str) {
  //prints a list of sorts, separated by str
  ATerm sort;
  while (ATmatch(sorts,"[SortId(<term>),<list>]",&sort,&sorts)) {
    mcrl_id(sort,NULL);
    if (!ATisEmpty(sorts)) printf("%s",str);
  }
}

char higher_order(ATerm sort) {
  // check if sort is first-order: either base type, or all arguments of base type
  ATerm arg, args;
  if (ATmatch(sort,"SortId(<term>)",NULL)) return 0;
  ATmatch(sort,"SortArrow(<term>,<term>)",&args,&sort);
  if (!ATmatch(sort,"SortId(<term>)",NULL)) return 1;
  while (ATmatch(args,"[<term>,<list>]",&arg,&args))
    if (!ATmatch(arg,"SortId(<term>)",NULL)) return 1;
  return 0;
}

char first_order_rule(ATerm vars, ATerm lhs) {
  // check if all declarations in var have base sort and lhs is first_order
  if (ATmatch(lhs,"DataAppl(DataAppl(<term>,<term>),<term>)",NULL,NULL,NULL))
    return 0;
  while (ATmatch(vars,"[DataVarId(<term>,SortId(<term>)),<list>]",NULL,NULL,&vars));
  return ATisEmpty(vars);
}



void mcrl_decls(ATerm decls) {
  // useful for funcs, maps, but also don't care declarations
  ATerm name, sort, args;
  while (ATmatch(decls,"[OpId(<term>,<term>),<list>]",&name,&sort,&decls)
	 || ATmatch(decls,"[DataVarId(<term>,<term>),<list>]",&name,&sort,&decls)) 
  if (!higher_order(sort)) {
    printf("  ");
    mcrl_id(name,sort);
    printf(": ");
    args=(ATerm)ATempty;
    ATmatch(sort,"SortId(<term>)",&sort)
      || ATmatch(sort,"SortArrow(<term>,SortId(<term>))", &args,&sort);
    mcrl_sorts(args," # ");
    printf(" -> ");
    mcrl_id(sort,NULL);
    printf("\n");
  }
}

void mcrl_vars(ATerm vars,char* str) {
  // print sorted variable declaration, separated by str
  ATerm var,sort;
  while (ATmatch(vars,"[DataVarId(<term>,SortId(<term>)),<list>]",&var,&sort,&vars)) {
    printf("  ");
    mcrl_id(var,NULL);
    printf(": ");
    mcrl_id(sort,NULL);
    if (!ATisEmpty(vars))
      printf("%s",str);
  }
  if (!ATisEmpty(vars)) 
    fprintf(stderr,"Sorry, higher-order variables are not supported\n");
}

void mcrl_term(ATerm term);

void mcrl_terms(ATerm terms) {
  ATerm term;
  if (!ATisEmpty(terms)) {
    printf("(");
    while (ATmatch(terms,"[<term>,<list>]",&term,&terms)) {
      mcrl_term(term);
      if (!ATisEmpty(terms)) printf(",");
    }
    printf(")");
  }
}

void mcrl_term(ATerm term) {
  ATerm terms,sort;
  if (ATmatch(term,"OpId(<term>,<term>)",&term,&sort)) mcrl_id(term,sort);
  else if (ATmatch(term,"DataVarId(<term>,<term>)",&term,&sort)) mcrl_id(term,sort);
  else if (ATmatch(term,"DataAppl(OpId(<term>,<term>),<term>)",&term,&sort,&terms)) {
    mcrl_id(term,sort);
    mcrl_terms(terms);
  }
}

ATerm rew_exception(ATerm rew) {
  // some higher-order rules should be turned into first order rules.

  // Pos2Nat -> @cNat   should be   Pos2Nat(p) -> _cNat(p)
  if (ATmatch(rew,"DataEqn([],Nil,\
        OpId(\"Pos2Nat\",SortArrow([SortId(\"Pos\")],SortId(\"Nat\"))),\
        OpId(\"@cNat\",SortArrow([SortId(\"Pos\")],SortId(\"Nat\"))))"))
    return ATmake("DataEqn(\
        [DataVarId(\"p\",SortId(\"Pos\"))],Nil,\
        DataAppl(OpId(\"Pos2Nat\",SortArrow([SortId(\"Pos\")],SortId(\"Nat\"))),\
                 [DataVarId(\"p\",SortId(\"Pos\"))]),\
        DataAppl(OpId(\"@cNat\",SortArrow([SortId(\"Pos\")],SortId(\"Nat\"))),\
                 [DataVarId(\"p\",SortId(\"Pos\"))]))");

  // Nat2Int -> cInt   should be   Nat2Int(n) -> cInt(n)
  else if (ATmatch(rew,"DataEqn([],Nil,\
        OpId(\"Nat2Int\",SortArrow([SortId(\"Nat\")],SortId(\"Int\"))),\
        OpId(\"@cInt\",SortArrow([SortId(\"Nat\")],SortId(\"Int\"))))"))
    return ATmake("DataEqn(\
        [DataVarId(\"n\",SortId(\"Nat\"))],Nil,\
        DataAppl(OpId(\"Nat2Int\",SortArrow([SortId(\"Nat\")],SortId(\"Int\"))),\
                 [DataVarId(\"n\",SortId(\"Nat\"))]),\
        DataAppl(OpId(\"@cInt\",SortArrow([SortId(\"Nat\")],SortId(\"Int\"))),\
                 [DataVarId(\"n\",SortId(\"Nat\"))]))");

  // Int2Real -> cReal   should be   Int2Real(x) -> cReal(x)
  else if (ATmatch(rew,"DataEqn([],Nil,\
        OpId(\"Int2Real\",SortArrow([SortId(\"Int\")],SortId(\"Real\"))),\
        OpId(\"@cReal\",SortArrow([SortId(\"Int\")],SortId(\"Real\"))))"))
    return ATmake("DataEqn(\
        [DataVarId(\"x\",SortId(\"Int\"))],Nil,\
        DataAppl(OpId(\"Int2Real\",SortArrow([SortId(\"Int\")],SortId(\"Real\"))),\
                 [DataVarId(\"x\",SortId(\"Int\"))]),\
        DataAppl(OpId(\"@cReal\",SortArrow([SortId(\"Int\")],SortId(\"Real\"))),\
                 [DataVarId(\"x\",SortId(\"Int\"))]))");

  else return rew;
}

void mcrl_rews(ATerm eqns) {
  ATerm eqn,vars,cond,lhs,rhs;
  while (ATmatch(eqns,"[<term>,<list>]",&eqn,&eqns)) {
    eqn = rew_exception(eqn);
    ATmatch(eqn,"DataEqn(<term>,<term>,<term>,<term>)",&vars,&cond,&lhs,&rhs);
    if (first_order_rule(vars,lhs)) {
      if (!ATisEmpty(vars)) {
	printf("\nvar\n");
	mcrl_vars(vars,"\n");
      }
      printf("\nrew\n");
      printf("  ");
      if (cond==ATmake("Nil")) {
	mcrl_term(lhs);
	printf("\n= ");
	mcrl_term(rhs);
	printf("\n");
      }
      else {
	mcrl_term(lhs);
	printf("\n= if(");
	mcrl_term(cond);
	printf(",");
	mcrl_term(rhs);
	printf(",");
	mcrl_term(lhs);
	printf(")\n\n");
      }
    }
  }
}

void mcrl_actdecls(ATerm acts) {
  ATerm act,sorts;
  if (!ATisEmpty(acts)) {
    printf("\nact\n");
    while (ATmatch(acts,"[ActId(<term>,<term>),<list>]",&act,&sorts,&acts)) {
      printf("  ");
      mcrl_id(act,NULL);
      if (!ATisEmpty(sorts)) printf(": ");
      mcrl_sorts(sorts," # ");
      printf("\n");
    }
    printf("\n");
  }
}

void mcrl_pars(ATerm pars) {
  printf("\nproc X");
  if (!ATisEmpty(pars)) {
    printf("(\n");
    mcrl_vars(pars,",\n");
    printf("\n)");
  }
  printf(" =\n\n  ");
}

void mcrl_sumvars(ATerm vars) {
  ATerm var, sort;
  if (!ATisEmpty(vars)) {
    while (ATmatch(vars,"[DataVarId(<term>,SortId(<term>)),<list>]",&var,&sort,&vars)) {
      printf("sum(");
      mcrl_id(var,NULL);
      printf(":");
      mcrl_id(sort,NULL);
      printf(",");
    }
    printf("\n  ");
  }
}

void mcrl_cond(ATerm cond) {
  printf("<| ");
  mcrl_term(cond);
  printf(" |> delta");
}

ATerm act_report(ATerm act) {
  ATermList out=ATempty;
  ATerm name,acts;
  ATmatch(act,"MultAct(<term>)",&acts);
  while(ATmatch(acts,"[Action(ActId(<term>,<term>),<term>),<list>]",
		&name,NULL,NULL,&acts))
    out=ATinsert(out,name);
  return (ATerm)ATreverse(out);
}

void mcrl_act(ATerm act) {
  ATerm args;
  if (ATmatch(act,"MultAct([Action(ActId(<term>,<term>),<term>)])",&act,NULL,&args)) {
    mcrl_id(act,NULL);
    mcrl_terms(args);
    printf(".\n");
  }
  else  if (ATmatch(act,"MultAct([])")) {
    printf("tau.\n");
  }
  else 
    ATerror("Sorry, multi-actions are not supported: %t\n",act_report(act));
}

void mcrl_next(ATerm pars, ATerm nexts) {
  ATerm par,next,term;
  printf("  X");
  
  if (!ATisEmpty(pars)) {
    printf("(");
    next=ATmake("Nil");
    ATmatch(nexts,"[DataVarIdInit(DataVarId(<term>,<term>),<term>),<list>]",
	    &next,NULL,&term,&nexts);
    while (ATmatch(pars,"[DataVarId(<term>,SortId(<term>)),<list>]",&par,NULL,&pars)) {
      if (next==par) {
	mcrl_term(term);
	ATmatch(nexts,"[DataVarIdInit(DataVarId(<term>,<term>),<term>),<list>]",
		&next,NULL,&term,&nexts);
      }    
      else
	mcrl_id(par,NULL);
      if (!ATisEmpty(pars)) printf(",");
    }
    printf(")");
  }
  printf("\n");
}

void mcrl_sums(ATerm pars, ATerm sums) {
  ATerm vars,cond,act,next;
  int i;
  while (ATmatch(sums,"[LinearProcessSummand(<term>,<term>,<term>,Nil,<term>),<list>]",
		 &vars,&cond,&act,&next,&sums)) {
    mcrl_sumvars(vars);
    if (act==ATmake("Delta"))
      printf("delta\n");
    else {
      mcrl_act(act);
      mcrl_next(pars,next);
    }
    mcrl_cond(cond);
    for (i=0;i<ATgetLength(vars);i++) printf(")"); // close sum brackets
    if (!ATisEmpty(sums)) printf("\n\n+ ");
  }
  printf("\n");
  if (!ATisEmpty(sums)) ATerror("Sorry, timed specification not supported.\n");
}

void mcrl_dontcares(ATerm dontcares) {
  if (!ATisEmpty(dontcares)) {
    printf("\nmap\n");
    mcrl_decls(dontcares);
  }
}

void lps2mcrl(ATerm t) {
  ATerm data,acts,dontcares1,pars,sums,dontcares2,inits,sorts,cons,maps,eqns;

  if (!ATmatch(t,"LinProcSpec(<term>,ActSpec(<term>),\
                  LinearProcess(<term>,<term>,<term>),LinearProcessInit(<term>,<term>))",
	       &data,&acts,&dontcares1,&pars,&sums,&dontcares2,&inits))
    ATerror("Sorry, mcrl2 specification not recognized\n");

  if (!ATmatch(data,"DataSpec(SortSpec(<term>),ConsSpec(<term>),\
                     MapSpec(<term>),DataEqnSpec(<term>))",
	       &sorts,&cons,&maps,&eqns))
    ATerror("Sorry, mcrl2 data specification not recognized\n");


  printf("sort\n  ");
  mcrl_sorts(sorts,"\n  ");
  printf("\n\nfunc\n");
  mcrl_decls(cons);
  printf("\nmap\n");
  mcrl_decls(maps);
  mcrl_rews(eqns);
  mcrl_dontcares(dontcares1);
  mcrl_actdecls(acts);
  mcrl_pars(pars);
  mcrl_sums(pars,sums);
  mcrl_dontcares(dontcares2);
  printf("\ninit ");
  mcrl_next(pars,inits);
}


int main(int argc,char* argv[]) {
  ATerm bottomofstack;
  ATerm t;

  ATinit(argc,argv,&bottomofstack);
  fprintf(stderr,"mcrl2 in lps-format to muCRL specification (stdin -> stdout)\n");
  t = ATreadFromFile(stdin);
  //ATfprintf(stderr,"%t\n",t);
  lps2mcrl(t);
  exit(0);
}
