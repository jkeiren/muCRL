/* $Id: sumelm.c,v 1.3 2005/04/21 13:16:03 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <string.h>
#include "rw.h"

static char *who = "Sumelm";
static ATbool nosingleton = ATfalse, monitor = ATfalse; 
static int cnt = 0, skipped = 0;
#define TABLESIZE 20
static ATermTable db_sort_constant, db_hash;
static ATbool verbose = ATfalse;
static int vSmnds=0, pSmnds=0, nSmnds=0;

static void WarningHandler(const char *format, va_list args) {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }
     
static void ErrorHandler(const char *format, va_list args)
     {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     exit(-1);
     }
    
static void helpmsg(ATbool all) 
    {
    Pr("Usage: sumelm [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\tyields this message");
    Pr("-help-all:\tyields all help information");
    Pr("-version:\tget the version number of this release");
    Pr("-monitor:\tdisplays progressing information");
    Pr("-nosingleton:\tno extra search for variables which");
    Pr("\t\thave sorts of cardinality one");  
    Pr("\t\tThese variables are candidates for substitution");
    if (all) {
       MCRLhelp();
       RWhelp();
       }   
    }

static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("Sometimes a sum variable is bound to a data term by the function \"eq\"");
    Pr("in a condition of a summand.");
    Pr("This sum variable will be eliminated. The found data term");
    Pr("will be substituted in all the occurrences of this sum variable");
    Pr("in that summand.");
    Pr("The LPO will be rewritten during the elimination of sum variables.");
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    exit(0);
    }

static void version(void)
    {
    /*
    Pr("$Id: sumelm.c,v 1.3 2005/04/21 13:16:03 bertl Exp $");
    */
    char buf[100];
    sprintf(buf, "%s: version %s", who, VERSION);
    Pr(buf);
    }
   
static void Init(void) {
    db_sort_constant = ATtableCreate(TABLESIZE,50);
    if (!db_sort_constant) ATerror("Table is not allocated");
    }
           
static ATermList MakeVars(ATermList vars, ATermList varnames) {
     ATermList result = ATempty;
     for (;!ATisEmpty(vars);vars=ATgetNext(vars))
          {ATerm var =  ATgetFirst(vars);
          if (ATindexOf(varnames, ATgetArgument((ATermAppl) var, 0),0)>=0)
              result = ATinsert(result, var);
          }
     return ATreverse(result);
     }
        
static ATermList GetVarNames(ATermList pars) {
     ATermList result = ATempty;
     for (;!ATisEmpty(pars);pars=ATgetNext(pars)) {
          ATerm par = ATgetFirst(pars);
          result = ATinsert(result, ATgetArgument((ATermAppl) par,0));
          }
     return ATreverse(result);
     }
     
static ATermList Intersection(ATermList t1s, ATermList t2s) {
     ATermList result = ATempty;
     for (;!ATisEmpty(t1s);t1s=ATgetNext(t1s)) {
          ATerm t1 = ATgetFirst(t1s);
          if (ATindexOf(t2s, t1,0)>=0) result = ATinsert(result, t1);
          }
     /* ATwarning("Intersection %t\n",result); */
     return result;
     }
     
static ATermList Union(ATermList t1s, ATermList t2s) {
     ATermList result = t2s;
     /* ATwarning("Arguments union %t %t",t1s,t2s); */ 
     for (;!ATisEmpty(t1s);t1s=ATgetNext(t1s)) {
          ATerm t1 = ATgetFirst(t1s);
          if (ATindexOf(t2s, t1,0)<0) result = ATinsert(result, t1);
          }
     return result;
     }
     
static ATermList Minus(ATermList pars1, ATermList pars2) {
     ATermList result = ATempty;
     for (;!ATisEmpty(pars1);pars1=ATgetNext(pars1)) {
          ATerm par1 = ATgetFirst(pars1);
          if (ATindexOf(pars2 , par1,0)<0) result = ATinsert(result, par1);
          }
     return ATreverse(result);
     }
     
static ATermList TestEqual(ATerm var, ATerm  cond) {
     Symbol bsym = ATgetSymbol(cond);
     ATermList result = ATempty;
     ATerm notVar = NULL;
    /* ATwarning("TestEqual var = %t cond = %t", var, cond); */ 
     if (db_hash) { 
          result = (ATermList) ATtableGet(db_hash, cond);
          if (result) return result;
          }
     notVar = (ATerm) ATmakeAppl1(MCRLsym_not, var);
     if (ATisEqual(cond, var)) return ATmakeList1(MCRLterm_true);
     if (ATisEqual(cond, notVar)) return ATmakeList1(MCRLterm_false);
     if (bsym == MCRLsym_not) return ATempty; 
     if (ATgetArity(bsym)==2 && !strncmp(ATgetName(bsym),"eq#",3)) {
     /* if (MCRLgetType(bsym)==MCRLeqfunction) { */
          if (ATisEqual(ATgetArgument((ATermAppl) cond, 0), var)) {
              /*  ATwarning("1: %t",ATmakeList1(ATgetArgument((ATermAppl) cond,
               1))); */
               return ATmakeList1(ATgetArgument((ATermAppl) cond, 1));
               }
          if (ATisEqual(ATgetArgument((ATermAppl) cond, 1), var)) {
               /* ATwarning("0: %t",ATmakeList1(ATgetArgument((ATermAppl) cond,
               0)));  */
               return ATmakeList1(ATgetArgument((ATermAppl) cond, 0));
               }
          return ATempty;     
          }
     
     if (bsym == MCRLsym_and) result = Union(
          TestEqual(var, ATgetArgument((ATermAppl) cond , 0)),
          TestEqual(var, ATgetArgument((ATermAppl) cond , 1)));
     else
     if (bsym == MCRLsym_or) result =  Intersection(
          TestEqual(var, ATgetArgument((ATermAppl) cond , 0)),
          TestEqual(var, ATgetArgument((ATermAppl) cond , 1)));
     else
     if (MCRLgetType(bsym) == MCRLcasefunction 
         && MCRLgetSortSym(bsym) == ATgetAFun(MCRLterm_bool)) {
          int n = ATgetArity(bsym), i = 0;
          /* First case Case(e,F,F,F,F,t,F,F) return {d4} */
          result = NULL;
          if (ATisEqual(var,ATgetArgument((ATermAppl) cond , 0))) {
               ATerm selector = NULL;
               ATermList selectors = MCRLgetCaseSelectors(bsym);
               for (i=1;i<n && !ATisEmpty(selectors) && 
               (ATisEqual(ATgetArgument((ATermAppl) cond , i), MCRLterm_false)
                    || !selector); i++, selectors = ATgetNext(selectors)) {
                  if (!ATisEqual(ATgetArgument((ATermAppl) cond , i), 
                       MCRLterm_false)) selector =  ATgetFirst(selectors);   
                  } 
               if (i==n && selector) result = ATmakeList1(selector);
               }
           if (result==NULL) {
               /* arg1 n arg2 ,..., argn */
               result = TestEqual(var, ATgetArgument((ATermAppl) cond , 1));
               for (i=2;!ATisEmpty(result)&& i<n;i++) {
                    ATerm arg = ATgetArgument((ATermAppl) cond , i);
                    if (!ATisEqual(arg, MCRLterm_false))
                         result = Intersection(result, TestEqual(var, arg));
                    }
               };
          }
     else return ATempty;
     if (db_hash) ATtablePut(db_hash, cond, (ATerm) result);
     /* if (!result) abort(); */ 
     return result;      
     }
          
static ATermList NotOccursInSummand(ATermList varnames, ATermList actargs, 
     ATerm procarg, ATerm cond);

     
static ATermList SelectOccurringParameters(ATermList ls, ATermList cs) {
     ATermList cs0 = Minus(ls, cs);
     /* cs subset of ls  (ls are found parameters) */     
     for (;!ATisEmpty(cs);cs=ATgetNext(cs)) {
           ATerm c = ATgetFirst(cs);
           RWassignVariable(ATgetSymbol(c), c, NULL, 1);
           }
     return cs0;     
     }
     
static ATermList CandidatesForParameterSubstitution(
     ATermList parnames, ATerm smd) {
     ATerm procarg = (ATerm) ATgetArgument((ATermAppl) smd, 3),
          cond = (ATerm) ATgetArgument((ATermAppl) smd, 4);
     ATermList vars = (ATermList) ATgetArgument((ATermAppl) smd, 0),
         actargs = (ATermList) ATgetArgument((ATermAppl) smd, 2),
     result = ATempty, notOccurredVars = NULL;
     for (;!ATisEmpty(parnames);parnames=ATgetNext(parnames)) {
          ATerm parname = ATgetFirst(parnames);
          ATermList constants = NULL;
          db_hash = ATtableCreate(20,75);
          constants = TestEqual(parname, cond);
          /*if (!ATisEmpty(constants)) 
            ATwarning("QQ constants = %t = %t %t", parname, constants, cond);
          */
          if (db_hash) {ATtableDestroy(db_hash); db_hash = NULL;}
          if (!ATisEmpty(constants)) {
               ATerm constant = ATgetFirst(constants);
   /* To prevent TestEqual(x=y and y=x) -> 
       delete (x,y);subst(y in x);subst(x in y) */
               if  (MCRLisClosedTerm(constant)) { 
                   ATerm constant = ATgetFirst(constants);
                   RWassignVariable(ATgetSymbol(parname), constant, NULL,1);
                   result = ATinsert(result, parname);
                   } 
            }
          }
     parnames = ATreverse(result);
     notOccurredVars =  NotOccursInSummand(parnames, actargs, procarg, NULL);
     /* notOccurredVar subset of parnames */
     result = SelectOccurringParameters(parnames,  notOccurredVars);
     if (ATgetLength(notOccurredVars)<ATgetLength(parnames)) {
         if (monitor)
         for (parnames=result;!ATisEmpty(parnames);
                        parnames = ATgetNext(parnames)) {
             ATwarning("Summand %d: substituted for parameter %t the term %t",
             cnt+1, ATmake("<str>", MCRLgetName(ATgetFirst(parnames))), 
                   MCRLprint(
                     RWgetAssignedVariable(ATgetAFun(ATgetFirst(parnames)))));
             }
         nSmnds++;pSmnds++;
         }
     return result;
     }
      
static void Singletons(ATermList sorts) {
     for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts)) {
          ATerm sortterm = ATgetFirst(sorts);
          ATermList constructors = MCRLgetConstructors(ATgetAFun(sortterm));
	  if (MCRLgetType(ATgetSymbol(sortterm))==MCRLsort) continue;
          if (ATgetLength(constructors)==1) {
               ATerm constructor = ATgetFirst(constructors);
               if (ATisEmpty(ATgetArguments((ATermAppl) constructor))) {
                    ATwarning("Sort %t has only constructor: %t",
                    sortterm, MCRLprint(constructor));
                    ATtablePut(db_sort_constant, sortterm, constructor);
                    }
               }
          }
     }
    
static ATermList SingletonVars(ATermList vars) {
     ATermList result = ATempty;
     for (;!ATisEmpty(vars);vars=ATgetNext(vars)) {
          ATerm var = ATgetFirst(vars),
          varname = ATgetArgument((ATermAppl)var,0),
          sort = ATgetArgument((ATermAppl)var,1),
          constant = ATtableGet(db_sort_constant, sort);
          if (constant) {
               RWassignVariable(ATgetSymbol(varname), constant, NULL,1);
               result = ATinsert(result, varname);
               }
          }
     return ATreverse(result);
     }
                                                  
static ATermList CandidatesForSumelimination(ATerm smd) {
     ATerm procarg = (ATerm) ATgetArgument((ATermAppl) smd, 3),
          cond = (ATerm) ATgetArgument((ATermAppl) smd, 4);
     ATermList vars = (ATermList) ATgetArgument((ATermAppl) smd, 0),
         actargs = (ATermList) ATgetArgument((ATermAppl) smd, 2),
     result = ATempty, remainingVars = ATempty,
     singletonVars = nosingleton?ATempty:SingletonVars(vars),
     varnames = Minus(GetVarNames(vars), singletonVars); 
     for (;!ATisEmpty(varnames);varnames=ATgetNext(varnames)) {
          ATerm varname = ATgetFirst(varnames);
          ATermList constants = NULL, previous = ATinsert(result, varname);
          db_hash = ATtableCreate(20,75);
          constants = TestEqual(varname, cond);
          if (db_hash) {ATtableDestroy(db_hash); db_hash = NULL;}
          /* Previous variables inclusive itself are not permitted to 
             occur in substitution term */
          if (!ATisEmpty(constants) && 
            ATisEqual(MCRLremainingVars(ATgetFirst(constants), previous), 
            previous)) {
               ATerm constant = ATgetFirst(constants);
               RWassignVariable(ATgetSymbol(varname), constant, NULL,1); 
               result = ATinsert(result, varname);
               } else remainingVars = ATinsert(remainingVars, varname);
          }
     /* result = ATreverse(result); */
     remainingVars = NotOccursInSummand(remainingVars, actargs, procarg, cond);
     for (varnames=result;!ATisEmpty(varnames);varnames=ATgetNext(varnames)) {
        ATerm varname = ATgetFirst(varnames);
        ATerm term = RWrewrite(RWgetAssignedVariable(ATgetAFun(varname)));
        if (monitor) ATwarning("Summand %d: substituted for variable %t the term %t",
        cnt+1, ATmake("<str>", MCRLgetName(varname)), MCRLprint(term));
        RWassignVariable(ATgetSymbol(varname), term, NULL,1);
        }
     if (monitor)    
        for (varnames = remainingVars;!ATisEmpty(varnames);
             varnames=ATgetNext(varnames))
        ATwarning(
   "Variable \"%s\" (sort %a) in the sum operator of summand %d has been deleted"
       ,MCRLgetName(ATgetFirst(varnames)), MCRLgetSort(ATgetFirst(varnames)), 
          cnt+1); 
     if (!ATisEmpty(result) || !ATisEmpty(remainingVars)) {nSmnds++;vSmnds++;}
     result = ATconcat(ATconcat(result, remainingVars), singletonVars);
     return result;
     } 

static ATermList NotOccursInSummand(ATermList varnames, ATermList actargs, 
     ATerm procarg, ATerm cond) {
     ATermList remainingVars = varnames;
     for (;!ATisEmpty(actargs) && !ATisEmpty(remainingVars);
          actargs=ATgetNext(actargs)) {
          ATerm actarg = ATgetFirst(actargs);
          remainingVars = MCRLremainingVars(actarg, remainingVars);
          }
     if (!ATisEqual(procarg, MCRLterm_terminated)) {
          ATermList terms = 
             (ATermList) ATgetArgument((ATermAppl) procarg,0); 
          for (;!ATisEmpty(remainingVars) && !ATisEmpty(terms);
               terms=ATgetNext(terms))
               {ATerm term = ATgetFirst(terms);
               remainingVars = MCRLremainingVars(term, remainingVars);
               }
          }
     if (cond && !ATisEmpty(remainingVars)) 
          remainingVars = MCRLremainingVars(cond, remainingVars);
     return remainingVars;    
     }   
    
static ATerm  MakeEq(AFun sortsym, ATerm nameterm, ATerm val) {
     ATerm result = NULL,
         sort = (ATerm) ATmakeAppl0(sortsym);
     ATbool new = ATfalse;
     AFun s = MCRLputEqFunction(sort, &new);
     /* ATwarning("QQQ MakeEqu %a %a",sortsym, s); */
     if (s) 
          {if (new && verbose) ATwarning("Map %a: added", s);}
     else {
         ATwarning("Equality function on sort %a is not declared",
                    sortsym);
         return result;
        }        
     result =
          (ATerm) ATmakeAppl2(s, nameterm, val);
     return result;
     }
     
static ATerm Equ(ATerm parName, ATerm val) {
     return MakeEq(MCRLgetSort(parName), parName, val);
     }
              
static ATerm ExtendCondition(ATerm cond, ATermList selectedPars) {
/* if (cnt == 4)
ATwarning("QQ: selectedPars %t cond %t", selectedPars, MCRLprint(cond));
*/ 
     for (;!ATisEmpty(selectedPars);selectedPars=ATgetNext(selectedPars))
        {ATerm selectedPar = ATgetFirst(selectedPars);
        ATerm val = RWgetAssignedVariable(ATgetSymbol(selectedPar));
        if (!ATisEqual(selectedPar, val)) {
           ATerm eq = Equ(selectedPar, val);
           if (!eq) continue;
           cond = (ATisEqual(cond, MCRLterm_true)? eq:
           (ATerm) ATmakeAppl2(MCRLsym_and, cond, eq));
           }
        } 
     return cond;  
     } 
        
static ATermList SubstituteConstantParametersInSums(ATermList sums, ATermList pars) {
     ATermList result = ATempty;
     ATwarning("Read %d summands", ATgetLength(sums));
     ATwarning("Number of parameters of input LPO: %d", ATgetLength(pars));
     for (cnt = 0, skipped = 0;!ATisEmpty(sums);sums=ATgetNext(sums), cnt++)
          {ATerm sum = ATgetFirst(sums),
          procarg = (ATerm) ATgetArgument((ATermAppl) sum, 3),
          cond = (ATerm) ATgetArgument((ATermAppl) sum, 4);
          ATermList vars = (ATermList) ATgetArgument((ATermAppl) sum, 0),
          varnames = GetVarNames(vars),
          acts = (ATermList) ATgetArgument((ATermAppl) sum, 2),
          selectedPars = CandidatesForParameterSubstitution(GetVarNames(pars), sum),
          selectedVars =  CandidatesForSumelimination(sum), 
          remainingVars = Minus(varnames, selectedVars);
          if (ATisEqual((cond=RWrewrite(cond)), MCRLterm_false)) {
               /* This summand will be skipped */
               RWflush(); RWresetVariables(1);
               skipped++; continue;
               }           
        /* In the "true" branch of the <| cond |> must 
          be done also substitutions in the process (action) parameters 
         */  
          /* Definition of bound process parameters */  
          acts = RWrewriteList(acts);
          if (!ATisEqual(procarg, MCRLterm_terminated)) {
             ATermList terms = 
                  (ATermList) ATgetArgument((ATermAppl) procarg,0);
             terms = RWrewriteList(terms);
             procarg = (ATerm) ATmakeAppl1(ATgetSymbol(procarg), (ATerm) terms);
             }
          cond = ExtendCondition(cond, selectedPars); 
          RWflush(); RWresetVariables(1);
          sum = (ATerm) ATmakeAppl5(
          ATgetSymbol(sum), (ATerm) MakeVars(vars, remainingVars),
             (ATerm) ATgetArgument((ATermAppl) sum, 1), (ATerm) acts, procarg, 
             cond);
        result = ATinsert(result, sum);
        /* if (monitor) ATwarning("Summand %d is updated", cnt+1); */
        }
     if (nSmnds>0) {
     ATwarning("Number of summands in which proc parameters are changed: %d",
        pSmnds);
     ATwarning("Number of summands in which sum variables are changed: %d",
        vSmnds);
     ATwarning("Number of summands which are changed: %d", nSmnds);
        }
     else ATwarning("No summands are changed");
     ATwarning("Written %d summands", cnt-skipped);
     ATwarning("Number of parameters of output LPO: %d", ATgetLength(pars));
     return ATreverse(result); 
     }
                              
static ATbool Sumelm(void) {
    ATerm proc = MCRLgetProc();
    ATermList pars = MCRLgetListOfPars(), inits = MCRLgetListOfInitValues(),
    sums = MCRLgetListOfSummands(), sums0 = sums;
    RWdeclareVariables(pars);
    for (;!ATisEmpty(sums0); sums0= ATgetNext(sums0)) {
        RWdeclareVariables(MCRLgetListOfVars(ATgetFirst(sums0)));
        }
    if (!nosingleton) Singletons((ATermList) ATgetArgument(
         (ATermAppl) ATgetArgument(MCRLgetAdt(),0),0));
    sums = SubstituteConstantParametersInSums(sums, pars);
    MCRLsetProc((ATerm)ATmakeAppl3(ATgetSymbol(proc), 
         (ATerm) inits, (ATerm) pars, (ATerm) sums));
    return !ATisEqual(proc, MCRLgetProc());
    }
                    
int main(int argc, char *argv[]) {
    int i, j =0;
    ATbool new;
    char **newargv = (char**) calloc(argc + 1, sizeof(char*));
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0];
    ATinit(argc, argv, (ATerm*) &argc);
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    for (i=1;i<argc;i++) {
	help(argv[i]);
	if (!strcmp(argv[i],"-version")) {
	    version();
	    exit(0);
	    }
       if (!strcmp(argv[i],"-verbose")) {
            verbose = ATtrue;
            monitor = ATtrue;
             /* continue; */
            }
       if (!strcmp(argv[i],"-nosingleton")) {
	    nosingleton = ATtrue;
	    continue;
	    }
       if (!strcmp(argv[i],"-monitor")) {
	    monitor = ATtrue;
	    continue;
	    }
        newargv[j++] = argv[i];   
	}
    Init();
    if (!MCRLinitRW(j, newargv)) exit(-1);
    {AFun s = MCRLputAndFunction(&new);
    if (s) {
        if  (verbose) {  
            if (new) ATwarning("Map %a: added", s);
                else ATwarning("Map %a: already present", s);
                }
        } else
        ATerror("Funcion \"and\" is not available");
    } 
    Sumelm();    
    MCRLoutput();
    exit(EXIT_SUCCESS);      
    }
    
