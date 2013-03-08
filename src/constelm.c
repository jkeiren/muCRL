/* $Id: constelm.c,v 1.5 2005/04/21 13:16:03 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "rw.h"

static char *who="Constelm";

static ATbool monitor = ATfalse,
nosingleton = ATfalse, nocondition = ATfalse;
static int cnt = 0, skipped = 0;

#define TABLESIZE 300
static ATermTable constantpar_tab;

#define IsConstant(par) (ATtableGet(constantpar_tab, par)!=NULL)


static void WarningHandler(const char *format, va_list args) {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }
     
static void ErrorHandler(const char *format, va_list args) {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     exit(-1);
     }
          
static void helpmsg(ATbool all) 
    {
    Pr("Usage: constelm [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\tyields this message");
    Pr("-help-all:\tyields all help information");
    Pr("-version:\tget the version number of this release");
    Pr("-monitor:\tdisplays progressing information"); 
    Pr("-nosingleton:\tno removal of process parameters which");
    Pr("\t\thave sorts of cardinality one");
    Pr("-nocondition:\tsaves computing time. No check if conditions are");
    Pr("\t\trewritten to false");
    if (all) {
       MCRLhelp();
       RWhelp();
       }   
    }
    

static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("");
    Pr("This filter removes process parameters which are constant");
    Pr("in the reachable state space and rewrites the LPO.");
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    exit(1);
    }
    
static void version(void)
    {
    /*
    Pr("$Id: constelm.c,v 1.5 2005/04/21 13:16:03 bertl Exp $");
    */
    char buf[100];
    sprintf(buf, "%s: version %s", who, VERSION);
    Pr(buf);
    }


static void Init(void) {
    constantpar_tab = ATtableCreate(TABLESIZE,75);
    if (!constantpar_tab) ATerror("Table is not allocated");
    }
     
static ATermList AddSingletonPars(ATermList sorts, ATermList vars)
     {
     ATermTable db_sort_constant = ATtableCreate(TABLESIZE,50);
     for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts))
          {ATerm sortterm = ATgetFirst(sorts);
          ATermList constructors = MCRLgetConstructors(ATgetAFun(sortterm));
	  if (MCRLgetType(ATgetSymbol(sortterm))==MCRLsort) continue;
          if (ATgetLength(constructors)==1)
               {
               ATerm constructor = ATgetFirst(constructors);
               if (ATisEmpty(ATgetArguments((ATermAppl) 
                    constructor))) {
                    ATwarning("Sort %t has only constructor: %t\n",
                    sortterm, MCRLprint(constructor));
                    ATtablePut(db_sort_constant, sortterm, constructor);
                    }
               }
          }
     for (;!ATisEmpty(vars);vars=ATgetNext(vars))
          {ATerm var = ATgetFirst(vars),
          varname = ATgetArgument((ATermAppl)var,0),
          sort = ATgetArgument((ATermAppl)var,1),
          constant = ATtableGet(db_sort_constant, sort);
          if (constant) 
               {
               RWassignVariable(ATgetSymbol(varname), constant,
               NULL,0);
               ATtablePut(constantpar_tab, varname, constant); 
               }
          }
     ATtableDestroy(db_sort_constant);
     return ATtableKeys(constantpar_tab);
     }
                              
static ATermList SetOfConstantParameters(void)
     {
     ATerm proc = MCRLgetProc(), adt = MCRLgetAdt();
     int cycle = 0;
     ATermList inits0 = RWrewriteList((ATermList) ATgetArgument((ATermAppl) proc, 0)),
     pars = (ATermList) ATgetArgument((ATermAppl) proc, 1),
     constantpars = NULL, inits = NULL;
     
     for (inits = (ATermList) ATgetArgument((ATermAppl) proc, 0);
          !ATisEmpty(inits)&&!ATisEmpty(pars);
          inits=ATgetNext(inits),pars=ATgetNext(pars))
          {
          ATerm init = ATgetFirst(inits), par = 
          ATgetArgument((ATermAppl) ATgetFirst(pars), 0);
          ATtablePut(constantpar_tab, par, init);
          }
          
     for (inits = inits0, pars = (ATermList) ATgetArgument((ATermAppl) proc, 1); 
         !ATisEmpty(inits); inits = ATgetNext(inits), pars=ATgetNext(pars))
         RWassignVariable(ATgetSymbol(ATgetArgument((ATermAppl) ATgetFirst(pars),0)),
                  ATgetFirst(inits), NULL, 0);
     do
     {
     ATermList sums = (ATermList) ATgetArgument((ATermAppl) proc, 2);
     constantpars = ATtableKeys(constantpar_tab); 
     if (monitor) 
       ATwarning("Cycle %d  #Constant variables %d", cycle, ATgetLength(constantpars));
     for (;!ATisEmpty(sums);sums=ATgetNext(sums))
          {ATerm sum = ATgetFirst(sums);
           ATerm procarg = ATgetArgument((ATermAppl) sum ,3);
           if (!ATisEqual(procarg, MCRLterm_terminated))
               {
               ATermList procargs = (ATermList) ATgetArgument(procarg,0);
               for (inits = inits0,
                    pars = (ATermList) ATgetArgument((ATermAppl) proc, 1);
                   !ATisEmpty(inits)&&!ATisEmpty(procargs);
                   inits=ATgetNext(inits),pars=ATgetNext(pars),
                   procargs = ATgetNext(procargs))
                   {ATerm init = ATgetFirst(inits), 
                   par = ATgetArgument((ATermAppl)ATgetFirst(pars),0),
                   procarg = ATgetFirst(procargs);
                   if (IsConstant(par)) { 
                   /* ATwarning("%t",MCRLprint(procarg)); */
                       if (!ATisEqual(RWrewrite(procarg), init) &&
                           (nocondition || 
                           !ATisEqual(RWrewrite((ATerm) ATgetArgument((ATermAppl) sum, 4)), 
                                      MCRLterm_false))
                         )
                         {
                         ATtableRemove(constantpar_tab, par);
                         RWassignVariable(ATgetSymbol(par) ,par, NULL, 0);
                         }
                       }
                   }
               }    
           } 
        }
        while (cycle++,!ATisEqual(constantpars, ATtableKeys(constantpar_tab)));
        return nosingleton?constantpars:
         AddSingletonPars((ATermList) ATgetArgument(
              (ATermAppl)ATgetArgument((ATermAppl) adt,0),0), 
        (ATermList) ATgetArgument((ATermAppl) proc, 1));
     }
          
     
static ATermList DeleteConstantPars(ATermList pars)
     {
     ATermList result = ATmakeList0();
     int k = 1;
     for (;!ATisEmpty(pars);pars=ATgetNext(pars),k++)
          {ATerm par = ATgetFirst(pars),
          parname = (ATerm) ATgetArgument((ATermAppl) par, 0),
          sortname = (ATerm) ATgetArgument((ATermAppl) par, 1);
          if (IsConstant(parname))
               {
               ATerm init  =  ATtableGet(constantpar_tab,  parname);
               ATwarning("Constant parameter %t (pos %d, sort %t) = \"%t\" is removed",
                  ATmake("<str>",MCRLgetName(parname)), k, sortname, MCRLprint(init));
               }
               else 
               result = ATinsert(result, par);
          }
     return ATreverse(result);
     }
          
static ATermList DeleteConstantTerms(ATermList terms, ATermList pars)
     {
     ATermList result = ATmakeList0();
     for (;!ATisEmpty(pars) && !ATisEmpty(terms);
          pars=ATgetNext(pars), terms = ATgetNext(terms))
          {ATerm par = ATgetFirst(pars),
          parname = (ATerm) ATgetArgument((ATermAppl) par, 0),
          term = ATgetFirst(terms);
          if (!IsConstant(parname))
               result = ATinsert(result, term);
          }
     return ATreverse(result);
     }
         
static ATermList SubstituteConstantParametersInSums(ATermList sums, ATermList pars)
     {
     ATermList result = ATmakeList0();
     for (cnt = 1, skipped = 0;!ATisEmpty(sums);sums=ATgetNext(sums), cnt++)
          {
          ATerm sum = ATgetFirst(sums);
          ATermList vars = (ATermList) ATgetArgument((ATermAppl) sum, 0),
                    acts = (ATermList) ATgetArgument((ATermAppl) sum, 2);
          ATerm procarg = (ATerm) ATgetArgument((ATermAppl) sum, 3),
                cond = (ATerm) ATgetArgument((ATermAppl) sum, 4);
          cond = RWrewrite(cond);
          if (ATisEqual(cond, MCRLterm_false)) 
               {
               /* This summand will be skipped */
               skipped++; 
               continue;
               }
          acts = RWrewriteList(acts);
          if (!ATisEqual(procarg, MCRLterm_terminated))
	       {
               ATermList terms = 
                    (ATermList) ATgetArgument((ATermAppl) procarg,0);
               terms = RWrewriteList(DeleteConstantTerms(terms, pars));
               procarg = (ATerm) ATmakeAppl1(ATgetSymbol(procarg), 
                    (ATerm) terms);
               }
          sum = (ATerm) ATmakeAppl5(ATgetSymbol(sum), 
               (ATerm) vars,
               (ATerm) ATgetArgument((ATermAppl) sum, 1), 
               (ATerm) acts, procarg, cond);
          result = ATinsert(result, sum);
          if (monitor) ATwarning("Summand %d is updated", cnt);
          }
     return ATreverse(result); 
     }
                           
static ATerm Run(ATerm proc) {
    ATermList inits = (ATermList) ATgetArgument((ATermAppl) proc,0),
    pars = (ATermList) ATgetArgument((ATermAppl) proc,1),
    sums = (ATermList) ATgetArgument((ATermAppl) proc,2), sums0 = sums;
    RWdeclareVariables(pars);
    for (;!ATisEmpty(sums0); sums0= ATgetNext(sums0)) {
        RWdeclareVariables(MCRLgetListOfVars(ATgetFirst(sums0)));
        }
    SetOfConstantParameters();      
    sums = SubstituteConstantParametersInSums(sums, pars);  
    inits = DeleteConstantTerms(inits, pars);
    pars = DeleteConstantPars(pars);
    proc = (ATerm) ATmakeAppl3(ATgetSymbol(proc), 
         (ATerm) inits, (ATerm) pars, (ATerm) sums);
    return proc;
    }
    
ATbool Constelm(void) {
     ATerm proc = MCRLgetProc();
     ATermList pars = MCRLgetListOfPars();
     int n = ATgetLength(pars);
     ATwarning("Read %d summands",
          ATgetLength(MCRLgetListOfSummands()));
     ATwarning("Number of parameters of input LPO: %d", ATgetLength(pars));
     MCRLsetProc(Run(proc));
     pars = MCRLgetListOfPars();
     n -= ATgetLength(pars); /* Number of removed parameters */
     if (n) {
          ATwarning("Number of removed parameter(s):%d", n);
          ATwarning("Number of remaining parameter(s) of output LPO:%d", 
          ATgetLength(pars));
          }
     ATwarning("Written %d summands", cnt-1-skipped);
     ATwarning("Number of parameters of output LPO: %d", ATgetLength(pars));
     return !ATisEqual(proc, MCRLgetProc());
     }
                      
int main(int argc, char *argv[]) {
    int i, j = 0;
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
       if (!strcmp(argv[i],"-monitor")) {
	    monitor = ATtrue;
	    continue;
	    }
       if (!strcmp(argv[i],"-nosingleton") || 
           !strcmp(argv[i],"-no-singleton"))  {
	    nosingleton = ATtrue;
	    continue;
	    }
       if (!strcmp(argv[i],"-nocondition") ||
           !strcmp(argv[i],"-no-condition")) {
	    nocondition = ATtrue;
	    continue;
	    }
        j=MCRLcopyOption(newargv, argv, argc, i, j);
	}
    Init();
    if (!MCRLinitRW(j, newargv)) exit(-1);
    Constelm();    
    MCRLoutput();
    exit(EXIT_SUCCESS);    
    }
    
