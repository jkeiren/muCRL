/* $Id: binary.c,v 1.3 2005/04/21 13:16:03 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "mcrl.h"
#include "rw.h"
#include "string.h"
#include "assert.h"

static char *who="Binary";

static int rewrite = 1;   /* This variable indicates whether the
                              replaced terms must be rewritten */
static int generate_invariant = 0; /* This variable indicates that 
			     an invariant must be generated
			     restricting the sizes of the domains
			     represented as booleans */
static int generate_invariant_file = 0; /* Same as above, but generates the
					    invariant and puts it in a file */
static char *invariant_file_name = NULL;

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
    Pr("Usage: binary [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:      yields this message");
    Pr("-help-all:  yields all help information");
    Pr("-version:   get the version number of this release");
    Pr("-norewrite: do not rewrite after replacing parameters"); 
    Pr("-inv:       add a condition to each summand restricting the");
    Pr("            new boolean parameters to values corresponding to");
    Pr("            valid values of the enumerated types");
    Pr("-invfile <file>: do the same as -inv, but put the conditions");
    Pr("            as an invariant in the file <file>");
    if (all) {
       MCRLhelp();
       RWhelp();
       }   
}
    

static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("This program transforms each parameter of enumerated sort to a");
    Pr("sequence of parameters of sort Bool.");
    Pr("The resulting LPO, written on standard output, is strongly bisimilar to the");
    Pr("original LPO. It does not affect parameters in sums. If needed this could"); 
    Pr("be added in a later version of this tool.");
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    exit(0);
    }
    
static void version(void)
    {
    char buf[100];
    sprintf(buf, "%s: version %s", who, VERSION);
    Pr(buf);
    }

ATermTable newparametersTable = NULL;

static void Init(void) 
    { newparametersTable=ATtableCreate(128,50);
    }
     
/***********************  ReplaceEnumeratedPars  ***********************/

static int is_finite_type_and_not_Bool(AFun sort)
{ 
  if (sort==ATmakeAFun("Bool",0,ATtrue)) return 0;
  if (MCRLisFiniteSort(sort)) return 1;
  return 0;
}

static int logo2(int n)
{ /* This function delivers the number of bits to represent
     a domain of n elements */
  int r=0;
  if (n==0) ATerror("Domain cannot be empty");
  n=n-1; /* now n is the maximal value to be represented */
  for( ; n>0 ; r++, n=n/2) {}
  return r;
}

static int powerof2(int n)
{ int r=1;
  for(  ; n>0 ; r=r*2, n=n-1) {}
  return r;
}

static ATerm makeDomainRestriction(ATermList parameters,int n)
{ ATerm result=NULL;
  ATerm parameter=NULL;

  assert(n>1);

  n=n-1;
  for( ; (n>0) ; n=n/2)
    { parameter=ATgetFirst(parameters);
      parameters=ATgetNext(parameters);
      if ((n % 2)==0)
       { if (result==NULL)
          { result=ATmake("\"not#Bool\"(<term>)",parameter);
          }
         else
          { result=ATmake("\"and#Bool#Bool\"(\"not#Bool\"(<term>),<term>)",
                    parameter,result);
          }
       }
     else
       { if (result==NULL)
          { result=ATmake("\"T#\"");
          }
         else
          { result=ATmake("\"or#Bool#Bool\"(\"not#Bool\"(<term>),<term>)",
	                          parameter,result);

          }
       }
    }
  return result;
}
 
                              
static ATermList ReplaceEnumeratedPars(ATermList pars, ATerm *invariant)
{    ATermList result = ATmakeList0();
     int i = 0;
     for (;!ATisEmpty(pars);pars=ATgetNext(pars),i++)
        { ATerm par = ATgetFirst(pars),
          parname = (ATerm) ATgetArgument((ATermAppl) par, 0),
          sortname = (ATerm) ATgetArgument((ATermAppl) par, 1);
          if (is_finite_type_and_not_Bool(ATgetAFun(sortname)))
          {  /* n is the number of booleans to represent sortname */
             ATermList newparameterlist=ATempty;
             int n=logo2(ATgetLength(MCRLgenerateElementsOfFiniteSort(ATgetAFun(sortname))));
             ATwarning("Parameter %t:%t has been replaced by %d parameters of type Bool",
                  ATmake("<str>",MCRLgetName(parname)), sortname,n);
             for(i=0 ; i<n ; i++)
             { ATerm newname=MCRLuniqueTerm(
                            ATgetName(ATgetAFun(parname)),ATempty);
	       RWdeclareVariables((ATermList)ATmake("[v(<term>,<term>)]",
		                        newname,sortname));
               newparameterlist=ATinsert(newparameterlist,newname);
               result = ATinsert(result,ATmake("v(<term>,\"Bool\")",newname));
             }

	     if (generate_invariant | generate_invariant_file) 
	           *invariant=ATmake("\"and#Bool#Bool\"(<term>,<term>)",
		      makeDomainRestriction(newparameterlist,
		          ATgetLength(MCRLgenerateElementsOfFiniteSort(ATgetAFun(sortname)))),
		      *invariant);
             ATtablePut(newparametersTable,parname,
                            (ATerm)ATreverse(newparameterlist));
          }
          else 
	  {
          if (!ATisEqual(sortname, MCRLterm_bool)) 
          ATwarning("Parameter %t:%t has not been replaced by parameters of type Bool",
	              ATmake("<str>",MCRLgetName(parname)), sortname);
	  result = ATinsert(result, par);
	  }
        }
     return ATreverse(result);
}

/* AFun MCRLgetCaseFunction(AFun fsort, AFun ssort)
{ ATermList l=MCRLgetCaseFunctions(ssort);

  for( ; (!ATisEmpty(l)) ; l=ATgetNext(l) )
  { ATerm t=ATgetFirst(l);
    if (ATgetAFun(ATgetArgument(t,0))==fsort)
    { return ATgetAFun(t); }
  }
  ATerror("Cannot find case function for %s and %s",
                 ATgetName(fsort),ATgetName(ssort));
  return -1;
} */

static ATerm makeIfThenElseTree(ATermList newparameters,
                 ATermList enumeratedElements,AFun sort)
{ int n=0,m=0;
  ATbool dummy;

  if (ATisEmpty(newparameters))
  { return ATgetFirst(enumeratedElements); }

  n=ATgetLength(enumeratedElements);
  m=powerof2(ATgetLength(newparameters)-1);  
  if (m>n) m=n;
  
  return (ATerm)ATmakeAppl3(
         MCRLputCaseFunction(2,(ATerm) ATmakeAppl0(sort),&dummy), 
           ATgetFirst(newparameters),
           makeIfThenElseTree(ATgetNext(newparameters),
                ATgetSlice(enumeratedElements,((m==n)?m-1:m),n),sort),
           makeIfThenElseTree(ATgetNext(newparameters),
                 ATgetSlice(enumeratedElements,0,m),sort));
}


static ATerm ReplaceEnumeratedParametersInTerm(ATerm term, ATermTable hashtable)
{ 
  ATermList enumeratedElements=NULL;
  ATermList newparameters=NULL;

  ATerm t=ATtableGet(hashtable,term);
  if (t!=NULL) return t;
    
  newparameters=(ATermList)ATtableGet(newparametersTable,term);
  if (newparameters==NULL)
  { int i, arity=ATgetArity(ATgetAFun(term));
    DECLA(ATerm,atermarray,arity); 
    /* ATerm *atermarray=alloca(sizeof(ATerm)*arity); */
    for (i=0 ; i<arity ; i++) 
    { atermarray[i] = ReplaceEnumeratedParametersInTerm(ATgetArgument(term,i),hashtable);
    }  
    t=(ATerm)ATmakeApplArray(ATgetAFun(term),atermarray);
    ATtablePut(hashtable,term,t);
    return t;
  }

  enumeratedElements=MCRLgenerateElementsOfFiniteSort(MCRLgetSort(term));
  
  t=makeIfThenElseTree(newparameters,enumeratedElements,MCRLgetSort(term));
  ATtablePut(hashtable,term,t);
  return t;
}

          
static ATermList ReplaceEnumeratedParametersInTerms(ATermList terms,ATermTable hashtable)
{ ATermList result = ATempty;
  for (; !ATisEmpty(terms); terms = ATgetNext(terms))
  { result = ATinsert(result, 
          ReplaceEnumeratedParametersInTerm(ATgetFirst(terms),hashtable));
    
  }
  return ATreverse(result);
}

static ATermList ReplaceEnumeratedParametersInProcessArguments
       (ATermList procargs,ATermTable hashtable)
{ ATermList result = ATempty;
  
  for( ; !ATisEmpty(procargs) ; procargs=ATgetNext(procargs))
  { ATerm arg=ATgetFirst(procargs);
    ATbool new = ATfalse;
    AFun eqsym = 
        MCRLputEqFunction((ATerm) ATmakeAppl0(MCRLgetSort(arg)), &new);
    if (eqsym==0) ATerror(
    "Not possible to define eq-function belonging to sort %a", 
        MCRLgetSort(arg));
    if (is_finite_type_and_not_Bool(MCRLgetSort(arg)))
    { /* Replace the single occurrence of this variable
         by a multiple occurrence of booleans */
      int i=0;
      ATermList l=MCRLgenerateElementsOfFiniteSort(MCRLgetSort(arg));
      arg=ReplaceEnumeratedParametersInTerm(arg,hashtable);
      if (rewrite) arg=RWrewrite(arg);
      for(i=logo2(ATgetLength(l)) ; i>0 ; i--)
      {	int j=0;
        ATerm r=MCRLterm_false;
        ATermList l1=l;
	for( ; !ATisEmpty(l1) ; )
	{ for(j=0 ; j<powerof2(i-1) ; j++)
	    { if (!ATisEmpty(l1)) l1=ATgetNext(l1);
	    }
	  for(j=0 ; j<powerof2(i-1) ; j++)
	    { if (!ATisEmpty(l1)) 
	      { 
	        r=(ATerm) ATmakeAppl2(MCRLsym_or, r,
    		    (ATerm) ATmakeAppl2(eqsym,arg,ATgetFirst(l1)));
                l1=ATgetNext(l1);
              }
            }
	}
        result=ATinsert(result,r);
      }
    }
    else /* we cannot replace this variable */
    { arg=ReplaceEnumeratedParametersInTerm(arg,hashtable);
      if (rewrite) arg=RWrewrite(arg);
      result=ATinsert(result,arg);
    }
  }
  return ATreverse(result);
}
         
static ATermList ReplaceEnumeratedParametersInSums(ATermList sums,
                   ATerm invariant,ATbool include_invariant, ATermTable hashtable)
{ ATermList result = ATempty;
  int i=1;
  for (  ; !ATisEmpty(sums); sums=ATgetNext(sums))
  { /* For the moment we do not replace the sums, this
       might be considered for a later moment */
    ATerm sum = ATgetFirst(sums); 
    ATermList vars = (ATermList) ATgetArgument((ATermAppl) sum, 0),
              acts = (ATermList) ATgetArgument((ATermAppl) sum, 2);
    ATerm procarg = (ATerm) ATgetArgument((ATermAppl) sum, 3),
              cond = (ATerm) ATgetArgument((ATermAppl) sum, 4);
    /* ATfprintf(stderr,"NEXT %d\n",i); fflush(stderr);i++; */
    RWdeclareVariables(vars);
    cond = ReplaceEnumeratedParametersInTerm(cond,hashtable);
    if (include_invariant) 
           cond = (ATerm) ATmakeAppl2(MCRLsym_and, cond,invariant);
    if (rewrite) cond = RWrewrite(cond);

    acts = ReplaceEnumeratedParametersInTerms(acts,hashtable);
    if (rewrite) acts = RWrewriteList(acts);

    if (!ATisEqual(procarg, MCRLterm_terminated))
    { ATermList terms = (ATermList) ATgetArgument((ATermAppl) procarg,0);
      terms=ReplaceEnumeratedParametersInProcessArguments(terms,hashtable);
      procarg = (ATerm) ATmakeAppl1(ATgetSymbol(procarg), (ATerm)terms);
    }

    sum = (ATerm) ATmakeAppl5(
	       ATgetSymbol(sum),
	       (ATerm) vars,
	       (ATerm) ATgetArgument((ATermAppl) sum, 1),
               (ATerm) acts, procarg, cond);
    result = ATinsert(result, sum);
  }
  return ATreverse(result); 
}
                           
static ATerm Replace_Enumerated_Parameters_By_Booleans(ATerm proc) {
    ATerm invariant=MCRLterm_true;
    ATermList inits = (ATermList) ATgetArgument((ATermAppl) proc,0),
              pars = (ATermList) ATgetArgument((ATermAppl) proc,1),
              sums = (ATermList) ATgetArgument((ATermAppl) proc,2);
    ATermTable hashtable=ATtableCreate(1024,80);
    /* Replace all variables of an enumerated type by booleans */
    RWdeclareVariables(pars);
    pars = ReplaceEnumeratedPars(pars,&invariant);
    RWdeclareVariables(pars);
    inits = ReplaceEnumeratedParametersInProcessArguments(inits,hashtable);
    if (rewrite) inits=RWrewriteList(inits);
    if (rewrite) invariant=RWrewrite(invariant);
    if (generate_invariant_file)
    {  ATwriteToNamedTextFile(MCRLprint(invariant),invariant_file_name);  
    }  
    sums = ReplaceEnumeratedParametersInSums(sums,invariant,generate_invariant,hashtable);  
    proc = (ATerm) ATmakeAppl3(ATgetSymbol(proc), 
         (ATerm) inits, (ATerm) pars, (ATerm) sums);
    return proc;
    }
    
static void Binary(void) 
{ 
  ATermList pars = MCRLgetListOfPars();
  int n = ATgetLength(pars);
  ATbool new;
  if (!(new = ATfalse, MCRLputOrFunction(&new)) ||
      !(new = ATfalse, MCRLputAndFunction(&new)) ||
      !(new = ATfalse, MCRLputNotFunction(&new)))
  ATerror("Not possible to define new and/or/not function"); 
  ATwarning("Read %d summands",
          ATgetLength(MCRLgetListOfSummands()));
  ATwarning("Number of parameters of input LPO: %d", ATgetLength(pars));
  MCRLsetProc(Replace_Enumerated_Parameters_By_Booleans(MCRLgetProc()));
  pars = MCRLgetListOfPars();
  n -= ATgetLength(pars); /* Number of removed parameters */
  if (n) 
  { ATwarning("Number of added parameter(s):%d", -n);
          ATwarning("Number of remaining parameter(s) of output LPO:%d", 
          ATgetLength(pars));
  }
  ATwarning("Number of parameters of output LPO: %d", ATgetLength(pars));
  
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
	if (!strcmp(argv[i],"-norewrite")) {
            rewrite=0;
	    }
	else if (!strcmp(argv[i],"-inv")) {
            generate_invariant=1;
	    }
	else if (!strcmp(argv[i],"-invfile")) {
            generate_invariant_file=1;
	    i++;
	    invariant_file_name=argv[i];
	    if (invariant_file_name[0]=='-')
	       ATerror("Argument of flag -invfile starts with dash. Most likely a mistake");
	    }
	else newargv[j++] = argv[i];
	}
    Init();
    if (!MCRLinitRW(j, newargv)) exit(-1);
    Binary();    
    MCRLoutput();
    exit(EXIT_SUCCESS);
}
    
