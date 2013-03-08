/* $Id: parelm.c,v 1.4 2005/04/21 13:16:03 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "aterm2.h"
#include "mcrl.h"

#define TABLESIZE 20
#define ERRORLENGTH 1024

/*
#define ATtableRemove(db, t) ATtablePut(db, t, (ATerm) INVALID)
*/



static char *who = "Parelm";
static ATermTable sortdb, hashtable;
static ATermInt mark;
static unsigned int trial, hit;
static ATbool verbose = ATfalse, monitor = ATfalse;


static void WarningHandler(const char *format, va_list args)
     {
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
    Pr("Usage: parelm [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\tyields this message");
    Pr("-help-all:\tyields all help information");
    Pr("-version:\tget the version number of this release");
    Pr("-ascii:\t\twrites .tbf file in ascii code");
    /* Pr("-monitor:\tprints the deleted sum variables"); */
    if (all) MCRLhelp();
    exit(0);
    }

static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("This filter reads from input an LPO in tbf format and reduces");
    Pr("it to an LPO which is strongly bisimilar with it.");  
    Pr("It removes process parameters and sum variables."); 
    Pr("Also the local variables of the summands which not occur");
    Pr("It does the following steps:");
    Pr("- Selects the process parameters which occur in the conditions");
    Pr("and the action arguments of the LPO.");
    Pr("- Adds to that selection all these process parameters on which all");
    Pr("in the previous step selected process parameters depend.");
    Pr("- Removes all these parameters which are not selected.");
    Pr("In each summand will be removed the process arguments belonging");
    Pr("to the removed parameters.");
    Pr("- Removes for each summand all these sum variables which occur neither");
    Pr("in the condition, nor in the action arguments, nor in the state vector.");
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    exit(0);
    }

static void version(void)
    {
    /*
    Pr("$Id: parelm.c,v 1.4 2005/04/21 13:16:03 bertl Exp $");
    */
    char buf[100];
    sprintf(buf, "%s:version %s", who, VERSION);
    Pr(buf);
    }

static ATbool Mark(ATerm t);

static ATbool _Mark(ATerm t)
    {
    ATermList args = ATgetArguments((ATermAppl) t);
    if (ATisEmpty(args))
         {
         ATerm r = ATtableGet(sortdb,t);
         if (r && !ATisEqual(r,mark))
	      {
	      ATtablePut(sortdb, t, (ATerm) mark);
	      return ATtrue;
	      }
          else return ATfalse;
          }
     else
          { 
          ATbool result = ATfalse;  
          for (;!ATisEmpty(args);args=ATgetNext(args))
               {ATerm arg = ATgetFirst(args);
                ATbool b = Mark(arg);
	        result = result || b;
	       }
          return result;
          }
    }
    
static ATbool Mark(ATerm t)
    {
    ATerm val = hashtable?ATtableGet(hashtable, t):NULL;
    /*
    if (trial % 100000 == 0) ATfprintf(stderr, "n mark: %d n hits %d\n", trial, hit);
    trial++;
    */
    if (val)
        {
        /*
        hit++;
        */
        return (ATbool) ATgetInt((ATermInt) val);
        }
         {
         ATbool result = _Mark(t);
         if (hashtable) ATtablePut(hashtable, t, (ATerm) ATmakeInt((int) result));
         return result;
         }
    }

static void PrintUnmarked(void)
    {
    int ndel = 0;
    ATermList l = ATtableKeys(sortdb);
    for (;!ATisEmpty(l);l = ATgetNext(l))
	{
	ATerm t = ATgetFirst(l); 
	if (!ATisEqual(ATtableGet(sortdb,t), mark))
	    {
	    ATwarning( "Parameter \"%s\" (sort %t) is removed", 
	    MCRLgetName(t), ATtableGet(sortdb,t));
	    ndel++;
	    }
	}
    if (ndel == 0)
	ATwarning( "No process parameters have been removed");
    else
    if (ndel == 1)
	ATwarning( "In total %d process parameter has been removed", 
	    ndel);
    else
	ATwarning( "In total %d parameters have been removed", ndel);
    }
    
static ATbool MarkState(ATermList pars, ATerm sum)
     {
     ATerm procarg = ATgetArgument((ATermAppl) sum, 3);
     ATbool result = ATfalse;
     if (ATisEqual(procarg, MCRLterm_terminated)) return result;
	{
        ATermList terms = (ATermList) ATgetArgument((ATermAppl)
        procarg,0);
        for (;!ATisEmpty(pars) && !ATisEmpty(terms);
             pars=ATgetNext(pars), terms=ATgetNext(terms))
             {ATerm par = ATgetArgument((ATermAppl) ATgetFirst(pars),0), 
                  term = ATgetFirst(terms);     
	      ATerm markedPar = ATtableGet(sortdb, par); 
	      if (ATisEqual(markedPar, mark))
		     {
		     /* Mark all variables in term */
                     ATbool b = Mark(term);
		     result = b || result;
                     }
	     }
         }
    return result;
    }
     
static ATbool MarkStates(ATermList pars, ATermList sums)
    {
    ATbool result = ATfalse;
    for (;!ATisEmpty(sums);sums=ATgetNext(sums))
          {ATerm sum = ATgetFirst(sums);
          ATbool b = MarkState(pars, sum);
          result = b || result;
          }
    return result;
    }

static ATermList SmallerSumvars(ATermList pars, ATermList sums);

static int StoreSortsInDb(ATermList pars)
     {
     int cnt = 0;
     for (;!ATisEmpty(pars);pars=ATgetNext(pars))
        {ATerm par = ATgetFirst(pars);
        ATerm name = ATgetArgument((ATermAppl) par,0),
             sort = ATgetArgument((ATermAppl) par,1);
	ATtablePut(sortdb, name, sort);
	cnt++;
	}
     return cnt;
     }
     
static void MarkActions(ATermList acts)
{
for (;!ATisEmpty(acts);acts=ATgetNext(acts))
     {ATerm act = ATgetFirst(acts);
      Mark(act);
     }
}


         
static void MarkActionAndCondition(ATermList sums){
int k = 0;
for (;!ATisEmpty(sums);sums=ATgetNext(sums), k++)
    {ATerm sum = ATgetFirst(sums);
     hashtable = ATtableCreate(TABLESIZE, 50);
     trial = 0; hit = 0;
     if (hashtable)
     {
     ATerm cond = ATgetArgument((ATermAppl) sum, 4); 
     ATermList acts = (ATermList) ATgetArgument((ATermAppl) sum, 2),
     vars = (ATermList) ATgetArgument((ATermAppl) sum, 0);
     Mark(cond);
     MarkActions(acts);
     ATtableDestroy(hashtable);hashtable = NULL;
     }
     else ATerror("Cannot allocate hash table\n");
    }    
}

static ATermList DeleteTerms(ATermList terms, ATermList pars) {
     ATermList result = ATmakeList0();
     for (;!ATisEmpty(pars)&&!ATisEmpty(terms);
          pars=ATgetNext(pars), terms = ATgetNext(terms))
         {ATerm par = ATgetArgument((ATermAppl) ATgetFirst(pars),0);
         ATerm term =  ATgetFirst(terms);
         if (ATisEqual(ATtableGet(sortdb, par), mark))
         result = ATinsert(result, term);
         } 
     return ATreverse(result);
     } 
     
static ATermList ReduceProcargs(ATermList pars, ATermList sums) {
     ATermList result = ATmakeList0();
     for (;!ATisEmpty(sums);sums=ATgetNext(sums))
          {ATerm sum = ATgetFirst(sums);
           ATermList vars = (ATermList) ATgetArgument((ATermAppl) sum, 0),
           acts = (ATermList) ATgetArgument((ATermAppl) sum, 2);
           ATerm cond = ATgetArgument((ATermAppl) sum, 4),
           nextstate = ATgetArgument((ATermAppl) sum, 3);
           if (!ATisEqual(nextstate, MCRLterm_terminated)) {
                ATermList procargs = (ATermList) ATgetArgument(nextstate,0);
                procargs = DeleteTerms(procargs, pars);
                sum = (ATerm) ATmakeAppl5(ATgetSymbol(sum), (ATerm) vars,
                     ATgetArgument((ATermAppl) sum, 1), (ATerm) acts, 
                     (ATerm) ATmakeAppl1(MCRLsym_i,(ATerm ) procargs), cond);
                }
           result = ATinsert(result, sum);     
          }
     return ATreverse(result);
     }

static ATermList ReducePars(ATermList pars) {
     ATermList result = ATmakeList0();
     for (;!ATisEmpty(pars);pars=ATgetNext(pars))
         {ATerm par = ATgetFirst(pars),
              name = ATgetArgument((ATermAppl) par, 0);
         if (ATisEqual(ATtableGet(sortdb, name), mark))
         result = ATinsert(result, par);
         }
     return ATreverse(result);
     }
        
static ATbool Smaller(ATerm proc) {
    ATermList pars = (ATermList) ATgetArgument((ATermAppl) proc,1),
    inits = (ATermList) ATgetArgument((ATermAppl) proc,0),
    sums = (ATermList) ATgetArgument((ATermAppl) proc,2);
    int cnt = StoreSortsInDb(pars);
    ATerm r = NULL; ATbool result = ATfalse;
    ATwarning("Number of parameters of input LPO: %d",cnt);
    MarkActionAndCondition(sums);
    while (MarkStates(pars,sums)); 
    PrintUnmarked(); 
    sums = ReduceProcargs(pars, sums);
    inits = DeleteTerms(inits, pars);
    pars = ReducePars(pars);
    ATwarning("Number of parameters of output LPO: %d",ATgetLength(inits));
    r = (ATerm) ATmakeAppl3(ATgetSymbol(proc), (ATerm) inits, (ATerm) pars, 
         (ATerm) sums);
    result = ATisEqual(r, MCRLgetProc()); 
    MCRLsetProc(r);
    return result; 
    }

/* Considers state components as sets.
If state vector has length n, then ther are n state sets
*/
                
void Init(void) {
    ATprotect((ATerm*) &mark);
    mark = ATmakeInt(1);
    sortdb = ATtableCreate(TABLESIZE,50);
    if (!sortdb) ATerror("Table is not allocated\n");
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
	    version(); exit(0);
	    }
        /*
        if (!strcmp(argv[i],"-verbose")) {
            monitor = ATtrue;
	    verbose = ATtrue; 
	    }
        if (!strcmp(argv[i],"-monitor")) {
            monitor = ATtrue;
            continue;
	    }
        */
	newargv[j++] = argv[i];
	}
    Init();
    if (!MCRLinitOnly(j, newargv)) exit(EXIT_FAILURE);
    Smaller(MCRLgetProc());
    MCRLoutput();
    exit(EXIT_SUCCESS);
    }
