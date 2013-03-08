/* $Id: */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdio.h>
#include "rw.h"

static char *who = "Tbfinfo";

static unsigned int cnt;
ATermList smds = NULL, pars = NULL, inits =  NULL, vars = NULL,
actnames = NULL, actargs = NULL;
static ATbool extra = ATfalse, npars = ATfalse;

static void WarningHandler(const char *format, va_list args)
     {
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

static void helpmsg(void) 
    {
    Pr("Usage: tbfinfo [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\tyields this message");
    Pr("-version:\tget the version number of this release");
    Pr("-pars:\t\tprints the list of parameters");
    Pr("-npars:\t\tprints only the number of parameters");
    Pr("Prints info about the .tbf file");
    MCRLhelp();
    }
    
static void help(void)
    {
    Pr("");
    helpmsg();
    Pr("");
    Pr("");
    }

static void version(void)
    {
    char buf[100];
    sprintf(buf,"%s: version %s",who, VERSION);
    Pr(buf);
    }


static void SubstituteInPars(ATermList pars, ATermList gs) {
     for (;!ATisEmpty(gs);gs = ATgetNext(gs), pars = ATgetNext(pars)) {
         RWassignVariable(ATgetSymbol(ATgetArgument(ATgetFirst(pars),0)) ,
         ATgetFirst(gs), NULL, 0);
         }
     }
      
static void DisabledEdges(ATermList gs) {
     ATermList smds = MCRLgetListOfSummands(),
     pars = MCRLgetListOfPars();
     int false_cnt = 0, true_cnt = 0, n = ATgetLength(smds);
     static int k = 1;
     SubstituteInPars(pars, gs);
     for (;!ATisEmpty(smds);smds=ATgetNext(smds)) {
         ATerm smd = ATgetFirst(smds),
               c = ATgetArgument((ATermAppl) smd,4),
         cw = NULL;
         if (!ATisEmpty((ATermList) ATgetArgument((ATermAppl) smd, 0)))
          ATerror("Flag -extra is used while sum variables occur");
         cw = RWrewrite(c);
         if (
           ATisEqual(cw, MCRLterm_false)) false_cnt++;
         if (
           ATisEqual(cw, MCRLterm_true)) true_cnt++;
         }
         fprintf(stdout, "Summand %d N = %d disabled %d enabled %d\n", 
         k++, n, false_cnt, true_cnt);
     }
             
int main(int argc, char *argv[]) {
    int i, j = 0;
    char **newargv = (char**) calloc(argc + 2, sizeof(char*));
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0]; newargv[j++] = "-no-extra-rules";
    ATinit(argc, argv, (ATerm*) &argc);
    ATprotect((ATerm*) &smds);
    ATprotect((ATerm*) &pars);
    ATprotect((ATerm*) &inits);
    ATprotect((ATerm*) &vars);
    ATprotect((ATerm*) &actnames);
    ATprotect((ATerm*) &actargs);
    vars = actnames = actargs = ATempty;
    for (i=1;i<argc;i++) {
    if (!strcmp(argv[i],"-help")) {
	help();
	exit(0);
	}
    if (!strcmp(argv[i],"-version")) {
	version();
	exit(0);
	}
   if (!strcmp(argv[i],"-pars")) {
	pars = ATempty;
        continue;
	}
   if (!strcmp(argv[i],"-npars")) {
	npars = ATtrue;
        continue;
	}
   if (!strcmp(argv[i],"-extra")) {
	extra = ATtrue;
        continue;
	}
    newargv[j++] = argv[i];
    }
    if (extra) {
         if (!MCRLinitRW(j, newargv)) exit(EXIT_FAILURE);
         RWdeclareVariables(MCRLgetListOfPars());
         }
    else
    {if (!MCRLinitSU(j, newargv)) exit(EXIT_FAILURE);}
    if (npars) {
        fprintf(stdout,"%d", MCRLgetNumberOfPars());
        exit(EXIT_SUCCESS);
        }
    smds = MCRLgetListOfSummands();
    if (pars) {
         pars = MCRLgetListOfPars();
         inits = MCRLgetListOfInitValues();
         }
    ATfprintf(stdout, "Number of process parameters: %d\n", 
          MCRLgetNumberOfPars());
    ATfprintf(stdout, "Number of summands: %d\n",ATgetLength(smds));
    for (;!ATisEmpty(smds);smds=ATgetNext(smds)) {
         ATerm smd = ATgetFirst(smds);
         ATerm actname = ATgetArgument((ATermAppl) smd, 1),
               actarg = ATgetArgument((ATermAppl) smd, 2);
         vars = ATconcat(vars, (ATermList) ATgetArgument((ATermAppl) smd, 0));
         if (ATindexOf(actnames , actname, 0) < 0 || 
               ATindexOf(actargs , actarg, 0)<0) {
                actnames = ATinsert(actnames, actname); 
                actargs = ATinsert(actargs, actarg);
                }
         if (extra) {
                if (!ATisEmpty(vars)) ATerror(
                "Flag -extra cannot be used, there are sum variables present");
                DisabledEdges(
                   (ATermList) ATgetArgument(
                      (ATermAppl)ATgetArgument((ATermAppl) smd, 3), 0));
                }
         }
    ATfprintf(stdout, "Number of sum variables: %d\n", ATgetLength(vars));
    ATfprintf(stdout, "Number of different action names: %d\n", 
               ATgetLength(actnames));
    if (pars) {
        ATfprintf(stdout, "Process parameters\n");
        for (i=1;!ATisEmpty(pars)&&!ATisEmpty(inits);
             pars=ATgetNext(pars), inits=ATgetNext(inits),i++) {
             ATerm par = ATgetFirst(pars);
             ATfprintf(stdout, "%t:\t%t\tinit[%d]=%t\n", MCRLprint(
                   ATgetArgument((ATermAppl)par, 0)),
                   MCRLprint(ATgetArgument((ATermAppl)par, 1)),
                   i, MCRLprint(ATgetFirst(inits))); 
             }
       }
    exit(EXIT_SUCCESS); 
    }
