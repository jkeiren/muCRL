/* $Id: decluster.c,v 1.7 2005/12/22 10:41:10 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "rw.h"
#include "step.h"


static char *who="Decluster";
static ATermList *deletedVars = NULL, deletedSorts = NULL, definedSorts = NULL;

static ATbool split = ATfalse, finite = ATfalse, report = ATfalse;


static void helpmsg(ATbool all) 
    {
    Pr("Usage: decluster [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\tyields this message");
    Pr("-help-all:\tyields all help information");
    Pr("-version:\tget the version number of this release");
    Pr("-finite:\tprocesses only sumvariables whose sorts are finite");
    Pr("-sort <sort>:\tprocesses only sumvariables of <sort>");
    Pr("-report:\t\treports the sorts which are processed");
    SThelp();
    if (all) {
       MCRLhelp();
       RWhelp();
       }
    }
    
static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    Pr("This filter reads from input an LPO in .tbf format and makes");
    Pr("sumvariables superfluous by enlarging the number of summands.");
    Pr("The output LPO will be written on stdout");
    Pr("The sumvariables will be removed");   
    Pr("");
    exit(0);
    }

static void version(void) {
    char buf[100];
    sprintf(buf,"Rewriter: version %s",VERSION);
    Pr(buf);
    }

static ST_ORDER  order = noOrdering;
static int nPars, nPars2, nWrittenSummands = 0;

static ATerm *src, *dest, *src_pt, *dest_pt, label;
static ATermList sums = NULL;

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
/* 
static void CallBack(ATerm sumvars, ATerm actname, ATermList actargs,
ATermList nextstates, ATerm cond) {
*/

static void CallBack(void) {
     ATerm sum = STcurrentSummand();
     sum = (ATerm) ATsetArgument((ATermAppl) sum, 
     (ATerm) deletedVars[STgetSmdIndex()] ,0);
     sums = ATinsert(sums, sum);
     nWrittenSummands++;
     }

static void Report(ATermList srts) {
     ATwarning("The declustered sorts are:");
     for (;!ATisEmpty(srts);srts=ATgetNext(srts)) {
        ATerm srt = ATgetFirst(srts);
        ATfprintf(stderr, " %t",srt);
        }
     ATfprintf(stderr, "\n"); 
     }
               
static void Initialize(void) {
     ATermList smds = MCRLgetListOfSummands(), newsmds = ATempty, 
     newsorts = ATempty;
     int n = ATgetLength(smds), i;
     deletedVars = (ATermList*) calloc(n, sizeof(ATermList));
     ATprotectArray((ATerm*) deletedVars, n);
     for (i=0;i<n;i++) deletedVars[i] = ATempty;
     for (i=0;!ATisEmpty(smds);smds=ATgetNext(smds),i = i+1) {
        ATerm smd = ATgetFirst(smds);
        ATermList vars = MCRLgetListOfVars(smd), newvars = ATempty;
        RWdeclareVariables(vars);
        for (;!ATisEmpty(vars);vars=ATgetNext(vars)) {
            ATerm var = ATgetFirst(vars);
            ATerm srt = ATgetArgument((ATermAppl) var, 1);
            AFun sort = ATgetAFun(srt);
            /* Ignore the undetermined and infinite sorts */
            if (ATindexOf(deletedSorts, srt, 0)>=0 ||
            MCRLgetType(sort) == MCRLsort||(finite&&!MCRLisFiniteSort(sort))) 
            deletedVars[i] = ATinsert(deletedVars[i], var);
            else {
               newvars = ATinsert(newvars, var);
               if (ATindexOf(newsorts, srt, 0)<0) 
                  newsorts = ATinsert(newsorts, srt);
               }
            }
         newsmds = ATinsert(newsmds, (ATerm) 
             ATsetArgument((ATermAppl) smd, (ATerm) ATreverse(newvars), 0)); 
         } 
     if (report) Report(ATreverse(newsorts)); 
     MCRLsetListOfSummands(ATreverse(newsmds));                 
     nPars = MCRLgetNumberOfPars();  nPars2 = 2 * nPars;
     if (!(src = calloc(nPars2, sizeof(ATerm))))
         {ATerror("Cannot allocate src (%d bytes)",nPars2*sizeof(ATerm));
         exit(1);}
     if (!(dest = calloc(nPars2, sizeof(ATerm))))
         {ATerror("Cannot allocate dest (%d bytes)",nPars2*sizeof(ATerm));
         exit(1);}
     ATprotectArray(src, nPars2); ATprotectArray(dest, nPars2);
     label=(ATerm)0;
     ATprotect(&label);
     ATprotect((ATerm*) &sums);
     src_pt = src + nPars; dest_pt = dest + nPars;
     sums = ATempty;
     }

static int FirstStep() {
     int result, i=0, n = MCRLgetNumberOfPars();
     ATermList pars = MCRLgetListOfPars();
     for (i=0;i<n;i++, pars = ATgetNext(pars)) src_pt[i] =  
        ATgetArgument((ATermAppl) ATgetFirst(pars),0);
     result = STstep(src_pt);
     return result;
     }

ATermList IdemPotentSums(ATermList sums) {
     ATermList newsmds = ATempty;
     int cnt = 0;
     for (nWrittenSummands = 0;!ATisEmpty(sums); sums = ATgetNext(sums)) {
        ATerm smd = ATgetFirst(sums);
        if (ATindexOf(newsmds, smd, 0)<0) { 
           newsmds = ATinsert(newsmds, smd);
           nWrittenSummands++;
           }
        else
           cnt++;
      }  
     if (cnt>0) ATwarning("There are %d equal summands found", cnt);
     return ATreverse(newsmds);
     }

static ATerm Inst(ATerm smd, ATerm cond, ATbool b) {
     ATerm vterm = ATgetArgument((ATermAppl) cond, 0);
     AFun v = ATgetAFun(vterm);
     ATerm result = NULL;
     ATerm procarg = ATgetArgument((ATermAppl) smd, 3);
     if (b) { 
          ATerm c = ATgetArgument((ATermAppl) cond, 1);
          RWassignVariable(v, MCRLterm_true, NULL, 1);
          cond = 
           (ATerm) ATmakeAppl2(MCRLsym_and,vterm, RWrewrite(c));
          }
     else {
          ATerm c = ATgetArgument((ATermAppl) cond, 2);
          RWassignVariable(v, MCRLterm_false, NULL, 1);
          cond = 
           (ATerm) ATmakeAppl2(MCRLsym_and,
                (ATerm) ATmakeAppl1(MCRLsym_not, vterm), RWrewrite(c));
          }
     if (!ATisEqual(procarg, MCRLterm_terminated)) {
          ATermList states = (ATermList) ATgetArgument((ATermAppl) procarg, 0);
          states = RWrewriteList(states);
          procarg = (ATerm) ATmakeAppl1(MCRLsym_i, (ATerm) states);
          }
     RWresetVariables(1);
     cond = RWrewrite(cond);
     if (ATisEqual(cond, MCRLterm_false)) return NULL; 
     result = (ATerm) ATmakeAppl5(ATgetAFun(smd), ATgetArgument((ATermAppl)
        smd,0), ATgetArgument((ATermAppl) smd, 1), 
        (ATerm) RWrewriteList((ATermList) ATgetArgument((ATermAppl) smd, 2)),  
        procarg, cond);
     return result;
     }

static ATermList Split(ATermList sums) {
     ATermList newsums = ATempty;
     ATerm r = NULL;
     for (;!ATisEmpty(sums);sums=ATgetNext(sums)) {
         ATerm sum = ATgetFirst(sums);
         ATerm cond = ATgetArgument((ATermAppl) sum,4);
         if (MCRLgetType(ATgetAFun(cond))==MCRLcasefunction &&
          MCRLgetSort(cond)== ATgetAFun(MCRLterm_bool) &&
          ATgetArity(ATgetAFun(cond))==3 &&
          MCRLgetType(ATgetAFun(
               ATgetArgument((ATermAppl) cond, 0)))==
                     MCRLvariable) {
             r = Inst(sum, cond, ATtrue);
             if (r) {
                 newsums = ATinsert(newsums, r);
                 nWrittenSummands++;
                 }
             r = Inst(sum, cond, ATfalse);
             if (r) {
                 newsums = ATinsert(newsums, r);
                 nWrittenSummands++;
                 }
         }
         else {
            newsums = ATinsert(newsums, sum);
            nWrittenSummands++;
            }
        }
     return ATreverse(newsums);    
     }
     
static void DeletedSorts(ATermList definedSorts) {
      if (definedSorts == ATempty) {
          deletedSorts = ATempty;
          return;
          }
      deletedSorts = MCRLgetAllSorts();
      for (;!ATisEmpty(definedSorts);definedSorts = ATgetNext(definedSorts)) { 
          ATermList deletedSorts0 = 
          ATremoveElement(deletedSorts,ATgetFirst(definedSorts));
          if (ATisEqual(deletedSorts, deletedSorts0)) 
             ATerror("Argument %t of -sort is not an existing sort",
                      ATgetFirst(definedSorts));
           deletedSorts = deletedSorts0;
          }
      }
                
int main(int argc, char *argv[]) { 
    int i, j = 0, n;
    char **newargv = (char**) calloc(argc + 2, sizeof(char*));
    if (!newargv) {
        fprintf(stderr,"Cannot allocate array argv");
        exit(1);
        }  
    newargv[j++] = argv[0];newargv[j++]="-abstract";
    ATinit(argc, argv, (ATerm*) &argc);
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    ATprotect((ATerm*) &deletedSorts);ATprotect((ATerm*) &definedSorts);
    definedSorts = ATempty;
    for (i=1;i<argc;i++) {
	help(argv[i]);
	if (!strcmp(argv[i],"-version")) {
	    version();
	    exit(0);
	    }
   if (!strcmp(argv[i],"-split")) {
	    split = ATtrue;
            continue;
	    }
   if (!strcmp(argv[i],"-finite")) {
	    finite = ATtrue;
            continue;
	    }
   if (!strcmp(argv[i],"-report")) {
	    report = ATtrue;
            continue;
	    }
   if (!strcmp(argv[i],"-sort")) {
	    if ((++i)<argc && strncmp(argv[i],"-",1)) {
                definedSorts = ATinsert(definedSorts,ATmake("<str>",argv[i])); 
                }
	    else
		ATerror("Name of sort expected after %s\n",argv[i-1]);
	    continue;
	    }   
       newargv[j++] = argv[i];
	}
    STsetArguments(&j, &newargv);
    if (!MCRLinitRW(j, newargv)) exit(1);
    n = ATgetLength(MCRLgetListOfSummands());
    DeletedSorts(definedSorts);
    if (!split) {
        Initialize();
        STinitialize(order, &label, dest, CallBack); 
        if (FirstStep()<0) ATerror("Cannot decluster");
        MCRLsetProc(ATmake("initprocspec(<term>,<term>,<term>)",
       (ATerm) RWrewriteList((ATermList) MCRLgetListOfInitValues()), 
        MCRLgetListOfPars(), (ATerm) IdemPotentSums(sums)));
        }
    else {
        RWdeclareVariables(MCRLgetListOfPars());
        MCRLsetListOfSummands(Split(MCRLgetListOfSummands()));
        }
    MCRLoutput();
    ATwarning("Input  %d summands _ Output %d summands", 
               n, nWrittenSummands);
    exit(EXIT_SUCCESS);
    }
          
