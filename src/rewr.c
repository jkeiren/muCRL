/* $Id: rewr.c,v 1.11 2006/10/06 13:35:36 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "string.h"
#include "rw.h"
#define MCRLLIB
#include "prover.h"
#undef MCRLLIB

static char *who="Rewr", *compile = NULL;

static  unsigned int cnt, newcnt, monitor = 0; 

static ATbool proverFlag = ATfalse, write = ATtrue;

static FILE *invariant;
static ATermList invars = NULL;

static void helpmsg(ATbool all) 
    {
    Pr("Usage: rewr [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\tyields this message");
    Pr("-help-all:\tyields all help information");
    Pr("-version:\tget the version number of this release");
    Pr("-monitor:\tdisplays progressing information");
    Pr("-prover:\tthe conditions will be rewritten using BDD techniques");
    Pr("-compile:\tonly the rewrite system will be compiled and written to");
    Pr("\t\t<input file>.so. The last argument must be <input file>");
    Pr("-no-compile:\t<input file>.so containing the compiled rewrite system");
    Pr("\t\tbelonging to <input file> will be used, instead of generating one.");
    Pr("-invariant <filename>:\tlike -prover, in addition the invariant term");
    Pr("\t\t\twritten in file <invariant> will be used");
    if (all) {
      MCRLhelp();
      RWhelp();
      }
    }
    
static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("This filter reads from input an LPO in tbf format and reduces");
    Pr("it to an LPO which is equivalent to it by rewriting");  
    Pr("all terms of the input LPO."); 
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    exit(1);
    }

static void version(void)
    {
    char buf[100];
    /*
    P("$Id: rewr.c,v 1.11 2006/10/06 13:35:36 bertl Exp $");
    */
    sprintf(buf,"Rewriter: version %s",VERSION);
    Pr(buf);
    }



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
     
static ATerm _ProveCondition(ATerm c) {
       /* Obliged that last branch must be "if (b, T, F)" 
       Invariant will be used at each first argument of "if" */
      ATerm result = c;
      ATermList ts = ATempty;
      while (ATgetAFun(c)==MCRLsym_ite && 
           ATgetArgument((ATermAppl) c, 2) == MCRLterm_false) {
          ts = ATinsert(ts, ATgetArgument((ATermAppl) c, 0));
          c = ATgetArgument((ATermAppl) c, 1);
          }
     if (ATisEmpty(ts)) return result;
     else {
         int n = ATgetLength (ts), i;
         DECLA(ATerm, l, n);DECLA(ATerm, r, n); DECLA(ATerm, s, n);
         ATerm I = MCRLgetInvariant(0);
         for (i=n-1;i>=0;i--, ts = ATgetNext(ts)) 
            l[i] = ATgetFirst(ts);
         for (i=0;i<n;i++) {
            int j, p; 
            for (p = 0, j=n-1;j>=0;j--) 
            if (i!=j) {
                s[p] = 
                   (ATerm) ATmakeAppl3(MCRLsym_ite, l[j], 
                   p>0?s[p-1]:MCRLterm_true,MCRLterm_false);
                   p++;
                }
            r[i] = p>0?s[p-1]:MCRLterm_true;  
         }
         for (i=0;i<n;i++) {
     /* If proven (I and r) -> l  then (c = l and r) will be replaced by r */
            ATerm IandR = (ATerm) ATmakeAppl2(MCRLsym_and, I, r[i]),
            arrow = Prove((ATerm) ATmakeAppl3(MCRLsym_ite, IandR, l[i], 
                 MCRLterm_true));
            /* ATwarning("QQQA %t", MCRLprint(arrow)); */
            if (ATisEqual(arrow, MCRLterm_true)) {
                 return r[i];
                 } 
            }
      return result;
      }
    }
      
static ATerm ProveCondition(ATerm c) {
   ATerm result = NULL;
   while (!ATisEqual(result, c)) {
          result = c;
          c = _ProveCondition(c);
          }
   return result;
   }
         
static ATermList ProveList(ATermList args) {
     ATermList r = ATempty;
     AFun bool = ATgetAFun(MCRLterm_bool);
     for (;!ATisEmpty(args);args=ATgetNext(args)) {
         ATerm arg = ATgetFirst(args);
         r = ATinsert(r, MCRLgetSort(arg)==bool?
             RWrewrite(Prove(arg)):RWrewrite(arg));
         }
     return ATreverse(r);
     }
                                        
static ATbool Reduce(void) {
    ATerm proc = MCRLgetProc();
    ATermList sums = MCRLgetListOfSummands(),
    pars = MCRLgetListOfPars();
    ATermList newsums = ATmakeList0();
     
    if (proverFlag) { 
       Declare_vars(pars);
       if (invariant) MCRLparseInvariants(invariant);
       } 
    else
       RWdeclareVariables(pars);
    for (cnt=0,newcnt = 0;!ATisEmpty(sums);sums=ATgetNext(sums),cnt++) {
         ATerm sum = ATgetFirst(sums), newsum = NULL;
         ATermList vars = (ATermList) ATgetArgument((ATermAppl) sum,0);
         ATerm actname = ATgetArgument((ATermAppl) sum, 1);
         ATermList actargs = (ATermList) ATgetArgument((ATermAppl) sum,2);
         ATerm procarg = ATgetArgument((ATermAppl) sum, 3);
         ATerm cond = ATgetArgument((ATermAppl) sum,4);
         ATbool invariantUsed = ATfalse;
         if (proverFlag) {
            if (!ATisEmpty(vars)) Declare_vars(vars); 
            cond = Prove(cond);
            if (invariant) {
              ATerm cond1 = ProveCondition(cond);
              if (!ATisEqual(cond1, cond)) {
                   invariantUsed = ATtrue;
                   cond = cond1;
                   }
              /* ATwarning("QQQ cond = %t", cond); */
              }
            cond = RWrewrite(cond);
            }
         else {
            if (!ATisEmpty(vars)) RWdeclareVariables(vars);
            cond = RWrewrite(cond);
            }
   /* if (monitor) ATwarning("Condition of summand %d is rewritten", cnt+1); */
         if (ATisEqual(cond, MCRLterm_false)) continue;
         newcnt++;
         actargs = RWrewriteList(actargs);
         if (!ATisEqual(procarg, MCRLterm_terminated)) {
              ATermList states = (ATermList) ATgetArgument((ATermAppl) procarg, 0);
              states = proverFlag?ProveList(states):RWrewriteList(states);
              procarg = (ATerm) ATmakeAppl1(MCRLsym_i, (ATerm) states);
              }
         newsum = ATmake("smd(<term>,<term>,<term>,<term>,<term>)",vars, actname,
              actargs,procarg, cond);
         newsums = ATinsert(newsums, newsum);
         if (monitor && !ATisEqual(sum, newsum)) 
               ATwarning("Summand %d is rewritten %s", cnt+1,
               invariantUsed?"(invariant is used)":""); 
         }
    MCRLsetProc(ATmake("initprocspec(<term>,<term>,<term>)",
    (ATerm) RWrewriteList((ATermList) MCRLgetListOfInitValues()), 
          pars, (ATerm) ATreverse(newsums)));
    return !ATisEqual(MCRLgetProc(), proc);      
    }
     
int main(int argc, char *argv[]) { 
    int i, j = 0, newargc = argc +5, lastadded =0;
    char **newargv = (char**) calloc(newargc, sizeof(char*));
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0];
    ATinit(argc, argv, (ATerm*) &argc);
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    ATprotect((ATerm*) &invars);    
    for (i=1;i<argc;i++) {
	help(argv[i]);
	if (!strcmp(argv[i],"-version")) {
	    version();
	    exit(0);
	    }
	if (!strcmp(argv[i],"-prover")) {
            proverFlag = ATtrue;
	    continue;
	    }
       if (!strcmp(argv[i],"-monitor")) {
	    monitor = 1;
	    continue;
	    }
       if (!strcmp(argv[i],"-compile") || !strcmp(argv[i],"-no-compile")) {
            if (!compile) {
               write = !strcmp(argv[i],"-compile")?ATtrue:ATfalse;
               compile = calloc(256, sizeof(char));
               MCRLsetOutputFile(compile);
               strcpy(compile, argv[argc-1]);
               if (strrchr(compile,'.')) *(strrchr(compile,'.'))='\0';
               strcat(compile,".so");
               {int k;
               for (k=0;k<argc && strcmp(argv[k],"-alt");k++); 
               if (k==argc) { 
                  newargv[j++]="-alt";
                  newargv[j++]="rw";
                  }
               }
               newargv[j++]=write?"-write-so":"-read-so";
               newargv[j++]= compile;
               lastadded = j;
	       }
            continue;
            }
       if (!strcmp(argv[i],"-invariant")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *name = argv[i];
                if (invariant) ATerror("flag -invariant already present");
                proverFlag = ATtrue;
                invariant = fopen(name,"r");
                if (!invariant) ATerror("Cannot open file %s", name); 
                continue;
                }
            ATerror("Option %s needs argument.\n",argv[i-1]);
            }
        j=MCRLcopyOption(newargv, argv, argc, i, j);
	}
    if (lastadded>0 && j==lastadded) 
         ATerror("Last argument must be file name"); 
    if (proverFlag) {
         if (!MCRLinit(&j, &newargv)) exit(-1);
         if (!Init_prover(MCRLgetAdt(), j, newargv)) {
            help("-help");
            exit(1);
            }
         }
    else {
         if (!MCRLinitRW(j, newargv)) exit(-1);
         }
    if (compile) {
         if (write) {
           exit(EXIT_SUCCESS);
           }
         else ATwarning("Compiled rewrite system is read from %s.so", compile);
         }
    Reduce();
    ATwarning("Read %d summands",  cnt);
    ATwarning("Written %d summands", newcnt); 
    MCRLoutput();
    exit(EXIT_SUCCESS);  
    }
	    
