/* $Id: tbfupdate.c,v 1.9 2005/09/12 13:56:54 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdio.h>
#include "rw.h"
#include "edit.h"

typedef struct {
     ATerm lhs, rhs;
     ATerm* cond;
     int len;
     } match_t;

static match_t *match;
static ATermList protect = NULL;
     
static char *who = "tbfupdate";
static FILE *editfile = NULL;

static int match_size, cnt, newcnt = 0, updcnt = 0, monitor = 0,
deltacnt = 0, delta_elm = 1, updateCond = 0;

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
     
static void helpmsg(ATbool all) {
    Pr("Usage: tbfupdate [options] [input file]");
    Pr("The following options can be used");
    Pr("-help:\t\tyields this message");
    Pr("-version:\tgets the version number of this release");
    Pr("-edit <file>:");
    Pr("\t\t<file> contains the conditional substitution rules.");
    Pr("\t\tThe format of a rule is:");
    Pr("\t\t<match_action_term>'->'<new_action_term> ['<|'<condition_terms>]");
    Pr("\t\t<condition_terms>::=<condition_term> ('&'<condition_term>)*");
    Pr("\t\t<condition_term>::=<matching variable>'='<term>");
    Pr("\t\tUnknown variables in the match_action_term will be interpreted");
    Pr("\t\tas matching variables. The matched subterm will be assigned");
    Pr("\t\tto them in the matching phase. These variables can be used in");
    Pr("\t\t<new_action_term> and <condition_terms>.");
    Pr("\t\tThe first encountered match will be applied."); 
    Pr("\t\tIf the matching rule has a condition then");
    Pr("\t\ta second summand will be generated in which its guard is");
    Pr("\t\ta conjunction with the previous guard and the negated condition.");
    Pr("\t\tFile \"abp.edt\" contains an example.");
    Pr("-cond:\t\tConditions will be replaced by fresh functions. Extra rewrite rules");
    Pr("\t\tare added. Sometimes this optimizes the generation of the state space.");
    Pr("-delta:\t\tDoesn't eliminate summands with action \"delta\"");
    Pr("-monitor:\tdisplays updates during run");
    if (all) {
      MCRLhelp();
      /* RWhelp(); */
      }
    } 
        
static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("Renaming of actions directed by conditional substitution rules.");
    Pr("The updated \".tbf\" file will be written on stdout.");
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    exit(EXIT_SUCCESS);
    }
        
static void version(void)
    {
    char buf[100];
    sprintf(buf,"%s: version %s",who, VERSION);
    Pr(buf);
    }


    
static void FillTable(ATermList ts) {
    int i = 0;
    match_size = ATgetLength(ts);
    match = calloc(match_size, sizeof(match_t));
    if (!match) ATerror("Cannot allocate match (%d)", match_size);
    for (i=0;!ATisEmpty(ts);ts=ATgetNext(ts), i++) {
        ATerm t  = ATgetFirst(ts);
        int n = ATgetArity(ATgetAFun(t))-2, j;
        match[i].lhs = ATgetArgument((ATermAppl) t, 0);
        match[i].rhs = ATgetArgument((ATermAppl) t, 1);
        match[i].len = n;
        if (n>0) {
           match[i].cond = malloc(n*sizeof(ATerm));
           for (j=0;j<n;j++) match[i].cond[j] = ATgetArgument((ATermAppl) t, j+2); 
           }
        }
    }

static AFun Match(ATermTable db, ATerm p, ATerm t) {
    int i, n = ATgetArity(ATgetAFun(p));
    DECLA(AFun, a, n);
    if (n==0) {
        AFun p1 = MCRLextendSymbol(NULL,0, ATgetName(ATgetAFun(p)));
        if (MCRLgetType(p1)==MCRLvariable) 
           ATerror("Forbidden to use process variable %t in matching term:", p);
        {
        AFun s = MCRLgetSortSymbol(p1);
        if (s==0) {
             /* ATwarning("pt = %a = %t %a", p1, t, MCRLgetSort(t)); */
             ATtablePut(db, p, t);
             return MCRLgetSort(t); 
             }
        if (p1==ATgetAFun(t)) return s;
        return 0;
        }
        }
    if (n != ATgetArity(ATgetAFun(t))) return 0;
    for (i=0;i<n;i++)  
    if ((a[i] = Match(db, ATgetArgument((ATermAppl) p, i),
                          ATgetArgument((ATermAppl) t, i)))==0) 
                return 0;
    {
    AFun p1 = MCRLextendSymbol(a , n, ATgetName(ATgetAFun(p)));
    /* ATwarning("pt = %a = %t", p1, t); */
    if (p1==ATgetAFun(t)) return MCRLgetSortSymbol(p1);
    }
    return 0;
    }
    
static ATerm Subs(ATermTable db, ATerm t) {
     int i, n = ATgetArity(ATgetAFun(t));
     DECLA(AFun, a, n); DECLA(ATerm, b, n);
     if (n==0) {
        AFun t1 = MCRLextendSymbol(NULL,0, ATgetName(ATgetAFun(t)));
        if (MCRLgetType(t1)==MCRLvariable) 
           ATerror("Forbidden to use process variable %t in substitution term:", t);
        {
        AFun s = MCRLgetSortSymbol(t1);
        if (s==0) {
             return ATtableGet(db, t); 
             }
        return (ATerm) ATmakeAppl0(t1);
        }
        }
     for (i=0;i<n;i++) {
          b[i] = Subs(db,  ATgetArgument((ATermAppl) t, i)); 
          a[i] = MCRLgetSort(b[i]);
          }
     {
     AFun t1 = MCRLextendSymbol(a , n, ATgetName(ATgetAFun(t)));
     if (MCRLgetSortSymbol(t1)==0) 
          ATerror("Function %a is not declared", t1);
     return (ATerm) ATmakeApplArray(t1, b);
     }
     }
     
static ATerm EqFunction(match_t *match, ATermTable db, int i) {    
     ATerm d = ATtableGet(db, match->cond[i]),
     t = MCRLtranslate(match->cond[i+1]);
     if (!d) ATerror("Matching variable %t doesn't exist", match->cond[i]);
     if (!t) ATerror("Term %t has not a valid sort",  match->cond[i+1]);
     {
     ATerm c = MCRLmakeEq(d, t);
     if (c==NULL) 
     ATerror("Illegal use of eq function (args: %t:%a %t:%a)", 
          MCRLprint(d), MCRLgetSort(d), 
          MCRLprint(t), MCRLgetSort(MCRLtranslate(t)));
     /* ATwarning("c = %t", c); */
     return c;
     }
     }
     
static ATerm NewAction(match_t *match, ATerm action, ATerm *cond)  {
    *cond = NULL;
    if (ATgetAFun(match->lhs)!=ATgetAFun(action)) return NULL;
    {
    static ATermTable db = NULL;
    int n = ATgetArity(ATgetAFun(action)), i;
    DECLA(int, a, n); 
    if (db) ATtableReset(db);
    else db  = ATtableCreate(100,50);
    if (n==0) {
        return match->rhs;
        }
    for (i=0;i<n;i++) 
    if ((a[i] = Match(db,  ATgetArgument((ATermAppl) match->lhs, i),
                           ATgetArgument((ATermAppl) action, i)))==0)
    return NULL;
    if (match->len>1) {
        *cond = EqFunction(match, db, 0);
        for (i=2;i<match->len;i+=2)
          *cond = MCRLmakeAnd(*cond, EqFunction(match, db, i));
        }
    n = ATgetArity(ATgetAFun(match->rhs));
    {
    DECLA(ATerm, b, n);
    if (n==0) {
        if (ATtableGet(db, match->rhs)) 
           ATerror("Matching variable %t not permitted in this location", 
        match->rhs);
        return match->rhs;
        }
    for (i=0;i<n;i++) b[i] = 
             Subs(db, ATgetArgument((ATermAppl) match->rhs, i)); 
    return (ATerm) ATmakeApplArray(ATgetAFun(match->rhs), b);
    }
    }
    } 
       
ATerm UseFirstMatchingRule(int *from, ATerm action, ATerm *cond) {
     *cond = NULL;
     for (;*(from)<match_size;(*from)++) {
        ATerm t = NewAction(match+ (*from), action, cond);
        /* if (ATgetAFun(action)== ATmakeSymbol("c2",4, ATtrue))
              ATwarning("%t =?= %t", match[*from].lhs, action); */ 
        if (t!=NULL) return t;
        /*if (ATgetAFun(action)== ATmakeSymbol("c2",4, ATtrue)) 
            ATwarning("no"); */
     }
     return action;
     }
    
static ATerm Action(ATerm actname, ATermList  actargs) {
      return 
      (ATerm) ATmakeApplList(
      ATmakeAFun(ATgetName(ATgetSymbol(actname)),ATgetLength(actargs), ATtrue),
      actargs);
      }
           
static ATbool Transform(void) {
    ATerm proc = MCRLgetProc();
    ATermList sums = MCRLgetListOfSummands(),
    pars = MCRLgetListOfPars();
    ATermList newsums = ATmakeList0();
    for (cnt=0;!ATisEmpty(sums);sums=ATgetNext(sums),cnt++) {
         ATerm sum = ATgetFirst(sums), newsum = NULL;
         int from = -1;
         MCRLdeclareVars(MCRLgetListOfVars(sum));
         {
         ATermList vars = (ATermList) ATgetArgument((ATermAppl) sum,0);
         ATerm actname = ATgetArgument((ATermAppl) sum, 1);
         ATermList actargs = (ATermList) ATgetArgument((ATermAppl) sum,2);
         ATerm procarg = ATgetArgument((ATermAppl) sum, 3);
         ATerm cond = ATgetArgument((ATermAppl) sum, 4);
         ATerm action = Action(actname, actargs);
         ATerm precond = NULL;
         ATerm pcond0 = NULL, pcond = NULL;
	 int changed =  0, changed2delta = 0;
         do {
            ATerm newaction = 
                (from++,UseFirstMatchingRule(&from, action, &precond));
	    /* precond == NULL and newaction == action if no matching rule is 
	       found */
            actargs = ATgetArguments((ATermAppl) newaction);
            actname = (ATerm) ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(newaction)),
                  0, ATtrue));
            if (!ATisEqual(newaction, action) || !ATisEqual(pcond, pcond0)) {
                 pcond0 = pcond;
		 changed = 1;
                 if (precond) {
                     pcond = (pcond0?MCRLmakeAnd(precond, pcond0):precond);
                     }
                 if (delta_elm && ATisEqual(newaction,MCRLterm_delta)) {
		     changed2delta = 1;
                     if (monitor) 
                        ATwarning("smd %d: %t -> %t <| %t (summand deleted)", 
                        cnt+1, MCRLprint(action), MCRLprint(newaction),
                        pcond?MCRLprint(pcond):MCRLprint(MCRLterm_true));
                     }
		  else {
                  /*ATwarning("Success actname %t arctargs %t cond = %t", actname, actargs,
                  precond?precond:(ATerm) ATempty); */
                  if (monitor) 
                      ATwarning("smd %d: %t -> %t <| %t", 
                      cnt+1, MCRLprint(action), MCRLprint(newaction),
                         pcond?MCRLprint(pcond):MCRLprint(MCRLterm_true));
		      }
		  }
	     if (!delta_elm || !ATisEqual(newaction,MCRLterm_delta)) {
                 newsum = ATmake("smd(<term>,<term>,<term>,<term>,<term>)",vars, actname,
                 actargs,procarg, pcond?MCRLmakeAnd(pcond, cond):cond);
                 newsums = ATinsert(newsums, newsum); newcnt++;
		 }
            if (precond) pcond = (pcond0?MCRLmakeAnd(MCRLmakeNot(precond), pcond0)
                     :MCRLmakeNot(precond));
            } while (from<match_size && precond);
	    if (changed) updcnt++;
	    if (changed2delta) deltacnt++;
         }
         }
    MCRLsetProc(ATmake("initprocspec(<term>,<term>,<term>)",
    MCRLgetListOfInitValues(), pars, (ATerm) ATreverse(newsums)));
    return !ATisEqual(MCRLgetProc(), proc);      
    }

ATermList sieve(ATermList vs, ATermList rs) {
    ATermList r = ATempty;
    /* ATwarning("rs = %t", rs); */
    for (;!ATisEmpty(vs);vs=ATgetNext(vs)) 
    if (ATindexOf(rs, ATgetFirst(vs), 0)<0) r = ATinsert(r, ATgetFirst(vs));
    /* ATwarning("r = %t", r); */
    return ATreverse(r); 
    }
        
static void AddRewriteConditions(void) {
     ATermList sums = MCRLgetListOfSummands(), newSums = ATempty;
     int nSummands = ATgetLength(sums), k=0;
     static char buf[40], *bufpt;
     sprintf(buf,"%s","c-");
     bufpt = buf + strlen(buf);
     for (;!ATisEmpty(sums);sums=ATgetNext(sums),k++) {
         ATerm sum = ATgetFirst(sums);
         ATerm cond = ATgetArgument((ATermAppl) sum, 4);
         ATerm map; AFun mapfun;
         int n, i;
         ATermList vs = MCRLgetListOfVars(sum), vs0;
         ATbool _new;
         MCRLdeclareVars(vs);
         vs = ATconcat(MCRLgetListOfPars(), MCRLgetListOfVars(sum));
         vs =  sieve(vs, MCRLremainingVars(cond, vs));
         vs0 = vs;
         n = ATgetLength(vs);
         {
         DECLA(ATerm, a, n); DECLA(ATerm, b, n);
         for (i=0;i<n;i++, vs = ATgetNext(vs)) {
           a[i] = ATgetArgument((ATermAppl) ATgetFirst(vs) , 1);
           b[i] = ATgetArgument((ATermAppl) ATgetFirst(vs) , 0);
           }
         sprintf(bufpt,"%d", k);
         mapfun = ATmakeAFun(buf, n, ATtrue);
         map = (ATerm) ATmakeApplArray(mapfun, a);
         mapfun = MCRLputMap(map, MCRLterm_bool, &_new);
         /* ATwarning("mapfun %d", mapfun); */
         if (mapfun>0) {
             ATerm lhs = (ATerm) ATmakeApplArray(mapfun, b),
                   eq = ATmake("<appl(<term>,<term>,<term>)>",
                       "e", vs0, lhs, cond);
             /* ATwarning("Hallo %t", eq); */
             MCRLputEquation(eq, &_new);
             newSums = ATinsert(newSums, 
                (ATerm) ATsetArgument((ATermAppl) sum, lhs, 4));
             }
         else ATerror("Change in summand %d is not permitted", k);
         }
         MCRLsetListOfSummands(ATreverse(newSums));
         }
     }
                        
int main(int argc, char *argv[]) {
    int i, j = 0;
    char **newargv = (char**) calloc(argc + 2, sizeof(char*));
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0]; 
    ATinit(argc, argv, (ATerm*) &argc);
    for (i=1;i<argc;i++) {
    help(argv[i]);
    if (!strcmp(argv[i],"-version")) {
	version();
	exit(0);
	}
    if (!strcmp(argv[i],"-monitor")) {
	monitor = 1;
	continue;
	}
    if (!strcmp(argv[i],"-delta")) {
	delta_elm = 0;
	continue;
	}
    if (!strcmp(argv[i],"-cond")) {
	updateCond = 1;
	continue;
	}
    if (!strcmp(argv[i],"-edit")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *name = argv[i];
                if (editfile) ATerror("flag -edit already present");
                editfile = fopen(name,"r");
                if (!editfile) ATerror("Cannot open file %s", name);
                continue;
                }
            ATerror("Option %s needs argument.\n",argv[i-1]);
            }
    newargv[j++] = argv[i];
    }
    /*
    if (!editfile) {
            help("help");
            ATerror("Flag -edit <file_name> must be present");
            }
     */
    {if (!MCRLinitOnly(j, newargv)) exit(EXIT_FAILURE);}
    MCRLdeclareVars(MCRLgetListOfPars());
    if (editfile) {
        ATprotect((ATerm*) &protect);
        protect = ParseFile(editfile);
        /* ATwarning("proftect = %t", protect); */
        FillTable(protect); 
        Transform();
        ATwarning("Read %d summands",  cnt);
        ATwarning("Updated %d summands",  updcnt);
        if (deltacnt>0) ATwarning("(Of which updated to delta: %d summands)",  deltacnt);
        ATwarning("Written %d summands", newcnt);
        }
    if (updateCond) {
        AddRewriteConditions();
        }
    MCRLoutput();
    exit(EXIT_SUCCESS); 
    }
