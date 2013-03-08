/* $Id: critpairs.c,v 1.2 2005/11/10 16:11:47 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdio.h>
#include <string.h>
#include "rw.h"
#include "unification.h"
#define P(msg)  fprintf(stderr,"%s\n",msg)

static char *who = "Critpairs";
static ATermList functions = NULL;
static ATermStack sigma, subterms, eqs1, eqs2, subterm2rule;
static ATermTable db, compose = NULL;
static int nvars = 0;
static ATermTable idx;
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
    P("Usage: critpairs [options] [input file]");
    P("");
    P("The following options can be used");
    P("-help:\t\tyields this message");
    P("-version:\tgets the version number of this release");
    P("-compose:\tadds new rewrite rules which is the composition of two");
    P("\t\texisting rewrite rules. The rewrite system must be confluent.");
    P("Prints numbers of overlapping rewrite rules");
    P("and its critical pairs");
    // MCRLhelp();
    }
    
static void help(void)
    {
    P("");
    helpmsg();
    P("");
    P("");
    }

static void version(void)
    {
    char buf[100];
    sprintf(buf,"%s: version %s",who, VERSION);
    P(buf);
    }
#undef P

static ATerm ApplyRule(ATerm s_lhs, ATerm s_redex, ATerm s_rhs) {
    int n = ATgetArity(ATgetAFun((ATermAppl) s_lhs)), i;
    if (ATisEqual(s_lhs, s_redex)) return s_rhs;
    if (n>0) {
    ATerm *b = alloca(n*sizeof(ATerm));
    for (i=0;i<n;i++) b[i] = ApplyRule(ATgetArgument((ATermAppl) s_lhs, i),
       s_redex, s_rhs);
       return (ATerm) ATmakeApplArray(ATgetAFun(s_lhs), b);
       }
    return s_lhs;
    }
    
static ATerm RenameBackTerm(ATerm t, ATermList vs1, ATermList vs2) {
    if (ATgetType(t)==AT_INT) {
        int n = ATgetInt((ATermInt) t);
        return  n<nvars?ATgetArgument((ATermAppl) ATelementAt(vs1, n), 0)
                       :ATgetArgument((ATermAppl) ATelementAt(vs2, n-nvars),0)
                       ;
        }
    if (ATgetArity(ATgetAFun((ATermAppl) t))==0) {
        return t;
        }
    else {
        int n = ATgetArity(ATgetAFun((ATermAppl) t)), i;
        ATerm *b = alloca(n*sizeof(ATerm));
        for (i=0;i<n;i++) 
           b[i] = RenameBackTerm(ATgetArgument((ATermAppl) t, i), vs1, vs2);
        return (ATerm) 
          ATmakeApplArray(ATgetAFun(t), b);
        }
    }
     
static ATerm RenameBackRule(ATerm eq, ATermList vs1, ATermList vs2) {
    return (ATerm) ATmakeAppl3(ATgetAFun(eq), 
           (ATerm) ATempty,
           RenameBackTerm(ATgetArgument((ATermAppl) eq, 1), vs1, vs2),
           RenameBackTerm(ATgetArgument((ATermAppl) eq, 2), vs1, vs2));
    }

static ATermList NewVs(ATermList  vs) {
    ATermList r = ATempty;
    for (;!ATisEmpty(vs);vs=ATgetNext(vs)) {
      char buf[80];
      sprintf(buf,"%s",
      ATgetName(ATgetAFun(ATgetArgument((ATermAppl) ATgetFirst(vs), 0))));
      buf[strlen(buf)-1]='\0';strcat(buf,"_#");
      r = ATinsert(r, ATmake("v(<str>,<term>)", buf,  
           ATgetArgument((ATermAppl) ATgetFirst(vs), 1)));
      }
    return ATreverse(r); 
    }
    
static ATermList Union(ATermList vs1, ATermList vs2) {
    ATermList r = vs1;
    for (;!ATisEmpty(vs2);vs2=ATgetNext(vs2))
    if (ATindexOf(r, ATgetFirst(vs2),0)<0) 
          r = ATinsert(r, ATgetFirst(vs2));
    return ATreverse(r);
    }
    
ATermStack OverLappingTerms(ATerm t1, ATerm t2);
              
static int PrintCriticalPair(int p, int q) {
    int n, r = 0;
    ATbool v;
    ATerm lhs1 = ATgetArgument((ATermAppl)ATstackGet(eqs1, p), 1),
          redex = ATstackGet(subterms, q); // Subterms of eqs2
    
    ATstackReset(sigma);
    // ATwarning("redex:%t", MCRLprint(redex));
    // if (ATgetArity(ATgetAFun(lhs1))==0) return 0;
    v = ATunify(lhs1, redex, sigma); 
    // sigma(lhs1) subterm of lhs2 or (?compose) rhs2
    n = ATstackDepth(sigma);
    if (v && n>0) {
       ATerm rule1 = ATstackGet(eqs1, p),
             rule2 = ATstackGet(subterm2rule, q);
       ATermList vs1 =  (ATermList) ATgetArgument((ATermAppl) rule1, 0),
                 vs2 =  compose?
                 NewVs((ATermList) ATgetArgument((ATermAppl) rule2, 0)):
                      (ATermList) ATgetArgument((ATermAppl) rule2, 0);         
       ATerm rhs1 = ATgetArgument((ATermAppl) rule1, 2),
             rhs2 = ATgetArgument((ATermAppl) rule2, 2);
       ATerm lhs2 = ATgetArgument((ATermAppl) rule2, 1);
       ATerm s_lhs1 =  RenameBackTerm(ATsubstitute(lhs1, sigma),vs1, vs2),
             s_rhs1 =  RenameBackTerm(ATsubstitute(rhs1, sigma),vs1, vs2),
             s_lhs2 =  RenameBackTerm(ATsubstitute(lhs2, sigma),vs1, vs2),
             s_rhs2 = RenameBackTerm(ATsubstitute(rhs2, sigma), vs1, vs2);
       ATerm r_rhs1 = RenameBackTerm(
           ApplyRule((compose?s_rhs1:s_lhs1), s_lhs2, s_rhs2), vs1, vs2);
       int n1 , n2;
       
       rule1 = RenameBackRule(rule1, vs1, vs2);
       rule2 = RenameBackRule(rule2, vs1, vs2);
    RWdeclareVariables(vs1); RWdeclareVariables(vs2);
    n1 = ATindexedSetGetIndex(idx, rule1)+1;
    n2 = ATindexedSetGetIndex(idx, rule2)+1;
    if (compose) {
       ATerm e = ATmake("e(<term>,<term>,<term>)", Union(vs1, vs2), 
       s_lhs1, /*RWrewrite(*/r_rhs1/*)*/);
       /* ATfprintf(stderr, "New rule %d -> %d\n", n1, n2); */
       r = 1; 
       if (ATtableGet(compose, lhs1)==NULL) 
                     ATtablePut(compose, lhs1, e);
       else ATtablePut(compose, lhs1, (ATerm) ATempty);
       /* ATwarning("eq: %t", e); */
       /*
       ATfprintf(stderr,"\t%t\n", MCRLprint(s_lhs1));
       ATfprintf(stderr,"SIGMA(RHS(%d))-%d->\n\t%t\n\n", n2, n1, 
              MCRLprint(r_rhs2));
       */
    } else {
        if (!ATisEqual(RWrewrite(s_rhs1), RWrewrite(r_rhs1))) {
        r = 1;
        ATfprintf(stderr, "Overlapping rules: %d and %d.\n", n2, n1);
        ATfprintf(stderr,"SIGMA(LHS(%d))-%d->\n" , n1, n1);
        ATfprintf(stderr,"\t%t\n", MCRLprint(s_rhs1));
        ATfprintf(stderr,"SIGMA(LHS(%d))-%d->\n\t%t\n", n1, n2, MCRLprint(r_rhs1));
        /* ATfprintf(stderr,"%t != %t\n", MCRLprint(RWrewrite(s_rhs2)), 
                                     MCRLprint(RWrewrite(r_rhs2))); */
        ATfprintf(stderr, "lhs rule %d: %t\n", n2, MCRLprint(
          RenameBackTerm(lhs2, vs1, vs2)));
        ATfprintf(stderr, "lhs rule %d: %t\n", n1, MCRLprint(
             RenameBackTerm(lhs1, vs1, vs2)));                           
        // ATfprintf(stderr,"\t%t=%t\n", MCRLprint(s_lhs1), MCRLprint(s_rhs1));
        ATfprintf(stderr,"\n");
        }
    }
    }
    return r;
    }

static int SubTerms(ATermAppl t, ATerm rule) {
    int n = ATgetArity(ATgetAFun(t)), i;
    static int k = 0, pt = 0, size0 =0;
    static ATerm rule0 = NULL;
    for (i=0;i<n;i++) SubTerms((ATermAppl) ATgetArgument(t,i), rule);
    if (MCRLgetTypeTerm((ATerm) t)!=MCRLvariable) {
       ATstackPush(subterms, (ATerm) t);
       // ATwarning("Problems: %t", rule);
       ATstackPush(subterm2rule, rule);
       }
    return ATstackDepth(subterms)-1;
    }
    

static ATerm RenameTerm(ATerm t) {
    if (ATgetType(t)==AT_INT) 
        return (ATerm) ATmakeInt(ATgetInt((ATermInt) t)+nvars);
    if (ATgetArity(ATgetAFun((ATermAppl) t))==0) {
        return t;
        }
    else {
        int n = ATgetArity(ATgetAFun((ATermAppl) t)), i;
        ATerm *b = alloca(n*sizeof(ATerm));
        for (i=0;i<n;i++) b[i] = RenameTerm(ATgetArgument((ATermAppl) t, i));
        return (ATerm) 
          ATmakeApplArray(ATgetAFun(t), b);
        }
    }

        
static ATerm RenameRule(ATerm eq) {
    return (ATerm) ATmakeAppl3(ATgetAFun(eq), 
           ATgetArgument((ATermAppl) eq, 0),
           RenameTerm(ATgetArgument((ATermAppl) eq, 1)),
           RenameTerm(ATgetArgument((ATermAppl) eq, 2)));
    }
    
static ATermStack SubTerms2(ATermStack subterms, ATerm t) {
    if (!subterms) subterms = ATstackCreate(500);
    if (MCRLgetTypeTerm((ATerm) t)!=MCRLvariable) {
    int n = ATgetArity(ATgetAFun(t)), i;
    ATstackPush(subterms, t);
    for (i=0;i<n;i++) 
        SubTerms2(subterms, ATgetArgument(t,i));
    }
    return subterms;
    }
    
/* Variables in terms must be disjunct */
ATermStack OverLappingTerms(ATerm t1, ATerm t2) {
    ATermStack subterms = SubTerms2(NULL, t1);
    ATbool v = ATfalse;
    ATermStack sigma = ATstackCreate(10);
    /* ATwarning("Found subterms: %d", ATstackDepth(subterms)); */
    while (ATstackDepth(subterms)>0 && !v) {
       ATerm redex = ATstackPop(subterms);
       v = ATunify(redex, t2, sigma);
       }
    if (!v) {ATstackDestroy(sigma); return NULL;}
    return sigma;
    }
                                
int main(int argc, char *argv[]) {
    int i, j = 0, n, m, *a, k, cnt = 0;
    char **newargv = (char**) calloc(argc + 2, sizeof(char*));
    ATermList eqs;
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0]; 
    ATinit(argc, argv, (ATerm*) &argc);
    for (i=1;i<argc;i++) {
    if (!strcmp(argv[i],"-help")) {
	help();
	exit(0);
	}
    if (!strcmp(argv[i],"-version")) {
	version();
	exit(0);
	}
    if (!strcmp(argv[i],"-compose")) {
        compose = ATtableCreate(50,50);
        continue;
	}
    newargv[j++] = argv[i];
    }
    if (!MCRLinitRW(j, newargv)) exit(EXIT_FAILURE);
    ATprotect((ATerm*) &functions);
    functions = MCRLgetAllFunctions();
    sigma = ATstackCreate(10);
    subterms = ATstackCreate(500);
    subterm2rule = ATstackCreate(500);
    eqs1 = ATstackCreate(500); eqs2 = ATstackCreate(500);
    db = ATtableCreate(100,80); idx = ATindexedSetCreate(500, 80);
    eqs = (ATermList) ATgetArgument((ATermAppl) MCRLgetAdt(), 1);
    for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
       ATbool new;
       ATindexedSetPut(idx, (ATerm) ATsetArgument((ATermAppl) 
       ATgetFirst(eqs), (ATerm) ATempty, 0), &new);
       if (!new) {
           ATindexedSetPut(idx, (ATerm) ATmakeInt(k), &new);
           k++;
           }
       }
    for (;!ATisEmpty(functions);functions = ATgetNext(functions)) {
       ATerm f = ATgetFirst(functions);
       {
       // ATwarning("f = %t type = %d type eq = %d", 
       // f, MCRLgetType(ATgetAFun(f)), MCRLeqfunction);
       if (MCRLgetType(ATgetAFun(f))==MCRLeqfunction) continue;
       {
       ATermList rules = MCRLgetRewriteRules(ATgetAFun(f));
       // ATwarning("Test %t\n", rules);
       for (;!ATisEmpty(rules);rules=ATgetNext(rules)) {
            int n = ATgetLength(ATgetArgument((ATermAppl) ATgetFirst(rules),
                0));
            nvars = n>nvars?n:nvars;
            ATstackPush(eqs1, ATgetFirst(rules));
            }
       }
       }
       }
   n = ATstackDepth(eqs1);
   for (i=0;i<n;i++) {
       ATstackPush(eqs2, RenameRule(ATstackGet(eqs1, i)));
       } 
   a = malloc(sizeof(int)*n);
   for (i=0;i<n;i++) {
       ATerm rule = ATstackGet(eqs2, i),
           lhs = ATgetArgument((ATermAppl) rule, 1),
           rhs = ATgetArgument((ATermAppl) rule, 2);
       if (MCRLgetType(ATgetAFun(lhs))==MCRLeqfunction) continue;
         {
         // ATwarning("nvars = %d lhs = %t", nvars, lhs);
         a[i] = SubTerms((ATermAppl) (compose?rhs:lhs), rule);
         }
       }
    m = ATstackDepth(subterms); 
    for (i=0;i<n;i++)
     for (j=0;j<m;j++)
     if (a[i]!=j && PrintCriticalPair(i,j)) cnt++; 
 /* Term not equals to itsself */
    if (compose) {
         ATermList es = ATtableValues(compose);
         ATbool new = ATfalse;int count = 0;
         for (;!ATisEmpty(es);es=ATgetNext(es))
              if (ATgetType(ATgetFirst(es))==AT_APPL) {
                 MCRLputEquation(ATgetFirst(es), &new);
                 count++;
                 }
         MCRLoutput();
         ATwarning("There are %d equations added", count);
         }
    exit(EXIT_SUCCESS); 
    }
