/* $Id: librw.c,v 1.17 2008/04/28 14:14:10 bertl Exp $ */
/* Include file destined for both programs */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include "mcrl.h"

#define MAXLEVEL 3
#define PERLEVEL 2600
#define MAXVARS 512
/*  Include file */

#ifndef OUTPUTTEXT
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdarg.h>
#include <stdlib.h>
#include <dlfcn.h>
#include "tasks.h"
#include <libgen.h>
#define DEFAULT_VAL 0

/*  Must be extern because of dynamic linking */
 
ATerm *rw_varnames = NULL, *rw_substitute =  NULL, *rw_quick =  NULL,
rw_term = NULL;
int rw_n_substitute = 0, rw_number_of_vars = 0, rw_number_per_level = PERLEVEL;
ATermTable rw_db  = NULL;
/*
ATerm *rw_normal;
unsigned int *rw_round;
unsigned int round;

#define RWW_ROUND  10000000 
#define RWW_NORMAL 256
#define RWW_NORMAL1 255
*/

int rw_size = 0, rw_size_s_inv = 0, rw_stop_store = 0;
AFun *rw_s = NULL, *rw_s_inv = NULL,  *rw_leveled_subs[MAXLEVEL];

typedef ATerm (*LOOKUP) (ATerm);
LOOKUP *rw_lookup;
/* End extern variables */
 
static char cmd[256], *c_or_e=NULL;
static char *program = NULL, *makefile = NULL;
static ATbool rw_simple = ATfalse, rw_debug = ATfalse,
verbose = ATfalse, rw_eq = ATtrue, indirect = ATfalse;

#define setOpenTerm(t) (ATsetAnnotation(t, _openTerm, _openTerm))
#define isOpenTerm(t)  (ATisEqual(t,infinite) || ATgetAnnotation(t, _openTerm)!=NULL)

static FILE *fp = NULL;
static ATerm *symTab = NULL, _openTerm = NULL, _dummy = NULL,
*varTab = NULL, anno = NULL, anno2 = NULL;
static AFun pos_sym, eq_sym, default_sym, a_sym, getafun_sym,
normal_sym;
static int cursor = 0, lastvar = 0, hash = 0, hashvar = 1,
optimize  = 0, conditional = 1;  

static ATbool autoCache = ATfalse, reset = ATtrue, rw_case = ATfalse;
static ATermIndexedSet subterms = NULL;
static ATerm adt = NULL, infinite = NULL;

static ATermIndexedSet decl = NULL;

static ATermList initCalls;
static char *rw_read = NULL, *rw_write = NULL, *rw_read_src = NULL;
static char *dyndir = "./";

#define MAXCOLS 80

static int Warning(const char *format, ...) {
   va_list ap;
   va_start(ap, format);
   return 0;
   }

/* Part I output rewrite system */ 
/*    
static void ClearVarsInSymbolTable(ATerm eq) {
     ATermList vars = (ATermList) ATgetArgument((ATermAppl) eq,0);
     for (;!ATisEmpty(vars);vars=ATgetNext(vars)) {
         ATerm var = ATgetFirst(vars);
         AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) var, 0));
         symTab[sym] = NULL;
         }
     }
*/
     
static AFun CreateSymFromFunc(ATerm f) {
     char *name = ATgetName(ATgetAFun(ATgetArgument((ATermAppl) f, 0))); 
     int n = ATgetLength((ATermList) ATgetArgument((ATermAppl) f, 1));
     return ATmakeAFun(name, n, ATtrue);
     }
     
static char *LocationRww(void) {
   char *rwwname = (char*) malloc(256);
   FILE *f;
   strcpy(rwwname,"./Rww");
   if (!(f=fopen("./Rww","r"))&&!(f=fopen("../../src/Rww","r")))
       snprintf(rwwname,256, "%s/%s", LIBEXECDIR, "Rww");
   else {
      snprintf(rwwname, 256, "%s/%s", SRCDIR, "Rww");
      fclose(f);
      }
   return rwwname;
   } 

/*
static int IsLocal(void) {
   FILE *f = fopen("./Rww", "r");
   if (!f) return 0;
   fclose(f);
   return 1;
   } 
*/

static void ClearVarTab(void) {
   int i;
   for (i=0;i<MAXVARS && varTab[i]!=NULL;i++) {
       varTab[i]=NULL;
       }
   }  


             
static void AllocateSymbolTable(void) {
     ATermList eqs = (ATermList) ATgetArgument((ATermAppl) adt,1);
     ATermList sig = (ATermList) ATgetArgument((ATermAppl) adt,0);
     ATermList funcs = (ATermList) ATgetArgument(sig,1), funcs0 = funcs;
     ATermList maps = (ATermList) ATgetArgument(sig,2), maps0 = maps;
     AFun sm = ATmakeAFun("rw_s", 3, ATfalse);
     if (sm > rw_size) rw_size = sm;
     sm = ATmakeAFun("f", 3, ATfalse);
     if (sm > rw_size) rw_size = sm;
     sm = ATmakeAFun("e", 3, ATfalse);
     if (sm > rw_size) rw_size = sm;
     sm = ATmakeAFun("d", 3, ATfalse);
     if (sm > rw_size) rw_size = sm;
     for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs))
           {ATerm eq = ATgetFirst(eqs);
           AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) eq, 1));
           ATermList vars = (ATermList) ATgetArgument((ATermAppl) eq,0);
           if ((int) sym > rw_size) rw_size = sym;
           for (;!ATisEmpty(vars);vars=ATgetNext(vars)) {
                ATerm var = ATgetFirst(vars);
                AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) var, 0));
                if ((int) sym > rw_size) rw_size = sym; 
                } 
           } 
     for (;!ATisEmpty(funcs);funcs=ATgetNext(funcs))
           {ATerm func = ATgetFirst(funcs);
           AFun sym = CreateSymFromFunc(func);
           if ((int) sym > rw_size) rw_size = sym;
           }
     for (;!ATisEmpty(maps);maps=ATgetNext(maps))
           {ATerm map = ATgetFirst(maps);
           AFun sym = CreateSymFromFunc(map);
           if ((int) sym > rw_size) rw_size = sym;
           }
     rw_size++;          
     symTab = (ATerm*) calloc(rw_size, sizeof(ATerm));
     ATprotectArray(symTab, rw_size); 
// ATwarning("ATprotectArray symtab = %d size = %d", symTab, rw_size);
     varTab = (ATerm*) calloc(MAXVARS, sizeof(ATerm));
     ATprotectArray(varTab, MAXVARS);
     ClearVarTab();
     for (funcs = funcs0;!ATisEmpty(funcs);funcs=ATgetNext(funcs))
           {ATerm func = ATgetFirst(funcs);
           AFun sym = CreateSymFromFunc(func);
           symTab[sym] = (ATerm) ATempty;
           }
     for (maps = maps0;!ATisEmpty(maps);maps=ATgetNext(maps))
           {ATerm map = ATgetFirst(maps);
           AFun sym = CreateSymFromFunc(map);
           symTab[sym] = (ATerm) ATempty;
           } 
     if (!_dummy) {
        eq_sym = ATmakeSymbol("==",2, ATfalse);ATprotectSymbol(eq_sym);
        a_sym = ATmakeSymbol("A",2, ATfalse);ATprotectSymbol(a_sym);
	normal_sym = ATmakeSymbol("normal",1, ATfalse);
	ATprotectSymbol(normal_sym);
        getafun_sym = ATmakeSymbol("ATgetAFun",1, ATfalse);
             ATprotectSymbol(getafun_sym);
        pos_sym = ATmakeSymbol("pos",1, ATfalse);ATprotectSymbol(pos_sym); 
        default_sym = ATmakeSymbol("default",2, ATfalse);
                      ATprotectSymbol(default_sym);
        ATprotect((ATerm*) &_openTerm); _openTerm = ATmake("<appl>", "open");
        ATprotect((ATerm*) &_dummy); _dummy = ATmake("<appl>", "dummy");
        ATprotect((ATerm*) &infinite); infinite = ATmake("<appl>", "infinite");
        ATprotect((ATerm*) &anno); anno = ATmake("<appl>", "->");
        ATprotect((ATerm*) &anno2); anno2 = ATmake("<appl>", "|");
        ATprotect((ATerm*) &rw_term); rw_term = ATmake("<appl>", "rw_term");
        }
     subterms = ATindexedSetCreate(100, 70);
     initCalls = ATempty; 
     ATprotect((ATerm*) &initCalls);       
     } 

/*
static ATbool isVariable(ATerm t) {
     AFun sym = ATgetSymbol(t);
     if (ATgetArity(sym)>0) return ATfalse;
     if (symTab[sym]==NULL) return ATtrue;
     if (ATgetType(symTab[sym])==AT_LIST) return ATfalse;
     if (ATgetType(symTab[sym]) == AT_APPL) return ATtrue;
     return ATfalse; 
     }
*/

static ATerm MakeEq(ATerm t1, ATerm t2) {
     return (ATerm) ATmakeAppl2(eq_sym, t1, t2);
}

static ATerm Substitute(ATerm lhs, ATerm t) {
     AFun sym = ATgetSymbol(t);
     int  n = ATgetArity(sym);
     ATerm result = NULL;
     if (MCRLgetTypeTerm(t)<MCRLvariable) { 
        ATwarning("Illegal symbol %a in Right Hand Side of", sym);
        return NULL;
        }      
     if (MCRLgetTypeTerm(t)==MCRLvariable) {
	  int idx = ATgetInt((ATermInt) t);
	  ATerm p = varTab[idx];
          if (!p) ATerror("Illegal variable in rhs: %t",t);
          return setOpenTerm((ATerm) ATgetArgument((ATermAppl) p, 0));
          }
     if (n>0) {
          int i = 0;
          ATbool openTerm = ATfalse;
          DECLA(ATerm, a, n);
          for (i=0;i<n;i++) {
           a[i] = (conditional && ATisEqual(lhs,ATgetArgument((ATermAppl) t, i)))?infinite:
                 Substitute(lhs, ATgetArgument((ATermAppl) t, i));
           if (a[i]==NULL) return NULL;
              openTerm = openTerm || isOpenTerm(a[i]); 
              }
          result = 
            openTerm?setOpenTerm((ATerm) ATmakeApplArray(sym, a)):t; 
          if (!openTerm) {
            ATbool new;
            int ind  = ATindexedSetPut(subterms, t, &new);
            if (ind>lastvar) lastvar = ind;
          }     
          } 
     else {
        ATbool new;
        int ind  = ATindexedSetPut(subterms, t, &new);
        if (ind>lastvar) lastvar = ind;
        result = t;
        } 
     return result;   
}
     
static ATerm Detect(ATerm t, ATermList loc) {
     ATermList args = (ATermList) ATgetArguments((ATermAppl) t),
     newargs = ATempty;
     AFun symbol = ATgetSymbol(t);
     int i=0, j=0, n = ATgetArity(symbol);
     /* ATwarning("Detect %t", t); */
     for (;!ATisEmpty(args);args=ATgetNext(args),j++) {
           ATerm arg = ATgetFirst(args);
           ATermList newloc = ATinsert(loc, (ATerm) ATmakeInt(j));
           if (MCRLgetTypeTerm(arg)!=MCRLvariable) {
               ATerm detect = Detect(arg, newloc);
               newargs = 
                  ATinsert(newargs, MakeEq((ATerm) newloc, detect));
               /* ATwarning("Newargs %t", newargs); */
               }
          if (MCRLgetTypeTerm(arg)==MCRLvariable) {
	       int idx = ATgetInt((ATermInt) arg);
               ATerm p = varTab[idx];
               if (!p) {
                  varTab[idx] = 
                  (ATerm) ATmakeAppl1(pos_sym, (ATerm) newloc);
                  }
               else {
                  newargs = ATinsert(newargs, MakeEq(
                  ATgetArgument(p,0), (ATerm) newloc));
                  }  
               }
           }
     newargs = ATreverse(newargs);
     /* Symbol was already mentioned in switch function */
        args = ATempty;
        for (i=0;i<n;i++) args = ATinsert(args, _dummy);
        if (n>0) {
            args = ATreplace(args, (ATerm) newargs, 0);
            return (ATerm) ATmakeApplList(symbol, args);
            }
     /* ATwarning("Detect result %t", t); */
     return t;
     }

static ATermList Flatten(ATermList  ts, ATermList env, ATermList r) {
     for (;!ATisEmpty(ts);ts=ATgetNext(ts)) {
        ATerm t = ATgetFirst(ts), 
        val = ATgetArgument((ATermAppl)t, 1);
        ATermList loc = (ATermList) ATgetArgument((ATermAppl)t, 0);
        if (ATindexOf(env, (ATerm) loc,0)<0) r = ATinsert(r, t);
        else if (ATgetArity(ATgetAFun(val))>0) {
          r = ATconcat(Flatten((ATermList) 
             ATgetArgument(val , 0), env, r), r);
          }
        }
     return r;
     }
     
static ATerm CompileRule(ATerm eq, ATermList env) {
     ClearVarTab();
     {
     ATerm lhs = ATgetArgument((ATermAppl) eq, 1);
     ATerm rhs = ATgetArgument((ATermAppl) eq, 2);
     ATerm detect = Detect(lhs, ATempty);
     ATerm substitute = Substitute(lhs, ATgetArgument((ATermAppl) eq, 2));
     int arity = ATgetArity(ATgetSymbol(detect));
     if (substitute==NULL) ATerror("%t=%t",MCRLprint(lhs), MCRLprint(rhs));
     if (arity>0) {
        ATermList ts = Flatten((ATermList) ATgetArgument(detect, 0), env, ATempty);
        detect = (ATerm) ATsetArgument((ATermAppl) detect, (ATerm) ts, 0);
        }
     /* ATwarning("CompileRule %t-> %t", eq, detect); */
     {
     return ATmake("e(<term>,<term>)", 
        arity>0? ATgetArgument((ATermAppl) detect,0):(ATerm) ATempty, 
        substitute);
     }
     }
     }

static ATerm Argument(ATerm lhs, ATermList suffix) {
     suffix = ATreverse(suffix);
     for (;!ATisEmpty(suffix); suffix = ATgetNext(suffix)) {
        int n = ATgetInt((ATermInt) ATgetFirst(suffix)), arity;
        if (ATgetType(lhs)==AT_INT) return NULL;
        arity = ATgetArity(ATgetAFun(lhs));
        if (n>=arity) return NULL;
        if (arity==0)  return lhs;
        lhs = (ATerm) ATgetArgument(lhs, n);
        }
     return lhs;
     }
     
static AFun headerSymbol(ATerm lhs, ATermList suffix) {
     ATerm arg = Argument(lhs, suffix);
     int arity;
     if (!arg) return 0;
     if (ATgetType(arg)==AT_INT) return 0;
     arity = ATgetArity(ATgetAFun(arg));
     if (arity==0) return 0;
     return ATgetAFun(arg);
     } 
              


static int compareTerm(ATerm t1, ATerm t2) {
      if (ATgetType(t1)<ATgetType(t2)) return 1;
      if (ATgetType(t1)>ATgetType(t2)) return -1;
      /* ATwarning("CompareTerm %t %t", t1, t2); */
      switch (ATgetType(t1)) {
         case AT_INT: return 0;
         case AT_APPL: return ATgetAFun(t1)-ATgetAFun(t2);
        }
      return 0;
      }

/* [f(a, b ,c), f(a, d, e), f(g, h, i), f(x, 1, 2)] -> 
   [[[f(a, b, c), f(a, d, e)]|(a), [f(g, h, i)]|(g)]|0, f(x,1,2)]

  Classify(List l, Pos pos, Idx idx) {
      anno = 
      arity = GetArity(ATgetFirst(l), pos);
      if (arity==0) return l;
      if (idx>=arity) {
            l = Classify(l, Prepend(idx, pos), 0);
            if (anno) l = ATsetAnnotation(l, anno);
            }
      r = Split(l, pos, idx);
      for l in r && l == list {
          Classify(l, pos, idx+1);
          }
      else remainder = append(remainder, l);
      Classify(remainder, pos, idx+1);
      }
*/ 

static ATermList Reorder(ATermList eqs, ATermList pos) {
     int n = ATgetLength(eqs), i;
     ATerm last = NULL;
     ATermList remainder = ATempty;
     DECLA(ATerm, a, n);
     /* ATwarning("Reorder eqs = %t pos = %t", eqs, pos); */
     for (i = 0;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
         ATerm eq = ATgetFirst(eqs),
               lhs = Argument(ATgetArgument((ATermAppl)eq, 1), pos);
         if (lhs) {
            int j;
            for (j=i-1;j>=0 && 
                 compareTerm(lhs, Argument(
		  ATgetArgument((ATermAppl) a[j], 1), 
		   pos))<0;
                 j--) {
                    a[j+1]=a[j];
                    }
            a[j+1] = eq;
            /* ATwarning("a[%d] = %t", j+1, eq); */
            i++;
            }
         }
     for (eqs = ATempty, i=n-1;i>=0;i--) {
         ATerm lhs = Argument(ATgetArgument((ATermAppl) a[i], 1), pos);
         /* ATwarning("QQQ lhs? %t", lhs); */
         if (ATgetType(lhs) != AT_INT) {
         if (last == NULL || compareTerm(lhs, last)) {
            if (!ATisEmpty(eqs)) 
                eqs = ATinsert(ATgetNext(eqs),
                    ATsetAnnotation(ATgetFirst(eqs), anno, last));
            last = Argument(ATgetArgument((ATermAppl) a[i], 1), pos);
            eqs = ATinsert(eqs, (ATerm) ATmakeList1(a[i]));
            }
         else eqs = ATinsert(ATgetNext(eqs), (ATerm)
                    ATinsert((ATermList) ATgetFirst(eqs), a[i]));
                    
         } 
         else remainder = ATinsert(remainder, a[i]);
         }
     if (!ATisEmpty(eqs)) 
         eqs = ATinsert(ATgetNext(eqs),
         ATsetAnnotation(ATgetFirst(eqs), anno, last));
     /* ATwarning("QQQ eqs = %t remainder %t", eqs, remainder); */
     return 
          (ATisEmpty(eqs)?remainder:ATinsert(remainder,
          ATsetAnnotation((ATerm) eqs, anno2, (ATerm) pos)));
     }

static ATermList Classify(ATermList eqs, ATermList poss, ATermList env);

static ATermList Explore(ATermList ts0, ATermList pos) {
      ATermList r = ATempty;
      int i;
      for (i=0;i<100000;i++) {
         ATermList pos1 = ATinsert(pos, (ATerm) ATmakeInt(i)), ts;
         ATbool found = ATfalse;
         for (ts = ts0;!ATisEmpty(ts);ts = ATgetNext(ts)) {
           ATerm t = ATgetFirst(ts);
           ATerm a = Argument(ATgetArgument((ATermAppl) t,1), pos1);
           if (a) {
             found = ATtrue;
             if (ATgetType(a)==AT_APPL) {
                r = ATinsert(r, (ATerm) pos1);
                break;
                }
           }
         }
         if (!found) break;
        }
      return ATreverse(r);
      }

static ATermList Positions(ATermList ts) {
       ATermList queu = ATmakeList1((ATerm) ATempty); /* Initial state */
       ATermList r = ATempty;
       while (!ATisEmpty(queu)) {
           ATermList pos = (ATermList) ATgetFirst(queu);
           ATermList poss = Explore(ts, pos);
           queu = ATgetNext(queu);
           queu = ATconcat(queu, poss);
           r = ATconcat(r, poss);
           }
       return r;
       }
            
static ATermList Divide(ATermList eqs, ATermList poss, ATermList env) {
     if (ATgetLength(eqs)<=0) return eqs;
     {
     ATermList remainder = eqs, r = ATempty;
     if (ATgetType(ATgetFirst(eqs))==AT_LIST) {
       remainder = ATgetNext(eqs);
       eqs = (ATermList) ATgetFirst(eqs);
       {
       ATerm label2 = ATgetAnnotation((ATerm) eqs, anno2);
       if (label2) {
       for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
              ATermList eq = (ATermList) ATgetFirst(eqs);
	      /* ATwarning("Divide1 %t", eq); */
              r = ATinsert(r, (ATerm) Classify((ATermList) eq, poss, env)); 
             }
           r = ATreverse(r); 
           r = (ATermList) ATsetAnnotation((ATerm) r, anno2, label2);
           } 
          } 
        }
      return ATisEmpty(r)? Classify(remainder, poss, ATgetNext(env)) :
          ATinsert(Classify(remainder, poss, ATgetNext(env)), (ATerm) r);
      }
      }
             
static ATermList Classify(ATermList eqs, ATermList poss, ATermList env) {
      if (ATisEmpty(poss)) {
           ATermList r = ATempty;
           ATerm label = ATgetAnnotation((ATerm) eqs, anno), 
                 label2 = ATgetAnnotation((ATerm) eqs, anno2);
           for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
              /* ATwarning("CompileRule: %t env = %t", eqs, env);*/
                r = ATinsert(r, CompileRule(ATgetFirst(eqs), env));
              }
           r = ATreverse(r);
           if (label) r = (ATermList) ATsetAnnotation((ATerm) r, anno, label);
           if (label2) r = (ATermList) ATsetAnnotation((ATerm) r, anno2, label2);
           return r;
           }
      {
      ATermList  pos = (ATermList) ATgetFirst(poss);
      if (ATisEmpty(eqs)) return eqs;
          {
          ATerm lhs = Argument(
                ATgetArgument((ATermAppl) ATgetFirst(eqs), 1), pos);
	  if (!lhs) {
	       /*
               ATermList r = ATempty;
               ATerm label = ATgetAnnotation((ATerm) eqs, anno), 
                     label2 = ATgetAnnotation((ATerm) eqs, anno2);
               for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
                    r = ATinsert(r, CompileRule(ATgetFirst(eqs), env));
                  }
               r = ATreverse(r);
               if (label) r = (ATermList) ATsetAnnotation((ATerm) r, anno, label);
               if (label2) r = (ATermList) ATsetAnnotation((ATerm) r, anno2, label2);
	       */
               return Classify(eqs, ATgetNext(poss), env);
               }
          {
             ATerm label = ATgetAnnotation((ATerm) eqs, anno), 
             label2 = ATgetAnnotation((ATerm) eqs, anno2);
	  eqs = Reorder(eqs, pos); 
	  /* ATwarning("Divide? eqs = %t", eqs); */
	  eqs = Divide(eqs, ATgetNext(poss), ATinsert(env, ATgetFirst(poss)));
          if (label) eqs = (ATermList) ATsetAnnotation((ATerm) eqs, anno, label);
          if (label2) eqs = (ATermList) ATsetAnnotation((ATerm) eqs, anno2, label2);
          return eqs;
      }
      }
      }
     } 
        	

     
/* f(x,g(x, y)) = h(x) will be stored in symTab[f] as
            [e([[1]=g([[0,0]=[0]], _dummy)], h([0])), default([],f([0],[1])]
   f(x,g(y, x)) = h(y) will be stored in symTab[f] as
            [e([[1]=g([[0,1]=[0]], _dummy)], h([0,1])), default([],f([0],[1])]
   f(x,g) = h(x) will be stored in symTab[f] as
            [e([[1]=g()], h([0])),default([],f([0],[1]))]
            
   [a,b] are position numbers of arguments, left the arg. pos on highest level,
   right the arg. pos on lowest level. From this data structure can be 
   generated easily code. "dummy" is needed to make have the symbol the
   right number of arguments
   
   [e([[1]=g([[0,0]=[0]], _dummy)], h([0])), 
      e([[1]=g([[0,1]=[0]], _dummy)], h([0,1]))] ->
   [[[1]=g([e([[0,0]=[0]],h([0])),e([[0,1]=[0]],h([0,1]))], _dummy)],
   default([],f([0],[1])]
*/

static int IsEqualFunction(AFun sym) {
     return rw_eq && MCRLgetType(sym)== MCRLeqfunction  && 
     MCRLisPureConstructorSort(
         ATgetAFun(ATgetArgument((ATermAppl) MCRLgetFunction(sym), 0)));
     }
     
static void ComputeSymbolTable(void) {
     ATermList fs = MCRLgetAllFunctions();
     for (;!ATisEmpty(fs);fs=ATgetNext(fs)) {
        ATerm f = ATgetFirst(fs);
        AFun sym = ATgetAFun(f);
        ATermList eqs = MCRLgetRewriteRules(sym);
        if (!rw_simple && !IsEqualFunction(sym)) { 
                 ATermList poss;
                 /* ATwarning("sym %a", sym); */
                 poss = Positions(eqs);
                 /* ATfprintf(stderr,"Positions %t\n", poss); */
                 symTab[sym] = (ATerm) Classify(eqs, poss, ATempty);
                 // ATfprintf(stderr,"Classify? %t\n", symTab[sym]); 
                 }
        else  {
           for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
              ATerm eq = ATgetFirst(eqs);
              AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) eq, 1));
              symTab[sym] = (ATerm) ATinsert((ATermList) symTab[sym], 
                    CompileRule(eq, ATempty));
             // ATfprintf(stderr,"%t\n", symTab[sym]);
              ClearVarTab(); 
              }
           symTab[sym] = (ATerm) ATreverse((ATermList) symTab[sym]);
           }
        }
     Warning("QQ: End Compute Symbol Table");  
     }
     
static ATerm DefaultRhs(AFun sym) {
     ATermList r = ATempty;
     ATerm result = NULL;
     int n = ATgetArity(sym), i = 0;
     for (i=n-1;i>=0;i--) r = ATinsert(r, (ATerm) ATmakeList1(
           (ATerm) ATmakeInt(i))); 
     result =  (ATerm) ATmakeApplList(sym, r); 
     if (n>0) result = setOpenTerm(result);
     else {
          ATbool new;
          int ind  = ATindexedSetPut(subterms, result, &new);
          if (ind>lastvar) lastvar = ind;
          }
     return result;   
     }
     
static void AddDefaultRules(void) {
     int i;
     for (i=0;i<rw_size;i++) {
      
     if (symTab[i] && ATgetType(symTab[i])==AT_LIST)
         symTab[i] = (ATerm) ATinsert((ATermList) symTab[i], 
           (ATerm) ATmakeAppl2(default_sym, (ATerm) ATempty, DefaultRhs(i))
           );      
           } 
     }
     
static int P(const char *format, ...) {
   int r  = 0;
   va_list ap;
   va_start(ap, format);
   if (format[0]=='\n') cursor = 0;
   if (cursor>= MAXCOLS) {fprintf(fp,"\n"); cursor = 0;} 
   r = ATvfprintf(fp, format, ap);
   /* ATwarning("r = %d cursor = %d", r, cursor); */
   cursor += r;
   if (format[strlen(format)-1]=='\n') cursor = 0;
   return r;
   }
   
   
static int PRappl(AFun sym) {
   int arity = ATgetArity(sym);
   if (indirect) {
   switch (arity) {
   case 0: return P("(ATerm) ATmakeAppl0(rw_s_inv[%d]",rw_s[sym]);
   case 1: return P("(ATerm) ATmakeAppl1(rw_s_inv[%d],",rw_s[sym]);
   case 2: return P("(ATerm) ATmakeAppl2(rw_s_inv[%d],",rw_s[sym]);
   case 3: return P("(ATerm) ATmakeAppl3(rw_s_inv[%d],",rw_s[sym]);
   case 4: return P("(ATerm) ATmakeAppl4(rw_s_inv[%d],",rw_s[sym]);
   case 5: return P("(ATerm) ATmakeAppl5(rw_s_inv[%d],",rw_s[sym]);
   case 6: return P("(ATerm) ATmakeAppl6(rw_s_inv[%d],",rw_s[sym]);
   default: return P("(ATerm) ATmakeAppl(rw_s_inv[%d],",rw_s[sym]);
   }
   } else {
   switch (arity) {
   case 0: return P("(ATerm) ATmakeAppl0(%d",sym);
   case 1: return P("(ATerm) ATmakeAppl1(%d,",sym);
   case 2: return P("(ATerm) ATmakeAppl2(%d,",sym);
   case 3: return P("(ATerm) ATmakeAppl3(%d,",sym);
   case 4: return P("(ATerm) ATmakeAppl4(%d,",sym);
   case 5: return P("(ATerm) ATmakeAppl5(%d,",sym);
   case 6: return P("(ATerm) ATmakeAppl6(%d,",sym);
   default: return P("(ATerm) ATmakeAppl(%d,",sym);
   }
   }    
}

static char *Fname(char *prefix, AFun symbol) {         
   static char buffer[256];
   char *bufpt = buffer;
   char *name = strdup(ATgetName(symbol)), *sep = "?-#\"'$@!~`;.\\|*/^";
   int n = strcspn(name,sep), k = 0;
   if (n==0) name[0]='_';
   n = strcspn(name, sep);
   k+=sprintf(buffer,"%s_%d_",prefix, indirect?rw_s[symbol]:symbol);
   bufpt = bufpt + k;
   n =  k+n<255?n:255-k;
   strncpy(bufpt, name,n);
   bufpt[n]='\0';
   return buffer;   
   } 
     
static void PRheader(AFun symbol) {
   int n = ATgetArity(symbol), i =0;
   P("/* %s (arity %d) */\n", ATgetName(symbol), n);  
   P("static ATerm %s(", Fname(c_or_e, symbol));
   if (n==0) P("void)");
   else {
      for (i=0;i<n;i++) P("%sATerm arg%d", i==0?"":",",i);
      P(")");
      }
   }
   
static void PRheaderD(AFun symbol) {
   P("static ATerm %s(",  Fname("D", symbol));
   P("ATerm t)");
   }
   
static void PRauxVars(void) {  
   P("static ATerm aux[%d];\n",lastvar+1);
   }

/*   
static ATerm PRval(ATerm t) {
    return rw_s?Val1(t):Val2(t);
    }
   if (indirect) {
     P("#define Val(t) ((ATgetAFun(t)<rw_n_substitute && rw_substitute[ATgetAFun(t)]) ? \\\n");
     P("\trw_substitute[ATgetAFun(t)]:rw_lookup[rw_s[ATgetAFun(t)]](t))\n");
     }
   else {
     P("#define Val(t) (ATgetAFun(t)<%d ? \\\n",rw_size);
     P("\tlookup[ATgetAFun(t)](t):( \\\n");
     P("\t(ATgetAFun(t)<rw_n_substitute && rw_substitute[ATgetAFun(t)]) ? \\\n");
     P("\trw_substitute[ATgetAFun(t)]:Exit(ATgetAFun(t))))\n");
     }
   P("ATerm Innermost(ATerm t) {\n");
   P("\treturn Val(t);\n");
   P("\t}\n");
   P("static ATerm innermost(ATerm t) {\n");
   P("\treturn Val(t);\n");
   P("\t}\n");
   }
*/
static void PRval(void) {
   /*
   P("static ATerm Val(ATerm t){\n");
   if (indirect) P("\treturn Val1(t);\n");
   else P("\treturn Val2(t);\n");
   P("\t}\n");
   if (indirect) P("#define Val Val1\n");
   else
   P("#define Val Val2\n");
   */
   P("static ATerm innermost(ATerm t){return Val(t);}\n"); 
   P("ATerm Innermost(ATerm t){return Val(t);}\n");  
   }
   
static void PRprotect(void) {
   P("static void Protect(void) {\n");
   P("\tmemset(aux, 0, sizeof(ATerm)*%d);\n",lastvar+1);
   P("\tATprotectArray(aux, %d);\n", lastvar+1);
   P("\t}\n");
   }
   
static void PRunprotect(void) {
   P("void Unprotect(void) {\n"); 
   P("\tATunprotect(aux);\n");
   P("\t}\n");
   }
      
static void PRdeclarations(void) {
   int i = 0;
   /* P("#include \"%s/librw.c\"\n",DATADIR); */ 
   P("#include \"librw.c\"\n"); 
   /* if (!conditional) */ PRauxVars();
   for (i=0;i<rw_size;i++) 
   if (symTab[i] && ATgetType(symTab[i]) == AT_LIST) {
       PRheaderD(i);P(";\n"); 
       }
   for (i=0;i<rw_size;i++)
   if (symTab[i] && ATgetType(symTab[i]) == AT_LIST) {
      if (ATgetArity(i)==0) {
          c_or_e = "E";
          PRheader(i);
          P(";\n");  
          } 
      c_or_e = "C";
      PRheader(i);
      P(";\n");  
      }
   /* if (!conditional) */ {
      PRprotect();
      PRunprotect();
      }
   PRval();
   }

static void PRnormaliseConstants() {
   P("static void NormaliseConstants(void) {\n");
   /* initCalls = ATreverse(initCalls); */
   for (;!ATisEmpty(initCalls);initCalls = ATgetNext(initCalls)) {
        ATermList l = (ATermList) ATgetFirst(initCalls);
        if (indirect) {
        P("\trw_quick[%t]=%t();\n",ATelementAt(l,0), ATelementAt(l,1));
	}
        else
        P("\trw_substitute[%t]=%t();\n",ATelementAt(l,0), ATelementAt(l,1));
        }
   P("}\n");
}



static void PbuildTerm(ATerm t, ATerm *sym, ATbool declare) {
   static int pt = 0, newline = 0;
   if (newline>4) {P("\n");newline=0;}
   if (ATgetType(t)==AT_LIST) {
        ATermList l = (ATermList) t;
        int i, m = ATgetLength(l);
        if (!declare) {P("ATmakeList(%d", m);newline++;}
        for (i=0;i<m;i++, l = ATgetNext(l)) {
          if (!declare) {P(",");newline++;}
          PbuildTerm(ATgetFirst(l), sym, declare);
          }
        if (!declare) {P(")");}
        }
   else if (ATgetType(t)==AT_APPL) {
        ATermAppl p = (ATermAppl) t;
        AFun f = ATgetAFun(p);
        int i, n = ATgetArity(f);
        if (declare) {
           if (f>=rw_size) ATerror("System error f=%d>%d=rw_size",f, rw_size);
           if (!sym[f]) {
             char *name = ATgetName(f);
             DECLA(char, buf, strlen(name)+20);
             int ptr;
             sprintf(buf,"v%d_%s", f, name);
             ptr = strcspn(buf,"?-#\"'$@!~`;.\\|*/");
             *(buf+ptr) = '\0';                
             sym[f] = ATmake("<appl>", buf);
             P("%c%s", pt>0?',':' ', buf);
             pt++;newline++;
             }
           for (i=0;i<n;i++) {
               PbuildTerm(ATgetArgument(p, i), sym, declare);
               }
           }
        else {
        switch (n) {
          case 0: P("ATmakeAppl0(%t",sym[f]); break;
          case 1: P("ATmakeAppl1(%t",sym[f]); break;
          case 2: P("ATmakeAppl2(%t",sym[f]); break;
          case 3: P("ATmakeAppl3(%t",sym[f]); break;
          case 4: P("ATmakeAppl4(%t",sym[f]); break;
          default: P("ATmakeAppl(%t",sym[f]); 
          }
          newline++;
        for (i=0;i<n;i++) {
           P(", (ATerm) ");newline++;
           PbuildTerm(ATgetArgument(p, i), sym, declare);
           }
        P(")");
        }
        }
   } 
        
static void PRinit(void) {
   int i, k = 0;
   ATerm *sym = NULL;
   PRnormaliseConstants();
   /* ---- Definition InitRewriteSystem --- */
   P("static LOOKUP lookuparray[] = {");
   if (indirect) {
   for (k=0;k<rw_size_s_inv;k++) {
      if (k%5==0) P("\n\t"); 
      i = rw_s_inv[k];
      if (k==0) P("GetVal");
      else
      if (symTab[i] && ATgetType(symTab[i]) == AT_LIST) 
           P(",%s",Fname("D", i));
      else
           P(",%s", "GetVal2");
      }
   } else {
   for (i=0;i<rw_size;i++) {
      if (i%5==0) P("\n\t"); 
      if (symTab[i] && ATgetType(symTab[i]) == AT_LIST) 
           P("%s%s",i?",":" ",Fname("D", i));
      else
           P("%s%s",i?",":" ","GetVal");
      }
   }
   P("\t};\n");
   P("ATerm TestRewriteSystem(void) {\n");
   if (indirect) {
       int i;
       sym  = (ATerm*) calloc(rw_size, sizeof(ATerm));
       ATprotectArray(sym, rw_size);
       P("ATerm t;\n");
       P("AFun ");
       PbuildTerm(ATgetArgument(MCRLgetAdt(), 0), sym, ATtrue);
       P(";");
       for (i=0;i<rw_size;i++) 
       if (sym[i]) P("ATprotectAFun((%t= ATmakeAFun(\"%s\", %d, %s)));\n", 
          sym[i], ATgetName(i), ATgetArity(i), ATisQuoted(i)?"ATtrue":"ATfalse");
   P("t = (ATerm)");
                  PbuildTerm(ATgetArgument(MCRLgetAdt(), 0), sym, ATfalse); 
                  P(";");
   P("t = (ATerm) ATmakeList2(t, rw_term);\n");
   P("return t;");
   ATunprotect(sym);
      }          
   else P("return (ATerm) NULL;");
   P("}\n");
   P("ATerm InitRewriteSystem(void) {\n");
   P("\tAllocate(lookuparray);\n");
   P("\tProtect();\n");
   P("\tNormaliseConstants();\n");
   P("return (ATerm) NULL;");
   P("}\n");
   }
   
static void PRbodyCaseD(AFun sym) {
   int i = 0, n = ATgetArity(sym);
   ATermList sels = MCRLgetCaseSelectors(sym); 
   PRheaderD(sym); P("{\n");
   if (n==0) {
      if (indirect)
      P("\treturn rw_quick[%d];\n",rw_s[sym]);
      else
      P("\treturn rw_substitute[%d];\n",sym);
      }
   else {
      if (hash) {
        P("\tATerm result = DBget(t);\n");
        P("\tif (result) return result;\n");
       /* P("ATwarning(\"QQQ: %s\",t);\n","%t"); */
        P("\t{\n");
        P("\tATerm selt = Val(A(t,0));\n");
        P("\tAFun sel = ATgetAFun(selt);\n");
        if (indirect) P("\tif (sel<rw_size) sel = rw_s[sel];\n");
        for (i=1;i<n;i++, sels = ATgetNext(sels)) {
           P("\tif (sel== %d) {\n",indirect?rw_s[ATgetAFun(ATgetFirst(sels))]:
                                              ATgetAFun(ATgetFirst(sels)));
P(
"\t\tresult = (ATisEqual(A(t,0), A(t,%d))?selt:Val(A(t,%d)));\n",
           i, i);
           P("\t\tif (!rw_stop_store) DBput(t, result);\n");
           P("\t\treturn result;\n");
           P("\t\t}\n"); 
           }
        P("\tresult = %s(selt\n",Fname("C", sym));
        for (i=1;i<n;i++) {
           P("\t,Val(A(t,%d))", i);
        }
        P("\t);\n");
        P("\tif (!rw_stop_store) DBput(t, result);\n");
        P("\treturn result;\n");
        P("\t}\n"); 
     }
     else {
        P("\tATerm selt = Val(A(t,0));\n");
        P("\tAFun sel = ATgetAFun(selt);\n");
        if (indirect) P("\tif (sel<rw_size) sel = rw_s[sel];\n"); 
        for (i=1;i<n;i++, sels = ATgetNext(sels)) {
           P("\tif (sel== %d) \n",indirect?rw_s[ATgetAFun(ATgetFirst(sels))]:
                                              ATgetAFun(ATgetFirst(sels)));
           P(
" return (ATisEqual(A(t,0), A(t,%d))?selt:Val(A(t,%d)));\n",
               i, i, i, i);
           }
        P("\treturn %s(\n",Fname("C", sym));
        P("selt");
        for (i=1;i<n;i++) {
           P(",Val(A(t,%d))", i);
           }
           P(");\n");
        }
     }
     P("\t}\n"); 
   }
   
static void _isNeeded(AFun sym, ATermList eqs, int *args) {
   for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
       if (ATgetType(ATgetFirst(eqs))==AT_APPL) {
          ATermList es = (ATermList) ATgetArgument((ATermAppl) ATgetFirst(eqs) , 0);
          for (;!ATisEmpty(es);es=ATgetNext(es)) { 
              ATermList sel = (ATermList) 
                 ATgetArgument((ATermAppl) ATgetFirst(es), 0);
              if (!ATisEmpty(sel)) {
                 int d = ATgetInt((ATermInt) ATgetLast(sel));
                 if (args[d]==0) args[d]+=2;
                 }
              }
         } else {
         ATermList eq = (ATermList) ATgetFirst(eqs);
         ATermAppl pair = (ATermAppl) ATgetAnnotation((ATerm) eq, anno);
         ATermList locs = (ATermList) ATgetArgument(pair, 0);
         ATerm val = ATgetArgument(pair, 1);
         if (ATgetType(val) != AT_INT && !ATisEmpty(locs)) {
                int d = ATgetInt((ATermInt) ATgetLast(locs));
                if (args[d]==0) args[d]+=2; 
                }     
         _isNeeded(sym, eq, args);
         }
    }
 }  
  
static void __isOccurring(ATerm right, int *args) {
   if (ATgetType(right)==AT_LIST) {
     ATermList rs = (ATermList) right;
     if (!ATisEmpty(rs)) {
        int d = ATgetInt((ATermInt) ATgetLast(rs));
        if (args[d]%2==0) args[d]++;
        }
     return;
     }      
     {
     int i, n = ATgetArity(ATgetAFun(right));
     for (i=0;i<n;i++) __isOccurring(ATgetArgument((ATermAppl) right, i),
        args);
     }
   }
     
static void _isOccurring(AFun sym, ATermList eqs, int *args) {
   for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
         ATerm eq = ATgetFirst(eqs);
         if (!ATisEmpty(eqs) && ATgetType(eq)==AT_APPL) {
            ATerm right = ATgetArgument((ATermAppl) eq, 1);
            __isOccurring(right, args);
            continue;
          }  
    _isOccurring(sym, (ATermList) (ATgetFirst(eqs)), args);  
    }
   } 

/*    
static int *isNeededOrOccurring(AFun sym) {
   ATermList eqs = ATgetNext((ATermList) symTab[sym]);
   int n = ATgetArity(sym);
   int *args = calloc(n, sizeof(int));
   _isNeeded(sym, eqs, args);
   _isOccurring(sym, eqs, args);
   return args;
   } 
*/

/*
static void printArgs(AFun sym, int *args) {
   int n = ATgetArity(sym), i;
   ATwarning("Symbol %a", sym);
   for (i=0;i<n;i++) fprintf(stderr,"%d ", args[i]);
   fprintf(stderr,"\n");
   }

static ATbool isRemoved(AFun sym, int *args) {
   int i, n = ATgetArity(sym);
   for (i=0;i<n && args[i]>0;i++); 
   return i<n;
   } 
*/
                  
static void PRbodyD(AFun sym) {
   int i = 0, n = ATgetArity(sym);
   /* int *args = isNeededOrOccurring(sym); */
   int *args = NULL;
   /*
   ATbool removed = 
        !IsEqualFunction(sym) && isRemoved(sym, args);
	printArgs(sym, args);
   */
   ATbool removed = ATfalse;
   PRheaderD(sym); P("{\n");
   /* P("ATwarning(\"%ct\", t);\n",'%'); */
   if (n==0) {
      if (indirect)
         P("\treturn rw_quick[%d];\n",rw_s[sym]);
      else {
         P("\treturn rw_substitute[%d];\n",sym);
         }
      }
   else {
      if (rw_eq && MCRLgetType(sym)== MCRLeqfunction) {
        P("\tif (ATisEqual(A(t,0),A(t,1))) return MCRLterm_true;\n");
      }
      if (hash) {
        if (IsEqualFunction(sym)) P("\t{");
        else P("\t");
        P("ATerm result = DBget(t);\n");
        P("\tif (result) return result;\n");
        /* P("ATwarning(\"QQQ: %s\",t);\n","%t"); */
        P("\tresult = %s(\n",Fname("C", sym));
        for (i=0;i<n;i++) {
           if (!args || args[i]>-1) P("\t%sVal(A(t,%d))\n",(i==0?" ":","), i);
           else {
             P("\t%sA(t,%d)\n",(i==0?" ":","), i);
             }
           }
        P("\t);\n");
        /* P("ATwarning(\"result: %s\",result);\n","%t"); */
        P("\tif (!rw_stop_store) DBput(t, result);\n");
        if (!removed) P("\treturn result;\n");
     }
     else {
        if (removed) 
              P("\tATerm result = %s(\n",Fname("C", sym));
        else  P("\treturn %s(\n",Fname("C", sym));
        for (i=0;i<n;i++) {
           if (!args || args[i]>-1) P("\t%sVal(A(t,%d))\n",(i==0?" ":","), i);
           else {
             P("\t%sA(t,%d)\n",(i==0?" ":","), i);
             }
           }
           P("\t);\n");
     if (removed) {
          P("\tif (ATgetAFun(result)==%d)\n\t", sym);
          P("\tresult = %s(\n",Fname("C", sym));
          for (i=0;i<n;i++) 
             if (args[i]==0) P("\t%sVal(A(result,%d))\n",(i==0?" ":","), i);
             else
             P("\t%sA(result,%d)\n",(i==0?" ":","), i);
          P("\t);\n");
         }
     }
     if (removed) P("\treturn result;\n");
     if (hash && IsEqualFunction(sym)) P("\t}\n"); 
     }
     P("\t}\n"); 
     if (args) free(args);
   }
   
static void PRoutputVariable(ATermList locs);
 
static ATbool _PRdeclareVariable(ATermList locs, char *buf, ATbool first) {
   ATbool isNew; int d;
   if (ATisEmpty(locs)) return first;
   first = _PRdeclareVariable(ATgetNext(locs), buf, first);
   d = ATgetInt((ATermInt) ATgetFirst(locs));
   sprintf(buf+strlen(buf), "_%d", d);
   ATindexedSetPut(decl, (ATerm) ATmakeAppl0(ATmakeAFun(buf, 0, ATfalse)), 
    &isNew);
/* ATwarning("PRdeclare %t %d", 
   (ATerm) ATmakeAppl0(ATmakeAFun(buf, 0, ATfalse)), isNew); */ 
   if (isNew) {
   if (first) {
         P("AFun "); first = ATfalse;
         }
      else P(",");
      P("%s = 0", buf);
      }
   return first;
   }

static ATbool PRdeclareVariable(ATermList locs, ATbool first) {
   char buf[1024];
   sprintf(buf,"%s", "sym");
   first = _PRdeclareVariable(locs, buf, first);
   return first; 
   }
 
/*   
static ATbool _PRselectVariable(ATermList locs, char *buf, ATbool first) {
   if (ATisEmpty(locs)) return first;
   {
   int d = ATgetInt((ATermInt) ATgetFirst(locs)); 
   first = _PRselectVariable(ATgetNext(locs), buf, first);
   sprintf(buf+strlen(buf), "_%d", d);
   return first;
   }
   }
*/

static void PRselectVariable(ATermList locs) {
   if (indirect) P("rw_s[");
   P("ATgetAFun("); 
   PRoutputVariable(locs);
   P(")");
   if (indirect) P("]");
   }
   
static void _PRoutputVariable(ATermList locs, char *buf) {
   if (ATisEmpty(locs)) return;
   {
   int d = ATgetInt((ATermInt) ATgetFirst(locs)); 
   _PRoutputVariable(ATgetNext(locs), buf);
   if (ATgetLength(locs)==1) {
      sprintf(buf+strlen(buf), "%d", d);
      }
   else {
      char *bufold = strdup(buf);
      buf[0]='\0';
      sprintf(buf, "A(%s, %d)", bufold, d);
      free(bufold);
      }
   }
   }

static void PRoutputVariable(ATermList locs) {
   char buf[1024];
   sprintf(buf,"%s", "arg");
   _PRoutputVariable(locs, buf); 
   P("%s", buf);
   }
          
static void PRtestEqual(ATermList locs1, ATerm match) {
   AFun sym = ATgetAFun(match); 
   if (ATgetType(match) == AT_APPL) {
       if (indirect) P("rw_s[");
       P("ATgetAFun(");
       }
   PRoutputVariable(locs1);
   if (ATgetType(match) == AT_APPL) {
         P(")");
         if (indirect) P("]");
         }
   P("==");
   if (ATgetType(match) == AT_LIST) {
       PRoutputVariable((ATermList) match);
       }
   else
       P("%d",indirect?rw_s[sym]:sym);
   }
   
static void PRlinesConformPatterns(ATermList patterns) {
   for (;!ATisEmpty(patterns);patterns=ATgetNext(patterns)) {
       ATerm pattern = ATgetFirst(patterns);
       ATermList locs = (ATermList) ATgetArgument((ATermAppl) pattern, 0);
       ATerm match = ATgetArgument((ATermAppl) pattern, 1);
       PRtestEqual(locs, match);
       if (ATgetType(match) == AT_APPL && ATgetArity(ATgetAFun(match))>0) { 
           ATermList pats = (ATermList) ATgetArgument((ATermAppl) match, 0);
           if (ATgetLength(pats)>0) {
                P("&&"); 
                PRlinesConformPatterns(pats);
                }             
           }
           if (!ATisEmpty(ATgetNext(patterns))) P("&&");
        }
   }
   
   
       
static ATbool PRassign (ATerm arg) {
   AFun sym = ATgetAFun(arg);
   if (ATgetArity(sym)>0) {
        int ind = ATindexedSetGetIndex(subterms, arg);
        if (ind<0) ATabort("System error: %t",arg);
        P("aux[%d]?aux[%d]:(aux[%d]=",ind, ind, ind);
        return ATtrue;
        }
   else {
       if (indirect)
       P("rw_quick[%d]?rw_quick[%d]:(rw_quick[%d]=",rw_s[sym],
       rw_s[sym], rw_s[sym]);
       else
       P("rw_substitute[%d]?rw_substitute[%d]:(rw_substitute[%d]=",sym,
       sym, sym);
       /*
       if (indirect) P("rw_quick[%d]", rw_s[sym]);
       else P("rw_substitute[%d]", sym);
       */
       }
      return ATtrue;
   }
   
static void PRsubsList(ATermList args, ATbool val) {
/* Prints commands to makes a copy of the pattern, in which the
variables are replaced by calls of ATgetArguments */
     int i = 0;
     for (;!ATisEmpty(args);args=ATgetNext(args),i++){ 
         ATerm arg = ATgetFirst(args);
         int n = ATgetArity(ATgetAFun(arg));
         ATbool rhs = ATtrue;
         if (i>0) P(",");
         if (ATgetType(arg)==AT_LIST) { 
               PRoutputVariable((ATermList) arg);
               continue;
               }
         if (!isOpenTerm(arg)) rhs = PRassign(arg);
	 /* PRappl(ATgetAFun(arg)); */
         if (rhs) {
           P("%s(", Fname(n==0?c_or_e:"C",ATgetAFun(arg)));
           PRsubsList(ATgetArguments((ATermAppl) arg), val);
           if (!isOpenTerm(arg)) P(")");
           P(")");
           }
         } 
}


static ATbool PRrightN(ATerm rhs, ATbool lazy) {
   AFun sym = 0, sm = 0; int n = 0;
   ATbool rh = ATtrue, condition = ATfalse, result = ATfalse;
   sym = ATgetAFun(rhs); n = ATgetArity(sym);
   sm = indirect?rw_s[sym]:0;
   if (conditional && MCRLgetType(sym)==MCRLcasefunction && 
   n==3 && ATgetArgument((ATermAppl)rhs, 2)==infinite) 
   condition = ATtrue;
   if (condition) {
       ATermList sels = MCRLgetCaseSelectors(sym);
       ATerm cond = ATgetArgument((ATermAppl)rhs, 0);
       P("if(ATisEqual(%s(),(",
       Fname(n==0?c_or_e:"C",ATgetAFun(ATgetFirst(sels))));
       
       /*
       sym = ATgetAFun(rhs);
       P("%s(", Fname(n==0?c_or_e:"C",sym));
       */
       PRsubsList(ATmakeList1(cond), ATfalse);
       P(")))");
       rhs = ATgetArgument((ATermAppl)rhs, 1);
       sym = ATgetAFun(rhs);
       result = ATtrue;
       }
   if (ATgetType(rhs)==AT_LIST) {
        P(" return ");PRoutputVariable((ATermList) rhs);P(";\n"); return;
   }
   if (!lazy) P(" "); 
   P(" return ");
   if (!isOpenTerm(rhs) && !strcmp(c_or_e, "C")) rh = PRassign(rhs);
   if (rh) {
   if (!lazy) 
        {P("%s(", Fname(n==0?c_or_e:"C",sym));}
   else {
        if (rw_case) P("MCRLcaseDistribution(rw_lookup[%d],",indirect?sm:sym);
	PRappl(sym);
        }
   PRsubsList(ATgetArguments((ATermAppl) rhs), ATfalse);
   if (lazy && rw_case) P(")");
   P(")");
   if (!isOpenTerm(rhs) && !strcmp(c_or_e, "C")) 
         P(")");
   }
   P(";\n");
   return result;         
   }
   
/*
and(F,F)=F and(T,F)=F and(F,T)=F and(T,T)=T

and->[e([[0]=F,[1]=F],F),e([[0]=T,[1]=F],F),
      e([[0]=F,[1]=T],F),e([[0]=T,[1]=T],T),
      default([],and([0],[1])]
      
F->and([e([[1]=F,F), e([[1]=T,F)], dummy)
T->and([e([[1]=F,F), e([[1]=T,T)], dummy)
[default([],and([0],[1])]
*/
         
static ATbool PRrule(ATerm eq) {  
   ATbool lazy = (ATgetAFun(eq)==default_sym);
   ATermList patterns = (ATermList) ATgetArgument((ATermAppl) eq,0);
   ATerm right = ATgetArgument((ATermAppl) eq, 1);
   ATbool r = ATfalse;
   if (!ATisEmpty(patterns)) {
       P("\tif(");
       PRlinesConformPatterns(patterns);
       P(")\n");
       r = ATtrue;
       }
   /* ATwarning("QQ: %s %t", ATgetName(sym), right); */
   r |= PRrightN(right, lazy);
   return r;
   }

static void PRbody(AFun sym) {    
   if (indirect) {
   /* 
   P("ATwarning(\"PRbody %ca\", %s);\n",'%', Fname("E", sym)); 
   */
   P("\treturn rw_quick[%d]?rw_quick[%d]:(rw_quick[%d]=%s());\n",rw_s[sym],
   rw_s[sym], rw_s[sym], Fname("E", sym));
   }
   else
   P("\treturn rw_substitute[%d]?rw_substitute[%d]:(rw_substitute[%d]=%s());\n",sym,
   sym, sym, Fname("E", sym));
   }
   
static void PRbodyC(AFun sym) {
   PRheader(sym); P("{\n");
   PRbody(sym);
   P("\t}\n");
   }
    
static void PRshortCodeEqu(AFun sym, ATbool enumerated) {
   P("\tif (MCRLgetType(ATgetAFun(arg0))==MCRLconstructor && \n");
   P("\t    MCRLgetType(ATgetAFun(arg1))==MCRLconstructor)\n");
   P("\tif (ATisEqual(arg0, arg1)) return MCRLterm_true; else\n");
   if (!enumerated) {
     P("\tif (ATgetAFun(arg0)!=ATgetAFun(arg1))\n");
     }
   P("\treturn MCRLterm_false;\n");
   }
   
static ATbool WalkThruPatterns(ATermList patterns, ATbool first) {
   for (;!ATisEmpty(patterns);patterns=ATgetNext(patterns)) {
       ATerm pattern = ATgetFirst(patterns);
       ATermList locs = (ATermList) ATgetArgument((ATermAppl) pattern, 0);
       ATerm match = (ATerm) ATgetArgument((ATermAppl) pattern, 1);
       first = PRdeclareVariable(locs, first);
       if (ATgetType(match) == AT_APPL) {
           if (ATgetArity(ATgetAFun(match))>0) { 
           ATermList pats = (ATermList) ATgetArgument((ATermAppl) match, 0);
           if (ATgetLength(pats)>0) {
                /* P(","); */
                first = WalkThruPatterns(pats, first);
                }             
              }
           }
        else  first = PRdeclareVariable((ATermList) match, first);
        }
     return first;
   }

static ATbool WalkThruRHS(ATerm t, ATbool first) {
   if (ATgetType(t)==AT_LIST) {
     first = PRdeclareVariable((ATermList) t, first);
     return first;
     }
   {
   AFun sym = ATgetAFun(t);
   int n = ATgetArity(sym), i;
   for (i=0;i<n;i++) first = WalkThruRHS(
       ATgetArgument((ATermAppl)t, i), first); 
   }
   return first;
   } 
   
static ATbool Execution(AFun sym, ATermList eqs) { 
   int n = ATgetArity(sym);
   ATbool r = ATfalse; 
   if (rw_simple || n==0)    
   for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
        /* New */
        if (ATgetType(ATgetFirst(eqs))== AT_APPL)
             r |= PRrule(ATgetFirst(eqs)); 
        }
   else {
    if (IsEqualFunction(sym)) {
     PRshortCodeEqu(sym, 
     MCRLgetType(ATgetAFun(ATgetArgument((ATermAppl) MCRLgetFunction(sym), 0)))
     ==MCRLenumeratedsort?ATtrue:ATfalse); 
     for (; !ATisEmpty(eqs);eqs=ATgetNext(eqs))
     if (ATgetType(ATgetFirst(eqs))== AT_APPL) {
        ATermAppl eq = (ATermAppl) ATgetFirst(eqs);
        ATermList p = (ATermList) ATgetArgument(eq, 0);
	/* [0]=S(x) [1]=S(x) */
        if (ATgetLength(p)==2)  {
           ATerm a1 = ATgetArgument((ATermAppl) ATelementAt(p,0), 1);
           ATerm a2 = ATgetArgument((ATermAppl) ATelementAt(p,1), 1);
           AFun s1 = ATgetAFun(a1), s2 = ATgetAFun(a2);
/* if ((ATisEqual(a1, a2) && ATgetArity(s1)>0)) { */
           if (s1==s2 && ATgetArity(s1)>0) {
           r |= PRrule((ATerm) eq);
           }
           }
        else r |= PRrule((ATerm) eq);
        }  
   } else {
     for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
        if (ATgetType(ATgetFirst(eqs))== AT_APPL) {
        /* ATwarning("PRrule %t",ATgetFirst(eqs)); */
        r |= PRrule(ATgetFirst(eqs));
        } 
       }
   }
   }
   return r;
   }

static ATbool PRnested(AFun sym, ATermList eqs);
 
static ATermList PRswitch(AFun sym, ATermList eqs) {
   for(;!ATisEmpty(eqs)&& (ATgetType(ATgetFirst(eqs))==AT_LIST);
                   eqs=ATgetNext(eqs)) {
      ATermList ts = (ATermList) ATgetFirst(eqs);
      ATermList locs = (ATermList) ATgetAnnotation((ATerm) ts, anno2);
      P("switch(");
      PRselectVariable(locs);
      P("){\n");
      for (;!ATisEmpty(ts);ts = ATgetNext(ts)) {
         ATerm t = ATgetFirst(ts),
         v = ATgetAnnotation(t, anno);
         P("case %d :{ /* %a */\n",
         indirect?rw_s[ATgetAFun(v)]:ATgetAFun(v), ATgetAFun(v));
         if (PRnested(sym, (ATermList) t)) P("break;");
         P("}\n");
         }
      P("}\n");
      }
   return eqs; 
   }
       
static ATbool PRnested(AFun sym, ATermList eqs) {
   ATermList eqs0 = eqs; ATbool r = ATfalse;
   eqs = PRswitch(sym, eqs); 
   r |= (eqs != eqs0);
   r |= Execution(sym, eqs); 
   return r;    
   } 
                                      
static ATerm PRbodyCE(AFun sym, ATermList eqs) {
   int n = ATgetArity(sym);
   c_or_e = n==0?"E":"C"; /* E functions will be called at initialising */
   PRheader(sym); P("{\n");
   PRnested(sym, ATgetNext(eqs));
   /* Default rules */
   PRnested(sym, ATmakeList1(ATgetFirst(eqs)));
   P("\t}\n");
   if (n==0) {
   /* Extra E subroutines which will be used one time at intialisation,
      to rewrite constants terms. The C subroutines uses these rewritten
      constants */
        c_or_e = "C";
        PRbodyC(sym); 
        return ATmake("<appl>",Fname("E", sym));
        }
   return NULL;
   } 
   
static void PRbodies(void) {
   int i = 0;
   Warning("QQ: Start PRbodies");
   for (i=0;i<rw_size;i++) 
   if (symTab[i] && ATgetType(symTab[i])==AT_LIST) {
        ATerm t = PRbodyCE(i, (ATermList) symTab[i]);
        if (t) initCalls = ATinsert(initCalls, 
             (ATerm) ATmakeList2(
             (ATerm) ATmakeInt(indirect?rw_s[i]:i),t));
        if (!rw_simple && MCRLgetType(i)==MCRLcasefunction)
            PRbodyCaseD(i);
        else 
            PRbodyD(i);
        }
   Warning("QQ: End PRbodies");
   }

static char *Command(const char *format, ...) {
   int n = strlen(format);
   char *r = NULL;
   const char *t;
   va_list ap;
   va_start(ap, format);
   for (t=format;(t=strchr(t,'%'));n+=strlen(va_arg(ap, char *)),t++) {
       /* fprintf(stderr,"QQQ %s %s\n", t, s); */ 
       }
   va_end(ap);
   va_start(ap, format);
   r = (char*) malloc((n+1)*sizeof(char));
   vsprintf(r, format, ap);
   va_end(ap);
   /*fprintf(stderr,"QQQ Command n=%d r = %s l = %d\n", n, r, strlen(r)); */
   return r;
   }
     
static void OutputRewriteSystem(char *filename) {  
    char a[256], c[256], b[512], base[256], *includedir=strdup(makefile);
    char includeline[256], *cmdstring; 
    char *dir;
    FILE *f=fopen(program,"r");
    if (f) {
        GetCwd(b, 400);
        fclose(f);
        }
    else {
       sprintf(b, "%s", strcmp(program,"instantiate")?BINDIR:LIBEXECDIR);
       }
    sprintf(b+strlen(b),"/%s", program);
    /* ATwarning("Program = %s b = %s", program, b); */
    *strrchr(includedir,'/')='\0';
    strncpy(a, filename, 256);
    strncpy(c, filename, 256);
    dir = strdup(dirname(a)); 
    strncpy(base, basename(c), 256); 
    // dir = dirname(a); base = basename(c);
    strncat(filename,".c", 256);
    strncat(base,".so", 256);
    snprintf(includeline,256, "\"-I%s -I%s/.. -I%s/../aterm\"",
    includedir, includedir, includedir);
    if (!rw_read_src) {
       if (!(fp = fopen(filename,"w"))) {
            ATwarning("File %s cannot be opened", filename);
            exit(1);
            }
       PRdeclarations();
       PRbodies();
       PRinit();
       fclose(fp);
       }
    else {
      if (!(fp = fopen(filename,"r"))) {
            ATwarning("File %s cannot be opened", filename);
            exit(1);
            }
      fclose(fp);
      }
    if (verbose) ATwarning("NOW COMPILING");
    cmdstring = Command("cd %s;%s -f %s %s %s %s%s %s%s %s CPP=%s %s", 
    dir, MAKE, makefile, verbose?"":"-s", base,
    "PROG=", b, "VAL=", indirect?"Val1":"Val2" ,rw_debug?"DEBUG=\\#":"", includeline, "1>&2");
    /* ATwarning("%s",cmdstring); */ 
    if (!verbose) ATwarning("Start compiling ..."); 
    if (system(cmdstring)>0)
         ATerror("Fail: make %s", filename);
    
    if (!verbose) ATwarning(".... end compiling.");
    filename[strlen(filename)-2]='\0';
    free(cmdstring); 
    }
    
/* Part II  API interface */


typedef ATerm (*load_function_type)(void);
typedef ATerm (*innermost_function_type)(ATerm);

static void *rewriter_handle=NULL;

static innermost_function_type innermost_function = NULL;

static void EnlargeDeclare(void) {
   int i;
   for (i=0;i<MAXLEVEL;i++) {
       while (rw_number_per_level <= rw_leveled_subs[i][0]) rw_number_per_level *= 2;
       }
   for (i=0;i<MAXLEVEL;i++) {
       if (!(rw_leveled_subs[i] = (AFun*) realloc(rw_leveled_subs[i],
             rw_number_per_level*sizeof(AFun))))
        ATerror("Cannot reallocate array (%d)", rw_number_per_level);
      }
   }
           
static void EnlargeSubstitute(AFun sym) {
      if (rw_n_substitute > sym) return;
      { long old=rw_n_substitute;
      ATunprotectArray(rw_substitute); 
      ATunprotectArray(rw_varnames);
      while (rw_n_substitute <= sym) rw_n_substitute *= 2;  
      if (!(rw_substitute = (ATerm*) realloc(rw_substitute, 
             rw_n_substitute*sizeof(ATerm))))
        ATerror("Cannot reallocate term array (%d)", rw_n_substitute);
      if (!(rw_varnames = (ATerm*) realloc(rw_varnames, 
             rw_n_substitute*sizeof(ATerm))))
        ATerror("Cannot reallocate term array (%d)", rw_n_substitute);
     
      if (!(rw_lookup = (LOOKUP*) realloc(rw_lookup, 
             rw_n_substitute*sizeof(LOOKUP))))
        ATerror("Cannot reallocate rw_lookup (%d)", rw_n_substitute);
       if (indirect) {
       if (rw_n_substitute>rw_size)
       if (!(rw_s = (AFun*) realloc(rw_s, 
             rw_n_substitute*sizeof(AFun))))
        ATerror("Cannot reallocate rw_s (%d)", rw_n_substitute);
	}
      for (;old<rw_n_substitute;old++) {
           rw_substitute[old]=NULL;
           rw_varnames[old]=NULL;
	   if (indirect && old>=rw_size) rw_s[old] = 0;
	   rw_lookup[old]=rw_lookup[0]; /* GetVal or GetVal2 */
           }
      ATprotectArray(rw_substitute, rw_n_substitute); 
      ATprotectArray(rw_varnames, rw_n_substitute);
      }     
}

static void put_var(AFun f, ATerm t, int level) {
  if (level>0) {
    int n_vars = ++rw_leveled_subs[(--level)][0];
    if (n_vars < rw_number_per_level) 
        rw_leveled_subs[level][n_vars] = f; 
    else {
        if (ATisEqual(rw_substitute[f],rw_varnames[f])) {
           /* 
           ATerror("Too many substitutions (>%d) at level %d\n",PERLEVEL,level+1);
           */
           EnlargeDeclare();
           rw_leveled_subs[level][n_vars] = f; 
           }
        else
        rw_leveled_subs[level][0]--;
        }
   /*  Warning("QQ put_var n_vars = %d value = %s level = %d",
       n_vars, ATgetName(f), level); */
  }
  if (f>=rw_n_substitute)
    ATerror("Symbol index too high (%d > %d)\n",f, rw_n_substitute); 
  rw_substitute[f] =t;
}

static void reset_var(int level) {
  int n_vars,j;
  if (level>0) {
    n_vars=rw_leveled_subs[level-1][0];
    rw_leveled_subs[level-1][0]=0;
    for (j=1;j<=n_vars;j++) {
      AFun sym = rw_leveled_subs[level-1][j];
      /* Warning("QQ: Reset %s %d", ATgetName(sym), level);
      Warning("QQ: Reset2 %t", rw_varnames[sym]); */
      rw_substitute[sym]=  rw_varnames[sym];
      }
  }
  else
    ATerror("resetting level 0");
}

static void RWWstopStore(void) {
     rw_stop_store = ATtrue;
     }

static void RWWresumeStore(void) {
     rw_stop_store = ATfalse;
     }

static void RWWassignVariable(AFun var, ATerm t, ATerm tsort, int level) {
  if (level>=MAXLEVEL)
    ATerror("Level (%d) exceeds MAXLEVEL (%d)",level,MAXLEVEL);
  put_var(var,t,level);
  /* round++; */
  if (rw_db && autoCache) { 
      if (level==0) {
        if (!reset) ATtableReset(rw_db); reset = ATtrue;
        }
       else 
        RWWstopStore();
     }
  /* ATwarning("QQ: Assign %d %d  %d",autoCache,rw_stop_store,level); */
  }

static void RWWresetVariables(int level) {
  reset_var(level);
  if(rw_db && autoCache && level==1) RWWresumeStore();
 /* ATwarning("QQ: Reset %d %d  %d",autoCache,rw_stop_store,level); */
  }
  
static void RWWsetAutoCache(ATbool b) {
  autoCache = b;
  /* Warning("QQ: Setautocache %d %d",autoCache,rw_stop_store); */
  }
   
static void RWWdeclareVariable(ATerm t) {
   AFun s = ATgetAFun(t);
   /*
   ATwarning("QQ: declareVar %t %d > %d",t, rw_number_per_level, rw_number_of_vars);
   */
   EnlargeSubstitute(s);
   EnlargeDeclare();
   /* ATwarning("Declare %s (%d, %d) %t",ATgetName(s),s,ATgetArity(s), t); */ 
   rw_substitute[s] = rw_varnames[s]=t; 
   rw_number_of_vars++;
   }

static void RWWdeclareVariables(ATermList vars) { 
  for (;!ATisEmpty(vars);vars = ATgetNext(vars)) {
    ATerm var = ATgetFirst(vars);
    if (ATgetArity(ATgetSymbol(var))==2) var = 
      ATgetArgument(ATgetFirst(vars),0);
    RWWdeclareVariable(var);
  }
}

static ATerm RWWgetAssignedVariable(AFun var) {
   return rw_substitute[var];
   }
   
static ATerm RWWrewrite(ATerm t) {
   if (rw_db) reset = ATfalse;
   return (*innermost_function) (t);   
   }
   
static ATermList RWWrewriteList(ATermList ts) {
   ATermList r = ATempty; 
   for (;!ATisEmpty(ts); ts=ATgetNext(ts)) {
        r = ATinsert(r,RWWrewrite(ATgetFirst(ts)));
        }
   return ATreverse(r);
   }
      
static ATerm PerformLoadFunction(const char *name) {
   load_function_type load_function=(load_function_type) 
   dlsym(rewriter_handle,name);
   if (load_function==NULL) 
       ATerror("Finding code for `%s' fails: %s", name, dlerror());
   return (*load_function)(); 
   }

static void LoadInnermostFunction(void) {   
   innermost_function=(innermost_function_type) 
   dlsym(rewriter_handle,"Innermost");
   if (innermost_function==NULL) 
       ATerror("Finding code for `%s' fails: %s", "Innermost", dlerror());
   }

static void CloseDl(void) {
   if (rewriter_handle) {
       dlclose(rewriter_handle);
       /* system(cmd); */
   }
}
      
static void MakeClean(void) {
   if (!rewriter_handle) return;
   if (rw_db) {
       ATtableDestroy(rw_db);
       rw_db = NULL;
       rw_stop_store = ATfalse;
       }
   if (subterms) {
       ATindexedSetDestroy(subterms);subterms = NULL;
       }
   ATunprotect(symTab); free(symTab); symTab = NULL;
   PerformLoadFunction("Free");
   dlclose(rewriter_handle); rewriter_handle = NULL;
   }

typedef struct {
   char *name;
   int arity;
   AFun sym;
   } FUNREC;
   
typedef int (*compar_f) (const void *,const void *);

static int compare(const FUNREC *a, const FUNREC *b) {
  int result;
  return (result=strcmp(a->name, b->name))!=0?result:a->arity-b->arity;
  }
  
static void DefineIdx2Sym() {
   ATermList fs = MCRLgetAllFunctions();
   int i = 0; 
   FUNREC *funrec;
   rw_size_s_inv = ATgetLength(fs)+1;
   if (!(rw_s_inv=(AFun*) malloc(sizeof(AFun)*rw_size_s_inv)))
       ATerror("idx2sym not allocated (%d)", rw_size_s_inv);
   if (!(rw_quick=(ATerm*) calloc(rw_size_s_inv, sizeof(ATerm))))
       ATerror("rw_quick not allocated (%d)", rw_size_s_inv);
   ATprotectArray(rw_quick, rw_size_s_inv);
   if (!(rw_s = (AFun*) calloc(rw_size, sizeof(AFun))))
       ATerror("sym2idx not allocated (%d)", rw_size);
   if (!(funrec=(FUNREC*) malloc(sizeof(FUNREC)*rw_size_s_inv)))
       ATerror("funrec not allocated (%d)", rw_size_s_inv);
   funrec[0].sym = 0;
   funrec[0].name = "GetVal";
   funrec[0].arity = 1; 
   for (i=1;!ATisEmpty(fs);fs=ATgetNext(fs),i++) {
      funrec[i].sym = ATgetAFun(ATgetFirst(fs));
      funrec[i].name = ATgetName(funrec[i].sym);
      funrec[i].arity = ATgetArity(funrec[i].sym);
      }
   qsort(funrec+1, rw_size_s_inv-1, sizeof(FUNREC), (compar_f) compare);
   for (i=0;i<rw_size_s_inv; i++) {
      /* ATprotectSymbol((rw_s_inv[i] = funrec[i].sym)); */
      rw_s_inv[i] = funrec[i].sym;
      rw_s[funrec[i].sym] = i;
      }
   free(funrec);
   }

static void fnamecpy(char *path, char *dir,   char *fname) {
   if (fname[0]=='/') strncpy(path, fname,256);
   else snprintf(path, 256, "%s/%s", dir, fname);
   }
              
static int RWWinitialiseRewriter(ATerm datatype, long rewritelimit, int hashvar) {
     FILE *np = NULL;
     static char *filename = NULL;
     ATerm sig = NULL;
     makefile = LocationRww();
     if (filename==NULL) filename = calloc(256, sizeof(char));
     if (rw_read || rw_write || rw_read_src) {
         if (rw_write) {
           fnamecpy(filename,rw_debug?dyndir:DYNDIR, rw_write);
           ATwarning("Compiled rewrite system is written in %s.so", filename);
           }
         if (rw_read) {
             fnamecpy(filename, rw_debug?dyndir:DYNDIR, rw_read);
             ATwarning("Compiled rewrite system is read from %s.so", filename);
             }
         if (rw_read_src) {
             fnamecpy(filename, rw_debug?dyndir:DYNDIR, rw_read_src);
             ATwarning("Source code compiled rewrite system is written in %s.c", 
                  filename);
             }
         }
     /* else if (rw_debug) fnamecpy(filename, dyndir, "RWW"); */
     else  {
           char aux[256];
           sprintf(cmd, "%s -f %s %s all", MAKE, makefile, "-s");
           if (verbose) ATwarning("%s",cmd); 
           if ((np=Popen(cmd,"r"))==NULL)
               ATerror("Fail: %s",MAKE);
           if (fgets(aux, 256, np)==NULL) 
                 ATerror("Reading filename for %s not possible", MAKE);
           aux[strlen(aux)-1]='\0';
           Pclose(np);
           fnamecpy(filename, DYNDIR, aux);
           }
     adt = datatype;
     hash = hashvar;
     ATprotect(&adt);
     MakeClean();
     if (hashvar && !rw_db) rw_db = ATtableCreate(250, 75);
     decl = ATindexedSetCreate(250, 75);
     AllocateSymbolTable(); 
     ComputeSymbolTable();
     AddDefaultRules();
     if (indirect) DefineIdx2Sym();
     /* fprintf(stderr,"Test1 %s\n", filename); */
     if (!rw_read) {
       OutputRewriteSystem(filename);
       }
     /* fprintf(stderr,"Test2 %s\n", filename); */
     strcat(filename,".so");
     rewriter_handle=dlopen(filename,RTLD_NOW);
     if (rewriter_handle==NULL) {
        ATerror("Loading %s fails: %s",filename, dlerror());
        system("rm -f so_locations");
        sprintf(cmd,"rm -f %s", filename);
        system(cmd);
        return 0;
        }
    if (!rw_debug && !rw_write && !rw_read && !rw_read_src) {
        sprintf(cmd,"rm -f %s", filename);
        system(cmd);
        }
    LoadInnermostFunction();
    sig = PerformLoadFunction("TestRewriteSystem");
    if (sig) {
       if (ATgetType(sig)==AT_LIST && ATisEqual(ATelementAt((ATermList) sig, 1), 
       rw_term)) {
           sig = ATgetFirst((ATermList) sig);
           }
       else ATerror("Wrong format of compiled file (format of -rw expected)");
       if (!ATisEqual(sig, ATgetArgument(
          (ATermAppl)MCRLgetAdt(), 0))) 
       ATerror("Loaded signature is not equal to the read signature");
       }
    PerformLoadFunction("InitRewriteSystem");
    Warning("End of loading");
    atexit(CloseDl);  
    return 1; 
    }

static void RWWflush(void) {
    if (rw_db) ATtableReset(rw_db);
} 
   
static ATbool RWWinitialize(ATerm datatype) {
    if (!MCRLgetAdt() && !MCRLinitializeAdt(datatype)) return ATfalse; 
    RWWsetAutoCache(ATtrue);
    return (ATbool) RWWinitialiseRewriter(datatype, 0, hashvar); 
    }

static int RwRead(int n, char **argv) {
    int k;for (k=0;k<n;k++) 
    if (!strcmp(argv[k],"-read-so")) return 1;
    return 0;
    }
        
static void RWWsetArguments(int *argc, char ***argv) {
     int i, j=0;
     char **newargv = (char**) calloc(*argc + 1, sizeof(char*)), *ptr;
     int skip = RwRead(*argc, *argv);
     ATbool forbiddenAfterRead = ATfalse;
     if (!newargv) ATerror("Cannot allocate array argv");
     dyndir = (char*) malloc(3*sizeof(char));
     strcpy(dyndir,"./");
     ptr = newargv[j++] = (*argv) [0];
     if (!(program=strrchr(ptr,'/'))) program = ptr;
     else program++;
     for(i=1;i<*argc;i++) {
     if (!strcmp((*argv)[i],"-simple")) {
          if (skip) continue;
          rw_simple = ATtrue;
          rw_eq = ATfalse;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-no-eq")) {
          if (skip) continue;
          rw_eq = ATfalse;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-eq")) {
          if (skip) continue;
          rw_eq = ATtrue;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-case")) {
          if (skip) continue;
          rw_case = ATtrue;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-debug")) {
          if (skip) continue;
          verbose = ATtrue;
          rw_debug = ATtrue;
          dyndir = (char*) malloc(3*sizeof(char));
          strcpy(dyndir,"./");
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-verbose")) {
          if (skip) continue;
          verbose = ATtrue;
          /* continue; */
          }
     if (!strcmp((*argv)[i],"-no-hash")) {
          if (skip) continue;
          hashvar=0;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     /*
     if (!strcmp((*argv)[i],"-indirect")) {
          indirect = ATtrue;
          continue;
          }
     */
     if (!strcmp((*argv)[i],"-hash")) {
          if (skip) continue;
          hashvar=1;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-rww-O")) {
          if (skip) continue;
          optimize = 1;
          continue;
          }
     if (!strcmp((*argv)[i],"-conditional")) {
          if (skip) continue;
          conditional = 1;
          continue;
          }
     if (!strcmp((*argv)[i],"-no-conditional")) {
          if (skip) continue;
          conditional = 0;
          continue;
          }
     if (!strcmp((*argv)[i],"-read-so")) {
            if ((++i)<(*argc) && (*argv)[i][0] && strncmp((*argv)[i],"-",1)) {
                char *name = (*argv)[i], *ptr;
                rw_read = (char*) malloc((strlen(name)+1)*sizeof(char));
                strcpy(rw_read, name);
                if ((ptr=strrchr(rw_read,'.')) && !strcmp(ptr,".so")) 
                      *ptr = '\0';
                indirect = ATtrue;
                continue;
                }
            fprintf(stderr, "Option %s needs argument.\n",(*argv)[i-1]);
            exit(1);
            }
     if (!strcmp((*argv)[i],"-write-so")) {
            if ((++i)<(*argc) && (*argv)[i][0] && strncmp((*argv)[i],"-",1)) {
                char *name = (*argv)[i], *ptr;
		if (skip) continue;
                rw_write = (char*) malloc((strlen(name)+1)*sizeof(char));
                strcpy(rw_write, name);
                if ((ptr=strrchr(rw_write,'.')) && !strcmp(ptr,".so")) 
                      *ptr = '\0';
                indirect = ATtrue;
                continue;
                }
            fprintf(stderr, "Option %s needs argument.\n",(*argv)[i-1]);
            exit(1);
            }
      if (!strcmp((*argv)[i],"-read-c")) {
            if ((++i)<(*argc) && strncmp((*argv)[i],"-",1)) {
                char *name = (*argv)[i], *ptr;
		if (skip) continue;
                rw_read_src = (char*) malloc((strlen(name)+1)*sizeof(char));
                if ((ptr=strrchr(name,'.')) && !strcmp(ptr,".c")) *ptr = '\0';
                strcpy(rw_read_src, name);
                continue;
                }
            fprintf(stderr, "Option %s needs argument.\n",(*argv)[i-1]);
            exit(1);
            }
        newargv[j++] = (*argv)[i];
        }
      *argc = j;  *argv = newargv;
      /*
      if (rw_read && forbiddenAfterRead) {
           fprintf(stderr, 
      "Compiled rewrite system will be loaded; rewriter options are not valid"
         ); 
         exit(1);
           }
     */
     }
     
static void RWWhelp(void) {
  Pr("Extra options of rw are:");
  Pr("-simple:\t\tTranslation of rewrite rules without optimizing");
  Pr("-conditional:\t\tHandles conditional rewrite rules");
  Pr("-no-eq:\t\t\tNo optimisation at rewriting of eq rules"); 
  Pr("-debug:\t\t\tThe source code of the compiled rewrite system");
  Pr("\t\t\tis located on ./RWW.c and will not be removed. The source");
  Pr("\t\t\twill be compiled with the flag -g. Also the \".so\" file will");
  Pr( "\t\t\tnot be removed.");
  Pr("-write-so <file>\tWrites compiled rewrite system in \"<file>.so\"");
  Pr("-read-so <file>\t\tReads compiled rewrite system from \"<file>.so\"");
  Pr("-read-c <file>\t\tReads rewrite system source code from \"<file>.c\""); 
  }
           
TASKS RWtasks = {RWWsetArguments, RWWinitialize, RWWassignVariable, 
RWWgetAssignedVariable, RWWresetVariables, RWWdeclareVariables,
RWWrewrite, RWWrewriteList, RWWsetAutoCache, RWWflush, RWWhelp};

#else

/*  ---------------------OUTPUTTEXT -------------------------------------- */

#define A(t,i) (ATgetArgument((ATermAppl) t ,i))

/* Extern variables */
extern ATerm *rw_varnames, *rw_substitute, *rw_quick, rw_term;
extern int rw_n_substitute, rw_number_of_vars, rw_number_per_level;
extern ATermTable rw_db;
extern int rw_size, rw_size_s_inv, rw_stop_store;
extern AFun *rw_s, *rw_s_inv,  *rw_leveled_subs[];
typedef ATerm (*LOOKUP) (ATerm);
extern LOOKUP *rw_lookup;
static void Unprotect(void);

static ATerm innermost(ATerm t);
/* SUBSTITUTION */
static void Allocate(LOOKUP lookuparray[]) {
   int i;
   rw_n_substitute = !rw_s?rw_size:rw_size_s_inv;
   rw_substitute = (ATerm*) calloc(rw_n_substitute, sizeof(ATerm));
   rw_varnames = (ATerm*) calloc(rw_n_substitute,sizeof(ATerm));
   ATprotectArray(rw_substitute, rw_n_substitute); 
   ATprotectArray(rw_varnames, rw_n_substitute);
   rw_lookup = malloc(rw_n_substitute*sizeof(LOOKUP));
   memcpy(rw_lookup,lookuparray,rw_n_substitute*sizeof(LOOKUP));
   for (i=0;i<MAXLEVEL;i++) {
       rw_leveled_subs[i] = (AFun*) calloc(rw_number_per_level, sizeof(AFun));
       }
   }
 
ATerm Free(void) {
   if (rw_varnames) {
      int i;
      ATunprotect(rw_substitute); free(rw_substitute); rw_substitute = NULL; 
      ATunprotect(rw_varnames); free(rw_varnames); rw_varnames = NULL;
      Unprotect();
      for (i=0;i<MAXLEVEL;i++) {
        free(rw_leveled_subs[i]);
      }
      free(rw_lookup);
  }
  return (ATerm) NULL;
}

static ATerm Exit(AFun a) {
  ATerror("Variable/Function %a is not declared", a);
  return (ATerm) NULL;
  }
  

    
static ATerm DBget(ATerm t) {
    ATerm result = NULL;
    ATermTable db0 = NULL;
    if (rw_db) {
          if ((result = ATtableGet(rw_db, t)))  {
              if (rw_stop_store) {
                    db0 = rw_db; rw_db = NULL;
                    result = innermost(result);
                    rw_db = db0;
                    }
              }
          }
    return result;
    }

static void DBput(ATerm t, ATerm result) {
    ATtablePut(rw_db, t, result);
    }

static ATerm Val(ATerm t);

    

static ATerm Val1(ATerm t) {
     AFun s = ATgetAFun(t);
     if(0<=s && s<rw_n_substitute) {
     AFun a = rw_s[s];
     /* assert(0<=a && a<rw_n_substitute); */
     return rw_lookup[a](t);
     }
     return t;
     }

static ATerm Val2(ATerm t) {
     AFun s = ATgetAFun(t);
     if (0<=s && s<rw_n_substitute) return rw_lookup[s](t);
     return t;
     }

/*
static ATerm Val(ATerm t) {
    return rw_s?Val1(t):Val2(t);
    }
*/

/*   
static ATerm innermost(ATerm t) {
    return Val(t);
    }
            
ATerm Innermost(ATerm t) {
     return Val(t);
     }
*/   

static ATerm GetVal(ATerm t) {
    ATerm r =  rw_substitute[ATgetAFun(t)];
    if (!r) {
      int n = ATgetArity(ATgetAFun(t)), i;   
      ATerm *a = (ATerm*) malloc(n*sizeof(ATerm));
      for (i=0;i<n;i++)
         a[i] = Val(ATgetArgument(t,i));
      r = (ATerm) ATmakeApplArray(ATgetAFun(t), a);
      free(a);
      }
    return r;
    /* return (ATerm) ((int) rw_substitute[ATgetAFun(t)] || (int) Exit(t)); */
    }
#endif
