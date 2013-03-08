/* $Id: librww.c,v 1.12 2005/12/22 10:41:10 bertl Exp $ */
/* Include file destined for both programs */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "mcrl.h"

#define MAXLEVEL 3
#define PERLEVEL 2600

/*  Include file */

#ifndef OUTPUTTEXT

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdarg.h>
#include <stdlib.h>
#include <dlfcn.h>
#include "tasks.h"

#define DEFAULT_VAL 0

/*  Must be extern because of dynamic linking */
 
ATerm *rww_varnames = NULL, *rww_substitute =  NULL, *rww_quick =  NULL,
rww_term = NULL;
int rww_n_substitute = 0, rww_number_of_vars = 0, *rww_leveled_subs[MAXLEVEL],
    rww_number_per_level = PERLEVEL;
ATermTable rww_db  = NULL;
int rww_size = 0, rww_size_s_inv = 0, rww_stop_store = 0;
int *rww_s = NULL, *rww_s_inv = NULL; 
/* End extern variables */
 
static char cmd[256], *c_or_e=NULL;
static char *program = NULL, *makefile = NULL;
static ATbool rww_simple = ATfalse, rww_debug = ATfalse,
verbose = ATfalse, rww_eq = ATtrue, indirect = ATfalse;

#define setOpenTerm(t) (ATsetAnnotation(t, _openTerm, _openTerm))
#define isOpenTerm(t)  (ATgetAnnotation(t, _openTerm)!=NULL)

static FILE *fp = NULL;
static ATerm *symTab = NULL, _openTerm = NULL, _dummy = NULL;
static AFun pos_sym, eq_sym, default_sym, a_sym, getafun_sym;
static int cursor = 0, lastvar = 0, hash = 0, hashvar = 1; 

static ATbool autoCache = ATfalse, reset = ATtrue, rww_case = ATfalse;
static ATermIndexedSet subterms = NULL;
static ATerm adt = NULL;

static ATermTable decl = NULL;
static ATbool declaration = ATfalse;
static int nvars = 0;
static ATermList initCalls;
static char *rww_read = NULL, *rww_write = NULL, *dyndir = NULL,
            *rww_read_src = NULL;

#define MAXCOLS 80

static int Warning(const char *format, ...) {
   va_list ap;
   va_start(ap, format);
   return 0;
   }

/* Part I output rewrite system */ 
    
static void ClearVarsInSymbolTable(ATerm eq) {
     ATermList vars = (ATermList) ATgetArgument((ATermAppl) eq,0);
     for (;!ATisEmpty(vars);vars=ATgetNext(vars)) {
         ATerm var = ATgetFirst(vars);
         AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) var, 0));
         symTab[sym] = NULL;
         }
     }
     
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

static int IsLocal(void) {
   FILE *f = fopen("./Rww", "r");
   if (!f) return 0;
   fclose(f);
   return 1;
   } 
              
static void AllocateSymbolTable(void) {
     ATermList eqs = (ATermList) ATgetArgument((ATermAppl) adt,1);
     ATermList sig = (ATermList) ATgetArgument((ATermAppl) adt,0);
     ATermList funcs = (ATermList) ATgetArgument(sig,1), funcs0 = funcs;
     ATermList maps = (ATermList) ATgetArgument(sig,2), maps0 = maps;
     AFun sm = ATmakeAFun("rww_s", 3, ATfalse);
     if (sm > rww_size) rww_size = sm;
     sm = ATmakeAFun("f", 3, ATfalse);
     if (sm > rww_size) rww_size = sm;
     sm = ATmakeAFun("e", 3, ATfalse);
     if (sm > rww_size) rww_size = sm;
     sm = ATmakeAFun("d", 3, ATfalse);
     if (sm > rww_size) rww_size = sm;
     for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs))
           {ATerm eq = ATgetFirst(eqs);
           AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) eq, 1));
           ATermList vars = (ATermList) ATgetArgument((ATermAppl) eq,0);
           if ((int) sym > rww_size) rww_size = sym;
           for (;!ATisEmpty(vars);vars=ATgetNext(vars)) {
                ATerm var = ATgetFirst(vars);
                AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) var, 0));
                if ((int) sym > rww_size) rww_size = sym; 
                } 
           } 
     for (;!ATisEmpty(funcs);funcs=ATgetNext(funcs))
           {ATerm func = ATgetFirst(funcs);
           AFun sym = CreateSymFromFunc(func);
           if ((int) sym > rww_size) rww_size = sym;
           }
     for (;!ATisEmpty(maps);maps=ATgetNext(maps))
           {ATerm map = ATgetFirst(maps);
           AFun sym = CreateSymFromFunc(map);
           if ((int) sym > rww_size) rww_size = sym;
           }
     rww_size++;          
     symTab = (ATerm*) calloc(rww_size, sizeof(ATerm));
     ATprotectArray(symTab, rww_size); 
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
        getafun_sym = ATmakeSymbol("ATgetAFun",1, ATfalse);
             ATprotectSymbol(getafun_sym);
        pos_sym = ATmakeSymbol("pos",1, ATfalse);ATprotectSymbol(pos_sym); 
        default_sym = ATmakeSymbol("default",2, ATfalse);
                      ATprotectSymbol(default_sym);
        ATprotect((ATerm*) &_openTerm); _openTerm = ATmake("<appl>", "open");
        ATprotect((ATerm*) &_dummy); _dummy = ATmake("<appl>", "dummy");
        ATprotect((ATerm*) &rww_term); rww_term = ATmake("<appl>", "rww_term");
        }
     subterms = ATindexedSetCreate(100, 70);
     initCalls = ATempty; 
     ATprotect((ATerm*) &initCalls);       
     } 

static ATbool isVariable(ATerm t) {
     AFun sym = ATgetSymbol(t);
     if (ATgetArity(sym)>0) return ATfalse;
     if (symTab[sym]==NULL) return ATtrue;
     if (ATgetType(symTab[sym])==AT_LIST) return ATfalse;
     if (ATgetType(symTab[sym]) == AT_APPL) return ATtrue;
     return ATfalse; 
     }

static ATerm MakeEq(ATerm t1, ATerm t2) {
     return (ATerm) ATmakeAppl2(eq_sym, t1, t2);
}

static ATerm Substitute(ATerm t) {
     AFun sym = ATgetSymbol(t);
     int  n = ATgetArity(sym);
     ATerm result = NULL;
     if (isVariable(t)) {
          ATerm p = symTab[ATgetSymbol(t)];
          if (!p) ATerror("Illegal variable in rhs: %t",t);
          
          return setOpenTerm((ATerm) ATgetArgument((ATermAppl) p, 0));
          }
     if (n>0) {
          int i = 0;
          ATbool openTerm = ATfalse;
          DECLA(ATerm, a, n);
          for (i=0;i<n;i++) {
              a[i] = Substitute(ATgetArgument((ATermAppl) t, i));
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
     for (;!ATisEmpty(args);args=ATgetNext(args),j++)
           {ATerm arg = ATgetFirst(args);
           ATermList newloc = ATinsert(loc, (ATerm) ATmakeInt(j));
           if (!isVariable(arg)) {
               newargs = ATinsert(newargs, MakeEq((ATerm) newloc, 
                   Detect(arg, newloc)));
               i++;
               }
           else {
               ATerm p = symTab[ATgetSymbol(arg)];
               /*
               if (ATgetType(p)==AT_LIST) 
                 ATerror("No variable of name \"%a\" is permitted", 
                        ATgetSymbol(arg));
               */
               if (!p) {
                    symTab[ATgetSymbol(arg)] = 
                    (ATerm) ATmakeAppl1(pos_sym, (ATerm) newloc);
                    }  
               else {
                 newargs = ATinsert(newargs, MakeEq(
                    ATgetArgument(p,0), (ATerm) newloc));
               i++;
               } 
           }
        }
     if (n>0) {
        args = ATmakeList1((ATerm) ATreverse(newargs));
        for (i=1;i<n;i++) args = ATinsert(args, _dummy);
        return (ATerm) ATmakeApplList(symbol, ATreverse(args));
        }
     return t;
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
*/

static void ComputeSymbolTable(void) {
     ATermList eqs = ATreverse((ATermList) ATgetArgument((ATermAppl) adt,1));
     Warning("QQ: Start Compute Symbol Table");
     for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs))
           {ATerm eq = ATgetFirst(eqs);
           AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) eq, 1));
           ATerm detect = Detect(ATgetArgument((ATermAppl) eq, 1), ATempty);
           ATerm rww_substitute = Substitute(ATgetArgument((ATermAppl) eq, 2));
           int arity = ATgetArity(ATgetSymbol(detect));
           /* ATwarning("QQ detect = %t",detect); */
           /* Needed because the order of evaluation of arguments
              is different in Linux and Sun */
           symTab[sym] = (ATerm) ATinsert((ATermList) symTab[sym], 
           ATmake("e(<term>,<term>)", 
           arity>0? ATgetArgument((ATermAppl) detect,0):(ATerm) ATempty, 
           rww_substitute));
           ClearVarsInSymbolTable(eq); 
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
     for (i=0;i<rww_size;i++)
     if (symTab[i] && ATgetType(symTab[i])==AT_LIST)
         symTab[i] = (ATerm) ATreverse(ATinsert((ATermList) symTab[i], 
           (ATerm) ATmakeAppl2(default_sym, (ATerm) ATempty, DefaultRhs(i))
           )); 
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
   
static void PbuildTerm(ATerm t, ATerm *sym, ATbool declare) {
   static int pt = 0, newline = 0;
   /* ATwarning("newline %d", newline); */
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
           if (f>=rww_size) ATerror("System error f=%d>%d=rww_size",f, rww_size);
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
   
static int PRappl(AFun sym) {
   int arity = ATgetArity(sym);
   if (indirect) {
   switch (arity) {
   case 0: return P("(ATerm) ATmakeAppl0(rww_s_inv[%d]",rww_s[sym]);
   case 1: return P("(ATerm) ATmakeAppl1(rww_s_inv[%d],",rww_s[sym]);
   case 2: return P("(ATerm) ATmakeAppl2(rww_s_inv[%d],",rww_s[sym]);
   case 3: return P("(ATerm) ATmakeAppl3(rww_s_inv[%d],",rww_s[sym]);
   case 4: return P("(ATerm) ATmakeAppl4(rww_s_inv[%d],",rww_s[sym]);
   case 5: return P("(ATerm) ATmakeAppl5(rww_s_inv[%d],",rww_s[sym]);
   case 6: return P("(ATerm) ATmakeAppl6(rww_s_inv[%d],",rww_s[sym]);
   default: return P("(ATerm) ATmakeAppl(rww_s_inv[%d],",rww_s[sym]);
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
   char *name = ATgetName(symbol);
   int n = strcspn(name,"?-#\"'$@!~`;.\\|*/"), k = 0;
   k+=sprintf(buffer,"%s_%d_",prefix, indirect?rww_s[symbol]:symbol);
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
   /* P("#include \"%s/librww.c\"\n",DATADIR); */ 
   P("#include \"librww.c\"\n"); 
   PRauxVars();
   for (i=0;i<rww_size;i++) 
   if (symTab[i] && ATgetType(symTab[i]) == AT_LIST) {
       PRheaderD(i);P(";\n"); 
       }
   for (i=0;i<rww_size;i++)
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
   PRprotect();
   PRunprotect();
   }

static void PRnormaliseConstants() {
   P("static void NormaliseConstants(void) {\n");
   /* initCalls = ATreverse(initCalls); */
   for (;!ATisEmpty(initCalls);initCalls = ATgetNext(initCalls)) {
        ATermList l = (ATermList) ATgetFirst(initCalls);
        if (indirect)
        P("\trww_quick[%t]=%t();\n",ATelementAt(l,0), ATelementAt(l,1));
        else
        P("\trww_substitute[%t]=%t();\n",ATelementAt(l,0), ATelementAt(l,1));
        }
   P("}\n");
}

static void PRval(void) {
   if (indirect) {
     P("#define Val(t) ((ATgetAFun(t)<rww_n_substitute && rww_substitute[ATgetAFun(t)]) ? \\\n");
     P("\trww_substitute[ATgetAFun(t)]:lookup[rww_s[ATgetAFun(t)]](t))\n");
     }
   else {
     P("#define Val(t) (ATgetAFun(t)<%d ? \\\n",rww_size);
     P("\tlookup[ATgetAFun(t)](t):( \\\n");
     P("\t(ATgetAFun(t)<rww_n_substitute && rww_substitute[ATgetAFun(t)]) ? \\\n");
     P("\trww_substitute[ATgetAFun(t)]:Exit(ATgetAFun(t))))\n");
     }
   P("ATerm Innermost(ATerm t) {\n");
   P("\treturn Val(t);\n");
   P("\t}\n");
   P("static ATerm innermost(ATerm t) {\n");
   P("\treturn Val(t);\n");
   P("\t}\n");
   }
      
static void PRinit(void) {
   int i, k = 0;
   ATerm *sym = NULL;
   PRnormaliseConstants();
   /* ---- Definition InitRewriteSystem --- */
   P("static LOOKUP lookuparray[] = {");
   if (indirect) {
   for (k=0;k<rww_size_s_inv;k++) {
      if (k%5==0) P("\n\t"); 
      i = rww_s_inv[k];
      if (symTab[i] && ATgetType(symTab[i]) == AT_LIST) 
           P("%s%s",k?",":" ",Fname("D", i));
      else
           P("%s%s",k?",":" ","GetVal2");
      }
   } else {
   for (i=0;i<rww_size;i++) {
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
       sym  = (ATerm*) calloc(rww_size, sizeof(ATerm));
       ATprotectArray(sym, rww_size);
       P("ATerm t;\n");
       P("AFun ");
       PbuildTerm(ATgetArgument(MCRLgetAdt(), 0), sym, ATtrue);
       P(";");
       for (i=0;i<rww_size;i++) 
       if (sym[i]) P("ATprotectAFun((%t= ATmakeAFun(\"%s\", %d, %s)));\n", 
          sym[i], ATgetName(i), ATgetArity(i), ATisQuoted(i)?"ATtrue":"ATfalse");
   P("t = (ATerm)");
                  PbuildTerm(ATgetArgument(MCRLgetAdt(), 0), sym, ATfalse); 
                  /* PbuildTerm(ATmake("<str>", "aap")); */
                  P(";");
   P("t = (ATerm) ATmakeList2(t, rww_term);\n");              
   P("return t;");
   ATunprotect(sym);
      }          
   else P("return (ATerm) NULL;");
   P("}\n");
   P("ATerm InitRewriteSystem(void) {\n");
   P("\tlookup = lookuparray;\n");
   P("\tAllocate();\n");
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
      P("\treturn rww_quick[%d];\n",rww_s[sym]);
      else
      P("\treturn rww_substitute[%d];\n",sym);
      }
   else {
      if (hash) {
        P("\tATerm result = DBget(t);\n");
        P("\tif (result) return result;\n");
       /* P("ATwarning(\"QQQ: %s\",t);\n","%t"); */
        P("\t{\n");
        P("\tAFun sel = ATgetAFun(Val(A(t,0)));\n");
        if (indirect) P("\tif (sel<rww_size) sel = rww_s[sel];\n");
        for (i=1;i<n;i++, sels = ATgetNext(sels)) {
           P("\tif (sel== %d) {\n",indirect?rww_s[ATgetAFun(ATgetFirst(sels))]:
                                              ATgetAFun(ATgetFirst(sels)));
           P("\t\tresult = Val(A(t,%d));\n", i);
           P("\t\tif (!rww_stop_store) DBput(t, result);\n");
           P("\t\treturn result;\n");
           P("\t\t}\n"); 
           }
        P("\tresult = %s(\n",Fname("C", sym));
        for (i=0;i<n;i++) {
           P("\t%sVal(A(t,%d))\n",
           (i==0?" ":","), i);
        }
        P("\t);\n");
        P("\tif (!rww_stop_store) DBput(t, result);\n");
        P("\treturn result;\n");
        P("\t}\n"); 
     }
     else {
        P("\tAFun sel = ATgetAFun(Val(A(t,0)));\n");
        if (indirect) P("\tif (sel<rww_size) sel = rww_s[sel];\n"); 
        for (i=1;i<n;i++, sels = ATgetNext(sels)) {
           P("\tif (sel== %d) {\n",indirect?rww_s[ATgetAFun(ATgetFirst(sels))]:
                                              ATgetAFun(ATgetFirst(sels)));
           P(" return Val(A(t,%d));}\n", i);
           }
        P("\treturn %s(\n",Fname("C", sym));
        for (i=0;i<n;i++) {
           P("\t%sVal(A(t,%d))\n",
           (i==0?" ":","), i);
           }
           P("\t);\n");
        }
     }
     P("\t}\n"); 
   }
   

                 
static void PRbodyD(AFun sym) {
   int i = 0, n = ATgetArity(sym);
   PRheaderD(sym); P("{\n");
   if (n==0) {
      if (indirect)
         P("\treturn rww_quick[%d];\n",rww_s[sym]);
      else
         P("\treturn rww_substitute[%d];\n",sym);
      }
   else {
      if (rww_eq && MCRLgetType(sym)== MCRLeqfunction) {
        P("\tif (ATisEqual(A(t,0),A(t,1))) return MCRLterm_true;\n");
      }
      if (hash) {
        if (rww_eq && MCRLgetType(sym)== MCRLeqfunction) P("\t{");
        else P("\t");
        P("ATerm result = DBget(t);\n");
        P("\tif (result) return result;\n");
        /* P("ATwarning(\"QQQ: %s\",t);\n","%t"); */
        P("\tresult = %s(\n",Fname("C", sym));
        for (i=0;i<n;i++) {
           P("\t%sVal(A(t,%d))\n",
           (i==0?" ":","), i);
           }
        P("\t);\n");
        P("\tif (!rww_stop_store) DBput(t, result);\n");
        P("\treturn result;\n");
        if (rww_eq && MCRLgetType(sym)== MCRLeqfunction) P("\t}\n");
     }
     else {
        P("\treturn %s(\n",Fname("C", sym));
        for (i=0;i<n;i++) {
           P("\t%sVal(A(t,%d))\n",
           (i==0?" ":","), i);
           }
           P("\t);\n");
         }
     }
     P("\t}\n"); 
   }

static ATerm selectVariable(ATermList locs) {
   static char buf[10];
   static ATerm *anames = NULL;
   if (!anames) {
        anames = (ATerm*) calloc(256,sizeof(ATerm));
        ATprotectArray(anames, 256);
        }
   if (ATisEmpty(locs)) return NULL;
   if (ATgetLength(locs)==1) { 
        int n = ATgetInt((ATermInt) ATgetFirst(locs));
        ATerm t = NULL;
        if (n>=256 || !anames[n]) {
             sprintf(buf,"arg%d",n);
             t = ATmake("<appl>", buf);
             }
        return t?(n<256?(anames[n]=t):t):anames[n]; 
        }
   return (ATerm) ATmakeAppl2(a_sym, 
                  selectVariable(ATgetNext(locs)), ATgetFirst(locs));
   }
  
static void PRselectVariable(ATermList locs) {
   int n = ATgetLength(locs);
   if (n<1) return;
   if (n==1) {
       P("arg%d",ATgetInt((ATermInt) ATgetFirst(locs)));
       return;
       }
   P("A(");PRselectVariable(ATgetNext(locs));
   P(",%d",ATgetInt((ATermInt) ATgetFirst(locs)));
   P(")");
   }
      
static void PRtestEqual(ATermList locs1, ATerm match) {
   static char buf[10];
   static ATerm *anames = NULL;
   AFun sym = ATgetAFun(match); ATerm key = NULL;
   if (!anames) {
        anames = (ATerm*) calloc(256,sizeof(ATerm));
        ATprotectArray(anames, 256);
        }
   if (ATgetType(match) != AT_LIST /* && n>0 */) { 
       ATerm sel = selectVariable(locs1);
       ATbool isVariable = (ATgetArity(ATgetAFun(sel))==0);
       key = (ATerm) ATmakeAppl1(getafun_sym, sel);
       if (declaration) {
            if (!ATtableGet(decl,key)) {
                ATerm v = NULL;
                if (nvars>=256 || !anames[nvars]) {
                   sprintf(buf,"sym%d",nvars);
                   v = ATmake("<appl>", buf);
                   }
                v = v?(nvars<256?(anames[nvars]=v):v):anames[nvars]; 
                ATtablePut(decl, key, v); 
                /* v = sym...  key = ATgetAfun(arg...) */
                nvars++;
                if (isVariable) { 
                  if (indirect) 
                   P("\tAFun %t = (%t<rww_size?rww_s[%t]:%d);\n", v, key,  key, -1);
                  else
                   P("\tAFun %t = %t;\n",v, key); 
                  }
                else P("\tAFun %t = %d;\n",v, DEFAULT_VAL);
                }
            return;
            }
        if (isVariable) P("%t",ATtableGet(decl, key));
        else P(indirect?"(%t==%d?(%t=(%t<rww_size?rww_s[%t]:-1)):%t)":"(%t==%d?(%t=%t):%t)",
             ATtableGet(decl, key),
             DEFAULT_VAL, ATtableGet(decl, key), key, key, ATtableGet(decl, key));
        }
   else {
        if (declaration) return;
        PRselectVariable(locs1);
        } 
   P("==");
   if (ATgetType(match) == AT_LIST) {
       ATermList locs2 = (ATermList) match;
       PRselectVariable(locs2);
       }
   else
       P("%d",indirect?rww_s[sym]:sym);
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
                if (!declaration) P("&&"); 
                PRlinesConformPatterns(pats);
                }             
           }
           if (!declaration && !ATisEmpty(ATgetNext(patterns))) P("&&");
        }
   }
   
   
       
static ATbool PRassign (ATerm arg) {
   AFun sym = ATgetAFun(arg);
   if (ATgetArity(sym)>0) {
        int ind = ATindexedSetGetIndex(subterms, arg);
        if (ind<0) ATerror("System error: %t",arg);
        P("aux[%d]?aux[%d]:(aux[%d]=",ind, ind, ind);
        return ATtrue;
        }
   else {
       if (indirect)
       P("rww_quick[%d]?rww_quick[%d]:(rww_quick[%d]=",rww_s[sym],
       rww_s[sym], rww_s[sym]);
       else
       P("rww_substitute[%d]?rww_substitute[%d]:(rww_substitute[%d]=",sym,
       sym, sym);
       /*
       if (indirect) P("rww_quick[%d]", rww_s[sym]);
       else P("rww_substitute[%d]", sym);
       */
       }
      return ATtrue;
   }
   
static void PRsubsList(ATermList args) {
/* Prints commands to makes a copy of the pattern, in which the
variables are replaced by calls of ATgetArguments */
     int i = 0;
     for (;!ATisEmpty(args);args=ATgetNext(args),i++){ 
         ATerm arg = ATgetFirst(args);
         int n = ATgetArity(ATgetAFun(arg));
         ATbool rhs = ATtrue;
         if (i>0) P(",");
         if (ATgetType(arg)==AT_LIST) { 
               PRselectVariable((ATermList) arg);
               continue;
               }
         if (!isOpenTerm(arg)) rhs = PRassign(arg);
	 /* PRappl(ATgetAFun(arg)); */
         if (rhs) {
           P("%s(", Fname(n==0?c_or_e:"C",ATgetAFun(arg)));
           PRsubsList(ATgetArguments((ATermAppl) arg));
           if (!isOpenTerm(arg)) P(")");
           P(")");
           }
         } 
}



static void PRrightN(ATerm rhs, ATbool lazy) {
   AFun sym = 0, sm = 0; int n = 0;
   ATbool rh = ATtrue;
   if (ATgetType(rhs)==AT_LIST) {
        P("\t\treturn ");PRselectVariable((ATermList) rhs);P(";\n"); return;
   }
   sym = ATgetAFun(rhs); n = ATgetArity(sym);
   sm = indirect?rww_s[sym]:0;
   if (!lazy) P("\t");
   P("\treturn ");
   if (!isOpenTerm(rhs) && !strcmp(c_or_e, "C")) rh = PRassign(rhs);
   if (rh) {
   if (!lazy) 
        {P("%s(", Fname(n==0?c_or_e:"C",sym));}
   else {
        if (rww_case) P("MCRLcaseDistribution(lookup[%d],",indirect?sm:sym);
	PRappl(sym);
        }
   PRsubsList(ATgetArguments((ATermAppl) rhs));
   if (lazy && rww_case) P(")");
   P(")");
   if (!isOpenTerm(rhs) && !strcmp(c_or_e, "C")) 
         P(")");
   }
   P(";\n");          
   }
   
ATermList MakeSubpattern(ATermList patterns, AFun sel, int pos) {
  ATermList result = ATempty;
  for (;!ATisEmpty(patterns);patterns=ATgetNext(patterns)) {
      ATerm pattern = ATgetFirst(patterns);
      ATerm match = ATgetArgument((ATermAppl) pattern, 1);
      int var = ATgetInt((ATermInt) 
      ATgetFirst((ATermList) ATgetArgument((ATermAppl) pattern, 0)));
      if (ATgetType(match) == AT_APPL && ATgetAFun(match)==sel && var == pos)
      {if (ATgetArity(sel)>0) result = ATconcat (result, 
           (ATermList) ATgetArgument((ATermAppl)match, 0));}
      else result = ATinsert(result, pattern);
      }
   return ATreverse(result);
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

static ATerm MakeEntry(AFun sym) {
    int n = ATgetArity(sym), i;
    DECLA(ATerm, aux, n);
    ATerm t = NULL;
    for (i=0;i<n;i++) aux[i] = (ATerm) ATempty;
    t = (ATerm) ATmakeApplArray(sym, aux);
    return t;
    }

static ATermList Insert(ATermList l, ATerm  t) {
    return (ATindexOf(l,t,0)<0)?ATinsert(l,t):l;
}
    
static void TransformPatterns(ATerm eq, AFun sym, ATermList *accepted, 
   ATermList *rejected) {
   ATermList patterns = (ATermList) ATgetArgument((ATermAppl)
           eq,0), patterns0 = patterns;
   ATerm right = ATgetArgument(eq,1);
   int n = ATgetArity(sym), i;
   DECLA(ATbool, rejec, n);
   for (i=0;i<n;i++) rejec[i] = ATtrue; 
   for (;!ATisEmpty(patterns);patterns=ATgetNext(patterns)) {
       ATerm pattern = ATgetFirst(patterns);
       ATermList locs = (ATermList) ATgetArgument((ATermAppl) pattern, 0);
       ATerm match = ATgetArgument((ATermAppl) pattern, 1), neweq = NULL;
       if (ATgetType(match) == AT_APPL && ATgetArity(ATgetAFun(match))>=0  &&
          ATgetLength(locs)==1) {
          AFun sel = ATgetAFun(match);
          int pos = ATgetInt((ATermInt) ATgetFirst(locs));
          rejec[pos] = ATfalse;
          accepted[pos] = Insert(accepted[pos],
                  ATmake("<int>",ATgetAFun(match)));
          if (!rww_substitute[sel]) rww_substitute[sel] = MakeEntry(sym);
          neweq = (ATerm) ATmakeAppl2(ATgetAFun(eq),
              (ATerm) MakeSubpattern(patterns0, sel, pos), right);
          rww_substitute[sel] = (ATerm) ATsetArgument((ATermAppl) rww_substitute[sel], 
               (ATerm) 
               Insert((ATermList) ATgetArgument(rww_substitute[sel], pos), neweq),
               pos);
          } 
       }
      for (i=0;i<n;i++) if (rejec[i]) 
          {rejected[i] = Insert(rejected[i], eq);}
   }
   
static void AllocateArrays(int n, 
   ATerm **substitute,
   ATermList **accepted, ATermList **rejected) {
   int i;
   *substitute = (ATerm*) calloc(rww_size, sizeof(ATerm));
   *rejected = (ATermList*) calloc(n, sizeof(ATerm));
   *accepted = (ATermList*) calloc(n, sizeof(ATerm));
   ATprotectArray(*substitute, rww_size);
   ATprotectArray((ATerm*) *rejected, n);
   ATprotectArray((ATerm*) *accepted, n);
   for (i=0;i<n;i++) (*rejected)[i] = ATempty;
   for (i=0;i<n;i++) (*accepted)[i] = ATempty;
   }
   
static void PRrule(ATerm eq) {  
   ATbool lazy = (ATgetAFun(eq)==default_sym);
   ATermList patterns = (ATermList) ATgetArgument((ATermAppl) eq,0);
   ATerm right = ATgetArgument((ATermAppl) eq, 1);
   if (!ATisEmpty(patterns)) {
       P("\tif(");
       PRlinesConformPatterns(patterns);
       P(")\n");
       }
   /* ATwarning("QQ: %s %t", ATgetName(sym), right); */
   PRrightN(right, lazy);
   }
   
static void PRrules(ATermList as, ATermList rs, ATerm *subs, int k) {
   as = ATreverse(as);
   for (;!ATisEmpty(as);as=ATgetNext(as))
        {ATerm a = ATgetFirst(as);
        ATermList eqs = 
        (ATermList) ATgetArgument((ATermAppl) subs[ATgetInt((ATermInt) a)], k);
        ATerm key = (ATerm) ATmakeAppl1(getafun_sym, 
             selectVariable(ATmakeList1((ATerm) ATmakeInt(k))));
        ATerm var = ATtableGet(decl,key);
        P("\tif (%t==%d) {\n", var, indirect?rww_s[ATgetInt((ATermInt) a)]:
                                               ATgetInt((ATermInt) a));
        for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs))
             {ATerm eq = ATgetFirst(eqs);
             PRrule(eq);
             }
        P("\t}\n"); 
        }
    rs = ATreverse(rs);
    for (;!ATisEmpty(rs);rs=ATgetNext(rs))
        PRrule(ATgetFirst(rs));
    }
    
int LeastLengthRejected(ATermList *rejected, int n) {
    int l = 1000000, p = -1, i;
    for (i=0;i<n;i++) 
    if (ATgetLength(rejected[i])<l) {p = i; l = ATgetLength(rejected[i]);}
    return p;
    }

static void PRbody(AFun sym) {    
   if (indirect)
   P("\treturn rww_quick[%d]?rww_quick[%d]:(rww_quick[%d]=%s());\n",rww_s[sym],
   rww_s[sym], rww_s[sym], Fname("E", sym));
   else
   P("\treturn rww_substitute[%d]?rww_substitute[%d]:(rww_substitute[%d]=%s());\n",sym,
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
     P("\tif (ATgetArity(ATgetAFun(arg0))!=ATgetArity(ATgetAFun(arg1))||\n");
     P("\t ATgetAFun(arg0)!= ATgetAFun(arg1))\n"); 
     }
   P("\treturn MCRLterm_false;\n");
   }

                                 
static ATerm PRbodyCE(AFun sym) {
   int i = 0, n = ATgetArity(sym);
   ATermList eqs = (ATermList) symTab[sym];
   ATermList *rejected = NULL, *accepted = NULL;
   c_or_e = n==0?"E":"C"; /* E functions will be called at initialising */
   PRheader(sym); P("{\n"); 
   declaration = ATtrue;
   if (!rww_simple && n>0) AllocateArrays(n, &rww_substitute, &accepted, &rejected); 
   nvars = 0; ATtableReset(decl);
   for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
        ATermList patterns = (ATermList) ATgetArgument((ATermAppl)
           ATgetFirst(eqs),0);
       if (!ATisEmpty(patterns)) {
            if (!rww_simple && n>0) TransformPatterns(ATgetFirst(eqs), sym, accepted, rejected);
            PRlinesConformPatterns(patterns);
            }
       else if (!rww_simple) {
           for (i=0;i<n;i++)
           rejected[i] = Insert(rejected[i], ATgetFirst(eqs));
           /* Add default Rule */
           }
       }   
   declaration = ATfalse;
   if (rww_simple || n==0)    
   for (eqs = (ATermList) symTab[sym]; !ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
        PRrule(ATgetFirst(eqs)); 
        }
   else {
   if (rww_eq && MCRLgetType(sym)== MCRLeqfunction  && 
     MCRLisPureConstructorSort(
         ATgetAFun(ATgetArgument((ATermAppl) MCRLgetFunction(sym), 0)))) {
     PRshortCodeEqu(sym, 
     MCRLgetType(ATgetAFun(ATgetArgument((ATermAppl) MCRLgetFunction(sym), 0)))
     ==MCRLenumeratedsort?ATtrue:ATfalse); 
     for (eqs = (ATermList) symTab[sym]; !ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
        ATermAppl eq = (ATermAppl) ATgetFirst(eqs);
        ATermList p = (ATermList) ATgetArgument(eq, 0);
        if (ATgetLength(p)>=2) {
           ATerm a1 = ATgetArgument((ATermAppl) ATelementAt(p,0), 1);
           ATerm a2 = ATgetArgument((ATermAppl) ATelementAt(p,1), 1);
           AFun s1 = ATgetAFun(a1);
           AFun s2 = ATgetAFun(a2);
           if ((ATisEqual(a1, a2) && ATgetArity(s1)>0) 
               /* && (MCRLgetType(s1)>=MCRLfunction || 
               MCRLgetType(s2)>=MCRLfunction) */) {
           PRrule((ATerm) eq);
           }
           }
        else PRrule((ATerm) eq);
        }  
   } else {
     int k = LeastLengthRejected(rejected,n);
     PRrules(accepted[k], rejected[k], rww_substitute, k);
   }
   }
   P("\t}\n");
   if (rww_substitute) {
      ATunprotect(rww_substitute); free(rww_substitute); rww_substitute = NULL;
      ATunprotect((ATerm*) accepted); free(accepted); accepted = NULL;
      ATunprotect((ATerm*) rejected); free(rejected); rejected = NULL;
      }
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
   P("static ATerm innermost(ATerm t);\n");
   for (i=0;i<rww_size;i++) 
   if (symTab[i] && ATgetType(symTab[i])==AT_LIST) {
        ATerm t = PRbodyCE(i);
        if (t) initCalls = ATinsert(initCalls, 
             (ATerm) ATmakeList2(
             (ATerm) ATmakeInt(indirect?rww_s[i]:i),t));
        if (!rww_simple && MCRLgetType(i)==MCRLcasefunction)
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
   /* fprintf(stderr,"QQQ Command n=%d r = %s l = %d\n", n, r, strlen(r));  */
   return r;
   }
     
static void OutputRewriteSystem(char *filename) {  
    char a[256], b[512], *includedir=strdup(makefile);
    char includeline[256], *cmdstring; 
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
    strcpy(a, filename);
    sprintf(filename, "%s/%s.c", rww_debug||rww_write||rww_read_src?
         dyndir:DYNDIR, a);
    snprintf(includeline,256, "\"-I%s -I%s/.. -I%s/../aterm\"",
    includedir, includedir, includedir);
    if (!rww_read_src) {
       if (!(fp = fopen(filename,"w"))) {
            ATwarning("File %s cannot be opened", filename);
            exit(1);
            }
       PRdeclarations();
       PRval();
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
    strcat(a,".so");
    if (verbose) ATwarning("NOW COMPILING");
    cmdstring = Command("cd %s;%s -f %s %s %s %s%s %s CPP=%s %s", 
    rww_debug||rww_write?dyndir:DYNDIR, MAKE, makefile, verbose?"":"-s", a,
    "PROG=", b ,rww_debug?"DEBUG=\\#":"", includeline, "1>&2");
    /* ATwarning("%s",cmd); */
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
       while (rww_number_per_level <= rww_leveled_subs[i][0]) rww_number_per_level *= 2;
       }
   for (i=0;i<MAXLEVEL;i++) {
       if (!(rww_leveled_subs[i] = (int*) realloc(rww_leveled_subs[i],
             rww_number_per_level*sizeof(int))))
        ATerror("Cannot reallocate array (%d)", rww_number_per_level);
      }
   }
           
static void EnlargeSubstitute(AFun sym) {
      if (rww_n_substitute > sym) return;
      { long old=rww_n_substitute;
      ATunprotectArray(rww_substitute); 
      ATunprotectArray(rww_varnames);
      while (rww_n_substitute <= sym) rww_n_substitute *= 2;  
      if (!(rww_substitute = (ATerm*) realloc(rww_substitute, 
             rww_n_substitute*sizeof(ATerm))))
        ATerror("Cannot reallocate term array (%d)", rww_n_substitute);
      if (!(rww_varnames = (ATerm*) realloc(rww_varnames, 
             rww_n_substitute*sizeof(ATerm))))
        ATerror("Cannot reallocate term array (%d)", rww_n_substitute);
      for (;old<rww_n_substitute;old++) {
           rww_substitute[old]=NULL;
           rww_varnames[old]=NULL;
           }
      ATprotectArray(rww_substitute, rww_n_substitute); 
      ATprotectArray(rww_varnames, rww_n_substitute);
      }     
}

static void put_var(AFun f, ATerm t, int level) {
  if (level>0) {
    int n_vars = ++rww_leveled_subs[(--level)][0];
    if (n_vars < rww_number_per_level) 
        rww_leveled_subs[level][n_vars] = f; 
    else {
        if (ATisEqual(rww_substitute[f],rww_varnames[f])) {
           /* 
           ATerror("Too many substitutions (>%d) at level %d\n",PERLEVEL,level+1);
           */
           EnlargeDeclare();
           rww_leveled_subs[level][n_vars] = f; 
           }
        else
        rww_leveled_subs[level][0]--;
        }
   /*  Warning("QQ put_var n_vars = %d value = %s level = %d",
       n_vars, ATgetName(f), level); */
  }
  if (f>=rww_n_substitute)
    ATerror("Symbol index too high (%d > %d)\n",f, rww_n_substitute); 
  rww_substitute[f] =t;
}

static void reset_var(int level) {
  int n_vars,j;
  if (level>0) {
    n_vars=rww_leveled_subs[level-1][0];
    rww_leveled_subs[level-1][0]=0;
    for (j=1;j<=n_vars;j++) {
      AFun sym = rww_leveled_subs[level-1][j];
      /* Warning("QQ: Reset %s %d", ATgetName(sym), level);
      Warning("QQ: Reset2 %t", rww_varnames[sym]); */
      rww_substitute[sym]=  rww_varnames[sym];
      }
  }
  else
    ATerror("resetting level 0");
}

static void RWWstopStore(void) {
     rww_stop_store = ATtrue;
     }

static void RWWresumeStore(void) {
     rww_stop_store = ATfalse;
     }

static void RWWassignVariable(AFun var, ATerm t, ATerm tsort, int level) {
  if (level>=MAXLEVEL)
    ATerror("Level (%d) exceeds MAXLEVEL (%d)",level,MAXLEVEL);
  put_var(var,t,level);
  if (rww_db && autoCache) { 
      if (level==0) {
        if (!reset) ATtableReset(rww_db); reset = ATtrue;
        }
       else 
        RWWstopStore();
     }
  /* ATwarning("QQ: Assign %d %d  %d",autoCache,rww_stop_store,level); */
  }

static void RWWresetVariables(int level) {
  reset_var(level);
  if(rww_db && autoCache && level==1) RWWresumeStore();
 /* ATwarning("QQ: Reset %d %d  %d",autoCache,rww_stop_store,level); */
  }
  
static void RWWsetAutoCache(ATbool b) {
  autoCache = b;
  /* Warning("QQ: Setautocache %d %d",autoCache,rww_stop_store); */
  }
   
static void RWWdeclareVariable(ATerm t) {
   AFun s = ATgetAFun(t);
   /*
   ATwarning("QQ: declareVar %t %d > %d",t, rww_number_per_level, rww_number_of_vars);
   */
   EnlargeSubstitute(s);
   EnlargeDeclare();
   /* ATwarning("Declare %s (%d, %d) %t",ATgetName(s),s,ATgetArity(s), t); */ 
   rww_substitute[s] = rww_varnames[s]=t; 
   rww_number_of_vars++;
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
   return rww_substitute[var];
   }
   
static ATerm RWWrewrite(ATerm t) {
   /* ATwarning("QQ %t",MCRLprint(t)); */  
   if (rww_db) reset = ATfalse;
   return (*innermost_function) (t);   
   }
   
static ATermList RWWrewriteList(ATermList ts) {
   ATermList r = ATempty; 
   for (;!ATisEmpty(ts); 
        r = ATinsert(r,RWWrewrite(ATgetFirst(ts))),
        ts=ATgetNext(ts));
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
   if (rww_db) {
       ATtableDestroy(rww_db);
       rww_db = NULL;
       rww_stop_store = ATfalse;
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
   rww_size_s_inv = ATgetLength(fs);
   /* ATwarning("DefineIdx2Sym %d",rww_size_s_inv); */
   if (!(rww_s_inv=(int*) malloc(sizeof(int)*rww_size_s_inv)))
       ATerror("idx2sym not allocated (%d)", rww_size_s_inv);
   if (!(rww_quick=(ATerm*) calloc(rww_size_s_inv, sizeof(ATerm))))
       ATerror("rww_quick not allocated (%d)", rww_size_s_inv);
   ATprotectArray(rww_quick, rww_size_s_inv);
   if (!(rww_s = (int*) malloc(rww_size*sizeof(int))))
       ATerror("sym2idx not allocated (%d)", rww_size);
   if (!(funrec=(FUNREC*) malloc(sizeof(FUNREC)*rww_size_s_inv)))
       ATerror("funrec not allocated (%d)", rww_size_s_inv);
   for (i=0;!ATisEmpty(fs);fs=ATgetNext(fs),i++) {
      funrec[i].sym = ATgetAFun(ATgetFirst(fs));
      funrec[i].name = ATgetName(funrec[i].sym);
      funrec[i].arity = ATgetArity(funrec[i].sym);
      }
   qsort(funrec, rww_size_s_inv, sizeof(FUNREC), (compar_f) compare);
   for (i=0;i<rww_size;i++) rww_s[i] = -1;
   for (i=0;i<rww_size_s_inv; i++) {
      /* ATprotectSymbol((rww_s_inv[i] = funrec[i].sym)); */
      rww_s_inv[i] = funrec[i].sym;
 /* 
 ATwarning("Test i=%d sym = %d name = %a", i, funrec[i].sym, funrec[i].sym);
 */
      rww_s[funrec[i].sym] = i;
      }
   free(funrec);
   }

static int RwRead(int n, char **argv) {
    int k;for (k=0;k<n;k++) 
    if (!strcmp(argv[k],"-read-so")) return 1;
    return 0;
    } 
                 
static int RWWinitialiseRewriter(ATerm datatype, long rewritelimit, int hashvar) {
     FILE *np = NULL;
     static char *filename = NULL;
     ATerm sig = NULL;
     makefile = LocationRww();
     if (filename==NULL) filename = calloc(255, sizeof(char));
     if (!rww_read) {
     if (rww_read_src) strncpy(filename,rww_read_src,255);
     else
     if (rww_write) strncpy(filename,rww_write,255);
     else if (rww_debug) strncpy(filename,"RWW",255); 
     else  {
           sprintf(cmd, "%s -f %s %s all", MAKE, makefile, "-s");
           if (verbose) ATwarning("%s",cmd); 
           if ((np=Popen(cmd,"r"))==NULL)
               ATerror("Fail: %s",MAKE);
           if (fgets(filename, 255, np)==NULL) 
                 ATerror("Reading filename for %s not possible", MAKE);
           filename[strlen(filename)-1]='\0';
           Pclose(np);
           }
     }
     adt = datatype;
     hash = hashvar;
     ATprotect(&adt);
     MakeClean();
     if (hashvar && !rww_db) rww_db = ATtableCreate(250, 75);
     decl = ATtableCreate(250, 75);
     AllocateSymbolTable(); 
     ComputeSymbolTable();
     AddDefaultRules();
     if (indirect) DefineIdx2Sym();
     if (rww_read) {
         strncpy(filename,rww_read, 255);
         }
     else {
       OutputRewriteSystem(filename);
       if (rww_write) sprintf(filename,"%s/%s.so", dyndir, rww_write);
           else strcat(filename,".so");
       }
     rewriter_handle=dlopen(filename,RTLD_NOW);
     if (rewriter_handle==NULL) {
        ATerror("Loading %s fails: %s",filename, dlerror());
        system("rm -f so_locations");
        sprintf(cmd,"rm -f %s", filename);
        system(cmd);
        return 0;
        }
    if (!rww_debug && !rww_write && !rww_read) {
        sprintf(cmd,"rm -f %s", filename);
        system(cmd);
        }
    LoadInnermostFunction();
    sig = PerformLoadFunction("TestRewriteSystem");
    /* ATwriteToNamedTextFile(ATgetArgument((ATermAppl)MCRLgetAdt(), 0), 
    "mark"); */
    if (sig) {
       if (ATgetType(sig)==AT_LIST) {
           ATerm typ = ATelementAt((ATermList) sig, 1);
           if (!ATisEqual(typ, rww_term)) 
             ATerror("Wrong format of compiled file (format of -rww expected)");
           sig = ATgetFirst((ATermList) sig);
           }
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
    if (rww_db) ATtableReset(rww_db);
} 
   
static ATbool RWWinitialize(ATerm datatype) {
    if (!MCRLgetAdt() && !MCRLinitializeAdt(datatype)) return ATfalse; 
    RWWsetAutoCache(ATtrue);
    return (ATbool) RWWinitialiseRewriter(datatype, 0, hashvar); 
    }
        
static void RWWsetArguments(int *argc, char ***argv) {
     int i, j=0;
     char **newargv = (char**) calloc(*argc + 1, sizeof(char*)), *ptr;
     ATbool forbiddenAfterRead = ATfalse;
     int skip = RwRead(*argc, *argv);
     if (!newargv) ATerror("Cannot allocate array argv");
     dyndir = (char*) malloc(3*sizeof(char));
     strcpy(dyndir,"./"); strcpy(dyndir,"./");
     ptr = newargv[j++] = (*argv) [0];
     if (!(program=strrchr(ptr,'/'))) program = ptr;
     else program++;
     for(i=1;i<*argc;i++) {
     if (!strcmp((*argv)[i],"-simple")) {
          if (skip) continue;
          rww_simple = ATtrue;
          rww_eq = ATfalse;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-no-eq")) {
          if (skip) continue;
          rww_eq = ATfalse;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-eq")) {
          if (skip) continue;
          rww_eq = ATtrue;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-case")) {
          if (skip) continue;
          rww_case = ATtrue;
          forbiddenAfterRead = ATtrue;
          continue;
          }
     if (!strcmp((*argv)[i],"-debug")) {
          if (skip) continue;
          verbose = ATtrue;
          rww_debug = ATtrue;
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
     if (!strcmp((*argv)[i],"-read-so")) {
            if ((++i)<(*argc) && (*argv)[i][0] && strncmp((*argv)[i],"-",1)) {
                char *name = (*argv)[i], *ptr;
                rww_read = (char*) malloc(strlen(name)+5);
                if (strchr(name,'/')) rww_read[0]='\0';
                else strcpy(rww_read,"./");
                strcat(rww_read, name);
                if (!(ptr=strrchr(rww_read,'.')) || strcmp(ptr,".so")) 
                      strcat(rww_read,".so");
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
                rww_write = (char*) malloc((strlen(name)+4)*sizeof(char));
                dyndir = (char*) malloc((strlen(name)+1)*sizeof(char)); 
                if ((ptr=strrchr(name,'/'))) {
                    strcpy(rww_write, ptr+1);
                    strcpy(dyndir,name);
                    ptr = strrchr(dyndir,'/'); *ptr ='\0';
                    }
                else {
                    strcpy(dyndir,".");
                    strcpy(rww_write, name);
                    }
                if ((ptr=strrchr(rww_write,'.')) && !strcmp(ptr,".so")) *ptr = '\0';
                indirect = ATtrue;
                /* fprintf(stderr,"QQQ %s %s \n", rww_write, dyndir); */
                continue;
                }
            fprintf(stderr, "Option %s needs argument.\n",(*argv)[i-1]);
            exit(1);
            }
      if (!strcmp((*argv)[i],"-read-c")) {
            if ((++i)<(*argc) && strncmp((*argv)[i],"-",1)) {
                char *name = (*argv)[i], *ptr;
		if (skip) continue;
                rww_read_src = (char*) malloc(strlen(name)+5);
                dyndir = (char*) malloc((strlen(name)+1)*sizeof(char));
                strcpy(dyndir,"."); 
                if ((ptr=strrchr(name,'.')) && !strcmp(ptr,".c")) *ptr = '\0';
                if ((ptr=strrchr(name,'/'))) {
                    strcpy(rww_read_src, ptr+1);
                    *ptr = '\0';
                    strcpy(dyndir,name);
                    }
                else
                    strcpy(rww_read_src, name);
                continue;
                }
            fprintf(stderr, "Option %s needs argument.\n",(*argv)[i-1]);
            exit(1);
            }
        newargv[j++] = (*argv)[i];
        }
      *argc = j;  *argv = newargv;
      /*
      if (rww_read && forbiddenAfterRead) {
           fprintf(stderr, 
      "Compiled rewrite system will be loaded; rewriter options are not valid"
         ); 
         exit(1);
           }
	   */
     }
     
static void RWWhelp(void) {
  Pr("Extra options of rww are:");
  Pr("-simple:\t\tTranslation of rewrite rules without optimizing");
  Pr("-no-eq:\t\t\tNo optimisation at rewriting of eq rules"); 
  Pr("-debug:\t\t\tThe source code of the compiled rewrite system");
  Pr("\t\t\tis located on ./RWW.c and will not be removed. The source");
  Pr("\t\t\twill be compiled with the flag -g. Also the \".so\" file will");
  Pr( "\t\t\tnot be removed.");
  Pr("-write-so <file>\tWrites compiled rewrite system in \"<file>.so\"");
  Pr("-read-so <file>\t\tReads compiled rewrite system from \"<file>.so\"");
  Pr("-read-c <file>\t\tReads rewrite system source code from \"<file>.c\""); 
  }
           
TASKS RWWtasks = {RWWsetArguments, RWWinitialize, RWWassignVariable, 
RWWgetAssignedVariable, RWWresetVariables, RWWdeclareVariables,
RWWrewrite, RWWrewriteList, RWWsetAutoCache, RWWflush, RWWhelp};

#else

/*  ---------------------OUTPUTTEXT -------------------------------------- */


#define A(t,i) (ATgetArgument((ATermAppl) t ,i))
/* Extern variables */
extern ATerm *rww_varnames, *rww_substitute, *rww_quick, rww_term;
extern int rww_n_substitute, rww_number_of_vars, *rww_leveled_subs[],
     rww_number_per_level;
extern ATermTable rww_db;
extern int rww_size, rww_stop_store;
extern int *rww_s, *rww_s_inv;
typedef ATerm (*LOOKUP) (ATerm);
static ATerm innermost(ATerm t);
static void Unprotect(void);
static LOOKUP *lookup;

/* SUBSTITUTION */
static void Allocate(void) {
   int i;
   /* Warning("QQ: Allocate %d",rww_size, rww_number_per_level); */
   rww_n_substitute = rww_size;
   rww_substitute = (ATerm*) calloc(rww_n_substitute, sizeof(ATerm));
   rww_varnames = (ATerm*) calloc(rww_n_substitute,sizeof(ATerm));
   ATprotectArray(rww_substitute, rww_n_substitute); 
   ATprotectArray(rww_varnames, rww_n_substitute);
   for (i=0;i<MAXLEVEL;i++) {
       rww_leveled_subs[i] = (int*) calloc(rww_number_per_level, sizeof(int));
       }
   }

ATerm Free(void) {
   if (rww_varnames) {
      int i;
      ATunprotect(rww_substitute); free(rww_substitute); rww_substitute = NULL; 
      ATunprotect(rww_varnames); free(rww_varnames); rww_varnames = NULL;
      Unprotect();
      for (i=0;i<MAXLEVEL;i++) {
        free(rww_leveled_subs[i]);
      }
  }
  return (ATerm) NULL;
}

static ATerm Exit(AFun a) {
  ATerror("Variable/Function %a is not declared", a);
  return (ATerm) NULL;
  }
  
static ATerm GetVal(ATerm t) {
    static AFun a;
    a =  ATgetAFun(t);
    t = rww_substitute[a];
    return t?t:Exit(a); 
    /* return (ATerm) ((int) rww_substitute[ATgetAFun(t)] || (int) Exit(t)); */
    }
    
static ATerm GetVal2(ATerm t) {
    static AFun a;
    a =  ATgetAFun(t);
    t = rww_substitute[rww_s[a]];
    return t?t:Exit(a); 
    }
    
static ATerm DBget(ATerm t) {
    ATerm result = NULL;
    ATermTable db0 = NULL;
    if (rww_db) {
          if ((result = ATtableGet(rww_db, t)))  {
              if (rww_stop_store) {
                    db0 = rww_db; rww_db = NULL;
                    result = innermost(result);
                    rww_db = db0;
                    }
              }
          }
    return result;
    }

static void DBput(ATerm t, ATerm result) {
    ATtablePut(rww_db, t, result);
    }
    

#endif
