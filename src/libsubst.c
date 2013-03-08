/* $Id: libsubst.c,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdio.h>
#include <stdlib.h>
#include "aterm2.h"
#include "tasks.h"

#define A(t,i) ATgetArgument((ATermAppl) t ,i)
#define MAXLEVEL 3
#define PERLEVEL 2600

/*  Include file */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

static ATerm *substitute = (ATerm*) NULL;
static ATerm *varnames;
static int n_substitute = PERLEVEL;
static int number_per_level = PERLEVEL;
static ATermTable db;
static int *leveled_subs[MAXLEVEL], number_of_vars = 0;

static int Warning(const char *format, ...) {
   va_list ap;
   va_start(ap, format);
   return 0;
   }
   
static void EnlargeDeclare(void) { 
   int i;  
   while (number_per_level <= number_of_vars) number_per_level *= 2;
      for (i=0;i<MAXLEVEL;i++) {
       if (!(leveled_subs[i] = (int*) realloc(leveled_subs[i], 
             number_per_level*sizeof(ATerm))))
        ATerror("Cannot reallocate array (%d)", number_per_level);
      }
   }
           
static void EnlargeSubstitute(AFun sym) {
      if (n_substitute > sym) return;
      { long old=n_substitute;
      ATunprotectArray(substitute); 
      ATunprotectArray(varnames);
      while (n_substitute <= sym) n_substitute *= 2;  
      if (!(substitute = (ATerm*) realloc(substitute, 
             n_substitute*sizeof(ATerm))))
        ATerror("Cannot reallocate term array (%d)", n_substitute);
      if (!(varnames = (ATerm*) realloc(varnames, 
             n_substitute*sizeof(ATerm))))
        ATerror("Cannot reallocate term array (%d)", n_substitute);
      for (;old<n_substitute;old++) {
           substitute[old]=NULL;
           varnames[old]=NULL;
           }
      ATprotectArray(substitute, n_substitute); 
      ATprotectArray(varnames, n_substitute);
      }     
}

static void put_var(AFun f, ATerm t, int level) {
  if (level>0) {
    int n_vars = ++leveled_subs[level-1][0];
    leveled_subs[level-1][n_vars] = f;
   /*  Warning("QQ put_var n_vars = %d value = %s level = %d",
       n_vars, ATgetName(f), level); */
  }
  if (f>=n_substitute)
    ATerror("Symbol index too high (%d > %d)\n",f, n_substitute);
  substitute[f] =t;
}

static void reset_var(int level) {
  int n_vars,j;
  if (level>0) {
    n_vars=leveled_subs[level-1][0];
    leveled_subs[level-1][0]=0;
    for (j=1;j<=n_vars;j++) {
      AFun sym = leveled_subs[level-1][j];
      /* Warning("QQ: Reset %s %d", ATgetName(sym), level);
      Warning("QQ: Reset2 %t", varnames[sym]); */
      substitute[sym]=  varnames[sym];
      }
  }
  else
    ATerror("resetting level 0");
}
/* SUBSTITUTION */

static void Allocate(void) {
   int i;
   Warning("QQ: Allocate %d",n_substitute, number_per_level);
   substitute = (ATerm*) calloc(n_substitute, sizeof(ATerm));
   varnames = (ATerm*) calloc(n_substitute,sizeof(ATerm));
   ATprotectArray(substitute, n_substitute); 
   ATprotectArray(varnames, n_substitute);
   for (i=0;i<MAXLEVEL;i++) {
       leveled_subs[i] = (int*) calloc(number_per_level, sizeof(int));
       }
   Warning("End of allocating");
   }

static void Free(void) {
   if (varnames) {
      int i;
      ATunprotect(substitute); free(substitute); substitute = NULL; 
      ATunprotect(varnames); free(varnames); varnames = NULL;
      for (i=0;i<MAXLEVEL;i++) {
        free(leveled_subs[i]);
      }
  }
}
     
static ATerm Subst(ATerm t){
     ATerm result = NULL;
     AFun sym = ATgetAFun(t);
     int n = ATgetArity(sym), i = 0;
     ATerm *aux = NULL;
     if (n==0) return substitute[ATgetSymbol(t)]?
           substitute[ATgetSymbol(t)]:t;
     if (db) {
          result = ATtableGet(db, t);
          if (result) return result;
          }
     aux = (ATerm*) calloc(n, sizeof(ATerm));
     ATprotectArray(aux, n);
     for (i=0;i<n;i++)
        aux[i] = Subst(A(t, i));
     result =  (ATerm) ATmakeApplArray(sym, aux); 
     if (db) ATtablePut(db, t, result);
     ATunprotect(aux); free(aux);
     return result;                 
     }
     
static void RWassignVariable(AFun var, ATerm t, ATerm tsort, int level) {
  if (level>=MAXLEVEL)
    ATerror("Level (%d) exceeds MAXLEVEL (%d)",level,MAXLEVEL);
  put_var(var,t,level);
  /* ATwarning("QQ: Assign %d %d  %d",autoCache,stop_store,level); */
  }

static void RWresetVariables(int level) {
  reset_var(level);
  }
     
static void RWdeclareVariable(ATerm t) {
   AFun s = ATgetAFun(t);
   /*
   ATwarning("QQ: declareVar %t %d > %d",t, number_per_level, number_of_vars);
    */
   EnlargeSubstitute(s);
   EnlargeDeclare();
   substitute[s] = varnames[s]=t; 
   number_of_vars++;
   }

static void RWdeclareVariables(ATermList vars) {
  /* ATfprintf(stderr,"Declare: %t\n",vars); */
  for (;!ATisEmpty(vars);vars = ATgetNext(vars)) {
    ATerm var = ATgetFirst(vars);
    if (ATgetArity(ATgetSymbol(var))==2) var = 
      ATgetArgument(ATgetFirst(vars),0);
    RWdeclareVariable(var);
  }
}

static ATerm RWgetAssignedVariable(AFun var) {
   return substitute[var]?substitute[var]:(ATerm) ATmakeAppl0(var);
   }
   
static ATerm RWrewrite(ATerm t) {
   return Subst(t);   
   }
   
static ATermList RWrewriteList(ATermList ts) {
   ATermList r = ATempty; 
   for (;!ATisEmpty(ts); 
        r = ATinsert(r,RWrewrite(ATgetFirst(ts))),
        ts=ATgetNext(ts));
   return ATreverse(r);
   }
                
static int RWinitialiseRewriter(ATerm datatype, long rewritelimit, int hashvar) {
     /* ATwarning("QQ Entry init %d %s", hashvar, ATgetName(0)); */
   Free();
   Allocate();
   return 1; 
   }
    
static ATbool RWinitialize(ATerm datatype) {
    return (ATbool) RWinitialiseRewriter(datatype, 0, 0); 
    }

static void RWflush(void) {
    if (db) ATtableReset(db);
    }
           
static void RWsetArguments(int *argc, char ***argv) {
     int i, j=0;
     char **newargv = (char**) calloc(*argc + 1, sizeof(char*));
     db = ATtableCreate(250, 75);
     if (!newargv) ATerror("Cannot allocate array argv");
     newargv[j++] = (*argv) [0];
     for(i=1;i<*argc;i++) {
     if (!strcmp((*argv)[i],"-no-hash")) {
          ATtableDestroy(db);
          db = NULL;
          continue;
          }
     if (!strcmp((*argv)[i],"-hash")) {
          continue;
          }
        newargv[j++] = (*argv)[i];
        }
      *argc = j;  *argv = newargv;
     }

static void RWhelp(void) {
  }
           
TASKS SUBStasks = {RWsetArguments, RWinitialize, RWassignVariable, 
RWgetAssignedVariable, RWresetVariables, RWdeclareVariables,
RWrewrite, RWrewriteList, (RWSETAUTOCACHE) NULL, RWflush, RWhelp};





