/* $Id: signature.c,v 1.4 2005/04/20 14:25:55 vdpol Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "aterm2.h"
#ifdef MCRLLIB
#include "rw.h"
#endif
#include "signature.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

static char VERBOSE=0;
#ifdef MCRLLIB
static int PRESERVE = 0;
#endif

static int max=0;

ATerm prTRUE;
ATerm prFALSE;
ATerm prBOOL;

 Symbol andF;
 Symbol orF;
 Symbol notF;
 Symbol iteF;

struct info {
  ATerm sort;
  char type; // 0=func, 1=map (but not eq), 2=eq (provided it is map)
};

static struct info *Fun;
static ATermTable Var;

static Symbol find_ite(ATermList maps) {
  ATerm t;
  Symbol sym;

  while (!ATisEmpty(maps)) {
    if (ATmatch(ATgetFirst(maps),
		"f(<term>,[\"Bool\",\"Bool\",\"Bool\"],\"Bool\")",
		&t)) {
      if (VERBOSE) ATfprintf(stderr,"Using as if-then-else symbol: %t\n",t);
      sym = ATmakeSymbol(ATgetName(ATgetSymbol(t)),3,ATtrue);
      ATprotectSymbol(sym);
      return sym;
    }
    maps = ATgetNext(maps);
  }
  ATerror("No if-then-else symbol found");
}

static void parse_argument_line(int *argc,char ***argv) {
  int i, j=0;
  char **newargv = (char**) calloc(*argc + 1, sizeof(char*));
  if (!newargv) ATerror("Cannot allocate array argv"); 
  newargv[j++] = (*argv)[0];
  for (i=1;i<*argc;i++) {
    if (!strcmp((*argv)[i],"-sig-verbose")) {
      VERBOSE=1;
      continue;
      }
#ifdef MCRLLIB
    if (!strcmp((*argv)[i],"-sig-preserve")) {
      PRESERVE=1;
      continue;
      }
#endif
      newargv[j++] = (*argv)[i];
  }
  *argc = j;  *argv = newargv; 
}

void Init_signature(ATerm signature, int argc,char *argv[]) {
  ATermList sorts,funcs,maps,todo,inputs;
  ATerm f,sort;
  Symbol sym;
  int i=0;

  parse_argument_line(&argc,&argv);
  if (!ATmatch(signature,"s(<term>,<term>,<term>)",
	       &sorts,&funcs,&maps))
    ATerror("Signature 's(sorts,funcs,maps)' expected\n");

  // First: find max index of funcs and maps

  todo=ATconcat(funcs,maps);
  while (!ATisEmpty(todo)) {
    if (!ATmatch((ATerm)todo,"[f(<term>,<term>,<term>),<list>]",
		 &f,&inputs,NULL,&todo))
      ATerror("Function declaration expected\n");
    
    i=ATgetLength(inputs);
    sym = ATmakeSymbol(ATgetName(ATgetSymbol(f)),i,ATtrue);
    ATprotectSymbol(sym);
    if ((int)sym > max) max = (int)sym;
  }

  /* Add 1000 to max, to allow for temporary function names 
     Jan Friso Groote. See function SignatureAddMap
  */

  max=max+1000;
  if (VERBOSE) ATfprintf(stdout,"MAX %d\n",max);

  // Next: Allocate array Fun, and fill it appropriately.
 
  Fun = (struct info*)calloc((size_t)max+1,sizeof(struct info));

  for (i=0; i<=max; i++) {
    Fun[i].sort = NULL;
    ATprotect(&Fun[i].sort);
  }
  
  todo=funcs;
  while (!ATisEmpty(todo)) {
    if (!ATmatch((ATerm)todo,"[f(<term>,<term>,<term>),<list>]",
		 &f,&inputs,&sort,&todo))
      ATerror("Function declaration expected\n");
    sym = ATmakeSymbol(ATgetName(ATgetSymbol(f)),ATgetLength(inputs),ATtrue);
    Fun[(int)sym].sort = sort;
    Fun[(int)sym].type = 0;
  }

  todo=maps;
  while (!ATisEmpty(todo)) {
    if (!ATmatch((ATerm)todo,"[f(<term>,<term>,<term>),<list>]",
		 &f,&inputs,&sort,&todo))
      ATerror("Function declaration expected\n");
    sym = ATmakeSymbol(ATgetName(ATgetSymbol(f)),ATgetLength(inputs),ATtrue);
    Fun[(int)sym].sort = sort;
    if (strncmp(ATgetName(sym),"eq#",3))
      Fun[(int)sym].type = 1;
    else
      Fun[(int)sym].type = 2;
  }


  // Now prefabricate Bool, True, False, And, Or, Not, Ite (if-then-else)

  prBOOL = ATmake("\"Bool\""); ATprotect(&prBOOL);
  prTRUE = ATmake("\"T#\"");  ATprotect(&prTRUE);
  prFALSE = ATmake("\"F#\""); ATprotect(&prFALSE);
  
  assert(Fun[(int)ATgetSymbol(prTRUE)].sort == prBOOL);
  assert(Fun[(int)ATgetSymbol(prFALSE)].sort == prBOOL);
  
  andF = ATmakeSymbol("and#Bool#Bool",2,ATtrue);
  ATprotectSymbol(andF);
  if (Fun[(int)andF].sort != prBOOL)
    ATerror("'and: Bool#Bool -> Bool' not found\n");
  orF = ATmakeSymbol("or#Bool#Bool",2,ATtrue);
  ATprotectSymbol(orF);
  if (Fun[(int)orF].sort != prBOOL)
    ATerror("'or: Bool#Bool -> Bool' not found\n");
  notF = ATmakeSymbol("not#Bool",1,ATtrue);
  ATprotectSymbol(notF);
  if (Fun[(int)notF].sort != prBOOL)
    ATerror("'not: Bool -> Bool' not found\n");
  iteF = find_ite(maps);
  // ATprotectSymbol(iteF);
  
  Var = ATtableCreate(1024,50);
}

/* next function has been added by Jan Friso Groote */
void SignatureAddMap(char *name,ATermList args,ATerm sort)
{
  AFun sym = ATmakeSymbol(name,ATgetLength(args),ATtrue);
  if ((int)sym>=max) ATerror("Too many temporary function symbols: %d %d",sym, max);
  Fun[(int)sym].sort = sort;
  Fun[(int)sym].type = 1;
}


#ifdef MCRLLIB
                   
void SignatureSetArguments(int *argc,char ***argv) {
    parse_argument_line(argc,argv);
} 
  
void SignatureInitialize(void) {
/* Is dependent of librw and .... libmcrl */
  ATermList sorts = NULL, funcs = NULL, maps = NULL,
  todo = NULL,inputs = NULL;
  ATerm f = NULL, sort = NULL, adt = NULL;
  Symbol sym =0, sym0 = 0, sym3 = 0;
  int i=0;
  ATerm signature = NULL;
  ATermList equations = NULL;

  prBOOL = MCRLterm_bool;
  prTRUE = MCRLterm_true;
  prFALSE = MCRLterm_false;

  {ATbool new=ATfalse;
   ATermList Sorts = (ATermList)ATgetArgument(ATgetArgument(MCRLgetAdt(),0),0);
  MCRLputAndFunction(&new);
  new=ATfalse;
  MCRLputOrFunction(&new);
  new=ATfalse;
  MCRLputNotFunction(&new);
  new=ATfalse;
  MCRLputIfFunction(prBOOL,&new);

  for (;!ATisEmpty(Sorts);Sorts=ATgetNext(Sorts)) {
    new=ATtrue;
    MCRLputEqFunction(ATgetFirst(Sorts),&new);
  }
  }

  adt = MCRLgetAdt();

  if (!ATmatch(adt,"d(<term>,<term>)",&signature,&equations))
    ATerror("Data specification expected.\n");
  if (!ATmatch(signature,"s(<term>,<term>,<term>)",
	       &sorts,&funcs,&maps))
    ATerror("Signature 's(sorts,funcs,maps)' expected\n");

  // First: find max index of funcs and maps

  todo=ATconcat(funcs,maps);
  while (!ATisEmpty(todo)) {
    if (!ATmatch((ATerm)todo,"[f(<term>,<term>,<term>),<list>]",
		 &f,&inputs,NULL,&todo))
      ATerror("Function declaration expected\n");
    sym = ATmakeSymbol(ATgetName(ATgetSymbol(f)),ATgetLength(inputs),ATtrue);
    ATprotectSymbol(sym);
    if ((int)sym > max) max = (int)sym;
  }
 
  /* Add 1000 to max, to allow for temporary function names 
     Jan Friso Groote. See function SignatureAddMap
  */

  max=max+1000;
  if (VERBOSE) ATfprintf(stdout,"MAX %d\n",max);

  // Next: Allocate array Fun, and fill it appropriately.
 
  Fun = (struct info*)calloc((size_t)max+1,sizeof(struct info));

  for (i=0; i<=max; i++) {
    Fun[i].sort = NULL;
    ATprotect(&Fun[i].sort);
  }
  
  todo=funcs;
  while (!ATisEmpty(todo)) {
    if (!ATmatch((ATerm)todo,"[f(<term>,<term>,<term>),<list>]",
		 &f,&inputs,&sort,&todo))
      ATerror("Function declaration expected\n");
    sym = ATmakeSymbol(ATgetName(ATgetSymbol(f)),ATgetLength(inputs),ATtrue);
    Fun[(int)sym].sort = sort;
    Fun[(int)sym].type = 0;
  }

  todo=maps;
  while (!ATisEmpty(todo)) {
    if (!ATmatch((ATerm)todo,"[f(<term>,<term>,<term>),<list>]",
		 &f,&inputs,&sort,&todo))
      ATerror("Function declaration expected\n");
    sym = ATmakeSymbol(ATgetName(ATgetSymbol(f)),ATgetLength(inputs),ATtrue);
    Fun[(int)sym].sort = sort;
    if (strncmp(ATgetName(sym),"eq#",3))
      Fun[(int)sym].type = 1;
    else
      Fun[(int)sym].type = 2;
  }

  // Now prefabricate Bool, True, False, And, Or, Not, Ite (if-then-else)

  andF = MCRLsym_and;
  if (Fun[(int)andF].sort != prBOOL)
    ATerror("'and: Bool#Bool -> Bool' not found\n");
  orF = MCRLsym_or;
  if (Fun[(int)orF].sort != prBOOL)
    ATerror("'or: Bool#Bool -> Bool' not found\n");
  notF = MCRLsym_not;
  if (Fun[(int)notF].sort != prBOOL)
    ATerror("'not: Bool -> Bool' not found\n");
  iteF = MCRLsym_ite;
  if (Fun[(int)iteF].sort != prBOOL)
    ATerror("'if: Bool#Bool#Bool -> Bool' not found\n");

  Var = ATtableCreate(1024,50);
}
#endif

void Declare_vars(ATermList vars) {
  ATerm var, sort;
  RWdeclareVariables(vars); /* Bert Lisser 8 Januari Jaco?? */
  while (!ATisEmpty(vars)) {
    if (!ATmatch((ATerm)vars,"[v(<term>,<term>),<list>]",&var,&sort,&vars))
      ATerror("Variable declaration '[v(var,sort),...]' expected\n");
    ATtablePut(Var,var,sort);
  }
}

ATerm Is_var(ATerm t) { 
  return ATtableGet(Var,t); 
}

ATerm Is_func(ATerm t) {
  // returns true for funcs, so type=0
  if (Is_var(t)) return NULL;
  if (!(Fun[(int)ATgetSymbol(t)].type))
    return Fun[(int)ATgetSymbol(t)].sort;
  return NULL;
}

ATerm Is_map(ATerm t){
  // returns true for maps, so type=1 or 2
  if (Is_var(t)) return NULL;
  if (Fun[(int)ATgetSymbol(t)].type)
    return Fun[(int)ATgetSymbol(t)].sort;
  return NULL;
}

char Is_eq(ATerm t) {
  // returns true for maps, so type=2
  if (Is_var(t)) return 0;
  return (Fun[(int)ATgetSymbol(t)].type == 2);
}

char Is_ite(ATerm t) {
  return ATgetSymbol(t)==iteF;
}

ATerm Sort_of(ATerm t) {
  int i;
  ATerm result = Is_var(t);
  if (result) { return result; }
  i=(int)ATgetSymbol(t);
  if (i<=max && (result=Fun[i].sort))
    return result;
  else
    ATerror("Sort of %t not found\n",t);
}

ATermList prettyprint_decls(ATermList decl) {
  // remove # from list of variable declarations

  ATermList todo = ATreverse(decl);
  decl = ATmakeList0();
  while (!ATisEmpty(todo)) {
    ATerm x, sort;
    char buf[1024];
    if (!ATmatch(ATgetFirst(todo),"v(<term>,<term>)",&x,&sort))
      ATerror("Variable declaration v(x,sort) expected.\n");
    strcpy(buf,ATgetName(ATgetSymbol(x)));
    x = ATmake("<appl>",strtok(buf,"#"));
    strcpy(buf,ATgetName(ATgetSymbol(sort)));
    sort = ATmake("<appl>",buf);
    decl = ATinsert(decl,ATmake("v(<term>,<term>)",x,sort));
    todo = ATgetNext(todo);
  }
  return decl;
}

ATermList parse_decls(ATermList decl) {
  // add # to list of variable declarations
  ATerm x, sort;
  char buf[1024];
  ATermList todo = ATreverse(decl);
  decl = ATmakeList0();
  while (!ATisEmpty(todo)) {
    if (!ATmatch(ATgetFirst(todo),"v(<term>,<term>)",&x,&sort))
      ATerror("Variable declaration v(x,sort) expected.\n");
    strcpy(buf,ATgetName(ATgetSymbol(x)));
    strcat(buf,"#");
    x=ATmake("<str>",buf);
    strcpy(buf,ATgetName(ATgetSymbol(sort)));
    sort=ATmake("<str>",buf);
    decl = ATinsert(decl,ATmake("v(<term>,<term>)",x,sort));
    todo = ATgetNext(todo);
  }
  return decl;
}

ATerm prettyprint(ATerm t) {
  Symbol f = ATgetSymbol(t);
  int n = ATgetArity(f);
  //ATerm* result = (ATerm*)alloca(n*sizeof(ATerm));
  DECLA(ATerm,result,n);
  int i;
  char buf[1024];
  strcpy(buf,ATgetName(f));
  f = ATmakeSymbol(strtok(buf,"#"),n,ATfalse);
  for (i=0;i<n;i++)
    result[i]=prettyprint(ATgetArgument(t,i));
  return (ATerm)ATmakeApplArray(f,result);
}

ATerm parse(ATerm t) {
  int i;
  char buf[1024];

  if (ATgetType(t)==AT_INT) {
    sprintf(buf,"%d#",ATgetInt((ATermInt)t));
    return ATmake("<str>",buf);
  }
  else {
    Symbol f = ATgetSymbol(t);
    int n = ATgetArity(f);
    //ATerm* result = (ATerm*)alloca(n*sizeof(ATerm));
    DECLA(ATerm,result,n);
    
    for (i=0;i<n;i++)
      result[i]=parse(ATgetArgument(t,i));
    
    strcpy(buf,ATgetName(f));
    strcat(buf,"#");
    
    for (i=0;i<n;i++) {
      strcat(buf,ATgetName(ATgetSymbol(Sort_of(result[i]))));
      if (i<n-1) strcat(buf,"#");
    }
    f = ATmakeSymbol(buf,n,ATtrue);
    t = (ATerm)ATmakeApplArray(f,result);
    
    if (Is_var(t) || ((int)f<=max && Fun[(int)f].sort)) return t;
    
    ATerror("Function or variable %s not found\n",buf);
  }
}

ATerm prEQ(ATerm t, ATerm s) {
  char eq[1024],buf[1024];
  ATerm sort;
  Symbol sym;
  sort = Sort_of(t);
  if (Sort_of(s) != sort)
    ATerror("apply eq on different sorts: %t:%t = %t:%t",
	    MCRLprint(t),sort,MCRLprint(s),Sort_of(s));
  assert(Sort_of(s)==sort);
  strcpy(buf,ATgetName(ATgetSymbol(sort)));
  sprintf(eq,"eq#%s#%s",buf,buf);
  sym = ATmakeSymbol(eq,2,ATtrue);
  if (Fun[(int)sym].sort != prBOOL)
    ATerror("Equality on sort %t is not declared\n",sort);
  return (ATerm)ATmakeAppl2(sym,t,s);
}

ATerm prAND(ATerm t, ATerm s) {return (ATerm)ATmakeAppl2(andF,t,s);}
ATerm prOR(ATerm t, ATerm s) {return (ATerm)ATmakeAppl2(orF,t,s);}
ATerm prNOT(ATerm t) {return (ATerm)ATmakeAppl1(notF,t);}
ATerm prIMPLIES(ATerm t, ATerm s) { return prOR(prNOT(t),s);}
ATerm prITE(ATerm e, ATerm high, ATerm low) {
  return (ATerm)ATmakeAppl3(iteF,e,high,low);}

ATerm read_formula(FILE* fp) {
  // read formula from file.

  ATerm t= MCRLparseFile(fp);
  // ATfprintf(stderr,"%t",t);
  return t;

  /*  int i=0,MAX=100000;
  char* s = (char*)malloc(MAX);
  ATerm t;
  while (i<MAX-1 && !feof(fp))
    s[i++]=fgetc(fp);
  if (!feof(fp))
    ATwarning("file with formula too long (increase MAX=%d)",MAX);
  s[i]='\0';
  t=MCRLparse(s);
  if (!t) {
    ATwarning("Couldn't read valid term");
    return NULL;
  }
  if (MCRLgetSort(t) != ATgetSymbol(MCRLterm_bool)) {
    ATwarning("formula is not of type Bool");
    return NULL;
  }
  // ATwarning("formula: %t\n",t);
  return t;
  */
}
