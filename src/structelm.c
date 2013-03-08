/*$Id: structelm.c,v 1.7 2007/06/19 09:35:57 bertl Exp $*/

#include "string.h"
#include "rw.h"

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#define LEN  1024
#define N_ENUMERATED_SORTS 60

char *who = "Structelm";

static ATerm detTag = NULL, projTag = NULL;

static ATbool expand = ATfalse, report = ATfalse, 
binary = ATfalse, candidates = ATfalse,
verbose = ATfalse;

int depth = 1;

static ATermTable tab;

static char *vname = "_v",/*  *wname = "_w", */ *ename = "_e";

static ATerm proc = NULL , proc0 = NULL, adt = NULL, sig = NULL;

static ATermList expandtypelist=NULL, expandnamelist=NULL, 
newDetSorts=NULL, choiceVariables=NULL; 

static ATerm label=NULL;

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
    Pr("Usage: structelm [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\tYields this message.");
    Pr("-version:\tGet the version number of this release.");
    Pr("-ascii:\t\tWrites .tbf file in ascii code.");
    Pr("-report:\tReturns a list of composite sorts.");
    Pr("-expand <sort>:\tFlag to specify which sort must be expanded.");
    Pr("-binary:\tBinary case functions will be used.");
    Pr("-verbose:\tPrints messages during run.");
    Pr("-depth <num>:\tThe recursion depth of the expanding.");
    }

static void help(void)
    {
    Pr("");
    helpmsg();
    Pr("");
    }

static void version(void)
    {
    /*
    Pr("$Id: structelm.c,v 1.7 2007/06/19 09:35:57 bertl Exp $");
    */
    char buf[100];
    sprintf(buf, "%s: version %s", who, VERSION);
    Pr(buf);
    }



char *Name(char *format,...)
    {
    static char buf[256];
    va_list ap;
    va_start(ap, format);
    vsprintf(buf,format,ap);
    return buf;
    }

static void DeclareVariables(ATermList pars, ATermList sums) {
  RWdeclareVariables(pars);
  for (;!ATisEmpty(sums);sums=ATgetNext(sums)) {
     ATerm sum = ATgetFirst(sums);
     ATermList vars = MCRLgetListOfVars(sum);
     RWdeclareVariables(vars);
     }
}

static void Initialize(void) {
    ATprotect(&label);
    ATprotect((ATerm*) &newDetSorts);
    ATprotect((ATerm*) &expandtypelist);
    ATprotect((ATerm*) &choiceVariables);
    proc0 = proc = MCRLgetProc();
    adt = MCRLgetAdt();
    sig = ATgetArgument((ATermAppl) adt, 0);
    ATprotect(&adt);
    ATprotect(&sig);
    ATprotect(&proc);
    label = ATmake("<appl>","sortlabel");
    expandtypelist = ATmakeList0();
    choiceVariables = ATmakeList0();
    newDetSorts = ATmakeList0(); 
    DeclareVariables(MCRLgetListOfPars(), MCRLgetListOfSummands());
    }


/* ----------------------------- CREATION PART ---------------------------- */ 
         
static void GenerateNewCaseFunctions(ATerm sig, ATermList sorts) {
     /* Puts the case function needed for the expansion as first element
     of the list */
     for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts))
          {ATerm sort = ATgetFirst(sorts);
          ATbool new = ATtrue;
          int n = binary?2:MCRLgetNumberOfConstructors(ATgetAFun(sort));
          if (MCRLputCaseFunction(n, sort, &new)==0) 
          ATerror("Forbidden to add case function with sort %t and arity %d",
               sort, n);
          }
     }
                 
static ATermList CreateDetNormal(ATerm sort) {
     int n = MCRLgetNumberOfConstructors(ATgetAFun(sort));
     Symbol sortsym = ATgetSymbol(sort);
     ATbool new = ATfalse;
     AFun esort = 
     ATgetAFun(ATgetArgument((ATermAppl) 
         MCRLgetFunction(MCRLputCaseFunction(n, sort, &new)), 0));
     char *esortname = ATgetName(esort);
     ATerm f = MCRLuniqueTerm(Name("Det-%s",esortname), ATmakeList1(sort));
     ATerm fname = ATmake("<str>",ATgetName(ATgetAFun(f)));
     ATerm result = ATmake("f(<term>, <term>, <term>)", fname, 
          ATmakeList1(sort), (ATerm) ATmakeAppl0(esort));
     ATermList oldDets = MCRLgetDetFunctions(sortsym);
     if (oldDets && ATgetLength(oldDets)==1) 
          return ATempty;
     MCRLdeclareFunction(f, MCRLfunction, esort);
     /* ATwarning("QQ:MCRLsetDetFunctions %t %t", sort, f); */
     MCRLsetDetFunctions(sortsym, ATmakeList1(f));
     return ATmakeList1(result);
     }
     
static ATermList CreateDetBinary(ATerm sort) {
     int n = MCRLgetNumberOfConstructors(ATgetAFun(sort)), k = 1, l = 0;
     ATbool new = ATfalse;
     Symbol sortsym = ATgetSymbol(sort);
     AFun esort = 
     ATgetAFun(ATgetArgument((ATermAppl) 
         MCRLgetFunction(MCRLputCaseFunction(2, sort, &new)), 0));
     char *esortname = ATgetName(esort);
     ATermList result = ATmakeList0(), dets = ATempty;
     
     /*
     oldDets = MCRLgetDetFunctions(sortsym);
     if (oldDets &&  (ATgetLength(oldDets)>1 || 
        (ATgetLength(oldDets)==1 && 
     MCRLgetSort(ATgetFirst(oldDets)) == ATgetAFun(MCRLterm_bool)))) 
          return result;
     */
     for (;k<n;k*=2, l++) {
          ATerm f = MCRLuniqueTerm(Name("Det-%s-%d",esortname,l), 
          ATmakeList1(sort));
          ATerm fname = (ATerm) ATmake("<str>", ATgetName(ATgetSymbol(f))); 
          result = ATinsert(result, 
          ATmake("f(<term>, <term>, <term>)", fname, 
          ATmakeList1(sort), (ATerm) ATmakeAppl0(esort)));
          MCRLdeclareFunction(f, MCRLfunction, esort);
          dets = ATinsert(dets, f);
          }
     MCRLsetDetFunctions(sortsym, ATreverse(dets));
     return result;
     } 

static ATermList CreateDet(ATerm sort) {
     if (binary) return CreateDetBinary(sort);
     return CreateDetNormal(sort); 
     }
       
static ATermList ConstructorCreateProjections(
     ATermList maps, ATerm constructor, int k, ATerm sort)
     {
     Symbol sortsym = ATgetSymbol(sort);
     ATermList args = ATgetArguments((ATermAppl) constructor);
     int i = 0;
     if (!MCRLgetProjections(sortsym)) 
     for (i=0;!ATisEmpty(args);args=ATgetNext(args),i++)
          {ATerm arg = ATgetFirst(args);
          Symbol argsym = ATgetSymbol(arg);
          ATerm f = MCRLuniqueTerm(Name("Pi-%d-%s-%s-%d",
          k, MCRLgetName(constructor) , ATgetName(argsym),i),
          ATmakeList1(sort));
          ATerm fname = (ATerm) ATmake("<str>", ATgetName(ATgetSymbol(f)));
          ATerm result = ATmake("f(<term>, <term>, <term>)", fname, 
                    ATmakeList1(sort), arg);
          MCRLdeclareFunction(f, MCRLfunction, argsym);
          MCRLsetProjection(ATgetAFun(constructor), i, f);
          if (ATindexOf(maps, result, 0) < 0)  maps = ATinsert(maps, result);
          }
     return maps;
     }  
        
static ATermList CreateProjections(ATermList maps, ATerm sort)
     {
     ATermList constructors = MCRLgetConstructors(ATgetAFun(sort));
     int i = 0;
     ATermList dets = CreateDet(sort);
     if (ATindexOf(newDetSorts, sort,0) < 0)  
           newDetSorts = ATinsert(newDetSorts, sort);
     for (;!ATisEmpty(dets);dets = ATgetNext(dets)) {
         ATerm det = ATgetFirst(dets);
          if (ATindexOf(maps, det,0) < 0)
             { 
             maps = ATinsert(maps, det);
             }
         }
     for (;!ATisEmpty(constructors);constructors=ATgetNext(constructors),i++)
          {ATerm constructor = ATgetFirst(constructors);
          maps = ConstructorCreateProjections(maps, constructor, i, sort);
          }
     return maps;
     }
               
static ATerm GenerateNewMaps(ATerm sig, ATermList sorts)
     {
     /* Detmaps en Pi maps */
     ATermList maps = (ATermList) ATgetArgument((ATermAppl) sig, 2);
     for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts))
          {ATerm sort = ATgetFirst(sorts);
          maps = CreateProjections(maps, sort);
          }
     return ATmake("s(<term>,<term>,<term>)",
           ATgetArgument((ATermAppl) sig, 0),
           ATgetArgument((ATermAppl) sig, 1),
           maps);    
     }
          
static ATbool IsRealConstructorSort(ATerm fsort) {
      ATermList constructors = MCRLgetConstructors(ATgetAFun(fsort));
      for (;!ATisEmpty(constructors);constructors=ATgetNext(constructors)) {
         ATerm constructor = ATgetFirst(constructors);
         if (!ATisEmpty(MCRLgetRewriteRules(ATgetAFun(constructor)))) {
             if (report) 
                 ATwarning("%t is rejected as candidate (because of constructor %t)",
                 MCRLprint(fsort), MCRLprint(constructor));
         return ATfalse;
         }
      }
      return ATtrue;
      }
                
static ATermList GenerateAllConstructorSorts(void)
    {
    ATerm sig = ATgetArgument(adt,0);
    ATermList sorts = (ATermList) ATgetArgument(sig,0),
    result = ATmakeList0();
    for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts))
          {ATerm sort = ATgetFirst(sorts);
          if (MCRLgetType(ATgetAFun(sort))==MCRLconstructorsort) {
               ATermList constructors = MCRLgetConstructors(
                               ATgetAFun(sort));
               ATermList casefunctions = MCRLgetCaseFunctions(
                         ATgetAFun(sort));
               int n = ATgetLength(constructors);
               if (!IsRealConstructorSort(sort)) continue;
               if (report) {
                    ATerm t = MCRLdummyVal(ATgetAFun(sort));
                    if (!t) ATwarning("Constructors of sort %t", sort);
                    else
                    ATwarning("Constructors of sort %t with dummy %t", sort,
                    MCRLprint(MCRLdummyVal(ATgetAFun(sort))));
                    }
	       if (candidates) {
	          ATfprintf(stdout, "%t = %t\n", MCRLprint(sort),
                     MCRLprint(MCRLdummyVal(ATgetAFun(sort))));
	       }
               for (;!ATisEmpty(constructors);constructors=ATgetNext(constructors)) {
                   ATerm constructor = ATgetFirst(constructors);
                   if (report) ATwarning("\t%t",MCRLprint(constructor));
                   }
               result = ATinsert(result, sort);
               if (report)
                    {        
                    if (MCRLgetEnumSort(n)==0)
                    ATwarning("Enumerated sort of size %d must be constructed",n);
                    else
                    ATwarning("Enumerated sort %a is already present",
                    MCRLgetEnumSort(n));
               
                    /* ATwarning("Case functions"); */
                    for (;!ATisEmpty(casefunctions);casefunctions=ATgetNext(casefunctions))
                    {ATerm casefunction = ATgetFirst(casefunctions);
                    if (ATgetLength(ATgetArguments((ATermAppl)
                         casefunction)) == n + 1)
                         {
                         ATwarning("\tNeeded casefunction %t found",
                         MCRLprint(casefunction));
                         break;
                         }
                    }
                    if (ATisEmpty(casefunctions)) 
                    if (verbose) ATwarning("Casefunction not found");
                    }
               }
          }
    return ATreverse(result);
    }

static ATermList SelectSorts(ATermList constructorsorts, ATermList names)
     {
     ATermList result = names;
     for (;!ATisEmpty(names);names=ATgetNext(names))
          {ATerm name = ATgetFirst(names);
          if (ATindexOf(constructorsorts, name, 0)<0) 
               ATerror("Sort %t is not a constructor sort\n", name);
          }
     return result;
     }

/* ----------------------------- EQUATION PART ---------------------------- */
 
static ATerm *BinaryTree(ATerm parsort) {
    ATermList constructors = MCRLgetConstructors(ATgetAFun(parsort));
    int n = ATgetLength(constructors),i=0, d=n;
    unsigned int mask=1; 
    ATerm *aux = (ATerm*) calloc(2*n, sizeof(ATerm));
    ATerm caseFunction = 
                 ATgetFirst(MCRLgetCaseFunctions(ATgetAFun(parsort))); 
    Symbol caseSymbol = ATgetSymbol(caseFunction);
    ATprotectArray(aux, 2*n);
    for (i=n;!ATisEmpty(constructors);
         constructors=ATgetNext(constructors), i++)
           {ATerm constructor = ATgetFirst(constructors);
           aux[i] = constructor;
           }
    for (i=n-1;i>=1;i--) {
          if (2*i <d) {d = i+1; mask=mask<<=1;} 
	   aux[i]=(ATerm) 
             ATmakeAppl3(caseSymbol,  
                 (ATerm) ATmakeInt((int) mask), aux[i+i], aux[i+i+1]);
           } 
    return aux;
    }

static int UpperBound(int n) {
   int m = 1;
   for (;m<n;m*=2);
   return m;
   }
   
static int WordSize(int n) {
   int m = 1, d = 0;
   for (;m<n;m*=2, d++);
   return d;
   }
static ATerm FindConstructor(ATerm *aux, int n, int code) {
/* Find constructor which is reached by traversing the path defined in
   parameter code */
   unsigned int mask = 0;
   int i = 1;
   for (;i<n;i= ((code&mask)?2*i+1:2*i)) {
       mask = 
       (unsigned int) ATgetInt((ATermInt) ATgetArgument((ATermAppl) aux[i], 0));   
   }
   return aux[i];
} 

static ATerm Search2(ATermList ls) {
    for (;!ATisEmpty(ls);ls=ATgetNext(ls))
       if (ATgetArity(ATgetAFun(ATgetFirst(ls)))==3) return ATgetFirst(ls);
    return NULL;
    }
    
static ATermList MakeVal(ATerm parsort, int n, int code) {
   ATermList sels = MCRLgetCaseSelectors(ATgetSymbol(Search2(
             MCRLgetCaseFunctions(ATgetAFun(parsort))))), 
   result = ATmakeList0();
   unsigned int mask = 1, m = WordSize(n), i = 0; 
   for (;i<m;i++, mask = mask<<1) {
        result = ATinsert(result, 
        code&mask?ATelementAt(sels, 1): ATelementAt(sels, 0)); 
        } 
    /* ATfprintf(stderr,"QQ: code = %d result = %t\n",code, result); */              
    return result;              
  } 

static void FillConstructorTable(ATerm parsort) {
    int n = MCRLgetNumberOfConstructors(ATgetAFun(parsort));
    int m = UpperBound(n), i = m-1;
    ATerm *aux = BinaryTree(parsort);
    if ((tab=ATtableCreate(50,75))==NULL) ATerror("Cannot allocate table");
    for (;i>=0;i--) {
        ATerm key = FindConstructor(aux, n, i);
        ATermList vals = MakeVal(parsort,n, i);
        /* ATwarning("QQ: TablePut %t %t",key, vals); */
        ATtablePut(tab, key, (ATerm) vals);
    }
    ATunprotect(aux);
    free(aux);
}

static ATerm CreateDetEq(ATerm constructor, ATerm val, ATerm leftname)
     {
     ATermList args = ATgetArguments((ATermAppl) constructor),
          vars = ATmakeList0(), newargs = ATmakeList0();
     int i = 0;
     for (;!ATisEmpty(args);args=ATgetNext(args),i++)
          {ATerm arg = ATgetFirst(args);
          ATerm varname  = 
          ATmake("<str>", MCRLextendName(Name("%s%d",vname,i), ATempty));
          newargs = ATinsert(newargs, varname);
          vars = ATinsert(vars, ATmake("v(<term>,<term>)",varname, 
                 ATremoveAllAnnotations(arg)));
          }
     return ATmake("e(<term>,<term>,<term>)",vars, 
     ATmakeAppl1(ATgetSymbol(leftname), (ATerm) ATmakeApplList(ATgetSymbol(constructor),
     ATreverse(newargs))), val);
     }
     
static ATerm NewConstructor(ATerm constructor, ATerm val) {
     ATermList anno = (ATermList) ATgetAnnotation(constructor, detTag);
     if (!anno) anno = ATmakeList0();
     anno = ATappend(anno, val);
     constructor=ATsetAnnotation(constructor, detTag, (ATerm) anno);
     return constructor;
     }

static ATermList GenerateDetEqsNormal(ATermList eqs, ATerm sort, int *nDets) {
     ATermList newconstructors = ATmakeList0();
     ATermList vals = MCRLgetCaseSelectors(
     ATgetSymbol(ATgetFirst(
          MCRLgetCaseFunctions(ATgetAFun(sort))))),
     constructors = MCRLgetConstructors(ATgetAFun(sort));
     ATerm leftname = ATgetFirst(MCRLgetProjections(ATgetAFun(sort)));
     ATerm anno = ATgetAnnotation((ATerm) constructors, projTag);
     // ATfprintf(stderr,"anno= %t\n", anno);
     for (;!ATisEmpty(constructors) && !ATisEmpty(vals);
          constructors=ATgetNext(constructors), vals=ATgetNext(vals))
          {ATerm constructor = ATgetFirst(constructors),
          val = ATgetFirst(vals);
          ATerm eq = CreateDetEq(constructor, val, leftname);
          eqs = ATinsert(eqs, eq);
          newconstructors = ATinsert(newconstructors, 
                           NewConstructor(constructor, val));
          }
     newconstructors = ATreverse(newconstructors);
     if (anno) newconstructors = (ATermList) 
                        ATsetAnnotation((ATerm) newconstructors, projTag, anno);
     MCRLsetConstructors(ATgetAFun(sort), newconstructors);
     *nDets = 1;
     return eqs;
     }
     
static ATermList GenerateDetEqsBinary(ATermList eqs, ATerm parsort, int *nDets) {
     ATermList constructors = MCRLgetConstructors(ATgetAFun(parsort)),
     newconstructors = ATmakeList0(),
     dets0 = MCRLgetProjections(ATgetAFun(parsort));
     ATerm anno = ATgetAnnotation((ATerm) constructors, projTag);
     FillConstructorTable(parsort);
     *nDets = 0;
     for (;!ATisEmpty(constructors);
          constructors=ATgetNext(constructors))
          {ATerm constructor = ATgetFirst(constructors);
          ATermList sels = (ATermList) ATtableGet(tab, constructor),
          dets = dets0;
          if (ATgetLength(sels)> *nDets) *nDets = ATgetLength(sels);
          for (;!ATisEmpty(sels);sels=ATgetNext(sels),dets=ATgetNext(dets))
               {ATerm sel = ATgetFirst(sels), det = ATgetFirst(dets);
                ATerm eq = CreateDetEq(constructor, sel, det);
                /* ATfprintf(stderr, "QQ: eq = %t\n",eq); */
                eqs = ATinsert(eqs, eq);
          newconstructors = ATinsert(newconstructors, 
                           NewConstructor(constructor, sel));
               }
          }
     newconstructors = ATreverse(newconstructors);
     if (anno) newconstructors = (ATermList) 
                        ATsetAnnotation((ATerm) newconstructors, projTag, anno);
     MCRLsetConstructors(ATgetAFun(parsort), newconstructors);
     ATtableDestroy(tab);
     return eqs;
     }
     
static ATermList GenerateDetEqs(ATermList eqs, ATerm parsort, int *nDets) {
     if (binary) return GenerateDetEqsBinary(eqs, parsort, nDets);
     return GenerateDetEqsNormal(eqs, parsort, nDets);
     }
          
static ATerm CreateProjection(ATerm proj, ATerm constructor, 
     ATerm index_constructor, int pos, ATerm dummy)
     {
     /* Pi_i^k(f_i(...,x_k...) = x_k */
     ATermList args = ATgetArguments((ATermAppl) constructor),
          vars = ATmakeList0(), newargs = ATmakeList0();
     ATerm left = NULL, right = dummy, eq = NULL;   
     int i=0;
     for (;!ATisEmpty(args);args=ATgetNext(args),i++)
          {ATerm arg = ATgetFirst(args);
          ATerm varname  = ATmake("<str>",
                MCRLextendName(Name("%s%d",vname,i), ATempty));
          newargs = ATinsert(newargs, varname);
          vars = ATinsert(vars, ATmake("v(<term>,<term>)",varname, 
                 ATremoveAllAnnotations(arg)));
          if (i==pos && ATisEqual(constructor, index_constructor)) 
               right = varname;
          }
     left = (ATerm) ATmakeAppl1 (ATgetSymbol(proj),(ATerm) ATmakeApplList(ATgetSymbol(constructor),
     ATreverse(newargs)));
     eq = ATmake("e(<term>,<term>,<term>)",vars, left , right);
     return eq;
     }
     
static ATermList CreateEqsBelongingToProjection(ATermList eqs, ATerm proj, 
     ATerm index_constructor, int pos, ATerm sort)
     {
     ATermList constructors = MCRLgetConstructors(ATgetAFun(sort));
     ATerm dummy = MCRLdummyVal(
     ATgetAFun(ATelementAt(ATgetArguments((ATermAppl) 
          index_constructor),pos)));
     for (;!ATisEmpty(constructors); constructors=ATgetNext(constructors))
          {ATerm constructor = ATgetFirst(constructors);
          eqs = ATinsert(eqs, 
          CreateProjection(proj, constructor, index_constructor, pos, dummy));
          }
     return eqs;
     }

static ATermList GenerateProjEqs(ATermList eqs, ATerm sort, int n)
     {
     ATermList projs = ATgetTail(MCRLgetProjections(ATgetAFun(sort)), n),
     constructors = MCRLgetConstructors(ATgetAFun(sort));
     for (;!ATisEmpty(constructors); constructors = ATgetNext(constructors))
          {ATerm constructor = ATgetFirst(constructors);
          int m = ATgetLength(ATgetArguments((ATermAppl) constructor)),
          i = 0;
          for (;i<m;i++, projs=ATgetNext(projs))
               {
               ATerm proj = ATgetFirst(projs); 
               eqs = CreateEqsBelongingToProjection
                    (eqs, proj, constructor, i, sort);
               }
          }
     return eqs;
     } 
                                            
static ATerm GenerateEqs(ATerm adt, ATermList sorts)
     {
     ATermList eqs = ATreverse((ATermList) ATgetArgument(adt, 1));
     for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts))
          {ATerm sort = ATgetFirst(sorts);
          int nDets;
          eqs = GenerateDetEqs(eqs, sort, &nDets);
          // ATfprintf(stderr,"DetEqs: %t %d", eqs, nDets);
          eqs = GenerateProjEqs(eqs, sort, nDets);
          }
     return ATmake("d(<term>,<term>)",sig, ATreverse(eqs));     
     }

static Symbol CaseSymbolWhichBelongToSortOfVal(ATerm val, int nargs) {
     ATbool new = ATfalse;
     /* ATwarning("CaseSymbolWhichBelongToSortOfVal val %t sort %a nargs=%d", 
               val, MCRLgetSort(val), nargs); */
     return MCRLputCaseFunction(nargs-1, 
         (ATerm) ATmakeAppl0(MCRLgetSort(val)), &new);
     }          
/* ----------------------------- CONSTRAINT PART --------------------------- */

static ATerm  MakeEq(ATerm sortterm, ATerm nameterm)
     {
     ATerm result = NULL;
     char *eq = "eq", *sort = ATgetName(ATgetSymbol(sortterm));
     char *buffer = (char*) malloc((strlen(eq)+2*strlen(sort)+3)
          *sizeof(char));
     ATerm d = MCRLdummyVal(ATgetAFun(sortterm));
     sprintf(buffer,"%s#%s#%s",eq,sort,sort);
     result =
          (ATerm) ATmakeAppl2(ATmakeSymbol(buffer, 2, ATtrue), nameterm, d);     
     free(buffer);
     return result;
     }
     
static ATerm *Unfold(int n, ATerm t);
static void Fold(int n, ATerm *aux, Symbol sym);
     
static ATerm ConstraintCondition(ATerm var)
/* C(e,eq(v00,d00) and eq(v01,d01) and ...MINUS (eq(vi1,di1)...eq(vim,dim))
      and ,..., eq(vn0, dn0),.....) */
     {
     ATerm varname = ATgetArgument((ATermAppl) var, 0),
     sort = ATgetArgument((ATermAppl) var, 1), r = NULL;
     ATermList constructors = MCRLgetConstructors(ATgetAFun(sort));
     ATerm caseFunction = RWgetAssignedVariable(ATgetSymbol(varname));
     ATermList nameargs = ATgetNext(ATgetArguments((ATermAppl) caseFunction));
     int m = ATgetLength(constructors),i = 0;
     ATermList results = ATmakeList0();
     ATerm *aux = NULL;
     Symbol sym = binary?
     CaseSymbolWhichBelongToSortOfVal(MCRLterm_true, 3):
     CaseSymbolWhichBelongToSortOfVal(MCRLterm_true, m+1);
     if (binary) {
            aux = Unfold(m, caseFunction);
            nameargs = ATempty;
            for (i=2*m-1;i>=m;i--) nameargs = ATinsert(nameargs, aux[i]);
            }
     for (i=0;i<m;i++) results = ATinsert(results, MCRLterm_true); 
     for (i=0;!ATisEmpty(nameargs) && !ATisEmpty(constructors);
          nameargs=ATgetNext(nameargs), constructors=ATgetNext(constructors),i++)
          {ATermList namecargs = ATgetArguments((ATermAppl)
               ATgetFirst(nameargs)), 
           sortcargs = ATgetArguments((ATermAppl) ATgetFirst(constructors));
           for (;!ATisEmpty(namecargs) && !ATisEmpty(sortcargs);
               namecargs=ATgetNext(namecargs), sortcargs=ATgetNext(sortcargs))
               {ATerm namecarg = ATgetFirst(namecargs), 
                sortcarg = ATgetFirst(sortcargs);
                int j=0;
                for (;j<m;j++) 
                if (j!=i) 
                     {
                     ATerm result = ATelementAt(results, j),
                     t = MakeEq(sortcarg, namecarg);
                     if (ATisEqual(result, MCRLterm_true)) result = t;
                     else
                     result = (ATerm) ATmakeAppl2(MCRLsym_and, result, t);
                     results = ATreplace(results, result, j);
                     }
                }
           }
      /* ATwarning("QQQ results = %t",results); */
     if (!binary) {
           results = ATinsert(results, 
                ATgetArgument((ATermAppl) caseFunction ,0));
           r = (ATerm) ATmakeApplList(sym, results);
           }
     else  {
            int i, m2 = 2*m;
            for (i=m;i<m2;i++,results = ATgetNext(results)) 
               aux[i] = ATgetFirst(results);
            Fold(m, aux, sym);
            r = aux[1];
            ATunprotect(aux); free(aux);
           }
     /* ATwarning("QQ: r = %t\n",r); */           
     return r;
     }
     
/* ----------------------------- EXPANSION PART of PARAMETERS ------------ */

ATermList NewConstructorInstance(char *totalname,
       ATerm *constructor, ATermList result, int *k) { 
       Symbol constructorSymbol = ATgetSymbol(*constructor);
       char *name = totalname + strlen(totalname);
       ATermList cargs = ATgetArguments((ATermAppl) *constructor),
       newcargs = ATmakeList0();
          for (;!ATisEmpty(cargs);cargs=ATgetNext(cargs),(*k)++)
               {ATerm carg = ATgetFirst(cargs), f = NULL;
               /* sprintf(name,"%s_%d", vname, k); */
               sprintf(name,"_%d",  *k);
               f = MCRLuniqueTerm(totalname, ATempty);
               newcargs = ATinsert(newcargs, ATmake("<term>",f));
               result = ATinsert(result, ATmake("v(<term>,<str>)",
                    f, ATgetName(ATgetAFun(carg))));
               }
          *constructor = (ATerm) ATmakeApplList(constructorSymbol, 
          ATreverse(newcargs));
          return result;
          } 
   
static ATermList CreateBinaryCaseInstantiations(ATerm parname, ATerm parsort, 
    int level) {
    char totalname[256], *name = NULL;
    ATermList constructors = MCRLgetConstructors(ATgetAFun(parsort)),
    result = ATmakeList0();
    int n = ATgetLength(constructors), 
        i, d = ATgetLength(constructors), k = 0, l = 0;
    ATerm *aux = (ATerm*) calloc(2*n, sizeof(ATerm));
    ATerm caseFunction = NULL; 
    Symbol caseSymbol = 0;
    ATermList cs = MCRLgetCaseFunctions(ATgetAFun(parsort));
    /* ATwarning("QQQ Constructors %t",constructors); */
    for(;!ATisEmpty(cs)&&ATgetArity(ATgetAFun(ATgetFirst(cs)))!=3;
        cs=ATgetNext(cs));
    caseFunction = ATgetFirst(cs);
    caseSymbol = ATgetAFun(caseFunction);
    ATprotectArray(aux, 2*n);
    sprintf(totalname,"%s",ATgetName(ATgetSymbol(parname)));
    name = totalname + strlen(totalname)-(MCRLoldTbf?0:1);
    for (k=0, i=n;!ATisEmpty(constructors);
         constructors=ATgetNext(constructors), i++)
           {ATerm constructor = ATgetFirst(constructors);
           *name = '\0';
           result = NewConstructorInstance(totalname, &constructor, 
           result,  &k);
           aux[i] = constructor;
           /* ATfprintf(stderr, "aux[%d]=%t\n",i,aux[i]); */
           }
    result = ATreverse(result);
    *name = '\0';
    sprintf(name,"%s", ename);
    name = totalname + strlen(totalname);
    for (i=n-1;i>=1;i--) {
          ATerm f = NULL;
          if (2*i < d) {d = i+1; l++;};
           /* fprintf(stderr, "i= %d (%d, %d)  level = %d (d= %d)\n",
             i, 2*i, 2*i+1,l, d); */
           sprintf(name,"_%d",  l);
           f = MCRLuniqueTerm(totalname, ATempty);
           {
           ATerm t = ATmake("v(<term>,<term>)",f,
                   ATgetArgument((ATermAppl) caseFunction,0));
           if (ATindexOf(result, t,0)<0) 
                 result = ATinsert(result, t);   
	   aux[i]=(ATerm) 
             ATmakeAppl3(caseSymbol, f, aux[i+i], aux[i+i+1]);
           }    
	}
    RWassignVariable(ATgetSymbol(parname),  aux[1], NULL, level);
    ATunprotect(aux);
    free(aux);
    /* ATfprintf(stderr, "QQQ vars = %t\n",result); */ 
    return result;
    }

static ATermList CreateNormalCaseInstantiations(ATerm parname, ATerm parsort, int
level)
     {
     char totalname[256], *name = NULL;
     ATerm caseFunction = ATgetFirst(MCRLgetCaseFunctions(
          ATgetAFun(parsort))), 
          subs = NULL;
     ATermList newargs = ATmakeList0(), result = NULL,     
     constructors = MCRLgetConstructors(ATgetAFun(parsort));
     int k = 0;
     Symbol caseSymbol = ATgetSymbol(caseFunction);
     ATerm f = NULL;
     /* ATwarning("QQQ: caseFunction %t parsort = %t",caseFunction, parsort); */
     sprintf(totalname,"%s",ATgetName(ATgetSymbol(parname)));
     name = totalname + strlen(totalname)-(MCRLoldTbf?0:1);
     /* sprintf(name,"%s_%d", ename, ATgetLength(args)); */
     sprintf(name,"%s", ename);
     f = MCRLuniqueTerm(totalname, ATempty);
     result = ATmakeList1(ATmake("v(<term>,<term>)", f,
                   ATgetArgument((ATermAppl) caseFunction,0)));    
     newargs = ATinsert(newargs, ATmake("<term>",f));    
     for (k=0;!ATisEmpty(constructors);constructors=ATgetNext(constructors))
          {ATerm constructor = ATgetFirst(constructors);
          *name ='\0';
          result =  NewConstructorInstance(totalname,
          &constructor, result, &k); 
          newargs = ATinsert(newargs, constructor);
          }
     subs = (ATerm) ATmakeApplList(caseSymbol, ATreverse(newargs)); 
     /*ATfprintf(stderr,"Assign: %t = %t\n", parname, RWrewrite(subs)); */
     RWassignVariable(ATgetSymbol(parname),  RWrewrite(subs), NULL, level); 
     return ATreverse(result);
     }
     
static ATermList  CreateCaseInstantiations(ATerm parname, ATerm parsort, 
      int level) {
      if (binary) 
        return CreateBinaryCaseInstantiations(parname, parsort, level);
      return CreateNormalCaseInstantiations(parname, parsort, level);
      }
             
static ATermList InitExpansions(ATermList pars,  ATerm *cond)
     {
     ATermList result = ATmakeList0();
     static int cnt  = 0; 
     int npars = 0;
     if (!cond) cnt = 0;
     for (;!ATisEmpty(pars);pars=ATgetNext(pars))
          {ATerm par = ATgetFirst(pars),
          parsort = ATgetArgument((ATermAppl) par, 1);
          if (ATindexOf(expandtypelist, parsort,0)>=0)
               {
               ATerm parname = ATgetArgument((ATermAppl) par, 0);
               ATermList newvars = CreateCaseInstantiations(parname,
                    parsort, cond?1:0),
               declareVariables =  ATmakeList0(), declareSorts = ATmakeList0();
               RWdeclareVariables(newvars);
               if (!cond) { 
                    if (verbose) ATwarning("Parameter %s: %t is expanded to %d parameters",
                    MCRLgetName(parname), parsort, ATgetLength(newvars));
                    choiceVariables = ATinsert(choiceVariables,
                    ATgetFirst(newvars));
                    }
               for (;!ATisEmpty(newvars);newvars=ATgetNext(newvars))
                    {ATerm newvar = ATgetFirst(newvars);
                    ATerm varname = ATgetArgument((ATermAppl) newvar,0),
                    varsort = ATgetArgument((ATermAppl) newvar,1);
                    result = ATinsert(result, newvar);
                    declareVariables = ATinsert(declareVariables, varname);
                    declareSorts = ATinsert(declareSorts, varsort);
                    }   
               if (cond)
                    *cond = (ATerm) ATmakeAppl2(MCRLsym_and, 
                            *cond, ConstraintCondition(par));
               npars++;
               }
          else
               result = ATinsert(result, par);
          }
     if (cond) 
          {
          if (npars>0 && verbose) ATwarning("In summand %d: %d variable(s) is (are) expanded",
          cnt, npars);
          cnt++;
          } 
     return ATreverse(result);    
     }
     
static ATerm *Unfold(int n, ATerm t) {
     ATerm *aux = calloc(2*n, sizeof(ATerm));
     int i=0;
     aux[1] = t;
     ATprotectArray(aux, 2*n);
     for(i=1;i<n;i++){
	aux[i+i]=ATgetArgument(aux[i],1);
	aux[i+i+1]=ATgetArgument(aux[i],2);
     }
     return aux;
}

static void Fold(int n, ATerm *aux, Symbol sym) {
    int i = 0;
    for (i=n-1;i>=1;i--) { 
	   aux[i]=(ATerm) 
             ATmakeAppl3(sym,  
                 ATgetArgument((ATermAppl) aux[i],0), aux[i+i], aux[i+i+1]);
           } 
    }

static ATerm CasePosBinary(ATerm t, int n, int pos, ATerm val, ATerm dummy) {
     ATerm *aux = Unfold(n, t), *aux0 = aux + n, result = NULL;
     int i = 0;
     Symbol sym = n>1?CaseSymbolWhichBelongToSortOfVal(val,
                  ATgetLength(ATgetArguments((ATermAppl) t))):0;
     for (;i<n;i++) 
        if (i != pos) aux0[i] = dummy;
        else
           aux0[i] = val;
     Fold(n, aux, sym);
     result = aux[1];
     ATunprotect(aux);
     free(aux);
     return result;
     }
                 
static ATerm CasePosNormal(ATerm casef, int pos, ATerm val, ATerm dummy)
     {
     Symbol sym = CaseSymbolWhichBelongToSortOfVal(val,
                  ATgetLength(ATgetArguments((ATermAppl) casef)));
     ATermList args = ATmakeList1(ATgetArgument((ATermAppl) casef, 0));
     int i = 0, n = ATgetArity(sym)-1;
     for (;i<pos && i < n;i++) args = ATinsert(args, dummy);
     if (i == pos) {args = ATinsert(args, val);i++;}
     for (;i < n;i++) 
          args = ATinsert(args, dummy);
     /* ATwarning("QQQ: %a %t", sym, ATreverse(args)); */
     return (ATerm) ATmakeApplList(sym, ATreverse(args));
     }

         
static ATerm CasePos(ATerm casef, int n, int pos, ATerm val, ATerm dummy) {
     if (binary) 
         return CasePosBinary(casef,  n, pos, val, dummy);
     return CasePosNormal(casef, pos, val, dummy);
} 
   

static ATermList UnfoldE(ATerm *aux, int n) {
    ATermList result = ATmakeList0(); 
    int i=n-1;
    /* ATwarning("UnfoldE %d", n); */
     for (;i>=1;i--) { 
         ATerm t = ATgetArgument(aux[i],0);
	 /* ATwarning("t = %t",t); */
         if (ATindexOf(result,t,0)<0) result = ATinsert(result,  t);
         }
     return result; 
     }
     
static ATermList UnfoldT(ATerm *aux, int n) {
     ATermList result = ATmakeList0();
     int i=n;
     for (i=2*n-1;i>=n;i--) result = ATinsert(result, aux[i]);
     return result;    
     }

static ATermList KernelGetExpansion(ATerm t, ATermList sel, ATermList  args) {     
    int pos = 0, n = ATgetLength(args);
    ATermList result = ATmakeList0();
    for (;!ATisEmpty(args);args=ATgetNext(args), pos++)
         {ATerm arg = ATgetFirst(args);
         ATermList  cargs = ATgetArguments((ATermAppl) arg);
         for (;!ATisEmpty(cargs);cargs=ATgetNext(cargs))
              {ATerm carg = ATgetFirst(cargs);
              result = ATinsert(result, CasePos(t, n, pos, carg,
                   MCRLdummyVal(MCRLgetSort(carg))));
              /* ATfprintf(stderr,"HELP %t\n", result); */
              }
         }
         return ATconcat(sel, ATreverse(result));
    }
         
static ATermList GetExpansionBinary(int n, ATerm term) {
      if (ATgetArity(ATgetSymbol(term)) !=0) return NULL;
      {
      ATerm t =  RWgetAssignedVariable(ATgetSymbol(term));
      if (!t || ATisEmpty(ATgetArguments((ATermAppl) t))) return NULL;
      /* ATfprintf(stderr,"t = %t\n",t); */
      {
      ATerm *aux = Unfold(n, t);
      ATermList result = KernelGetExpansion(t, UnfoldE(aux, n), 
                UnfoldT(aux, n));
     /* ATfprintf(stderr, "result expand = %t %t\n",UnfoldE(aux, n),
      UnfoldT(aux,n)); */ 
      ATunprotect(aux);
      free(aux); 
      return result;
      }
      }
      }
          
static ATermList GetExpansionNormal(ATerm term)
     {
     if (ATgetArity(ATgetSymbol(term)) !=0) return NULL;
          {
          ATerm t =  RWgetAssignedVariable(ATgetSymbol(term));
/* ATfprintf(stderr, "HELP %t = %t\n", term, t); */
          if (!t || MCRLgetType(ATgetAFun(t))!=MCRLvariable) return NULL;
               {
               return KernelGetExpansion(t, 
                    ATmakeList1(ATgetArgument((ATermAppl) t, 0)),
                    ATgetNext(ATgetArguments((ATermAppl) t))
                    );
               }    
          }
     }
     
static ATermList GetExpansion(ATerm sortname, ATerm term) {
     if (binary) {
         return GetExpansionBinary(
               MCRLgetNumberOfConstructors(ATgetAFun(sortname)), term);
         }
     return GetExpansionNormal(term);
}

static ATermList searchAnnotation(ATerm term) {
   // ATfprintf(stderr,"searchAnno %t\n", term);
   AFun srt = MCRLgetSort(term), afun = ATgetAFun(term);
   ATermList constructors =MCRLgetConstructors(srt);
   // ATfprintf(stderr,"searchAnno1 %t\n", constructors);
   for (;!ATisEmpty(constructors);constructors = ATgetNext(constructors))
   if (ATgetAFun(ATgetFirst(constructors))== afun) break;
   if (ATisEmpty(constructors)) return NULL;
   return (ATermList) ATgetAnnotation(ATgetFirst(constructors), detTag);
   }

static int isDetFunction(ATerm proj) {
    // ATfprintf(stderr,"Entree %t\n", proj);
    if (ATgetArity(ATgetAFun(proj))!=1) return -1;
    {
    ATerm t = ATgetArgument(proj, 0);
    ATermList dets = MCRLgetDetFunctions(ATgetAFun(t));
    if (!dets) return -1;
    ATerm sig = MCRLgetFunction(ATgetAFun(proj));
    // ATfprintf(stderr,"HALLO1  %t\n", sig);
    // ATfprintf(stderr,"HALLO2  %t\n", dets);
    return ATindexOf(dets, sig, 0);
    }
   }

static ATermList Replace(ATermList projs, ATerm term) {
     ATermList result = ATmakeList0();
     ATermList anno = (ATermList) searchAnnotation(term);
     for (;!ATisEmpty(projs);projs=ATgetNext(projs)) {
           ATerm proj = ATgetFirst(projs);
           if (isDetFunction(proj)>=0) {
             /* if (anno) ATfprintf(stderr,"Annotation %t\n", anno); */
             if (anno && !ATisEmpty(anno)) { 
                  result = ATinsert(result, ATgetFirst(anno));  
                  anno = ATgetNext(anno);
                  }
             else {
              result = ATinsert(result, 
               (ATerm) ATmakeAppl1(ATgetSymbol(proj), term));
               }
           }
           else {
          result = ATinsert(result, 
          (ATerm) ATmakeAppl1(ATgetSymbol(proj), term));
          }
         }
     return ATreverse(result);
     }
        
static ATermList ExpandTerms(ATermList terms, ATermList pars) {
     ATermList result = ATmakeList0();
     for (;!ATisEmpty(pars) && !ATisEmpty(terms);
          pars=ATgetNext(pars), terms = ATgetNext(terms))
          {ATerm par = ATgetFirst(pars),
         /*  parname = (ATerm) ATgetArgument((ATermAppl) par, 0), */
          sortname = (ATerm) ATgetArgument((ATermAppl) par, 1),
          term = ATgetFirst(terms);
          if (ATindexOf(expandtypelist,sortname,0)>=0)
               {
               ATermList expandpars  =  GetExpansion(sortname, term); 
               if (!expandpars) expandpars = 
                    Replace(MCRLgetProjections(ATgetAFun(sortname)), term);
               for (;!ATisEmpty(expandpars);expandpars=ATgetNext(expandpars))
                    {ATerm expandpar = ATgetFirst(expandpars);
                    result = ATinsert(result, expandpar);
                    }
               }
          else result = ATinsert(result, term);
          }
     result = ATreverse(result);
/* ATfprintf(stderr,"HELP return expandTerms = %t\n", result); */
     return result;
     } 
     
              
static ATermList SubstituteCasesInParameters(ATermList sums, ATermList pars)
     {
     ATermList result = ATmakeList0();
     for (;!ATisEmpty(sums);sums=ATgetNext(sums))
          {ATerm sum = ATgetFirst(sums);
          ATermList vars = (ATermList) ATgetArgument((ATermAppl) sum, 0),
          acts = (ATermList) ATgetArgument((ATermAppl) sum, 2);
          ATerm procarg = (ATerm) ATgetArgument((ATermAppl) sum, 3),
          cond = (ATerm) ATgetArgument((ATermAppl) sum, 4);
          ATermList newvars = NULL;
          newvars = InitExpansions(vars, &cond);
          cond = RWrewrite(cond);
          acts = RWrewriteList(acts);
          if (!ATisEqual(procarg, MCRLterm_terminated))
	     {
             ATermList terms = 
                 (ATermList) ATgetArgument((ATermAppl) procarg,0);
             terms = ExpandTerms(terms, pars); 
             terms = RWrewriteList(terms);
/* ATfprintf(stderr, "Expand QQQ before %t\n", terms);  */
             procarg = (ATerm) ATmakeAppl1(ATgetSymbol(procarg), (ATerm) terms);
             }
          sum = (ATerm) ATmakeAppl5(ATgetSymbol(sum), 
             (ATerm) newvars,
             (ATerm) ATgetArgument((ATermAppl) sum, 1), 
             (ATerm) acts, procarg, cond);
        result = ATinsert(result, sum);
        RWflush();
        RWresetVariables(1);
        }
     return ATreverse(result); 
     }
     
/* ----------------------------- MAIN PART ------------------------------- */

static ATermList  GetParNames(ATermList pars)
     {
     ATermList result = ATmakeList0();
     for (;!ATisEmpty(pars);pars=ATgetNext(pars))
          {ATerm par = ATgetFirst(pars);
          result = ATinsert(result, ATgetArgument((ATermAppl) par,0));
          }
     return ATreverse(result);
     }


static void TestSorts(ATermList inits, ATermList newpars) {
     for (;!ATisEmpty(inits)&&!ATisEmpty(newpars);inits=ATgetNext(inits),
          newpars=ATgetNext(newpars)) {
          ATerm init = ATgetFirst(inits), newpar =  ATgetFirst(newpars);
          if (MCRLgetSort(init)!= 
              ATgetAFun(ATgetArgument((ATermAppl) newpar, 1)))
          ATwarning("Sort init %t (%s) != sort v %t",
          init, ATgetName(MCRLgetSort(init)),newpar); 
          }   
     }
     
static ATerm Expand(ATerm proc)
    {
    ATermList pars = (ATermList) ATgetArgument((ATermAppl) proc,1);
    ATermList newpars = InitExpansions(pars,NULL),
    inits = (ATermList) ATgetArgument((ATermAppl) proc,0),
    sums = (ATermList) ATgetArgument((ATermAppl) proc,2),
    parnames = GetParNames(pars);
    int n = ATgetLength(parnames);
    ATwarning( "Number of parameters of input LPO: %d",n);
    sums = SubstituteCasesInParameters(sums, pars);
    inits = ExpandTerms(RWrewriteList(inits), pars);
// ATfprintf(stderr,"aap: %t\n", inits);
    TestSorts(inits, newpars); 
    RWflush();
    proc = (ATerm) ATmakeAppl3(ATgetSymbol(proc), 
         (ATerm) inits, (ATerm) newpars, (ATerm) sums);
    ATwarning("Number of parameter(s) of output LPO:%d", 
         ATgetLength(newpars));
    /* ATwarning("Choice variables are  %t", choiceVariables); */
    return proc;
    }

static void Assign(ATerm proc) {
    ATermList inits;
    ATermList pars = (ATermList) ATgetArgument((ATermAppl) proc, 1);
    RWdeclareVariables(pars);
    for (inits = (ATermList) ATgetArgument((ATermAppl) proc, 0);
          !ATisEmpty(inits)&&!ATisEmpty(pars);
          inits=ATgetNext(inits),pars=ATgetNext(pars))
          {
          ATerm init = ATgetFirst(inits), par =
          ATgetArgument((ATermAppl) ATgetFirst(pars), 0);
          /* ATfprintf(stderr,"Assign %t= %t\n", par, init); */
          RWassignVariable(ATgetAFun(par), init, NULL, 0);
          }
    }

static int CountConstantArguments() {
    int i, cnt = 0;
    ATermList inits = (ATermList) ATgetArgument((ATermAppl) proc, 0);
    ATermList sums = (ATermList) ATgetArgument((ATermAppl) proc,2);
    Assign(proc0);
    Assign(proc);
    for (i=0;!ATisEmpty(inits);i++, inits = ATgetNext(inits)) { 
       ATermList sums = (ATermList) ATgetArgument((ATermAppl) proc,2);
       for (;!ATisEmpty(sums);sums=ATgetNext(sums)) { 
          ATermAppl sum = (ATermAppl) ATgetFirst(sums);
          ATermAppl procarg = (ATermAppl) ATgetArgument((ATermAppl) sum, 3);
          ATermList w = (ATermList) ATgetArgument(procarg, 0);
          ATerm d = RWrewrite(ATelementAt(w, i));
          if (!ATisEqual(d, ATgetFirst(inits))) { 
              ATerm q = MCRLgetFunction(ATgetAFun(d));
              int k = isDetFunction(q); 
              if (k>=0) {
                ATermList z = searchAnnotation(ATgetArgument(d,0)); 
                if (!z || !ATisEqual(ATgetFirst(inits), ATelementAt(z, k)))  {
                     /* if (z) {ATfprintf(stderr, "z= %d\n", z);
                     ATfprintf(stderr, "%d:%t != %t\n", i, ATgetFirst(inits), 
                           ATelementAt(z,k));
                     }
                     */
                     break;
                     }
                    // ATfprintf(stderr,"d = %t %d\n", d , isDetFunction(q)); 
              } else break;
       }
     }
     if (ATisEmpty(sums)) cnt++;
     }
    return cnt;
    }
    

                 
int main(int argc, char *argv[]) {
    int i, j = 0, number_of_new_equations, cnt = 0;
    char **newargv = (char**) calloc(argc + 2, sizeof(char*));
    ATbool new = ATfalse;
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0];
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    ATinit(argc, argv,(ATerm*) &argc);
    ATprotect((ATerm*) &expandnamelist);
    ATprotect(&detTag);
    detTag = ATmake("<appl>","det");
    ATprotect(&projTag);
    projTag = ATmake("<appl>","projection");
    expandnamelist = ATmakeList0();
    for (i=1;i<argc&&j<argc+1;i++) {
	if (!strcmp(argv[i],"-help")) {
	    help(); exit(0);
	    }
	if (!strcmp(argv[i],"-version")) {
	    version(); exit(0);
	    }
        if (!strcmp(argv[i],"-binary")) {
            binary = ATtrue; continue;
            }
        if (!strcmp(argv[i],"-verbose")) {
            verbose = ATtrue; /* continue; */
            }
       if (!strcmp(argv[i],"-report")) {
            report = ATtrue; continue;
            }
       if (!strcmp(argv[i],"-candidates_for_expansion")) {
            candidates = ATtrue; continue;
            }
       if (!strcmp(argv[i],"-depth")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *endptr = NULL;
                depth = strtol(argv[i],&endptr,10);
                if (*endptr != '\0') ATerror("Number expected after \"-depth\"");
                }
            else
                ATerror("Integer (depth) expected after %s\n",argv[i-1]);
            continue;
            }        
	if (!strcmp(argv[i],"-expand")) {
	    expand = ATtrue;
	    if ((++i)<argc && strncmp(argv[i],"-",1))
            expandnamelist = 
                ATinsert(expandnamelist,ATmake("<str>",argv[i]));
	    else
		ATerror("Name of sort expected after %s\n",argv[i-1]);
	    continue;
	    }    
	newargv[j++] = argv[i];
	}
    if (!MCRLinitRW(j, newargv)) exit(EXIT_FAILURE);
    ATwarning("Number of existing projections: %d",
      MCRLregistrateExistingProjections(&number_of_new_equations));
  if (number_of_new_equations>0)  
  ATwarning("Number of added equations: %d", number_of_new_equations);
    {AFun s = MCRLputAndFunction(&new); new = ATfalse;
    if (s) {
       if (verbose) {
        if (new) ATwarning("Map %a: added", s);
         else ATwarning("Map %a: already present", s);
         }
       }
   else ATerror("No \"and\" is present");
   }
   Initialize(); 
   expandtypelist = GenerateAllConstructorSorts();
   if (report || candidates) exit(0);
   if (!ATisEmpty(expandnamelist)) expandtypelist = 
        SelectSorts(expandtypelist, expandnamelist);
   {ATermList sorts = expandtypelist; 
   for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts)) {
      ATerm sort = ATgetFirst(sorts);
      ATermList cons = MCRLgetConstructors(ATgetAFun(sort));
      for (;!ATisEmpty(cons);cons=ATgetNext(cons)) {
          ATerm con = ATgetFirst(cons);
          ATermList args = ATgetArguments((ATermAppl) con);
          for (;!ATisEmpty(args);args=ATgetNext(args), new = ATfalse) {
           ATerm arg = ATgetFirst(args);
           AFun s = MCRLputEqFunction(arg, &new);
           if (s) {
               if (verbose) { 
                 if (new) ATwarning("Map %a: added", s);
                 else ATwarning("Map %a: already present", s);
                 }
               }
           else ATerror("No eq function belonging to sort %t present",
                    arg); 
           }
       }
    }
    } 
   GenerateNewCaseFunctions(sig, expandtypelist);
   adt = MCRLgetAdt(); 
   sig = ATgetArgument((ATermAppl) adt, 0);
   sig =  GenerateNewMaps(sig, expandtypelist);
   adt = ATmake("d(<term>,<term>)",sig, ATgetArgument(adt, 1));
   adt = GenerateEqs(adt, newDetSorts);
   MCRLsetAdt(adt);
   for (i=0;i<depth;i++) proc = Expand(proc);
   MCRLsetProc(proc);
   cnt = CountConstantArguments();
   if (cnt>0) fprintf(stderr,
   "At least %d constant process parameter%s can be eliminated by constelm\n", 
    cnt, cnt>1?"s":"");
   MCRLsetAdt(ATremoveAllAnnotations(MCRLgetAdt()));
   MCRLoutput();
   exit(EXIT_SUCCESS);     
   }
    
