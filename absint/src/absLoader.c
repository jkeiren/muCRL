/* $Id: absLoader.c,v 1.1.1.1 2004/09/07 15:06:34 uid523 Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "rw.h"
#include "libAbsint.h"
/*
#include "libmcrl.c"
*/
#define TABLESIZE 500

static char *who="AbsInt"; /* Name of the tool */
static FILE *f;

static ATbool EXPORT = ATfalse;
static ATbool EXPORT_OLD = ATfalse;
static ATbool LOAD = ATfalse;
static ATbool IMPORT = ATfalse;
static ATbool AUTO = ATfalse;
static ATbool AUTO_ALL = ATfalse;
static ATbool SC = ATfalse;
static ATbool LIFT = ATfalse;
static ATbool HOMOMORPHISM = ATtrue;

static void WarningHandler(const char *format, va_list args) {
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
	  
static char loadFile[100] = "";
ATerm sortToAbstract;
char sortToAbstractName[NAME_LENGTH];


static ATerm absAdt;
static ATermList absFuncs, absEqs, absCons, absSorts;


ATermList conflictingSorts;

/*--------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------*/
static ATermTable absFunc_tab;
static ATermIndexedSet absSort_set;

static void initTables(void) {
	 absFunc_tab = ATtableCreate(TABLESIZE,75);
    if (!absFunc_tab) ATerror("Table is not allocated"); 
	 absSort_set = ATindexedSetCreate(TABLESIZE,75);
    if (!absSort_set) ATerror("Table is not allocated"); 
	 

}
/*--------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------*/
static int	numAbsSorts = 0;
static char absSortNames[MAX_NUM_PARS][NAME_LENGTH];

void tokSorts(char *sortList){
	char listAux[NAME_LENGTH];
	char *sortName;
	ATerm termSort;
	
	strcpy(listAux, sortList);
	sortName = (char *)strtok(listAux, "#"); 
	
	strcpy(absSortNames[numAbsSorts], sortName);
	while (sortName != NULL)
  	{
		numAbsSorts++;
    	sortName = (char *)strtok (NULL, "#");
		if(sortName != NULL){	
			strcpy(absSortNames[numAbsSorts], sortName);
		}
	}
}


ATbool toAutoAbstractSort(ATerm termSort){
	int i;
	char *sortName;
			
	if(AUTO_ALL)
		return ATtrue;
	
	if(!isAbstracted(termSort))
		return ATfalse;
	if(isLifted(termSort))
		termSort = getUnLifted(termSort);
	sortName = MCRLgetName(termSort);
	
	for(i =0; i<= numAbsSorts; i++){
		if(!strcmp(absSortNames[i], sortName))
			return ATtrue;
	}
	return ATfalse;
}

/*--------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------*/
#define TABLESIZE 500

static void helpmsg() 
{  
    P("Imports, exports and automatically generates abstract data specifications.");
	 P("Usage: absLoader [options]");
	 P("The following options can be used:");	
	 P("-E: \t\tExports abstract data signature");
    P("-L: \t\tfile.mcrl Loads the data specification");
	 P("-A list: \tGenerates a pointwise abstraction for the selected sorts");
	 P("-Aall: \t\tGenerates a pointwise abstraction for all abstract sorts");
    P("list:\t\tnames joint by '#'. Example: t#s#...#r");
	 P("-SC:\t\tGenerates the safety conditions");
	 P("-Lift sort: \tLift sort and related functions");
 	 P("-H:\tUses Homomorphic abstraction");
    P("-G:\tUses Galois Connection abstraction");
    P("-help:\tYields this message");
}

 

static void parseCommandLine(int argc, char *argv[]){
	int i = 0, j;
	char sortName[NAME_LENGTH];
	
	P("Abstraction Loader for mCRL Abstract Specifications"); 	
	for (i=1;i<argc;i++) {
	  if (!strcmp(argv[i],"-E")){	
	 		EXPORT = ATtrue;
	 		LOAD = ATfalse;
	 		IMPORT = ATfalse;
	  		AUTO = ATfalse;
	  		AUTO_ALL = ATfalse;
	  		SC = ATfalse;
	  		LIFT = ATfalse;
	  		continue;
	  }
	  if (!strcmp(argv[i - 1],"-A")){	
	 		EXPORT = ATfalse;
	 		LOAD = ATfalse;
	 		IMPORT = ATfalse;
	  		AUTO = ATtrue;		
	  		AUTO_ALL = ATfalse;	
	  		SC = ATfalse; 
	  		tokSorts(argv[i]);
	  		LIFT = ATfalse;
	  		continue;
	  }
	  if (!strcmp(argv[i],"-L")){	
	 		EXPORT = ATfalse;
	  		SC = ATfalse;
	 		LOAD = ATtrue;
	 		IMPORT = ATfalse;
	  		AUTO = ATfalse;
	  		AUTO_ALL = ATfalse;
	  		LIFT = ATfalse;
	  		continue;
	  }
	  if (!strcmp(argv[i],"-Aall")){	
	 		EXPORT = ATfalse;
	 		LOAD = ATfalse;
	 		IMPORT = ATfalse;
	  		AUTO_ALL = ATtrue;
			AUTO = ATfalse;
	  		SC = ATfalse;
	  		LIFT = ATfalse;
			continue;
	  }
	  if (!strcmp(argv[i],"-SC")){	
	 		EXPORT = ATfalse;
	 		LOAD = ATfalse;
	 		IMPORT = ATfalse;
	  		AUTO_ALL = ATfalse;
			AUTO = ATfalse;
	  		SC = ATtrue;
	  		LIFT = ATfalse;
			continue;
	  }
	  if (!strcmp(argv[i - 1],"-L")){
	 		EXPORT = ATfalse;
	 		LOAD = ATtrue;
	 		IMPORT = ATfalse;
	  		AUTO_ALL = ATfalse;
			AUTO = ATfalse;
	  		LIFT = ATfalse;
	  		SC = ATfalse;
			if(argv[i][0]!='-')
				strcpy(loadFile, argv[i]);
	  		continue;
	  }
	  if(!strcmp(argv[i],"-H")){
	  	HOMOMORPHISM = ATtrue;
	  }
	  if(!strcmp(argv[i],"-G")){
	  	HOMOMORPHISM = ATfalse;
		setGalois();
	  }
	  if (!strcmp(argv[i - 1],"-Lift")){
	 		EXPORT = ATfalse;
	 		LOAD = ATfalse;
	 		IMPORT = ATfalse;
	  		AUTO_ALL = ATfalse;
			AUTO = ATfalse;
	  		LIFT = ATtrue;
	  		SC = ATfalse;
			if(argv[i][0]!='-'){
				strcpy(sortToAbstractName, argv[i]);
			}
			continue;
	  }
	  if (!strcmp(argv[i],"-help")){
	  		helpmsg();
    		exit(0);
	  }
	} 
	if(EXPORT){
		P("Exporting Abstract Signature");
	}
	if(LOAD){
		fprintf(stderr,"Loading Abstract Data Specification from: %s\n",
			 loadFile);
	}
	if(AUTO || AUTO_ALL){
		P("Auto Generation of the Abstract Data Specification");
	}
}
/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

static void printFunc(AFun fun, ATermList argSorts, ATerm fSort){
	char fName[NAME_LENGTH];
	ATermList funcs;
	ATerm argSort;
	
	getFuncName(fun, fName);
 	fprintf(f,"   %s:", fName);
	
   for(;!ATisEmpty(argSorts); argSorts = ATgetNext(argSorts)){
		argSort = ATgetFirst(argSorts);
		fprintf(f,"%s", MCRLgetName(argSort));	
	   if(!ATisEmpty(ATgetNext(argSorts)))
			fprintf(f,"#");
	}
 	fprintf(f," -> %s\n", MCRLgetName(fSort));	
}

static void printSort(ATerm sortTerm){
	fprintf(f,"%s ", MCRLgetName(sortTerm));
}

/*--------------------------------------------------------------------------*/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/*--------------------------------------------------------------------------*/ 


void abstractAndLiftFunctions(ATerm adt){
	ATermList funcList = getFunctions(adt);
	ATermList consList = getConstructors(adt);
	ATerm funcTerm; 
	ATerm fTerm;
	ATerm sortTerm;
	char fName[NAME_LENGTH];
	int i;
	ATermList argSorts, newArgSorts;
	ATerm arg, argSort;
	ATbool toAbstract;
	AFun newFun;
	AFun fun;
	
	funcList = ATconcat(funcList, consList);
	for(;!ATisEmpty(funcList); funcList = ATgetNext(funcList)){
		fTerm = ATgetFirst(funcList);
		funcTerm = ATgetArgument(fTerm, 0);
		sortTerm = ATgetArgument(fTerm, 2);
		fun = ATgetAFun(funcTerm);
		argSorts = (ATermList) ATgetArgument(fTerm, 1);
		getFuncName(fun, fName);
		toAbstract = ATfalse;
	
		if(reservedFunc(fun))
			continue;
		
		newArgSorts = ATmakeList0();
		for(;!ATisEmpty(argSorts); argSorts = ATgetNext(argSorts)){
			argSort = ATgetFirst(argSorts);	
			if(argSort == sortToAbstract){
				argSort = liftSort(abstractSort(argSort));
				toAbstract = ATtrue;
			}
			newArgSorts = ATappend(newArgSorts, argSort);
		}
		
		if(toAbstract){
			if(sortTerm == sortToAbstract){
				sortTerm = abstractSort(sortTerm);
			}
			sortTerm = liftSort(sortTerm);
			fTerm = (ATerm)ATsetArgument((ATermAppl)fTerm, sortTerm, 2);
			fTerm = (ATerm)ATsetArgument((ATermAppl)fTerm,(ATerm)newArgSorts,1);
			newFun = createNewFunc(ATgetAFun(funcTerm), newArgSorts, sortTerm);
			fprintf(stderr,".");
			continue;
		}	
	}	
	fprintf(stderr,"\n");
}
/*--------------------------------------------------------------------------*/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/*--------------------------------------------------------------------------*/ 


void importConstructors(){
	ATerm cons;
	ATbool ok;
	ATerm newCons, targetSort;
	AFun newFun;
	
	for(;!ATisEmpty(absCons); absCons = ATgetNext(absCons)){
		cons = ATgetFirst(absCons);
		targetSort = ATgetArgument(cons, 2);
		newFun = ATmakeSymbol(ATgetName(ATgetAFun(ATgetArgument(cons, 0))),
					ATgetLength(ATgetArgument(cons, 1)), ATtrue);
		newCons = (ATerm) ATmakeApplList(newFun,
			 (ATermList) ATgetArgument(cons, 1));		
		MCRLputConstructor(newCons, targetSort, &ok);
	}		
}
void importMaps(){
	ATerm mapTerm;
	ATbool ok;
	ATerm newMap, targetSort;
	ATermList argSorts;
	AFun newFun;
	
	for(;!ATisEmpty(absFuncs); absFuncs = ATgetNext(absFuncs)){
		mapTerm = ATgetFirst(absFuncs);	
		targetSort = ATgetArgument(mapTerm, 2);
		argSorts = (ATermList) ATgetArgument(mapTerm, 1);
		newFun = ATmakeSymbol(ATgetName(ATgetAFun(ATgetArgument(mapTerm, 0))),
					ATgetLength(argSorts), ATtrue);
		newMap= (ATerm) ATmakeApplList(newFun,argSorts);	
		MCRLputMap(newMap, targetSort, &ok);
	}		
}
void importEqs(){
	ATerm eq;
	ATbool ok;
	for(;!ATisEmpty(absEqs); absEqs = ATgetNext(absEqs)){
		eq = ATgetFirst(absEqs);
		MCRLputEquation(eq, &ok);
		if(ok)
			fprintf(stderr, ".");
	}
	fprintf(stderr, "\n");
	
}

void importSorts(){
	ATermList sorts;
	ATerm sortTerm;
	ATbool ok;

	for(;!ATisEmpty(absSorts); absSorts = ATgetNext(absSorts)){
		sortTerm = ATgetFirst(absSorts);
		MCRLputSort(sortTerm, &ok);	
	}
}

void importFuncs(){
	ATermList funcList = getFunctions(MCRLgetAdt());
	ATerm funcTerm; 
	ATerm fTerm;
	ATerm sortTerm;
	char fName[NAME_LENGTH];
	int i;
	ATermList argSorts;
	ATerm arg, argSort;
	ATbool abstracted, lifted;
	absFuncs = getFunctions(absAdt);
	absEqs = getEquations(absAdt);
	absCons = getConstructors(absAdt);
	absSorts = getListOfSorts(absAdt);
	
	ATprotect((ATerm*) &absFuncs);
	ATprotect((ATerm*) &absCons);
	ATprotect((ATerm*) &absEqs);
	importSorts();
	importConstructors();
	importMaps();
	importEqs();
}

/*--------------------------------------------------------------------------*/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/*--------------------------------------------------------------------------*/ 
autoEquality(ATerm con, ATerm sortTerm){
	AFun tag;
	ATbool ok;
	ATerm left, right, newEq;
	ATermList argSorts;
			
	tag = createNewFuncSym(absEqSym, ATmakeList2(sortTerm, sortTerm));			
	MCRLputMap((ATerm)ATmakeAppl2(tag, sortTerm, sortTerm), 
		 MCRLterm_bool, &ok);	 
	left = (ATerm) ATmakeAppl2(tag, con, con);
	right = MCRLterm_true;	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", 
		ATmakeList0(), left, right);
	MCRLputEquation(newEq, &ok);
}

ATerm autoConstructor(ATerm absSort){
	char *sortName; 
	char newName[NAME_LENGTH];
	ATbool ok;
	AFun newTag;
	ATerm newCons;

	sortName = ATgetName(ATgetAFun(absSort));
	appendString(constructorPrefix, sortName, newName);
	strcat(newName, "#");
	sortName = newName;
	newTag = ATmakeSymbol(sortName, 0, ATtrue);
	newCons = (ATerm)ATmakeAppl0(newTag);
	MCRLputConstructor(newCons, absSort, &ok);
	if(ok) autoEquality(newCons, absSort);
	return newCons;
}

ATerm autoAbstractH(ATerm absSort){
	AFun tag;
	ATbool ok;
	ATerm crtSort;	
	ATerm absCons;
	ATerm left, right, newEq;
	ATermList vars;
	ATerm x;
	AFun funcH;
	
	funcH = createAbstractH(absSort);
	absCons = autoConstructor(absSort);
	crtSort = getConcrete(absSort);
	
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	vars = ATmakeList1(ATmake("v(<term>, <term>)", x, crtSort)); 		
	left = (ATerm) ATmakeAppl1(funcH, x);
	right = absCons;
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);	
	
	fprintf(stderr, "Auto Equations for: %s -> ", ATgetName(funcH));
	fprintf(stderr, "%s\n", ATgetName(ATgetAFun(absSort)));
}

ATerm autoAbstractAlpha(ATerm absSort){
	AFun tag;
	ATbool ok;
	ATerm crtSort;	
	ATerm absCons;
	ATerm left, right, newEq;
	ATermList vars;
	ATerm X;
	AFun funcH;
	
	funcH = createAbstractAlpha(absSort, NULL);
	absCons = autoConstructor(absSort);
	crtSort = getConcrete(absSort);
	
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	vars = ATmakeList1(ATmake("v(<term>, <term>)", X, liftSort(crtSort))); 	
	left = (ATerm) ATmakeAppl1(funcH, X);
	right = absCons;
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);	
	
	fprintf(stderr, "Auto Equations for: %s -> ", ATgetName(funcH));
	fprintf(stderr, "%s\n", ATgetName(ATgetAFun(absSort)));
}

ATerm autoInverseH(ATerm absSort){
	AFun tag;
	ATbool ok;
	ATerm crtSort;	
	ATerm absCons;
	ATerm left, right, newEq;
	ATermList vars;
	ATerm x;
	AFun invH;
	
	crtSort = getConcrete(absSort);
	invH = createAbstractHinv(absSort);
	
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	vars = ATmakeList1(ATmake("v(<term>, <term>)", x, absSort)); 		
	left = (ATerm) ATmakeAppl1(invH, x);
	right = createFullCons(liftSort(crtSort));
	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);	
	
	fprintf(stderr, "Auto Equations for: %s -> ", ATgetName(invH));
	fprintf(stderr, "%s\n", ATgetName(ATgetAFun(liftSort(crtSort))));
}

ATerm autoInverseGamma(ATerm absSort){
	AFun tag;
	ATbool ok;
	ATerm crtSort;	
	ATerm absCons;
	ATerm left, right, newEq;
	ATermList vars;
	ATerm x;
	AFun invH;
	
	crtSort = getConcrete(absSort);
	invH = createAbstractGamma(absSort);
	
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	vars = ATmakeList1(ATmake("v(<term>, <term>)", x, absSort)); 		
	left = (ATerm) ATmakeAppl1(invH, x);
	right = createFullCons(liftSort(crtSort));
	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);	
	fprintf(stderr, "Auto Equations for: %s -> ", ATgetName(invH));
	fprintf(stderr, "%s\n", ATgetName(ATgetAFun(liftSort(crtSort))));
}

/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

void autoEquations(AFun tag, ATermList sorts, int i, ATerm targetSort, 
			ATermList listLeft, ATermList vars);
			

void autoEquations(AFun tag, ATermList sorts, int i, ATerm targetSort, 
			ATermList listLeft, ATermList vars){		
	ATbool ok;
	ATerm x;
	ATerm newEq, sortTerm;
	ATerm leftTerm, rightTerm = NULL;	
	ATermList newVars = ATmakeList0();
	ATermList newlistLeft = ATmakeList0();
	char varName1[10];
	AFun inTag;
			
	if(i == ATgetLength(sorts)){
		if(isAbstracted(targetSort)){
			rightTerm = autoConstructor(getUnLifted(targetSort));
			rightTerm = createSingTerm(rightTerm, targetSort);
		}
		else{
			rightTerm = createFullCons(targetSort);
		}
		
		leftTerm = (ATerm) ATmakeApplList(tag, listLeft);
		newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", 
					vars, leftTerm, rightTerm);
		MCRLputEquation(newEq, &ok);		
	}
	else{
		sprintf(varName1, "%s_%d", "x", i);
		sortTerm = ATelementAt(sorts, i);
		
		x = (ATerm) ATmakeAppl0(ATmakeAFun(varName1, 0, ATtrue));
		newVars= ATappend(vars, ATmake("v(<term>, <term>)", x, sortTerm));
		newlistLeft = ATappend(listLeft, x);
		
		autoEquations(tag, sorts, i+1, targetSort, 
			newlistLeft, newVars);
			 
	}			
}


ATbool toAutoAbstractArgSorts(ATermList argSorts){
	ATerm argSort;
	ATbool toAbstract = ATfalse; 
	
	for(;!ATisEmpty(argSorts); argSorts = ATgetNext(argSorts)){
		argSort = ATgetFirst(argSorts);
		if(isAbstracted(argSort)){
			if(toAutoAbstractSort(argSort))
				toAbstract = ATtrue;
			else
				return ATfalse;
		}
	}
	return toAbstract; 	
}

void autoAdt(){
	ATermList sorts = getListOfSorts(MCRLgetAdt()), funcList;
	ATerm fSort, argSort;
	ATerm funcTerm; 
	char fName[NAME_LENGTH];
	int i;
	ATermList argSorts;
	AFun tag;
	
	for(;!ATisEmpty(sorts); sorts = ATgetNext(sorts)){
		fSort = ATgetFirst(sorts);
		if(!isAbstracted(fSort) || isLifted(fSort))
			continue;
			
		if(toAutoAbstractSort(fSort)){
			fprintf(stderr, "Auto Constructor for: %s\n", MCRLgetName(fSort));
			autoConstructor(fSort);
			if(HOMOMORPHISM)
				autoAbstractH(fSort);
			else
				autoAbstractAlpha(fSort);
			if(ATindexOf(conflictingSorts, fSort, 0) != -1){
				if(HOMOMORPHISM)
				 autoInverseH(fSort);
				else
				 autoInverseGamma(fSort);
			}
		}
	}	
	
	
	funcList = ATtableKeys(absFunc_tab);
	for(;!ATisEmpty(funcList); funcList = ATgetNext(funcList)){
		funcTerm = ATgetFirst(funcList);
		fSort = ATtableGet(absFunc_tab, funcTerm);
		argSorts = (ATermList) ATgetArgument(funcTerm, 0);
		
		tag = ATgetAFun(funcTerm);
		 
		if(isAbstracted(fSort)){
			if(!toAutoAbstractSort(fSort)) 
				continue;
		}
		else{
			if(!toAutoAbstractArgSorts(argSorts))
				continue;
		}		
		
		fprintf(stderr, "Auto Equations for: %s -> ", ATgetName(tag));
		fprintf(stderr, "%s\n", ATgetName(ATgetAFun(fSort)));
		argSorts = (ATermList) ATgetArgument(funcTerm, 0);
		
		autoEquations(tag,
			argSorts, 0, fSort, ATmakeList0(),
			ATmakeList0());
		
	}	  
	fprintf(stderr,"\n");
}


/*--------------------------------------------------------------------------*/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/*--------------------------------------------------------------------------*/ 

static int nSC = 0;

void genSC(AFun fun, ATermList argSorts, ATerm fSort){	
	char name[NAME_LENGTH];
	char varName[NAME_LENGTH]; 
	char absVar[NAME_LENGTH];
	char *sortName;
	char head[NAME_LENGTH + 1000];
	char headAux[NAME_LENGTH + 1000];
	char tail[NAME_LENGTH + 1000];
	char dec[NAME_LENGTH + 1000]; 
	char declarations[10000];
	ATerm argSort;
	int i =0;
	
	getFuncName(fun, name);
	
	strcpy(head, memberSym);

	if(HOMOMORPHISM){
		if(isAbstracted(fSort))		
			sprintf(headAux, "(%s(%s(", absH, name);
		else
			sprintf(headAux, "(%s(", name); 
	}
	else{
		sprintf(headAux, "(%s(", name);
	}
	
	strcat(head, headAux);
		
	sprintf(tail, "%s(", name);
	
	strcpy(declarations, "[");
	for(;!ATisEmpty(argSorts); argSorts = ATgetNext(argSorts)){
		argSort = ATgetFirst(argSorts);
				
		sprintf(varName, "%s_%d", "x", i);
		i++;				
		sortName = ATgetName(ATgetAFun(getConcrete(argSort)));
		
		sprintf(dec, "v(%s,%s)", varName, sortName);
		strcat(declarations, dec);
		
		strcat(head, varName);
		
		if(isAbstracted(argSort)){
			if(HOMOMORPHISM)
				sprintf(absVar, "%s(%s)", absH, varName);
			else
				sprintf(absVar, "%s(%s(%s))", absAlpha, singSym, varName);
				
			strcat(tail, absVar);
		}
		else{
			strcat(tail, varName);
		}
		
		if(!ATisEmpty(ATgetNext(argSorts))){
			strcat(declarations, ", ");
			strcat(head, ", ");
			strcat(tail, ", ");
		}
			
	}
	strcat(declarations, "], ");
	strcat(head, ")");
	if(isAbstracted(fSort)){
		if(HOMOMORPHISM){	
			strcat(head, ")");
			strcat(head, ", ");
		}
		else{
			strcat(head, ", ");
			strcat(head, absGamma);		
			strcat(head, "(");
		}
	}
	else	
		strcat(head, ", ");
	
	strcat(tail, "))");
	
	fprintf(f,"%s",declarations);
	fprintf(f,"%s",head);
	fprintf(f,"%s",tail);
	if(isAbstracted(fSort) && !HOMOMORPHISM)
		fprintf(f,")");	
}
void genSCs(){
	ATermList funcList, argSorts;
	ATerm fTerm, fSort;
	AFun fun;
	char *fName;
	
	funcList = ATtableKeys(absFunc_tab);
	for(;!ATisEmpty(funcList); funcList = ATgetNext(funcList)){
		fTerm = ATgetFirst(funcList);
		fun = ATgetAFun(fTerm);
		argSorts = (ATermList) ATgetArgument(fTerm, 0);
		fSort = ATtableGet(absFunc_tab, fTerm);
		if(nSC == 0)
			fprintf(f,"[");
		else
			fprintf(f,",\n");		
		genSC(fun, argSorts, fSort);
		nSC++;	
	}
	if(nSC > 0)
		fprintf(f,"]\n");
	fflush(f); 
	fprintf(stderr, "Generated %d Safety Conditions \n", nSC);
}
/*--------------------------------------------------------------------------*/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/*--------------------------------------------------------------------------*/ 

void exportFuncs(){
	ATermList funcList, argSorts;
	ATerm fTerm, fSort;
	AFun fun;
	char *fName;
	
	funcList = ATtableKeys(absFunc_tab);
	for(;!ATisEmpty(funcList); funcList = ATgetNext(funcList)){
		fTerm = ATgetFirst(funcList);
		fun = ATgetAFun(fTerm);
		argSorts = (ATermList) ATgetArgument(fTerm, 0);
		fSort = ATtableGet(absFunc_tab, fTerm);
		printFunc(fun, argSorts, fSort); 	
	}
		
}
void exportSorts(){
	ATermList sortList;
	ATerm tSort;
	AFun tagH, tagEq;
	ATerm fTerm;
	
	sortList = ATindexedSetElements(absSort_set);
	for(;!ATisEmpty(sortList); sortList = ATgetNext(sortList)){
		tSort = ATgetFirst(sortList);
		if(isAbstracted(tSort) && !isLifted(tSort)){
			printSort(tSort);
			if(HOMOMORPHISM){
				tagH = ATmakeSymbol(absH, 1, ATtrue);
				fTerm = (ATerm) 
					ATmakeAppl1(tagH, (ATerm) ATmakeList1(getConcrete(tSort)));
			}
			else{
				tagH = ATmakeSymbol(absAlpha, 1, ATtrue);
				fTerm = (ATerm) ATmakeAppl1(tagH, (ATerm)
						 ATmakeList1(liftSort(getConcrete(tSort))));	
			}
			ATtablePut(absFunc_tab, fTerm, tSort);	
			if(ATindexOf(conflictingSorts, tSort, 0) != -1){
				if(HOMOMORPHISM)
					tagH = ATmakeSymbol(absHinv, 1, ATtrue);
				else
					tagH = ATmakeSymbol(absGamma, 1, ATtrue);		
				fTerm = (ATerm) 
					ATmakeAppl1(tagH, (ATerm) ATmakeList1(tSort));
				ATtablePut(absFunc_tab, fTerm, liftSort(getConcrete(tSort)));			
			}
		}
		
		if(isLifted(tSort) && isAbstracted(tSort)){
			tSort = getUnLifted(tSort);
			tagEq = ATmakeSymbol(absEqSym, 1, ATtrue);
			fTerm = (ATerm) 
				ATmakeAppl1(tagEq, (ATerm) ATmakeList2(tSort, tSort));
			
			ATtablePut(absFunc_tab, fTerm, MCRLterm_bool);
		}		
	}
}

/*--------------------------------------------------------------------------*/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/*--------------------------------------------------------------------------*/ 

void genAbsTerm(ATerm fTerm);

void genAbsFunc(ATerm fTerm){
	ATermList argSorts, newArgSorts;
	ATerm arg, argSort, fSort = NULL, funcTerm, auxSort; 
	int i, j;
	char fName[NAME_LENGTH];
	char nameAux[NAME_LENGTH];
	AFun fun, newFun;
	ATbool abstracted, new;
	
	
	fun = ATgetAFun(fTerm); 
	
	getFuncName(fun, fName);
	
	fSort = ATmake("<str>",ATgetName(MCRLgetSort(fTerm)));
	
	argSorts = getFuncSortList(fTerm);
	newArgSorts = ATmakeList0();
	abstracted = ATfalse;
	
	if(fSort == NULL)
		return;
	
	if(!strcmp(fName, absGamma)){
		auxSort = abstractSort(getUnLifted(fSort));
		if(-1 == ATindexOf(conflictingSorts, auxSort , 0)){
			conflictingSorts = ATappend(conflictingSorts, auxSort);
		}
	}
	
	ATindexedSetPut(absSort_set, fSort, &new);	
	
	if(isAbstracted(fSort))
		abstracted = ATtrue;	
				
	for(i=0; i< ATgetArity(fun); i++){
		arg = ATgetArgument((ATermAppl) fTerm, i);
		argSort = ATelementAt(argSorts, i);
		
		genAbsTerm(arg);
		
		argSort = getUnLifted(argSort);
		newArgSorts = ATappend(newArgSorts, argSort);
		
		if(isAbstracted(argSort)){
			abstracted = ATtrue;	
			ATindexedSetPut(absSort_set, argSort, &new);
		}				
	}
	
	if(reservedFunc(fun)) return;
	
	if(abstracted){
		fun = createNewFuncSym(fName, newArgSorts);
		funcTerm = (ATerm) ATmakeAppl1(fun, (ATerm) newArgSorts);	
		ATtablePut(absFunc_tab, funcTerm, fSort);
		return;
	}
}


void genAbsTerm(ATerm fTerm){
	if(ATgetArity(ATgetAFun(fTerm)) > 0){
		genAbsFunc(fTerm);
	}
}


void genAbsProcs(ATermList procArgs){
	ATerm procArg;	
		
	for (;!ATisEmpty(procArgs); 
			procArgs = ATgetNext(procArgs)) { 
		procArg = ATgetFirst(procArgs);
		genAbsTerm(procArg);	
	}	
}

void genAbsActs(ATermList actArgs){
	ATerm actArg;
	
	for(;!ATisEmpty(actArgs); actArgs = ATgetNext(actArgs)) {
		actArg = ATgetFirst(actArgs);		
		genAbsTerm(actArg);
	 }
}

void genAbsInits(ATermList inits){
	ATerm init;
		
	for (;!ATisEmpty(inits); inits= ATgetNext(inits)){
		init = ATgetFirst(inits);
		genAbsTerm(init);	
	}
}

void genAbsCond(ATerm cond){
	genAbsTerm(cond);
}


void genAbsSum(ATerm summ){
	ATerm procSpec, cond, newTerm;
	ATermList procArgs, actArgs;
	ATermList inits;
	ATerm label;
	ATermList vars;
			
	procSpec = ATgetArgument(summ, 3);
	procArgs = (ATermList)ATgetArgument((ATermAppl) procSpec,0);
	
	genAbsProcs(procArgs);

	actArgs = (ATermList)ATgetArgument(summ,2);
	genAbsActs(actArgs);

	cond = ATgetArgument(summ, 4);	
	genAbsCond(cond);
}

void genAbsSummands(){
	ATermList sums, newSums, inits;
	ATerm proc = MCRLgetProc();
	ATerm sum;
	ATbool may = ATfalse;
	
	P("Extracting Abstracted Functions");
	inits = MCRLgetListOfInitValues();
	genAbsInits(inits);
	
	sums = MCRLgetListOfSummands();	
	
	for(;!ATisEmpty(sums); sums= ATgetNext(sums)){
		sum = ATgetFirst(sums);
		genAbsSum(sum);
		fprintf(stderr,".");
	}	
	fprintf(stderr,"\n");
}

/*--------------------------------------------------------------------------*/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/*--------------------------------------------------------------------------*/ 

int main(int argc, char *argv[]) {
    int i, j = 0;
    ATbool result = ATfalse;
 	 ATermList eqs;
	 ATerm adt;
 
    char **newargv = (char**) calloc(argc + 1, sizeof(char*));
	 parseCommandLine(argc, argv);
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0];
    ATinit(argc, argv, (ATerm*) &argc);
	 ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);

	 if (!MCRLinitRW(j, newargv)) exit(-1);
	    
	 initTables();	
	 conflictingSorts = ATmakeList0();
    ATprotect((ATerm *)&conflictingSorts); 
	 
	 if(LOAD){
		f = fopen(loadFile, "r");
		if(!f) ATerror("File %s does not exist", loadFile);
		absAdt = MCRLparseAdt(f);
		ATprotect((ATerm*) &absAdt);
		importFuncs(MCRLparseAdt(f));
		MCRLoutput();
	 }	 
	 if(EXPORT){
   	f = stdout;
	 	genAbsSummands();
		P("Abstract Signature:");
		fprintf(f,"sort\n   "); 
		exportSorts();
		fprintf(f,"\n");
		fprintf(f,"map\n");
		exportFuncs();
	 }
	  
	 if(LIFT){
		ATwarning("Generating Abstract Signature for: %s", sortToAbstractName);
   	f = stdout;
		sortToAbstract = 
			(ATerm) ATmakeAppl0(ATmakeAFun(sortToAbstractName, 0, ATtrue));	
	 	abstractAndLiftFunctions(MCRLgetAdt());
		MCRLoutput();
	 }
	 if(SC){
   	f = stdout;
	 	genAbsSummands();
		genSCs();
	 	
	 }
	 if(AUTO || AUTO_ALL){
	 	genAbsSummands();
		autoAdt();
		MCRLoutput();
	 }	 
    exit(EXIT_SUCCESS);    
}
   
