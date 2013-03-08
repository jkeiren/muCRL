/* $Id: absint.c,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "rw.h"
#include "libAbsint.h"
 
static char *who="AbsInt"; /* Name of the tool */
static ATbool HOMOMORPHISM = ATfalse;
static ATbool GALOIS = ATfalse;
static ATbool LIFTEDHOMO = ATtrue;

static ATbool ALL_VAR = ATfalse;   

static ATbool BUT_PAR = ATfalse;
static ATbool BUT_VAR = ATfalse;
static ATbool BUT_SORT = ATfalse;

static ATbool MAY = ATtrue; 
static ATbool MUST = ATtrue;

static ATbool DEBUG = ATfalse;

int nSum;

/*--------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------*/

static int	numAbsPars = 0;
static char absPars[MAX_NUM_PARS][NAME_LENGTH];

static int	numAbsSorts = 0;
static char absSorts[MAX_NUM_PARS][NAME_LENGTH];

static int	numAbsVars = 0;
static char absVars[MAX_NUM_PARS][NAME_LENGTH];

/*--------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------*/

static void WarningHandler(const char *format, va_list args) {
	if(DEBUG){
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");}
     }
     
static void ErrorHandler(const char *format, va_list args) {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
		fprintf(stderr,"%d: ", nSum);
      
     exit(-1);
     }
 
/*--------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------*/
#define TABLESIZE 500

static ATermTable var_tab, par_tab;
     
static void initTables(void) { 
	 var_tab = ATtableCreate(TABLESIZE,75);
    if (!var_tab) ATerror("Table is not allocated"); 
	 
	 par_tab = ATtableCreate(TABLESIZE,75);
    if (!par_tab) ATerror("Table is not allocated"); 
}
ATermList conflictingPars;

/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

void tokParameters(char *parameterList){
	char listAux[NAME_LENGTH];
	char *par;
	
	strcpy(listAux, parameterList);
	par = (char *)strtok(listAux, "#");
	strcpy(absPars[numAbsPars], par);
	while (par != NULL)
  	{
		numAbsPars++;
    	par = (char *)strtok (NULL, "#");
		if(par != NULL){
			strcpy(absPars[numAbsPars], par);
		}
	}
}

void tokVars(char *varList){
	char listAux[NAME_LENGTH];
	char *var;
	
	strcpy(listAux, varList);
	var = (char *)strtok(listAux, "#");
	strcpy(absVars[numAbsVars], var);
	while (var != NULL)
  	{
		numAbsVars++;
    	var = (char *)strtok (NULL, "#");
		if(var != NULL){
			strcpy(absVars[numAbsVars], var);
		}
	}
}

void tokSorts(char *sortList){
	char listAux[NAME_LENGTH];
	char *sortName;
	
	strcpy(listAux, sortList);
	sortName = (char *)strtok(listAux, "#");

	strcpy(absSorts[numAbsSorts], sortName);
	while (sortName != NULL)
  	{
		numAbsSorts++;
    	sortName = (char *)strtok (NULL, "#"); 
		if(sortName != NULL){
			strcpy(absSorts[numAbsSorts], sortName);
		}
	}
}
 
ATbool toAbstractPar(ATerm parTerm){
	int i;
	char *parName;
	
	parName = MCRLgetName(parTerm);
	
	for(i =0; i< numAbsPars; i++){
		if(!strcmp(absPars[i], parName)){
			if(BUT_PAR) return ATfalse;
			return ATtrue;
		}		
	}
	if(BUT_PAR) return ATtrue;
	return ATfalse;
}

ATbool toAbstractVar(ATerm varTerm){
	int i;
	char *varName;
	
	varName = MCRLgetName(varTerm);
	if(ALL_VAR) return ATtrue;
	for(i = 0; i< numAbsVars; i++){
		if(!strcmp(absVars[i], varName)){
			if(BUT_VAR) return ATfalse;
			return ATtrue;
		}		
	}
	if(BUT_VAR) return ATtrue;
	return ATfalse;
}


ATbool toAbstractSort(ATerm termSort){
	int i;
	char *sortName;
	
	termSort = getConcrete(getUnLifted(termSort));
	
	sortName = MCRLgetName(termSort);
				
	for(i =0; i< numAbsSorts; i++){
		if(!strcmp(absSorts[i], sortName)){
			if(BUT_SORT) return ATfalse;
			return ATtrue;
		}		
	}
	if(BUT_SORT) return ATtrue;
	return ATfalse;
}

/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/


ATbool isParameter(ATerm term){
	if (NULL != ATtableGet(par_tab,term)){
		return ATtrue;
	} 	
	return ATfalse;
}

ATbool isConstant(ATerm term){
	return (ATgetArity(ATgetAFun(term)) == 0);
}

ATbool isVariable(ATerm term){
	if (NULL != ATtableGet(var_tab,term)){
		return ATtrue;
	} 	
	return ATfalse;
}

ATerm getTermSort(ATerm term){
	ATerm sort;
	if(isVariable(term)){
		sort = ATtableGet(var_tab, term);
	}
	else if(isParameter(term)){
		sort = ATtableGet(par_tab, term);
	} 	
	else {
		sort =  (ATerm) ATmake("<str>",ATgetName(MCRLgetSort(term)));
	}
	if(!strcmp("\"<int>\"", ATwriteToString(sort))){
		PP("ERROR: ");
		PP(ATgetName(MCRLgetSort(term)));
		fprintf(stderr, " %d ", nSum);
		pTerm(term);
		exit(0);
	}
	return sort;
}


/*--------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------*/
static void helpmsg() 
{  
    P("Reads a mCRL specification in tbf format from the standard input");
    P("and generates a new may/must abstract specification");
	 P("Usage: absint [options]");
	 P("The following options can be used:");	
	 P("-P list: \tParameters to abstract");
  	 P("-PallBut list: \tParameters to keep concrete");
	 P("-V list:\tVariables to abstract");
	 P("-Vall:\t\tAll variables to abstract");
	 P("-VallBut list: \tVariables to keep concrete ");
	 P("-S list:\tSorts to abstract");
	 P("-SallBut list:\tSorts to keep concrete\t");
    P("list:\tnames joint by '#'. Example: t#s#...#r");
	 P("-help:\tYields this message");
 	 P("-H:\tUses Homomorphic abstraction");
 	 P("-lH:\tUses Lifted Homomorphism ");
    P("-G:\tUses Galois Connection abstraction");
    P("-May:\tOnly May actions are generated");
    P("-Must:\tOnly Must actions are generated");
}

/*--------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------*/
static void parseCommandLine(int argc, char *argv[]){
	int i = 0, j;
	
	P("Abstract Interpreter for mCRL Specifications");
	for (i=1;i<argc;i++) {
	  if (!strcmp(argv[i - 1],"-P")){
	  		BUT_PAR = ATfalse;
			tokParameters(argv[i]);
	  		continue;
	  } 
	  if (!strcmp(argv[i],"-Pall")){	
	  		BUT_PAR = ATfalse;
			continue;
	  } 
	  if (!strcmp(argv[i-1],"-PallBut")){	
	  		BUT_PAR = ATtrue;
	  		tokParameters(argv[i]);
			continue;
	  } 
	  if (!strcmp(argv[i-1],"-VallBut")){	
	  		BUT_VAR = ATtrue;
	  		ALL_VAR = ATfalse;
	  		tokVars(argv[i]);
			continue;
	  } 
	  if (!strcmp(argv[i - 1],"-V")){
	  		BUT_VAR = ATfalse;
	  		ALL_VAR = ATfalse;
	  		tokVars(argv[i]);
	  		continue;
	  } 
	  if (!strcmp(argv[i],"-Vall")){	
	  		BUT_VAR = ATfalse;
	  		ALL_VAR = ATtrue;
			continue;
	  } 
	  if (!strcmp(argv[i-1],"-VallBut")){	
	  		BUT_VAR = ATtrue;
	  		ALL_VAR = ATfalse;
	  		tokVars(argv[i]);
			continue;
	  } 
	  if (!strcmp(argv[i - 1],"-S")){
	  		BUT_SORT = ATfalse;
	  		tokSorts(argv[i]);
	  		continue;
	  } 
	  if (!strcmp(argv[i - 1],"-SallBut")){
	  		BUT_SORT = ATtrue;
	  		tokSorts(argv[i]);
	  		continue;
	  } 
	  if (!strcmp(argv[i],"-H")){
	  		HOMOMORPHISM = ATtrue;
	  		GALOIS = ATfalse;
	  		LIFTEDHOMO = ATfalse;
         continue;
	  }
	  if (!strcmp(argv[i],"-lH")){
	  		HOMOMORPHISM = ATfalse;
	  		GALOIS = ATfalse;
	  		LIFTEDHOMO = ATtrue;
         continue;
	  }
	  if (!strcmp(argv[i],"-G")){
	  		HOMOMORPHISM = ATfalse; 
	  		GALOIS = ATtrue;
	  		LIFTEDHOMO = ATfalse; 
         continue;
		} 
	  if (!strcmp(argv[i],"-help")){
	  		helpmsg();
    		exit(0);
	  }
	  if (!strcmp(argv[i],"-May")){
	  	   MUST = ATfalse;
			continue;
		}
	  if (!strcmp(argv[i],"-Must")){
	  		MAY = ATfalse;
      	continue;
		}
	  if (!strcmp(argv[i],"-Debug")){
	  		DEBUG = ATtrue;
      	continue;
		}
	  if (!strcmp(argv[i],"-Order")){
	  		setOrder();
      	continue;
		}
	} 	
	if(HOMOMORPHISM)
		P("Abstraction Type: HOMOMORPHISM");
	if(LIFTEDHOMO)
		P("Abstraction Type: LIFTED HOMOMORPHISM");
	if(GALOIS){
		setGalois();
		P("Abstraction Type: GALOIS CONNECTION");
	}
}

/*--------------------------------------------------------------------------*/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/****************************************************************************/
/*--------------------------------------------------------------------------*/ 
ATbool toLiftTerm(ATerm term);


ATbool toLiftFunc(ATerm func){
	ATerm arg;
	int i;
	ATermList argSorts, args;
	ATerm fSort, argSort;
	
	fSort = getTermSort(func);

	argSorts = getFuncSortList(func);
	
	if(toAbstractSort(fSort))
		return ATtrue;
		
	for(i=0; i< ATgetArity(ATgetAFun(func)); i++){
		arg = ATgetArgument((ATermAppl) func, i);		
		if(toLiftTerm(arg))
			return ATtrue;
	}	
	return ATfalse;
}

ATbool toLiftTerm(ATerm term){
	ATerm sort;
	if(isParameter(term) || isVariable(term)){
		sort = getTermSort(term);		
		return isLifted(sort) || isAbstracted(sort);
	}	
	else { /* is a function */
		return toLiftFunc(term);
	}
}

void liftPars(){
	 ATermList sums, newSums;
	 ATerm sum;
	 ATerm procSpec, procArg;
	 ATermList procArgs;
	 
	 ATermList pars, newPars;
	 ATerm proc = MCRLgetProc();	
	 ATerm par, parName, parSort;
	 ATbool repeat;
	 
	 do{
	 	repeat = ATfalse;
		sums = MCRLgetListOfSummands();
		for(;!ATisEmpty(sums); sums= ATgetNext(sums)){
			sum = ATgetFirst(sums);	
			procSpec = ATgetArgument(sum, 3);
			procArgs = (ATermList)ATgetArgument((ATermAppl) procSpec,0);
			pars = MCRLgetListOfPars();
			newPars = ATmakeList0();
		
			for(;!ATisEmpty(procArgs); 
					procArgs = ATgetNext(procArgs), pars = ATgetNext(pars)) { 
				procArg = ATgetFirst(procArgs);
				par = ATgetFirst(pars);
				parSort = (ATerm) ATgetArgument((ATermAppl) par, 1);
				parName = (ATerm) ATgetArgument((ATermAppl) par, 0);
				if(!isLifted(parSort)){
					if(toLiftTerm(procArg)){
						repeat = ATtrue;
						parSort = liftSort(parSort);
					}
				}		
				par = (ATerm) ATsetArgument((ATermAppl) par, parSort, 1);
				newPars = ATappend(newPars, par);
				ATtablePut(par_tab, parName, parSort);
			}
			proc = (ATerm) ATsetArgument((ATermAppl)proc,(ATerm) newPars, 1);
			MCRLsetProc(proc);
			if(repeat) break;
			fprintf(stderr,".");
	 	}
	}while(repeat);
}   

void abstractVars(){	
	ATermList newSums, sums = MCRLgetListOfSummands();
	ATermList vars, newVars;
	ATerm proc, sum; 
	ATerm var, varSort, varName, oldVarSort;
		
	proc = MCRLgetProc();
	newSums = ATmakeList0();
	
	for(;!ATisEmpty(sums); sums= ATgetNext(sums)){
		sum = ATgetFirst(sums);	
		vars = (ATermList) ATgetArgument((ATermAppl) sum ,0);
		newVars = ATmakeList0();

		for(;!ATisEmpty(vars);  vars= ATgetNext(vars)){
			var = (ATerm) ATgetFirst(vars);
		   varName = (ATerm) ATgetArgument((ATermAppl) var, 0);
		   varSort = (ATerm) ATgetArgument((ATermAppl) var, 1);
		
			oldVarSort = ATtableGet(var_tab, varName);
			
			if(oldVarSort != NULL)
				if(varSort != getConcrete(oldVarSort)){
				PP("Variable "); ppTerm(varName);
				PP(" appears with two different types, ");
				ppTerm(varSort); PP(" and "); pTerm(oldVarSort);
				P("please modify the specification");
				exit(-1);
			}
		
		
			if(toAbstractVar(varName)){
				varSort = abstractSort(varSort);
			}
			if(toAbstractSort(varSort)){
				varSort = abstractSort(varSort);
			}
			if(!toAbstractSort(varSort) && BUT_SORT){
				varSort = getConcrete(varSort);
			}
			
			
			ATtablePut(var_tab, varName, varSort);
			
			var = (ATerm) ATsetArgument((ATermAppl) var, varSort, 1);
			newVars = ATinsert(newVars, var);		

		}
		sum = (ATerm) ATsetArgument((ATermAppl) sum, 
				(ATerm) ATreverse(newVars), 0);
		newSums = ATinsert(newSums, sum);
	}
	
	proc = (ATerm) ATsetArgument((ATermAppl) proc, 
					(ATerm)ATreverse(newSums), 2);

	MCRLsetProc(proc);
}
     

void abstractPars(){
	 ATermList pars = MCRLgetListOfPars();
	 ATermList newPars = ATmakeList0();
	 ATerm proc = MCRLgetProc();
	 ATerm par, parName, parSort;
	 
	 for(;!ATisEmpty(pars); pars= ATgetNext(pars)){
		par = (ATerm) ATgetFirst(pars);
		parName = (ATerm) ATgetArgument((ATermAppl) par, 0);
		parSort = (ATerm) ATgetArgument((ATermAppl) par, 1);
		if(toAbstractPar(parName)){
			parSort = liftSort(abstractSort(parSort));
		}
		if(toAbstractSort(parSort)){
			parSort = liftSort(abstractSort(parSort));
		}
		if(!toAbstractSort(parSort) && BUT_SORT){
			parSort = getConcrete(getUnLifted(parSort));
		}
				
		par = (ATerm) ATsetArgument((ATermAppl) par, parSort, 1);
		newPars = ATappend(newPars, par);
		ATtablePut(par_tab, parName, parSort);
	 }
	 proc = (ATerm) ATsetArgument((ATermAppl)proc,(ATerm) newPars, 1);
	 MCRLsetProc(proc);
}


void abstractParsAndVars(){
	P("Abstracting Parameters and Variables:");	
	abstractPars();
	abstractVars();
	liftPars();	
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

ATerm termAbstraction(ATerm term, ATerm dstSort);


ATbool toLiftTarget(ATerm termSort, ATerm fSort){
	
	if(isLifted(fSort))
		return ATfalse;
		
	if(isAbstracted(termSort) || isLifted(termSort)){
			return ATtrue;
	}
	
	return ATfalse;
}

ATbool toAbstractTarget(ATerm termSort, ATerm fSort){
	
	if(isAbstracted(fSort))
		return ATfalse;
	
	if(isAbstracted(termSort)){
		if(matchesSort(termSort, fSort))
			return ATtrue;
	}
	return ATfalse;	
}

ATbool toAbstractArg(ATerm argSort, ATermList argSorts, ATerm fSort){
	ATerm argSortAux;
	
	if(isAbstracted(argSort))
		return ATfalse;
		
	if(toAbstractSort(argSort))
		return ATtrue;	
	
	if(matchesSort(argSort, fSort)){
		if(isAbstracted(fSort) && !isAbstracted(argSort)){
				return ATtrue;
			}
	}		
	for(;!ATisEmpty(argSorts); argSorts = ATgetNext(argSorts)){
		argSortAux = ATgetFirst(argSorts);		
		if(matchesSort(argSort, argSortAux)){
			if(isAbstracted(argSortAux) && !isAbstracted(argSort)){
				return ATtrue;
			}
		}				
	}
	return ATfalse;
}

 
ATerm funcAbstraction(ATerm func, ATerm dstSort){ 
	ATermList argSorts;
	ATerm newTerm, newTermSort;
	ATerm arg, argSort, fSort, argSortAux;  
	ATbool  modified;
	int i, j;
	char *fName;
	AFun fun;
	
	argSorts = getFuncSortList(func);	
	fSort = getTermSort(func);
	
	fun = ATgetAFun(func); 
	fName = ATgetName(fun);
	
	if(reservedFunc(fun)) 
		return func;	

	do{
		modified = ATfalse;
		for(i=0; i< ATgetArity(ATgetAFun(func)); i++){
			arg = ATgetArgument((ATermAppl) func, i);
			argSort = ATelementAt(argSorts, i);
	 
			if(toAbstractArg(argSort, argSorts, fSort))
				argSort = liftSort(abstractSort(getUnLifted(argSort)));
			
			
			newTerm = termAbstraction(arg, argSort);
			newTermSort = getTermSort(newTerm); 
			
			
			if(newTerm != arg)
				modified = ATtrue;
			
			func = (ATerm) ATsetArgument((ATermAppl) func, newTerm, i);
			argSorts =  ATreplace(argSorts, newTermSort, i);
			
			if(toAbstractTarget(newTermSort, fSort))
				fSort = liftSort(abstractSort(getUnLifted(fSort)));
			
			if(toLiftTarget(newTermSort, fSort))
				fSort = liftSort(fSort);
				
			if(modified) break;
		}
	} while(modified);
		
	
	if(toAbstractSort(fSort) && abstractedSorts(argSorts))
		fSort = liftSort(abstractSort(getUnLifted(fSort)));

	func = createNewFuncTerm(func, argSorts, fSort);
	return func;
}


ATerm termAbstraction(ATerm term, ATerm dstSort){
	ATerm newCons;
	AFun singTag;
	ATerm termSort, parSort;
	
	
	if(!(isVariable(term) || isParameter(term) || isConstant(term))){
		term = funcAbstraction(term, dstSort);	
		
	}
	termSort = getTermSort(term);
	
	if(isLifted(dstSort)){
		if(isAbstracted(dstSort)){
			if(!isAbstracted(termSort)){
				if(!isLifted(termSort)){
					termSort = liftSort(termSort);
					term = createSingTerm(term, termSort);
				}
				term = createAlphaTerm(term, termSort);
			}
			else{
				if(!isLifted(termSort)){
					termSort = liftSort(abstractSort(termSort));
					term = createSingTerm(term, termSort);		
				}
			}
		}
		else{
			if(!isLifted(termSort)){
				termSort = liftSort(termSort);
				term = createSingTerm(term, termSort);		
			}
		}		
	}
	
	return term;
}

/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

ATermList procAbstraction(ATermList procArgs){
	ATerm procArg, newTerm, par, parSort, parName;
	ATermList newProcArgs = ATmakeList0();	
	ATermList pars = MCRLgetListOfPars();
	ATerm termSort;
		
	for (;!ATisEmpty(procArgs); 
			procArgs = ATgetNext(procArgs), pars = ATgetNext(pars)) { 
		procArg = ATgetFirst(procArgs);	
		par = ATgetFirst(pars);
		parSort = (ATerm) ATgetArgument((ATermAppl) par, 1);
		parName = (ATerm) ATgetArgument((ATermAppl) par, 0);
		newTerm = termAbstraction(procArg, parSort);	
		
		termSort = getTermSort(newTerm);
		

		if(isAbstracted(termSort) && !isAbstracted(parSort)){
			if(!isLifted(termSort)){
				newTerm = createSingTerm(newTerm, liftSort(termSort));
				termSort = liftSort(termSort);
			}
			newTerm = createGammaTerm(newTerm, termSort);
			if(-1 == ATindexOf(conflictingPars, parName , 0))
				conflictingPars = ATappend(conflictingPars, parName);
		}
					
		newProcArgs = ATappend(newProcArgs, newTerm);
	}
	return newProcArgs;	
}

ATermList actAbstraction (ATermList actArgs){
	ATerm actArg, actArgSort, newTerm;
	ATermList newActArgs = ATmakeList0();
	
	for(;!ATisEmpty(actArgs); actArgs = ATgetNext(actArgs)) {
		actArg = ATgetFirst(actArgs);
		actArgSort = getTermSort(actArg);				
		if(toAbstractSort(actArgSort)){
			actArgSort = liftSort(abstractSort(getUnLifted(actArgSort)));
		}
		newTerm = termAbstraction(actArg, actArgSort);
		newActArgs = ATappend(newActArgs, newTerm);
	 }
	return newActArgs;
}

ATerm condAbstraction(ATerm cond){
	return termAbstraction(cond, MCRLterm_bool);	
}

ATermList initAbstraction(ATermList inits){
	ATermList pars = MCRLgetListOfPars();
	ATermList newInits = ATmakeList0();
	ATerm init, par, parSort, newTerm, initSort;
		
	for (;!ATisEmpty(inits); inits= ATgetNext(inits), pars = ATgetNext(pars)){
		init = ATgetFirst(inits);
		par = ATgetFirst(pars);
		parSort = (ATerm) ATgetArgument((ATermAppl) par, 1);
		newTerm = init;
		initSort = getConcrete(getUnLifted(parSort));
		if(isLifted(parSort)){
			initSort = liftSort(initSort);
			newTerm = createSingTerm(newTerm, initSort);
		}		
		if(isAbstracted(parSort)){
			newTerm = createAlphaTerm(newTerm, initSort);
		}
		newInits = ATappend(newInits, newTerm);
		
	}
	return newInits;
}

/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

ATerm sumAbstraction(ATerm proc){
	ATerm procSpec, cond, newTerm;
	ATermList procArgs, actArgs;
	ATermList inits;
	
	procSpec = ATgetArgument(proc, 3);
	procArgs = (ATermList)ATgetArgument((ATermAppl) procSpec,0);

	newTerm = (ATerm) procAbstraction(procArgs);
	
	procSpec = (ATerm)ATsetArgument((ATermAppl)procSpec, newTerm, 0);
	proc = (ATerm)ATsetArgument((ATermAppl)proc, procSpec, 3);
		
	actArgs = (ATermList)ATgetArgument(proc,2);
	newTerm = (ATerm)actAbstraction(actArgs);
	proc = (ATerm)ATsetArgument((ATermAppl)proc, newTerm, 2);
	
	cond = ATgetArgument(proc, 4);	
	newTerm = condAbstraction(cond);
	proc = (ATerm)ATsetArgument((ATermAppl)proc, newTerm, 4);
	
	return proc;
}


void specAbstraction(){	
	ATermList inits;
	ATermList newSums, sums;
	int i;
	ATerm proc, sum, var, varName, parName, par;
	ATermList vars, pars, newVars, newPars;
	
	proc = MCRLgetProc();
	
	P("Specification Abstraction");	
	
	inits = MCRLgetListOfInitValues();
	inits = initAbstraction(inits);
	proc = (ATerm) ATsetArgument((ATermAppl)proc, (ATerm) inits, 0);
	MCRLsetProc(proc);
	
	newSums = ATmakeList0();
	sums = MCRLgetListOfSummands();
	for(nSum = 1; !ATisEmpty(sums); sums= ATgetNext(sums), nSum++){ 
		sum = ATgetFirst(sums);	
	 	sum = sumAbstraction(sum);
		newSums = ATinsert(newSums, sum);
		fprintf(stderr,".");
	}
		
	proc = (ATerm) ATsetArgument((ATermAppl) proc, 
						(ATerm) newSums, 2);
	MCRLsetProc(proc);
	
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


ATerm addVar(ATerm sum, ATerm varName, ATerm varSort){
	ATermList vars = ATmakeList0();
	ATerm var;
	AFun vTag  = ATmakeSymbol("v",2, ATfalse); 
	
	vars = (ATermList) ATgetArgument((ATermAppl) sum ,0);
	vars = ATinsert(vars,(ATerm)ATmakeAppl2(vTag,varName,varSort));
	
	return (ATerm) ATsetArgument((ATermAppl) sum, (ATerm) vars, 0);
}

ATerm createAuxCondition2(ATerm auxCond, ATerm cond){
	AFun andTag;
	andTag = createNewFuncSym(andSym, 
			ATmakeList2(MCRLterm_bool, MCRLterm_bool));
	
	if(auxCond != NULL){
		cond = (ATerm) ATmakeAppl2(andTag, cond, 
							auxCond);
	} 
	return cond;
}
ATerm createSingleton(ATerm value, ATerm sort){
	ATerm setSort;
	AFun inFun; 
	ATerm emptyTerm;
	
	setSort = liftSort(sort);
	inFun = createInCons(sort, setSort);
	emptyTerm = createEmptyCons(setSort);
	
	return (ATerm) ATmakeAppl2(inFun, value, emptyTerm);
}

ATerm createMemberAuxCondition(ATerm cond, ATerm var, 
					ATerm arg, ATerm varSort){
	AFun memberTag, andTag;
	
	memberTag = createNewFuncSym(memberSym, 
			ATmakeList2(varSort, liftSort(varSort)));
	
	andTag = createNewFuncSym(andSym, 
			ATmakeList2(MCRLterm_bool, MCRLterm_bool));
			
	if(cond == NULL){
		cond = (ATerm) ATmakeAppl2(memberTag, var, arg);
	} 
	else{
		cond = (ATerm) ATmakeAppl2(andTag, cond, 
							(ATerm) ATmakeAppl2(memberTag, var, arg));
	}
	return cond;
}

ATerm createSingletonAuxCondition(ATerm cond, ATerm func, ATerm fSort){
	AFun singletonTag, andTag;
	andTag = createNewFuncSym(andSym, 
			ATmakeList2(MCRLterm_bool, MCRLterm_bool));
	
	singletonTag = createNewFuncSym(singletonSym, 
		ATmakeList1(fSort));	
			
	if(cond == NULL){
		cond = (ATerm) ATmakeAppl1(singletonTag, func);
	} 
	else{
		cond = (ATerm) ATmakeAppl2(andTag, cond, 
							(ATerm) ATmakeAppl1(singletonTag, func));
	}
	return cond;
}

ATerm createMaySum(ATerm sum){	
	ATerm cond, newCond, condSort, act, newAct, newSum;
	char newActName[250];
	AFun memberTag; 
	ATbool toAbs = ATfalse;
	
	
	memberTag = createNewFuncSym(memberSym, 
			ATmakeList2(MCRLterm_bool, liftSort(MCRLterm_bool)));
	
	cond = (ATerm) ATgetArgument((ATermAppl) sum ,4);
	condSort = getTermSort(cond);
	
	if(isLifted(condSort)) toAbs = ATtrue;
	
	if(isAbstracted(condSort))
		cond = createGammaTerm(cond, condSort);
	
	
	if(toAbs){	
		newCond = (ATerm) ATmakeAppl2(memberTag, MCRLterm_true, cond);
		newSum = (ATerm) ATsetArgument((ATermAppl) sum, (ATerm) newCond, 4);
	}
	else{
		newCond = cond;
	}
	
	newSum = (ATerm) ATsetArgument((ATermAppl) sum, (ATerm) newCond, 4);
	act = (ATerm) ATgetArgument((ATermAppl) sum, 1);
	appendString(MCRLgetName(act), maySufix, newActName);
	newAct = (ATerm) ATmakeAppl0(ATmakeAFun(newActName, 0, ATtrue));
	return (ATerm) ATsetArgument((ATermAppl) newSum, (ATerm) newAct, 1);	
}

ATerm createMustSum(ATerm sum){	
	ATerm cond, newCond, condSort, act, newAct, newSum;
	char newActName[250];
	AFun memberTag; 
	ATbool toAbs = ATfalse;
	
	memberTag = createNewFuncSym(memberSym, 
			ATmakeList2(MCRLterm_bool, liftSort(MCRLterm_bool)));
	
	cond = (ATerm) ATgetArgument((ATermAppl) sum ,4);	
	condSort = getTermSort(cond);
	
	if(isLifted(condSort)) toAbs = ATtrue;
	
	if(isAbstracted(condSort))
		cond = createGammaTerm(cond, condSort);
		
	if(toAbs){	
		newCond = (ATerm) ATmakeAppl1(MCRLsym_not,
			(ATerm) ATmakeAppl2(memberTag, MCRLterm_false, cond));
	}
	else{
		newCond = cond;
		newSum = sum;
	}
	newSum = (ATerm) ATsetArgument((ATermAppl) sum, (ATerm) newCond, 4);
	act = (ATerm) ATgetArgument((ATermAppl) sum, 1);
	appendString(MCRLgetName(act), mustSufix, newActName);
	newAct = (ATerm) ATmakeAppl0(ATmakeAFun(newActName, 0, ATtrue));
	return (ATerm) ATsetArgument((ATermAppl) newSum, newAct, 1);
}


ATermList generateNewSums(ATerm sum){
	ATerm maySum, mustSum;
	ATermList procArgs, newProcArgs;
	ATerm  proc, procArg, procArgSort;
	ATermList actArgs;
	ATermList newActArgs;
   ATerm actArg, actArgSort;
	ATermList vars;
	ATerm var, varName, varSort;
	ATerm cond, auxMayCondition, auxMustCondition;
	int i;
	char auxVarName[NAME_LENGTH];
	
	proc = (ATerm) ATgetArgument(sum, 3);
	procArgs = (ATermList)ATgetArgument(proc, 0);
	newProcArgs = ATmakeList0();
	
	auxMayCondition = NULL;
	auxMustCondition = NULL;
	maySum = sum;	
	mustSum = sum;					
	if(HOMOMORPHISM){
		for(i=0;!ATisEmpty(procArgs); procArgs= ATgetNext(procArgs)) {
			procArg = ATgetFirst(procArgs);	
			
			procArgSort = getTermSort(procArg);
			
			if(isLifted(procArgSort)){
				sprintf(auxVarName, "%s%d", auxVarPrefix, i);
				i++;
				varName = (ATerm)ATmakeAppl0(ATmakeAFun(auxVarName, 0, ATtrue));
				varSort = getUnLifted(procArgSort);
				maySum = addVar(maySum, varName, varSort);
				newProcArgs = ATappend(newProcArgs, 
						createSingleton(varName, varSort));
				auxMayCondition = createMemberAuxCondition(auxMayCondition, 
							varName, procArg, varSort);
				auxMustCondition = createSingletonAuxCondition(auxMustCondition, 
						procArg, procArgSort);
			}
			else{
				newProcArgs = ATappend(newProcArgs, procArg);	
			}
		}
		proc = (ATerm)ATsetArgument((ATermAppl)
					proc, (ATerm) newProcArgs, 0);
		maySum = (ATerm)ATsetArgument((ATermAppl)maySum, proc, 3);
	
		mustSum = sum;					
		actArgs = (ATermList)ATgetArgument(sum,2);
		newActArgs = ATmakeList0();
				
		for(;!ATisEmpty(actArgs); actArgs= ATgetNext(actArgs),i++) {
			actArg = ATgetFirst(actArgs);	
			actArgSort = getTermSort(actArg);
			if(isLifted(actArgSort)){
				sprintf(auxVarName, "%s%d", auxVarPrefix, i);
				i++;
				varName = (ATerm)ATmakeAppl0(ATmakeAFun(auxVarName, 0, ATtrue));
				varSort = getUnLifted(actArgSort);
				maySum = addVar(maySum, varName, varSort);
				mustSum = addVar(mustSum, varName, varSort);
				newActArgs = ATappend(newActArgs, varName);
				auxMayCondition = createMemberAuxCondition(auxMayCondition, 
							varName, actArg, varSort);
				auxMustCondition = createMemberAuxCondition(auxMustCondition, 
							varName, actArg, varSort);
				auxMustCondition = createSingletonAuxCondition(auxMustCondition, 
						actArg, actArgSort);	
			}
			else{
				newActArgs = ATappend(newActArgs, actArg);	
			}
			maySum = (ATerm)ATsetArgument((ATermAppl)maySum,
				(ATerm)newActArgs, 2);
		}
	}
		maySum = (ATerm)createMaySum(maySum);
		mustSum = (ATerm)createMustSum(mustSum);

	if(HOMOMORPHISM){	
		cond = ATgetArgument(maySum, 4);
		cond = createAuxCondition2(auxMayCondition, cond);	
		maySum = (ATerm)ATsetArgument((ATermAppl)maySum, cond, 4);
	
		cond = ATgetArgument(mustSum, 4);
		cond = createAuxCondition2(auxMustCondition, cond);	
		mustSum = (ATerm)ATsetArgument((ATermAppl)mustSum, cond, 4);
	}
	
	if(MAY && MUST)
		return ATmakeList2(maySum, mustSum);
	else if(MAY)
		return ATmakeList1(maySum);
	else if(MUST)
		return ATmakeList1(mustSum);
}

void abstractSummands(){	
	ATermList mayMustSums, newSums, sums = MCRLgetListOfSummands();
	ATerm proc, sum;
	
	proc = MCRLgetProc();
	newSums = ATmakeList0();
	
	P("Generating Abstract Summands");
	sums = ATreverse(sums);
	for(nSum = 1; !ATisEmpty(sums); sums= ATgetNext(sums), nSum++){
		sum = ATgetFirst(sums);	
		mayMustSums = generateNewSums(sum);
		newSums = ATconcat(newSums, mayMustSums);
		fprintf(stderr,".");
	}
	
	proc = (ATerm) ATsetArgument((ATermAppl) proc, 
					(ATerm)newSums, 2);

	MCRLsetProc(proc);	
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
ATbool prevAbstraction(){
	ATermList sorts;
	ATerm sort;
		
	sorts = getListOfSorts(MCRLgetAdt());
	return abstractedOrLiftedSorts(sorts); 
}


void initAbsInt(){
	ATbool ok;
	AFun memberTag;	

	initTables();	
	
	conflictingPars = ATmakeList0();

	ATprotect((ATerm *)&conflictingPars);
	
	memberTag = createNewFuncSym(memberSym, 
			ATmakeList2(MCRLterm_bool, liftSort(MCRLterm_bool)));
	
	MCRLputMap((ATerm)ATmakeAppl2(memberTag, 
				MCRLterm_bool, liftSort(MCRLterm_bool)), 
			MCRLterm_bool, &ok);	
}

void printResults(){
	ATermList pars;
	ATermList vars;
	ATermList abstracted, lifted;
	ATerm par, parSort;
	ATerm var, varSort;
	
	abstracted = ATmakeList0();
	lifted = ATmakeList0();
	
	pars = ATtableKeys(par_tab);
	for(;!ATisEmpty(pars); pars = ATgetNext(pars)){
		par = ATgetFirst(pars);
		parSort = ATtableGet(par_tab, par);
		if(isAbstracted(parSort)){
			abstracted = ATinsert(abstracted, par);
		}
		else if (isLifted(parSort)){
			lifted = ATinsert(lifted, par);
		}
	}
	fprintf(stderr, "%d Parameters Abstracted:\n", ATgetLength(abstracted));
	pTerm((ATerm) abstracted);
	fprintf(stderr, "%d Parameters Lifted:\n", ATgetLength(lifted)); 
	pTerm((ATerm) lifted);
	fprintf(stderr, "%d Conflicting Parameters:\n", 
			ATgetLength(conflictingPars)); 
	pTerm((ATerm) conflictingPars);
	
	abstracted = ATmakeList0();
	vars = ATtableKeys(var_tab);
	for(;!ATisEmpty(vars); vars = ATgetNext(vars)){
		var = ATgetFirst(vars);
		varSort = ATtableGet(var_tab, var);
		if(isAbstracted(varSort)){
			abstracted = ATinsert(abstracted, var);
		}
	}
	fprintf(stderr, "%d Variables Abstracted:\n", ATgetLength(abstracted));
	pTerm((ATerm) abstracted);
}

int main(int argc, char *argv[]) {
    int i, j = 0;
    ATbool result = ATfalse; 	
    int absCounter;
	 char **newargv = (char**) calloc(argc + 1, sizeof(char*));
	 
	 parseCommandLine(argc, argv);
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0];
    ATinit(argc, argv, (ATerm*) &argc);
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
 	 if (!MCRLinitRW(j, newargv)) exit(-1);
	 
	 fprintf(stderr, "Number of Summands (input): %d\n",
	 	 ATgetLength(MCRLgetListOfSummands()));
	 
	 if(prevAbstraction()){
	 	P("The Specification has been abstracted before.");
		exit(0);
	 }
	 initAbsInt();
	 
	 abstractParsAndVars();
	 specAbstraction();
	 abstractSummands();
	 
	 fprintf(stderr, "Number of Summands (output): %d\n",
	 	 ATgetLength(MCRLgetListOfSummands()));

	 printResults();
	 
	 MCRLoutput();
	 
    if (!result) exit(EXIT_FAILURE); else exit(EXIT_SUCCESS);    
}
   
