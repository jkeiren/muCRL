/* $Id: libAbsint.c,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */

#include <string.h>
#include "libAbsint.h"

ATbool ORDER = ATfalse;
ATbool GALOIS =ATfalse;

void setOrder(){ 
	ORDER = ATtrue;
}

void setGalois(){
	GALOIS = ATtrue;
}
/*-------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

void appendString(char *head, char *tail, char *newString){
	strcpy(newString, head);
	newString = (char *)strcat(newString, tail);
}
/*-------------------------------------------------------------*/ 
/*----------------------------------------------------------------------------*/

ATbool createMCRLSort(ATerm sort){
	ATbool ok; 
	MCRLputSort(sort, &ok);
	if(MONITOR && ok)
		ATwarning("New Sort %s", ATwriteToString(sort));
	return ok;
}
/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/

ATbool hasPrefix(char *string, char *prefix){
	int i;
	if(strlen(string) < strlen(prefix)){
		return ATfalse;
	}
	for(i=0; i< strlen(prefix); i++){
		if(string[i] != prefix[i])
			return ATfalse;
	}
	return ATtrue;
}
ATbool isLifted(ATerm sort){
	if(hasPrefix(ATgetName(ATgetAFun(sort)), setPrefix)){
		return ATtrue;
	}
	return ATfalse;
}

ATerm getUnLifted(ATerm sort){
	char name[NAME_LENGTH];
	char *sortName;
	int i, j;
	
	if(!isLifted(sort)){
		return sort;
	}
	
	sortName = ATgetName(ATgetAFun(sort));
	
	for(i=strlen(setPrefix), j = 0; i< strlen(sortName); i++, j++){
		name[j] = sortName[i];
		name[j + 1] = (char)NULL;
	}
	return (ATerm) ATmake("<str>", name);
}



ATbool isAbstracted(ATerm sort){
	if(isLifted(sort))
		sort = getUnLifted(sort);
	if(hasPrefix(ATgetName(ATgetAFun(sort)), absPrefix)){
		return ATtrue;
	}	
	return ATfalse;
}

ATerm getConcrete(ATerm sort){
	char name[NAME_LENGTH];
	char *sortName;
	int i, j;
	int len;
	int aux; 
	 
	
	if(isLifted(sort)){
		ATerror("Cannot get Concrete of a lifted sort");
	}
	
	if(!isAbstracted(sort)){
		return sort;
	}
	
	sortName = ATgetName(ATgetAFun(sort));
	
	if(2 == sscanf(sortName + strlen(absPrefix), "%d_%s", &aux, name)){
		return (ATerm) ATmake("<str>", name);
	}
	
	for(i=strlen(absPrefix), j = 0; i< strlen(sortName); i++, j++){
		name[j] = sortName[i];
		name[j + 1] = (char)NULL;
	}
	return (ATerm) ATmake("<str>", name);
}

ATbool matchesSort(ATerm s1, ATerm s2){
	if(isLifted(s1)) s1 = getUnLifted(s1);
	if(isLifted(s2)) s2 = getUnLifted(s2);
	if(isAbstracted(s1)) s1 = getConcrete(s1);
	if(isAbstracted(s2)) s2 = getConcrete(s2);
	return s1 == s2;	
}



AFun createAbstractH(ATerm absSort){
	AFun tag;
	ATbool ok;
	ATerm func, sort;	
	
	sort = getConcrete(absSort);
	
	tag = createNewFuncSym(absH, ATmakeList1(sort));
	func = (ATerm)ATmakeApplList(tag, ATmakeList1(sort));
	MCRLputMap(func, absSort, &ok);
	
	return tag;
}

AFun createAbstractHinv(ATerm absSort){
	AFun tag;
	ATbool ok;
	ATerm func, sort;	
	
	sort = getConcrete(absSort);
	
	if(GALOIS)
		tag = createNewFuncSym(absGamma, ATmakeList1(absSort));
	else
		tag = createNewFuncSym(absHinv, ATmakeList1(absSort));
	func = (ATerm)ATmakeApplList(tag, ATmakeList1(absSort));
	MCRLputMap(func, liftSort(sort), &ok);
	
	return tag;
}

AFun createAbstractAlpha(ATerm absSort, AFun H){
	AFun alpha;
	ATbool ok;
	ATerm func, sort;	
	ATerm emptyTerm, emptyAbsTerm, X, x, newEq;
	ATerm fullTerm, fullAbsTerm;
	ATermList vars;
	AFun inFun, inAbsFun;
	ATerm left, right;
	
	sort = getConcrete(absSort);
	
	alpha = createNewFuncSym(absAlpha, 
			ATmakeList1(liftSort(sort)));
	func = (ATerm)ATmakeApplList(alpha, ATmakeList1(liftSort(sort)));
	MCRLputMap(func, liftSort(absSort), &ok);
	
	if(GALOIS) return alpha;
	
	emptyTerm = createEmptyCons(liftSort(sort));
	emptyAbsTerm = createEmptyCons(liftSort(absSort));
	
	fullTerm = createFullCons(liftSort(sort));
	fullAbsTerm = createFullCons(liftSort(absSort));
	
	inFun = createInCons(sort, liftSort(sort));
	inAbsFun = createInCons(absSort, liftSort(absSort));
	
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	
	vars = ATmakeList0();
	
	left = (ATerm) ATmakeAppl1(alpha, emptyTerm);
	right = emptyAbsTerm;
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	left = (ATerm) ATmakeAppl1(alpha, fullTerm);
	right = fullAbsTerm;
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	
	
	MCRLputEquation(newEq, &ok);
	
	vars = ATmakeList2(ATmake("v(<term>, <term>)", x, sort),
					   ATmake("v(<term>, <term>)", X, liftSort(sort)));
	
	left = (ATerm) ATmakeAppl1(alpha, (ATerm)ATmakeAppl2(inFun, x, X));
	
	right = (ATerm) ATmakeAppl2(inAbsFun, 
					(ATerm)ATmakeAppl1(H, x), 
					(ATerm) ATmakeAppl1(alpha, X));
	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
}

AFun createAbstractGamma(ATerm absSort){
	AFun gamma;
	ATbool ok;
	ATerm func, sort;	
	ATerm emptyTerm, emptyAbsTerm, X, x, newEq;
	ATerm fullTerm, fullAbsTerm;
	ATermList vars;
	AFun unionFun, inAbsFun;
	ATerm left, right;
	AFun Hinv;
	
	sort = getConcrete(absSort);
	
	gamma = createNewFuncSym(absGamma, 
			ATmakeList1(liftSort(absSort)));
	func = (ATerm)ATmakeApplList(gamma, ATmakeList1(liftSort(absSort)));
	MCRLputMap(func, liftSort(sort), &ok);
	
	Hinv = createAbstractHinv(absSort);
		
	emptyTerm = createEmptyCons(liftSort(sort));
	emptyAbsTerm = createEmptyCons(liftSort(absSort));
	 
	fullTerm = createFullCons(liftSort(sort));
	fullAbsTerm = createFullCons(liftSort(absSort));

	unionFun = createNewFuncSym(unionSym, 
					 ATmakeList2(liftSort(sort), liftSort(sort)));
	inAbsFun = createInCons(absSort, liftSort(absSort));
	
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	
	vars = ATmakeList0();
	
	left = (ATerm) ATmakeAppl1(gamma, emptyAbsTerm);
	right = emptyTerm;
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	left = (ATerm) ATmakeAppl1(gamma, fullAbsTerm);
	right = fullTerm;
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	vars = ATmakeList2(ATmake("v(<term>, <term>)", x, absSort),
					   ATmake("v(<term>, <term>)", X, liftSort(absSort)));
	
	left = (ATerm) ATmakeAppl1(gamma, (ATerm)ATmakeAppl2(inAbsFun, x, X));
	
	right = (ATerm) ATmakeAppl2(unionFun, 
					(ATerm)ATmakeAppl1(Hinv, x), 
					(ATerm) ATmakeAppl1(gamma, X));
	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
}


ATerm abstractSort(ATerm sort){
	char *name, newName[NAME_LENGTH];
	ATerm abstractedSort;
	AFun H;	
	if(isAbstracted(sort)){
		return sort;
	}	
		
	if(isLifted(sort)){
		ATerror("Lifted Sorts cannot be abstracted");
	}
	
	name = ATgetName(ATgetAFun(sort));

	appendString(absPrefix, name, newName);
	
	abstractedSort = (ATerm) ATmakeAppl0(ATmakeAFun(newName, 0, ATtrue));
	createMCRLSort(abstractedSort);	
	if(!GALOIS)
		H = createAbstractH(abstractedSort);
	createAbstractAlpha(abstractedSort, H);
	createAbstractGamma(abstractedSort);
	createIfFunc(abstractedSort);
	


	return abstractedSort;
}

ATerm liftSort(ATerm sort){
	char *name, newName[NAME_LENGTH];
	ATerm liftedSort;
	if(isLifted(sort)){
		return sort;	
	}
	name = ATgetName(ATgetAFun(sort));
	appendString(setPrefix, name, newName);
	liftedSort = (ATerm) ATmakeAppl0(ATmakeAFun(newName, 0, ATtrue));
	if(createMCRLSort(liftedSort)){
		createSetFuncs(sort, liftedSort);
	}
	return liftedSort;	
}


ATerm createEmptyCons(ATerm setSort){
	char newName[250];
	AFun newTag;
	ATbool ok;
	
	strcpy(newName, emptyPrefix);
	strcat(newName, ATgetName(ATgetAFun(setSort)));
	strcat(newName, "#");
		
	newTag = ATmakeAFun(newName, 0, ATtrue);
	MCRLputConstructor((ATerm)ATmakeAppl0(newTag), setSort, &ok);
	return (ATerm) ATmakeAppl0(newTag);
}

ATerm createFullCons(ATerm setSort){
	char newName[250];
	AFun newTag;
	ATbool ok;
	
	if(getUnLifted(setSort) == MCRLterm_bool)
		return createFullSetOfBool();
	
	strcpy(newName, fullPrefix);
	strcat(newName, ATgetName(ATgetAFun(setSort)));
	strcat(newName, "#");
		
	newTag = ATmakeAFun(newName, 0, ATtrue);
	MCRLputConstructor((ATerm)ATmakeAppl0(newTag), setSort, &ok);
	return (ATerm) ATmakeAppl0(newTag);
}

ATerm createFullSetOfBool(){
	AFun inTag = createNewFuncSym(inSym, 		
			ATmakeList2(MCRLterm_bool, liftSort(MCRLterm_bool)));
	return (ATerm) ATmakeAppl2(inTag,
			MCRLterm_true, (ATerm)ATmakeAppl2(inTag,
			MCRLterm_false, createEmptyCons(liftSort(MCRLterm_bool))));
}


AFun createInCons(ATerm sort, ATerm setSort){
	AFun newTag;
	ATbool ok;
				
	newTag = createNewFuncSym(inSym, 
					 ATmakeList2(sort, setSort));
			
	MCRLputConstructor((ATerm)ATmakeAppl2(newTag, sort, setSort), 
							setSort, &ok);
	return newTag;
}


AFun createEqFunc(ATerm sort){
	AFun newTag;
	ATbool ok;
	
	if(isAbstracted(sort)){		
		newTag = createNewFuncSym(absEqSym, 
					 ATmakeList2(sort, sort));
	}
	else{
		newTag = createNewFuncSym(eqSym, 
					 ATmakeList2(sort, sort));
	}
		

	MCRLputMap((ATerm)ATmakeAppl2(newTag, sort, sort), 
		MCRLterm_bool, &ok);


	return newTag;
}

AFun createUnionFunc(ATerm sort, ATerm setSort, ATerm emptyTerm, 
			ATerm fullTerm, AFun inFun, AFun ifFun, AFun memberFun){
	AFun newTag, newTag0, newTag1, newTag2, notTag;
	ATbool ok;
	ATerm newEq;
	ATerm x,X,y,Y;
	ATermList vars;
	ATerm left, right;
			
	
	newTag0 = createNewFuncSym(unionSym, 
					 ATmakeList2(setSort, setSort));
	newTag1 = createNewFuncSym(unionSym, 
					 ATmakeList2(sort, setSort));
	newTag2 = createNewFuncSym(unionSym, 
					 ATmakeList2(setSort, sort));

	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	y = (ATerm) ATmakeAppl0(ATmakeAFun("y", 0, ATtrue));
	Y = (ATerm) ATmakeAppl0(ATmakeAFun("Y", 0, ATtrue));
	
	MCRLputMap((ATerm)ATmakeAppl2(newTag0, setSort, setSort), 
			setSort, &ok);
	MCRLputMap((ATerm)ATmakeAppl2(newTag1, sort, setSort), 
			setSort, &ok); 
	MCRLputMap((ATerm)ATmakeAppl2(newTag2, setSort, sort), 
			setSort, &ok);
	
	vars = ATmakeList1(ATmake("v(<term>, <term>)", X, setSort)); 
				 
	left = (ATerm) ATmakeAppl2(newTag0, X, emptyTerm);
	right = X; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	left = (ATerm) ATmakeAppl2(newTag0, X, fullTerm);
	right = fullTerm; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	left = (ATerm) ATmakeAppl2(newTag0, fullTerm, X);
	right = fullTerm; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	vars = ATmakeList1(ATmake("v(<term>, <term>)", x, sort));
	 
	left = (ATerm) ATmakeAppl2(newTag0, x, fullTerm);
	right = fullTerm; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	left = (ATerm) ATmakeAppl2(newTag0, fullTerm, x);
	right = fullTerm; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	vars = ATmakeList3(ATmake("v(<term>, <term>)", y, sort),
					   ATmake("v(<term>, <term>)", X, setSort),
					   ATmake("v(<term>, <term>)", Y, setSort)); 
	left = (ATerm) ATmakeAppl2(newTag0, X, 
							(ATerm) ATmakeAppl2(inFun, y, Y));
	
	notTag = createNewFuncSym(notSym, 
					 ATmakeList1(MCRLterm_bool));
	
					 
	right = (ATerm) ATmakeAppl2(newTag0, 
					(ATerm) ATmakeAppl3(
							ifFun,
							(ATerm) ATmakeAppl1(
								notTag,
								(ATerm) ATmakeAppl2(memberFun,
										y, X)), 
							(ATerm) ATmakeAppl2(
								inFun, y, X),
							X 
							),
					Y);	
					
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	vars = ATmakeList2(ATmake("v(<term>, <term>)", y, sort),
					   ATmake("v(<term>, <term>)", X, setSort)); 
	left = (ATerm) ATmakeAppl2(newTag2, X, y);
							
	right = (ATerm) ATmakeAppl3(
						ifFun,
						(ATerm) ATmakeAppl1(
							notTag,
							(ATerm) ATmakeAppl2(memberFun, y, X)), 
							(ATerm) ATmakeAppl2(inFun, y, X),
							X 
					);
					
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	vars = ATmakeList2(ATmake("v(<term>, <term>)", x, sort),
					   ATmake("v(<term>, <term>)", Y, setSort));
	left = (ATerm) ATmakeAppl2(newTag1, x, Y);						
	right = (ATerm) ATmakeAppl3(
						ifFun,
						(ATerm) ATmakeAppl1(
							notTag,
							(ATerm) ATmakeAppl2(memberFun, x, Y)), 
							(ATerm) ATmakeAppl2(inFun, x, Y),
							Y 
					);
	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	return newTag0;	
}

AFun createIfFunc(ATerm sort){
	AFun newTag;
	ATbool ok;
	ATerm newEq;
	ATerm X,Y;
	ATermList vars;
	ATerm left, right;
	
	if(isAbstracted(sort)){
		newTag = createNewFuncSym(absIfSym, 
			ATmakeList3(MCRLterm_bool, sort, sort));
	}
	else{
		newTag = createNewFuncSym(ifSym, 
			ATmakeList3(MCRLterm_bool, sort, sort));
	}				 
	MCRLputMap((ATerm)ATmakeAppl3(newTag, MCRLterm_bool, sort, sort), 
			sort, &ok);
	
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	Y = (ATerm) ATmakeAppl0(ATmakeAFun("Y", 0, ATtrue));
	vars = ATmakeList2(ATmake("v(<term>, <term>)", X, sort), 
		   ATmake("v(<term>, <term>)", Y, sort));
	left = (ATerm) ATmakeAppl3(newTag, MCRLterm_true, X, Y);
	right = X; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	left = (ATerm) ATmakeAppl3(newTag, MCRLterm_false, X, Y);
	right = Y; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	return newTag;
}

AFun createMemberFunc(ATerm sort, ATerm setSort, AFun eqFun,
					   AFun inFun, ATerm emptyTerm, ATerm fullTerm, AFun ifFun){
	AFun newTag;
	ATbool ok;
	
	ATerm newEq;
	ATerm x,y,X;
	ATermList vars;
	ATerm left, right;
			
	newTag = createNewFuncSym(memberSym, 
					 ATmakeList2(sort, setSort));
					 
	MCRLputMap((ATerm)ATmakeAppl2(newTag, sort, setSort), 
			MCRLterm_bool, &ok);
				
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	vars = ATmakeList1(ATmake("v(<term>, <term>)", x, sort)); 
	left = (ATerm) ATmakeAppl2(newTag, x, emptyTerm);
	right = MCRLterm_false; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	 
	left = (ATerm) ATmakeAppl2(newTag, x, fullTerm);
	right = MCRLterm_true; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	y = (ATerm) ATmakeAppl0(ATmakeAFun("y", 0, ATtrue));
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	vars = ATmakeList3(ATmake("v(<term>, <term>)", x, sort),
					   ATmake("v(<term>, <term>)", y, sort),
					   ATmake("v(<term>, <term>)", X, setSort)); 
	left = (ATerm) ATmakeAppl2(newTag, x, 
							(ATerm) ATmakeAppl2(inFun, y, X));
	right = (ATerm) ATmakeAppl3(ifFun, 
					(ATerm) ATmakeAppl2(eqFun, x, y),
					MCRLterm_true,
					(ATerm) ATmakeAppl2(newTag, x, X));
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);

	MCRLputEquation(newEq, &ok);
	  
	return newTag;
}
AFun createOrderedInFunc(ATerm sort, ATerm setSort, AFun inFun, AFun ifFun,
							ATerm emptyTerm, ATerm fullTerm){
	AFun oInFun, ltTag;
	ATbool ok;
	
	ATerm newEq;
	ATerm x,y,X;
	ATermList vars;
	ATerm left, right;
			
	ltTag = createNewFuncSym(ltSym, 
					 ATmakeList2(sort, sort));
					 
	oInFun = createNewFuncSym(orderedInSym, 
					 ATmakeList2(sort, setSort));
					 
	MCRLputMap((ATerm)ATmakeAppl2(oInFun, sort, setSort), 
			setSort, &ok);
			
	ltTag = createNewFuncSym(ltSym, 
					 ATmakeList2(sort, sort));
					 
	MCRLputMap((ATerm)ATmakeAppl2(ltTag, sort, sort), 
			MCRLterm_bool, &ok);
				
								
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	
	vars = ATmakeList1(ATmake("v(<term>, <term>)", x, sort)); 
	
	left = (ATerm) ATmakeAppl2(oInFun, x, emptyTerm);
	right = (ATerm) ATmakeAppl2(inFun, x, emptyTerm); 
	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	 
	left = (ATerm) ATmakeAppl2(oInFun, x, fullTerm);
	right = fullTerm; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	y = (ATerm) ATmakeAppl0(ATmakeAFun("y", 0, ATtrue));
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	vars = ATmakeList3(ATmake("v(<term>, <term>)", x, sort),
					   ATmake("v(<term>, <term>)", y, sort),
					   ATmake("v(<term>, <term>)", X, setSort)); 
	
	left = (ATerm) ATmakeAppl2(oInFun, x, 
							(ATerm) ATmakeAppl2(inFun, y, X));
	
	right = (ATerm) ATmakeAppl3(ifFun, 
					(ATerm) ATmakeAppl2(ltTag, x, y),
					 (ATerm) ATmakeAppl2(inFun, x, 
					 	(ATerm)ATmakeAppl2(inFun, y, X)),
					(ATerm)ATmakeAppl2(inFun, y, 
						(ATerm) ATmakeAppl2(oInFun, x, X)));
						
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);

	MCRLputEquation(newEq, &ok);
	  
	return oInFun;
}



AFun createHeadFunc(ATerm sort, ATerm setSort, AFun inFun){
	AFun newTag;
	ATbool ok;
	
	ATerm newEq;
	ATerm x,y,X;
	ATermList vars;
	ATerm left, right; 
			
	newTag = createNewFuncSym(headSym, ATmakeList1(setSort));
					 
	MCRLputMap((ATerm)ATmakeAppl1(newTag, setSort), sort, &ok);
				
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	
	vars = ATmakeList2(ATmake("v(<term>, <term>)", x, sort),
					   ATmake("v(<term>, <term>)", X, setSort));
						 
	left = (ATerm) ATmakeAppl1(newTag, 
							(ATerm) ATmakeAppl2(inFun, x, X));
	right = x;
	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);

	MCRLputEquation(newEq, &ok);
	  
	return newTag;
}


AFun createSingCons(ATerm sort, ATerm setSort, 
					   ATerm emptyTerm, AFun inFun){
	AFun newTag;
	ATbool ok;
	
	ATerm newEq;
	ATerm x,y,X;
	ATermList vars;
	ATerm left, right;
	
		
	newTag = createNewFuncSym(singSym, 		
				ATmakeList1(sort));	
	MCRLputMap((ATerm)ATmakeAppl1(newTag, sort), 
			setSort, &ok);
				
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	vars = ATmakeList1(ATmake("v(<term>, <term>)", x, sort)); 

	left = (ATerm) ATmakeAppl1(newTag, x);
	right = 	(ATerm) ATmakeAppl2(inFun, x, emptyTerm);
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	 
	return newTag;
}


AFun createSubsetFunc(ATerm sort, ATerm setSort, AFun memberFun,
					   AFun inFun, ATerm emptyTerm, ATerm fullTerm, AFun ifFun){
	AFun newTag;
	ATbool ok;
	
	ATerm newEq;
	ATerm x,y,X,Y;
	ATermList vars;
	ATerm left, right;
	
	newTag = createNewFuncSym(subsetSym, 		
				ATmakeList2(setSort, setSort));
					
	MCRLputMap((ATerm)ATmakeAppl2(newTag, setSort, setSort), 
			MCRLterm_bool, &ok);				
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	vars = ATmakeList1(ATmake("v(<term>, <term>)", X, setSort)); 
	
	left = (ATerm) ATmakeAppl2(newTag, emptyTerm, X); 
	right = MCRLterm_true; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	
	MCRLputEquation(newEq, &ok);
	
	left = (ATerm) ATmakeAppl2(newTag, X, emptyTerm); 
	right = MCRLterm_false; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	
	MCRLputEquation(newEq, &ok);
	
	if(sort != MCRLterm_bool){
		left = (ATerm) ATmakeAppl2(newTag, fullTerm, X); 
		right = MCRLterm_false; 
		newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	
		MCRLputEquation(newEq, &ok);
	}
	left = (ATerm) ATmakeAppl2(newTag, X, fullTerm); 
	right = MCRLterm_true; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	
	MCRLputEquation(newEq, &ok);
	
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	Y = (ATerm) ATmakeAppl0(ATmakeAFun("Y", 0, ATtrue));
	
	vars = ATmakeList3(ATmake("v(<term>, <term>)", x, sort),
					   ATmake("v(<term>, <term>)", X, setSort),
					   ATmake("v(<term>, <term>)", Y, setSort));

	left = (ATerm) ATmakeAppl2(newTag, 
							(ATerm) ATmakeAppl2(inFun, x, X), Y);
						
	right = (ATerm) ATmakeAppl3(ifFun, 
			      (ATerm) ATmakeAppl2(memberFun, x, Y),
					(ATerm) ATmakeAppl2(newTag, X, Y), MCRLterm_false);	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	 
	
	return newTag;
}
AFun createSingletonFunc(ATerm sort, ATerm setSort, AFun eqFun,
					   AFun inFun, ATerm emptyTerm, ATerm fullTerm, AFun ifFun){
	AFun newTag;
	ATbool ok;
	
	ATerm newEq;
	ATerm x,y,X;
	ATermList vars;
	ATerm left, right;
	
	newTag = createNewFuncSym(singletonSym, 		
				ATmakeList1(setSort));
		
	MCRLputMap((ATerm)ATmakeAppl1(newTag, setSort), 
			MCRLterm_bool, &ok);
	
	vars = ATmakeList0();		
	left = (ATerm) ATmakeAppl1(newTag, emptyTerm);
	right = MCRLterm_false; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);	
	
	vars = ATmakeList0();		
	left = (ATerm) ATmakeAppl1(newTag, fullTerm);
	right = MCRLterm_false; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);	
	
	x = (ATerm) ATmakeAppl0(ATmakeAFun("x", 0, ATtrue));
	
	vars = ATmakeList1(ATmake("v(<term>, <term>)", x, sort));
	 
	left = (ATerm) ATmakeAppl1(newTag,
			 (ATerm) ATmakeAppl2(inFun, x, emptyTerm));
			 
	right = MCRLterm_true; 
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);
	
	y = (ATerm) ATmakeAppl0(ATmakeAFun("y", 0, ATtrue));
	X = (ATerm) ATmakeAppl0(ATmakeAFun("X", 0, ATtrue));
	vars = ATmakeList3(ATmake("v(<term>, <term>)", x, sort),
					   ATmake("v(<term>, <term>)", y, sort),
					   ATmake("v(<term>, <term>)", X, setSort));
						 
	left = (ATerm) ATmakeAppl1(newTag, 
						(ATerm) ATmakeAppl2(inFun, x, 
						(ATerm) ATmakeAppl2(inFun, y, X)));
	
	right = (ATerm)ATmakeAppl3(ifFun, 
					(ATerm) ATmakeAppl2(eqFun, x, y),
					(ATerm) ATmakeAppl1(newTag,  
							(ATerm) ATmakeAppl2(inFun, y, X)),
					MCRLterm_false);
	
	
	newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", vars, left, right);
	MCRLputEquation(newEq, &ok);	 
 

	return newTag;
}


void createSetFuncs(ATerm sort, ATerm setSort){
	/* Generates the auxialiry functions used to manipulate sets */
	
	ATerm emptyTerm, fullTerm;
	AFun eqFun, inFun, ifFun, singFun, inOrderedFun,
				memberFun, unionFun, singletonFun, subsetFun;
				
	eqFun = createEqFunc(sort);
	emptyTerm = createEmptyCons(setSort);
	fullTerm = createFullCons(setSort);
	
	inFun = createInCons(sort, setSort);
	
	singFun = createSingCons(sort, setSort, emptyTerm, inFun);
	
	ifFun = createNewFuncSym(ifSym, 
		ATmakeList3(MCRLterm_bool, MCRLterm_bool, 
			MCRLterm_bool));	
			
	memberFun = createMemberFunc(sort, 
			setSort, eqFun, inFun, emptyTerm, fullTerm, ifFun);
			
	createHeadFunc(sort, setSort, inFun);
	subsetFun = createSubsetFunc(sort, setSort, memberFun, inFun, 
			emptyTerm, fullTerm, ifFun);
	singletonFun = createSingletonFunc(sort, 
			setSort, eqFun, inFun, emptyTerm, fullTerm, ifFun);
	
	ifFun = createIfFunc(setSort);	
	
	if(ORDER){
		inOrderedFun = createOrderedInFunc(sort, setSort, inFun, 
			ifFun, emptyTerm, fullTerm);
		unionFun = createUnionFunc(sort, setSort, 
			emptyTerm, fullTerm, inOrderedFun, ifFun, memberFun);
	}
	else{	
		unionFun = createUnionFunc(sort, setSort, 
			emptyTerm, fullTerm, inFun, ifFun, memberFun);
	}
}


ATermList getVarSorts(ATermList vars, ATermList sorts){
	ATerm var, sort;
	ATermList varSorts = ATmakeList0();
	
	for(;!ATisEmpty(vars); sorts = ATgetNext(sorts), vars = ATgetNext(vars)){
		var = ATgetFirst(vars);
		sort = getUnLifted(ATgetFirst(sorts));
		if(hasPrefix(ATgetName(ATgetAFun(var)), "x"))
			varSorts = ATappend(varSorts, sort);
		else
			varSorts = ATappend(varSorts, liftSort(sort));
	}
	return varSorts;
}

void createNewEquations(AFun tag, ATermList sorts, int i, ATerm targetSort, 
			ATermList listLeft, ATerm right, ATermList rl1, ATermList rl2, 
			ATermList vars, ATbool done){	
	/* Generates the auxiliary functions to deal with sets of values*/
	
	ATbool ok;
	ATerm x, X;
	ATerm newEq, sort;
	ATerm left, newRight = NULL;	
	ATermList newVars = ATmakeList0();
	ATermList newListLeft = ATmakeList0();
	ATermList newRl1 = ATmakeList0();
	ATermList newRl2 = ATmakeList0();
	char varName1[10], varName2[10];
	ATerm newFunc;
	char newName[NAME_LENGTH];
	AFun unionTag, inTag;
	AFun rl1Tag, rl2Tag;
	
	if(i == ATgetLength(sorts)){
		if(done){	
			if(right == NULL){
				unionTag = ATmakeSymbol(unionSym, 2, ATtrue);
				
				rl1Tag = createNewFuncSym(ATgetName(tag), 		
				 	getVarSorts(rl1,sorts));
				rl2Tag = createNewFuncSym(ATgetName(tag), 		
				 	getVarSorts(rl2,sorts));
				
				right = (ATerm) ATmakeAppl2(unionTag,
					(ATerm) ATmakeApplList(rl1Tag, rl1),
					(ATerm) ATmakeApplList(rl2Tag, rl2));	
			}
				
			left = (ATerm) ATmakeApplList(tag, listLeft);
				newEq = ATmake("<appl(<term>,<term>,<term>)>", "e", 
					vars, left, right);
			MCRLputEquation(newEq, &ok);
		}
	}
	else{
		sprintf(varName1, "%s_%d", "x", i);
		sprintf(varName2, "%s_%d", "X", i);
		x = (ATerm) ATmakeAppl0(ATmakeAFun(varName1, 0, ATtrue));
		X = (ATerm) ATmakeAppl0(ATmakeAFun(varName2, 0, ATtrue));
		sort = ATelementAt(sorts, i);

		if(isLifted(sort)){			
			if(!done){
				done = ATtrue;
				newRight = createEmptyCons(targetSort);	
				newListLeft = ATappend(listLeft, createEmptyCons(sort));	  
				
				createNewEquations(tag, sorts, i+1, targetSort, 
					 newListLeft, newRight, rl1, rl2, vars, done);
				
				if(sort != liftSort(MCRLterm_bool)){	 
					newRight = createFullCons(targetSort);	
					newListLeft = ATappend(listLeft, createFullCons(sort));	  	
					createNewEquations(tag, sorts, i+1, targetSort, 
						 newListLeft, newRight, rl1, rl2, vars, done);
				}
				
				newVars = ATappend(vars,ATmake("v(<term>, <term>)", 
						x, getUnLifted(sort)));						
				newVars = ATappend(newVars,ATmake("v(<term>, <term>)",X, sort));
				
				inTag = createNewFuncSym(inSym, 		
						ATmakeList2(getUnLifted(sort), sort));			
				
				newListLeft = ATappend(listLeft,
					(ATerm) ATmakeAppl2(inTag, x, X));
				newRl1 = ATappend(rl1, x); 
				newRl2 = ATappend(rl2, X); 
			} 
			else{
				newVars= ATappend(vars, ATmake("v(<term>, <term>)", X, sort));
				newRl1 = ATappend(rl1, X); 
				newRl2 = ATappend(rl2, X); 
				newListLeft = ATappend(listLeft, X);		
			}
			
			createNewFunc(tag, 
					ATreplace(sorts, getUnLifted(sort), i), targetSort);
	
			createNewEquations(tag, sorts, i+1, targetSort, 
					newListLeft, right, newRl1, newRl2, newVars, done);	
		}
		else{
			newVars = ATappend(vars, ATmake("v(<term>, <term>)", x, sort));
			newListLeft = ATappend(listLeft, x);
			newRl1 = ATappend(rl1, x); 
			newRl2 = ATappend(rl2, x); 
			createNewEquations(tag, sorts, i+1, targetSort,
					 newListLeft, right, newRl1, newRl2, newVars, done);
		}
	}			
}

ATbool abstractedOrLiftedSorts(ATermList sorts){
	ATerm sort;
	if(ATisEmpty(sorts))
		return ATtrue;
	for(;!ATisEmpty(sorts); sorts = ATgetNext(sorts)){
		sort = ATgetFirst(sorts);
		if(isAbstracted(sort) || isLifted(sort))
			return ATtrue;
	}
	return ATfalse;
} 
ATbool abstractedSorts(ATermList sorts){
	ATerm sort;
	if(ATisEmpty(sorts))
		return ATfalse;
	for(;!ATisEmpty(sorts); sorts = ATgetNext(sorts)){
		sort = ATgetFirst(sorts);
		if(isAbstracted(sort))
			return ATtrue;
	}
	return ATfalse;
} 

ATerm createSingTerm(ATerm term, ATerm setSort){
		AFun singTag;
		
		singTag = createNewFuncSym(singSym,
				 ATmakeList1(getUnLifted(setSort)));
		term = (ATerm) ATmakeAppl1(singTag, term);
		return term;
}

ATerm createAlphaTerm(ATerm term, ATerm termSort){
	ATerm absSort;
	AFun alpha;
	
	absSort = liftSort(abstractSort(getUnLifted(termSort)));
		
	alpha = createNewFuncSym(absAlpha, ATmakeList1(termSort));
	return (ATerm) ATmakeAppl1(alpha, term);
}

ATerm createGammaTerm(ATerm term, ATerm termSort){
	ATerm crtSort;
	AFun gamma;
	
	crtSort = liftSort(getConcrete(getUnLifted(termSort)));
	 
	gamma = createNewFuncSym(absGamma, ATmakeList1(termSort));
	return (ATerm) ATmakeAppl1(gamma, term);
}

ATermList getFuncSortList(ATerm func){
	int i;
	char *sortName, *funcName;
	char nameAux[NAME_LENGTH];
	ATermList sorts = ATmakeList0();
	
	funcName = ATgetName(ATgetAFun(func));
	strcpy(nameAux, funcName);
	
	sortName = (char *)strtok(nameAux, "#");	
	for(i = 0; i<ATgetArity(ATgetAFun(func)); i++){
		sortName = (char *)strtok(NULL, "#");
		sorts = ATinsert(sorts, 
					(ATerm)ATmakeAppl0(ATmakeAFun(sortName, 0, ATtrue)));
	}	
	return ATreverse(sorts);
}
 
ATermList getListOfSorts(ATerm adt){
	return (ATermList) ATgetArgument(ATgetArgument(adt, 0), 0);
}

ATermList getConstructors(ATerm adt){
	return (ATermList) ATgetArgument(ATgetArgument(adt, 0), 1);
}
ATermList getFunctions(ATerm adt){
	return (ATermList) ATgetArgument(ATgetArgument(adt, 0), 2);
}
ATermList getEquations(ATerm adt){
	return (ATermList) ATgetArgument(adt, 1);
}

ATbool reservedFunc(AFun fun){
	char name[NAME_LENGTH];
	 
	getFuncName(fun, name);
	if(0 == strcmp(name, unionSym))
		return ATtrue;
	if(0 == strcmp(name, singletonSym))
		return ATtrue;
	if(0 == strcmp(name, singSym))
		return ATtrue;
	if(0 == strcmp(name, memberSym))
		return ATtrue;
	if(!strcmp(name, inSym))
		return ATtrue;
	if(0 == strcmp(name, headSym))
		return ATtrue;
	if(0 == strcmp(name, absH))
		return ATtrue;	
	if(0 == strcmp(name, absHinv))
		return ATtrue;	
	if(0 == strcmp(name, absAlpha))
		return ATtrue;	
	if(0 == strcmp(name, absGamma))
		return ATtrue;	
	return ATfalse;
}


AFun createNewFunc(AFun fun, ATermList argSorts, ATerm fSort){
	ATbool ok;
	char sym[NAME_LENGTH];
	
	if(!abstractedOrLiftedSorts(argSorts))
		return fun;
	
	fun = createNewFuncSym(ATgetName(fun), argSorts);
	
	MCRLputMap((ATerm)ATmakeApplList(fun, argSorts), fSort, &ok);
	if(ok){
		strcpy(sym, ATgetName(fun));
		/*fprintf(stderr, "New Function %s --> %s\n", sym,
			 ATwriteToString(fSort));*/
		createNewEquations(fun, argSorts, 0, fSort, ATmakeList0(), NULL,
			ATmakeList0(), ATmakeList0(), ATmakeList0(), ATfalse);
	}
	return fun;
}

ATerm createNewFuncTerm(ATerm func, ATermList argSorts, ATerm fSort){
	ATermList args;
	AFun tag;
	
	tag = createNewFunc(ATgetAFun(func), argSorts, fSort);
	args = ATgetArguments((ATermAppl) func);
		
	func = (ATerm) ATmakeApplList(tag, args);
	
	return func;
}


AFun createNewFuncSym (char *funcName, ATermList sorts){
	/* Gets the function Name a the list of sorts 
			and generates the Function Symbol */

	char newName[NAME_LENGTH], nameAux[NAME_LENGTH];
	int nSorts = ATgetLength(sorts);
	char *sortName, *name;
	ATerm sort;
	AFun tag;
	ATbool ok;
	
	strcpy(nameAux, funcName);
	
	name = (char *)strtok(nameAux, "#");
	strcpy(newName, name);
	strcat(newName, "#");
	
	for(;!ATisEmpty(sorts); sorts = ATgetNext(sorts)){
		sort = ATgetFirst(sorts);
		strcat(newName, ATgetName(ATgetAFun(sort)));
		if(ATgetLength(sorts) > 1)
			strcat(newName, "#");
	}	
	tag = ATmakeSymbol(newName, nSorts, ATtrue);
	
	return tag;
}


void getFuncName(AFun fun, char *sym){
	/* Returns the function symbol: "add#Nat#Nat" -> "add" */
		
	char nameAux[NAME_LENGTH], *name;
	name = ATgetName(fun);	
	strcpy(nameAux, name);
	name = (char *)strtok(nameAux, "#");
	strcpy(sym, name);
}
