#define  NAME      "libmcparse"
#define  LVERSION   "0.3.6"
#define  AUTHOR    "Aad Mathijssen"

#ifdef __cplusplus
extern "C" {
#endif

#include <errno.h>
#include <string.h>
#include <stdlib.h>

#ifdef __cplusplus
}
#endif

#include "config.h"
#include "mcrl.h"
#include "libmcparse.h"

//global declarations
bool MCdebug = false;	                 /* print debug information, if true */

//external declarations
extern ATermAppl MCparse(FILE *formfile);/* declared in lexer.l */

//local declarations

bool hasFPQVarNameConflicts(ATermAppl form);
//Pre: form is a modal formula
//Ret: form contains a fixed point quantification with conflicting quantified
//     variable names
//Post:if true is returned, then an error message is printed on stderr for
//     quantification that has a conflict

int dangerousFPNestings(ATermAppl form);
//Pre: form is a modal formula that adheres to the variable convention
//Ret: the number of dangerous fixed point variable nestings in form

int dangerousFPNestingsContext(ATermAppl form, ATermList fpVarSorts);
//Pre: form is a modal formula that adheres to the variable convention
//     fpVarSorts is a list of pairs [fpVar, sorts], where:
//     - fpVar is a fixed point variable
//     - sorts is a list of sorts
//Ret: the number of dangerous fixed point variable nestings in form under
//     context fpVarSorts

bool checkMonotonicity(ATermAppl form);
//Pre: form is a modal formula that adheres to the variable convention
//Ret: form is monotonic

bool checkMonotonicityContext(ATermAppl form, ATermList fpVarNegs);
//Pre: form is a modal formula that adheres to the variable convention
//     fpVarNegs is a list of pairs [fpVar, neg], where:
//     - fpVar is a pair of a the name of the fixed point variable and its
//       number of arguments
//     - neg represents the number of negations in the context of the variable
//Ret: form is monotonic based on fpVarNegs

bool isReduced(ATermAppl form);
//Pre: form is a modal formula that adheres to the variable convention
//Ret: form is reduced

ATermAppl reduceFormula(ATermAppl form);
//Pre: form is a modal formula that adheres to the variable convention
//Ret: form in which each regular operation is replaced by an equivalent
//     non-regular operation

ATermAppl alphaConvert(ATermAppl form, bool full);
//Pre: form is a modal, regular or action formula that adheres to the variable
//     convention
//Ret: form in which bound variables are renamed such that:
//     if full, all names are distinct
//     otherwise, all names that are in each other's scope are distinct

ATermAppl alphaConvertContext(ATermAppl form, bool full, ATermList vars);
//Pre: form is a modal, regular or action formula that adheres to the variable
//     convention
//     vars is a list of variable names
//Ret: form in which bound variables are renamed such that all names are
//     different from vars and:
//     if full, all names are distinct
//     otherwise, all names that are in each other's scope are distinct

ATermAppl translateToMCRLFormat(ATermAppl form);
//Pre: the mCRL library is initialised
//     form is a modal, regular or action formula that adheres to the variable
//     convention
//Ret: a translation of term to the internal mCRL format using the data
//     specification that is available in the library, if everything went ok;
//     if something went wrong, NULL is returned and an error message is
//     displayed

ATermAppl translateToMCRLFormatContext(ATermAppl form);
//Pre: the mCRL library is initialised
//     form is a modal, regular or action formula that adheres to the variable
//     convention
//     all occurrences of variables in the context are declared in the mCRL
//     library
//Post:all quantified variables that occur in the result are declared
//Ret: a translation of term to the internal mCRL format using the data
//     specification that is available in the library, if everything went ok;
//     if something went wrong, NULL is returned and an error message is
//     displayed

ATermList getVariableNames(ATermAppl form);
//Pre: form is a modal, regular or action formula
//Ret: a list of ATerms that represent all variable names

ATermAppl renameVar(ATermAppl var, ATermAppl subst, int nArg, ATermAppl term);
//Pre: var and subst are variables, nArg >= 0
//     term is an arbitrary term according to the syntax of modal formulas
//     if term is quoted, it is not an action
//Ret: term in which all free occurrences of var with nArg arguments are
//     renamed to subst

bool occursVar(ATermAppl var, int nArg, ATermAppl term);
//Pre: var is a variable, nArg >= 0
//     term is an arbitrary term according to the syntax of modal formulas
//     if term is quoted, it is not an action
//Ret: var with nArg parameters occurs free in term

ATermAppl createFreshVar(bool cap, ATermList vars);
//Pre: vars is a list of variables, nArg >= 0
//     terms is a list of arbitrary terms that adhere to the syntax of modal
//     formulas; if such a term is quoted, it is not an action
//Ret: a variable that is different from any variable in vars
//     if cap, x is capitalised

ATermAppl createFreshVarNOcc(
  bool cap, ATermList vars, int nArg, ATermAppl term);
//Pre: vars is a list of variables, nArg >= 0
//     terms is a list of arbitrary terms that adhere to the syntax of modal
//     formulas; if such a term is quoted, it is not an action
//Ret: a variable x that satisfies the following conditions:
//     - each variable in vars is different from x
//     - x with nArg arguments does not occur free in term
//     if cap, x is capitalised

ATermAppl createFreshVarNOccs(
  bool cap, ATermList vars, int nArg, ATermList terms);
//Pre: vars is a list of variables, nArg >= 0
//     terms is a list of arbitrary terms that adhere to the syntax of modal
//     formulas; if such a term is quoted, it is not an action
//Ret: a variable x that satisfies the following conditions:
//     - each variable in vars is different from x
//     - x with nArg arguments does not occur free in any of the terms in terms
//     if cap, x is capitalised

ATermAppl createNewVar(bool cap, int index);
//Pre: index >= 0
//Ret: a variable whose name is uniquely determined by the value of index
//     if cap, name is capitalised

ATermList removeFPVar(ATermList fpVar, ATermList fpVarNegs);
//Pre: fpVar is a fixed point variable
//     fpVarNegs is a list of pairs [fpVar', neg], where:
//     - fpVar' is a fixed point variable
//     - neg indicates if the variable is in the context of an even number of
//       negations
//     - all fpVar''s are distinct
//Ret: fpVarNegs in which fpVar is removed, if it occurred in it

ATermList incNeg(ATermList fpVarNegs);
//Pre: fpVarNegs is a list of pairs [fpVar, neg], where:
//     - fpVar is a fixed point variable
//     - neg indicates if the variable is in the context of an even number of
//       negations
//     - all fpVar's are distinct
//Ret: fpVarNegs in which all neg's are incremented

bool evenNeg(ATermList fpVar, ATermList fpVarNegs);
//Pre: fpVar is a fixed point variable
//     fpVarNegs is a list of pairs [fpVar', neg], where:
//     - fpVar' is a fixed point variable
//     - neg indicates if the variable is in the context of an even number of
//       negations
//     - all fpVar''s are distinct
//Ret: The value of neg corresponding to variable fpVar in fpVarNegs is even

//implementation

ATermAppl MCparseModalFormula (FILE *formStream, bool reduce,
  int acLevel, int vbLevel, bool saveToMCRLFormat)
{
  ATermAppl result = NULL;
  //check preconditions
  if (acLevel < 0 || acLevel > 2) {
    throwVM0(NULL, "error: illegal value for the level of alpha conversion\n");
  }
  if (vbLevel < 0 || vbLevel > 3) {
    throwVM0(NULL, "error: illegal value for the level of verbosity\n");
  }
  if (formStream == NULL) {
    throwVM0(NULL, "error: formula stream may not be empty\n");
  }
  //set global debug flag
  MCdebug = (vbLevel == 3);
  //parse formula using lex and yacc
  if (vbLevel > 1) {
    printf("parsing formula from stream\n");
  }
  result = MCparse(formStream);
  if (result == NULL) {
    throwM0("error: parsing failed\n");
  }
  //check for fixed point quantifier variable name conflicts
  if (vbLevel > 1) {
    printf(
      "checking for variable name conflicts of fixed point quantifications\n");
  }
  if (hasFPQVarNameConflicts(result)) {
    throwV(NULL);
  }
  //check for dangerous nestings of fixed point variables
  if (vbLevel > 0) {
    if (vbLevel > 1) {
      printf("checking for dangerous nestings of fixed point variables\n");    
    }
    int n = dangerousFPNestings(result);
    if (n > 0 && vbLevel > 0) {  
      printf(
        "warning: formula contains %d dangerous nesting%s of fixed point "
        "variables (see documentation for details)\n", n, n!=1?"s":"");
    }
  }
  //check monotonicity
  if (vbLevel > 1) {
    printf("checking monotonicity of formula\n");
  }
  if (!checkMonotonicity(result)) {
    throwVM0(NULL, "error: formula is not monotonic\n");
  }
  //reduce formula if reduce is true
  if (reduce) {
    if (isReduced(result)) {
      if (vbLevel > 1) {
        printf("formula doesn't need to be reduced\n");        
      }
    } else {
      if (vbLevel > 1) {
        printf("reducing formula\n");
      }
      result = reduceFormula(result);
    }
  }
  //perform alpha conversion
  if (acLevel > 0) {
    if (vbLevel > 1) {
      printf("performing %s alpha conversion\n", (acLevel == 2)?"full":"scope");
    }
    result = alphaConvert(result, acLevel == 2);
  }
  //translate formula to the mCRL format
  if (saveToMCRLFormat) {
    if (vbLevel > 1) {
      printf(
        "translating formula to the internal mCRL format\n"
      );
    }
    result = translateToMCRLFormat(result);
    if (result == NULL) {
      throwM0("error: translation to the internal mCRL format failed\n");
    }
  }
finally:
  if (MCdebug) {
    if (result != NULL) {
      ATprintf("(MCparseModalFormula): return %t\n", result);
    } else {
      ATprintf("(MCparseModalFormula): return NULL\n");
    }
  }
  return result;
}

ATermAppl reduceFormula(ATermAppl form)
{
  ATermAppl result = NULL;
  if (MCdebug) {
    ATprintf("reducing formula\n  %t\n", form);
  }
  AFun formHead = ATgetAFun(form);
  char *formName = ATgetName(formHead);
  if (MCisForm(formName)) {
    //formHead is a formula; return form
    result = form;
  } else if (MCisT(formName) || MCisF(formName)) {
    //formHead is true or false; return form
    result = form;
  } else if (MCisNot(formName)) {
    //formHead is a negation; reduce its argument
    result = ATmakeAppl1(formHead, 
      (ATerm) reduceFormula(ATAgetArgument(form, 0)));
  } else if (MCisAnd(formName) || MCisOr(formName) 
      || MCisImp(formName) || MCisEq(formName)) {
    //formHead is a boolean binary operator; reduce both arguments
    result = ATmakeAppl2(formHead, 
      (ATerm) reduceFormula(ATAgetArgument(form,0)),
      (ATerm) reduceFormula(ATAgetArgument(form,1)));
  } else if (MCisForall(formName) || MCisExists(formName)) {
    //formHead is a boolean quantifier; reduce the body of the quantification
    result = ATsetArgument(
      form, (ATerm) reduceFormula(ATAgetArgument(form,2)), 2);
  } else if (MCisMay(formName)) {
    //formHead is the may operator; return equivalent non-regular formula
    ATermAppl regFrm = ATAgetArgument(form, 0);
    ATermAppl phi = ATAgetArgument(form, 1);
    char *regFrmName = ATgetName(ATgetAFun(regFrm));
    if (MCisNil(regFrmName)) {
      //may(nil,phi) -> may(tr_close(F),phi)
      result = reduceFormula(MCmakeMay(MCmakeTrClose(MCmakeF()), phi));
    } else if (MCisConcat(regFrmName)) {
      ATermAppl R1 = ATAgetArgument(regFrm, 0);
      ATermAppl R2 = ATAgetArgument(regFrm, 1);
      //may(concat(R1,R2),phi) -> may(R1,may(R2,phi))
      result = reduceFormula(MCmakeMay(R1, MCmakeMay(R2, phi)));
    } else if (MCisChoice(regFrmName)) {
      ATermAppl R1 = ATAgetArgument(regFrm, 0);
      ATermAppl R2 = ATAgetArgument(regFrm, 1);
      //may(choice(R1,R2),phi) -> or(may(R1,phi),may(R2,phi))
      result = reduceFormula(MCmakeOr(MCmakeMay(R1,phi),MCmakeMay(R2,phi)));
    } else if (MCisTrClose(regFrmName)) {
      ATermAppl R = ATAgetArgument(regFrm, 0);
      //may(tr_close(R),phi) -> mu(X,[],or(phi,may(R,X)),[]),
      //where X does not occur free in phi or R
      ATermAppl X = createFreshVarNOccs(
        true, ATmakeList0(), 0, ATmakeList2((ATerm) phi, (ATerm) R));
      result = reduceFormula(MCmakeMu(X, ATmakeList0(), 
        MCmakeOr(phi,MCmakeMay(R,MCmakeRec(X))), ATmakeList0()));
    } else if (MCisTClose(regFrmName)) {
      ATermAppl R = ATAgetArgument(regFrm, 0);
      //may(t_close(R),phi) -> may(concat(R,tr_close(R)),phi)
      result = reduceFormula(MCmakeMay(MCmakeConcat(R,MCmakeTrClose(R)),phi));
    } else {
      //regFrm is an action formula; reduce phi
      result = ATsetArgument(form, (ATerm) reduceFormula(phi), 1);
    }
  } else if (MCisMust(formName)) {
    //formHead is the must operator; return equivalent non-regular formula
    ATermAppl regFrm = ATAgetArgument(form, 0);
    ATermAppl phi = ATAgetArgument(form, 1);
    char *regFrmName = ATgetName(ATgetAFun(regFrm));
    if (MCisNil(regFrmName)) {
      //must(nil,phi) -> must(tr_close(F),phi)
      result = reduceFormula(MCmakeMust(MCmakeTrClose(MCmakeF()), phi));
    } else if (MCisConcat(regFrmName)) {
      ATermAppl R1 = ATAgetArgument(regFrm, 0);
      ATermAppl R2 = ATAgetArgument(regFrm, 1);
      //must(concat(R1,R2),phi) -> must(R1,must(R2,phi))
      result = reduceFormula(MCmakeMust(R1, MCmakeMust(R2, phi)));
    } else if (MCisChoice(regFrmName)) {
      ATermAppl R1 = ATAgetArgument(regFrm, 0);
      ATermAppl R2 = ATAgetArgument(regFrm, 1);
      //must(choice(R1,R2),phi) -> and(must(R1,phi),must(R2,phi))
      result = reduceFormula(MCmakeAnd(MCmakeMust(R1,phi),MCmakeMust(R2,phi)));
    } else if (MCisTrClose(regFrmName)) {
      ATermAppl R = ATAgetArgument(regFrm, 0);
      //must(tr_close(R),phi) -> nu(X,[],and(phi,must(R,X)),[]),
      //where X does not occur free in phi and R
      ATermAppl X = createFreshVarNOccs(
        true, ATmakeList0(), 0, ATmakeList2((ATerm) phi, (ATerm) R));
      result = reduceFormula(MCmakeNu(X, ATmakeList0(), 
        MCmakeAnd(phi,MCmakeMust(R,MCmakeRec(X))), ATmakeList0()));
    } else if (MCisTClose(regFrmName)) {
      ATermAppl R = ATAgetArgument(regFrm, 0);
      //must(t_close(R),phi) -> must(concat(R,tr_close(R)),phi)
      result = reduceFormula(MCmakeMust(MCmakeConcat(R,MCmakeTrClose(R)),phi));
    } else {
      //regFrm is an action formula; reduce phi
      result = ATsetArgument(form, (ATerm) reduceFormula(phi), 1);
    }
  } else if (MCisLoop(formName)) {   
    //formHead is the loop operator; return equivalent non-regular formula
    ATermAppl R = ATAgetArgument(form, 0);
    //loop(R) -> nu(X,[],may(R,X),[]),
    //where X does not occur free in R
    ATermAppl X = createFreshVarNOcc(true, ATmakeList0(), 0, R);
    result = reduceFormula(
      MCmakeNu(X, ATmakeList0(), MCmakeMay(R,MCmakeRec(X)), ATmakeList0()));
  } else if (MCisRec(formName)) {
    //formHead is a fixed point variable occurrence; return form
    result = form;
  } else if (MCisMu(formName) || MCisNu(formName)) {
    //formHead is a fixed point quantification; reduce the body of the
    //quantification
    result = ATsetArgument(form, 
      (ATerm) reduceFormula(ATAgetArgument(form, 2)), 2);
  }
finally:
  if (MCdebug) {
    ATprintf("(reduceFormula): reduced formula\n  %t\nto\n  %t\n", 
      form, result);
  }
  return result;  
}

bool isReduced(ATermAppl form)
{
  bool result = false;
  char *name = ATgetName(ATgetAFun(form));
  if (MCisForm(name)) {
    //head is a formula; return true
    result = true;
  } else if (MCisT(name) || MCisF(name)) {
    //head is a true or false; return true
    result = true;
  } else if (MCisNot(name)) {
    //head is a negation; check its first argument
    result = isReduced(ATAgetArgument(form, 0));
  } else if (MCisAnd(name) || MCisOr(name) || MCisImp(name) || MCisEq(name)) {
    //head is a boolean binary operator; check its first and second argument
    result = 
      isReduced(ATAgetArgument(form,0)) && isReduced(ATAgetArgument(form,1));
  } else if (MCisForall(name) || MCisExists(name)) {
    //head is a boolean quantifier; check its third argument
    result = isReduced(ATAgetArgument(form, 2));
  } else if (MCisMay(name) || MCisMust(name)) {
    //head is a may or must operator; return false if the head of the first
    //argument is "nil", "concat", "choice", "tr_close" or "t_close", check the
    //second argument, otherwise
    char *regName = ATgetName(ATgetAFun(ATAgetArgument(form, 0)));
    if (MCisNil(regName) || MCisConcat(regName) || MCisChoice(regName) ||
      MCisTrClose(regName) || MCisTClose(regName))
    {
      result = false;
    } else {
      result = isReduced(ATAgetArgument(form, 1));
    }
  } else if (MCisLoop(name)) {   
    //head is the loop operator; return false
    result = false;
  } else if (MCisRec(name)) {
    //head is a fixed point variable occurrence; return true
    result = true;
  } else if (MCisMu(name) || MCisNu(name)) {
    //head is a fixed point quantifier; check its third argument
    result = isReduced(ATAgetArgument(form, 2));
  }
finally:
  if (MCdebug) {
    ATprintf("(isReduced): return %s for formula\n  %t\n", 
      result?"true":"false", form);
  }
  return result;  
}

ATermAppl alphaConvert(ATermAppl form, bool full) {
  ATermAppl result = NULL;
  if (MCdebug) {
    ATprintf("performing %s alpha conversion on formula\n  %t\n",
    full?"full":"scope", form);
  }
  result = alphaConvertContext(form, full, ATmakeList0());
finally:
  if (MCdebug) {
    ATprintf("(alphaConvert): return\n  %t for formula\n  %t\n", 
      result, form);
  }
  return result;  
}

ATermAppl alphaConvertContext(ATermAppl form, bool full, ATermList vars) {
  ATermAppl result = NULL;
  if (MCdebug) {
    ATprintf(
      "performing %s alpha conversion on formula\n  %t,\n  "
      "under context %t\n", full?"full":"scope", form, vars);
  }
  AFun formHead = ATgetAFun(form);
  char *formName = ATgetName(formHead);
  if (MCisForm(formName) || MCisAct(formName) || MCisRec(formName)) {
    //formHead is an indicator of an mCRL formula, an action or a fixed point
    //variable occurrence; return form
    result = form;
  } else if (MCisForall(formName) || MCisExists(formName)) {
    //formHead is a boolean quantifier; if the quantified variable occurs
    //in vars, replace it by a fresh one; after that, apply alpha conversion
    //on the body of the quantification, where vars is extended with the
    //quantified variable
    result = form;
    ATermAppl qVar = ATAgetArgument(form, 0);
    ATermAppl body = ATAgetArgument(form, 2);
    if (ATindexOf(vars, (ATerm) qVar, 0) >= 0) {
      //qVar occurs in vars; replace it by a fresh one
      ATermAppl qVarNew = createFreshVar(false, vars);
      body = renameVar(qVar, qVarNew, 0, body);
      qVar = qVarNew;
      result = ATsetArgument(result, (ATerm) qVar, 0);
    }
    //apply alpha conversion on the body of the quantification
    body = alphaConvertContext(body, full, ATinsert(vars, (ATerm) qVar));
    result = ATsetArgument(result, (ATerm) body, 2);
  } else if (MCisMu(formName) || MCisNu(formName)) {
    //formHead is a fixed point quantifier; if a quantified variable occurs
    //in vars, replace it by a fresh one; after that, apply alpha conversion
    //on the body of the quantification, where vars is extended with the
    //quantified variables
    result = form;
    ATermAppl fpVar = ATAgetArgument(form, 0);
    ATermList vds = ATLgetArgument(form, 1);
    ATermAppl body = ATAgetArgument(form, 2);
    int fpNArg = ATgetLength(vds);
    ATermList newVars = vars;
    //check if the fixed point variable occurs in vars
    if (ATindexOf(newVars, (ATerm) fpVar, 0) >= 0) {
      //fpVar occurs in vars; replace it by a fresh one
      ATermAppl fpVarNew = createFreshVar(true, newVars);
      body = renameVar(fpVar, fpVarNew, fpNArg, body);
      result = ATsetArgument(result, (ATerm) fpVarNew, 0);
      newVars = ATinsert(newVars, (ATerm) fpVarNew);
    } else {
      //fpVar does not occur in vars
      newVars = ATinsert(newVars, (ATerm) fpVar);
    }
    //check if a variable of the variable declarations occurs in vars
    for (int i = 0; i < fpNArg; i++) {
      //check if the i'th variable in the variable declarations occurs in vars
      ATermAppl vd = ATAelementAt(vds, i);
      ATermAppl qVar = ATAgetArgument(vd, 0);
      if (ATindexOf(newVars, (ATerm) qVar, 0) >= 0) {
        //qVar occurs in newVars; replace it by a fresh one
        ATermAppl qVarNew = createFreshVar(true, newVars);
        body = renameVar(qVar, qVarNew, 0, body);
        vd = ATsetArgument(vd, (ATerm) qVarNew, 0);
        vds = ATreplace(vds, (ATerm) vd, i);
        result = ATsetArgument(result, (ATerm) vds, 1);
        newVars = ATinsert(newVars, (ATerm) qVarNew);
      } else {
        //qVar does not occur in newVars
        newVars = ATinsert(newVars, (ATerm) qVar);
      }
    }
    //apply alpha conversion on the body of the quantification
    body = alphaConvertContext(body, full, newVars);
    result = ATsetArgument(result, (ATerm) body, 2);
  } else {
    //formHead is something else; apply alpha conversion on the arguments
    int formArity = ATgetArity(formHead);
    if (formArity == 0) {
      result = form;
    } else if (formArity == 1) {
      ATermAppl arg = alphaConvertContext(ATAgetArgument(form, 0), full, vars);
      result = ATmakeAppl1(formHead, (ATerm) arg);
    } else if (formArity == 2) {
      //apply alpha conversion on the first argument
      ATermAppl arg0 = alphaConvertContext(ATAgetArgument(form, 0), full, vars);
      //apply alpha conversion on the second argument, where the vars is
      //extended with the variables from arg0 if full is true
      ATermList newVars = vars;
      if (full) {
        newVars = ATconcat(newVars, getVariableNames(arg0));
      }
      ATermAppl arg1 = 
        alphaConvertContext(ATAgetArgument(form, 1), full, newVars);
      result = ATmakeAppl2(formHead, (ATerm) arg0, (ATerm) arg1);
    } else {
      throwVM1(
        NULL, 
        "error in alphaConvertContext: "
        "arity of formula %s is greater than 2\n", 
        ATwriteToString((ATerm) form));
    }
  }
finally:
  if (MCdebug) {
    ATprintf(
      "(alphaConvertContext): return\n  %t for formula\n  %t,\n  "
      "and context %t\n", result, form, vars);
  }
  return result;  
}

ATermAppl translateToMCRLFormat(ATermAppl form) {
  ATermAppl result = NULL;
  //check if the mCRL library is initialised
  if (!MCRLisInitialized()) {
    throwVM0(NULL, "error: the mCRL library has not been initialised\n");
  }  
  //translate form to the mCRL format
  result = translateToMCRLFormatContext(form);
  if (result == NULL) { throwV(NULL); }
  //remove all variables that are declared by the previous function call
  MCRLundeclareVarNames(getVariableNames(result));
finally:
  if (MCdebug) {
    if (result != NULL) {
      ATprintf("(translateToMCRLFormat): return\n  %t\n for form\n  %t\n",
        result, form);
    } else {
      ATprintf("(translateToMCRLFormat): return NULL for form\n  %t\n", form);
    }
  }
  return result;  
}

ATermAppl translateToMCRLFormatContext(ATermAppl form) {
  ATermAppl result = NULL;
  if (MCdebug) {
    ATprintf(
      "translating the following formula to the internal format:\n  %t\n", form);
  }
  AFun formHead = ATgetAFun(form);
  char *formName = ATgetName(formHead);
  if (MCisForm(formName)) {
    //formHead is a formula indicator;
    //translate the formula and check if it is of type Bool
    ATerm arg = MCRLtranslate(ATgetArgument(form, 0));
    if (arg == NULL) { throwVM0(NULL, "\n"); }
    AFun argSort = MCRLgetSort(arg);
    if (argSort == 0) { throwV(NULL); }
    if (argSort != ATgetAFun(MCRLterm_bool)) {
      ATfprintf(stderr, "error: formula %t is of type %a\n", 
        ATgetArgument(form, 0), argSort);
      throwV(NULL);
    }
    result = ATmakeAppl1(formHead, arg);
  } else if (MCisRec(formName)) {
    //formHead is a fixed point variable occurrence indicator;
    //translate this occurrence
    ATerm arg = MCRLtranslate(ATgetArgument(form, 0));
    if (arg == NULL) { throwVM0(NULL, "\n"); }
    //make sure the occurrence does not have a return sort
    AFun argSort = MCRLgetSort(arg);
    if (argSort != 0) {
      ATfprintf(stderr, 
        "error: fixed point variable occurrence has return sort %a\n", argSort);
      throwV(NULL);        
    }
    //make sure the occurrence is a variable
    if (MCRLgetTypeTerm(arg) != MCRLvariable) {
      throwVM0(NULL, 
        "error: fixed point variable occurrence is not a variable\n");
    }    
    result = ATmakeAppl1(formHead, arg);
  } else if (MCisAct(formName)) {
    //formHead is an action indicator; translate the arguments of the action
    ATermAppl act = ATAgetArgument(form, 0);
    AFun actHead = ATgetAFun(act);
    int actArity = ATgetArity(actHead);
    if (actArity == 0) {
      result = form;
    } else {
      //actArity > 0
      DECLA(ATerm, actArgs, actArity);
      for (int i = 0; i < actArity; i++) {
        actArgs[i] = (ATerm) MCRLtranslate(ATgetArgument(act, i));
        if (actArgs[i] == NULL) { throwV(NULL); }
      }
      result = ATmakeAppl1(
        formHead, (ATerm) ATmakeApplArray(actHead, actArgs));
    }
  } else if (MCisForall(formName) || MCisExists(formName)) {
    //formHead is a boolean quantifier; translate the quantified variable and
    //the body of the quantification
    ATermAppl qVar  = ATAgetArgument(form, 0);
    ATerm     qSort = ATgetArgument(form, 1);
    ATermAppl body  = ATAgetArgument(form, 2);    
    //make new unique variable in the mCRL format
    ATerm qVarNewInt =
      MCRLuniqueTerm(ATgetName(ATgetAFun(qVar)), ATmakeList0());
    //translate it back from the mCRL format to a new variable
    ATermAppl qVarNew = ATmakeAppl0(
      ATmakeAFun(MCRLgetName(qVarNewInt), 0, ATtrue));
    //compare the new variable to the old one
    if (!ATisEqual(qVar, qVarNew)) {
      //the variables are different; rename all free occurrences of the old
      //one to the new one in the body of the quantification
      body = renameVar(qVar, qVarNew, 0, body);
    }
    //declare the new internal variable
    MCRLdeclareVar((ATerm) ATmakeAppl2(MCRLsym_v, qVarNewInt, qSort));
    //translate the body
    body = translateToMCRLFormatContext(body);
    if (body == NULL) { throwV(NULL); }
    //save the quantification
    result = ATmakeAppl3(formHead, qVarNewInt, qSort, (ATerm) body);
  } else if (MCisMu(formName) || MCisNu(formName)) {
    //formHead is a fixed point quantifier;
    //translate the variable initialisations, the quantified variables and
    //the body
    ATermAppl fpVar  = ATAgetArgument(form, 0);
    ATermList vds    = ATLgetArgument(form, 1);
    ATermAppl body   = ATAgetArgument(form, 2);
    ATermList vis    = ATLgetArgument(form, 3);
    int fpNArg       = ATgetLength(vds);
    //translate each of the variable initialisations
    for (int i = 0; i < fpNArg; i++) {
      //translate the i'th variable initialisation
      ATerm vi = MCRLtranslate(ATelementAt(vis, i));
      if (vi == NULL) { throwVM0(NULL, "\n"); }
      //check if the declared sort and the derived sort are equal
      AFun viSort = MCRLgetSort(vi);
      AFun qSort  = ATgetAFun(ATgetArgument(ATAelementAt(vds, i), 1));
      if (viSort != qSort) {
        ATfprintf(stderr, 
          "term %t has sort %a, but it is declared as having sort %a\n",
          ATelementAt(vis, i), viSort, qSort);
        throwV(NULL);
      }
      //save the result
      vis = ATreplace(vis, vi, i);
    }
    //translate the quantified variables
    for (int i = 0; i < fpNArg; i++) {
      //translate the i'th quantified variable
      ATermAppl vd     = ATAelementAt(vds, i);
      ATermAppl qVar   = ATAgetArgument(vd, 0);
      ATerm qSort      = ATgetArgument(vd, 1);
      //make new unique variable in the mCRL format
      ATerm qVarNewInt =
        MCRLuniqueTerm(ATgetName(ATgetAFun(qVar)), ATmakeList0());
      //translate it back from the mCRL format to a new variable
      ATermAppl qVarNew = ATmakeAppl0(
        ATmakeAFun(MCRLgetName(qVarNewInt), 0, ATtrue));
      //compare the new variable to the old one
      if (!ATisEqual(qVar, qVarNew)) {
        //the variables are different; rename all free occurrences of the old
        //one to the new one in the body of the quantification
        body = renameVar(qVar, qVarNew, 0, body);
      }
      //save the new internal variable
      vd = ATsetArgument(vd, qVarNewInt, 0);
      vds = ATreplace(vds, (ATerm) vd, i);
      //declare the new internal variable
      MCRLdeclareVar((ATerm) ATmakeAppl2(MCRLsym_v, qVarNewInt, qSort));
    }
    //translate the fixed point variable
    ATermList fpSorts = ATmakeList0();
    for (int i = 0; i < fpNArg; i++) {
      fpSorts = ATinsert(fpSorts, ATgetArgument(ATAelementAt(vds, i), 1));      
    }
    ATerm fpVarNewInt =
      MCRLuniqueTerm(ATgetName(ATgetAFun(fpVar)), fpSorts);
    ATermAppl fpVarNew = ATmakeAppl0(
      ATmakeAFun(MCRLgetName(fpVarNewInt), 0, ATtrue));
    //compare the new variable to the old one
    if (!ATisEqual(fpVar, fpVarNew)) {
      //the variables are different; rename all free occurrences of the old
      //one to the new one in the body of the quantification
      body = renameVar(fpVar, fpVarNew, fpNArg, body);
    }
    //declare the new internal variable
    MCRLdeclareVarName(fpVarNewInt);
    //translate the body
    body = translateToMCRLFormatContext(body);
    if (body == NULL) { throwV(NULL); }
    //save the fixed point quantification
    result = ATmakeAppl4(
      formHead, fpVarNewInt, (ATerm) vds, (ATerm) body, (ATerm) vis);
  } else {
    //formHead is something else; translate the arguments to the mCRL format
    int formArity = ATgetArity(formHead);
    if (formArity == 0) {
      result = form;
    } else {
      DECLA(ATerm, formArgs, formArity);
      for (int i = 0; i < formArity; i++) {
        formArgs[i] = 
          (ATerm) translateToMCRLFormatContext(ATAgetArgument(form, i));
        if (formArgs[i] == NULL) { throwV(NULL); }
      }
      result = ATmakeApplArray(formHead, formArgs);
    }    
  }
finally:
  if (MCdebug) {
    if (result != NULL) {
      ATprintf(
        "(translateToMCRLFormatContext): return\n  %t\n for form\n  %t\n",
        result, form);
    } else {
      ATprintf("(translateToMCRLFormatContext): return NULL for form\n  %t\n", form);
    }
  }
  return result;  
}

ATermList getVariableNames(ATermAppl form) {
  ATermList result = NULL;
  AFun formHead = ATgetAFun(form);
  char *formName = ATgetName(formHead);
  if (MCisForm(formName) || MCisRec(formName) || MCisAct(formName)) {
    //formHead is the indicator of a formula, a fixed point variable occurrence
    //or an action; return the empty list
    result = ATmakeList0();
  } else if (MCisForall(formName) || MCisExists(formName)) {
    //formHead is a boolean quantifier;
    //return the name of the quantified variable and the variable names of the
    //body
    result = ATinsert(getVariableNames(ATAgetArgument(form, 2)),
      ATgetArgument(form, 0)); 
  } else if (MCisMu(formName) || MCisNu(formName)) {
    //formHead is a fixed point quantifier;
    //return the variable names of this quantifier and the variable names of
    //the body
    result = ATmakeList1(ATgetArgument(form, 0));
    ATermList vds    = ATLgetArgument(form, 1);
    int length = ATgetLength(vds);
    for (int i = 0; i < length; i++) {
      result = ATinsert(result, ATgetArgument(ATAelementAt(vds, i), 0));
    }
    result = ATconcat(result, getVariableNames(ATAgetArgument(form, 2)));
  } else {
    //formHead is something else; return the variable names in the arguments
    result = ATmakeList0();
    int formArity = ATgetArity(formHead);
    for (int i = 0; i < formArity; i++) {
      result = ATconcat(result, getVariableNames(ATAgetArgument(form, i)));
    }
  }
finally:
  return result;  
}

ATermAppl renameVar(ATermAppl var, ATermAppl subst, int nArg, ATermAppl term) {
  ATermAppl result = NULL;
  if (MCdebug) {
    ATprintf(
      "renaming variable %t to %t that occurs free with %d arguments in term "
      "%t\n", var, subst, nArg, term);
  }
  AFun varHead = ATgetAFun(var);
  AFun termHead = ATgetAFun(term);
  int termArity = ATgetArity(termHead);
  if (ATisQuoted(termHead)) {
    //the head of term is a data term or a fixed point variable occurrence;
    if (termArity > 0) {
      //the arity of term is greater than 0;
      //rename variables in the arguments of term
      DECLA(ATerm, termArgs, termArity);
      for (int i = 0; i < termArity; i++) {
        termArgs[i] = (ATerm) renameVar(
          var, subst, nArg, ATAgetArgument(term, i));
      }
      //if the name of var is equal to the name of term and if nArg is equal to
      //the arity of term, replace the name of term by the name of subst
      if (nArg == termArity &&
        strcmp(ATgetName(varHead), ATgetName(termHead)) == 0)
      {        
        result = ATmakeApplArray(
          ATmakeAFun(ATgetName(ATgetAFun(subst)), nArg, ATtrue), termArgs);
      } else {
        result = ATmakeApplArray(termHead, termArgs);
      }      
    } else {
      //the arity of term is 0;
      //if var is equal to term and nArg is equal to 0, replace term by subst
      if (nArg == 0 && ATisEqual(var, term)) {
        result = subst;
      } else {
        result = term;
      }
    }
  } else {
    //the head of term is not quoted
    char *name = ATgetName(termHead);
    if (MCisAct(name)) {
      //the head of term is an action;
      //rename variables in the arguments of the action
      ATermAppl act = ATAgetArgument(term, 0);
      AFun actHead = ATgetAFun(act);
      int actArity = ATgetArity(actHead);
      if (actArity == 0) {
        result = term;
      } else {
        //actArity > 0
        DECLA(ATerm, actArgs, actArity);
        for (int i = 0; i < actArity; i++) {
          actArgs[i] = (ATerm) renameVar(
            var, subst, nArg, ATAgetArgument(act, i));
        }
        result = ATmakeAppl1(
          termHead, (ATerm) ATmakeApplArray(actHead, actArgs));
      }
    } else if (MCisForall(name) || MCisExists(name)) {
      //the head of term is a boolean quantifier; perform renaming such that
      //the total number of renamings is minimised
      result = term;
      ATermAppl qVar = ATAgetArgument(result, 0);
      if (nArg == 0 && ATisEqual(var, qVar)) {
        //var is equal to the quantified variable; no renaming necessary
      } else {
        //var is different from the quantified variable; check free occurrences
        //of var with nArg arguments in the body of the quantification
        ATermAppl body = ATAgetArgument(result, 2);
        if (!occursVar(var, nArg, body)) {
          //var with nArg parameters does not occur free in the body of the
          //quantification; no renaming necessary
        } else {
          //var with nArg parameters occurs free in the body of the
          //quantification; check if the quantified variable matches subst with
          //nArg arguments and rename var to subst in the body
          if (0 == nArg && ATisEqual(qVar, subst)) {
            //the quantified variable qVar matches subst with nArg arguments;
            //replace qVar by a fresh variable that:
            //- is different from var and qVar
            //- does not occur free with 0 arguments in body
            ATermAppl freshQVar = createFreshVarNOcc(
              false, ATmakeList2((ATerm) var, (ATerm) qVar), 0, body);
            //rename qVar to freshQVar in body
            body = renameVar(qVar, freshQVar, 0, body);
            //replace the first argument of term by freshQVar
            result = ATsetArgument(result, (ATerm) freshQVar, 0);
          }
          //rename var to subst in the body
          body = renameVar(var, subst, nArg, body);
          result = ATsetArgument(result, (ATerm) body, 2);
        }
      }
    } else if (MCisMu(name) || MCisNu(name)) {
      //head is a fixed point quantifier; perform renaming on the variable
      //initialisations of the quantification and perform substitution on the
      //body of the quantification such that the total number of renamings is
      //minimised
      //-----------------------------------------------------------------------
      //perform renaming on the variable initialisations of the quantification
      result = term;
      ATermList vis = ATLgetArgument(result, 3);
      int fpNArg = ATgetLength(vis);
      if (fpNArg > 0) {
        for (int i = 0; i < fpNArg; i++) {
          ATermAppl vi = ATAelementAt(vis, i);
          vi = renameVar(var, subst, nArg, vi);
          vis = ATreplace(vis, (ATerm) vi, i);
        }
        result = ATsetArgument(result, (ATerm) vis, 3);
      }
      //check if var is bound by one of the quantified variables, i.e. one of
      //the following holds:
      //- var is equal to the fixed point quantifier and nArg is equal to the
      //  number of arguments of the fixed point quantifier
      //- var is equal to one of the variables of the variable declarations of
      //  the quantification and nArg is 0
      ATermAppl fpVar = ATAgetArgument(result, 0);
      ATermList vds = ATLgetArgument(result, 1);
      bool found = (nArg == fpNArg && ATisEqual(var, fpVar));
      if (nArg == 0) {
        for (int i = 0; i < fpNArg && !found; i++) {
          found = 
            ATisEqual((ATerm) var, ATgetArgument(ATelementAt(vds, i), 0));
        }
      }
      if (found) {
        //var is bound by one of the quantified variables;
        //no renaming necessary
      } else {
        //var is not bound by one of the quantified variables; check free
        //occurrences of var with nArg arguments in the body of the
        //quantification
        ATermAppl body = ATAgetArgument(result, 2);
        if (!occursVar(var, nArg, body)) {
          //var with nArg parameters does not occur free in the body of the
          //quantification; no renaming necessary
        } else {
          //var with nArg parameters occurs free in the body of the
          //quantification; check if the quantified variables match subst with
          //nArg arguments and rename var to subst in the body
          if (fpNArg == nArg && ATisEqual(fpVar, subst)) {
            //fpVar matches subst with nArg arguments;
            //replace fpVar by a fresh variable that:
            //- is different from var and fpVar
            //- does not occur free with nArg arguments in body
            ATermAppl freshFPVar = createFreshVarNOcc(
              true, ATmakeList2((ATerm) var, (ATerm) fpVar), nArg, body);
            //rename fpVar to freshFPVar in body
            body = renameVar(fpVar, freshFPVar, nArg, body);
            //replace the first argument of term by freshFPVar
            result = ATsetArgument(result, (ATerm) freshFPVar, 0);
          }
          if (nArg == 0) {
            for (int i = 0; i < fpNArg; i++) {
              ATermAppl vd = ATAelementAt(vds, i);
              ATermAppl qVar = ATAgetArgument(vd, 0);
              if (ATisEqual(qVar, subst)) {
                //the quantifier qVar of i'th argument of fpVar matches subst
                //with nArg arguments; replace qVar by a fresh variable that:
                //- is different from var and the variables from the variable
                //  declarations of fpVar
                //- does not occur free with 0 arguments in body
                ATermList vars = ATmakeList1((ATerm) var);
                for (int j = 0; j < fpNArg; j++) {
                  vars = ATinsert(vars, ATgetArgument(ATelementAt(vds, j), 0));
                }
                ATermAppl freshQVar = createFreshVarNOcc(
                  false, vars, 0, body);
                //rename qVar to freshQVar in body
                body = renameVar(qVar, freshQVar, 0, body);
                //replace the quantifier of the i'th argument of fpVar by
                //freshQVar
                vd = ATsetArgument(vd, (ATerm) freshQVar, 0);
                vds = ATreplace(vds, (ATerm) vd, i);
                result = ATsetArgument(result, (ATerm) vds, 1);
              }
            }
          }
          //rename var to subst in the body
          body = renameVar(var, subst, nArg, body);
          result = ATsetArgument(result, (ATerm) body, 2);
        }
      }
    } else {
      //head is something else; perform renaming on its arguments
      if (termArity == 0) {
        result = term;
      } else {
        DECLA(ATerm, termArgs, termArity);
        for (int i = 0; i < termArity; i++) {
          termArgs[i] = (ATerm) renameVar(
            var, subst, nArg, ATAgetArgument(term, i));
        }
        result = ATmakeApplArray(termHead, termArgs);
      }
    }
  }
finally:
  if (MCdebug) {
    ATprintf(
      "(renameVar): return %t for var %t, subst %t, nArg %d and term %t\n",
        result, var, subst, nArg, term);
  }
  return result;  
}

bool occursVar(ATermAppl var, int nArg, ATermAppl term) {
  bool result = false;
  if (MCdebug) {
    ATprintf(
      "checking free occurrences of variable %t with %d arguments in term "
      "%t\n", var, nArg, term);
  }
  AFun varHead = ATgetAFun(var);
  AFun termHead = ATgetAFun(term);
  int termArity = ATgetArity(termHead);
  if (ATisQuoted(termHead)) {
    //the head of term is a data term or a fixed point variable occurrence;
    //return true if the head of term matches with var and nArg;
    //check occurrences of var in the arguments of term otherwise
    if (termArity > 0) {
      result = (nArg == termArity &&
        strcmp(ATgetName(varHead), ATgetName(termHead)) == 0);
    } else {
      //termArity is 0
      result = (nArg == 0 && ATisEqual(var, term));
      for (int i = 0; i < termArity && !result; i++) {
        result = occursVar(var, nArg, ATAgetArgument(term, i));
      }
    }
  } else {
    //head is not quoted
    char *name = ATgetName(termHead);
    if (MCisAct(name)) {
      //the head of term is an action indicator;
      //check occurrences of var in the arguments of the action
      ATermAppl act = ATAgetArgument(term, 0);
      int actArity = ATgetArity(ATgetAFun(act));
      for (int i = 0; i < actArity && !result; i++) {
        result = occursVar(var, nArg, ATAgetArgument(act, i));
      }
    } else if (MCisForall(name) || MCisExists(name)) {
      //the head of term is a boolean quantifier;
      //return false if quantified variable is equal to var and nArg is 0
      //check occurrences of var in the body of the quantification, otherwise
      result = nArg == 0 && ATisEqual((ATerm) var, ATgetArgument(term, 0));
      if (!result) {
        result = occursVar(var, nArg, ATAgetArgument(term, 2));
      }
    } else if (MCisMu(name) || MCisNu(name)) {
      //the head of term is a fixed point quantifier;
      //check occurrences of var in the variable initialisations of the
      //quantification and check occurrences of var in the body of the
      //quantification if it is not equal to one of the quantified variables
      ATermList vis = ATLgetArgument(term, 3);
      int fpNArg = ATgetLength(vis);
      for (int i = 0; i < fpNArg && !result; i++) {
        result = occursVar(var, nArg, ATAelementAt(vis, i));
      }
      if (!result) {
        bool found = 
          nArg == fpNArg && ATisEqual((ATerm) var, ATgetArgument(term, 0));
        if (!found && nArg == 0) {
          ATermList vds = ATLgetArgument(term, 1);
          for (int i = 0; i < fpNArg && !found; i++) {
            found = 
              ATisEqual((ATerm) var, ATgetArgument(ATAelementAt(vds, i),0));
          }
        }
        if (!found) {
          result = occursVar(var, nArg, ATAgetArgument(term, 2));
        }
      }
    } else {
      //the head of term is something else;
      //check occurrences of var in the arguments of term
      for (int i = 0; i < termArity && !result; i++) {
        result = occursVar(var, nArg, ATAgetArgument(term, i));
      }
    }
  }
finally:
  if (MCdebug) {
    ATprintf("(occursVar): return %s for var %t, nArg %d and term %t\n", 
      result?"true":"false", var, nArg, term);
  }
  return result;  
}

ATermAppl createFreshVar(bool cap, ATermList vars)
{
  return createFreshVarNOccs(cap, vars, 0, ATmakeList0());
}

ATermAppl createFreshVarNOcc(
  bool cap, ATermList vars, int nArg, ATermAppl term)
{
  return createFreshVarNOccs(cap, vars, nArg, ATmakeList1((ATerm) term));
}

ATermAppl createFreshVarNOccs(
  bool cap, ATermList vars, int nArg, ATermList terms)
{
  if (MCdebug) {
    ATprintf(
      "creating fresh variable using vars %t, nArg %d and terms %t\n",
      vars, nArg, terms);
  }
  ATermAppl result = NULL;
  bool done = false;
  //iteratively create a unique variable and perform a number of checks on it;
  for (int i = 0; !done; i++) {
    //create variable with index i; capitalise variable if cap
    result = createNewVar(cap, i);
    //check if the new variable occurs free in terms with nArg arguments
    int length = ATgetLength(terms);
    bool found = false;    
    for (int j = 0; j < length && !found; j++) {
      found = occursVar(result, nArg, ATAelementAt(terms, j));
    }
    //check if the new variable is equal to an element of vars
    length = ATgetLength(vars);
    for (int j = 0; j < length && !found; j++) {
      found = (ATisEqual((ATerm) result, ATelementAt(vars, j)));
    }
    //if none of the checks returned true, then we are done
    if (!found) {
      done = true;
    }
  }
finally:
  if (MCdebug) {
    ATprintf(
      "(createFreshVarNOccs): return %t for vars %t, nArg %d and terms %t\n",
      result, vars, nArg, terms);
  }
  return result;  
}

ATermAppl createNewVar(bool cap, int index)
{
  if (MCdebug) {
    ATprintf("creating variable with index %d and cap %s\n",
      index, cap?"true":"false");
  }
  ATermAppl result = NULL;
  int suffix = index / 3;
  char name[suffix+2];
  char base;
  //choose x/X, y/Y or z/Z
  switch (index % 3) {
    case 0:
      base = cap?'X':'x';
      break;
    case 1:
      base = cap?'Y':'y';
      break;
    case 2:
      base = cap?'Z':'z';
      break;
  }
  //append suffix if necessary
  if (suffix == 0) {
    sprintf(name, "%c", base);
  } else {
    sprintf(name, "%c%d", base, suffix);
  }
  result = ATmakeAppl0(ATmakeAFun(name, 0, ATtrue));
finally:
  if (MCdebug) {
    ATprintf("(createNewVar): return %t for index %d and cap %s\n", 
      result, index, cap?"true":"false");
  }
  return result;
}

bool checkMonotonicity(ATermAppl form)
{
  bool result = checkMonotonicityContext(form, ATmakeList0());
finally:
  if (MCdebug) {
    ATprintf("(checkMonotonicity): return %s for formula\n  %t\n", 
      result?"true":"false", form);
  }
  return result;
}
bool checkMonotonicityContext(ATermAppl form, ATermList fpVarNegs)

{
  bool result = false;
  if (MCdebug) {
    ATprintf(
      "(checkMonotonicityContext): checking monotonicity of\n  %t,\n  using "
      "%t\n", form, fpVarNegs);
  }
  char *name = ATgetName(ATgetAFun(form));
  if (MCisForm(name)) {
    //form is an mCRL formula; return true
    result = true;
  } else if (MCisT(name) || MCisF(name)) {
    //form is true or false; return true
    result = true;
  } else if (MCisNot(name)) {
    //form is a negation; check monotonicity of its argument, where the number
    //of negations in fpVarNegs is incremented
    result = checkMonotonicityContext(
      ATAgetArgument(form,0), incNeg(fpVarNegs));
  } else if (MCisAnd(name) || MCisOr(name)) {
    //form is a conjunction or a disjunction; check monotonicity of both
    //arguments
    result = 
      checkMonotonicityContext(ATAgetArgument(form,0), fpVarNegs) &&
      checkMonotonicityContext(ATAgetArgument(form,1), fpVarNegs);
  } else if (MCisImp(name)) {
    //form is an implication; check monotonicity of both arguments, where the
    //number of negations in fpVarNegs is negated for the first argument
    result = 
      checkMonotonicityContext(ATAgetArgument(form,0), incNeg(fpVarNegs)) &&
      checkMonotonicityContext(ATAgetArgument(form,1), fpVarNegs);
  } else if (MCisEq(name)) {
    //form is an equivalence; check the following:
    //- monotonicity of both arguments, where the number of negations in
    //  fpVarNegs is incremented for the first argument
    //- monotonicity of both arguments, where the number of negations in
    //  fpVarNegs is incremented for the second argument
    result = 
      checkMonotonicityContext(ATAgetArgument(form,0), incNeg(fpVarNegs)) &&
      checkMonotonicityContext(ATAgetArgument(form,1), fpVarNegs) &&
      checkMonotonicityContext(ATAgetArgument(form,0), fpVarNegs) &&
      checkMonotonicityContext(ATAgetArgument(form,1), incNeg(fpVarNegs));
  } else if (MCisForall(name) || MCisExists(name)) {
    //form is a boolean quantification; check monotonicity of the body of the
    //quantification, where the quantified variable is removed from fpVarNegs,
    //if it occurs in it
    ATermList fpVar = ATmakeList2(
      ATgetArgument(form, 0), (ATerm) ATmakeInt(0));
    result = checkMonotonicityContext(
      ATAgetArgument(form,2), removeFPVar(fpVar, fpVarNegs));
  } else if (MCisMay(name) || MCisMust(name)) {
    //form is a modal operation; check monotonicity of its second argument
    result = checkMonotonicityContext(ATAgetArgument(form,1), fpVarNegs);
  } else if (MCisLoop(name)) {
    //form is a loop operation; return true
    result = true;
  } else if (MCisRec(name)) {
    //form is a fixed point variable occurrence indicator; return true if the
    //number of negations of the occurrence is even; return false otherwise
    AFun fun = ATgetAFun(ATgetArgument(form, 0));
    ATermList fpVar = ATmakeList2(
      (ATerm) ATmakeAppl0(ATmakeAFun(ATgetName(fun), 0, ATtrue)),
      (ATerm) ATmakeInt(ATgetArity(fun)));
    result = evenNeg(fpVar, fpVarNegs);
  } else if (MCisMu(name) || MCisNu(name)) {
    //form is a fixed point quantification; check monotonicity of the body of
    //the quantification, where fpVarNegs is extended or updated with the fixed
    //point variable, depending on if the variable already occurs in it
    ATermList fpVar = ATmakeList2(ATgetArgument(form, 0),
      (ATerm) ATmakeInt(ATgetLength(ATLgetArgument(form, 1))));
    ATermList fpVarNeg = ATmakeList2((ATerm) fpVar, (ATerm) ATmakeInt(0));
    result = checkMonotonicityContext(ATAgetArgument(form,2), 
      ATinsert(removeFPVar(fpVar, fpVarNegs), (ATerm) fpVarNeg));
  }
  if (MCdebug) {
    ATprintf("returned %s for\n  %t,\n  using %t\n", 
      result?"true":"false", form, fpVarNegs);
  }
finally:
  return result;  
}

ATermList removeFPVar(ATermList fpVar, ATermList fpVarNegs) {
  ATermList result = fpVarNegs;
  int length = ATgetLength(result);
  bool found = false;
  for (int i = 0; i < length && !found; i++) {
    if ATisEqual(fpVar, ATLelementAt(ATLelementAt(result, i), 0)) {
      result = ATremoveElementAt(result, i);
      found = true;
    }
  }
finally:
  return result;  
}

ATermList incNeg(ATermList fpVarNegs)
{
  ATermList result = ATmakeList0();
  int length = ATgetLength(fpVarNegs);
  for (int i = length-1; i >= 0; i--) {
    ATermList fpVarNeg = ATLelementAt(fpVarNegs, i);
    ATermAppl fpVar    = ATAelementAt(fpVarNeg, 0);
    int neg = ATgetInt(ATIelementAt(fpVarNeg, 1));
    fpVarNeg = ATmakeList2((ATerm) fpVar, (ATerm) ATmakeInt(neg+1));
    result = ATinsert(result, (ATerm) fpVarNeg);
  }
finally:
  if (MCdebug) {
    ATprintf("(incNeg): return\n  %t for list\n  %t\n", 
      result, fpVarNegs);
  }
  return result;
}

bool evenNeg(ATermList fpVar, ATermList fpVarNegs)
{
  bool result = false;
  int length = ATgetLength(fpVarNegs);
  bool found = false;
  for (int i = 0; i < length && !found; i++) {
    ATermList fpVarNeg = ATLelementAt(fpVarNegs, i);
    if (ATisEqual(fpVar, ATLelementAt(fpVarNeg, 0))) {
      result = (ATgetInt(ATIelementAt(fpVarNeg, 1)) % 2 == 0);
      found = true;      
    }
  }
finally:
  if (MCdebug) {
    ATprintf("(evenNeg): return %s for list\n  %t\n  and variable %t\n", 
      result?"true":"false", fpVarNegs, fpVar);
  }
  return result;
}

bool hasFPQVarNameConflicts(ATermAppl form)
{
  bool result = false;
  if (MCdebug) {
    ATprintf(
      "(hasFPQVarNameConflict): checking occurrences of fixed point variable "
      "name conflicts in %t\n", form);
  }
  AFun formHead = ATgetAFun(form);
  char *formName = ATgetName(formHead);
  if (MCisForm(formName) || MCisRec(formName) || MCisAct(formName)) {
    //formHead is the indicator of an mCRL formula, a fixed point variable
    //occurrence or an action; return false
  } else if (MCisForall(formName) || MCisExists(formName)) {
    //formHead is a boolean quantifier;
    //return the result of a recursive call to the body of the quantification
    result = hasFPQVarNameConflicts(ATAgetArgument(form, 2));
  } else if (MCisMu(formName) || MCisNu(formName)) {
    //formHead is a fixed point quantifier;
    //if the variable declarations of the quantification contains duplicate
    //variable names, return true; false otherwise
    ATermList vds  = ATLgetArgument(form, 1);
    ATermList vars = ATmakeList0();
    int length = ATgetLength(vds);
    for (int i = 0; i < length; i++) {
      vars = ATinsert(vars, ATgetArgument(ATAelementAt(vds, i), 0));
    }
    for (int i = 0; i < length-1 && !result; i++) {
      result = (ATindexOf(vars, ATelementAt(vars, i), i+1) >= 0);
    }
    if (result) {
      ATfprintf(stderr, 
        "error: quantification %t has a variable name conflict\n", form);
    }
  } else {
    //formHead is something else; recursively call function on the arguments
    int formArity = ATgetArity(formHead);
    for (int i = 0; i < formArity; i++) {
      if (hasFPQVarNameConflicts(ATAgetArgument(form, i))) {
        result = true;
      }
    }
  }
finally:
  return result;  
}

int dangerousFPNestings(ATermAppl form)
{
  int result = dangerousFPNestingsContext(form, ATmakeList0());
finally:
  if (MCdebug) {
    ATprintf("(dangerousFPNestings): return %d for formula\n  %t\n", 
      result, form);
  }
  return result;
}

int dangerousFPNestingsContext(ATermAppl form, ATermList fpVarSorts)
{
  int result = 0;
  if (MCdebug) {
    ATprintf(
      "(dangerousFPNestingsContext): counting dangerous fixed point variable "
      "nestings in\n  %t,\n  under context %t\n", form, fpVarSorts);
  }
  char *name = ATgetName(ATgetAFun(form));
  if (MCisForm(name) || MCisRec(name)) {
    //form is an mCRL formula or a fixed point variable occurrence; return 0
    result = 0;
  } else if (MCisT(name) || MCisF(name)) {
    //form is true or false; return 0
    result = 0;
  } else if (MCisNot(name)) {
    //form is a negation; count dangerous nestings in the first argument
    result = dangerousFPNestingsContext(ATAgetArgument(form,0), fpVarSorts);
  } else if (MCisAnd(name) || MCisOr(name) || MCisImp(name) || MCisEq(name)) {
    //form is a conjunction, a disjunction, an implication or an equivalence;
    //count dangerous nestings in both arguments
    result = 
      dangerousFPNestingsContext(ATAgetArgument(form,0), fpVarSorts) +
      dangerousFPNestingsContext(ATAgetArgument(form,1), fpVarSorts);
  } else if (MCisForall(name) || MCisExists(name)) {
    //form is a boolean quantification; count dangerous nestings in the third
    //argument
    result = dangerousFPNestingsContext(ATAgetArgument(form,2), fpVarSorts);
  } else if (MCisMay(name) || MCisMust(name)) {
    //form is a modal operation; count dangerous nestings in the second
    //argument
    result = dangerousFPNestingsContext(ATAgetArgument(form,1), fpVarSorts);
  } else if (MCisLoop(name)) {
    //form is a loop operation; return 0
    result = 0;
  } else if (MCisMu(name) || MCisNu(name)) {
    //form is a fixed point quantification; do the following:
    //- compare the quantified variable of form to the elements of fpVarSorts;
    //  if the names and number of sorts are equal but the sorts are different,
    //  the result is incremented
    //- find dangerous nestings in the body of the quantification
    //-------------------------------------------------------------------------
    //set the quantified variable to fpVar, the sorts of the arguments to
    //sorts and the number of sorts to fpNArg
    ATermAppl fpVar = ATAgetArgument(form, 0);
    ATermList vds = ATLgetArgument(form, 1);
    int fpNArg = ATgetLength(vds);
    ATermList sorts = ATmakeList0();
    for (int i = 0; i < fpNArg; i++) {
      sorts = ATinsert(sorts, ATgetArgument(ATAelementAt(vds, i), 1));
    }
    //check all elements of fpVarSorts on dangerous nestings
    int length = ATgetLength(fpVarSorts);
    for (int i = 0; i < length; i++) {
      ATermList fpVarSorts_i = ATLelementAt(fpVarSorts, i);
      ATermAppl fpVar_i = ATAelementAt(fpVarSorts_i, 0);
      ATermAppl sorts_i = ATAelementAt(fpVarSorts_i, 1);      
      if (fpNArg == ATgetLength(sorts_i) && ATisEqual(fpVar, fpVar_i) 
        && !ATisEqual(sorts, sorts_i)) {
        //found dangerous nesting; increment result
        result++;
      }
    }
    //find dangerous nestings in the body of the quantification
    ATermList fpVarSort = ATmakeList2((ATerm) fpVar, (ATerm) sorts);
    int index = ATindexOf(fpVarSorts, (ATerm) fpVarSort, 0);
    result += dangerousFPNestingsContext(
      ATAgetArgument(form, 2),
      (index == -1)?ATinsert(fpVarSorts, (ATerm) fpVarSort):fpVarSorts);
  }
  if (MCdebug) {
    ATprintf("(dangerousFPNestingsContext): returned %d for\n  %t,\n  using "
      "%t\n", result, form, fpVarSorts);
  }
finally:
  return result;  
}

void MCtest(void) {  
}
