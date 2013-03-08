#include <stdbool.h>
#include "aterm2.h"

#ifdef __cplusplus
extern "C" {
#endif

//Global precondition: the ATerm library has been initialised

//String manipulation
//-------------------
//
//Re-implementation of strdup (because it is not part of the C99 standard)
#if defined HAVE_DECL_STRDUP && !HAVE_DECL_STRDUP
extern char *strdup(const char *s);
#endif /* HAVE_DECL_STRDUP */

//Exception handling macro's
//--------------------------
//
//When these are used the label 'finally' should be declared.
//If a value 'x' should be returned, the variable 'result' has to be declared, 
//and the type of 'x' should be convertible to that of 'result'.
//If a message, should be printed, the message has to be able to be used by
//function printf.

#define throw                      goto finally
//model C++ throw by a 'goto finally' statement

#define throwV(x)                  result = x; throw
//store x in result and throw an exception

#define throwM0(s)                 fprintf(stderr, s); throw
//print message s and throw an exception

#define throwVM0(x, s)             fprintf(stderr, s); throwV(x)
//print message s and throw an exception with value x

#define throwVM1(x, s, a1)         fprintf(stderr, s, a1); throwV(x)
//print message s with argument a1, and throw an exception with value x

#define throwVM2(x, s, a1, a2)     fprintf(stderr, s, a1, a2); throwV(x)
//print message s with argument a1 and a2,  and throw an exception with value x

#define throwVM3(x, s, a1, a2, a3) fprintf(stderr, s, a1, a2, a3); throwV(x)
//print message s with argument a1, a2 and a3,  and throw an exception with
//value x

//ATmake extensions
//-----------------
//
//Implements the making of all elements of the structure of ATerms to improve 
//readability and to minimise type casts in the rest of the code

ATermAppl MCmakeName(char *name);
ATermAppl MCmakeVar(ATermAppl vName, ATermAppl vSort);
ATermAppl MCmakeAct(ATermAppl action);
ATermAppl MCmakeT(void);
ATermAppl MCmakeF(void);
ATermAppl MCmakeNot(ATermAppl form);
ATermAppl MCmakeAnd(ATermAppl form0, ATermAppl form1);
ATermAppl MCmakeOr(ATermAppl form0, ATermAppl form1);
ATermAppl MCmakeImp(ATermAppl form0, ATermAppl form1);
ATermAppl MCmakeEq(ATermAppl form0, ATermAppl form1);
ATermAppl MCmakeForall(ATermAppl vName, ATermAppl vSort, ATermAppl form);
ATermAppl MCmakeExists(ATermAppl vName, ATermAppl vSort, ATermAppl form);
ATermAppl MCmakeNil(void);
ATermAppl MCmakeConcat(ATermAppl form0, ATermAppl form1);
ATermAppl MCmakeChoice(ATermAppl form0, ATermAppl form1);
ATermAppl MCmakeTrClose(ATermAppl form);
ATermAppl MCmakeTClose(ATermAppl form);
ATermAppl MCmakeFormRec(ATermAppl form);
ATermAppl MCmakeForm(ATermAppl form);
ATermAppl MCmakeRec(ATermAppl fpVO);
ATermAppl MCmakeMay(ATermAppl regFrm, ATermAppl modFrm);
ATermAppl MCmakeMust(ATermAppl regFrm, ATermAppl modFrm);
ATermAppl MCmakeLoop(ATermAppl form);
ATermAppl MCmakeMu(ATermAppl fpVar, ATermList vdList, ATermAppl modFrm, ATermList iList);
ATermAppl MCmakeNu(ATermAppl fpVar, ATermList vdList, ATermAppl modFrm, ATermList iList);

//strcmp extensions
//------------------
//
//Implements the comparison of the function names of all elements of the 
//structure of ATerms to improve readability

bool MCisVar(char *s);
bool MCisAct(char *s);
bool MCisT(char *s);
bool MCisF(char *s);
bool MCisNot(char *s);
bool MCisAnd(char *s);
bool MCisOr(char *s);
bool MCisImp(char *s);
bool MCisEq(char *s);
bool MCisForall(char *s);
bool MCisExists(char *s);
bool MCisNil(char *s);
bool MCisConcat(char *s);
bool MCisChoice(char *s);
bool MCisTrClose(char *s);
bool MCisTClose(char *s);
bool MCisFormRec(char *s);
bool MCisForm(char *s);
bool MCisRec(char *s);
bool MCisMay(char *s);
bool MCisMust(char *s);
bool MCisLoop(char *s);
bool MCisMu(char *s);
bool MCisNu(char *s);

//ATerm library work arounds
//--------------------------
//
//To eliminate ridiculous type casts in the rest of the code, we introducde
//wrappers around functions ATelementAt and ATgetArgument.
//This is caused by a bad interface design of the ATerm library

ATermAppl ATAelementAt(ATermList list, int index);
ATermList ATLelementAt(ATermList list, int index);
ATermInt  ATIelementAt(ATermList list, int index);
ATermAppl ATAgetArgument(ATermAppl appl, int nr);
ATermList ATLgetArgument(ATermAppl appl, int nr);
ATermInt  ATIgetArgument(ATermAppl appl, int nr);

#ifdef __cplusplus
}
#endif
