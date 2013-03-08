#include "mcfunc.h"
#include <string.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifdef __cplusplus
}
#endif

//ATmake extensions

ATermAppl MCmakeName(char *name)
{
  return ATmakeAppl0(ATmakeAFun(name, 0, ATtrue));
}

ATermAppl MCmakeVar(ATermAppl vName, ATermAppl vSort)
{
  return ATmakeAppl2(ATmakeAFun("v", 2, ATfalse), (ATerm) vName, (ATerm) vSort);
}

ATermAppl MCmakeAct(ATermAppl action)
{
  return ATmakeAppl1(ATmakeAFun("act", 1, ATfalse), (ATerm) action);
}

ATermAppl MCmakeT(void)
{
  return ATmakeAppl0(ATmakeAFun("T", 0, ATfalse));
}

ATermAppl MCmakeF(void)
{
  return ATmakeAppl0(ATmakeAFun("F", 0, ATfalse));
}

ATermAppl MCmakeNot(ATermAppl form)
{
  return ATmakeAppl1(ATmakeAFun("not", 1, ATfalse), (ATerm) form);
}

ATermAppl MCmakeAnd(ATermAppl form0, ATermAppl form1)
{
  return ATmakeAppl2(ATmakeAFun("and", 2, ATfalse),
    (ATerm) form0, (ATerm) form1);
}

ATermAppl MCmakeOr(ATermAppl form0, ATermAppl form1)
{
  return ATmakeAppl2(ATmakeAFun("or", 2, ATfalse), 
    (ATerm) form0, (ATerm) form1);
}

ATermAppl MCmakeImp(ATermAppl form0, ATermAppl form1)
{
  return ATmakeAppl2(ATmakeAFun("imp", 2, ATfalse), 
    (ATerm) form0, (ATerm) form1);
}

ATermAppl MCmakeEq(ATermAppl form0, ATermAppl form1)
{
  return ATmakeAppl2(ATmakeAFun("eq", 2, ATfalse), 
    (ATerm) form0, (ATerm) form1);
}

ATermAppl MCmakeForall(ATermAppl v_name, ATermAppl v_sort, ATermAppl form)
{
  return ATmakeAppl3(ATmakeAFun("forall", 3, ATfalse), 
    (ATerm) v_name, (ATerm) v_sort, (ATerm) form);
}

ATermAppl MCmakeExists(ATermAppl v_name, ATermAppl v_sort, ATermAppl form)
{
  return ATmakeAppl3(ATmakeAFun("exists", 3, ATfalse), 
    (ATerm) v_name, (ATerm) v_sort, (ATerm) form);
}

ATermAppl MCmakeNil(void)
{
  return ATmakeAppl0(ATmakeAFun("nil", 0, ATfalse));
}

ATermAppl MCmakeConcat(ATermAppl form0, ATermAppl form1)
{
  return ATmakeAppl2(ATmakeAFun("concat", 2, ATfalse),
    (ATerm) form0, (ATerm) form1);
}

ATermAppl MCmakeChoice(ATermAppl form0, ATermAppl form1)
{
  return ATmakeAppl2(ATmakeAFun("choice", 2, ATfalse),
    (ATerm) form0, (ATerm) form1);
}

ATermAppl MCmakeTrClose(ATermAppl form)
{
  return ATmakeAppl1(ATmakeAFun("tr_close", 1, ATfalse), (ATerm) form);
}

ATermAppl MCmakeTClose(ATermAppl form)
{
  return ATmakeAppl1(ATmakeAFun("t_close", 1, ATfalse), (ATerm) form);
}

ATermAppl MCmakeFormRec(ATermAppl form)
{
  return ATmakeAppl1(ATmakeAFun("form_rec", 1, ATfalse), (ATerm) form);
}

ATermAppl MCmakeForm(ATermAppl form)
{
  return ATmakeAppl1(ATmakeAFun("form", 1, ATfalse), (ATerm) form);
}

ATermAppl MCmakeRec(ATermAppl fpVO)
{
  return ATmakeAppl1(ATmakeAFun("rec", 1, ATfalse), (ATerm) fpVO);
}

ATermAppl MCmakeMay(ATermAppl regFrm, ATermAppl modFrm) 
{
  return ATmakeAppl2(ATmakeAFun("may", 2, ATfalse),
    (ATerm) regFrm, (ATerm) modFrm);
}

ATermAppl MCmakeMust(ATermAppl regFrm, ATermAppl modFrm)
{
  return ATmakeAppl2(ATmakeAFun("must", 2, ATfalse), 
    (ATerm) regFrm, (ATerm) modFrm);
}

ATermAppl MCmakeLoop(ATermAppl form)
{
  return ATmakeAppl1(ATmakeAFun("loop", 1, ATfalse), (ATerm) form);
}

ATermAppl MCmakeMu(ATermAppl fpVar, ATermList vdList, ATermAppl modFrm, ATermList iList)
{
  return ATmakeAppl4(ATmakeAFun("mu", 4, ATfalse), 
    (ATerm) fpVar, (ATerm) vdList, (ATerm) modFrm, (ATerm) iList);
}

ATermAppl MCmakeNu(ATermAppl fpVar, ATermList vdList, ATermAppl modFrm, ATermList iList)
{
  return ATmakeAppl4(ATmakeAFun("nu", 4, ATfalse), 
    (ATerm) fpVar, (ATerm) vdList, (ATerm) modFrm, (ATerm) iList);
}

//strcmp extensions

bool MCisVar(char *s)
{
  return strcmp(s, "v") == 0;
}

bool MCisAct(char *s)
{
  return strcmp(s, "act") == 0;
}

bool MCisT(char *s)
{
  return strcmp(s, "T") == 0;
}

bool MCisF(char *s)
{
  return strcmp(s, "F") == 0;
}

bool MCisNot(char *s)
{
  return strcmp(s, "not") == 0;
}

bool MCisAnd(char *s)
{
  return strcmp(s, "and") == 0;
}

bool MCisOr(char *s)
{
  return strcmp(s, "or") == 0;
}

bool MCisImp(char *s)
{
  return strcmp(s, "imp") == 0;
}

bool MCisEq(char *s)
{
  return strcmp(s, "eq") == 0;
}

bool MCisForall(char *s)
{
  return strcmp(s, "forall") == 0;
}

bool MCisExists(char *s)
{
  return strcmp(s, "exists") == 0;
}

bool MCisNil(char *s)
{
  return strcmp(s, "nil") == 0;
}

bool MCisConcat(char *s)
{
  return strcmp(s, "concat") == 0;
}

bool MCisChoice(char *s)
{
  return strcmp(s, "choice") == 0;
}

bool MCisTrClose(char *s)
{
  return strcmp(s, "tr_close") == 0;
}

bool MCisTClose(char *s)
{
  return strcmp(s, "t_close") == 0;
}

bool MCisFormRec(char *s)
{
  return strcmp(s, "form_rec") == 0;
}

bool MCisForm(char *s)
{
  return strcmp(s, "form") == 0;
}

bool MCisRec(char *s)
{
  return strcmp(s, "rec") == 0;
}

bool MCisMay(char *s)
{
  return strcmp(s, "may") == 0;
}

bool MCisMust(char *s)
{
  return strcmp(s, "must") == 0;
}

bool MCisLoop(char *s)
{
  return strcmp(s, "loop") == 0;
}

bool MCisMu(char *s)
{
  return strcmp(s, "mu") == 0;
}

bool MCisNu(char *s)
{
  return strcmp(s, "nu") == 0;
}

//ATerm libary work arounds

ATermAppl ATAelementAt(ATermList list, int index)
{
  return (ATermAppl) ATelementAt(list, index);
}

ATermList ATLelementAt(ATermList list, int index)
{
  return (ATermList) ATelementAt(list, index);
}

ATermInt ATIelementAt(ATermList list, int index)
{
  return (ATermInt) ATelementAt(list, index);
}

ATermAppl ATAgetArgument(ATermAppl appl, int nr)
{
  return (ATermAppl) ATgetArgument(appl, nr);
}

ATermList ATLgetArgument(ATermAppl appl, int nr)
{
  return (ATermList) ATgetArgument(appl, nr);
}

ATermInt ATIgetArgument(ATermAppl appl, int nr)
{
  return (ATermInt) ATgetArgument(appl, nr);
}
