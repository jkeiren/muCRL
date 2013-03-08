%{
/* In the following grammar/parser the regular formulas from the syntax 
   description are restricted such that they cannot accept action formulas
   surrounded by parentheses at the top level. The reason for this is that 
   in the original syntax the expression
     ( AN )
   where AN is an action name, could be parsed as both a regular formula and 
   an action formula. Although the meaning of both parses is the same, I think
   grammars should be unambiguous. Also, I don't like the parser to make its
   own choice and give an unnecessary warning message about a shift/reduce
   conflict.
   
   Also the rules for mCRL formulas and occurrences of fixed point variables
   are combined to avoid ambiguity. These will have to be split later.
*/

#include <stdio.h>
#include <string.h>
#include <stdbool.h>

#include "aterm2.h"
#include "mcfunc.h"

//Global precondition: the ATerm library has been initialised

//external declarations
extern ATermAppl MCtree;        /* declared in mclexer.l */
extern void MCyyerror(char *s); /* declared in mclexer.l */
extern int MCyylex(void);       /* declared in mclexer.c */
extern bool MCdebug;           /* declared in libmcparse.c */

//local declarations

ATermAppl splitFormRec(ATermAppl form);
//Pre: form is a modal formula
//Ret: form in which each term 'form_rec(t)' is replaced by:
//     - 'rec(t)', if t is bound by a fixed point quantifier mu of nu
//     - 'form(t)' , otherwise.

ATermAppl gSplitFormRec(ATermAppl form, ATermList fpVnNArgs);
//Pre: form is a modal formula, fpVnNArgs is a list of pairs of fixed point 
//     variable names and the number of arguments
//Ret: form in which each term 'form_rec(t)' is replaced by:
//     - 'rec(t)', if a pair (h,n) exists in fpVnNArgs, for which we have:
//        - the name of the head of t is equal to the name of h
//        - the arity of the head of t is equal to n
//     - 'form(t)' , otherwise.

%}
%union {
  ATermAppl appl;
  ATermList list;
}

%token PAR_OPEN PAR_CLOSE BR_OPEN BR_CLOSE ANG_OPEN ANG_CLOSE
%token COMMA SEMICOLON IS AT
%token <appl> KWTRUE KWFALSE KWNIL KWFORALL KWEXISTS KWMU KWNU RNAME

%left EQ
%right IMP
%left AND OR
%nonassoc NOT QUANTIFIER MAY MUST

%left PIPE
%left DOT
%nonassoc STAR PLUS

%type <appl> NAME dt act form_fp_vo
%type <list> vd vdi fp_vd dt_list vdi_list
%type <appl> act_frm reg_frm_woaf reg_frm mod_frm mod_frm_top

%start mod_frm_top
 
%%

//mCRL names
  
NAME:
  RNAME       { $$ = $1; }
  | KWTRUE    { $$ = $1; }
  | KWFALSE   { $$ = $1; }
  | KWFORALL  { $$ = $1; }
  | KWEXISTS  { $$ = $1; }
  | KWNIL     { $$ = $1; }
  | KWMU      { $$ = $1; }
  | KWNU      { $$ = $1; }
  ;
  
//mCRL data terms

dt:
  NAME
    { 
      $$ = $1;
      if (MCdebug) {
        ATprintf( "parsed data term\n  %t\n", $$);
      }
    }
  | NAME PAR_OPEN dt_list PAR_CLOSE        
    { 
      $$ = ATmakeApplList(ATmakeAFun(ATgetName(ATgetAFun($1)), ATgetLength($3),ATtrue),
             ATreverse($3));
      if (MCdebug) {
        ATprintf( "parsed data term\n  %t\n", $$);
      }
    }
  ;

dt_list: /* The resulting list is reversed with regard to the appearance
            of the parsed terms */
  dt 
    { 
      $$ = ATmakeList1((ATerm) $1);
      if (MCdebug) {
        ATprintf( "parsed data term list\n  %t\n", $$);
      }
    }
  | dt_list COMMA dt 
    { 
      $$ = ATinsert($1, (ATerm) $3);
      if (MCdebug) {
        ATprintf( "parsed data term list\n  %t\n", $$);
      }
    }
  ;

//mCRL actions

act:
  RNAME
    {
      $$ = $1;     
      if (MCdebug) {
        ATprintf( "parsed action\n  %t\n", $$);
      }
    }
  | RNAME PAR_OPEN dt_list PAR_CLOSE 
    {
      $$ = ATmakeApplList(
        ATmakeAFun(ATgetName(ATgetAFun($1)), ATgetLength($3), ATtrue),
        ATreverse($3));
      if (MCdebug) {
        ATprintf( "parsed action\n  %t\n", $$);
      }
    }
  ;

//mCRL formulas

form_fp_vo:
  RNAME
    { 
      $$ = $1;
      if (MCdebug) {
        ATprintf( "parsed mCRL formula/fixed point variable occurrence\n  %t\n", $$); 
      }
    }
  | RNAME PAR_OPEN dt_list PAR_CLOSE        
    { 
      $$ = ATmakeApplList(
        ATmakeAFun(ATgetName(ATgetAFun($1)), ATgetLength($3),ATtrue),
        ATreverse($3));
      if (MCdebug) {
        ATprintf( "parsed mCRL formula/fixed point variable occurrence\n  %t\n", $$); 
      }
    }
  ;

//variable declarations and initialisations

vd:
  RNAME SEMICOLON RNAME 
    { 
      $$ = ATmakeList2((ATerm) $1, (ATerm) $3);
      if (MCdebug) {
        ATprintf( "parsed mCRL variable declaration\n  %t\n", $$);
      }
    }
  ;

vdi:
  vd IS dt 
    { 
      $$ = ATmakeList3(ATelementAt($1, 0), ATelementAt($1, 1), (ATerm) $3);
      if (MCdebug) {
        ATprintf( "parsed mCRL variable declaration and initialisation\n  %t\n", $$);
      }
    }
  ;

vdi_list: /* The resulting list is reversed with regard to the appearance
            of the parsed terms */
  vdi
    { 
      $$ = ATmakeList1((ATerm) $1);
      if (MCdebug) {
        ATprintf( "parsed mCRL variable declaration and initialisation list\n  %t\n", $$);
      }
    }
  | vdi_list COMMA vdi
    {
      $$ = ATinsert($1, (ATerm) $3);  
      if (MCdebug) {
        ATprintf( "parsed variable declaration and initialisation list\n  %t\n", $$);
      }
    }
  ;

fp_vd:
  RNAME
    { 
      $$ = ATmakeList2((ATerm) $1, (ATerm) ATmakeList0());
      if (MCdebug) {
        ATprintf( "parsed fixed point variable declaration\n  %t\n", $$); 
      }
    }
  | RNAME PAR_OPEN vdi_list PAR_CLOSE        
    { 
      $$ = ATmakeList2((ATerm) $1, (ATerm) $3);
      if (MCdebug) {
        ATprintf( "parsed fixed point variable declaration\n  %t\n", $$);
      }
    }
  ;

//Action formulas

act_frm:
  act
    {
      $$ = MCmakeAct($1);
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  | PAR_OPEN act_frm PAR_CLOSE
    { 
      $$ = $2;
    }
  | KWTRUE
    { 
      $$ = MCmakeT();
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  | KWFALSE
    { 
      $$ = MCmakeF();
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  | NOT act_frm
    { 
      $$ = MCmakeNot($2);
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  | act_frm AND act_frm
    { 
      $$ = MCmakeAnd($1, $3);
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  | act_frm OR act_frm 
    { 
      $$ = MCmakeOr($1, $3);
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  | act_frm IMP act_frm
    { 
      $$ = MCmakeImp($1, $3);
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  | act_frm EQ act_frm
    { 
      $$ = MCmakeEq($1, $3);
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  | KWFORALL vd DOT act_frm %prec QUANTIFIER
    { 
      ATermAppl vName = ATAelementAt($2, 0);
      ATermAppl vSort = ATAelementAt($2, 1);
      $$ = MCmakeForall(vName, vSort, $4);
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  | KWEXISTS vd DOT act_frm %prec QUANTIFIER
    { 
      ATermAppl vName = ATAelementAt($2, 0);
      ATermAppl vSort = ATAelementAt($2, 1);
      $$ = MCmakeExists(vName, vSort, $4);
      if (MCdebug) {
        ATprintf( "parsed action formula\n  %t\n", $$);
      }
    }
  ;

//Regular formulas

reg_frm:
  act_frm
    {
      $$ = $1;
      if (MCdebug) {
        ATprintf( "parsed regular formula\n  %t\n", $$);
      }
    }    
  | reg_frm_woaf
    {
      $$ = $1;
    }
  ;

reg_frm_woaf: 
  PAR_OPEN reg_frm_woaf PAR_CLOSE
    { 
      $$ = $2;
    }
  | KWNIL
    { 
      $$ = MCmakeNil();
      if (MCdebug) {
        ATprintf( "parsed regular formula\n  %t\n", $$);
      }
    }
  | reg_frm DOT reg_frm
    { 
      $$ = MCmakeConcat($1, $3);
      if (MCdebug) {
        ATprintf( "parsed regular formula\n  %t\n", $$);
      }
    }
  | reg_frm PIPE reg_frm
    { 
      $$ = MCmakeChoice($1, $3);
      if (MCdebug) {
        ATprintf( "parsed regular formula\n  %t\n", $$);
      }
    }
  | reg_frm STAR
    { 
      $$ = MCmakeTrClose($1);
      if (MCdebug) {
        ATprintf( "parsed regular formula\n  %t\n", $$);
      }
    }
  | reg_frm PLUS
    { 
      $$ = MCmakeTClose($1);
      if (MCdebug) {
        ATprintf( "parsed regular formula\n  %t\n", $$);
      }
    }
  ;

//Modal formulas

mod_frm:
  form_fp_vo
    { 
      $$ = MCmakeFormRec($1);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | PAR_OPEN mod_frm PAR_CLOSE 
    { 
      $$ = $2;
    }
  | KWTRUE
    { 
      $$ = MCmakeT();
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | KWFALSE 
    { 
      $$ = MCmakeF();
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | NOT mod_frm
    { 
      $$ = MCmakeNot($2);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | mod_frm AND mod_frm
    { 
      $$ = MCmakeAnd($1, $3);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | mod_frm OR mod_frm 
    { 
      $$ = MCmakeOr($1, $3);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | mod_frm IMP mod_frm
    { 
      $$ = MCmakeImp($1, $3);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | mod_frm EQ mod_frm
    { 
      $$ = MCmakeEq($1, $3);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | KWFORALL vd DOT mod_frm %prec QUANTIFIER
    { 
      ATermAppl vName = ATAelementAt($2, 0);
      ATermAppl vSort = ATAelementAt($2, 1);
      $$ = MCmakeForall(vName, vSort, $4);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | KWEXISTS vd DOT mod_frm %prec QUANTIFIER
    { 
      ATermAppl vName = ATAelementAt($2, 0);
      ATermAppl vSort = ATAelementAt($2, 1);
      $$ = MCmakeExists(vName, vSort, $4);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | ANG_OPEN reg_frm ANG_CLOSE mod_frm %prec MAY
    { 
      $$ = MCmakeMay($2, $4);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | BR_OPEN  reg_frm BR_CLOSE  mod_frm %prec MUST  
    { 
      $$ = MCmakeMust($2, $4);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | AT PAR_OPEN reg_frm PAR_CLOSE
    { 
      $$ = MCmakeLoop($3);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }
  | KWMU fp_vd DOT mod_frm %prec QUANTIFIER
    {
      ATermAppl fpVN = ATAelementAt($2, 0);
      ATermList vdis = ATLelementAt($2, 1);
      int length = ATgetLength(vdis);
      //make list vds of variable declarations and is of initialisers
      //note that the list will be constructed in reversed order
      ATermList vds = ATmakeList0();
      ATermList is= ATmakeList0();
      for (int i = 0; i < length; i++) {
        ATermList vdi = ATLelementAt(vdis, i);
        vds = ATinsert(vds, (ATerm) MCmakeVar(ATAelementAt(vdi,0), ATAelementAt(vdi,1)));
        is  = ATinsert(is, ATelementAt(vdi,2));
      }
      //make mu application using fpVN, vds, $4 and is
      $$ = MCmakeMu(fpVN, vds, $4, is);
      if (MCdebug) {
        ATprintf( "parsed modal formula\n  %t\n", $$);
      }
    }    
  | KWNU fp_vd DOT mod_frm %prec QUANTIFIER
    {
      ATermAppl fpVN = ATAelementAt($2, 0);
      ATermList vdis = ATLelementAt($2, 1);
      int length = ATgetLength(vdis);
      //make list vds of variable declarations and is of initialisers
      //note that the list will be constructed in reversed order
      ATermList vds = ATmakeList0();
      ATermList is = ATmakeList0();
      for (int i = 0; i < length; i++) {
        ATermList vdi = ATLelementAt(vdis, i);
        vds = ATinsert(vds, (ATerm) MCmakeVar(ATAelementAt(vdi,0), ATAelementAt(vdi,1)));
        is  = ATinsert(is, ATelementAt(vdi,2));
      }
      //make nu application using fpVN, vds, $4 and is
      $$ = MCmakeNu(fpVN, vds, $4, is);
      if (MCdebug) {
        ATprintf("parsed modal formula\n  %t\n", $$);
      }
    }    
;

mod_frm_top:
  mod_frm 
    { 
      $$ = splitFormRec($1);
      if ($$ != NULL) {
        if (MCdebug) {      
          ATprintf("parsed modal formula\n  %t\n", $$);
        }
        MCtree = $$;
      }        
    }
  ;
%%

ATermAppl splitFormRec(ATermAppl form)
{
  ATermAppl result = gSplitFormRec(form, ATmakeList0());
finally:
  if (MCdebug) {
    ATprintf("(splitFormRec): return\n  %t\n", result);
  }
  return result;
}

ATermAppl gSplitFormRec(ATermAppl form, ATermList fpVnNArgs)
{
  ATermAppl result;
  AFun head = ATgetAFun(form);
  char *name = ATgetName(head);
  if (ATisQuoted(head) == ATtrue) {
    //head is quoted; this is not allowed
    throwVM0(NULL, "error: form may not contain a quoted term\n"); 
  }
  if (MCisFormRec(name)) {
    //head is a mCRL formula or a fixed point variable occurrence;
    //replace "form_rec" by "form" or "rec"
    AFun tHead = ATgetAFun(ATgetArgument(form, 0));  
    int length = ATgetLength(fpVnNArgs);
    bool found = false;                                
    for (int i = 0; i < length && !found; i++) {
      ATermList fpVnNArg = ATLelementAt(fpVnNArgs, i);
      AFun h = ATgetAFun(ATelementAt(fpVnNArg, 0));
      int n = ATgetInt(ATIelementAt(fpVnNArg, 1));
      if (strcmp(ATgetName(tHead), ATgetName(h)) == 0 && ATgetArity(tHead) == n)
      {
        found = true;
      }    
    }
    if (found) {
      result = MCmakeRec(ATAgetArgument(form, 0));
    } else {
      result = MCmakeForm(ATAgetArgument(form, 0));
    }    
  } else if (MCisForm(name) || MCisRec(name)) {
    //head is already split; return form
    result = form;
  } else if (MCisMu(name) || MCisNu(name)) {
    //head is a fixed point quantifier; perform split on the third parameter,
    //where fpVnNArgs is extended with a pair of the binding variable and the
    //number of data parameters, if it did not exist
    //make AtermList fpVnNArg that is a pair of the binding variable and the
    //number of parameters
    ATermList fpVnNArg = ATmakeList2(
      ATgetArgument(form, 0), 
      (ATerm) ATmakeInt(ATgetLength(ATgetArgument(form, 1))));
    //perform split on the third parameter, where fpVnNArgs is extended with
    //fpVnNArg
    int index = ATindexOf(fpVnNArgs, (ATerm) fpVnNArg, 0);
    ATermAppl arg2 = gSplitFormRec(
      ATAgetArgument(form, 2),
      (index == -1)?ATinsert(fpVnNArgs, (ATerm) fpVnNArg):fpVnNArgs);
    result = ATsetArgument(form, (ATerm) arg2, 2);
  } else if (MCisMay(name) || MCisMust(name)) {
    //head is a modal operator; perform split on the second parameter
    ATermAppl arg1 = gSplitFormRec(
      ATAgetArgument(form, 1),
      fpVnNArgs);
    result = ATsetArgument(form, (ATerm) arg1, 1);
  } else if (MCisLoop(name)) {
    //head is a loop operator; return form
    result = form;
  } else if (MCisForall(name) || MCisExists(name)) {
    //head is a boolean quantifier; perform split on the third parameter, where
    //the pair [first parameter,0] is removed from fpVnNArgs if it exists
    ATermList fpVnNArg = ATmakeList2(ATgetArgument(form, 0), (ATerm) ATmakeInt(0));
    ATermAppl arg2 = gSplitFormRec(
      ATAgetArgument(form, 2), 
      ATremoveElement(fpVnNArgs, (ATerm) fpVnNArg));
    result = ATsetArgument(form, (ATerm) arg2, 2);
  } else {
    //head is a boolean operator; perform split on its parameters
    ATermList args = ATmakeList0();
    int arity = ATgetArity(head);
    for (int i = 0; i < arity; i++) {
      args = ATinsert(args, 
        (ATerm) gSplitFormRec(ATAgetArgument(form, i), fpVnNArgs));
    }
    result = ATmakeApplList(head, ATreverse(args));
  }
finally:
  if (MCdebug) {
    ATprintf("(gSplitFormRec): return\n  %t\n", result);
  }
  return result;
}
