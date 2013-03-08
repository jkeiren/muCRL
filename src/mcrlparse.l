%{

/* $Id: mcrlparse.l,v 1.11 2004/05/06 09:28:26 bertl Exp $ */

#include <stdlib.h>
#include "aterm2.h"

#ifndef INITSIZE
#define INITSIZE 100
#endif
#define ESIZE 30

typedef struct {
  ATerm *e;
  int pt, size;
  } STACK;

typedef struct {
  char e[ESIZE];
  int left, right;
  }  WIN;
  
#define YY_USER_ACTION Copy2Win();

#define IsBottom(x) (ATgetType(x)==AT_LIST)
#define PushBottom(x) (PushTerm((ATerm) ATmakeList1(x)))
  
static void less(int n);

static WIN yy_win;

static char yy_msg[256], *yy_msgpt = yy_msg;

static ATbool enter_term_begin = ATfalse, enter_num_begin = ATfalse,
              enter_termlist_begin = ATfalse, enter_eq_begin = ATfalse,
              dummyHeader = ATfalse;

static ATermList yy_vars = NULL , yy_eqs = NULL , yy_sorts = NULL, 
    yy_funcs = NULL, yy_maps = NULL;

#define min(x,y) (x<=y?(x):(y));



static ATerm result = NULL;

static STACK term_s={NULL,0,0};
 
static void Enlarge(STACK *s) {
    int size = s->size;
    ATerm *e = s->e;
    if (s->pt<s->size) return;
    if (s->size == 0) s->size = INITSIZE;
    while (s->size<=s->pt) s->size *= 2;
    /* ATwarning("Enlarge old %d new %d", size, s->size); */
       if (!(s->e = (ATerm*) realloc(s->e, s->size*sizeof(ATerm))))
       ATerror("Cannot realloc enumerated sorts (%d)",s->size);
    if (e) ATunprotect(e);
    memset(s->e+size, 0, sizeof(ATerm)*(s->size - size));
    ATprotectArray(s->e, s->size);
    }

static void PushTerm(ATerm t) {
    Enlarge(&term_s);
    term_s.e[term_s.pt] = t;
    term_s.pt++;
    }
    
static ATerm PopTerm(void) {
   return term_s.e[--term_s.pt];
   }
          
static ATerm PopTermAppl(void) {
    int n;
    ATerm t;
    for (n=0, term_s.pt--;term_s.pt>=0&& !IsBottom(term_s.e[term_s.pt]);
       term_s.pt--,n++);
    t = (ATerm) ATmakeApplArray(
    ATmakeAFun(
        ATgetName(ATgetAFun(ATgetFirst((ATermList) term_s.e[term_s.pt]))), n, ATtrue),
          term_s.e + term_s.pt + 1);     
    return t;     
    }
    
static ATermList PopTermList(void) {
    ATermList r = ATempty;
    for (term_s.pt--;term_s.pt>=0;term_s.pt--)
    r = ATinsert(r, term_s.e[term_s.pt]);
    term_s.pt++;
    return r;
    }
    
static void EmptyTerm(void) {
    term_s.pt = 0;
    }
        
static ATerm TopTerm(void) {
    return term_s.pt>0?term_s.e[term_s.pt-1]:(ATerm) ATempty;
    }
            
 static void Copy2Win(void) {
    int l, n;
    char *pt = yytext;
    static ATbool skipBrace = ATfalse;
    if (dummyHeader && !strcmp(yytext,"dummy")) {
       skipBrace = ATtrue;
       }
    else
    if (skipBrace && yytext[0]=='(') skipBrace = ATfalse;
    else
    for (l = yyleng;l>0;l-= n) {
        n = min(l, ESIZE-yy_win.right);
        memcpy(yy_win.e+yy_win.right, pt, n); pt += n;
        if (yy_win.left <= yy_win.right) {
             yy_win.right = (yy_win.right + n) % ESIZE;
             if (yy_win.left == yy_win.right) yy_win.left = (yy_win.right+1) % ESIZE;
             }
         else {
             yy_win.right = (yy_win.right + n) % ESIZE;
             if (yy_win.right>=yy_win.left) yy_win.left = (yy_win.right+1) % ESIZE;
             }
        }
    }

static void ClearWin(void) {
    yy_win.left = yy_win.right = 0;
    }
        
static void PrintWin(void) {
    int i;
    yy_msgpt = yy_msg;
    yy_msgpt += sprintf(yy_msgpt, "syntax error line %d\n", yylineno);
    if (yy_win.left < yy_win.right) {
       for (i=yy_win.left+1;i<yy_win.right;i++) yy_msgpt+=sprintf(yy_msgpt, " ");
       yy_msgpt+=sprintf(yy_msgpt,"v\n");
       for (i=yy_win.left;i<yy_win.right;i++) yy_msgpt+=sprintf(yy_msgpt,"%c", yy_win.e[i]);
       }
    else {
        for (i=yy_win.left+1;i<ESIZE;i++) yy_msgpt+=sprintf(yy_msgpt, " ");
        for (i=0;i<yy_win.right;i++) yy_msgpt+=sprintf(yy_msgpt," ");
        yy_msgpt+=sprintf(yy_msgpt,"v\n");
        for (i=yy_win.left;i<ESIZE;i++) yy_msgpt+=sprintf(yy_msgpt, "%c", yy_win.e[i]);
        for (i=0;i<yy_win.right;i++) yy_msgpt+=sprintf(yy_msgpt, "%c", yy_win.e[i]); 
        }
    }
    
static void Error(char *lah) {
    if (dummyHeader) lah[strlen(lah)-1]='\0';
    ATwarning("%s%s", yy_msg, lah);
    }
        
%}
%option noyywrap
%option yylineno
%option stack
%option never-interactive
%option outfile="mcrlparse.h"
%option prefix="mcrl"
KEYWORD   "proc"|"comm"|"func"|"map"|"act"|"init"|"sort"|"rew"|"var"
ID [[:alnum:]^\-_']*[[:alnum:]^_']
SKIP [[:alnum:]^\-_'#<|>,:+.()={}]
NUM [[:digit:]]+
%x sort
%x func
%x map
%x rew
%x var
%x term_begin
%x term_list_begin
%x term_finished
%x term
%x term_next
%x term_next_id
%x term_end
%x term_list
%x var_next
%x var_next_id
%x sort_id
%x func_next
%x func_next_id
%x type
%x type_next
%x type_next_id
%x type_id
%x error
%x keys
%x nextvars
%x sortname
%x rew2
%x term1
%x term2
%x skip
%x term3
%x term4
%x num_list
%x num_next_in
%x num_next_id
%x num_begin
%x num_next
%x eq_begin
%%


    
  
        if (enter_term_begin) BEGIN(term_begin);
        if (enter_termlist_begin) BEGIN(term_list_begin);
        if (enter_num_begin) BEGIN(num_begin);
        if (enter_eq_begin) BEGIN(eq_begin);
        
<skip,sort,func,map,var,rew>{KEYWORD} {
       yy_pop_state(); yy_pop_state();
       yyless(0);
       }
                     
 <INITIAL>{
          "sort"   {yy_push_state(sort);yy_push_state(sort);}
          "func"   {yy_push_state(func);yy_push_state(func);}
          "map"    {yy_push_state(map);yy_push_state(map);}
          "var"    {
                   yy_vars = ATempty;
                   EmptyTerm();
                   yy_push_state(var);yy_push_state(var);
                   }
          "rew"    {yy_push_state(rew);yy_push_state(rew);}
         {KEYWORD} {yy_push_state(skip);yy_push_state(skip);}
 }

<sort>{ID}   {
             yy_sorts = ATinsert(yy_sorts, ATmake("<str>", yytext));
             }
                
<eq_begin>{
          "var"     {
                   yy_vars = ATempty;
                   EmptyTerm();
                   yy_push_state(var);yy_push_state(var);
                   }
         "rew"     {yy_push_state(rew);yy_push_state(rew);}
         {KEYWORD} {yy_push_state(skip);yy_push_state(skip);}
}

<term_begin>{ID} { 
          PushTerm(ATmake("<str>", yytext));
          BEGIN(term_finished); 
          yy_push_state(term);
          }
          
<term_list_begin>{ID} { 
          PushTerm(ATmake("<str>", yytext));
          yy_push_state(term4); 
          yy_push_state(term);
          }
                                      
<rew>{ID} {   
          PushTerm(ATmake("<str>", yytext));
          BEGIN(term1);yy_push_state(term);
          }
          
<var>{ID} {
          PushTerm(ATmake("<str>", yytext));
          BEGIN(var_next);
          } 

<func>{ID} {
          PushTerm(ATmake("<str>", yytext));
          BEGIN(func_next);
          }
          
<map>{ID} {
          PushTerm(ATmake("<str>", yytext));
          BEGIN(func_next);
          }
          
 /* ----------- BEGIN FUNC -------------------------------------------------- */
 /* <INIT>:           'func' func
    <func,func_next_id>: ID func_next
    <func_next>:        ',' func_next_id
                       ':' type
 */
        
<func_next_id>{ID} {
          PushTerm(ATmake("<str>", yytext)); 
          BEGIN(func_next);
          }

<func_next>{[,]   {BEGIN(func_next_id);}
            [:]   {BEGIN(type);}
}                    
                            
<type>{
      {ID} {
          result = (ATerm) PopTermList();
          PushTerm(ATmake("<str>", yytext));
          BEGIN(type_next);
          }
      "->"   {
             result = (ATerm) PopTermList();
             BEGIN(type_id);}
      }                            
 /* ----------------------------- T E R M -------------------------------- */

 /*  <INIT>:               ID term
    <term,term_next>:     '('term_list
    <term_list>:          ID term_next
    <term_next,term_end>: ')' term_end
                          ',' term_next_id
    <term_next_id>:       ID term_next
 */
                  
 <term,term_next>[(] {
             BEGIN(term_list);
             }
                                                      
<term_list>{ID} {
              ATerm t = ATmake("<str>", yytext);
              PushBottom(PopTerm());
              PushTerm(t);
              yy_push_state(term_next);
              }
                                       
<term_next,term_end>{[)] {
                   ATerm t = PopTermAppl();
                   PushTerm(t);
                   yy_pop_state();
                   if (yy_top_state()==term_list) BEGIN(term_end);
                   else {
                        yy_pop_state();}      
                   }

                    [,] {
                        BEGIN(term_next_id);
                        } 
}
                                          
<term_next_id>{ID}  {
            PushTerm(ATmake("<str>", yytext));
            BEGIN(term_next);
            }        
              
<term_finished>{. |
                <<EOF>> {
                 result = TopTerm();
                 /* ATwarning("R = %t\n", result); */
                 yyterminate();
                 }
}


 /* ----------- END TERM -------------------------------------------------- */
 
 /* ----------- BEGIN REW -------------------------------------------------- */
 
 /* <rew>:     ID <term> <term1> = <rew2> ID <term> <term2> */
 
<term1>[=]    {BEGIN(rew2);}

            
<rew2>{ID} {  
            PushTerm(ATmake("<str>", yytext));
            BEGIN(term2);yy_push_state(term);
            }
                        
                                 
 /* ----------- BEGIN VAR -------------------------------------------------- */
 /* <INIT>:           'var' var
    <var,var_next_id>: ID var_next
    <var_next>:        ',' var_next_id
                       ':' sort_id
    <sort_id>:         ID <var>
 */
        
<var_next_id>{ID} {
          PushTerm(ATmake("<str>", yytext)); 
          BEGIN(var_next);
          }

<var_next>{[,]   {BEGIN(var_next_id);}
           [:]   {BEGIN(sort_id);}
}

<sort_id>{ID}   {
                ATermList ts = PopTermList(), r = ATempty;
                ATerm sortstring = ATmake("<str>", yytext);
                for (;!ATisEmpty(ts);ts=ATgetNext(ts)) {
                    ATerm name = ATgetFirst(ts);
                    r = ATinsert(r, ATmake("v(<term>,<term>)",
                        name, sortstring)); 
                    }
                yy_vars = ATconcat(yy_vars, ATreverse(r));
                /* ATwarning("V= %t\n", yy_vars); */
                BEGIN(yy_top_state());
                }
                
 /* ----------- BEGIN TYPE -------------------------------------------------- */
 /* <INIT>:           ':' type
    <type,type_next_id>: ID type_next
    <type_next>:        "#" type_next_id
                       "->" type_id
    <type_id>:         ID <func>
 */
        
<type_next_id>{ID} {
          PushTerm(ATmake("<str>", yytext)); 
          BEGIN(type_next);
          }

<type_next>{[#]   {BEGIN(type_next_id);}
           "->"   {BEGIN(type_id);}
                   
}

<type_id>{ID}   {
                ATermList ts = PopTermList();
                ATerm sortstring = ATmake("<str>", yytext);
                ATermList funcs = (ATermList) result; 
                for (;!ATisEmpty(funcs);funcs = ATgetNext(funcs)) {
                   if (yy_top_state()==func)
                   yy_funcs = ATinsert(yy_funcs, ATmake("f(<term>,<term>, <term>)",
                              ATgetFirst(funcs), ts , sortstring));
                   else
                   yy_maps = ATinsert(yy_maps, ATmake("f(<term>,<term>, <term>)",
                              ATgetFirst(funcs), ts , sortstring)); 
                   }
                BEGIN(yy_top_state());
                }
                
  /* Format 2,4,5-6,5,7-10 : term */

                          
<num_begin>{NUM} {
          int n;
          sscanf(yytext,"%d", &n);
          PushTerm((ATerm) ATmakeInt(n));
          yy_push_state(num_next);
          }
          
<num_next_id>{NUM} {
          int n;
          sscanf(yytext,"%d", &n);
          PushTerm((ATerm) ATmakeInt(n)); 
          BEGIN(num_next);
          }
          
<num_next_in>{NUM} {
          int n = ATgetInt((ATermInt)TopTerm()), i, m;
          sscanf(yytext,"%d", &m);
          for (i=n;i<=m;i++)
              PushTerm((ATerm) ATmakeInt(i)); 
          BEGIN(num_next);
          }
                              
<num_next>{[,]   {BEGIN(num_next_id);}
           [-]   {BEGIN(num_next_in);}
           [:]   {BEGIN(num_list);}
          }
          
<num_list>{ID}   {
                ATermList ts = PopTermList();
                ATerm sortstring = ATmake("<str>", yytext);
                for (;!ATisEmpty(ts);ts=ATgetNext(ts)) {
                    ATerm name = ATgetFirst(ts);
                    yy_vars = ATinsert(yy_vars, name); 
                    }
                yy_vars = ATreverse(yy_vars);  
                PushTerm(ATmake("<str>", yytext));
                BEGIN(term3);yy_push_state(term);
                }
                                                     
<skip>{SKIP}*

<error>{[\n] | 
        .{1,10} | 
         <<EOF>> { 
              Error(yytext);return(1);
              }
}
                    
<*>[[:blank:]]*

<*>%[^\n]*

<*>[\n]      {ClearWin();}

<term>{. {less(0);yy_pop_state();}
       <<EOF>>  {
            if (yy_top_state()==term2) { 
                yy_eqs = ATinsert(yy_eqs, ATmake("e(<list>)", 
                   ATinsert(PopTermList(), (ATerm) yy_vars)));
                }
            if (yy_top_state()==term3) { 
                ATerm t = PopTerm();
                t = ATsetAnnotation(t, MCRLtag, (ATerm) yy_vars);
                yy_eqs = ATinsert(yy_eqs, t);
                yy_vars = ATempty;
                }
            if (yy_top_state()==term4) { 
                ATerm t = PopTerm();
                yy_eqs = ATinsert(yy_eqs, t);
                }
            if (yy_top_state()==term_finished) {
                  result = PopTerm();
                  /* ATwarning("R = %t\n", result); */
                  }
            yyterminate();
            }
}

<term2>{.    {
            yy_eqs = ATinsert(yy_eqs, ATmake("e(<list>)", 
               ATinsert(PopTermList(), (ATerm) yy_vars)));
            less(0);BEGIN(yy_top_state());
            }
        <<EOF>> { 
                yy_eqs = ATinsert(yy_eqs, ATmake("e(<list>)", 
                   ATinsert(PopTermList(), (ATerm) yy_vars)));
                yyterminate();
                }
}
<term3>{.   { /* Belongs to num_list */
            ATerm t = PopTerm();
            t = ATsetAnnotation(t, MCRLtag, (ATerm) yy_vars);
            yy_eqs = ATinsert(yy_eqs, t);
            yy_vars = ATempty;
            less(0);yy_pop_state();
            }
        <<EOF>> { 
                ATerm t = PopTerm();
                t = ATsetAnnotation(t, MCRLtag, (ATerm) yy_vars);
                yy_eqs = ATinsert(yy_eqs, t);
                yy_vars = ATempty;
                less(0);yy_pop_state();
                yyterminate();
                }
}

<term4>{.   { /* Belongs to term_list_begin */
            ATerm t = PopTerm();
            yy_eqs = ATinsert(yy_eqs, t);
            less(0);yy_pop_state();
            }
        <<EOF>> { 
                ATerm t = PopTerm();
                yy_eqs = ATinsert(yy_eqs, t);
                less(0);yy_pop_state();
                yyterminate();
                }
}                          
<*>.         {PrintWin();BEGIN(error);}
 
 

 /* [[:space:]]+/({KEYWORD})[[:space:]] {yymore(); r = ATinsert(r, ATmake("<str>", yytext));}
    [[:space:]]+[[:alnum:]]+  | 
    ^[[:alnum:]]+  {yymore();} */
%%


    
static void less(int n) {
    yy_win.right = (yy_win.right - yyleng + n) % ESIZE;
    yyless(n);
    }
    
static ATerm ParseFile(FILE *fp) {
    yyrestart(fp);
    enter_term_begin = ATtrue;
    if (!result) ATprotect((ATerm*) &result); 
    result = (ATerm) ATempty;
    ClearWin();
    yylex();
    return ATisEqual(result, ATempty)?NULL:result;
    }
    
static ATermList Parse2File(FILE *fp) {
    yyrestart(fp);
    enter_termlist_begin = ATtrue;
    if (!result) ATprotect((ATerm*) &result); 
    result = (ATerm) ATempty;
    ClearWin();
    yy_eqs = ATempty;
    if (yylex()) return NULL;
    return ATreverse(yy_eqs);
    }
     
static ATerm Parse(char *buf) {
    YY_BUFFER_STATE s;
    enter_term_begin = ATtrue;
    if (!result) ATprotect((ATerm*) &result); 
    result = (ATerm) ATempty;
    ClearWin();
    s = yy_scan_string(buf);
    if (yylex()) return NULL;
    yy_delete_buffer(s);
    return ATisEqual(result, ATempty)?NULL:result;
    }
    
static ATermList Parse2(char *buf) {
    char *buffer = (char*) malloc((strlen(buf)+10)*sizeof(char));
    YY_BUFFER_STATE s;
    if (!buffer) return NULL;
    enter_term_begin = ATtrue;
    sprintf(buffer,"dummy(%s)",buf);
    dummyHeader = ATtrue;
    if (!result) ATprotect((ATerm*) &result); 
    result = (ATerm) ATempty;
    ClearWin();
    s = yy_scan_string(buffer);
    yy_eqs = ATempty;
    if (yylex()) return NULL;
    yy_delete_buffer(s);
    free(buffer);
    return ATisEqual(result, ATempty)?NULL:(ATermList) ATgetArguments(
    (ATermAppl) result);
    }
    
static ATerm ParseAdt(FILE *fp) {
    yyrestart(fp);
    if (!result) ATprotect((ATerm*) &result); 
    if (!yy_vars) ATprotect((ATerm*) &yy_vars);
    if (!yy_eqs) ATprotect((ATerm*) &yy_eqs);
    if (!yy_sorts) ATprotect((ATerm*) &yy_sorts);
    if (!yy_maps) ATprotect((ATerm*) &yy_maps);
    if (!yy_funcs) ATprotect((ATerm*) &yy_funcs);
    result = (ATerm) ATempty;
    yy_eqs =  ATempty;
    yy_vars = ATempty;
    yy_sorts = ATempty;
    yy_maps = ATempty;
    yy_funcs = ATempty;
    ClearWin();
    if (yylex()) exit(1);
    result = ATmake("d(s(<term>,<term>,<term>),<term>)", 
         ATreverse(yy_sorts), 
         ATreverse(yy_funcs), 
         ATreverse(yy_maps), ATreverse(yy_eqs));
    /* ATwarning("Result = %t", result); */
    return result;
    }
    
static ATermList ParseEqs(FILE *fp) {
    yyrestart(fp);
    enter_eq_begin = ATtrue;
    if (!result) ATprotect((ATerm*) &result); 
    if (!yy_vars) ATprotect((ATerm*) &yy_vars);
    if (!yy_eqs) ATprotect((ATerm*) &yy_eqs);
    result = (ATerm) ATempty;
    yy_eqs = ATempty;
    yy_vars = ATempty;
    ClearWin();
    if (yylex()) exit(1);
    return ATreverse(yy_eqs);
    }

static ATermList ParseConditions(FILE *fp) {
    yyrestart(fp);
    enter_num_begin = ATtrue;
    if (!result) ATprotect((ATerm*) &result); 
    if (!yy_vars) ATprotect((ATerm*) &yy_vars);
    if (!yy_eqs) ATprotect((ATerm*) &yy_eqs);
    result = (ATerm) ATempty;
    yy_eqs = ATempty;
    yy_vars = ATempty;
    ClearWin();
    if (yylex()) exit(1);
    return ATreverse(yy_eqs);
    }
    
#ifndef MCRL_H            
main(int argc, char *argv[]) {
    ATinit(argc, argv, (ATerm*) &argc);
    ATfprintf(stderr, "Result = %t\n", ParseEqs(stdin));
    }
#endif
