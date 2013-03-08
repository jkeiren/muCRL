%{

#include <stdlib.h>

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
#define YY_DECL int lexscan(void)

#define IsBottom(x) (ATgetType(x)==AT_LIST)
#define PushBottom(x) (PushTerm((ATerm) ATmakeList1(x)))
  
static void less(int n);

static WIN yy_win;

static char yy_msg[256], *yy_msgpt = yy_msg;

static int pos = 0;

#define min(x,y) (x<=y?(x):(y));



static ATerm result = NULL;
static ATermList rlist = NULL;
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
    pos += strlen(yytext);
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
    
static int Error(char *lah) {
    ATerror("%s%s", yy_msg, lah);
    }
        
%}
%option noyywrap
%option yylineno
%option stack
%option outfile="edit.h"
%option never-interactive
%option prefix="edit"
ID [#[:alnum:]^\-_']*[[:alnum:]^_']
IMPLIES "->"
IFF "<|"
%x term_next
%x term_next_id
%x term_end
%x term_list
%x line
%x oldvalue
%x newvalue
%x oldvaluef
%x newvaluef
%x value
%x valuef
%x condition
%x conditionf
%x error
%%

   BEGIN(line); 

<line>{{ID} {
          if (result!=NULL) {
             result = ATmake("r(<list>)",PopTermList());
             /* ATfprintf(stderr,"put %t\n", result); */
             rlist = ATinsert(rlist, result);
             }
          less(0);
          /* fprintf(stderr,"start %s\n", yytext); */
          result = (ATerm) ATempty;
          yy_push_state(oldvalue);
          }
          <<EOF>>  {
                result = ATmake("r(<list>)",PopTermList());
                if (ATgetArity(ATgetAFun(result))==0) 
                   ATerror("<edit file> is empty");
                rlist = ATinsert(rlist, result);
                /* ATfprintf(stderr,"%t: put %t\n", rlist, result); */
                yyterminate();
                }
       }
       

<oldvaluef>{IMPLIES} {
                BEGIN(newvalue);
                }

<newvaluef>{{IFF} {
                BEGIN(condition);
                }
            {ID} {less(0); 
                  yy_pop_state();
                  /* PushTerm(MCRLterm_true); */
                  }
           <<EOF>> {
                  yy_pop_state();
                  /* PushTerm(MCRLterm_true); */
                  }
           } 
           
<condition>{ID} {
           PushTerm(ATmake("<str>", yytext));
           BEGIN(conditionf);
           }
           
<conditionf>[=] {
           BEGIN(value);
           }
           
<valuef>{
            {ID} {less(0); 
                  yy_pop_state();
                  }
           [&]  {BEGIN(condition);}
           <<EOF>> {
                  yy_pop_state();
                  }
           }
                                 
<value,newvalue,oldvalue>{ID} {
       PushTerm(ATmake("<str>", yytext));
       if (YYSTATE == value) BEGIN(valuef);
       if (YYSTATE == oldvalue) BEGIN(oldvaluef);
       if (YYSTATE == newvalue) BEGIN(newvaluef);
       }
                                   
<valuef,newvaluef,oldvaluef,term_next>[(] {
             /* fprintf(stderr,"term %s\n", yytext); */
             
             yy_push_state(term_list);
             }
                                                      
<term_list>{ID} {
              ATerm t = ATmake("<str>", yytext);
              /* fprintf(stderr,"term_list %s\n", yytext); */
              PushBottom(PopTerm());
              PushTerm(t);
              yy_push_state(term_next);
              }
                                       
<term_next,term_end>{[)] {
                   ATerm t = PopTermAppl();
                   /* fprintf(stderr,"term_next term_end %s\n", yytext); */
                   PushTerm(t);
                   yy_pop_state();
                   if (yy_top_state()==term_list) BEGIN(term_end);
                   else {
                        yy_pop_state();}     
                   }

                    [,] {
                        /*fprintf(stderr,"term_next term_end %s\n", yytext); */
                        BEGIN(term_next_id);
                        } 
}
                                          
<term_next_id>{ID}  {
            PushTerm(ATmake("<str>", yytext));
            /* fprintf(stderr,"term_next term_end %s\n", yytext); */
            BEGIN(term_next);
            }        
              


 /* ----------- END TERM -------------------------------------------------- */
                                                     


<*>[[:blank:]]*                    

<*>%[^\n]*

<*>[\n]      {ClearWin();}

       

<*>.         {PrintWin();BEGIN(error);}
 
<error>{[\n] | 
        .{1,10} | 
         <<EOF>> { 
              return Error(yytext);
              }
       }
%%


    
static void less(int n) {
    yy_win.right = (yy_win.right - yyleng + n) % ESIZE;
    yyless(n);
    }
    
static ATermList ParseFile(FILE *f) {
    static ATbool first = ATtrue;
    yyrestart(f);
    result = NULL;
    rlist = ATempty;
    if (first) {
      ATprotect((ATerm*) &result);
      ATprotect((ATerm*) &rlist);  
      first = ATfalse;
      } 
    ClearWin();
    if (lexscan()) exit(1);
    // ATwarning("QQQ %t", ATreverse(rlist));
    // exit(1);
    return ATreverse(rlist);
    }
   

