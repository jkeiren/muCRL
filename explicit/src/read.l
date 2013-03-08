%{

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
  int left, right, empty;
  }  WIN;
  
#define YY_DECL int lexreadscan(void)
#define YY_USER_ACTION Copy2Win();


#define IsBottom(x) (ATgetType(x)==AT_LIST)
#define PushBottom(x) (PushTerm((ATerm) ATmakeList1(x)))

static void less(int n);
static WIN yy_win;
static char yy_msg[256], *yy_msgpt = yy_msg;
static void Wrap(int all);
static ATerm result; 

static AFun Plus, Minus, Times, Div, Mod, Min;
static STACK term_s={NULL,0,0};

#define min(x,y) (x<=y?(x):(y));

static void Enlarge(STACK *s) {
    int size = s->size;
    ATerm *e = s->e;
    if (s->pt<s->size) return;
    if (s->size == 0) s->size = INITSIZE;
    while (s->size<=s->pt) s->size *= 2;
    /* ATwarning("Enlarge old %d new %d", size, s->size); 
    ATwarning("Realloc %d\n", s->size); */
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
static ATerm TopTerm(void) {
    return term_s.pt>0?term_s.e[term_s.pt-1]:(ATerm) ATempty;
    }
 
 static void ClearWin(void) {
    yy_win.left = yy_win.right = 0;
    yy_win.empty = 1;
    }
               
 static void Copy2Win(void) {
    int l, n;
    char *pt = yytext;
    if (yy_win.empty==1) yy_win.empty = 0;
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
        
static void PrintWin(void) {
    int i;
    yy_msgpt = yy_msg;
    yy_msgpt += sprintf(yy_msgpt, "syntax error line %d\n", yylineno);
    if (yy_win.empty || yy_win.left < yy_win.right) {
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
    ATwarning("%s%s", yy_msg, lah);
    return 0;
    }
    

/* KEYWORD "APPLICATION"|"DIRECT INPUT SECTION"|"OUTPUT SECTION"| \
     "CODE SYSTEM SECTION"|"CURRENT RESULT SECTION"| \
     "SELF-LATCHED PARAMETER SECTION"|"TIMER EXPRESSION RESULT SECTION"| \
     "BOOLEAN EQUATION SECTION"|"APPLICATION"|"TIME"| \
     "END BOOLEAN EQUATION SECTION"
*/        
%}

%option noyywrap
%option yylineno
%option stack
%option never-interactive
%option outfile="read.h"
%option prefix="detailed"
ID [[:alnum:]^\-_']+

%x term
%x signed_term
%x next
%x times
%x div
%x mod
%x plus
%x minus
%x expr
%x error
%%



  /* ----------------------------- T E R M -------------------------------- */

 /* 
   <start_term>:          signed_term 
   <signed_term>:         "~" signed_term
   <signed_term>:         term
   <signed_term>:         "(" expr
   <expr>:                signed_term
   <term>:                ID next
   <next>:                "*" times
   <next>:                "/" div
   <next>:                "%" mod
   <times>:               signed_term
   <div>:                 signed_term
   <mod>:                 signed_term
   <next>:                "+" plus
   <next>:                "~" minus
   <plus>:               signed_term
   <minus>:              signed_term
   <next>:               ")" next
 */ 

<INITIAL>.   {
    less(0);
    yy_push_state(signed_term);
    }

<*>[\n]  {ClearWin();}
   
<signed_term>{[~]      {yy_push_state(signed_term);}
	      [(]  {less(0);BEGIN(expr);}
              {ID}  {
                  less(0);
                  BEGIN(term);
                  }
	     }

<expr>[(]               {yy_push_state(signed_term);}

<term>{ID}              {
                        char *endptr;
                        long d = strtol(yytext, &endptr, 0);
                        if (*endptr) {
                          ATerm t = MCRLtranslate(ATmake("<str>", yytext));
                          if (t) {
                              if (MCRLgetSort(t)) {
                              char *s = ATgetName(MCRLgetSort(t));
                              if (strcmp(s, "Nat") && strcmp(s, "Pos")) { 
                        ATwarning(
                        "Variable \"%t\" (sort %s) must have sort Nat or Pos\n",
                               MCRLprint(t), s);
                               yyterminate();
                               }
                              } else {yyterminate();}
                              PushTerm(t);  
                         } else {yyterminate();} 
                        }
                        else PushTerm(ATmake("<int>", d));
                        
                        while (yy_top_state()==signed_term) {
                           yy_pop_state();
			   PushTerm((ATerm) ATmakeAppl1(Min, PopTerm()));
		           }
		        BEGIN(next);
			}

<next>{[\*]  {
            less(0);
            BEGIN(times);
	    }
       [/]  {
            less(0);
            BEGIN(div);
	    }
       [%]  {
            less(0);
            BEGIN(mod);
	    }
       [+] {
	    less(0);
            BEGIN(plus);
	    }
       [~] {
	    less(0);
            BEGIN(minus);
	    }
       [)] {
	   Wrap(1);
	   yy_pop_state();
	   BEGIN(next);
	   }
       <<EOF>> {
	   Wrap(1);
           if (yy_top_state()!=INITIAL) {
                PrintWin();BEGIN(error);
                }
           else {
	     result = TopTerm(); 
             /* ATwarning("R = %t\n", result); */
             yyterminate(); 
             }
          }   
       } 

<times,mod,div>[*/%] {
             // ATwarning("times");
             int s = YYSTATE;
             Wrap(0);
             BEGIN(s);
             yy_push_state(signed_term);
             }        

<plus,minus>[~+] {
             // ATwarning("plus");
             int s = YYSTATE;
             Wrap(1);
             BEGIN(s);
             yy_push_state(signed_term);
             }


      	                                             		
<*>[[:blank:]]*

       
  /* ----------- END TERM -------------------------------------------------- */                                


<*>.         {PrintWin();BEGIN(error);}
 
<error>{[\n] |
        .{1,30} | 
         <<EOF>> { 
              return Error(yytext);
              }
       }
%%



static void less(int n) {
    yy_win.right = (yy_win.right - yyleng + n) % ESIZE;
    yyless(n);
    }
    
static void Wrap(int all) {
   while (yy_top_state()==times || yy_top_state()==div || yy_top_state()==mod) {
           ATerm t2 = PopTerm(),
	         t1 = PopTerm();
           switch (yy_top_state()) {
	      case times: PushTerm((ATerm) ATmakeAppl2(Times, t1, t2)); break;
              case div: PushTerm((ATerm) ATmakeAppl2(Div, t1, t2)); break;
              case mod: PushTerm((ATerm) ATmakeAppl2(Mod, t1, t2)); break;
              }
           yy_pop_state();	           
	   }
   if (all)
   while (yy_top_state()==plus || yy_top_state()==minus) {
      ATerm t2 = PopTerm(),
            t1 = PopTerm();
      switch (yy_top_state()) {
        case plus: PushTerm((ATerm) ATmakeAppl2(Plus, t1, t2));	break;
        case minus: PushTerm((ATerm) ATmakeAppl2(Minus, t1, t2)); break;
        }
    yy_pop_state();
    }
}

static ATerm ParseFile(FILE *f) {
    yyrestart(f);
    Plus = ATmakeAFun("plus", 2, ATfalse);ATprotectSymbol(Plus);
    Minus = ATmakeAFun("minus", 2, ATfalse);ATprotectSymbol(Minus);
    Times = ATmakeAFun("times", 2, ATfalse);ATprotectSymbol(Times);
    Div = ATmakeAFun("div", 2, ATfalse);ATprotectSymbol(Div);
    Mod = ATmakeAFun("mod", 2, ATfalse);ATprotectSymbol(Mod);
    Min = ATmakeAFun("min", 1, ATfalse);ATprotectSymbol(Min);
    result = NULL; ATprotect((ATerm*) &result);
    ClearWin();
    lexreadscan();
    return result;
    }
