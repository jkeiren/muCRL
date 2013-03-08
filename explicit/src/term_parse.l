%{
/* $Id: term_parse.l,v 1.2 2005/01/25 14:53:00 uid523 Exp $ */

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
#define YY_DECL int lexscan(tdb_t tdb, int n)
#define YY_INPUT(buf,result,max_size) \
      if ( ((result = GZread(yyin, buf, max_size)) == 0) && !GZeof(yyin)) \
      YY_FATAL_ERROR( "input in flex scanner failed" );
#define IsBottom(x) (ATgetType(x)==AT_LIST)
#define PushBottom(x) (PushTerm((ATerm) ATmakeList1(x)))
  
static void less(int n);

static WIN yy_win;

static char yy_msg[256], *yy_msgpt = yy_msg;

static int pos = 0, pos0 = 0;

#define min(x,y) (x<=y?(x):(y));



static ATerm result = NULL;
static int cnt = 0;
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
    pos += yyleng;
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
    return mkerror(ERR_PARSE, "%s%s", yy_msg, lah);
    }
        
%}
%option noyywrap
%option yylineno
%option stack
%option outfile="term_parse.h"
%option never-interactive
%option prefix="tdb"
ID [[:alnum:]^\-_']*[[:alnum:]^_']
STRING \"[^"]*\"
%x term_begin
%x term
%x term_next
%x term_next_id
%x term_end
%x term_list
%x error
%%
   pos = 0;
   BEGIN(term); 

<term>{
      {STRING} {
          if (result!=NULL) {
             int new;
             result = PopTerm();
             /* ATfprintf(stderr,"put %t\n", result); */
             DBput(tdb, result, &new);
             cnt++;
             if (cnt == n) return pos0;
             }
          if (yytext[yyleng-1]=='"') {
             yytext[yyleng-1]='\0';
             PushTerm(ATmake("<str>", yytext+1));
             } 
          else
             PushTerm(ATmake("<str>", yytext));
          /* fprintf(stderr,"start %s\n", yytext); */
          result = (ATerm) ATempty;
          }
     {ID} {
          if (result!=NULL) {
             int new;
             result = PopTerm();
             /* ATfprintf(stderr,"put %t\n", result); */
             DBput(tdb, result, &new);
             cnt++;
             if (cnt == n) return pos0;
             }
          PushTerm(ATmake("<str>", yytext)); 
          /* fprintf(stderr,"start %s\n", yytext); */
          result = (ATerm) ATempty;
          }
          <<EOF>>  {
                int new;
		if (pos0==pos) {
                  result = PopTerm();
                  DBput(tdb, result, &new);
                  cnt++;
                  /* ATfprintf(stderr,"put %t\n", result); */
		  } 
		return pos0;
                // yyterminate();
                }
       }
                            
<term,term_next>[(] {
             /* fprintf(stderr,"term %s\n", yytext); */
             yy_push_state(term_list);
             }
                                                      
<term_list>{
           {STRING}  {
              PushBottom(PopTerm());
              if (yytext[yyleng-1]=='"') {
                  yytext[yyleng-1]='\0';
                  PushTerm(ATmake("<str>", yytext+1));
                  }
              /* fprintf(stderr,"term_list %s\n", yytext); */
              else
              PushTerm(ATmake("<str>", yytext));
              yy_push_state(term_next);
	    }
           {ID} {
              ATerm t = ATmake("<str>", yytext);
              /* fprintf(stderr,"term_list %s\n", yytext); */
              PushBottom(PopTerm());
              PushTerm(t);
              yy_push_state(term_next);
              }
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
                                          
<term_next_id>{
           {STRING}  {
           if (yytext[yyleng-1]=='"') {
               yytext[yyleng-1]='\0';
               PushTerm(ATmake("<str>", yytext+1));
               } else
            PushTerm(ATmake("<str>", yytext));  
            /* fprintf(stderr,"term_next term_end %s\n", yytext); */
            BEGIN(term_next);
	    }
           {ID}  {
            PushTerm(ATmake("<str>", yytext));
            /* fprintf(stderr,"term_next term_end %s\n", yytext); */
            BEGIN(term_next);
            }        
            }
              


 /* ----------- END TERM -------------------------------------------------- */
                                                     


<*>[[:blank:]]*                    

<*>[\n]      {ClearWin();pos0 = pos;}

       

<*>.         {PrintWin();BEGIN(error);}
 
<error>{[\n] | 
        .{1,10} | 
         <<EOF>> { 
              return pos0;
              }
       }
%%


    
static void less(int n) {
    yy_win.right = (yy_win.right - yyleng + n) % ESIZE;
    yyless(n);
    }
    
static int ParseFile(GZfile f, tdb_t tdb, int n) {
    char b[2], *s = GZgets(f, b, 2);  
    if (GZeof(f)) return 0;
    GZrewind(f);
    yyrestart(f);
    result = NULL; cnt = 0;
    ATprotect((ATerm*) &result); 
    ClearWin();
    return lexscan(tdb, n);
    }
   

