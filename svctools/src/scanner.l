%{
/* $Id: scanner.l,v 1.4 2004/01/29 13:41:38 bertl Exp $ */

#ifdef __cplusplus
extern "C" {
#endif 

#include <stdlib.h>
#include <string.h>
#include "aterm2.h"
#include "y.tab.h"
#ifdef __cplusplus
}
#endif 

static ATbool des = ATfalse, act = ATfalse;
static int level = 0;
static char *id = NULL;
%}
%option noyywrap
%option stack
%x action

DECIMALDIGIT      [0-9]
LETTER            [A-Za-z]
ID                [^[:blank:],()]+
SIGN              "+"|"-"
DECIMALINT        ({SIGN})?{DECIMALDIGIT}+

%%
    if (act) BEGIN(action); else BEGIN(INITIAL);
    
{DECIMALINT}      {yylval.decint=atoi(yytext);
                   return DECIMALINT;}
<action>{ID}      {strcat(id, yytext); 
                   /* fprintf(stderr, "Q:%s\n", id);*/
                  }
<action>"("      {level++;strcat(id, yytext);}
<action>")"      {level--;strcat(id, yytext);}
<INITIAL>"("      {return '(';}
<INITIAL>")"      {des = ATfalse; return ')';}
<INITIAL>","      {if (!des) {
                     id[0]='\0';
                     level = 0;
                     act = ATtrue;
                     }
                     return ',';
                  }
<action>","       {if (level==0) {
                        act = ATfalse;
                        yylval.string = id;
                        return ID;
                        }
                   else {
                      strcat(id, yytext);
                      }
                   }                 
"des"             {des = ATtrue; id = 
                     (char*) malloc(1024*sizeof(char)); 
                      return DES;}
"i"               {return TAU;}
[\t\n ]+          ;
.                 {return 0;}
%%
void yyerror(char *msg){
   fprintf(stderr, "%s:%s\n", msg, yytext);
}
