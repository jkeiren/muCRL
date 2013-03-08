/* $Id: mclexer.l,v 1.1.1.1 2004/09/07 15:06:34 uid523 Exp $ */
%{
#include <string.h>
#include "mclexer.h"
#include "mcparser.h"
#include "mcfunc.h"

//Global precondition: the ATerm library has been initialised

//global declarations
ATermAppl MCtree = NULL;         /* the parse tree */

//external declarations
int MCyyparse(void);             /* declared in mcparser.c */
extern YYSTYPE MCyylval;         /* declared in mcparser.c */
extern int fileno(FILE *stream); /* declared in stdio.h (forgotten by lex) */

//local declarations
int lineno = 1;                  /* line number in source file */
int colno  = 1;                  /* column number in source file */
void MCyyerror(char *s);         /* display error message (needed by yacc) */
int MCyywrap(void);              /* action taken after an EOF (needed by yacc) */

%}
layout        [ \t]
comment       "%".*
name          [A-Za-z0-9\^\_\'\\\-]+

%%

"("           { colno += MCyyleng; return PAR_OPEN; }
")"           { colno += MCyyleng; return PAR_CLOSE; }
"["           { colno += MCyyleng; return BR_OPEN; }
"]"           { colno += MCyyleng; return BR_CLOSE; }
"<"	      { colno += MCyyleng; return ANG_OPEN; }
">"	      { colno += MCyyleng; return ANG_CLOSE; }
","	      { colno += MCyyleng; return COMMA; }
":"	      { colno += MCyyleng; return SEMICOLON; }
"="           { colno += MCyyleng; return IS; }
"!"	      { colno += MCyyleng; return NOT; }
"&&"          { colno += MCyyleng; return AND; }
"||"          { colno += MCyyleng; return OR; }
"=>"          { colno += MCyyleng; return IMP; }
"=="          { colno += MCyyleng; return EQ; }
"."           { colno += MCyyleng; return DOT; }
"|"	      { colno += MCyyleng; return PIPE; }
"*"	      { colno += MCyyleng; return STAR; }
"+"	      { colno += MCyyleng; return PLUS; }
"@"           { colno += MCyyleng; return AT; }
"T"           { colno += MCyyleng; MCyylval.appl = MCmakeName(MCyytext); return KWTRUE; }
"F"           { colno += MCyyleng; MCyylval.appl = MCmakeName(MCyytext); return KWFALSE; }
"forall"      { colno += MCyyleng; MCyylval.appl = MCmakeName(MCyytext); return KWFORALL; }
"exists"      { colno += MCyyleng; MCyylval.appl = MCmakeName(MCyytext); return KWEXISTS; }
"nil"         { colno += MCyyleng; MCyylval.appl = MCmakeName(MCyytext); return KWNIL; }
"mu"          { colno += MCyyleng; MCyylval.appl = MCmakeName(MCyytext); return KWMU; }
"nu"          { colno += MCyyleng; MCyylval.appl = MCmakeName(MCyytext); return KWNU; }
{name}        { colno += MCyyleng; MCyylval.appl = MCmakeName(MCyytext); return RNAME; }
{layout}      { colno += MCyyleng; }
{comment}     { colno += MCyyleng; }
\r?\n         { lineno++; colno = 1; }
.             { colno += MCyyleng; MCyyerror("unknown character"); }

%%

void MCyyerror(char *s) {
  int oldcolno = colno - MCyyleng;
  if (oldcolno < 0) {
    oldcolno = 0;
  }
  fprintf(stderr, "token '%s' at position %d, %d caused the following error: %s\n", MCyytext, lineno, oldcolno, s); 
}

int MCyywrap(void) {
  return 1;
}

ATermAppl MCparse(FILE *formStream) {
  ATermAppl result = NULL;
  MCtree = NULL;
  ATprotect((ATerm*) &MCtree);
  lineno = 1;
  colno = 1;
  MCyyrestart(formStream);
  if (MCyyparse() != 0) {
    throwV(NULL);
  }
  //MCtree contains the parsed formula
  result = MCtree;
  MCtree = NULL;
finally:
  ATunprotect((ATerm*) &MCtree);
  return result;
}
