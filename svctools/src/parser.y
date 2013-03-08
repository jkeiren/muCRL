%{
/* $Id: parser.y,v 1.4 2004/04/05 09:18:32 sen2gst Exp $ */

#include <stdio.h>
#include <string.h>
#include "aterm2.h"
#include <time.h>
#include "svc.h"

extern char yytext[];
extern SVCfile outFile;
extern char *outFilename;
extern char *programName;

SVCparameterIndex parameter;
SVClabelIndex label;
SVCstateIndex fromState, toState;
SVCbool       _new;

char buffy[256];
time_t now;

%}
%union{
    char  *string;
    long  decint;
}
%token '(' ')' ','
%token <string> ID
%token <decint> DECIMALINT
%token <string> TAU
%token DES
%type  <string> label
%start aut
%%
aut     : header body;
header  : DES '(' DECIMALINT ',' DECIMALINT ',' DECIMALINT ')' {
                SVCsetInitialState(&outFile, SVCnewState(&outFile, (ATerm)ATmakeInt($3), &_new));
                SVCsetCreator(&outFile, "aut2svc");
             }
          ;
body    :       
          | body transition 
          ;
transition: '(' DECIMALINT ',' label DECIMALINT ')' {

                /* Registrate labels and states */

                fromState=SVCnewState(&outFile, (ATerm)ATmakeInt($2), &_new);
                toState=SVCnewState(&outFile, (ATerm)ATmakeInt($5), &_new);
                label=SVCnewLabel(&outFile, (ATerm)ATmakeAppl(ATmakeAFun($4,0,ATfalse)), &_new);
                parameter=SVCnewParameter(&outFile, (ATerm)ATmakeList0(), &_new);

                /* Add transition */

                SVCputTransition(&outFile, fromState, label, toState, parameter);
                /* Clean up */

                /* free($4); */

            }
          ;
label     : TAU       { $$=strdup("i");}
            | ID  { $$=$1; /* fprintf(stderr,"%s\n", $$); */}
            ;
%%
