
/* This file contains the basic definitions for the timed mCRL 
   static semantics checker 

   Work on this file started on 12 juli 1997, based on the CWI
   technical report "The Syntax and Semantics of Timed mCRL",
   by J.F. Groote.

   Everybody is free to use this software, provided it is not
   changed.

   In case problems are encountered when using this software,
   please report them to J.F. Groote, CWI, Amsterdam, jfg@cwi.nl

   This software comes as it is. I.e. the author assumes no
   responsibility for the use of this software. 

   THIS TEKST MUST STILL BE IMPROVED */


#ifndef __TMCRL_H__
#define __TMCRL_H__

/* #include <TB.h> */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "aterm2.h"
#define streq(s1,s2) !strcmp(s1,s2)

#define MAXLEN 200  /* maximum length of the name of a variable */
/* ERRORLENGTH gives the maximum length of an errormessage.
   PRINTEDTERMLENGTH gives the length of a ATerm in an errormessage.
   it should be substantially less than half ERRORLENGTH */
#define ERRORLENGTH 250
#define PRINTEDTERMLENGTH 80
#define MAXARG 1000
#define MAXENUM 100

#define MAXSORT 500
#define MAXOBJECT 10000
#define LINEBREAKLIMIT 70

/* #define number long */

typedef struct specificationbasictype {
            ATerm sorts;     /* storage place for sorts */
            ATerm funcs;     /* storage place for functions */
            ATerm maps;      /* storage place for constructors */
            ATerm acts;      /* storage place for actions */
            ATerm comms;     /* storage place for communications */
            ATerm procs;     /* storage place for processes,
                                         uses alt, seq, par, lmer, cond,sum,
                                         com, bound, at, name, delta,
                                   tau, hide, rename, encap */
            ATerm init;      /* storage place for initial process */       
            ATerm eqns;      /* storage place for equations */          
} specificationbasictype;

  
typedef struct arglist {
  int n;
  struct arglist *next; } arglist;

void release_totalarglist(arglist *c);
arglist *new_arglist(int s, arglist *a);
  
specificationbasictype *parse_script(char *name, char *err_mes);

void rg_error(char *s, ATerm t);

int declarevariables(ATerm t, char *emsg);
void resetvariables(ATerm vars);
int sscproc(specificationbasictype *spec, char *emsg);
ATerm transform(int init, specificationbasictype *spec, char *err_mes, int keep_structure);
/* The keep_structure argument was added to support multi LPO output
 * See comments in main.c
 */
void printLPO (FILE *outfile, ATerm t);


int correct(ATerm termlist, ATerm proc, char *emsg);
int welltyped(ATerm t, char *emsg);

int ssc(specificationbasictype *spec, char *emsg);
/* int ssc_spec(ATerm d, char *emsg); */
int correctopenterm(ATerm t,char *emsg);
int correctopenboolterm(ATerm t,char *emsg);


typedef struct string {
  char s[MAXLEN];  
  struct string *next; } string;  
  
string *new_string(char *s);
/* ATerm lnsubstituteterm(ATerm terms, ATerm tlist, ATerm vars, char *emsg);
ATerm substituteterm(ATerm terms, ATerm singleterm, ATerm vars, char *emsg);
ATerm lsubstituteterm(ATerm terms, ATerm tlist, ATerm vars, char *emsg);
ATerm repl(char *name,ATerm subs, ATerm t);
ATerm lrepl(char *name, ATerm subs, ATerm termlist); 
int closedl(ATerm t);
int closed(ATerm t); */
int welltyped2(ATerm t, arglist **sorts, char *culprit);
int welltypedopen2(ATerm t, ATerm vars1, ATerm vars2, arglist **sort, char *emsg);

int insertvariablename(char *c);
void yyrestart(FILE *);
int yyparse (void);
int yylex(void);

ATermList translate_sorts_2gen(ATerm t);
ATermList translate_funcs_2gen(ATerm t);
ATermList translate_eqns_2gen(ATerm t);
ATerm translate_lpo_2gen(ATerm t);

/* int existvar(char *str, int *sort); */
int existfuncmap(char *str, arglist *sorts, int *sort);
int existsort(char *c);
void initializefmts(void);
void finalizefmts(void);
void initialize_data(void);
void print_term (FILE *f,ATerm t, long *pos);

#endif /* __TMCRL_H__ */

