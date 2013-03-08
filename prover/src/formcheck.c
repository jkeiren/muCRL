/* $Id: formcheck.c,v 1.3 2004/11/23 12:36:17 uid523 Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "aterm2.h"
#include "mcrl.h"
#include "prover.h"
#include <string.h>

#define MY_NAME "Formcheck"
// VERSION assumed to be defined with -DVERSION=\"...\"

static char COUNTER=0;
static char WITNESS=0;
static char PRINT=0;
static char DOT=0;
static char* form_file=0;
static char* lpo_file=0;

void version() {
  fprintf(stderr,"%s (version %s)\n",MY_NAME, VERSION);
  exit(0);
}

static void WarningHandler(const char *format, va_list args)
     {
     fprintf(stderr,"%s: ", MY_NAME);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }
     
static void ErrorHandler(const char *format, va_list args)
     {
     fprintf(stderr,"%s: ", MY_NAME);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     exit(-1);
     }

void help() {
  ATfprintf(stderr,"%s\n",
	    "\nformcheck [-formula file] [-spec file.tbf] [options]");
  ATfprintf(stderr,"%s\n",
	    "-- checks whether formulas in 'file' hold given the datatypes in 'file.tbf'");
  ATfprintf(stderr,"%s\n",
	    "");
  ATfprintf(stderr,"%s\n",
	    "-formula file  : "
	    "contains variable declarations and formulae to be proved:");
  ATfprintf(stderr,"%s\n",
	    "                 [[v(x,sort),...],formula,...]");
  ATfprintf(stderr,"%s\n",
	    "-spec file.tbf  : "
	    "contains the specification in which the formulae are proved");
  ATfprintf(stderr,"%s\n",
	    "At least one of "
	    "-formula or -spec must be present;");
  ATfprintf(stderr,"%s\n",
	    "if -formula or -spec are missing, stdin is taken.");
  ATfprintf(stderr,"%s\n",
	    "");
  ATfprintf(stderr,"%s\n",
	    "OPTIONS:");
  ATfprintf(stderr,
	    "%s\n","-print         : "
	    "prints resulting BDDs as ASCII to stderr");
  ATfprintf(stderr,
	    "%s\n","-print-dot     : "
	    "prints resulting BDDs as dot graphs to stdout");
  ATfprintf(stderr,
	    "%s\n","-counter       : "
	    "prints counter-examples");
  ATfprintf(stderr,
	    "%s\n","-witness       : "
	    "prints witness for the formula");
  ATfprintf(stderr,"%s\n",
	    "-version       : "
	    "prints the version number");
  ATfprintf(stderr,"%s\n",
	    "-help          : "
	    "prints this message");
  exit(0);
}

void parse_argument_line(int argc,char *argv[]) {
  int i;
  
  for (i=1;i<argc;i++) {
    if (!strcmp(argv[i],"-counter"))
      COUNTER=1; 
    if (!strcmp(argv[i],"-witness"))
      WITNESS=1; 
    if (!strcmp(argv[i],"-print"))
      PRINT=1; 
    if (!strcmp(argv[i],"-print-dot"))
      DOT=1; 
    if (!strcmp(argv[i],"-formula"))
      form_file=argv[++i]; 
    if (!strcmp(argv[i],"-spec"))
      lpo_file=argv[++i];
    if (!strcmp(argv[i],"-help"))
      help(); 
    if (!strcmp(argv[i],"-version"))
      version();
  }
  if (!(form_file || lpo_file)) 
    ATerror("Specify at least one of -formula or -spec\n");
}

int main(int argc, char *argv[]) {
  ATerm bottomOfStack=NULL;
  ATerm spec=NULL, formula=NULL;
  static ATermList vars=NULL,list=NULL;
  int count = 0;
  FILE *lpo;
  FILE *form;

  ATinit(argc,argv, &bottomOfStack);
  ATsetWarningHandler(WarningHandler);
  ATsetErrorHandler(ErrorHandler);
  parse_argument_line(argc,argv);

  ATprotect(&spec);
  ATprotect(&formula);
  ATprotect((ATerm*)&vars);
  ATprotect((ATerm*)&list);

  if (!lpo_file) 
    lpo=stdin;
  else {
    lpo = fopen(lpo_file,"r");
    if (!lpo) {
      perror(lpo_file);
      exit(1);
    }
  }
  spec = ATreadFromFile(lpo);
  if (spec==NULL) exit(1);

  if (!ATmatch(spec,"spec2gen(<term>,<term>)",
	       &spec,NULL))
    ATerror("Not a muCRL (2nd generation) specification on standard input.\n");

  MCRLinitializeAdt(spec);
  ProverSetArguments(&argc,&argv);
  ProverInitialize();
  //  Init_prover(spec,argc,argv);

  if (!form_file)
    form=stdin;
  else {
    form = fopen(form_file,"r");
    if (!form) {
      perror(form_file);
      exit(1);
    }
  }
  list=(ATermList)ATreadFromFile(form);
  if (list==NULL) exit(1);
  if (ATgetType(list)!=AT_LIST)
    ATerror("The -formula file should contain a list of declarations/formulae\n");

  while (!ATisEmpty(list)) {
    ATfprintf(stderr,"%d: ",++count);
    vars = (ATermList)ATgetFirst(list);
    if (ATgetType(vars)!=AT_LIST)
      ATerror("Variable declaration list [v(x,sort),...] expected\n %t\n",vars);
    vars = parse_decls(vars);
    list = ATgetNext(list);
    Declare_vars(vars);
    formula = parse(ATgetFirst(list));
    if (Sort_of(formula)!=prBOOL)
      ATerror("Formula should be of type Bool\n");
    list = ATgetNext(list);
    
    formula = Prove(formula);
    if (formula == prTRUE)
      fprintf(stderr,"True\n");
    else if (formula == prFALSE)
      fprintf(stderr,"False\n");
    else {
      fprintf(stderr,"Don't know\n");
      if (PRINT) print_BDD(formula,stderr);
      if (DOT) dot_BDD(formula,stdout);
      if (COUNTER) print_example(formula,prFALSE,stderr);
      if (WITNESS) print_example(formula,prTRUE,stderr);
    }
  }
  exit(0);
}
