#define CAESAR_GRAPH_IMPLEMENTATION 24
#include "caesar_graph.h"
#include "lts.h"
#include "aterm2.h"
/* SENVA #include "mcrl/signature.h" */
#include <stdio.h>
#include <string.h> /* SENVA for strdup() */
#include <stdlib.h> /* SENVA for getenv() */

/* ADMINISTRATIVE STUFF */

CAESAR_TYPE_STRING CAESAR_GRAPH_COMPILER() {
  return "mcrl_open";
}

CAESAR_TYPE_VERSION CAESAR_GRAPH_VERSION() {
  return 2.14;
}

/* ENCODING OF STATES AND LABELS */

struct CAESAR_STRUCT_STATE {int state;};
struct CAESAR_STRUCT_LABEL {ATerm label;};

CAESAR_TYPE_NATURAL CAESAR_HINT_SIZE_STATE = sizeof(int);
CAESAR_TYPE_NATURAL CAESAR_HINT_SIZE_LABEL = sizeof(ATerm);

CAESAR_TYPE_NATURAL CAESAR_HINT_HASH_SIZE_STATE = sizeof(int);
CAESAR_TYPE_NATURAL CAESAR_HINT_HASH_SIZE_LABEL = sizeof(ATerm);

CAESAR_TYPE_NATURAL CAESAR_HINT_ALIGNMENT_STATE = 4;
CAESAR_TYPE_NATURAL CAESAR_HINT_ALIGNMENT_LABEL = 4;

CAESAR_TYPE_BOOLEAN CAESAR_COMPARE_STATE(CAESAR_TYPE_STATE s1, CAESAR_TYPE_STATE s2) {
  return (s1->state == s2->state ? CAESAR_TRUE : CAESAR_FALSE);
}

CAESAR_TYPE_BOOLEAN CAESAR_COMPARE_LABEL(CAESAR_TYPE_LABEL l1, CAESAR_TYPE_LABEL l2) {
  return (l1->label == l2->label ? CAESAR_TRUE : CAESAR_FALSE);
}

/* PRINTING OF STATES AND LABELS */

static state_format = 0;
CAESAR_TYPE_NATURAL CAESAR_MAX_FORMAT_LABEL(void) {return 0;}
CAESAR_TYPE_NATURAL CAESAR_MAX_FORMAT_STATE(void) {return 1;}

void CAESAR_FORMAT_STATE(CAESAR_TYPE_NATURAL x) {
  if (0<=x && x<=1) state_format = x;
  else ATerror("%d exceeds max state format",x);
}

void CAESAR_FORMAT_LABEL(CAESAR_TYPE_NATURAL x) {
  if (x != 0) ATerror("%d exceeds max label format",x);
}

void CAESAR_PRINT_STATE(CAESAR_TYPE_FILE f,CAESAR_TYPE_STATE s) {
  //  fprintf(f,"PRINT_STATE %d",s->state);
  ATermList values = (ATermList)LTSgetState(s->state);
  ATermList names = MCRLgetListOfPars();
  if (state_format>=1)
    fprintf(f,"\n(");
  else
    fprintf(f,"(");
  while (!ATisEmpty(values)) {
    if (state_format>=1) 
      ATfprintf(f,"%t = ",MCRLprint(ATgetArgument(ATgetFirst(names),0)));
    ATfprintf(f,"%t",MCRLprint(ATgetFirst(values)));
    values=ATgetNext(values);
    names=ATgetNext(names);
    if (!ATisEmpty(values)) 
      if (state_format>=1)
	fprintf(f,",\n");
      else
	fprintf(f,",");
  }
  fprintf(f,")");
}

void CAESAR_PRINT_LABEL(CAESAR_TYPE_FILE f,CAESAR_TYPE_LABEL l) {
  /* fprintf(stderr,"CAESAR_PRINT_LABEL\n"); */
  if (l->label==MCRLterm_tau)
    fprintf(f,"i");
  else 
    fprintf(f,"\"%s\"",ATgetName(ATgetSymbol(l->label)));
}

CAESAR_TYPE_STRING CAESAR_STRING_LABEL(CAESAR_TYPE_LABEL l) {
  // fprintf(stderr,"CAESAR_STRING_LABEL\n");
  char* L;
  static char *a = NULL;
  static int siz  = 0;
  if (l->label==MCRLterm_tau)
    L="i";
  else {
    L=ATgetName(ATgetSymbol(l->label));
    if (!a || strlen(L)>siz) {
      siz = strlen(L);
      a = realloc(a,  siz+5); 
      }
    sprintf(a,"\"%s\"",L);
    return a;
    }
  return L;
  }

void CAESAR_PRINT_STATE_HEADER(CAESAR_TYPE_FILE fp) {
  ATerm l = (ATerm)MCRLgetListOfPars();
  ATerm v,s;
  while (ATmatch(l,"[v(<term>,<term>),<list>]",
		 &v,&s,&l))
    ATfprintf(fp,"%t:%s \n",MCRLprint(v),ATgetName(ATgetSymbol(s)));
}

void CAESAR_DELTA_STATE(CAESAR_TYPE_FILE fp,CAESAR_TYPE_STATE s1,CAESAR_TYPE_STATE s2) {
  ATermList pars = (ATermList)MCRLgetListOfPars();
  ATermList l1 = (ATermList)LTSgetState(s1->state);
  ATermList l2 = (ATermList)LTSgetState(s2->state);
  while (!ATisEmpty(pars)) {
    ATerm x1 = ATgetFirst(l1);
    ATerm x2 = ATgetFirst(l2);
    if (x1 != x2)
      ATfprintf(fp,"%t := %t; ", 
		MCRLprint(ATgetArgument(ATgetFirst(pars),0)), 
		MCRLprint(x2));
    l1 = ATgetNext(l1);
    l2 = ATgetNext(l2);
    pars = ATgetNext(pars);
  }
  //  fprintf(fp,"Diff: %d - %d",s1->state,s2->state);
}


CAESAR_TYPE_STRING CAESAR_INFORMATION_LABEL(CAESAR_TYPE_LABEL l) {
  return "";
}



/* ON THE FLY EXPLORATION */

/* global variables to store arguments of CAESAR_ITERATE_STATE,
   i.e. the current call-back function, the source, label, destination
*/

static void (*CScallback)(CAESAR_TYPE_STATE, CAESAR_TYPE_LABEL, CAESAR_TYPE_STATE);
static CAESAR_TYPE_STATE S;
static CAESAR_TYPE_LABEL L;
static CAESAR_TYPE_STATE D;

/* needed to avoid that labels are garbage collected */
static ATermIndexedSet Label_set;

/* next one will be called by the MCRL library.
   it will call the CADP call-back function */

static void wrap_call_back(int src, ATerm label, int dest) {
  ATbool b;
  L->label = label;
  D->state = dest;
  ATindexedSetPut(Label_set,label,&b);
  CScallback(S,L,D);
}

void CAESAR_ITERATE_STATE(CAESAR_TYPE_STATE s1, 
			  CAESAR_TYPE_LABEL l, 
			  CAESAR_TYPE_STATE s2, 
    void (*callback) 
      (CAESAR_TYPE_STATE, CAESAR_TYPE_LABEL, CAESAR_TYPE_STATE)) {
  CScallback = callback;
  S=s1;
  L=l;
  D=s2;
  LTSstep(s1->state); /* which in turn calls wrap_call_back */
}

void CAESAR_START_STATE(CAESAR_TYPE_STATE s) {
  s->state = LTSgetInitialState();
}

/* SOME OTHER REQUIRED FUNCTIONS */

CAESAR_TYPE_BOOLEAN CAESAR_VISIBLE_LABEL(CAESAR_TYPE_LABEL x) {
  return (x->label==MCRLterm_tau ? CAESAR_FALSE : CAESAR_TRUE);
}

CAESAR_TYPE_NATURAL CAESAR_HASH_STATE(CAESAR_TYPE_STATE s,CAESAR_TYPE_NATURAL m) {
  return s->state % m;
}

CAESAR_TYPE_NATURAL CAESAR_HASH_LABEL(CAESAR_TYPE_LABEL l,CAESAR_TYPE_NATURAL m) {
  return (CAESAR_TYPE_NATURAL)l->label % m;
}


CAESAR_TYPE_STRING CAESAR_GATE_LABEL(CAESAR_TYPE_LABEL l) {
  return strtok(CAESAR_STRING_LABEL(l),"(");
}

CAESAR_TYPE_NATURAL CAESAR_CARDINAL_LABEL(CAESAR_TYPE_LABEL l) {
  return ATgetArity(ATgetSymbol(ATparse(CAESAR_STRING_LABEL(l))));
}

/* INITIALIZATION */

static void WarningHandler(const char *format, va_list args)
     {
     fprintf(stderr,"mcrl_open: ");
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }

static void ErrorHandler(const char *format, va_list args)
     {
     fprintf(stderr,"mcrl_open: ");
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     exit(-1);
     }

void CAESAR_INIT_GRAPH(void) {
  int argc;
  char **argv;
  char *FILENAME;
  char *OPTIONS;
  char *token;

  ATinitialize(0,NULL);
  ATsetWarningHandler(WarningHandler);
  ATsetErrorHandler(ErrorHandler);

  /* ATwarning ("Executing CAESAR_INIT_GRAPH"); */

  FILENAME = getenv ("OPEN_CAESAR_FILE");
  if (FILENAME == NULL)
	CAESAR_ERROR ("undefined environment variable $OPEN_CAESAR_FILE");

  OPTIONS = getenv ("MCRL_OPTIONS");
  if (OPTIONS == NULL)
	CAESAR_ERROR ("undefined environment variable $MCRL_OPTIONS");

  #define MAX_OPTIONS 100

  argv = (char**)calloc(MAX_OPTIONS,sizeof(char*));
  argc = 0;
  argv[argc] = "mcrl_open";
  // ATwarning ("%d -> \"%s\"\n", argc, argv [argc]);
  argc ++;
  
  /* skip leading white spaces */
  while (*OPTIONS == ' ') OPTIONS++;
  token = strtok (OPTIONS, " ");
  while (1) {
     if (token == NULL) break;
     argv [argc] = token;
     // ATwarning ("%d -> \"%s\"\n", argc, argv [argc]);
     argc ++; 
     token = strtok ((char *) NULL, " ");
  }

  argv [argc] = FILENAME;
  // ATwarning ("%d -> \"%s\"\n", argc, argv [argc]);
  argc ++;

  MCRLsetArguments(&argc, &argv);
  RWsetArguments(&argc,&argv);
  
  if (!MCRLinitialize())
    ATerror("%s cannot be opened\n",FILENAME);
  ATwarning("Opened %s",FILENAME);
  RWinitialize(MCRLgetAdt());
  LTSsetArguments(&argc,&argv);
  LTSinitialize(wrap_call_back);

  Label_set = ATindexedSetCreate(1024,75);
  /* ATwarning ("Leaving CAESAR_INIT_GRAPH"); */
}
