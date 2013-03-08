
%{
#include "tmcrl.h"
/* #include "TB.h" we now use Pieter Olivier's ATerm library */

#define YYDEBUG 1
/* #define YYINITDEPTH 200000 */
#define YYMAXDEPTH 10000000


void yyerror(char *);
extern FILE *yyin;
int aux=0;                 /* auxiliary variable used for parsing */

int lino = 1;              /* line number in source file */
int pos = 0;               /* position in line */

/* sorts, funcs, maps and eqns have the structure outlined in
   Dams & Groote. The structure of the rest needs to be defined */

static specificationbasictype spec;
extern int to_toolbus;
extern int to_file;
extern FILE *outfile;
extern int time_operators_used;
char *error_message=NULL;
int error=0;

ATermIndexedSet PROTECT;
ATbool* b; 

/* below we declare some temporary stores to be used when parsing */
ATerm auxterm=NULL, auxterm1=NULL, auxterm2=NULL ;
char *auxstring=NULL, *auxstring1=NULL;
char messagebuffer[256];

static ATerm eme = NULL, ems = NULL;

void init_structures(void)
{ ATprotect(&(spec.sorts));
  ATprotect(&(spec.funcs));
  ATprotect(&(spec.maps));
  ATprotect(&(spec.acts));
  ATprotect(&(spec.comms));
  ATprotect(&(spec.procs));
  ATprotect(&(spec.init));
  ATprotect(&(spec.eqns));
  ATprotect(&auxterm);
  ATprotect(&auxterm1);
  ATprotect(&auxterm2);
  ATprotect(&eme);
  ATprotect(&ems);

  ems=spec.sorts=ATmake("ems");
  spec.funcs=ATmake("emf");
  spec.maps=ATmake("emf");
  eme = spec.eqns=ATmake("eme");
  spec.acts=ATmake("ema");; /* actions ins(<string>,sortlist,tail) */
  spec.comms=ATmake("emc");
  spec.procs=ATmake("emp");
  spec.init=NULL;
  
  PROTECT=ATindexedSetCreate(1024,75);
}

specificationbasictype *parse_script(char *name,char *err_mes)
{ int pres;

  lino = 1;
  pos = 0;
  error_message=err_mes;
  error=0;
  if((yyin = fopen(name, "r")) == NULL)\
    { sprintf(err_mes,"Cannot open file `%s'", name);
      return NULL; }
yyrestart (yyin);
init_structures ();
pres = yyparse ();		/* at last, the actual parse */
fclose (yyin);
if (error)
  return NULL;
return &spec;
}

static ATerm Traverse(ATerm t, ATerm *a) {
   *a = ATgetArgument((ATermAppl) t, 0);
   return ATgetArgument((ATermAppl) t, 1);
   } 

static ATerm Reverse(ATerm t, ATerm em) {
   ATermList as = ATempty; 
   ATerm a, r = em;
   while (!ATisEqual(t, em)) {
       t =  Traverse(t, &a);
       as = ATinsert(as, a);
       }
   for (as=ATreverse(as);!ATisEmpty(as);as=ATgetNext(as)) {
       r = ATmake("ins(<term>,<term>)", ATgetFirst(as), r);
       }
   return r;
   }

/*--- Yacc stack type --------------------------*/

typedef struct {
  char      *string;   /* appear on parse stack */
  ATerm      t;        /* place to store intermediate terms */

  int lino;            /* I do not see the use of these fields (JFG) */
  int pos;
  int elino;
  int epos;

  /* TBbool    bool;      
  tkind     tk;
  ATerm      ATerm;
  char      *id;
  term_list *term_list; */
} yystype;

/* every non-terminal yields its begin and end coordinates
 * as four tuple (lino, pos, elino, epos). The following macro's
 * expect:
 * - res  (in all cases $$ of the current rule)
 * - b, e (the rule element, e.g. $i, defining the desired values)
 */

#define range(res,b,e)  res.lino = b.lino; res.pos = b.pos;\
                      res.elino = e.elino; res.epos = e.epos;
#define empty_range(res) res.lino = res.elino = lino; res.pos = res.epos = pos;

#define YYSTYPE yystype   /* Yacc stack entries */

%}

%token NAME
%token SORT
%token FUNC
%token MAP
%token VAR
%token REW
%token PROC
%token ACT
%token COMM
%token INIT
%token ARROW
%token MERGE
%token LEFTMERGE
%token LEFTTRIANGLE
%token RIGHTTRIANGLE
%token BOUNDINIT
%token DELTA
%token TAU
%token ENCAP
%token HIDE
%token RENAME
%token SUM

%start specification    /* Start symbol of the grammar */

%%

no_print_name_list : /* create a name list and deliver it in variable t on the 
               parse stack */
     NAME 
     { $$.t=ATmake("ins(<str>,ems)",$1.string);
       ATindexedSetPut(PROTECT,$$.t,b); }
   | no_print_name_list ',' NAME
     { $$.t=ATmake("ins(<str>,<term>)",$3.string,$1.t);
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);};

name_list : /* create a name list and deliver it in variable t on the 
               parse stack */
     NAME 
     { $$.t=ATmake("ins(<str>,ems)",$1.string); 
       ATindexedSetPut(PROTECT,$$.t,b);
       if (to_file) { fprintf(outfile,"%s",$1.string); fflush(outfile); } }
   | name_list ',' NAME
     { $$.t=ATmake("ins(<str>,<term>)",$3.string,$1.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       if (to_file) { fprintf(outfile,",%s",$3.string); fflush(outfile);}};

x_name_list : /* deliver in t a stringlist with the names */
     NAME 
     { $$.t=ATmake("ins(<str>,ems)",$1.string); 
       ATindexedSetPut(PROTECT,$$.t,b);
       if (to_file) { fprintf(outfile,"%s",$1.string);fflush(outfile);} }
   | NAME '#' 
     { if (to_file) { fprintf(outfile,"%s#",$1.string); fflush(outfile); } }
       x_name_list 
     { $$.t=ATmake("ins(<str>,<term>)",$1.string,$4.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$4.t);
	};

space_name_list:		/* This contains always sorts */
     NAME 
     { spec.sorts=ATmake("ins(<str>,<term>)",$1.string,spec.sorts); 
       if (to_file) { fprintf(outfile,"%s ",$1.string);fflush(outfile);} }
   | space_name_list NAME
     { spec.sorts=ATmake("ins(<str>,<term>)",$2.string,spec.sorts); 
       if (to_file) { fprintf(outfile,"%s ",$2.string);fflush(outfile);} };

sort_specification : /* done */
     SORT 
     { if (to_file)  { fprintf(outfile,"sort ");fflush(outfile);} }
        space_name_list 
     { if (to_file)  { fprintf(outfile,"\n\n");fflush(outfile);} };

function_specification : /* done */
     FUNC 
     { if (to_file)  { fprintf(outfile,"func ");fflush(outfile);} }
       space_function_declaration_list
     { if (to_file)  { fprintf(outfile,"\n");fflush(outfile);} }
   | MAP  
     { if (to_file)  { fprintf(outfile,"map  ");fflush(outfile);} }
       space_map_declaration_list 
     { if (to_file)  { fprintf(outfile,"\n");fflush(outfile);} };

space_function_declaration_list : /* done */
     function_declaration
   | space_function_declaration_list 
     { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
       function_declaration ;

space_map_declaration_list : /* done */
     map_declaration
   | space_map_declaration_list 
     { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
         map_declaration ;

function_declaration : /* constructor functions are stored in funcs */
     name_list ':' ARROW NAME
     { for(auxterm=Reverse($1.t, ems); 
           (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm)) ;
           spec.funcs=ATmake("ins(f(<str>,ems,<str>),<term>)",auxstring,$4.string,spec.funcs)){} ;
       if (to_file) { fprintf(outfile,":->%s\n",$4.string);fflush(outfile);}
     }
   | name_list ':' 
     { if (to_file) { fprintf(outfile,":");fflush(outfile);} }
       x_name_list ARROW NAME
     { for(auxterm=Reverse($1.t, ems) ; 
         (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm));
         spec.funcs=ATmake("ins(f(<str>,<term>,<str>),<term>)",auxstring,
                      $4.t,$6.string,spec.funcs)){};
       if (to_file) { fprintf(outfile,"->%s\n",$6.string);fflush(outfile);}
     } ;

map_declaration : /* mappings are stored in maps */
     name_list ':' ARROW NAME
     { for(auxterm=$1.t ; 
         (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm));
         spec.maps=ATmake("ins(f(<str>,ems,<str>),<term>)",auxstring,$4.string,spec.maps)){}; 
       if (to_file) { fprintf(outfile,":->%s\n",$4.string);fflush(outfile);}
     }
   | name_list ':' 
     { if (to_file) { fprintf(outfile,":");fflush(outfile);} } 
         x_name_list ARROW NAME
     { for(auxterm=$1.t ; 
         ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm);
         spec.maps=ATmake("ins(f(<str>,<term>,<str>),<term>)",auxstring,
                   $4.t,$6.string,spec.maps)){}; 
       if (to_file) { fprintf(outfile,"->%s\n",$6.string);fflush(outfile);}
     } ;

equation_specification : /* add the equations to eqns */
     variable_declaration equation_section
     { for( auxterm=$2.t;
       (ATmatch(auxterm,"ins(pair(<term>,<term>),<term>)",
               &auxterm1,&auxterm2,&auxterm));
       spec.eqns=ATmake("ins(e(<term>,<term>,<term>),<term>)",$1.t,auxterm1,auxterm2,spec.eqns)){} ; } ;

variable_declaration : /* delivers a variablelist in t */
     { $$.t=ATmake("emv"); 
       ATindexedSetPut(PROTECT,$$.t,b);
     }
   | VAR 
     { if (to_file) { fprintf(outfile,"var  ");fflush(outfile);} }
       space_variables_list
     { $$.t=$3.t; };
   
space_variables_list : /* delivers a variablelist in t */
    variables 
    { $$.t=$1.t; }
  | space_variables_list 
    { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
       variables
    { $$.t=auxterm1=$1.t; /* assignment to auxterm1 is for protection of this
                             term against garbage collection */
      ATindexedSetRemove(PROTECT,$1.t);
      for(auxterm=$3.t ;
        (ATmatch(auxterm,"ins(<str>,<str>,<term>)",&auxstring,&auxstring1,&auxterm));
        $$.t=auxterm1=ATmake("ins(<str>,<str>,<term>)",auxstring,auxstring1,$$.t)){}; 
      ATindexedSetPut(PROTECT,$$.t,b);
    } ;

variables : /* delivers a variablelist in t */
     name_list ':' NAME
     { auxterm1=ATmake("emv");
       for( auxterm=$1.t ; 
            (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm)) ;)
            { auxterm1=ATmake("ins(<str>,<str>,<term>)",auxstring,$3.string,auxterm1) ;
              /* insertvariablename(auxstring); */ }  
       if (to_file) { fprintf(outfile,":%s\n",$3.string);fflush(outfile);}
       $$.t=auxterm1;
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
     };

data_term_list : /* delivers in var. t on the stack the required termlist */
     data_term
     { $$.t=ATmake("ins(<term>,emt)",$1.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
     }
   | data_term ',' data_term_list
     { $$.t=ATmake("ins(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

data_term : /* delivers in variable t on the stack the required term */
     NAME
     { $$.t=ATmake("t(<str>,emt)",$1.string); 
       ATindexedSetPut(PROTECT,$$.t,b);
     }
   | NAME '(' data_term_list ')'
     { $$.t=ATmake("t(<str>,<term>)",$1.string,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

data_term_list_proc : 
     data_term_proc
     { $$.t=ATmake("ins(<term>,emt)",$1.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
     }
   | data_term_proc ',' data_term_list_proc
     { $$.t=ATmake("ins(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

data_term_proc : /* delivers in variable t on the stack the required term */
     NAME
     { $$.t=ATmake("t(<str>,emt)",$1.string); 
       ATindexedSetPut(PROTECT,$$.t,b);
     }
   | NAME '(' data_term_list_proc ')'
     { $$.t=ATmake("t(<str>,<term>)",$1.string,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

equation_section : /* delivers a list with pair of terms in t */
     REW 
     { if (to_file) { fprintf(outfile,"rew  ");fflush(outfile);} }
       space_single_equation_list
     { $$.t=Reverse($3.t, eme); 
       if (to_file) { fprintf(outfile,"\n");fflush(outfile);}} ;

space_single_equation_list : /* delivers a list with pairs of terms in t */
     single_equation
     { $$.t=ATmake("ins(<term>,eme)",$1.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
     }
   | space_single_equation_list 
     { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
       single_equation
     { $$.t=ATmake("ins(<term>,<term>)",$3.t,$1.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

single_equation : /* deliver pair(t1,t2) in t */
     data_term '=' data_term
     { $$.t=ATmake("pair(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
       if (to_file) 
        { long pos=0;
          print_term(outfile,$1.t,&pos);
          fprintf(outfile,"=");
          pos++;
          print_term(outfile,$3.t,&pos); 
          { fprintf(outfile,"\n");fflush(outfile);} }
     };

process_expression : /* deliver process expression in t */
     parallel_expression
     { $$.t=$1.t; }
   | parallel_expression '+' process_expression
     { $$.t=ATmake("alt(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

parallel_expression : /* deliver process expression in t */
     merge_parallel_expression
     { $$.t=$1.t; }
   | comm_parallel_expression
     { $$.t=$1.t; }
   | cond_expression
     { $$.t=$1.t; }
   | cond_expression LEFTMERGE cond_expression
     { $$.t=ATmake("lmer(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

merge_parallel_expression : /* deliver process expression in t */
     cond_expression MERGE merge_parallel_expression
     { $$.t=ATmake("par(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     }
   | cond_expression MERGE cond_expression
     { $$.t=ATmake("par(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

comm_parallel_expression : /* deliver process expression in t */
     cond_expression '|' comm_parallel_expression
     { $$.t=ATmake("com(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     }
   | cond_expression '|' cond_expression
     { $$.t=ATmake("com(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

cond_expression : /* deliver process expression in t */
     bounded_expression
     { $$.t=$1.t; }
   | bounded_expression LEFTTRIANGLE data_term_proc 
                 RIGHTTRIANGLE bounded_expression
     { $$.t=ATmake("cond(<term>,<term>,<term>)",$1.t,$3.t,$5.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
       ATindexedSetRemove(PROTECT,$5.t);
     } ;

bounded_expression : /* deliver process expression in t */
     dot_expression
     { $$.t=$1.t; }
   | dot_expression BOUNDINIT bounded_expression
     { $$.t=ATmake("bound(<term>,<term>)",$1.t,$3.t); 
       time_operators_used=1; 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

dot_expression : /* deliver process expression in t */
     basic_expression
     { $$.t=$1.t; }
   | basic_expression '.' dot_expression
     { $$.t=ATmake("seq(<term>,<term>)",$1.t,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

basic_expression : /* deliver process expression in t */
     DELTA
     { $$.t=ATmake("delta"); 
       ATindexedSetPut(PROTECT,$$.t,b);
     }
   | TAU
     { $$.t=ATmake("tau"); 
       ATindexedSetPut(PROTECT,$$.t,b);
     }
   | ENCAP '(' '{' no_print_name_list '}' ',' process_expression ')'
     { $$.t=ATmake("encap(<term>,<term>)",$4.t,$7.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$4.t);
       ATindexedSetRemove(PROTECT,$7.t);
     }
   | HIDE    '(' '{' no_print_name_list '}' ',' process_expression ')'
     { $$.t=ATmake("hide(<term>,<term>)",$4.t,$7.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$4.t);
       ATindexedSetRemove(PROTECT,$7.t);
     }
   | RENAME  '(' '{' renaming_declaration_list '}' ',' process_expression ')'
     { $$.t=ATmake("rename(<term>,<term>)",$4.t,$7.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$4.t);
       ATindexedSetRemove(PROTECT,$7.t);
     }
   | SUM     '(' NAME ':' NAME ',' process_expression ')'
     { $$.t=ATmake("sum(<str>,<str>,<term>)",$3.string,$5.string,$7.t); 
       insertvariablename($3.string); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$7.t);
     }
   | NAME
     { $$.t=ATmake("name(<str>,emt)",$1.string); 
       ATindexedSetPut(PROTECT,$$.t,b);
     }
   | NAME '(' data_term_list_proc ')'
     { $$.t=ATmake("name(<str>,<term>)",$1.string,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$3.t);
     }
   | '(' process_expression ')'
     { $$.t=$2.t; }
   | basic_expression '@' data_term_proc
     { $$.t=ATmake("at(<term>,<term>)",$1.t,$3.t); 
       time_operators_used=1; 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
       ATindexedSetRemove(PROTECT,$3.t);
     } ;

renaming_declaration_list : /* deliver renamings in t */
     NAME ARROW NAME
     { $$.t=ATmake("ins(<str>,<str>,emr)",$1.string,$3.string); 
       ATindexedSetPut(PROTECT,$$.t,b);
     }
   | renaming_declaration_list ',' NAME ARROW NAME
     { $$.t=ATmake("ins(<str>,<str>,<term>)",$3.string,$5.string,$1.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$1.t);
     } ;

single_variable_declaration_list : /* a variable list is delivered in t */
     NAME ':' NAME
     { $$.t=ATmake("ins(<str>,<str>,emv)",$1.string,$3.string); 
       insertvariablename($1.string); 
       ATindexedSetPut(PROTECT,$$.t,b);
     }
   | NAME ':' NAME ',' single_variable_declaration_list
     { $$.t=ATmake("ins(<str>,<str>,<term>)",$1.string,$3.string,$5.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$5.t);
       insertvariablename($1.string); 
     } ;

space_process_declaration_list : /* store in procs */
     process_declaration 
     { spec.procs=ATmake("ins(<term>,<term>)",$1.t,spec.procs); }
   | space_process_declaration_list process_declaration
     { spec.procs=ATmake("ins(<term>,<term>)",$2.t,spec.procs); };

process_specification : /* done */
     PROC space_process_declaration_list ;

process_declaration : /* deliver proc(%s,variablelist,process) in t */
     NAME '=' process_expression
     { $$.t=ATmake("proc(<str>,emv,<term>)",$1.string,$3.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$3.t);
     }
   | NAME '(' single_variable_declaration_list ')' '=' process_expression
     { $$.t=ATmake("proc(<str>,<term>,<term>)",
                            $1.string,$3.t,$6.t); 
       ATindexedSetPut(PROTECT,$$.t,b);
       ATindexedSetRemove(PROTECT,$3.t);
       ATindexedSetRemove(PROTECT,$6.t);
     } ;

space_action_declaration_list : /* done */
     action_declaration 
   | space_action_declaration_list 
       { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
       action_declaration ;

action_specification : /* done */
     ACT 
       { if (to_file) { fprintf(outfile,"act  ");fflush(outfile);} }
       space_action_declaration_list 
       { if (to_file) { fprintf(outfile,"\n");fflush(outfile);} } ;

action_declaration : /* actions are added to acts */
     NAME
     { spec.acts=ATmake("ins(<str>,ems,<term>)",$1.string,spec.acts); 
       if (to_file) { fprintf(outfile,"%s\n",$1.string);fflush(outfile);} }
   | name_list ':' 
     { if (to_file) { fprintf(outfile,":");fflush(outfile);} }
       x_name_list
     { for(auxterm=$1.t;
         (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm));
         spec.acts=ATmake("ins(<str>,<term>,<term>)",auxstring,$4.t,spec.acts)){} ; 
       if (to_file) { fprintf(outfile,"\n");fflush(outfile);}
     } ;

space_communication_declaration_list : /* done */
     communication_declaration 
   | space_communication_declaration_list communication_declaration ;

communication_specification : /* done */
     COMM space_communication_declaration_list ;

communication_declaration : /* communicating pairs are delivered in comms */
     NAME '|' NAME '=' NAME
     { spec.comms=ATmake("ins(<str>,<str>,<str>,<term>)",
                   $1.string,$3.string,$5.string,spec.comms); };

initial_declaration : /* insert the process in init */
     INIT process_expression
     { if (spec.init==NULL)
            spec.init=$2.t; 
          else yyerror("Only one init declaration is allowed"); } ;

specification : /* done */
   | sort_specification specification
   | function_specification specification
   | equation_specification specification
   | action_specification specification
   | communication_specification specification
   | process_specification specification
   | initial_declaration specification ;
  

%%

#include "lex.yy.c"

void yyerror(char *s)
{ sprintf(error_message,"line %d: %s, near %s\n", lino, s,
        get_token(yychar));
  /* fprintf(stderr,error_message); fflush(stderr); */
  error=1;
  /* err_fatal("line %d: %s, near %s", lino, s,
        get_token(yychar)); */
  return;
}

#ifndef HAVE_YYWRAP
int yywrap()
{
  return 1;
}
#endif

