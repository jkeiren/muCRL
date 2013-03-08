/* $Id: mucheck.c,v 1.2 2005/04/20 14:26:43 vdpol Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "aterm2.h"
#include "prover.h"
#include "mcrl.h"
#include "rw.h"
#include "libmcparse.h"


#define ERRORLENGTH 1024
#define P(msg)  fprintf(stdout,"%s\n",msg)

static int verbose=0;
static int monitor=0;
static int showsize=0;
static int show_bdd=0;
static int show_dot=0;
static int inequalities=0;
static int sound=1;
static int counterexample=0;

extern ATerm prTRUE;
extern ATerm prFALSE;


static ATerm Eqbdd(ATerm formula)
{ return (inequalities ? SimpIneq(Prove(formula)) : Prove(formula)); }

static char *AddFun(char *name,ATermList parameters, ATerm targetsort)
{ ATermList sorts=ATempty;
  AFun fun;
  ATbool new = ATfalse;
  
  SignatureAddMap(name,parameters,targetsort);

  for( ; !ATisEmpty(parameters) ; parameters=ATgetNext(parameters))
  { sorts=ATinsert(sorts,ATgetArgument(ATgetFirst(parameters),1));
  }
  sorts=ATreverse(sorts);

  fun=MCRLputMap((ATerm)ATmakeApplList(
       ATmakeAFun(name,ATgetLength(sorts),ATtrue),sorts),
       targetsort,&new);
  if ((new==0)||(fun==0))
     ATerror("Failed to add auxiliary internal mapping: %s",name);
   
  return ATgetName(fun);
}

extern ATerm Combine(Symbol f, ATermList args);

static ATerm Combine1(AFun f, ATerm t1)
{ assert(ATgetArity(f)==1);
  return Combine(f,ATinsert(ATempty,t1));
}

static ATerm Combine2(AFun f, ATerm t1, ATerm  t2)
{ assert(ATgetArity(f)==2);
  return Combine(f,ATinsert(ATinsert(ATempty,t2),t1));
}

static ATerm Combine3(AFun f, ATerm t1, ATerm  t2, ATerm t3)
{ assert(ATgetArity(f)==3);
  return Combine(f,ATinsert(ATinsert(ATinsert(ATempty,t3),t2),t1));
}


void RWflush(void);

char *who = "Mucheck";

static AFun truesymbol,falsesymbol,andsymbol,orsymbol,
     notsymbol,itesymbol,forallsymbol,existssymbol;

static char formula_file_name[ERRORLENGTH];
static ATermTable equationdefs=NULL;  

static ATermList variablelist=NULL;

static void internalsyntaxmsg(void)
{
  P("The internal syntax of modal formulas looks as follows (this syntax is only relevant");
  P("when adapting this tool):");
  P("");
  P("Action formulas:");
  P("  A ::= T | F | act(N(e1,...,en)) | and(A,A) | or(A,A) | not(A) | ");
  P("               exists(d,D,A) | forall(d,D,A).");
  P("");
  P("Modal formulas:");
  P("  phi ::= T | F | form(b) | rec(Y(e1,...,en)) | not(phi) | and(phi,phi) | or(phi,phi) |");
  P("          may(A,phi) | must(A,phi) | exists(d,D,phi) | forall(d,D,phi) |");
  P("          mu(X,[v(d1,D1),...,v(dn,Dn)],phi,[e1,...,en]) |");
  P("          nu(X,[v(d1,D1),...,v(dn,Dn)],phi,[e1,...,en])."); 
  P("");
  P("where b is a boolean expression, e1,...,en are expressions, may represents");
  P("<> and must []. d,d1,...,dn represent data variables, D,D1,...,Dn are sorts.");
  P("");

}

static void externalsyntaxmsg(void)
{
/*P("The syntax of modal formulas looks as follows:");
  P("");
  P("Action formulas:");
  P("  A ::= T | F | N(e1,...,en) | A&A | A|A | ~A | (A) | ?d:D.A | !d:D.A"); 
  P("");
  P("where ? is the existential and ! the universal quantifier. T stands for true,");
  P("F for false, & is and, | is or, and ~ is not. N is the name of an action and");
  P("the expressions e1,...,en are its arguments.");
  P("");
  P("Modal formulas:");
  P("  phi ::= T | F | b | Y(e1,...,en) | ~phi | (phi) | phi&phi | phi|phi |");
  P("          <A>phi | [A]phi | ?d:D.phi) | !d:D.phi) |");
  P("          mu(X[d1:D1,...,dn:Dn].phi)[e1,...,en] | mu X.phi)");
  P("          nu(X[d1:D1,...,dn:Dn].phi)[e1,...,en] | nu X.phi)");
  P("");
  P("where b is a boolean expression, Y and X are parameterized boolean variables");
  P("d,d1,...,dn represent data variables, D,D1,...,Dn are sorts and e1,...,en are");
  P("initial values of a fixed point formula. The names of the variables X and Y must");
  P("be unique and may not overlap with any name used in the LPO.");
  P("");
  P("All functions that are being used must have been declared in the file");
  P("containing the linear process. If not unspecified behaviour, likely including");
  P("core dumps will occur.");
  P("");
  P("Furthermore, all names of variables used in the formula, may not be used in the");
  P("process description. This also holds for the variables used in quantifiers. The tool");
  P("currently does not use any form of alpha conversion, and will be confused by different");
  P("variables with the same name");
  P("");
  P("All text starting with a % until the end of the line is considered to be comment."); */

  P("We  describe  the  syntax  and  partly  the  semantics  of the");
  P("contents  of  extended  mu-calculus formula files. Such a file");
  P("has  to  contain  exactly  one  modal  formula,  which  itself");
  P("consists  of  modal  formulas,  regular  formulas  and  action");
  P("formulas.");
  P(" ");
  P("In  formula files, text starting with the symbol \"%\" until the");
  P("end of the line character is considered to be comment. Further");
  P("we  need  the  following elements to describe action formulas,");
  P("regular formulas and modal formulas:");
  P(" AN        ::=  RNAME | RNAME \"(\" DT_LIST \")\"");
  P(" FORM      ::=  RNAME | RNAME \"(\" DT_LIST \")\"");
  P(" DT        ::=  NAME  | NAME \"(\" DT_LIST \")\"");
  P(" DT_LIST   ::=  DT    | DT_LIST \",\" DT");
  P(" VD        ::=  RNAME \":\" RNAME");
  P(" VDI       ::=  VD \"=\" DT");
  P(" VDI_LIST  ::=  VDI   | VDI_LIST \",\" VDI");
  P(" FP_VD     ::=  RNAME | RNAME \"(\" VDI_LIST \")\"");
  P(" FP_VO     ::=  RNAME | RNAME \"(\" DT_LIST \")\"");
  P(" ");
  P("Here NAME and RNAME both denote mCRL names, AN represents mCRL");
  P("action  names,  FORM  represents  mCRL  formulas, DT mCRL data");
  P("terms,   DT_LIST   lists  of  data  terms,  VD  mCRL  variable");
  P("declarations,  VDI variable declarations with initialisations,");
  P("VDI_LIST  lists of variable declarations with initialisations,");
  P("FP_VD  fixed point variable declarations and FP_VO fixed point");
  P("variable  occurrences.  In  order  to  avoid  ambiguity and to");
  P("increase  readability  in  action  names,  formulas,  variable");
  P("declarations and fixed point variables, an RNAME is restricted");
  P("such   that  the  mu-calculus  keywords  \"T\",  \"F\",  \"forall\",");
  P("\"exists\",  \"nil\",  \"mu\"  and  \"nu\" are not allowed. Also names");
  P("occurring  in  actions,  formulas  and  data  terms have to be");
  P("declared and well-typed, formulas should be of type \"Bool\" and");
  P("the  right part of a variable declaration should be a declared");
  P("sort.  Finally  every  occurrence  of  a  fixed point variable");
  P("should  be  in  the scope of a corresponding declaration, i.e.");
  P("the  declaration  and the occurrence should have the same name");
  P("and  the same number of parameters, where each parameter is of");
  P("the same type.");
  P(" ");
  P("Action  formulas  are  denoted by the non-terminal AF that has");
  P("the following definition:");
  P(" AF  ::=  AN  |  \"(\" AF \")\"  |  \"T\"  |  \"F\"  |  \"!\" AF");
  P("       |  AF \"&&\" AF  |  AF \"||\" AF  |  AF \"=>\" AF  |  AF \"==\" AF");
  P("       |  \"forall\" VD \".\" AF  |  \"exists\" VD \".\" AF");
  P(" ");
  P("Here  the  symbol  \"T\" stands for true, \"F\" for false, \"!\" for");
  P("not,  \"&&\" for and, \"||\" for or, \"=>\" for implication and \"==\"");
  P("for equivalence. The rules starting with \"forall\" and \"exists\"");
  P("stand for universal and existential quantification. The binary");
  P("infix operators are left-associative except for \"=>\", which is");
  P("right-associative.   The  quantifications  and  \"!\"  have  the");
  P("highest priority, followed by \"&&\" and \"||\", followed by \"=>\",");
  P("followed  by  \"==\". These priorities can be overruled with the");
  P("use of parentheses.");
  P(" ");
  P("Regular  formulas  are denoted by the non-terminal RF that has");
  P("the following definition:");
  P(" RF  ::=  AF  |  \"(\" RF \")\"  |  \"nil\"  |  RF \".\" RF  |  RF \"|\" RF");
  P("       |  RF \"*\"  |  RF \"+\"");
  P(" ");
  P("Here  \"nil\"  stands  for empty, \".\" for concatenation, \"|\" for");
  P("choice,  \"+\" for the transitive and reflexive closure, and \"+\"");
  P("for  the  transitive  closure.  The binary infix operators are");
  P("left-associative.   The   unary  operators  have  the  highest");
  P("priority,  followed  by \".\", followed by \"|\". These priorities");
  P("can be overruled with the use of parentheses.");
  P(" ");
  P("Modal formulas are denoted by the non-terminal MF that has the");
  P("following definition:");
  P(" MF  ::=  FORM  |  \"(\" MF \")\"  |  \"T\"  |  \"F\"  |  \"!\" MF");
  P("       |  MF \"&&\" MF  |  MF \"||\" MF  |  MF \"=>\" MF  |  MF \"==\" MF");
  P("       |  \"forall\" VD \".\" MF  |  \"exists\" VD \".\" MF");
  P("       |  \"<\" RF \">\" MF  |  \"[\" RF \"]\" MF  |  \"@\" \"(\" RF \")\"");
  P("       |  \"mu\" FP_VD \".\" MF  |  \"nu\" FP_VD \".\" MF  |  FP_VO");
  P(" ");
  P("The  symbol  \"T\"  stands for true, \"F\" for false, \"!\" for not,");
  P("\"&&\"  for  and, \"||\" for or, \"=>\" for implication and \"==\" for");
  P("equivalence.  The  rules  starting  with \"forall\" and \"exists\"");
  P("stand  for universal and existential quantification, the rules");
  P("\"<\"  RF  \">\"  MF  and  \"[\"  RF  \"]\"  MF  for  the may and must");
  P("operators,  the  rule  \"@\" \"(\" RF \">\" for the infinite looping");
  P("operator  and  the  rules  starting with \"mu\" and \"nu\" for the");
  P("smallest  and  largest fixed point operators. Recall that FORM");
  P("represents  an  mCRL formula, VD an mCRL variable declaration,");
  P("FP_VD  the declaration of a fixed point variable and FP_VO the");
  P("occurrence  of  a  fixed  point  variable.  The  binary  infix");
  P("operators  are  left-associative  except  for  \"=>\",  which is");
  P("right-associative.  The  quantifications, the prefix operators");
  P("and  the  may  and  must  operators have the highest priority,");
  P("followed by \"&&\" and \"||\", followed by \"=>\", followed by \"==\".");
  P("These priorities can be overruled with the use of parentheses.");
  P(" ");
  P("The  may  and must operators and the infinite looping operator");
  P("have  the  following  meaning. In a state of the state space a");
  P("formula  <R>phi  is  valid  if there exists a path starting in");
  P("this  state,  that  satisfies R and leads to a state such that");
  P("phi  is  valid. In a state of the state space a formula [R]phi");
  P("is  valid  if  all paths starting in this state, satisfying R,");
  P("lead  to  a  state  such  that phi is valid. In a state of the");
  P("state space @(R) holds if there exists a path starting in this");
  P("state  that  is  an  infinite  concatenation of sequences that");
  P("satisfy R.");
  P(" ");
  P("Note  that formulas containing fixed point operators should be");
  P("monotonic. Because \"!\" is not monotonic, every occurrence of a");
  P("fixed  point  variable  may  only  be  in the scope of an even");
  P("number of \"!\" operations.");
  P(" ");
  P("Besides   the   well-known   relations   between   symbols  of");
  P("first-order  logic,  the  following relations hold for regular");
  P("formulas,  for  fresh variable X, i.e. it may not occur in phi");
  P("or in the context:");
  P(" <nil>phi   = <F*>phi");
  P(" <R1.R2>phi = <R1><R2>phi");
  P(" <R1+R2>phi = <R1>phi || <R2>phi");
  P(" <R*>phi    = mu X.(phi || <R>X)");
  P(" <R+>phi    = <R.R*>phi");
  P(" ");
  P(" [nil]phi   = [F*]phi");
  P(" [R1.R2]phi = [R1][R2]phi");
  P(" [R1+R2]phi = [R1]phi && [R2]phi");
  P(" [R*]phi    = nu X.(phi && [R]X)");
  P(" [R+]phi    = [R.R*]phi");
  P(" ");
  P("The  following  relations  hold for the modal operators, where");
  P("phi(!X)   represents   substitution   of  !X  for  every  free");
  P("occurrence of X in phi:");
  P(" [R]phi     = !<R>!phi");
  P(" nu X.phi   = !mu X.!phi(!X)");
  P(" ");
  P("For infinite looping we have, for fresh X:");
  P("    @(R)       = nu X.<R>X");
  P(" ");
  P("Some examples are: ");
  P("Freedom of deadlock:");
  P("    [T*]<T>T");
  P(" ");
  P("There exists a loop a.b.c:");
  P("    <T*>@(a.b.c)");
  P(" ");
  P("Action  b may not happen after an action c, unless an action a");
  P("occurs after this c and before this b:");
  P("    [(!c)*.c.((!a && !b)* | a.(!c)*.c)*.b]F");
  P(" ");
  P("The same formula but now b may not occur initially:");
  P("    [((!a && !b)* | a.(!c)*.c)*.b]F");
  
}

static ATerm FORALL(ATerm var, ATerm sort, ATerm t)
{ return (ATerm)ATmakeAppl3(forallsymbol,var,sort,t); }

static ATerm EXISTS(ATerm var, ATerm sort, ATerm t)
{ return (ATerm)ATmakeAppl3(existssymbol,var,sort,t); }

static void helpmsg(void)
    {
    P("Usage: mucheck  [options] formula-file lpo-file ");
    P("");
    P("Mucheck checks whether a modal formula in the formula-file holds in the initial");
    P("state of the given linear process in the lpo-file");
    P("");
    P("The following options can be used");
    P("-help:\t\tyields this message");
    P("-version:\tget the version number of this release");
    P("-syntax:\tprovides the syntax for formulas");
    P("-internal:\tprovides the internal syntax for formulas");
    P("-verbose:\tprovides various forms of (internal) information");
    P("-counter:\tshow a BDD trace indicating that iteration has not stabilized");
    P("-show-size:\tshow the sizes of intermediate BDDs");
    P("-monitor:\tmonitor the approximation process");
    P("-show-bdd:\tshow the BDDs generated at intermediate steps in ASCII format");
    P("-show-dot:\tshow the BDDs generated at intermediate steps in dot format (use dot -Tps)");
    P("-inequalities:\t(experimental) simplify BDDs by assuming \"le\" is less-than-equal on Nat");
    P("-unsound:\tturns on the probably unsafe replacement of quantifiers by free variables");
    P("");
    P("Please read the disclaimer on the use of variable names at the end");
    P("of the syntax description");
    }

static void externalsyntax(void)
    {
    P("");
    externalsyntaxmsg();
    P("");
    P("");
    }

static void internalsyntax(void)
    {
    P("");
    internalsyntaxmsg();
    P("");
    P("");
    }

static void help(void)
    {
    P("");
    helpmsg();
    P("");
    P("");
    }

static void version(void)
    {
    char buf[100];
    sprintf(buf,"%s: version %s",who, VERSION);
    P(buf);
    }
#undef P

/************************************ General functions    **********************************/


static void Print_term(ATerm t);


static ATerm Prove_(ATerm t)
{ ATerm u=NULL;

  /* {ATfprintf(stdout,"Prover IN: "); Print_term(t); ATfprintf(stdout,"\n");}   */
  if (verbose) { fprintf(stdout,"P"); fflush(stdout); }
  u=(inequalities ? SimpIneq(Prove2(t)) : Prove2(t));
  if (verbose) { fprintf(stdout,"-"); fflush(stdout); }
  return u;
}

static ATerm Simplify_(ATerm t)
{ ATerm u=NULL;

  /* {ATfprintf(stdout,"Simplify IN: "); Print_term(t); ATfprintf(stdout,"\n");} */
  if (verbose) { fprintf(stdout,"S"); fflush(stdout); }
  u=Simplify(t);
  RWflush();
  if (verbose) { fprintf(stdout,"-"); fflush(stdout); }
  /* ATfprintf(stdout,"\nUIT:"); Print_term(u); ATfprintf(stdout,"\n"); */
  return u;
}

static ATerm Sort_of_(ATerm t)
{ ATerm u=NULL;

  /* if (verbose) {ATfprintf(stdout,"Sort_of IN: "); Print_term(t); ATfprintf(stdout,"\n");} */
  u=Sort_of(t);
  /* ATfprintf(stdout,"UIT:"); Print_term(u); ATfprintf(stdout,"\n"); */
  return u;
}

static ATermTable substituteTable=NULL;
static ATermTable substitutedTermsTable=NULL;


static ATerm substitute_var_(ATerm var)
{
  /*  ATfprintf(stdout,"PARS: %t\n",pars);
     ATfprintf(stdout,"ARGS: %t\n",args);   */

  ATerm r=ATtableGet(substituteTable,var);
  if (r==NULL)
     return var;
  return r;
}


static ATerm substitute_(ATerm t);

static ATermList substitutelist_(ATermList l)
{
  if (ATisEmpty(l)) return ATempty;
  
  return ATinsert(substitutelist_(ATgetNext(l)),
          substitute_(ATgetFirst(l)));
}



static ATerm substitute_(ATerm t)
{ ATerm t0=NULL, t1=NULL, t2=NULL, r=NULL;

  switch (ATgetArity(ATgetAFun(t)))
  { case 0: 
      { return substitute_var_(t); 
      }
    case 1:
      { 
        r=ATtableGet(substitutedTermsTable,t);
        if (r!=NULL) return r;
        t0=substitute_(ATgetArgument(t,0));
	r=(ATerm)ATmakeAppl1(ATgetAFun(t),t0);
        ATtablePut(substitutedTermsTable,t,r);
        return r; 
      }
    case 2:
      { 
        r=ATtableGet(substitutedTermsTable,t);
        if (r!=NULL) return r;
        t0=substitute_(ATgetArgument(t,0));
        t1=substitute_(ATgetArgument(t,1));
	r=(ATerm)ATmakeAppl2(ATgetAFun(t),t0,t1);
        ATtablePut(substitutedTermsTable,t,r);
        return r; 
      }
    case 3:
      { 
        r=ATtableGet(substitutedTermsTable,t);
        if (r!=NULL) return r;
        t0=substitute_(ATgetArgument(t,0));
        if (ATgetAFun(t)==itesymbol)
        { t0=RWrewrite(t0);
          if (t0==prTRUE)
          { r=substitute_(ATgetArgument(t,1)); 
            ATtablePut(substitutedTermsTable,t,r);
            return r; 
          }
          else if (t0==prFALSE)
          { r=substitute_(ATgetArgument(t,2)); 
            ATtablePut(substitutedTermsTable,t,r);
            return r; 
          }
        }
        t1=substitute_(ATgetArgument(t,1));
        t2=substitute_(ATgetArgument(t,2));
        if ((ATgetAFun(t)==itesymbol) && (t1==t2)) 
           r=t1;
	else r=(ATerm)ATmakeAppl3(ATgetAFun(t),t0,t1,t2);
        ATtablePut(substitutedTermsTable,t,r);
        return r; 
      }
    default: 
      { 
        r=ATtableGet(substitutedTermsTable,t);
        if (r!=NULL) return r;
        r=(ATerm)ATmakeApplList(ATgetAFun(t),
          substitutelist_(ATgetArguments((ATermAppl)t)));
        ATtablePut(substitutedTermsTable,t,r);
        return r; 
      }
  }

  assert(0);
  return NULL; 
}


static ATerm substitute(ATermList pars, ATermList args, ATerm t)
{ ATerm r=NULL;
  if (verbose) { fprintf(stdout,"+"); fflush(stdout); }

  /* ATfprintf(stdout,"Substitute %t %t\n",pars,args); fflush(stdout);  */

  if (substituteTable==NULL)
    substituteTable=ATtableCreate(256,50);
  if (substitutedTermsTable==NULL)
    substitutedTermsTable=ATtableCreate(512,75);
  for( ; !ATisEmpty(pars) ; )
  { ATtablePut(substituteTable,ATgetArgument(ATgetFirst(pars),0),ATgetFirst(args));
    pars=ATgetNext(pars);
    args=ATgetNext(args);
  }
  if (!ATisEmpty(args)) ATerror("List %t ought to be empty",args);
  r=substitute_(t);
  ATtableDestroy(substituteTable);
  ATtableDestroy(substitutedTermsTable);
  substituteTable=NULL;
  substitutedTermsTable=NULL;
  if (verbose) { fprintf(stdout,"-"); fflush(stdout); }
  return r;
}

static ATerm substitute_single_variable(ATerm par, ATerm arg, ATerm t)
{ 
  return substitute(ATinsert(ATempty,par),ATinsert(ATempty,arg),t);
}

static int stringcounter=0;
static char stringbuffer[ERRORLENGTH];

static char *newname(void)
{ 
  sprintf(stringbuffer,"NEWNAME%d#",stringcounter); 
  stringcounter++;
  return stringbuffer;
}

static ATermList pars2args(ATermList pars)
{ ATermList args=ATempty;
  ATerm name=NULL, sort=NULL;
  int i=0, l=ATgetLength(pars);
  for(i=0 ; i<l ; i++)
  { ATerm par=ATgetFirst(pars);
    pars=ATgetNext(pars);
    if (!ATmatch(par,"v(<term>,<term>)",&name,&sort))
    { ATerror("Ill shaped parameter %t",par); }
    args=ATinsert(args,name);
  }

  /* turn pars around */
  pars=ATempty;
  for(i=0 ; i<l ; i++)
  { pars=ATinsert(pars,ATgetFirst(args));
    args=ATgetNext(args);
  }
  return pars;
}

/************************************ Modcheck **********************************/

static int can_match(ATerm action, ATerm summand)
{ /* Determine whether the action formula action can possibly match with
     the summand; if not, no formula needs to be generated.
  */


  ATerm t=NULL,t1=NULL,t2=NULL;

  if ((ATmatch(action,"\"T#\""))||
      (ATmatch(action,"T")))
  { return 1; }
  if ((ATmatch(action,"\"F#\""))||
      (ATmatch(action,"F")))
  { return 0; }
  if (ATmatch(action,"act(<term>)",&t))
  { char *name1=NULL, *name2=NULL;
    int arity1=0, arity2=0;
    name1=ATgetName(ATgetAFun(t));
    arity1=ATgetArity(ATgetAFun(t));
    name2=ATgetName(ATgetAFun(ATgetArgument(summand,1)));
    arity2=ATgetLength(ATgetArgument(summand,2));
    if ((strcmp(name1,name2)==0) && (arity1==arity2))
      return 1;
    return 0;
  }

  if ((ATmatch(action,"\"and#Bool#Bool\"(<term>,<term>)",&t,&t1)) ||
      (ATmatch(action,"and(<term>,<term>)",&t,&t1)))
  { if (can_match(t,summand) && can_match(t1,summand))
    { return 1; }
    return 0;
  }

  if ((ATmatch(action,"\"or#Bool#Bool\"(<term>,<term>)",&t,&t1)) ||
      (ATmatch(action,"or(<term>,<term>)",&t,&t1)))
  { if (can_match(t,summand) || can_match(t1,summand))
    { return 1; }
    return 0;
  }

  if ((ATmatch(action,"\"not#Bool\"(<term>)",&t)) ||
      (ATmatch(action,"not(<term>)",&t)))
  { return 1-can_match(t,summand);
  }

  if (ATmatch(action,"forall(<term>,<term>,<term>)",&t,&t1,&t2))
  { return can_match(t2,summand); }

  if (ATmatch(action,"exists(<term>,<term>,<term>)",&t,&t1,&t2))
  { return can_match(t2,summand); }

  ATerror("Syntax error in formula: %t is not an action formula",action);
  return 1;
}

static ATerm actionmatch(ATerm action,char *name,ATermList arguments)
{ ATerm t=NULL, t1=NULL,t2=NULL;

  if ((ATmatch(action,"\"T#\""))||
      (ATmatch(action,"T")))
  { return(prTRUE); }
  if ((ATmatch(action,"\"F#\""))||
      (ATmatch(action,"F")))
  { return(prFALSE); }
  if ((ATmatch(action,"\"and#Bool#Bool\"(<term>,<term>)",&t1,&t2)) ||
            (ATmatch(action,"and(<term>,<term>)",&t,&t1)))
  { return prAND(actionmatch(t1,name,arguments),actionmatch(t1,name,arguments)); }
  if ((ATmatch(action,"\"or#Bool#Bool\"(<term>,<term>)",&t1,&t2))  ||
            (ATmatch(action,"or(<term>,<term>)",&t,&t1)))
  { return prOR(actionmatch(t1,name,arguments),actionmatch(t1,name,arguments)); }
  if ((ATmatch(action,"\"not#Bool\"(<term>)",&t1)) ||
        (ATmatch(action,"not(<term>)",&t1)))
     { return prNOT(actionmatch(t1,name,arguments)); } 
  if (ATmatch(action,"forall(<term>,<term>,<term>)",&t,&t1,&t2))
     { Declare_vars(ATinsert(ATempty,ATmake("v(<term>,<term>)",t,t1)));
       return FORALL(t,t1,actionmatch(t2,name,arguments)); 
     }
  if (ATmatch(action,"exists(<term>,<term>,<term>)",&t,&t1,&t2))
     { Declare_vars(ATinsert(ATempty,ATmake("v(<term>,<term>)",t,t1))); 
       return EXISTS(t,t1,actionmatch(t2,name,arguments)); 
     }
  if (ATmatch(action,"act(<term>)",&t1))
  { char *actname=ATgetName(ATgetAFun(t1));
    int arity=ATgetArity(ATgetAFun(t1));
    if ((strcmp(name,actname)==0) && (arity==ATgetLength(arguments)))
    { /* generate an equation saying that the arguments are equal */
      ATerm result=NULL;
      int i=0;
      for(i=0 ; i<arity ; i++)
      { 
        sprintf(stringbuffer,"eq#%s#%s",
              ATgetName(ATgetAFun(Sort_of_(ATgetArgument(t1,i)))),
              ATgetName(ATgetAFun(Sort_of_(ATgetFirst(arguments)))));


        if (result==NULL)
        { result=(ATerm)ATmakeAppl2(ATmakeAFun(stringbuffer,2,1),
                 ATgetArgument(t1,i),ATgetFirst(arguments));
        }
        else
          { result=prAND(result,(ATerm)ATmakeAppl2(ATmakeAFun(stringbuffer,2,1),
                 ATgetArgument(t1,i),ATgetFirst(arguments)));
       }
       arguments=ATgetNext(arguments);
      }
      if (result==NULL) return ATmake("\"T#\"");
      else return result;
    }
    else return ATmake("\"F#\"");
  }
  ATerror("Action formula %t has wrong syntax",action);
  return NULL;
}

static ATerm generate_may_match_formula(ATerm action, 
               ATerm summand, ATerm restformula)
{ ATerm condition=NULL,result=NULL;
  ATermList sum_variables=NULL;

  condition=ATgetArgument(summand,4);
  sum_variables=(ATermList)ATgetArgument(summand,0);

  result=prAND(condition,prAND(
         actionmatch(action,ATgetName(ATgetAFun(ATgetArgument(summand,1))),
                (ATermList)ATgetArgument(summand,2)),restformula));

  Declare_vars(sum_variables);
  for( ; !ATisEmpty(sum_variables) ; sum_variables=ATgetNext(sum_variables))
  { ATerm variable=NULL, sort=NULL;
    ATmatch(ATgetFirst(sum_variables),"v(<term>,<term>)",&variable,&sort);
    result=EXISTS(variable,sort,result);
  }

  return result;
}

static ATerm generate_must_match_formula(ATerm action, ATerm summand, ATerm restformula)
{ ATerm condition=NULL,result=NULL;
  ATermList sum_variables=NULL;

  condition=ATgetArgument(summand,4);
  sum_variables=(ATermList)ATgetArgument(summand,0);

  
  result=prOR(prNOT(prAND(condition,
         actionmatch(action,ATgetName(ATgetAFun(ATgetArgument(summand,1))),
                (ATermList)ATgetArgument(summand,2)))),restformula);

  Declare_vars(sum_variables);
  for( ; !ATisEmpty(sum_variables) ; sum_variables=ATgetNext(sum_variables))
  { ATerm variable=NULL, sort=NULL;
    ATmatch(ATgetFirst(sum_variables),"v(<term>,<term>)",&variable,&sort);
    result=FORALL(variable,sort,result);
  }

  return result;
}

static ATerm make_restformula(ATermList *stack,ATerm formula,
             ATermList parameters,ATermList local_parameters,
	     ATerm summand,ATermTable equations)
{ ATerm t=NULL;
  ATermList parlist=NULL, arglist=NULL;
  char *name=NULL;

  if ((ATmatch(formula,"\"T#\""))||
      (ATmatch(formula,"T")))
      { return prTRUE; }

  if ((ATmatch(formula,"\"F#\""))||
      (ATmatch(formula,"F")))
      { return prFALSE; }

  if (ATmatch(formula,"form(<term>)",&t))
      { ATerm g=ATgetArgument(summand,3);
       if (ATmatch(g,"i(<term>)",&g))
       return substitute(parameters,(ATermList)g,t); 
        else ATerror("Cannot deal with terminating summands in an LPO");
      }

  if (ATmatch(formula,"rec(<term>)",&t))  
  {  ATerm g=ATgetArgument(summand,3);
     ATermList l=NULL;
     ATermList local_parameters_for_t=NULL;
     ATerm name=NULL, temp=NULL;
     
     if (!ATmatch(g,"i(<term>)",&g))
        ATerror("Cannot deal with terminating summands in LPO");
     /* We need the local parameters, at the point of declaration
      *        when the function in t was declared */
     name=(ATerm)ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(t)),0,ATtrue));
     temp=ATtableGet(equations,name);
     if (temp==NULL)
          ATerror("XX Erroneous process name %t\n",name);
     local_parameters_for_t=(ATermList)ATgetArgument((ATermAppl)temp,1);
     l=ATconcat(pars2args(local_parameters_for_t),
            ATconcat(ATgetArguments((ATermAppl)t),(ATermList)g));
     
     return (ATerm)ATmakeApplList(ATmakeAFun(ATgetName(ATgetAFun(t)),ATgetLength(l),1),l);
  }

  /* else generate a new equation */

  if (ATmatch(formula,"nu(<str>,<term>,<term>,<term>)",
       &name,&parlist,&t,&arglist))
  { ATerm lhs=NULL;
    ATermList g=NULL;
    ATermList l=NULL;

    lhs=ATtableGet(equationdefs,formula);
    g=(ATermList)ATgetArgument(summand,3);
    if (!ATmatch((ATerm)g,"i(<term>)",&g))
      { ATerror("Cannot deal with terminating summands in an LPO"); }

    if (lhs==NULL)
    { variablelist=ATinsert(variablelist,ATmake("<str>",name));

      *stack=ATinsert(*stack,ATmake("nu(<str>,<term>,<term>,<term>,<term>)",
                  name,local_parameters,parlist,parameters,t)); 
       ATtablePut(equationdefs,formula,ATmake("<str>",name));
       l=ATconcat(ATconcat(pars2args(local_parameters),arglist),g); 
       return (ATerm)ATmakeApplList(ATmakeAFun(name,ATgetLength(l),ATtrue),l);
    }
    l=ATconcat(ATconcat(pars2args(local_parameters),arglist),g);
    return (ATerm)ATmakeApplList(ATmakeAFun(ATgetName(ATgetAFun(lhs)),
                             ATgetLength(l),ATtrue),l);
  }

  if (ATmatch(formula,"mu(<str>,<term>,<term>,<term>)",
       &name,&parlist,&t,&arglist))
  { ATerm lhs=ATtableGet(equationdefs,formula);
    ATermList g=(ATermList)ATgetArgument(summand,3);
    ATermList l=NULL;
    if (!ATmatch((ATerm)g,"i(<term>)",&g))
      { ATerror("Cannot deal with terminating summands in an LPO"); }

    if (lhs==NULL)
    {  variablelist=ATinsert(variablelist,ATmake("<str>",name));
       *stack=ATinsert(*stack,ATmake("mu(<str>,<term>,<term>,<term>,<term>)",
                  name,local_parameters,parlist,parameters,t)); 
       ATtablePut(equationdefs,formula,ATmake("<str>",name));
       l=ATconcat(ATconcat(pars2args(local_parameters),arglist),g);
       return (ATerm)ATmakeApplList(ATmakeAFun(name,ATgetLength(l),ATtrue),l);
    }
    l=ATconcat(ATconcat(pars2args(local_parameters),arglist),g);
    return (ATerm)ATmakeApplList(ATmakeAFun(ATgetName(ATgetAFun(lhs)),
                             ATgetLength(l),ATtrue),l);
  }

  { char *name;
    ATerm g=ATgetArgument(summand,3);
  
    ATerm lhs=ATtableGet(equationdefs,formula);
    if (lhs==NULL)
    {  name=newname();
       ATtablePut(equationdefs,formula,ATmake("<str>",name));
       variablelist=ATinsert(variablelist,ATmake("<str>",name));

       *stack=ATinsert(*stack,ATmake("nu(<str>,<term>,[],<term>,<term>)",
              name,local_parameters,parameters,formula)); 
    }
    else
     { name=ATgetName(ATgetAFun(lhs));
     }

    if (ATmatch(g,"i(<term>)",&g))
     { ATermList l=NULL;
       l=ATconcat(pars2args(local_parameters),(ATermList)g);
       return (ATerm)ATmakeApplList(ATmakeAFun(name,ATgetLength(l),ATtrue),l);
     }
    else ATerror("Cannot deal with terminating summands in LPO");
                  
    return ATmake("<str(<term>)>",name,
           pars2args(ATconcat(local_parameters,parameters)));
  }


  ATerror("Not all cases dealt with %t",formula);
  return NULL;
}

static ATerm Parse_formula(
         ATermList *stack,
         ATerm formula,
         ATermList parameters,
         ATermList local_parameters,
         ATermList summands,
         ATermTable equations)
{ ATerm t=NULL, t1=NULL;
  ATerm action=NULL;
  ATermList summand_walker=NULL;
  ATermList pars=NULL, args=NULL;
  ATerm nameterm=NULL; 
  ATerm name=NULL, sort=NULL;
  
  if ((ATmatch(formula,"\"T#\""))||
      (ATmatch(formula,"T")))
  { return prTRUE; }

  if ((ATmatch(formula,"\"F#\""))||
      (ATmatch(formula,"F")))
  { return prFALSE; }

  if (ATmatch(formula,"form(<term>)",&t))
  { return t; }

  if ((ATmatch(formula,"\"and#Bool#Bool\"(<term>,<term>)",&t,&t1)) ||
      (ATmatch(formula,"and(<term>,<term>)",&t,&t1)))
  { return prAND(Parse_formula(stack,t,parameters,local_parameters,summands,equations),
         Parse_formula(stack,t1,parameters,local_parameters,summands,equations));
  }

  if ((ATmatch(formula,"\"or#Bool#Bool\"(<term>,<term>)",&t,&t1)) ||
      (ATmatch(formula,"or(<term>,<term>)",&t,&t1)))
  { return prOR(Parse_formula(stack,t,parameters,local_parameters,summands,equations),
         Parse_formula(stack,t1,parameters,local_parameters,summands,equations));
  }

  if ((ATmatch(formula,"\"not#Bool\"(<term>)",&t)) ||
      (ATmatch(formula,"not(<term>)",&t)))
  { return prNOT(Parse_formula(stack,t,parameters,local_parameters,summands,equations));
  }

  if (ATmatch(formula,"eq(<term>,<term>)",&t,&t1))
      { t=Parse_formula(stack,t,parameters,local_parameters,summands,equations);
	t1=Parse_formula(stack,t1,parameters,local_parameters,summands,equations);
	return prOR(prAND(t,t1),prAND(prNOT(t),prNOT(t1)));
      }

  if (ATmatch(formula,"imp(<term>,<term>)",&t,&t1))
  { return prOR(prNOT(Parse_formula(stack,t,parameters,local_parameters,summands,equations)),
         Parse_formula(stack,t1,parameters,local_parameters,summands,equations));
  }

  if (ATmatch(formula,"may(<term>,<term>)",&action,&t))
  { ATerm result=NULL;
    
    for(summand_walker=summands; (!ATisEmpty(summand_walker)); 
                            summand_walker=ATgetNext(summand_walker))
    { 
      ATerm summand=NULL;
      summand=ATgetFirst(summand_walker);
      Declare_vars((ATermList)ATgetArgument(summand,0));
      if (can_match(action,summand))
      { if (result==NULL)
        { result=generate_may_match_formula(action,summand,
                make_restformula(stack,t,parameters,
                       local_parameters,summand,equations)); }
        else result=prOR(result,
           generate_may_match_formula(action,summand,
              make_restformula(stack,t,parameters,
                             local_parameters,summand,equations)));
      }

    }
    if (result==NULL)
    { return prFALSE;
    }
    else return result;
  }

  if (ATmatch(formula,"must(<term>,<term>)",&action,&t))
  { ATerm result=NULL;
    
    for(summand_walker=summands; (!ATisEmpty(summand_walker)); 
                          summand_walker=ATgetNext(summand_walker))
    { 
      ATerm summand=NULL;
      summand=ATgetFirst(summand_walker);
      Declare_vars((ATermList)ATgetArgument(summand,0));
      if (can_match(action,summand))
      { if (result==NULL)
        { result=generate_must_match_formula(action,summand,
                make_restformula(stack,t,parameters,
                  local_parameters,summand,equations)); }
          else result=prAND(result,generate_must_match_formula(action,summand,
              make_restformula(stack,t,parameters,
                    local_parameters,summand,equations)));
      }

    }
    if (result==NULL)
    { return prTRUE;
    }
    else return result;
  }

  if (ATmatch(formula,"forall(<term>,<term>,<term>)",&name,&sort,&t))
  { 
    Declare_vars(ATinsert(ATempty,ATmake("v(<term>,<term>)",name,sort)));
    return FORALL(name,sort,Parse_formula(stack,t,parameters,
             ATinsert(local_parameters,
                     ATmake("v(<term>,<term>)",name,sort)),summands,equations));
  }

  if (ATmatch(formula,"exists(<term>,<term>,<term>)",&name,&sort,&t))
  { 
    Declare_vars(ATinsert(ATempty,ATmake("v(<term>,<term>)",name,sort)));
    return EXISTS(name,sort,
        Parse_formula(stack,t,parameters, ATinsert(local_parameters,
                     ATmake("v(<term>,<term>)",name,sort)),summands,equations));
  }

  if (ATmatch(formula,"mu(<term>,<term>,<term>,<term>)",&nameterm,&pars,&t,&args))
  { variablelist=ATinsert(variablelist,
         (ATerm)ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(nameterm)),0,1)));
    *stack=ATinsert(*stack,ATmake("mu(<str>,<term>,<term>,<term>,<term>)",
               ATgetName(ATgetAFun(nameterm)),
                       local_parameters,pars,parameters,t));
    args=ATconcat(ATconcat(pars2args(local_parameters),args),pars2args(parameters));
    return (ATerm)ATmakeApplList(ATmakeAFun(ATgetName(ATgetAFun(nameterm)),
                          ATgetLength(args),1),args);
  }

  if (ATmatch(formula,"nu(<term>,<term>,<term>,<term>)",&nameterm,&pars,&t,&args))
   
  { 
    variablelist=ATinsert(variablelist,
         (ATerm)ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(nameterm)),0,1)));
    *stack=ATinsert(*stack,ATmake("nu(<str>,<term>,<term>,<term>,<term>)",
               ATgetName(ATgetAFun(nameterm)),
               local_parameters,pars,parameters,t));
    args=ATconcat(ATconcat(pars2args(local_parameters),args),pars2args(parameters));
    return (ATerm)ATmakeApplList(ATmakeAFun(ATgetName(ATgetAFun(nameterm)),
                          ATgetLength(args),1),args);
  }

  if (ATmatch(formula,"rec(<term>)",&t))
  { ATermList l=NULL;
    ATermList local_parameters_for_t=NULL;
    ATerm name=NULL, temp=NULL;
    /* We need the local parameters, at the point of declaration 
       when the function in t was declared */
    name=(ATerm)ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(t)),0,ATtrue));
    temp=ATtableGet(equations,name);
    if (temp==NULL) 
       ATerror("Erroneous process name %t\n",name);
    local_parameters_for_t=(ATermList)ATgetArgument((ATermAppl)temp,1);
    l=ATconcat(pars2args(local_parameters_for_t),
       ATconcat(ATgetArguments((ATermAppl)t),
                 pars2args(parameters))); 


    return (ATerm)ATmakeApplList(ATmakeAFun(ATgetName(ATgetAFun(t)),
               ATgetLength(l),1),l); 
  }          

  ATerror("Error translating formula %t",formula);
  return NULL;
}

static ATermTable Process_stack(
                ATermList *stack,
/*                 ATermList parameters, */
                ATermList summands,
                ATermTable equations)
{
  ATerm frame=NULL;
  ATerm formula=NULL;
  ATermList local_parameters=NULL, non_local_parameters=NULL,
            parameters=NULL;
  char *name=NULL;
  int minimal_fixed_point=0;

  if (ATisEmpty(*stack)) return equations;

  frame=ATgetFirst(*stack);
  *stack=ATgetNext(*stack);


  /* ATfprintf(stdout,"Frame: %t\n",frame); */
  
  if (ATmatch(frame,"mu(<str>,<term>,<term>,<term>,<term>)",
                 &name,&local_parameters,&non_local_parameters,
                 &parameters,&formula))
  { minimal_fixed_point=1;
  }  
  else if (ATmatch(frame,"nu(<str>,<term>,<term>,<term>,<term>)",
                     &name,&local_parameters,&non_local_parameters,
                     &parameters,&formula))
  { minimal_fixed_point=0;
  }
  else ATerror("Wrong stackframe %t",frame);

  Declare_vars(parameters);
  Declare_vars(local_parameters);
  Declare_vars(non_local_parameters);

  if (minimal_fixed_point)
  { name=AddFun(name,ATconcat(local_parameters,
               ATconcat(non_local_parameters,parameters)),prBOOL);
    /* First put a temporary version in the hash table */
    ATtablePut(equations,ATmake("<str>",name),
       ATmake("mu(<str>,<term>,<term>,<term>,this_is_the_place_for_the_body)",name,
             local_parameters,non_local_parameters,parameters));
                 
    ATtablePut(equations,ATmake("<str>",name),
       ATmake("mu(<str>,<term>,<term>,<term>,<term>)",name,
             local_parameters,non_local_parameters,parameters,
                 Simplify_(Parse_formula(stack,formula,parameters,
                              ATconcat(local_parameters,non_local_parameters),
			            summands,equations))));
       /* was Simplify hierboven, en hieronder, JFG. */
  }
  else
  { 
    name=AddFun(name,ATconcat(local_parameters,
               ATconcat(non_local_parameters,parameters)),prBOOL);
    /* First put a temporary version in the hash table */
    ATtablePut(equations,ATmake("<str>",name),
       ATmake("nu(<str>,<term>,<term>,<term>,this_is_the_place_for_the_body)",name,
                local_parameters,non_local_parameters,parameters));
    ATtablePut(equations,ATmake("<str>",name),
       ATmake("nu(<str>,<term>,<term>,<term>,<term>)",name,
                local_parameters,non_local_parameters,parameters,
	         Simplify_(Parse_formula(stack,formula,parameters,
                           ATconcat(local_parameters,non_local_parameters),
			         summands,equations))));

  }
  return Process_stack(stack,/* parameters, */summands,equations);
}

static ATermTable Generate_equations(
                ATerm formula, ATermList parameters,ATermList summands)
{ /* The generated equations have the format:

     mu(name,localparameterlist,parameterlist,lpoparameters,righthandside) or
     nu(name,localparameterlist,parameterlist,lpoparameters,righthandside)

     (the localparameterlist contains variables that occur globally to the
      proces definition)

     and are delivered in a list.

     We use an intermediated stack format on which we put equations
     mu(name,local variables from the formula, formula)
     nu(name,local variables from the formula, formula)

  */
  

  ATermList stack=ATempty;
  ATermTable equations=NULL;

  equations=ATtableCreate(64,80);

  variablelist=ATinsert(variablelist,ATmake("<str>","START#"));
  stack=ATinsert(stack,ATmake("nu(\"START#\",<term>,<term>,<term>,<term>)",
                         ATempty,ATempty,parameters,formula));
  
  return Process_stack(&stack,/* parameters,*/summands,equations);

}


static void printstring_without_hash(char *var)
{ /* also quotes are filtered out */
  int i=0;
  for(i=0 ; (var[i]!='#') && (var[i]!='\0') ; i++)
  { if (var[i]!='"') fprintf(stdout,"%c",var[i]); }
}

static void Print_term(ATerm t)
{ int i=0, arity=0;
  
  printstring_without_hash(ATgetName(ATgetAFun(t)));
  arity=ATgetArity(ATgetAFun(t));
  for(i=0 ; i<arity ; i++)
  { 
    fprintf(stdout,"%c",(i==0)?'(':',');
    Print_term(ATgetArgument(t,i));
  }
  if (arity>0) fprintf(stdout,")");
}

static void Print_parameters(ATermList pars)
{  int begin=1;
   char *var=NULL, *type=NULL;
   while (!ATisEmpty(pars))
   { ATerm par=ATgetFirst(pars);
     fprintf(stdout,"%s",((begin)?"(":","));
     begin=0;
     if (!ATmatch(par,"v(<str>,<str>)",&var,&type))
        ATerror("Wrong parameter %t",par);
     printstring_without_hash(var);
     fprintf(stdout,":%s",type);
     pars=ATgetNext(pars);
   }
   fprintf(stdout,")");
}

static void Print_equation(ATerm eqn, int counterexample)
{ 
  char *name=NULL;
  ATerm t=NULL; 
  ATermList pars1=NULL, pars2=NULL, localpars=NULL;

  if (ATmatch(eqn,"nu(<str>,<term>,<term>,<term>,<term>)",
            &name,&localpars,&pars1,&pars2,&t))
  { ATfprintf(stdout,"\nMAX ");
  }


  if (ATmatch(eqn,"mu(<str>,<term>,<term>,<term>,<term>)",
            &name,&localpars,&pars1,&pars2,&t))
  { ATfprintf(stdout,"\nMIN ");
  }
  printstring_without_hash(name);

  Print_parameters(ATconcat(localpars,ATconcat(pars1,pars2)));

  if (counterexample)
  { fprintf(stdout,"\n");
    if (showsize) count_BDD(t,stdout);
    print_example(t,prFALSE,stdout);
    print_example(t,prTRUE,stdout);
    fflush(stdout);
    return;
  }

  fprintf(stdout,"=");

  Print_term(t);
  fprintf(stdout,"\n\n");
  fflush(stdout);
}

static void Print_equations(ATermTable equations, int counterexample)
{ ATermList eqns=ATtableValues(equations);
  while (!ATisEmpty(eqns))
  { Print_equation(ATgetFirst(eqns),counterexample);
    eqns=ATgetNext(eqns);
  }

}

/***********************************  read formula ****************************/

static char inputstring[ERRORLENGTH];

typedef enum scansymbol {NONE,END_OF_FILE,SPACE,STRING,ROUND_BRACKET_OPEN,
             ROUND_BRACKET_CLOSE,COMMA,
             AND_SYMBOL,OR_SYMBOL,NOT_SYMBOL,EXISTS_SYMBOL,COLON,
             DOT,FORALL_SYMBOL,ANGLE_BRACKET_OPEN,
             ANGLE_BRACKET_CLOSE,SQUARE_BRACKET_OPEN,
             SQUARE_BRACKET_CLOSE} scansymbol;

static int lookahead=0;
static int line=1;
static int position=1;

static int get_character(FILE *f)
{ 
  int c;
  c=fgetc(f); 

  if (((c>='a')&&(c<='z'))||
                   ((c>='A')&&(c<='Z'))||
                  ((c>='0')&&(c<='9'))||
                   (c=='^')||(c=='_')||(c=='\'')||(c=='%')||
                   (c=='-')||(c=='(')||(c==')')||(c=='[')||
                   (c==']')||(c=='<')||(c=='>')||(c=='?')||
                   (c=='!')||(c==',')||(c=='.')||
                   (c=='&')||(c=='|')||(c=='~')||(c==EOF)||
                   (c==' ')||(c=='\n')||(c==':')) 
  { if (c=='\n') 
    { line++;position=1; c=' ';
    }
    else position++; 
    return c;
  }
  ATerror("Unexpected symbol `%c' at line %d position %d.",c,line,position);
  return -1;
}

static void scan_string(FILE *f)
{ int i=0;
  for (i=0 ; i<ERRORLENGTH-1 ; i++)
  { 
    if (lookahead==EOF)
      { inputstring[i+1]='\0';
        return;
      }

    inputstring[i]=lookahead;
    lookahead=get_character(f);
    if (!(((lookahead>='a')&&(lookahead<='z'))||
         ((lookahead>='A')&&(lookahead<='Z'))||
         ((lookahead>='0')&&(lookahead<='9'))||
          (lookahead=='^')||(lookahead=='_')||(lookahead=='\'')||(lookahead=='-')))
     { inputstring[i+1]='\0';
       return;
     }
  }
  inputstring[i]='\0';
  ATerror("String in formula file is too long: %s",inputstring);
  return;

}

static void skip_comment(FILE *f)
{ int c;
  do
  { c=fgetc(f);
  }
  while ((c!='\n') && (c!=EOF));
  line++;position=1;
}

static scansymbol scan_formula(FILE *f)
{ /* in case a string is read, it can be found in "inputstring". 
     in case an error is detected, it is reported immediately  */

  char result='\0';
  if (lookahead=='\0') lookahead=get_character(f);

  switch (lookahead) {
  case EOF:result=END_OF_FILE ; break;
  case '!':result=FORALL_SYMBOL; break;
  case '?':result=EXISTS_SYMBOL; break;
  case '>':result=ANGLE_BRACKET_CLOSE; break;
  case '<':result=ANGLE_BRACKET_OPEN; break;
  case '[':result=SQUARE_BRACKET_OPEN; break;
  case ']':result=SQUARE_BRACKET_CLOSE; break;
  case ')':result=ROUND_BRACKET_CLOSE; break;
  case '(':result=ROUND_BRACKET_OPEN; break;
  case ',':result=COMMA; break;
  case '.':result=DOT; break;
  case ':':result=COLON; break;
  case '&':result=AND_SYMBOL; break;
  case '|':result=OR_SYMBOL; break;
  case '~':result=NOT_SYMBOL; break;
  case ' ':lookahead=get_character(f); return scan_formula(f); 
  case '%':skip_comment(f);lookahead=get_character(f); return scan_formula(f);
  default:scan_string(f); return STRING; 
  }

  lookahead=get_character(f);
  return result;
}

/*************************  FIXED POINT ALGORITME  ******************/


static ATermList make_initial_solution(ATermList equations)
{ ATerm equation=NULL, t=NULL;
  ATermList pars1=NULL, pars2=NULL, localpars=NULL;
  char *name=NULL;

  if (ATisEmpty(equations)) return ATempty;
  equation=ATgetFirst(equations);
  if (ATmatch(equation,"nu(<str>,<term>,<term>,<term>,<term>)",
           &name,&localpars,&pars1,&pars2,&t))
    { return ATinsert(make_initial_solution(ATgetNext(equations)),
                ATmake("nu(<str>,<term>,\"T#\")",
                    name,ATconcat(localpars,ATconcat(pars1,pars2))));
    }
  if (ATmatch(equation,"mu(<str>,<term>,<term>,<term>,<term>)",
           &name,&localpars,&pars1,&pars2,&t))
    { return ATinsert(make_initial_solution(ATgetNext(equations)),
         ATmake("mu(<str>,<term>,\"F#\")",
             name,ATconcat(localpars,ATconcat(pars1,pars2))));
    }
  ATerror("Internal error: %t",equation);
  return NULL;
}

static ATerm functionsubstitute(ATerm t,ATermList fps);

static ATermList functionsubstitutelist(ATermList args,ATermList fps)
{

  if (ATisEmpty(args)) return ATempty;

  return ATinsert(functionsubstitutelist(ATgetNext(args),fps),
               functionsubstitute(ATgetFirst(args),fps));

}

static int match(char *name,ATermList fps, ATermList *pars, ATerm *t)
{
  ATfprintf(stdout,"FPS: %t\n",fps);
  for( ; !ATisEmpty(fps) ; fps=ATgetNext(fps))
  { if (strcmp(name,ATgetName(ATgetAFun(ATgetArgument(ATgetFirst(fps),0))))==0)
    { *pars=(ATermList)ATgetArgument(ATgetFirst(fps),1);
      *t=ATgetArgument(ATgetFirst(fps),2);
      return 1;
    }
  }
  return 0;
}

static ATerm functionsubstitute(ATerm t,ATermList fps)
{ 

 char *name=NULL;
 ATermList pars=NULL;
 ATerm t1=NULL;

 /* ATfprintf(stdout,"FUNCTIONSUSB: %t\n%t\n",t,fps); */
 name=ATgetName(ATgetAFun(t));
 
 if (match(name,fps,&pars,&t1))
 { ATermList args=ATgetArguments((ATermAppl)t);
   return substitute(pars,args,t1);
 }
 
 return (ATerm)ATmakeApplList(ATgetAFun(t),
         functionsubstitutelist(ATgetArguments((ATermAppl)t),fps));

 return NULL;
}


static void Print_report(
  ATerm result,
  ATermList initialstate,
  ATermList parameters)
{ ATerm reduced_result;
  if ((monitor) || (showsize))
     ATfprintf(stdout,"\nReport:\n");

  reduced_result=Prove_(substitute(parameters,initialstate,result));
  
  if (reduced_result==prTRUE)
     ATfprintf(stdout,"Modal formula holds in the initial state\n");
  else if (reduced_result==prFALSE)
     ATfprintf(stdout,"Modal formula does not hold in the initial state\n");
  else { ATfprintf(stdout,"Modal formula is undetermined in the initial state:\n");
         Print_term(reduced_result);ATfprintf(stdout,"\n"); 
       }

  if (result==prTRUE)
     ATfprintf(stdout,"Modal formula is valid for all states\n");
  else if (result==prFALSE)
     ATfprintf(stdout,"Modal formula is invalid for all states\n");
  return;
}

static ATerm substitute_inequality_rec(ATermList l1, ATermList l2, ATerm t)
{
  /* We assume that the term t has an if-then-else structure, or is a constant T or F 
  *  Code must be adapted to yield a proper eqBDD. Therefore, shared subterms must
  *  be checked. The term t is simplified under the assumption that all terms
  *  in l1 are equal, the terms in l2 are equal, and the terms in l1 and l2
  *  differ. */

  ATerm eq=NULL;
  /* ATfprintf(stdout,"TEST %t   %t     %t   %d\n",l1,l2,t,ATgetArity(ATgetAFun(t))); 
  fflush(stdout); */
  assert(((ATgetArity(ATgetAFun(t))==0) | (ATgetArity(ATgetAFun(t))==3)));
  
  if (ATgetArity(ATgetAFun(t))==0) return t;
  /* arity equals 3 */

  eq=ATgetArgument(t,0);
  if (Is_eq(eq))
  { 
    if (ATindexOf(l1,ATgetArgument(eq,0),0)>=0)
      { if (ATindexOf(l2,ATgetArgument(eq,1),0)>=0)
        { /* the equality eq cannot hold under the assumption 
      	   that lists l1 and l2 are different */
          return substitute_inequality_rec(l1,l2,ATgetArgument(t,2));
        }
        return (ATerm)ATmakeAppl3(ATgetAFun(t),eq,
	     substitute_inequality_rec(ATinsert(l1,ATgetArgument(eq,1)),l2,
                             (ATerm)ATgetArgument(t,1)),
	     substitute_inequality_rec(l1,l2,(ATerm)ATgetArgument(t,2)));

      }
    if (ATindexOf(l2,ATgetArgument(eq,0),0)>=0)
      { if (ATindexOf(l1,ATgetArgument(eq,1),0)>=0)
        { /* the equality eq cannot hold under the assumption 
	     that lists l1 and l2 are different */
          return substitute_inequality_rec(l1,l2,ATgetArgument(t,2));
        }
        return (ATerm)ATmakeAppl3(ATgetAFun(t),eq,
	     substitute_inequality_rec(l1,ATinsert(l2,ATgetArgument(eq,1)),
                                ATgetArgument(t,1)),
	     substitute_inequality_rec(l1,l2,ATgetArgument(t,2)));
      }
    if (ATindexOf(l1,ATgetArgument(eq,1),0)>=0)
      { /* does not hold and therefore does not need to be considered: 
                (ATindexOf(l2,ATgetArgument(eq,0),0)>=0) */
        return (ATerm)ATmakeAppl3(ATgetAFun(t),eq,
	     substitute_inequality_rec(ATinsert(l1,ATgetArgument(eq,0)),l2,
                        (ATerm)ATgetArgument(t,1)),
	     substitute_inequality_rec(l1,l2,(ATerm)ATgetArgument(t,2)));
  
      }
    if (ATindexOf(l2,ATgetArgument(eq,1),0)>=0)
      { /* following does not hold here: (ATindexOf(l1,ATgetArgument(eq,1),0)>=0) */
        return (ATerm)ATmakeAppl3(ATgetAFun(t),eq,
	     substitute_inequality_rec(l1,ATinsert(l2,ATgetArgument(eq,0)),
                        ATgetArgument(t,1)),
	     substitute_inequality_rec(l1,l2,ATgetArgument(t,2)));
      }
  }
  return  (ATerm)ATmakeAppl3(ATgetAFun(t),eq,
              substitute_inequality_rec(l1,l2,ATgetArgument(t,1)),
	      substitute_inequality_rec(l1,l2,ATgetArgument(t,2)));


}


static ATerm substitute_inequality(ATerm var1, ATerm var2, ATerm t)
{
  t=substitute_inequality_rec(ATinsert(ATempty,var1),
                         ATinsert(ATempty,var2),t);
  return t;
}

static int occurs_in(ATerm var,ATerm t)
{
  int arity=0, i=0;

  if (var==t)
     return 1;

  arity=ATgetArity(ATgetAFun(t));
 
  for(i=0 ; i<arity ; i++)
  { if (occurs_in(var,ATgetArgument(t,i)))
       return 1;
  }
  return 0;

}

static ATermList Merge(ATermList l1, ATermList l2)
{
  ATermList result=l2;
  
  for( ; !ATisEmpty(l1); l1=ATgetNext(l1) )
  { 
    if (ATindexOf(l2,ATgetFirst(l1),0)<0)
    { result=ATinsert(result,ATgetFirst(l1));
    }
  }
  
  return result;

}

static ATerm search_e_candidate(ATerm var, char *eqfunction, ATerm t)
{ 
  ATerm t1=NULL, t2=NULL;
  int n=0, i=0;

  /* first try to find out whether we are dealing with a relevant eq
   *  function.
   */

  n=ATgetArity(ATgetAFun(t));

  if (n==2)
   { t1=ATgetArgument(t,0);
     t2=ATgetArgument(t,1);

     if ((t1==var) & (strcmp(ATgetName(ATgetAFun(t)),eqfunction)==0))
      { return t2;
      }
    if ((t2==var) & (strcmp(ATgetName(ATgetAFun(t)),eqfunction)==0))
      { return t1;
      }

   }

    for(i=0 ; i<n ; i++)
    { ATerm result;
      
      result=search_e_candidate(var,eqfunction,ATgetArgument(t,i));
      if (result!=NULL)
       { return result;
       }	
    }

     return NULL; 
}


static ATermList search_e_candidates(ATerm var, char *eqfunction, ATerm t)
{ ATermList results=ATempty;
  ATerm t1=NULL, t2=NULL;
  int n=0, i=0;

  /* first try to find out whether we are dealing with a relevant eq
  *  function.
  */

  n=ATgetArity(ATgetAFun(t));
  
  if (n==2)
  { t1=ATgetArgument(t,0);
    t2=ATgetArgument(t,1);
    
    if ((t1==var) & (t1!=t2) & (strcmp(ATgetName(ATgetAFun(t)),eqfunction)==0))
    { return ATinsert(results,t2);
    }
    if ((t2==var) & (t1!=t2) & (strcmp(ATgetName(ATgetAFun(t)),eqfunction)==0))
    { return ATinsert(results,t1);
    return results;
    }

  }

  for(i=0 ; i<n ; i++)
  { results=Merge(results,search_e_candidates(var,eqfunction,ATgetArgument(t,i)));
  }

  return results;
}

static ATerm make_equations(ATerm var,ATermList list, 
                     int connective,char *eqfunction,int negate)
{ /* connective is 1 generates and's, otherwise or's */

  ATerm result=NULL,  equality=NULL;
  for( ; !ATisEmpty(list) ; list=ATgetNext(list) )
  { equality=ATmake("<str(<term>,<term>)>",eqfunction,var,ATgetFirst(list));
    if (negate)
    { equality = prNOT(equality);
    }
    if (result==NULL)
    { result=equality;
    }
    else 
    { if (connective==1)
      { result=prAND(equality,result);
      }
      else
      { result=prOR(equality,result);
      }
    }
  }

  if (result==NULL)
  { if (connective==1) 
       return prTRUE;
    return prFALSE;
  }
  return result;
}

static ATerm eliminate_universal_quantifier(ATerm var, ATerm sort, ATerm t)
{ /* 
     If it holds that for some value e, phi
     can be written as phi=if(d=e,psi,chi) where d does not occur in chi.
     then forall(d,D,phi) equals forall d (d=/=e or chi) and psi[d:=e].
     In case chi is true, this reduces to psi[d:=e].
     In case D has one element, this reduces to psi[d:=e].
     In case D has more than one element, this
     reduces to chi and psi[d:=e].

  */

  ATerm e_candidate=NULL, result_formula=prTRUE, t1=NULL,old_t=t, newvar=NULL;
  ATermList e_candidates=ATempty, e_pre_candidates=ATempty;
  char buffer[ERRORLENGTH];
  int varcounter=0;
 
  t=Prove_(t); /* This is needed to remove subterms of the form
                     eq(x,x) and to bring t in BDD form */

  /* First try to show that the variable does not occur in t1 */

  if (!occurs_in(var,t))
    { if (verbose) 
        ATfprintf(stdout,"Remove universal quantifier over variable %t of sort %a as %t does not occur freely\n",
            var,MCRLgetSort(var),var); 
      return t;
    }

  /* Next try to remove the universal quantor by simple enumeration,
     assuming that we are dealing with an enumerated sort */


  if (MCRLisFiniteSort(MCRLgetSort(var)))
  { 
    ATermList elements=MCRLgenerateElementsOfFiniteSort(MCRLgetSort(var));
    if (verbose) 
       ATfprintf(stdout,"Eliminate universal quantifier over %t:%a by enumeration\n",
             var,MCRLgetSort(var));

    for( ; !ATisEmpty(elements) ; elements=ATgetNext(elements))
    { if (result_formula==prTRUE)
      { result_formula=substitute_single_variable(
                   ATmake("v(<term>,<term>)",var,sort),ATgetFirst(elements),t);
      }
      else result_formula=prAND(result_formula,
               substitute_single_variable(ATmake("v(<term>,<term>)",var,sort),
                       ATgetFirst(elements),t));
    }
    return result_formula;
  }

  sprintf(buffer,"eq#%s#%s",ATgetName(ATgetAFun(sort)),ATgetName(ATgetAFun(sort)));

  for(e_pre_candidates=search_e_candidates(var,buffer,t); 
      e_pre_candidates!=ATempty;
      e_pre_candidates=search_e_candidates(var,buffer,t) )

  { int candidate_found=0;
    for( ; !ATisEmpty(e_pre_candidates) ; 
           e_pre_candidates=ATgetNext(e_pre_candidates))
    { e_candidate=ATgetFirst(e_pre_candidates);
      candidate_found=1;
      t1=Prove_(substitute_inequality(var,e_candidate,t));
      if (!occurs_in(var,t1))
      { 
        break; }
    }

    if (candidate_found==0) 
    { break;
    }

    if (verbose)
       ATfprintf(stdout,"Split term depending on whether variable %t is equal to %t\n",var,e_candidate);

    result_formula=
         prAND(result_formula,prOR(make_equations(e_candidate,e_candidates,0,buffer,0),
            substitute(
               (ATermList)ATmake("[v(<term>,<term>)]",var,sort),
               (ATermList)ATmake("[<term>]",e_candidate),t)));
    if(occurs_in(var,result_formula))
    { ATfprintf(stdout,
         "TROUBLE in intermediate formula which can be due to missing equation eq(x,x)=T:\n");
      Print_term(substitute(
              (ATermList)ATmake("[v(<term>,<term>)]",var,sort),
              (ATermList)ATmake("[<term>]",e_candidate),t));
      ATerror("Terminated");
    }

    e_candidates=ATinsert(e_candidates,e_candidate);
    t=t1;
  }

  if ((t1!=NULL) && (!occurs_in(var,t1)))
  { result_formula=prAND(result_formula,t1);
    ATfprintf(stdout,"The universally quantified variable %t:%t has been eliminated under assumption that the size of %t is sufficiently large\n",var,sort,sort);

    return result_formula;
  } 

  if (verbose) {
    ATfprintf(stdout,
	      "Cannot eliminate universally quantified variable %t of sort %t in\n",var,sort);
    Print_term(t);ATfprintf(stdout,"\n\n");
  }
  else  ATfprintf(stdout,
		  "Cannot eliminate universally quantified variable %t of sort %t\n",var,sort);
  if (sound) exit(-1);
  do {
    sprintf(buffer,"forall%d_%s",varcounter++,ATgetName(ATgetAFun(var)));
    newvar=ATmake(buffer); }
  while (occurs_in(newvar,old_t));
  Declare_vars((ATermList)ATmake("[v(<term>,<term>)]",newvar,sort));
  ATfprintf(stdout,
      "Therefore substitute variable %t of sort %t by globally universally quantified variable %t,\n",var,sort,newvar);
  return substitute_single_variable(ATmake("v(<term>,<term>)",var,sort),newvar,old_t);
}

static ATerm eliminate_existential_quantifier(ATerm var, ATerm sort, ATerm t)
{ 

  ATerm e_candidate=NULL, result_formula=prFALSE, t1=NULL, newvar=NULL, old_t=t;

  ATermList e_candidates=ATempty, e_pre_candidates=ATempty;
  char buffer[ERRORLENGTH];
  int varcounter=0;

  /* This is needed to remove subterms of the form
                     eq(x,x), and to bring t in BDD form */

  t=Prove_(t);

  /* First try to show that the variable does not occur in t1 */

  if (!occurs_in(var,t))
    { if (verbose)
      ATfprintf(stdout,"Remove existential quantifier over variable %t of sort %a as %t does not occur freely\n",
            var,MCRLgetSort(var),var);    
return t;
    }

 /* Next try to remove the existential quantor by simple enumeration,
    provided that we are dealing with an enumerated sort */

  if (MCRLisFiniteSort(MCRLgetSort(var)))
  { 
    ATermList elements=MCRLgenerateElementsOfFiniteSort(MCRLgetSort(var));
    if (verbose) 
       ATfprintf(stdout,"Eliminate existential variable %t:%a by enumeration\n",
             var,MCRLgetSort(var));

    for( ; !ATisEmpty(elements) ; elements=ATgetNext(elements))
    { if (result_formula==prFALSE)
      { result_formula=substitute_single_variable(ATmake("v(<term>,<term>)",var,sort),
                   ATgetFirst(elements),t);
      }
      else result_formula=prOR(result_formula,
               substitute_single_variable(ATmake("v(<term>,<term>)",var,sort),
                           ATgetFirst(elements),t));
    }
    return result_formula;
  }


  sprintf(buffer,"eq#%s#%s",ATgetName(ATgetAFun(sort)),ATgetName(ATgetAFun(sort)));
  
  for(e_pre_candidates=search_e_candidates(var,buffer,t);
      e_pre_candidates!=ATempty ;
      e_pre_candidates=search_e_candidates(var,buffer,t) )
  
  { int candidate_found=0;
    for( ; !ATisEmpty(e_pre_candidates) ;
           e_pre_candidates=ATgetNext(e_pre_candidates))
    { e_candidate=ATgetFirst(e_pre_candidates);
      candidate_found=1;
      t1=Prove_(substitute_inequality(var,e_candidate,t));
      if (!occurs_in(var,t1))
      { break; }
    }

    if (candidate_found==0)
    { break;
    }

    if (verbose)
       ATfprintf(stdout,"Split term depending on whether variable %t is equal to %t\n",var,e_candidate);

    result_formula=
      prOR(result_formula,prAND(make_equations(e_candidate,e_candidates,1,buffer,1),
           substitute(
              (ATermList)ATmake("[v(<term>,<term>)]",var,sort),
              (ATermList)ATmake("[<term>]",e_candidate),t)));
    if(occurs_in(var,result_formula))
    { ATfprintf(stdout,
         "TROUBLE in intermediate formula which can be due to missing equation eq(x,x)=T\n");
      Print_term(substitute(
              (ATermList)ATmake("[v(<term>,<term>)]",var,sort),
              (ATermList)ATmake("[<term>]",e_candidate),t));
      ATerror("Terminated");
    }

 
    e_candidates=ATinsert(e_candidates,e_candidate);
    t=t1;
  }
  
  if ((t1!=NULL) && (!occurs_in(var,t1)))
  { result_formula=prOR(result_formula,t1);
    ATfprintf(stdout,"The existentially quantified variable %t:%t has been eliminated under assumption that size of %t is sufficiently large\n",var,sort,sort);
    return result_formula;
  }
  if (verbose) {
    ATfprintf(stdout,
	      "Cannot eliminate existentially quantified variable %t:%t in\n",var,sort);
    Print_term(t);ATfprintf(stdout,"\n");
  }
  else
    ATfprintf(stdout,
	      "Cannot eliminate existentially quantified variable %t:%t\n",var,sort);
  if (sound) exit(-1);
  do {    
    sprintf(buffer,"exists%d_%s",varcounter++,ATgetName(ATgetAFun(var)));
    newvar=ATmake(buffer); }
  while (occurs_in(newvar,old_t)); 
  Declare_vars((ATermList)ATmake("[v(<term>,<term>)]",newvar,sort));
  ATfprintf(stdout,
      "Therefore substitute variable %t of sort %t by globally existentially quantified variable %t,\n",var,sort,newvar);
  return substitute_single_variable(ATmake("v(<term>,<term>)",var,sort),newvar,old_t);

}


static ATerm find_equation(ATerm variable,ATermTable equations)
{ 
  return ATtableGet(equations,variable);
}

static void set_symbols(void)
{ 
  ATprotectAFun(truesymbol);
  truesymbol=ATmakeAFun("T#",0,1);
  ATprotectAFun(falsesymbol);
  falsesymbol=ATmakeAFun("F#",0,1);
  ATprotectAFun(andsymbol);
  andsymbol=MCRLsym_and;
  ATprotectAFun(orsymbol);
  orsymbol=MCRLsym_or;
  notsymbol=MCRLsym_not;
  itesymbol=MCRLsym_ite;
  ATprotectAFun(forallsymbol);
  forallsymbol=ATmakeAFun("forall",3,0);
  ATprotectAFun(existssymbol);
  existssymbol=ATmakeAFun("exists",3,0);
}


static ATerm Solve_rec(ATerm old_solution,ATerm variable,ATerm t,ATermTable equations)
{ 
  ATerm equation=NULL;
  ATerm fname=NULL;
  AFun s=ATgetAFun(t); 

  if (verbose) { ATfprintf(stdout,"#"); fflush(stdout); }

  if (s==truesymbol) return prTRUE;
  if (s==falsesymbol) return prFALSE;
  if (s==andsymbol) 
        return prAND(Solve_rec(old_solution,variable,ATgetArgument(t,0),equations),
                   Solve_rec(old_solution,variable,ATgetArgument(t,1),equations)); 
  /*      return Combine2(andsymbol,
                   Solve_rec(old_solution,variable,ATgetArgument(t,0),equations),    
                   Solve_rec(old_solution,variable,ATgetArgument(t,1),equations)); */

  if (s==orsymbol)
  { return prOR(Solve_rec(old_solution,variable,ATgetArgument(t,0),equations),
                 Solve_rec(old_solution,variable,ATgetArgument(t,1),equations)); 
    /* return Combine2(orsymbol,
                   Solve_rec(old_solution,variable,ATgetArgument(t,0),equations),
                   Solve_rec(old_solution,variable,ATgetArgument(t,1),equations)); */
  }
  if (s==notsymbol)
  { return prNOT(Solve_rec(old_solution,variable,ATgetArgument(t,0),equations)); 
   /*  return Combine1(notsymbol, Solve_rec(old_solution,variable,ATgetArgument(t,0),equations)); */
  }
  if (s==itesymbol)
  { return prITE(Solve_rec(old_solution,variable,ATgetArgument(t,0),equations),
                     Solve_rec(old_solution,variable,ATgetArgument(t,1),equations),
                     Solve_rec(old_solution,variable,ATgetArgument(t,2),equations));
  }
  if (s==forallsymbol)
  {  ATerm var=ATgetArgument(t,0);
     ATerm sort=ATgetArgument(t,1);
     ATerm t1=ATgetArgument(t,2);
     Declare_vars(ATinsert(ATempty,ATmake("v(<term>,<term>)",var,sort)));
     t1=Simplify_(Solve_rec(old_solution,variable,t1,equations));
     return eliminate_universal_quantifier(var,sort,t1);
  }
  if (s==existssymbol)
  { ATerm var=ATgetArgument(t,0);
    ATerm sort=ATgetArgument(t,1);
    ATerm t1=ATgetArgument(t,2);
    Declare_vars(ATinsert(ATempty,ATmake("v(<term>,<term>)",var,sort)));
    t1=Simplify_(Solve_rec(old_solution,variable,t1,equations));
    return eliminate_existential_quantifier(var,sort,t1);
  }

  fname=(ATerm)ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(t)),0,1));

  if (fname==variable)
  { equation=ATtableGet(equations,fname); 
    if (equation==NULL) ATerror("Internal inconsistency");
    /* So, we are dealing with a boolean variable here, instead
       of an arbitrary expression */

    return substitute(
            ATconcat((ATermList)ATgetArgument((ATermAppl)equation,1),
            ATconcat((ATermList)ATgetArgument((ATermAppl)equation,2),
                     (ATermList)ATgetArgument((ATermAppl)equation,3))),
             ATgetArguments((ATermAppl)t),old_solution);
  }
   
  return t;
}

static int stable(ATerm old_solution, ATerm new_solution,
                      int max_fixed_point)
{

    /* ATfprintf(stdout,"NEwW %t\n OLD %t\n",new_solution,old_solution); */
    /* could use knowledge on init to terminate prematurely */

    ATerm t=NULL;

    if (counterexample)
    { ATfprintf(stdout,"Stable starts\n");fflush(stdout); }
    if (max_fixed_point)
    { 
      t=Combine2(orsymbol,new_solution,
		      Combine1(notsymbol,old_solution));
      if (t==prTRUE)
      return 1;
      t=Eqbdd(t);

      if (t==prTRUE)
          return 1; 
			          
      if (showsize) count_BDD(t,stdout); fflush(stdout);
      if (counterexample) print_example(t,prFALSE,stdout);
      return 0;
    }

    t=Combine2(orsymbol,old_solution,
		    Combine1(notsymbol,new_solution));
    if (t==prTRUE)
            return 1;
    t=Eqbdd(t);
    if (t==prTRUE)
        return 1;

     if (showsize) count_BDD(t,stdout);
     if (counterexample) print_example(t,prFALSE,stdout);
     return 0;
}


static ATerm Solve(ATerm variable,ATermTable equations)
{
  char *name=NULL;
  int max_fixed_point=0, round=0;
  ATerm equation=NULL, t=NULL, new_solution=NULL, old_solution=NULL ;
  ATermList pars1=NULL, pars2=NULL, localpars=NULL;

  if (monitor) ATfprintf(stdout,"SOLVE %t\n",variable); 

  equation=find_equation(variable,equations);

  if (equation==NULL)
     ATerror("Cannot find an equation for %t\n",variable);

  if (ATmatch(equation,"nu(<str>,<term>,<term>,<term>,<term>)",
           &name,&localpars,&pars1,&pars2,&t))
  { new_solution=prTRUE;
    max_fixed_point=1;
  }
  else 
  if (ATmatch(equation,"mu(<str>,<term>,<term>,<term>,<term>)",
           &name,&localpars,&pars1,&pars2,&t))
  { new_solution=prFALSE;
    max_fixed_point=0;
  }
  else ATerror("No match: internal error %t",equation);

  do
  { old_solution=new_solution;
    round++;
    if (monitor) ATfprintf(stdout,"Iterate (%d): %t\n",round,variable);
    /* ATtablePut(fps,variable,new_solution); */
    new_solution=Prove_(Solve_rec(old_solution,variable,t,equations)); 

    /* Print_term(new_solution); ATfprintf(stdout,"Hier\n");  */
    if (showsize)
         ATfprintf(stdout,"\nSIZE OF NEW SOLUTION IN ATERMNODES: %d\n",
	         ATcalcUniqueSubterms(new_solution)); 
    if (show_bdd) print_BDD(new_solution,stdout); 
    if (show_dot) dot_BDD(new_solution,stdout); 
    if (counterexample) fprintf(stdout,"------------------\n\n"); fflush(stdout);
 
  } while (!stable(old_solution,new_solution,max_fixed_point));

  return old_solution; 
}

static ATerm substitute_single_boolean_variable(
    ATerm solution,
    ATerm variable,
    ATerm t,
    ATermTable equations);

static ATermList substitute_single_boolean_variableList(
    ATerm solution,
    ATerm variable,
    ATermList l,
    ATermTable equations)
{ if (ATisEmpty(l)) return l;
  return ATinsert(
    substitute_single_boolean_variableList(solution,variable,ATgetNext(l),equations),
    substitute_single_boolean_variable(solution,variable,ATgetFirst(l),equations));
}

static ATerm substitute_single_boolean_variable(
    ATerm solution,
    ATerm variable,
    ATerm t,
    ATermTable equations)
{ /* ATfprintf(stdout,"single_func %t   %t\n",variable,t);  */

  { AFun s=ATgetAFun(t);
    if (s==truesymbol) return prTRUE;
    if (s==falsesymbol) return prFALSE;
    if (s==andsymbol)
            return prAND(substitute_single_boolean_variable
             (solution,variable,ATgetArgument(t,0),equations),
                     substitute_single_boolean_variable
             (solution,variable,ATgetArgument(t,1),equations));
    if (s==orsymbol)
            return prOR(substitute_single_boolean_variable
             (solution,variable,ATgetArgument(t,0),equations),
                     substitute_single_boolean_variable
             (solution,variable,ATgetArgument(t,1),equations));
    if (s==notsymbol)
            return prNOT(substitute_single_boolean_variable
                  (solution,variable,ATgetArgument(t,0),equations));
    if (s==itesymbol)
            return prITE(substitute_single_boolean_variable
             (solution,variable,ATgetArgument(t,0),equations),
                     substitute_single_boolean_variable
             (solution,variable,ATgetArgument(t,1),equations),
                     substitute_single_boolean_variable
             (solution,variable,ATgetArgument(t,2),equations));
    if (s==forallsymbol)
      { return FORALL(ATgetArgument(t,0),
                   ATgetArgument(t,1),
                   substitute_single_boolean_variable
             (solution,variable,ATgetArgument(t,2),equations));
      }
    if (s==existssymbol)
      { return EXISTS(ATgetArgument(t,0), 
                   ATgetArgument(t,1),
                   substitute_single_boolean_variable
             (solution,variable,ATgetArgument(t,2),equations));

      }
    if (strcmp(ATgetName(s),ATgetName(ATgetAFun(variable)))==0) /* t starts with 
                                                                     variable name */
    {  
       return substitute(
               ATconcat((ATermList)ATgetArgument(find_equation(variable,equations),1),
               ATconcat((ATermList)ATgetArgument(find_equation(variable,equations),2),
                        (ATermList)ATgetArgument(find_equation(variable,equations),3))),
                          ATgetArguments((ATermAppl)t),
                          solution); }
    
    return (ATerm)ATmakeApplList(s,
          substitute_single_boolean_variableList(solution,
                      variable,ATgetArguments((ATermAppl)t),equations));
  }

  return NULL;
}


static void Substitute_solution(
      ATerm variable,
      ATerm solution,
      ATermList temporary_variablelist,
      ATermTable equations)

{  ATerm var=NULL, t=NULL;
   ATermList pars1=NULL, pars2=NULL, localpars=NULL;
   /* ATfprintf(stdout,"SUBSTITUTE SOL: %t   %t\n",variable,solution);  */
   for(; !ATisEmpty(temporary_variablelist) ; 
           temporary_variablelist=ATgetNext(temporary_variablelist) )
   { ATerm v=ATgetFirst(temporary_variablelist);
     ATerm e=ATtableGet(equations,v);
     if (ATmatch(e,"nu(<term>,<term>,<term>,<term>,<term>)",
              &var,&localpars,&pars1,&pars2,&t))
     { ATtablePut(equations,v,
         ATmake("nu(<term>,<term>,<term>,<term>,<term>)",
           var,localpars,pars1,pars2,
             substitute_single_boolean_variable(solution,variable,t,equations)));
     }
     else if (ATmatch(e,"mu(<term>,<term>,<term>,<term>,<term>)",
              &var,&localpars,&pars1,&pars2,&t))
     { ATtablePut(equations,v,
         ATmake("mu(<term>,<term>,<term>,<term>,<term>)",
           var,localpars,pars1,pars2,
             substitute_single_boolean_variable(solution,variable,t,equations)));
     }
     else ATerror("Match failure");
   }
}

static void Solve_equations(ATermTable equations, 
            ATermList init,
            ATermList parameters)
{ 
  ATerm solution=NULL;

  for( ; !ATisEmpty(variablelist) ; variablelist=ATgetNext(variablelist))
  { if (monitor) ATfprintf(stdout,"\nVariablelist %t\n",variablelist);
    solution=Solve(ATgetFirst(variablelist),equations);
    Substitute_solution(ATgetFirst(variablelist),solution,
            ATgetNext(variablelist),equations);
  }

  Print_report(solution,init,parameters); 
}


/*************************  SCANNER  ******************/

static scansymbol next_symbol=NONE;

static ATerm read_or_tail(FILE *file);
static ATerm read_and_tail(FILE *file);
static ATerm read_not_formula(FILE *file);
static ATerm read_term(FILE *file, int action);

static ATermList read_variablelist(FILE *file)
{ char buf[ERRORLENGTH];
  ATermList result=ATempty;

  if (next_symbol!=SQUARE_BRACKET_OPEN)
    ATerror("Expect '[' in parameterlist for fixed point operator at line %d position %d.",
                                  line,position);
  do
  { 
    next_symbol=scan_formula(file);
    if (next_symbol!=STRING)
       ATerror("Expect variable at line %d position %d.",line,position);
    sprintf(buf,"%s#",inputstring);
    next_symbol=scan_formula(file);
    if (next_symbol!=COLON)
       ATerror("Expect ':' after variable at line %d position %d.",line,position);
    next_symbol=scan_formula(file);
    if (next_symbol!=STRING)
       ATerror("Expect sort after ':' at line %d position %d.",line,position);
    result=ATinsert(result,ATmake("v(<str>,<str>)",buf,inputstring));
    next_symbol=scan_formula(file);
  }
  while (next_symbol==COMMA);
    
  if (next_symbol!=SQUARE_BRACKET_CLOSE)
     ATerror("Expect ']' in input formula at line %d position %d.",line,position);
  next_symbol=scan_formula(file);

  Declare_vars(result);
  return result;
}


static ATermList read_termlist(FILE *file)
{
  ATermList result=ATempty;
  if (next_symbol!=SQUARE_BRACKET_OPEN)
    ATerror("Expect '[' in argumentlist for fixed point operator at line %d position %d.",line,position);
  next_symbol=scan_formula(file);
  result=ATinsert(result,read_term(file,0));
  while (next_symbol==COMMA)
  { next_symbol=scan_formula(file);
    result=ATinsert(result,read_term(file,0));
  }
  if (next_symbol!=SQUARE_BRACKET_CLOSE)
     ATerror("Expect ')' in input formula at line %d position %d.",line,position);
  next_symbol=scan_formula(file);
  return result;
}

static int fixedpointvarsinitcheck=0;
static ATermList fixedpointvars=NULL;

static int fixed_point_variable(ATerm t)
{ ATermList l=NULL, l1=NULL, l2=NULL, args=NULL;
  char *name=NULL;
  char *s1=NULL, *s2=NULL;
  int fail=0;
  

  if (!fixedpointvarsinitcheck) 
  { fixedpointvars=ATempty;
    fixedpointvarsinitcheck=1;
  }


  name=ATgetName(ATgetAFun(t));
  args=ATgetArguments((ATermAppl)t);
  for(l=fixedpointvars ; !ATisEmpty(l) ; l=ATgetNext(l))
  { if (strcmp(name,ATgetName(ATgetAFun(ATgetArgument(ATgetFirst(l),0))))==0)
    { /* we have a match, do the types of the arguments match? */
      l2=(ATermList)ATgetArgument(ATgetFirst(l),1);
      fail=0;
      for(l1=args ; !ATisEmpty(l1) ; l1=ATgetNext(l1))
      { if (ATisEmpty(l2)) { fail=1; break; }
        if (!ATmatch(ATgetFirst(l2),"v(<str>,<str>)",&s1,&s2))
          ATerror("Internal error %t",l2);
        if (strcmp(s2,ATgetName(ATgetAFun(Sort_of_(ATgetFirst(l1)))))>0)
          { fail=1; break; }
        l2=ATgetNext(l2);
      }
      if ((!fail) && ATisEmpty(l2)) return 1;
    }

  }
  return 0;
}


static ATerm fixedpointtail(int max,FILE *file)
{ char buf[ERRORLENGTH];


  if (!fixedpointvarsinitcheck) 
  { fixedpointvars=ATempty;
    fixedpointvarsinitcheck=1;
  }
  if (next_symbol==ROUND_BRACKET_OPEN)
  { ATermList l=NULL, l2=NULL;
    ATerm t=NULL;
    next_symbol=scan_formula(file);
    if (next_symbol!=STRING)
      ATerror("Expect string after fixed point operator and '(' at line %d position %d",
                                    line,position);
    strcpy(buf,inputstring);
    next_symbol=scan_formula(file);
    l=read_variablelist(file);
    for(l2=l ; !ATisEmpty(l2) ; l2=ATgetNext(l2))
    { strcat(strcat(buf,"#"),ATgetName(ATgetAFun(ATgetArgument(ATgetFirst(l2),1))));
    }
    fixedpointvars=ATinsert(fixedpointvars,ATmake("t(<str>,<term>))",buf,l));
    if (next_symbol!=DOT)
    ATerror("Expect '.' after fixed point operator and variabllist at line %d position %d",
                                         line,position);
    next_symbol=scan_formula(file);
    t=read_not_formula(file);
    if (next_symbol!=ROUND_BRACKET_CLOSE)
    ATerror("Expect ')' after formula in fixed point context at line %d position %d",
                                         line,position);
    next_symbol=scan_formula(file);
    l2=read_termlist(file);
    if (ATgetLength(l)!=ATgetLength(l2))
      ATerror("Parameter and argument lists do not have equal length for %s at line %d position %d.",
                             buf,line,position);
    return ATmake("<appl(<str>,<term>,<term>,<term>)>",(max?"nu":"mu"),buf,l,t,l2);
  

  }
  else
  if (next_symbol==STRING)
  { sprintf(buf,"%s#",inputstring);
    fixedpointvars=ATinsert(fixedpointvars,ATmake("t(<str>,[]))",buf));
    next_symbol=scan_formula(file);
    if (next_symbol!=DOT)
      ATerror("Expect '.' after fixed point operator at line %d position %d",line,position);
    next_symbol=scan_formula(file);
    return ATmake("<appl(<str>,[],<term>,[])>",(max?"nu":"mu"),buf,read_not_formula(file));
  }
  ATerror("Expect '(' or string after fixed point operator at line %d position %d",line,position);
  return NULL;
}

static ATerm read_not_action(FILE *file);
static ATerm read_and_action(FILE *file);

static ATerm read_and_action_tail(FILE *file)
{ 
  if (next_symbol==AND_SYMBOL)
  { 
    next_symbol=scan_formula(file);
    return read_not_action(file);
  }
  else
    return NULL;
}

static ATerm read_or_action_tail(FILE *file)
{ 
  if (next_symbol==OR_SYMBOL)
  { 
    next_symbol=scan_formula(file);
    return read_and_action(file);
  }
  else
    return NULL;
}


static ATerm read_and_action(FILE *file)
{ 
  ATerm t1=NULL, t2=NULL;

  t1=read_not_action(file);
  do
  { t2=read_and_action_tail(file);
    if (t2!=NULL)
    { t1=prAND(t1,t2);
    }
  }
  while (t2!=NULL);

  return t1;

}

static ATerm read_or_action(FILE *file)
{
 ATerm t1=NULL, t2=NULL;

  t1=read_and_action(file);
  do
  { t2=read_or_action_tail(file);
    if (t2!=NULL)
    { t1=prOR(t1,t2);
    }
  }
  while (t2!=NULL);

  return t1;
}

static ATerm read_quantified_action(FILE *file,int forall)
{
  char buf[ERRORLENGTH], buf2[ERRORLENGTH];
  AFun f=0;

  if (next_symbol!=STRING)      
    { ATerror("Expect identifier after quantifier at line %d position %d",line,position);
    }
  sprintf(buf,"%s#",inputstring);
  f = ATmakeSymbol(buf,0,ATtrue);

  next_symbol=scan_formula(file);
  if (next_symbol!=COLON)
  { ATerror("Expect colon after quantifier and identifier at line %d position %d %d"
,line,position,next_symbol);
  }
  next_symbol=scan_formula(file);    
  if (next_symbol!=STRING)
  { ATerror("Expect sort identifier after : at line %d position %d",line,position);
  }
  strcpy(buf2,inputstring);
  Declare_vars((ATermList)ATmake("[v(<str>,<str>)]",buf,buf2));
  next_symbol=scan_formula(file);
  if (next_symbol!=DOT)
  { ATerror("Expect dot after quantified variable at line %d position %d",line,position);
  }
  next_symbol=scan_formula(file);     
  if (forall)
        return ATmake("forall(<str>,<str>,<term>)",buf,buf2,read_not_action(file));
  return ATmake("exists(<str>,<str>,<term>)",buf,buf2,read_not_action(file));


}


static ATerm read_not_action(FILE *file)
{ 

  ATerm t=NULL;

  switch (next_symbol){
  case STRING :
    { 
      t=read_term(file,1);
      if ((ATmatch(t,"\"T\""))||
          (ATmatch(t,"T")))
         return prTRUE;
      if ((ATmatch(t,"\"F\""))||
          (ATmatch(t,"F")))
         return prFALSE;
      return ATmake("act(<term>)",t);
    }
  case NOT_SYMBOL :
    { next_symbol=scan_formula(file);
      t=read_not_action(file);
      return prNOT(t);
    }
  case ROUND_BRACKET_OPEN :
    { next_symbol=scan_formula(file);
      t=read_or_action(file);
      if (next_symbol!=ROUND_BRACKET_CLOSE)
      { ATerror("Expect ')' at line %d position %d",line,position);
      }
      next_symbol=scan_formula(file);
      return t;
    }
   case EXISTS_SYMBOL :
      next_symbol=scan_formula(file);
      return read_quantified_action(file,0);

   case FORALL_SYMBOL :
      next_symbol=scan_formula(file);
      return read_quantified_action(file,1);

   default : ATerror("Syntax error in formula at line %d position %d",line,position);
  }
  return NULL;
}

static ATerm read_and_formula(FILE *file)
{ ATerm t1=NULL, t2=NULL;

  t1=read_not_formula(file);
  do
  { t2=read_and_tail(file);
    if (t2!=NULL)
    { t1=prAND(t1,t2);
    }
  }
  while (t2!=NULL);
  
  return t1;

}

static ATerm read_or_formula(FILE *file)
{ ATerm t1=NULL, t2=NULL;

  t1=read_and_formula(file);
  do
  { t2=read_or_tail(file);
    if (t2!=NULL)
    { t1=prOR(t1,t2);
    }
  }
  while (t2!=NULL);
  
  return t1;

}

static ATermList read_optarguments(FILE *file);

static ATerm read_term(FILE *file, int action)
{ /* the second parameter indicates whether
     the term to be read is an action, in which
     case its head symbol should not get # marks
     to indicate typing */

  char buf[ERRORLENGTH];
  ATermList l=NULL, l1=NULL;
  AFun f=0;
  strcpy(buf,inputstring);
  next_symbol=scan_formula(file);
  l=read_optarguments(file);
  if (ATisEmpty(l))
     { if (!action) strcat(buf,"#"); 
     }
  else
     if (!action)
     { for(l1=l ; !ATisEmpty(l1) ; l1=ATgetNext(l1))
       { 
         strcat(strcat(buf,"#"),ATgetName(ATgetAFun(Sort_of_(ATgetFirst(l1)))));
       }  
     }
  f = ATmakeSymbol(buf,ATgetLength(l),ATtrue);
  return (ATerm)ATmakeApplList(f,l);
}

static ATermList read_optarguments(FILE *file)
{ 
  if (next_symbol==ROUND_BRACKET_OPEN)
  { ATermList result=ATempty;
    next_symbol=scan_formula(file);
    result=ATappend(result,read_term(file,0));
    while (next_symbol==COMMA)
    { next_symbol=scan_formula(file);
      result=ATappend(result,read_term(file,0));
    }
    if (next_symbol!=ROUND_BRACKET_CLOSE)
       ATerror("Expect ')' in input formula at line %d position %d.",line,position);
    next_symbol=scan_formula(file);
    return result;
  }
  return ATempty;

}

static ATerm read_quantified_variable(FILE *file,int forall)
{
  char buf[ERRORLENGTH], buf2[ERRORLENGTH];

  ATerm bufterm, buf2term;
  AFun f=0;

  if (next_symbol!=STRING)
    { ATerror("Expect identifier after quantifier at line %d position %d",line,position);
    }
  sprintf(buf,"%s#",inputstring);
  f = ATmakeSymbol(buf,0,ATtrue);

  next_symbol=scan_formula(file);
  if (next_symbol!=COLON)
  { ATerror("Expect colon after quantifier and identifier at line %d position %d %d",line,position,next_symbol);
  }
  next_symbol=scan_formula(file);
  if (next_symbol!=STRING)
  { ATerror("Expect sort identifier after : at line %d position %d",line,position);
  }
  strcpy(buf2,inputstring);
  bufterm=ATmake("<str>",bufterm);
  buf2term=ATmake("<str>",buf2term);

  Declare_vars((ATermList)ATmake("[v(<term>,<term>)]",bufterm,buf2term));
  next_symbol=scan_formula(file);
  if (next_symbol!=DOT)
  { ATerror("Expect dot after quantified variable at line %d position %d",line,position);
  }
  next_symbol=scan_formula(file);
  if (forall)
        return FORALL(bufterm,buf2term,read_not_formula(file));
  return EXISTS(bufterm,buf2term,read_not_formula(file));


}

static ATerm read_not_formula(FILE *file)
{ /* If the syntax 
     
         phi_and ::= N optarguments and_tail | ~phi_not and_tail | (phi_or) and_tail |
                    <actionformula>phi_not and_tail | [actionformula]phi_not and_tail |
                   !d:D.phi_not and_tail | ?d:D.phi_not and_tail | 
                   mu fixedpointtail and_tail|
                   nu fixedpointtail and_tail

     is encountered, the ATerm representing this term is 
     returned. Next_symbol is the first symbol after the term.
     Otherwise, parsing is stopped with an error message.
     All encountered types are checked on the way.

  */
  ATerm t=NULL, t1=NULL;

  switch (next_symbol){
  case STRING :
    { if (strcmp(inputstring,"mu")==0)
      { next_symbol=scan_formula(file);   
        return fixedpointtail(0,file);
      } else
      if (strcmp(inputstring,"nu")==0)
      { next_symbol=scan_formula(file);
        return fixedpointtail(1,file); 
      } else
      { t=read_term(file,0);
       if (t==prTRUE) return prTRUE;
       if (t==prFALSE) return prFALSE;
       if (fixed_point_variable(t)) return ATmake("rec(<term>)",t);
       if (Sort_of_(t)==prBOOL) return ATmake("form(<term>)",t);
       ATerror("Encountered badly typed expression: %t",t);
      }
      

    }
  case NOT_SYMBOL : 
    { next_symbol=scan_formula(file);
      t=read_not_formula(file);
      return prNOT(t); 
    }
  case ROUND_BRACKET_OPEN :
    { next_symbol=scan_formula(file);
      t=read_or_formula(file);
      if (next_symbol!=ROUND_BRACKET_CLOSE)
      { ATerror("Expect ')' at line %d position %d",line,position); 
      }
      next_symbol=scan_formula(file);
      return t;
    }
  case ANGLE_BRACKET_OPEN :
      next_symbol=scan_formula(file);
      t=read_or_action(file);
      if (next_symbol!=ANGLE_BRACKET_CLOSE)
      {  ATerror("Expect '>' at line %d position %d",line,position);
      }
      next_symbol=scan_formula(file);
      t1=read_not_formula(file);
      return ATmake("may(<term>,<term>)",t,t1);
  case SQUARE_BRACKET_OPEN :
      next_symbol=scan_formula(file);
      t=read_or_action(file);
      if (next_symbol!=SQUARE_BRACKET_CLOSE)
      {  ATerror("Expect ']' at line %d position %d",line,position);
      }
      next_symbol=scan_formula(file);
      t1=read_not_formula(file);
      return ATmake("must(<term>,<term>)",t,t1);
  case EXISTS_SYMBOL :
      next_symbol=scan_formula(file);
      return read_quantified_variable(file,0);
  case FORALL_SYMBOL :
      next_symbol=scan_formula(file);
      return read_quantified_variable(file,1);
  default : ATerror("Syntax error in formula at line %d position %d.",line,position);
  }
  return NULL;
}

static ATerm read_and_tail(FILE *file)
{ /* if syntax encountered is: & phi_and
     then phi_and is returned, and the focus is at
     the first next symbol. Otherwise NULL is returned.
  */

  if (next_symbol==AND_SYMBOL)
  { 
    next_symbol=scan_formula(file);
    return read_not_formula(file);
  }
  else
    return NULL;
}

static ATerm read_or_tail(FILE *file)
{ /* if syntax encountered is: & phi_and
     then phi_and is returned, and the focus is at
     the first next symbol. Otherwise NULL is returned.
  */

  if (next_symbol==OR_SYMBOL)
  { 
    next_symbol=scan_formula(file);
    return read_and_formula(file);
  }
  else
    return NULL;
}

static ATerm ReadFormula(char *formula_file_name)
{ 
  FILE *formula_file;
  ATerm resultaat=NULL;

  formula_file=fopen(formula_file_name,"r");
  if (formula_file==NULL)
  { ATerror("Cannot open formula file %s",formula_file_name); }

  if (next_symbol==NONE) next_symbol=scan_formula(formula_file);
  resultaat=read_or_formula(formula_file);
  if ((next_symbol!=END_OF_FILE) && (next_symbol!=SPACE))
    ATerror("Spurious symbols at end of the inputfile");
  return resultaat;
}

static void Modcheck(char *formula_file_name)
{ 
  FILE *formula_file;
  ATerm formula=NULL;
  ATermTable fixedpointequations=NULL;

  variablelist=ATempty;
  ATprotect((ATerm*)&variablelist);
  ATprotect((ATerm*)&fixedpointvars);

  set_symbols(); 
  
  /* formula=ReadFormula(formula_file_name); 
     Old code, replaced by libmuparse. */

  formula_file=fopen(formula_file_name,"r");
  if (formula_file==NULL)
  { ATerror("Cannot open formula file %s",formula_file_name); }

  formula=(ATerm)MCparseModalFormula(formula_file,1,2,1+verbose,1);
  if (formula==NULL) 
     { ATerror("Cannot read a modal formula from file \"%s\"",formula_file_name); }
  
  equationdefs=ATtableCreate(1024,80);
  fixedpointequations=Generate_equations(formula,MCRLgetListOfPars(),MCRLgetListOfSummands());
  if (verbose) Print_equations(fixedpointequations,0); 
  Declare_vars(MCRLgetListOfPars());
  Solve_equations(fixedpointequations,MCRLgetListOfInitValues(),MCRLgetListOfPars());
}

/************************************  Main  **********************************/

static void WarningHandler(const char *format, va_list args)
     {
     fprintf(stdout,"%s: ", who);
     ATvfprintf(stdout, format, args);
     fprintf(stdout,"\n");
     }

static void ErrorHandler(const char *format, va_list args)
     {
     fprintf(stdout,"%s: ", who);
     ATvfprintf(stdout, format, args);
     fprintf(stdout,"\n");
     if (verbose) abort();
     exit(-1);
     }

/* static ATerm *getStackBottom(void)
    {
       ATerm bottomOfStack = NULL;
       return &bottomOfStack;
    } */

static void parse_argument_line(int argc, char *argv[])
{ int i=0,formula_file_name_found=0;
  for (i=1;i<argc;i++)
  if (strlen(argv[i]))
    { if (!strcmp(argv[i],"-help"))
            {
            help();
            exit(0);
            }
       if (!strcmp(argv[i],"-version"))
            {
            version();
            exit(0);
            }
       if (!strcmp(argv[i],"-syntax"))
            {
            externalsyntax();
            exit(0);
            }
       if (!strcmp(argv[i],"-internal"))
            {
            internalsyntax();
            exit(0);
            }
       if (!strcmp(argv[i],"-verbose"))
            { verbose=1;
              continue;
            }
       if (!strcmp(argv[i],"-monitor"))
            { monitor=1;
              continue;
            }
       if (!strcmp(argv[i],"-show-size"))
            { showsize=1;
              continue;
            }
       if (!strcmp(argv[i],"-counter"))
            { counterexample=1;
              continue;
            }
       if (!strcmp(argv[i],"-show-bdd"))
            { show_bdd=1;
              continue;
            }
       if (!strcmp(argv[i],"-show-dot"))
            { show_dot=1;
              continue;
            }
       if (!strcmp(argv[i],"-inequalities"))
            { inequalities=1;
              continue;
            }
       if (!strcmp(argv[i],"-unsound"))
            { sound=0;
              continue;
            }
       if ((argv[i][0]!='-') && (i<argc-2))
            { ATerror("Unknown flag %s",argv[i]);
            }
       if (i==argc-2)
            { strncpy(formula_file_name,argv[i],ERRORLENGTH);
              formula_file_name_found=1;
            }
    }
    if (formula_file_name_found==0)
      ATerror("Expect formula file name and tbf file name");
    if (verbose==1) 
    {  monitor=1;
       counterexample=1;
    }
}


int main(int argc, char *argv[])
{ int i=0, j=0;

  /* char **newargv = (char**) calloc(argc + 1, sizeof(char*));
     if (!newargv) ATerror("Cannot allocate array argv");

     newargv[j++] = argv[0];   */

  ATinit(argc, argv, (ATerm*) &argc);
  ATsetWarningHandler(WarningHandler);
  ATsetErrorHandler(ErrorHandler);
   
  parse_argument_line(argc,argv);

  MCRLsetArguments(&argc,&argv);
  if (!MCRLinitialize()) ATerror("Error with MCRLinitialize");

  ProverSetArguments(&argc,&argv);
  ProverInitialize();

  MCRLdeclareVars(MCRLgetListOfPars());     

  Modcheck(formula_file_name); 
  exit(0);
 }
