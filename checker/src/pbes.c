/* $Id: pbes.c,v 1.4 2005/04/20 14:26:43 vdpol Exp $ */

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


#define P(msg)  fprintf(stdout,"%s\n",msg)

static int verbose=0;

extern ATerm prTRUE;
extern ATerm prFALSE;


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


static AFun truesymbol,falsesymbol,andsymbol,orsymbol,
     notsymbol,itesymbol,forallsymbol,existssymbol,variablesymbol;

static ATerm PBESand(ATerm t1, ATerm t2)
{ return ATmake("and(<term>,<term>)",t1,t2); }

static ATerm PBESor(ATerm t1, ATerm t2)
{ return ATmake("or(<term>,<term>)",t1,t2); }

static ATerm PBESimp(ATerm t1, ATerm t2)
{ return ATmake("or(<term>,<term>)",t1,t2); }

static ATerm PBESeq(ATerm t1, ATerm t2)
{ return ATmake("or(<term>,<term>)",t1,t2); }

static ATerm PBESnot(ATerm t)
{ return ATmake("not(<term>)",t); }

static ATerm PBEStrue(void)
{ return ATmake("T"); }

static ATerm PBESfalse(void)
{ return ATmake("F"); }

static ATerm PBESform(ATerm t)
{ return ATmake("form(<term>)",t); }

static ATerm VARIABLE(ATerm var, ATerm sort)
{ return (ATerm)ATmakeAppl2(variablesymbol,var,sort); }

static ATerm FORALL(ATerm var, ATerm sort, ATerm t)
{ return (ATerm)ATmakeAppl2(forallsymbol,VARIABLE(var,sort),t); }

static ATerm EXISTS(ATerm var, ATerm sort, ATerm t)
{ return (ATerm)ATmakeAppl2(existssymbol,VARIABLE(var,sort),t); }

void RWflush(void);

char *who = "pbes";

static char formula_file_name[MCRLsize];
static char outputFileName[MCRLsize];
static ATermTable equationdefs=NULL; 

static ATermList variablelist=NULL;

static void pbessyntaxmsg(void)
{
  P("A Parameterized Boolean Equation System (PBES) is stored as an ");
  P("ATerm in compressed toolbusfile (tbf) format with the following");
  P("term structure. The sort of each stored equation systems is Pbes.");
  P(" ");
  P("  PBES : DataTypes # FixedPointEqn* # String # Term* -> Pbes");
  P("  d : Signature # Equation* -> DataTypes");
  P("  e : Variable* # Term # Term -> Equation");
  P("  v : String # String -> Variable");
  P("  FPE : FixedPointSymbol # String # ");
  P("               Variable* # BooleanTerm -> FixedPointEqn");
  P("  mu : -> FixedPointSymbol");
  P("  nu : -> FixedPointSymbol");
  P("  T : -> BooleanTerm");
  P("  F : -> BooleanTerm");
  P("  not : BooleanTerm -> BooleanTerm");
  P("  and : BooleanTerm # BooleanTerm -> BooleanTerm");
  P("  or : BooleanTerm # BooleanTerm -> BooleanTerm");
  P("  imp : BooleanTerm # BooleanTerm -> BooleanTerm");
  P("  eq : BooleanTerm # BooleanTerm -> BooleanTerm");
  P("  forall : Variable # BooleanTerm -> BooleanTerm");
  P("  exists : Variable # BooleanTerm -> BooleanTerm");
  P("  form : Term -> BooleanTerm");
  P("  rec : String # IndexedTerm* -> BooleanTerm");
  P("  IT : Nat # Term -> IndexedTerm");
  P("  DC : Nat -> IndexedTerm");
  P("  S : String* # Function* # Function* -> Signature");
  P("  F : String # String* # String -> Function");
  P(" ");
  P("The sort Term consists of arbitrary ATerm terms where all function");
  P("symbols must be quoted. The sort String consists of quoted constants,");
  P("i.e. function symbols of arity 0. The sort Nat is the built in");
  P("sort of natural numbers in the ATerm library. The list");
  P("of elements of sort D is denoted by D*. The sort IndexedTerm");
  P("is introduced to store the parameters of a recursive invocation");
  P("in rec in an indexed way. E.g. rec(\"X\",[IT(2,t1),IT(5,t2),DC(7)]) says");
  P("that the parameters of X are t1 at position 2, t2 at position 5, and");
  P("don't care at position 7. All other parameters for X are unchanged.");
  P("The list of indexed terms is strictly increasing.");

}

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

static void helpmsg(void)
    {
    P("Usage: pbes  [options] formula-file lpo-file ");
    P("");
    P("The following options can be used");
    P("-help:      yields this message");
    P("-version:   get the version number of this release");
    P("-verbose:   causes some internal information to be printed");
    P("            while translating a formula and a linear process");
    P("-syntax:    provides the syntax for the input formulas");
    P("-pbessyntax:provides the syntax for the generated pbes");
    }

static void externalsyntax(void)
    {
    externalsyntaxmsg();
    }

static void pbessyntax(void)
    {
    pbessyntaxmsg();
    }

static void help(void)
    {
    helpmsg();
    }

static void version(void)
    {
    char buf[100];
    sprintf(buf,"%s: version %s",who, VERSION);
    P(buf);
    }
#undef P

/************************************ General functions    **********************************/


/* static void Print_term(ATerm t); */

static ATerm Simplify_(ATerm t)
{ ATerm u=NULL;

  if (verbose) { fprintf(stdout,"S"); fflush(stdout); }
  u=Simplify(t);
  RWflush();
  if (verbose) { fprintf(stdout,"-"); fflush(stdout); }
  return u;
}

static ATerm SimplifyPBESSpecificFunctions(ATerm t)
{ ATerm t1,t2,name,sort;

  if (ATmatch(t,"T") || ATmatch(t,"\"T#\""))
  { return ATmake("T"); } 

  if (ATmatch(t,"F") || ATmatch(t,"\"F#\""))
  { return ATmake("F"); } 
  
  if (ATmatch(t,"not(<term>)",&t1))
  { t1=SimplifyPBESSpecificFunctions(t1);
    if (ATmatch(t1,"T")) return ATmake("F");
    if (ATmatch(t1,"F")) return ATmake("T");
    if (ATmatch(t1,"not(<term>)",&t2)) return t2;
    return ATmake("not(<term>)",t1);
  }

  if (ATmatch(t,"and(<term>,<term>)",&t1,&t2))
  { t1=SimplifyPBESSpecificFunctions(t1);
    t2=SimplifyPBESSpecificFunctions(t2);
    if (ATmatch(t1,"T")) return t2;
    if (ATmatch(t1,"F")) return t1;
    if (ATmatch(t2,"T")) return t1;
    if (ATmatch(t2,"F")) return t2;
    if (t1==t2) return t1;
    return ATmake("and(<term>,<term>)",t1,t2);
  }

  if (ATmatch(t,"or(<term>,<term>)",&t1,&t2))
  { t1=SimplifyPBESSpecificFunctions(t1);
    t2=SimplifyPBESSpecificFunctions(t2);
    if (ATmatch(t1,"T")) return t1;
    if (ATmatch(t1,"F")) return t2;
    if (ATmatch(t2,"T")) return t2;
    if (ATmatch(t2,"F")) return t1;
    if (t1==t2) return t1;
    return ATmake("or(<term>,<term>)",t1,t2);
  }

  if (ATmatch(t,"imp(<term>,<term>)",&t1,&t2))
  { t1=SimplifyPBESSpecificFunctions(t1);
    t2=SimplifyPBESSpecificFunctions(t2);
    if (ATmatch(t1,"T")) return t2;
    if (ATmatch(t1,"F")) return ATmake("T");
    if (ATmatch(t2,"T")) return t2;
    if (ATmatch(t2,"F")) return ATmake("not(<term>)",t1);
    if (t1==t2) return ATmake("T");
    return ATmake("imp(<term>,<term>)",t1,t2);
  }

  if (ATmatch(t,"eq(<term>,<term>)",&t1,&t2))
  { t1=SimplifyPBESSpecificFunctions(t1);
    t2=SimplifyPBESSpecificFunctions(t2);
    if (ATmatch(t1,"T")) return t2;
    if (ATmatch(t1,"F")) 
          return SimplifyPBESSpecificFunctions(ATmake("not(<term>)",t2));
    if (ATmatch(t2,"T")) return t1;
    if (ATmatch(t2,"F")) 
          return SimplifyPBESSpecificFunctions(ATmake("not(<term>)",t1));
    if (t1==t2) return ATmake("T");
    return ATmake("eq(<term>,<term>)",t1,t2);
  }

  if (ATmatch(t,"forall(v(<term>,<term>),<term>)",&name,&sort,&t1))
  { t1=SimplifyPBESSpecificFunctions(t1);
    return ATmake("forall(v(<term>,<term>),<term>)",name,sort,t1);
  }
  
  if (ATmatch(t,"exists(v(<term>,<term>),<term>)",&name,&sort,&t1))
  { t1=SimplifyPBESSpecificFunctions(t1);
    return ATmake("exists(v(<term>,<term>),<term>)",name,sort,t1);
  }
  
  if(ATmatch(t,"form(<term>)",&t1))
  { if (t1==prTRUE) return ATmake("T");
    if (t1==prFALSE) return ATmake("F");
    return t;
  }

  if(ATmatch(t,"rec(<term>,<term>)",&name,&t1))
  { 
    return t;
  }

  ATerror("Unexpected match %t",t);

  return NULL;
  
}

static ATerm Sort_of_(ATerm t)
{ ATerm u=NULL;

  /* if (verbose) {ATfprintf(stdout,"Sort_of IN: "); Print_term(t); ATfprintf(stdout,"\n");} */
  u=Sort_of(t);
  /* ATfprintf(stdout,"UIT:"); Print_term(u); ATfprintf(stdout,"\n"); */
  return u;
}

static int stringcounter=0;
static char stringbuffer[MCRLsize];

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

/************************************ Substitute ********************************/

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



/************************** Routines to generate a PBEs  ************************/

static ATermList makeIndexedParameters(ATermList parameters,
                                       ATermList arguments, int index)
{
  if (parameters==ATempty)
  { if (arguments==ATempty)
    { return ATempty; }
    else ATerror("parameters and arguments must have the same length (1)");
  }

  if (arguments==ATempty)
  { ATerror("parameters and arguments must have the same length (2)"); }
  
  /* check whether first parameter and arguments match. In that case
     they do not need to be written */ 

  if (ATgetArgument(ATgetFirst(parameters),0)==ATgetFirst(arguments))
  { return makeIndexedParameters(ATgetNext(parameters),
                 ATgetNext(arguments),index+1); }
  else return ATinsert(makeIndexedParameters(ATgetNext(parameters),
                 ATgetNext(arguments),index+1),
       ATmake("IT(<int>,<term>)",index,ATgetFirst(arguments))); 

  return NULL;
}


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
  { return(PBEStrue()); }
  if ((ATmatch(action,"\"F#\""))||
      (ATmatch(action,"F")))
  { return(PBESfalse()); }
  if ((ATmatch(action,"\"and#Bool#Bool\"(<term>,<term>)",&t1,&t2)) ||
            (ATmatch(action,"and(<term>,<term>)",&t,&t1)))
  { return PBESand(actionmatch(t1,name,arguments),actionmatch(t1,name,arguments)); }
  if ((ATmatch(action,"\"or#Bool#Bool\"(<term>,<term>)",&t1,&t2))  ||
            (ATmatch(action,"or(<term>,<term>)",&t,&t1)))
  { return PBESor(actionmatch(t1,name,arguments),actionmatch(t1,name,arguments)); }
  if ((ATmatch(action,"\"not#Bool\"(<term>)",&t1)) ||
        (ATmatch(action,"not(<term>)",&t1)))
     { return PBESnot(actionmatch(t1,name,arguments)); } 
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
          { result=PBESand(result,(ATerm)ATmakeAppl2(ATmakeAFun(stringbuffer,2,1),
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

  result=PBESand(PBESform(condition),PBESand(
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

  
  result=PBESor(PBESnot(PBESand(PBESform(condition),
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
	     ATerm summand,ATermList equations, 
             ATermTable parametertable,
             ATermTable localparametertable)
{ ATerm t=NULL;
  ATermList parlist=NULL, arglist=NULL;
  ATerm name=NULL;

  if ((ATmatch(formula,"\"T#\""))||
      (ATmatch(formula,"T")))
      { return PBEStrue(); }

  if ((ATmatch(formula,"\"F#\""))||
      (ATmatch(formula,"F")))
      { return PBESfalse(); }

  if (ATmatch(formula,"form(<term>)",&t))
      { ATerm g=ATgetArgument(summand,3);
       if (ATmatch(g,"i(<term>)",&g))
       return PBESform(substitute(parameters,(ATermList)g,t)); 
        else ATerror("Cannot deal with terminating summands in an LPO");
      }

  if (ATmatch(formula,"rec(<term>)",&t))  
  {  ATerm g=ATgetArgument(summand,3);
     ATermList l=NULL;
     ATermList local_parameters_for_t=NULL;
     ATermList parameters_for_t=NULL;
     
     if (!ATmatch(g,"i(<term>)",&g))
        ATerror("Cannot deal with terminating summands in LPO");
     /* We need the local parameters, at the point of declaration
      *        when the function in t was declared */
     name=(ATerm)ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(t)),0,ATtrue));
     parameters_for_t=(ATermList)ATtableGet(parametertable,name);
     if (parameters_for_t==NULL)
          ATerror("XX Erroneous process name %t\n",name);
     local_parameters_for_t=(ATermList)ATtableGet(localparametertable,name);
     l=ATconcat(pars2args(local_parameters_for_t),
            ATconcat(ATgetArguments((ATermAppl)t),(ATermList)g));
     return (ATerm)ATmake("rec(<term>,<term>)",name,
            makeIndexedParameters(parameters_for_t,l,0));
  }

  /* else generate a new equation */

  if (ATmatch(formula,"nu(<term>,<term>,<term>,<term>)",
       &name,&parlist,&t,&arglist))
  { ATerm lhs=NULL;
    ATermList g=NULL;
    ATermList l=NULL;

    lhs=ATtableGet(equationdefs,formula);
    g=(ATermList)ATgetArgument(summand,3);
    if (!ATmatch((ATerm)g,"i(<term>)",&g))
      { ATerror("Cannot deal with terminating summands in an LPO"); }

    if (lhs==NULL)

    { 
      variablelist=ATinsert(variablelist,name);

      *stack=ATinsert(*stack,ATmake("nu(<term>,<term>,<term>,<term>,<term>)",
                  name,local_parameters,parlist,parameters,t)); 
       ATtablePut(equationdefs,formula,name);
       ATtablePut(parametertable,name,
               (ATerm)ATconcat(local_parameters,ATconcat(parlist,parameters)));
       ATtablePut(localparametertable,name,(ATerm)local_parameters);
       l=ATconcat(pars2args(local_parameters),ATconcat(arglist,g)); 
       return ATmake("rec(<term>,<term>)",name,
          makeIndexedParameters(
              ATconcat(local_parameters,ATconcat(parlist,parameters)),l,0));
    }
    l=ATconcat(pars2args(local_parameters),ATconcat(arglist,g));
    return (ATerm)ATmake("rec(<term>,<term>)",lhs,
          makeIndexedParameters(
              ATconcat(local_parameters,ATconcat(parlist,parameters)),l,0));
  }

  if (ATmatch(formula,"mu(<term>,<term>,<term>,<term>)",
       &name,&parlist,&t,&arglist))
  { ATerm lhs=ATtableGet(equationdefs,formula);
    ATermList g=(ATermList)ATgetArgument(summand,3);
    ATermList l=NULL;
    if (!ATmatch((ATerm)g,"i(<term>)",&g))
      { ATerror("Cannot deal with terminating summands in an LPO"); }

    if (lhs==NULL)
    {  variablelist=ATinsert(variablelist,name);
       *stack=ATinsert(*stack,ATmake("mu(<term>,<term>,<term>,<term>,<term>)",
                  name,local_parameters,parlist,parameters,t)); 
       ATtablePut(equationdefs,formula,name);
       ATtablePut(parametertable,name,
               (ATerm)ATconcat(local_parameters,ATconcat(parlist,parameters)));
       ATtablePut(localparametertable,name,(ATerm)local_parameters);
       l=ATconcat(pars2args(local_parameters),ATconcat(arglist,g));
       return ATmake("rec(<term>,<term>)",name,
          makeIndexedParameters(
              ATconcat(local_parameters,ATconcat(parlist,parameters)),l,0));
    }
    l=ATconcat(pars2args(local_parameters),ATconcat(arglist,g));
    return (ATerm)ATmake("rec(<term>,<term>)",lhs,
          makeIndexedParameters(
              ATconcat(local_parameters,ATconcat(parlist,parameters)),l,0));
  }

  { 
    ATerm g=ATgetArgument(summand,3);
  
    ATerm lhs=ATtableGet(equationdefs,formula);
    if (lhs==NULL)
    {  name=ATmake("<str>",newname());
       ATtablePut(equationdefs,formula,name);
       variablelist=ATinsert(variablelist,name);

       *stack=ATinsert(*stack,ATmake("nu(<str>,<term>,[],<term>,<term>)",
              name,local_parameters,parameters,formula)); 
    }
    else
     { name=lhs;
     }

    if (ATmatch(g,"i(<term>)",&g))
     { ATermList l=NULL;
       l=ATconcat(pars2args(local_parameters),(ATermList)g);
       return ATmake("rec(<term>,<term>)",
            name,
            makeIndexedParameters(ATconcat(local_parameters,parameters),l,0));
     }
    else ATerror("Cannot deal with terminating summands in LPO");
    
    assert(0);              
    return NULL;
  }


  ATerror("Not all cases dealt with %t",formula);
  return NULL;
}


static ATerm TranslateFormulaAndLPO(
         ATermList *stack,
         ATerm formula,
         ATermList parameters,
         ATermList local_parameters,
         ATermList summands,
         ATermList equations,
         ATermTable parametertable,
         ATermTable localparametertable)
{ ATerm t=NULL, t1=NULL;
  ATerm action=NULL;
  ATermList summand_walker=NULL;
  ATermList pars=NULL, args=NULL;
  ATerm nameterm=NULL; 
  ATerm name=NULL, sort=NULL;
  
  if ((ATmatch(formula,"\"T#\""))||
      (ATmatch(formula,"T")))
  { return PBEStrue(); }

  if ((ATmatch(formula,"\"F#\""))||
      (ATmatch(formula,"F")))
  { return PBESfalse(); }

  if (ATmatch(formula,"form(<term>)",&t))
  { return formula; }

  if ((ATmatch(formula,"\"and#Bool#Bool\"(<term>,<term>)",&t,&t1)) ||
      (ATmatch(formula,"and(<term>,<term>)",&t,&t1)))
  { return PBESand(TranslateFormulaAndLPO(stack,t,parameters,local_parameters,summands,equations,parametertable,localparametertable),
         TranslateFormulaAndLPO(stack,t1,parameters,local_parameters,summands,equations,parametertable,localparametertable));
  }

  if ((ATmatch(formula,"\"or#Bool#Bool\"(<term>,<term>)",&t,&t1)) ||
      (ATmatch(formula,"or(<term>,<term>)",&t,&t1)))
  { return PBESor(TranslateFormulaAndLPO(stack,t,parameters,local_parameters,summands,equations,parametertable,localparametertable),
         TranslateFormulaAndLPO(stack,t1,parameters,local_parameters,summands,equations,parametertable,localparametertable));
  }

  if ((ATmatch(formula,"\"not#Bool\"(<term>)",&t)) ||
      (ATmatch(formula,"not(<term>)",&t)))
  { return PBESnot(TranslateFormulaAndLPO(stack,t,parameters,local_parameters,summands,equations,parametertable,localparametertable));
  }

  if (ATmatch(formula,"eq(<term>,<term>)",&t,&t1))
      { return PBESeq(
          TranslateFormulaAndLPO(stack,t,parameters,local_parameters,summands,equations,parametertable,localparametertable),
	  TranslateFormulaAndLPO(stack,t1,parameters,local_parameters,summands,equations,parametertable,localparametertable));
      }

  if (ATmatch(formula,"imp(<term>,<term>)",&t,&t1))
  { return PBESimp(
        TranslateFormulaAndLPO(stack,t,parameters,local_parameters,summands,equations,parametertable,localparametertable),
        TranslateFormulaAndLPO(stack,t1,parameters,local_parameters,summands,equations,parametertable,localparametertable));
  }

  if (ATmatch(formula,"may(<term>,<term>)",&action,&t))
  { ATerm result=NULL;
    
    for(summand_walker=summands; (!ATisEmpty(summand_walker)); 
                            summand_walker=ATgetNext(summand_walker))
    { 
      ATerm summand=summand=ATgetFirst(summand_walker);
      Declare_vars((ATermList)ATgetArgument(summand,0));
      if (can_match(action,summand))
      { if (result==NULL)
        { result=generate_may_match_formula(action,summand,
                make_restformula(stack,t,parameters,
                       local_parameters,summand,equations,parametertable,localparametertable)); }
        else result=PBESor(result,
           generate_may_match_formula(action,summand,
              make_restformula(stack,t,parameters,
                             local_parameters,summand,equations,parametertable,localparametertable)));
      }

    }
    if (result==NULL)
    { return PBESfalse();
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
                  local_parameters,summand,equations,parametertable,localparametertable)); }
          else result=PBESand(result,generate_must_match_formula(action,summand,
              make_restformula(stack,t,parameters,
                    local_parameters,summand,equations,parametertable,localparametertable)));
      }

    }
    if (result==NULL)
    { return PBEStrue();
    }
    else return result;
  }

  if (ATmatch(formula,"forall(<term>,<term>,<term>)",&name,&sort,&t))
  { 
    Declare_vars(ATinsert(ATempty,ATmake("v(<term>,<term>)",name,sort)));
    return FORALL(name,sort,TranslateFormulaAndLPO(stack,t,parameters,
             ATinsert(local_parameters,
                     ATmake("v(<term>,<term>)",name,sort)),summands,equations,parametertable,localparametertable));
  }

  if (ATmatch(formula,"exists(<term>,<term>,<term>)",&name,&sort,&t))
  { 
    Declare_vars(ATinsert(ATempty,ATmake("v(<term>,<term>)",name,sort)));
    return EXISTS(name,sort,
        TranslateFormulaAndLPO(stack,t,parameters, ATinsert(local_parameters,
                     ATmake("v(<term>,<term>)",name,sort)),summands,equations,parametertable,localparametertable));
  }

  if (ATmatch(formula,"mu(<term>,<term>,<term>,<term>)",&nameterm,&pars,&t,&args))
  { 
    variablelist=ATinsert(variablelist,
         (ATerm)ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(nameterm)),0,1)));
    ATtablePut(parametertable,nameterm,
         (ATerm)ATconcat(local_parameters,ATconcat(pars,parameters)));
    ATtablePut(localparametertable,nameterm,(ATerm)local_parameters);
    *stack=ATinsert(*stack,ATmake("mu(<term>,<term>,<term>,<term>,<term>)",
                     nameterm,
                     local_parameters,pars,parameters,t));
    args=ATconcat(pars2args(local_parameters),ATconcat(args,pars2args(parameters)));
    return (ATerm)ATmake("rec(<term>,<term>)",nameterm,
           makeIndexedParameters(
                 ATconcat(local_parameters,ATconcat(pars,parameters)),args,0));
  }

  if (ATmatch(formula,"nu(<term>,<term>,<term>,<term>)",&nameterm,&pars,&t,&args))
   
  { 
    variablelist=ATinsert(variablelist,
         (ATerm)ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(nameterm)),0,1)));
    ATtablePut(parametertable,nameterm,
         (ATerm)ATconcat(local_parameters,ATconcat(pars,parameters)));
    ATtablePut(localparametertable,nameterm,(ATerm)local_parameters);
    *stack=ATinsert(*stack,ATmake("nu(<term>,<term>,<term>,<term>,<term>)",
               nameterm,
               local_parameters,pars,parameters,t));
    args=ATconcat(pars2args(local_parameters),ATconcat(args,pars2args(parameters)));
    return (ATerm)ATmake("rec(<term>,<term>)",nameterm,
           makeIndexedParameters(
                 ATconcat(local_parameters,ATconcat(pars,parameters)),args,0));
  }

  if (ATmatch(formula,"rec(<term>)",&t))
  { ATermList l=NULL;
    ATermList local_parameters_for_t=NULL;
    ATerm name=NULL;
    ATermList parameters_for_t=NULL;
    /* We need the local parameters, at the point of declaration 
       when the function in t was declared */
    name=(ATerm)ATmakeAppl0(ATmakeAFun(ATgetName(ATgetAFun(t)),0,ATtrue));
    parameters_for_t=(ATermList)ATtableGet(parametertable,name);
    if (parameters_for_t==NULL) 
       ATerror("Erroneous process name %t\n",name);
    local_parameters_for_t=(ATermList)ATtableGet(localparametertable,name);
    l=ATconcat(pars2args(local_parameters_for_t),
       ATconcat(ATgetArguments((ATermAppl)t),
                 pars2args(parameters))); 


    return ATmake("rec(<term>,<term>)",
               name,
               makeIndexedParameters(parameters_for_t,l,0)); 
  }          

  ATerror("Error translating formula %t",formula);
  return NULL;
}

static ATermList Process_stack(
                ATermList *stack,
                ATermList summands,
                ATermList equations,
                ATermTable parametertable,
                ATermTable localparametertable)
{
  ATerm frame=NULL;
  ATerm formula=NULL;
  ATerm result=NULL, fixedpointsymbol=NULL;
  ATermList local_parameters=NULL, non_local_parameters=NULL,
            parameters=NULL;
  char *name=NULL;

  if (ATisEmpty(*stack)) return equations;

  frame=ATgetFirst(*stack);
  *stack=ATgetNext(*stack);


  
  if (ATmatch(frame,"mu(<str>,<term>,<term>,<term>,<term>)",
                 &name,&local_parameters,&non_local_parameters,
                 &parameters,&formula))
  { fixedpointsymbol=ATmake("mu");
  }  
  else if (ATmatch(frame,"nu(<str>,<term>,<term>,<term>,<term>)",
                     &name,&local_parameters,&non_local_parameters,
                     &parameters,&formula))
  { fixedpointsymbol=ATmake("nu");
  }
  else ATerror("Wrong stackframe %t",frame);

  /* Declare_vars(parameters);
  Declare_vars(local_parameters);
  Declare_vars(non_local_parameters); */

  name=AddFun(name,ATconcat(local_parameters,
               ATconcat(non_local_parameters,parameters)),prBOOL);
                 
  
  result=Simplify_(TranslateFormulaAndLPO(stack,formula,parameters,
                              ATconcat(local_parameters,non_local_parameters),
			            summands,equations,parametertable,localparametertable));
  result=SimplifyPBESSpecificFunctions(result);
  
  return ATinsert(
             Process_stack(stack,summands,equations,parametertable,localparametertable),
             ATmake("FPE(<term>,<str>,<term>,<term>)",
               fixedpointsymbol,
               name,
               ATconcat(local_parameters,ATconcat(non_local_parameters,parameters)),
               result));
}

static ATermList Generate_equations(
                ATerm formula, ATermList parameters,ATermList summands)
{ 
  ATermList stack=ATempty;
  ATermList equations=ATempty;
  ATermTable parametertable=NULL;
  ATermTable localparametertable=NULL;

  parametertable=ATtableCreate(64,80);
  localparametertable=ATtableCreate(64,80);

  variablelist=ATinsert(variablelist,ATmake("<str>","START#"));
  stack=ATinsert(stack,ATmake("nu(\"START#\",<term>,<term>,<term>,<term>)",
                         ATempty,ATempty,parameters,formula));
  
  return Process_stack(&stack,summands,equations,parametertable,localparametertable);

}


/* static void printstring_without_hash(char *var)
{ / * also quotes are filtered out * /
  int i=0;
  for(i=0 ; (var[i]!='#') && (var[i]!='\0') ; i++)
  { if (var[i]!='"') fprintf(stdout,"%c",var[i]); }
}*/

/* static void Print_term(ATerm t)
{ int i=0, arity=0;
  
  printstring_without_hash(ATgetName(ATgetAFun(t)));
  arity=ATgetArity(ATgetAFun(t));
  for(i=0 ; i<arity ; i++)
  { 
    fprintf(stdout,"%c",(i==0)?'(':',');
    Print_term(ATgetArgument(t,i));
  }
  if (arity>0) fprintf(stdout,")");
} */


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
  forallsymbol=ATmakeAFun("forall",2,0);
  ATprotectAFun(existssymbol);
  existssymbol=ATmakeAFun("exists",2,0);
  ATprotectAFun(variablesymbol);
  variablesymbol=ATmakeAFun("v",2,0);
}


/*************************  MakePBES  ******************/

static ATerm MakePBES(char *formula_file_name)
{ 
  FILE *formula_file;
  ATerm formula=NULL;
  ATerm pbes=NULL;

  variablelist=ATempty;
  ATprotect((ATerm*)&variablelist);
  /* ATprotect((ATerm*)&fixedpointvars); */

  set_symbols(); 
  
  formula_file=fopen(formula_file_name,"r");
  if (formula_file==NULL)
  { ATerror("Cannot open formula file %s",formula_file_name); }

  formula=(ATerm)MCparseModalFormula(formula_file,1,2,1+verbose,1);
  if (formula==NULL) 
     { ATerror("Cannot read a modal formula from file \"%s\"",formula_file_name); }
  
  pbes=ATmake("PBES(<term>,<term>,<str>,<term>)",
         MCRLgetAdt(),
         (ATerm)ATreverse(Generate_equations(formula,MCRLgetListOfPars(),MCRLgetListOfSummands())),
         "START#",
         MCRLgetListOfInitValues());
  
  return pbes;
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
       if (!strcmp(argv[i],"-pbessyntax"))
            {
            pbessyntax();
            exit(0);
            }
       if (!strcmp(argv[i],"-verbose"))
            { verbose=1;
              continue;
            }
       if ((argv[i][0]!='-') && (i<argc-2))
            { ATerror("Unknown flag %s",argv[i]);
            }
       if (i==argc-2)
            { strncpy(formula_file_name,argv[i],MCRLsize);
              formula_file_name_found=1;
            }
    }
    if (formula_file_name_found==0)
      ATerror("Expect formula file name and tbf file name");
}


int main(int argc, char *argv[])
{ 
  ATerm pbes;
  FILE *outputfile;

  equationdefs = ATtableCreate(60,80);

  /* char **newargv = (char**) calloc(argc + 1, sizeof(char*));
     if (!newargv) ATerror("Cannot allocate array argv");

     newargv[j++] = argv[0];   */

  ATinit(argc, argv, (ATerm*) &argc);
  ATsetWarningHandler(WarningHandler);
  ATsetErrorHandler(ErrorHandler);
   
  parse_argument_line(argc,argv);

  /* the 2 lines below cause the base name of the
   * lpo file to be put in outputFileName */

  outputFileName[0]='\0';
  MCRLsetOutputFile(outputFileName);
  MCRLsetArguments(&argc,&argv);
  if (!MCRLinitialize()) ATerror("Error with MCRLinitialize");

  ProverSetArguments(&argc,&argv);
  ProverInitialize();

  MCRLdeclareVars(MCRLgetListOfPars());     

  pbes=MakePBES(formula_file_name);
  /* The two lines below are a trick to obtain the name of
   * the inputfile containing the lpo in 'outputFileName'. */

  if (strlen(outputFileName)+4<MCRLsize)
  { strcat(outputFileName,".pbes"); }
  else
  { ATerror("Input file name too long"); }
  
  outputfile=fopen(outputFileName,"w");
  ATwriteToBinaryFile(pbes,outputfile);

  exit(0);
 }
