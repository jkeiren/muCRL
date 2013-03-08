/* $Id: mcrl.h,v 1.7 2007/11/07 09:48:26 bertl Exp $ */
#ifndef MCRL_H
#define MCRL_H

#include <stdlib.h>
#include "aterm2.h"
#define MCRLsize 256
#ifdef __cplusplus
extern "C"
{
#endif/* __cplusplus */
extern ATbool MCRLoldTbf;

/* -----------------------------------Declarations ------------------------------ */

typedef ATerm (*MCRLREWRITE) (ATerm t);

typedef enum { MCRLunknown, MCRLsort, MCRLconstructorsort, 
               MCRLenumeratedsort, MCRLvariable, MCRLconstructor, 
               MCRLfunction, MCRLcasefunction, MCRLeqfunction } MCRLsymtype;
               
typedef enum {MCRLundefined, MCRLtext, MCRLbinary, MCRLsharedText, MCRLserializedBinary} 
        MCRL_OUTPUTFORMAT;

extern MCRL_OUTPUTFORMAT MCRLformat;
/* Argument type needed for MCRLwrite, which determines the format
of the output file */


/* Struct in which the fields are term constants,
   definition of these constants are in mcrlsig.h  */
   
extern ATerm MCRLterm_bool, MCRLterm_state, MCRLterm_false,
MCRLterm_true, MCRLterm_delta, MCRLterm_tau, MCRLterm_tau_c,
MCRLterm_terminated, MCRLterm_empty_tree, MCRLterm_i;

extern AFun MCRLsym_i, MCRLsym_v, MCRLsym_pair, MCRLsym_and, MCRLsym_or,
MCRLsym_not, MCRLsym_ite, MCRLsym_one, MCRLsym_x2p0, MCRLsym_x2p1;


extern ATerm MCRLtag;
   
/* ----------------------------------- End of declarations ------------------------------ */

/* ----------------------------------- Initialisation  of libraries --------------------- */
   
ATbool MCRLinit(int *argc, char ***argv);
/* Initializes only the MCRL library.
   Doesn't test presence of illegal flags 
*/
   
ATbool MCRLinitOnly(int argc, char **argv);
/* Initializes only the MCRL library.
   Tests presence of illegal flags */
   
ATbool MCRLinitRW(int argc, char **argv);
/* Initializes MCRL library and Rewriter library 
   Tests presence of illegal flags 
*/

ATbool MCRLinitSU(int argc, char **argv);
/* Initializes MCRL library and Substitution library 
   Tests presence of illegal flags 
*/
 
/* ----------------------------------- End Initialisation  of libraries ---------------- */

/* ----------------------------------- Main utilities ---------------------------------- */

void MCRLhelp(void);
/* Prints help information */ 

void MCRLsetOutputFile(char *filename);
/* Output must be written on a named output file instead of stdout.
   "filename" must be an address of a char array of MCRLsize bytes. 
   If filename[0]=='\0' then in this array will be stored the base name 
   of the inputfile, nothing with happen otherwise. 
   If MCRLsetOutputFile is called and the tool is invoked without filename in its last argument 
   then MCRLinitialize returns ATfalse 
 */
 
char *MCRLgetOutputFile(void);
/* Get the name of the output file. Returns NULL if it is not defined */      

void MCRLoutput(void);
/* Performs MCRLwrite using the arguments read by MCRLsetArguments */

void MCRLsetFilter(char *program);
/* Sets a program wich must be invoked before the tool starts.
   That program reads from stdin. The output of that program will be read by
   the tool.
*/

/* ----------------------------------- End of main utilities --------------------------- */

/* ----------------------------------- Updates and queries ----------------------------- */

ATerm MCRLgetSpec(void);
/* Returns the current mCRL specification */

void MCRLsetSpec(ATerm spec);
/* Replaces the current specification with mCRL specification "spec" */

ATerm MCRLgetProc(void);
/* Returns the LPE belonging to the current specification */

void MCRLsetProc(ATerm proc);
/* Replaces the LPE belonging to the current specification with LPE "proc" */

ATerm MCRLgetAdt(void);
/* Returns the ADT belonging to the current specification */

void MCRLsetAdt(ATerm adt);
/* Replaces the ADT belonging to the current specification with ADT "adt" */

ATermList MCRLgetListOfInitValues(void);
/* Returns the list of initial values in the process definition */

ATermList MCRLgetListOfPars(void);
/* Returns the list of data parameters in the process definition */

ATermList MCRLgetListOfVars(ATerm summand);
/* Returns the list of data variables belonging to the summand */

int MCRLgetNumberOfPars(void);
/* Returns the number of data parameters in the process definition */

int MCRLgetNumberOfVars(ATerm summand);
/* Returns the number of data variables belonging to the summand */

int MCRLgetNumberOfSummands(void);
/* Returns the number of summands of LPE */

ATermList  MCRLgetListOfSummands(void);
/* Returns the list of summands of LPE */

void MCRLsetListOfSummands(ATermList summands);
/* Sets the list of summands of LPE */

int MCRLstate2Number(ATerm x);
/* Returns the integer value argument x which has sort State
Def: I(one)->1  I(x2p0(x))->2*I(x)  I(x2p1(x))->2*I(x)+1 . 
I is short for MCRLstate2Number. (obselate)
*/

ATbool MCRLisClosedTerm(ATerm t);
/* Returns true if t is a closed term */

ATbool MCRLisPureConstructorSort(AFun sort);
/* Returns true if all constructors of sort are no lhs of a rewrite rule */

ATermList MCRLremainingVars(ATerm t, ATermList vars);
/* Arguments are a term and a variable list 
    [v(name_1, sort_1),...,v(name_n, sort_n)]
   Returned will be a list of variables which not occurs in t.
   If this list contains all variables and is equal to the original list then t is closed.
*/

/* ----------------------------------- End of updates and queries ------------------------- */

/* -------------------- Functions belongin to the type system ----------------------------- */

MCRLsymtype MCRLgetType(AFun s); 
MCRLsymtype MCRLgetTypeTerm(ATerm t);
/* Returns the type of symbol s. 
    (MCRLunknown, MCRLsort, MCRLconstructorsort, 
     MCRLenumeratedsort, MCRLvariable, MCRLconstructor, 
     MCRLfunction, MCRLcasefunction, or MCRLeqfunction) 
     Moreover:
     MCRLgetTypeTerm returns MCRLvariable if "t" is an integer term
*/

void MCRLsetType(AFun s, MCRLsymtype type); /* Obsolete */
void MCRLsetClass(AFun s, MCRLsymtype _class);
/* Sets the type of symbol s */

AFun MCRLgetSort(ATerm t);
/* Returns the sort of a term */


AFun MCRLgetSortSym(AFun f); /* obsolete */
AFun MCRLgetSortSymbol(AFun f);
/* Returns the sort of an AFun */

ATermList MCRLgetConstructors(AFun fsort);
/* Returns the constructors [cons_1(sort_1_1, sort_2_1,.., sort_n_1),
   ..., cons_m(sort_1_m, sort_2_m,.., sort_n_m)] of a constructor sort */

void MCRLsetConstructors(AFun fsort, ATermList cons);
   
ATermList  MCRLgetAllFunctions(void);
/* Returns the list of all defined functions. The arguments of these functions
are the sorts of the parameters. */

ATermList  MCRLgetAllSorts(void);
/* Returns the list of all defined sorts. */
  
int MCRLgetNumberOfConstructors(AFun fsort);
/* Returns the number of constructors of a constructor sort */

ATermList MCRLgetRewriteRules(AFun fsym);
/* Returns the rewrite rules belonging to fsym */

ATerm MCRLgetFunction(AFun fun);
/* Returns fun(sort_1,...,sort_n) belonging to AFun fun */

void MCRLdeclareVar(ATerm var);
/* Allocates an entry indexed by the symbol belonging to the name of
   var in the symbol table and puts the sort of var in that entry.
   That sort can obtained by MCRLgetSort. 
   Format var: v(name,sort) 
*/ 

void MCRLdeclareVars(ATermList variables);
/* Stores the variables and their sorts in the symbol table. 
   Supplies information needed for MCRLgetSort. All variables
   in terms used by the rewriter must be declared first by this routine
   or MCRLdeclareVarNames.
   Format variables: [v(name_1,sort_1)....v(name_n,sort_n)] 
*/

void MCRLdeclareVarName(ATerm varname);
/* Allocates an entry indexed by the symbol belonging to varname
   in the symbol table.  
*/ 

void MCRLdeclareVarNames(ATermList variable_names);
/* Stores the variable names in the symbol table. All variables in terms
   used by the rewriter must be declared first by this routine
   or MCRLdeclareVars.
   Format variable_names: [name_1 .... name_n]  
*/

void MCRLundeclareVar(ATerm var);
/* Removes an entry indexed by the symbol belonging to varname
   of parameter var from the symbol table.
*/

void MCRLundeclareVars(ATermList variables);
/* Removes entries indexed by the symbols belonging to the varnames
   of parameter variables from the symbol table.
   Format variables: [v(name_1,sort_1)....v(name_n,sort_n)] 
*/

void MCRLundeclareVarName(ATerm varname);
/* Removes an entry indexed by the symbol belonging to parameter varname
   from the symbol table.
*/

void MCRLundeclareVarNames(ATermList variables);
/* Removes entries indexed by the symbols belonging to the varnames
   of parameter variables from the symbol table.
   Format variable_names: [name_1 .... name_n]
*/

char *MCRLgetName(ATerm t);
/* Returns the print name of a MCRL function name. Important:
   the string stored in the array referenced by the returned adress will be 
   overwritten by a following call of MCRLgetName */

ATerm MCRLprint(ATerm t);
/* Returns the term which contains the print name of MCRL term t */

ATermList MCRLprintList(ATermList args);
/* Returns a list which contains the print names of the MCRL terms args */



void MCRLdeclareSort(AFun nsort, MCRLsymtype type, ATermList constructors);
/* Adds a new sort in the symbol table */

void MCRLdeclareFunction(ATerm function, MCRLsymtype type, AFun fsort);
void MCRLsetFunction(ATerm function, MCRLsymtype type, AFun fsort);
/* Adds a new function in the symbol table */
 
void MCRLassignSort(AFun var, AFun vsort);
/* Supplies information needed for MCRLgetSort */


ATerm MCRLdummyVal(AFun sort);
/* Returns a dummy value belonging to "sort" */


int MCRLisFiniteSort(AFun s);
/* Returns 1 if the sort s is `finite' otherwise
   0 is returned. We inductively define that a sort s is finite
   iff 
   1 there is at least one constructor function with target sort
     s. In other words s is a constructorsort (s is an MCRLconstructorsort
     or an MCRLenumeratedsort) and
   2 all argument sorts of each constructor with target sort s are finite.
*/

ATermList MCRLgenerateElementsOfFiniteSort(AFun s);
/* Returns a list of all elements of a sort s. 
   In case the list is not finite, it will not terminate.
   If sort s is not finite, this function yields NULL.
   See also MCRLisFiniteSort which contains the definition when
   a sort is considered finite.
   The order in which the terms is generated is deterministic
   and ought to be the same when this routine in invoked more
   often, except if new sorts or constructor functions have been
   added to the adt database.
*/


double MCRLgetNumberOfElements(AFun sort);
/* Returns an upperbound of the number of elements in <sort>. 
-1 will be returned if the estimated number of elements is infinite.
Remark: the rewrite system is not used during the computation */

char *MCRLextendName(char *name, ATermList sorts);
/* Returns a string that contains the function name as is used in the
   .tbf format. This is "name#sort_1#sort_2...#sort_n
*/

AFun MCRLextendSymbol(AFun *sorts, int n, char *format, ...);
/* Returns a symbol that contains the function name as is used in the
   .tbf format. This is "name#sort_1#sort_2...#sort_n
*/

ATerm MCRLuniqueTerm(char *fname, ATermList sorts);
/* Returns an unique function declaration fname(sort_1..sort_n), 
   which doesn't occur in specs */

void MCRLsetProjection(AFun constructor, int pos, ATerm projection);
/* Allocates a projection function to arg_pos of constructor.
   projection must have the form "projection_name(sort)"
*/

ATerm MCRLgetProjection(AFun constructor, int pos);
/* Get the projection function belonging to argument pos of the constructor */

ATermList MCRLgetProjections(AFun fsort);
/* Get the list of projections prepended with the list of det functions
   belonging to fsort if present, NULL otherwise */ 

void MCRLsetDetFunction(AFun fsort, AFun det);
/* Sets a determination function, "det" has the following format:
   detname(fsort) */
   
void MCRLsetDetFunctions(AFun fsort, ATermList dets);
 
ATermList MCRLgetDetFunctions(AFun fsort);
/* Get the list of determination functions [det_1(fsort),...,det_n(fsort)] 
   of fsort if present, NULL otherwise */

AFun MCRLgetEnumSort(int n); 
  
ATbool MCRLsetCaseFunction(AFun casef);

ATermList MCRLgetCaseFunctions(AFun fsort);
/* Get the list of casefunctions belonging to fsort if present, NULL otherwise.
   The format of the returned list: [casef_1(enum_m_1,fsort_1,...,fsort_m_1),...,
   casef_k(enum_m_k,fsort_1,...,fsort_m_k)]. The first case function
   has arity equal to number of constructers of fsort plus one. So,
   ATgetArity(ATgetAFun(ATgetFirst(MCRLgetCaseFunctions(fsort)))) = 
   MCRLnumberOfConstructors(fsort) + 1
*/

ATermList MCRLgetCaseSelectors(AFun casesym);
/* Get the list of case selecters (such as [T,F] in the case of "if") 
   of casesym in the right order if present, NULL otherwise */
   
ATerm MCRLparse(char *e);
/* Reads a term in natural form stored in char array e, and returns the 
   belonging MCRLterm (for example S(0) -> S#Nat(0#) )
*/

ATermList MCRLparseActions(char *e);
/* Reads a list of actions, separated by comma's, in natural form stored in 
   char array e and returns that list 
*/

ATerm MCRLparseFile(FILE *fp);
/* Reads a term in natural form from stream fp, and returns the
   belonging MCRLterm_
   However the names are NOT extended to "long names".
*/
 
int MCRLparseInvariants(FILE *fp);
/* Reads invariants for stream fp and makes it available for 
   MCRLgetInvariant and returns the number of read invariants.
*/

ATermList MCRLparseEquations(FILE *fp);
/* Reads a list of equations in natural form from stream fp.
   Returns the form e(varlist, lhs, rhs). 
   However the names are NOT extended to "long names".
*/

ATerm MCRLparseAdt(FILE *fp);
/* Returns the abstract data type belonging to the specification written 
on stream fp. 
*/

ATerm MCRLgetInvariant(int i);
/* Returns the i_th invariant.
   Can only be called after MCRLparseInvariants.
   The number i is counted from zero.
*/

ATermList MCRLparseTrace(FILE *fp, int *current);
/* Returns the trace read from trace file
   [action, statecomponent_1 ,..., statecomponent_npars, action, ......]
   current is the distance of the pointer to the end of the trace
*/ 
 
ATerm MCRLtranslate(ATerm e);
/* Translates the term e into ".tbf" format
*/ 

/* -------------------- Updating the abstract data type  ----------------------------- */
   
AFun MCRLputEquation(ATerm eq, ATbool *_new);
/* Adds an equation to the current specs. Format of an equation must be:
      e([v(<varname_1>, <sort_1>),...,v(<varname_n>, <sort_n>)], <lhs>, <rhs>)
      lhs and rhs are terms in which all variable names are from 
      {<varname_1>,...,<varname_n>} is not already present,
      assigns ATfalse to *new if already present and ATtrue otherwise,
      and returns the symbol of the left hand side.
      However if *new == NULL then only the check of presence will be done.
      If not present then 0 will be returned and the symbol of the left hand
      side otherwise.
      Attention: The rewrite system will not be updated !!! Only the specs which will be output
      is changed.
*/

AFun MCRLputConstructor(ATerm con, ATerm sort, ATbool *_new);
AFun MCRLputMap(ATerm map, ATerm sort, ATbool *_new);
/* Adds respectively a map, or constructor to the specs if not already present,
   assigns ATfalse to *new if it is already present and ATtrue otherwise,
   and returns the symbol of con respectively map. 
   However if *new == NULL then only the check of presence will be done.
   If not present then 0 will be returned and the symbol of con 
   respectively map will be returned otherwise.
   The signature sig has the following format 
   ATerm <f>(<sort_1>,...,<sort_n>); the result sort rsort has the format 
      ATmake("<str>",<sort name>)
   If the flag -no-extend-adt is used, then it is forbidden to add new
   functions and equations. If the wanted function is not found, then 
   these functions return 0.     
*/

AFun MCRLputSort(ATerm sort, ATbool *_new);
/* Adds a sort to the specs if not already present,
   assigns ATfalse to *new if it is already present and ATtrue otherwise,
   and returns the symbol of sort. 
   However if *new == NULL then only the check of presence will be done.
   If not present then 0 will be returned and the symbol of sort 
   will be returned otherwise.   
*/

AFun MCRLputIfFunction(ATerm sort, ATbool *_new);
/* Checks if there is already defined an if-then-else function
   with its belonging rewrite rules. If found and the rewrite rules
   are wrong then an error is generated.
   If not present it creates a new if-then-else function with its belonging 
   rewrite rules.
   Remark: It is not self-evident that the returned function is a case 
   function. The sequence of the selectors can be different from the
   sequences of the selectors of comparable case functions.
*/
    
AFun MCRLputCaseFunction(int n, ATerm sort, ATbool *_new);
/* Checks if there is already defined a casefunction
   with arity n+1 and sort "sort" and returns its symbol if present.
   If not present it creates a new case function with its belonging 
   rewrite rules. If not is available an enumerated sort of cardinality n, 
   then it creates that sort with his belonging constructors.
   However if *new === NULL it checks only if there is already defined a 
   casefunction and returns its symbol if found and 0 otherwise.

   The parameter *name is not present in the API.
   This will be automatically chosen as "if" if n=2 and "C<n>-<sort>" if n>2.
*/

AFun MCRLputAndFunction(ATbool *_new);
AFun MCRLputOrFunction(ATbool *_new);
AFun MCRLputNotFunction(ATbool *_new);
AFun MCRLputEqFunction(ATerm sort, ATbool *_new);
/* These functions add if not already present respectively "and","or","not", 
   and "eq#<sort>#<sort>" functions
   with their belonging equations to the specification. Returns its symbol 
   if success, 0 otherwise. Boolean parameter *new is ATfalse if the function 
   is already present and ATtrue if this function is added.
   If the flag -no-extend-adt is used, then it is forbidden to add new
   functions and equations. If the wanted function is not found, then 
   these functions return 0.
*/

/* -------- Utility functions to build terms -------- */
/* These functions can be used to build ATerm representations of mCRL terms
 * They check if their arguments are of the appropriate sort and all of
 * them fail (return NULL) if the required function symbols are not
 * present. <sort> stands for any sort. These functions require that
 * all variables are declared using MCRLdeclareVars
 */

/* eq : <sort> # <sort> -> Bool */
ATerm MCRLmakeEq(ATerm t1,ATerm t2);

/* if : Bool # <sort> # <sort> -> <sort> */
ATerm MCRLmakeIfThenElse(ATerm b,ATerm t1,ATerm t2);

/* and : Bool # Bool -> Bool */
ATerm MCRLmakeAnd(ATerm t1,ATerm t2);

/* or : Bool # Bool -> Bool */
ATerm MCRLmakeOr(ATerm t1,ATerm t2);

/* not : Bool -> Bool */
ATerm MCRLmakeNot(ATerm t);

/* T : -> Bool */
ATerm MCRLmakeTrue();

/* F : -> Bool */
ATerm MCRLmakeFalse();

/* -------- End of utility functions -------- */

/* -------- Level 2 Interface. Only needed for exceptional cases --------------------------*/
/* ----------------------------------- Initialisation  of libraries --------------------- */
   
ATbool MCRLinitializeXX(int *argc, char ***argv);
/* Initializes only the MCRL library.
   Doesn't test presence of illegal flags 
*/
   
ATbool MCRLinitializeYY(int *argc, char ***argv);
/* Initializes only the MCRL library.
   Tests presence of illegal flags */
   
ATbool MCRLinitializeRW(int *argc, char ***argv);
/* Initializes MCRL library and Rewriter library 
   Tests presence of illegal flags 
*/

ATbool MCRLinitializeSU(int *argc, char ***argv);
/* Initializes MCRL library and Substitution library 
   Tests presence of illegal flags 
*/
 
/* ----------------------------------- End Initialisation  of libraries ---------------- */
void MCRLsetArguments(int *argc, char ***argv);
/* Consumes the fitting arguments from the command line and makes a new 
   array of command arguments consisting of the remaining command arguments.
   In filename is stored the read file name. In argument filter can be defined 
   an input filter that will precede. 
*/ 

int MCRLcopyOption(char **newargv, char **argv, int argc, int i, int j);
/* Copies position i of argv to position j of newargv and returns j+1 */

ATbool MCRLisInitialized(void);
/* Returns ATtrue if the MCRL library is initialized, 
   ATfalse otherwise. 
*/
  
ATbool MCRLinitialize(void);
/* This must be called after MCRLsetArguments. This reads the
   .tbf file from stdin or from file specified in its last argument.
   Returns ATtrue if OK, ATfalse otherwise.
*/

ATbool MCRLinitializeAdt(ATerm adt);
/* This initializes the MCRLibrary if the .tbf file is already read.
   Only the data type definitions "adt" is given as its argument. The
   process part is not needed. MCRLgetSpec, MCRLgetProc ...   returns NULL.
   Returns ATtrue if OK, ATfalse otherwise.
*/

ATbool MCRLinitFile(FILE *inputfile);
/* Reads a MCRL specs in .tbf, .taf, or ATerm ascii format and 
   makes it current. 
   Returns ATtrue if OK, ATfalse otherwise.
*/

ATbool MCRLinitNamedFile(char *inputfilename);
/* Reads a MCRL specs in .tbf, .taf, or ATerm ascii format and 
   makes it current. If "inputfilename"==null" then read from stdin.
   Returns ATtrue if OK, ATfalse otherwise. 
*/

ATbool MCRLcheckRemainingFlags(int argc, char *argv[]);
/* Tests if there are flags left after consuming flags. Insensible
   for flags starting with -at-, -verbose. Returns ATtrue if OK,
   ATfalse otherwise.
*/

void MCRLwrite(char *filename, MCRL_OUTPUTFORMAT format);
/* Writes the current spec. on file "filename" in ASCII, TAF, or BAF format.
   If "filename" is null the specification is written to "stdout" 
*/

ATbool MCRLinitCaseDistribution(void);
/* Initializes the automatic case distribution mechanisme, which will be
   used by MCRLsimilarCasefunction */
   
AFun MCRLsimilarCasefunction(AFun srt, AFun casef);
/* MCRLsimilarCasefunction will be used by the automatic case distribution 
   mechanisme invoked by -case flag. Use only this routine after
   MCRLinitCaseDistribution
*/

ATerm MCRLcaseDistribution(MCRLREWRITE rewr, ATerm f); 
/*
Uses implicite distibutive rewrite rules on case functions.
f(x1,...,C(e,y1,...,ym),...,xn)=
         C(e,f(x1,...y1,...,xn),...,f(x1,...,ym,...xn))
*/         


int MCRLregistrateExistingProjections(int *_new);

#ifdef __cplusplus
}
#endif/* __cplusplus */
#endif
