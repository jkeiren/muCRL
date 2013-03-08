#include "signature.h"

#ifdef MCRLLIB
void ProverSetArguments(int *argc, char ***argv);
void ProverInitialize(void);
#endif

int Init_prover(ATerm datatype,int argc, char *argv[]);
    /* Initialize the prover with a data specification 
     * Assumptions:
     * - 'eq#..' symbols really mean equality
     * - 'C2-Bool#Bool#Bool#Bool' is defined and means if-then-else
     * returns 1 if there are no argments left, and 0 if there are
     * remaining arguments 
     */

ATerm Prove(ATerm formula);
    /* Computes an ATerm equivalent to formula.
     * Assumptions:
     * - Init_prover has been called with spec
     * - free variables of formula are declared with Declare_variables
     * - formula is well formed in spec and has type bool
     */

ATerm Simplify(ATerm term);
    /* Simplifies the term w.r.t. the data type.
     * Currently all equations are used, but
     * a future release may use "simplifying" rules only.
     */

void print_BDD(ATerm bdd,FILE*);
    /* given a boolean term (typically output of Prove),
     * prints it in a BDD-like fashion in ASCII
     */

void dot_BDD(ATerm bdd,FILE*);
    /* given a boolean term (typically output of Prove),
     * prints it in a BDD-like fashion in dot-format.
     * this can be visualized by dot -Tps and ghostview
     */

void count_BDD(ATerm bdd,FILE*);
    /* counts and prints the size of a formula in various ways */

void print_example(ATerm bdd, ATerm polarity, FILE*);
    /* given a BDD print a path to a leaf labeled 'polarity'.
     *  The polarity should be prTRUE or prFALSE 
     */

/* EXPERIMENTAL: */

ATerm Prove2(ATerm formula);
/* this function is similar to Prove, but computes
   a BDD in bottom-up fashion first
*/

ATerm SimpIneq(ATerm BDD);
/* Assumption: (Nat ; 0,s ; eq,le) is the substructure of
   the natural numbers with equality and less-than-or-equal.
   SimpIneq returns the BDD obtained by cutting away
   inconsistent paths in this substructure.
   It is not complete for =/=
   example: x<=y, y<=x+1, x<=z,z<=x+1, x<=w,w<=x+1,
            y =/= z, y =/= w, w =/= z
   is unsatisfiable, but this is currently not detected.
*/
