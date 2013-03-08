#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include "aterm2.h"
#include "config.h"
#include "mcfunc.h"
#include <stdbool.h>

//Global preconditions:
//- the ATerm library has been initialised

ATermAppl MCparseModalFormula(FILE *formStream, bool reduce,
  int acLevel, int vbLevel, bool saveToMCRLFormat);
/*Pre: formStream points to a stream from which can be read
       0 <= acLevel <= 2, 0 <= vbLevel <= 3
       if saveToMCRLFormat, an mCRL data specification is present in the mCRL
       library
  Post:if formStream contains exactly one modal formula, the formula is parsed
       and returned in the ATerm format; otherwise NULL is returned and an
       appropriate error message is printed to stderr.
       If reduce, all regular operations are replaced by equivalent non-regular
       operations.
       Alpha conversion is applied based on the value of acLevel:
       - 0 (none)   : no alpha conversion
       - 1 (scope)  : names of bound variables that are in each other's scope
                      are different
       - 2 (full)   : all names of bound variables are different
       The printing of intermediate messages is controlled by vbLevel:
       - 0 (silent) : only errors are printed
       - 1 (normal) : errors and warnings are printed
       - 2 (verbose): errors, warnings and short status information is printed
       - 3 (debug)  : many messages are printed to make debugging possible
       If saveToMCRLFormat, the types of expressions occurring in the modal
       formula are checked and the formula is translated to the internal mCRL
       format, using the data specification that is present in the mCRL library.
*/ 

void MCtest(void);
//will be removed in the final version

#ifdef __cplusplus
}
#endif
