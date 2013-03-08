#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include "aterm2.h"

//Global precondition: the ATerm library has been initialised

ATermAppl MCparse(FILE *formStream);
/*Pre: formStream is a valid formula stream from which can be read       
  Post:the modal formula in formStream is parsed
  Ret: the parsed formula, if everything went ok
       NULL, otherwise
*/ 

#ifdef __cplusplus
}
#endif

