/* $Id:$ */

/** @file sede.h 
    Serialize - Deserialize interface. 
    
    This interface is parametrized with a @c state type and a
    @c context type.
*/
    
#include <unistd.h>

/** Serialize Deserialize Callback Function. 
This function will be entered as a parameter to @c SEDEread or @c SEDEwrite.
This will be called during @c SEDEread or @c SEDEwrite.
@param size of the serialized state vector
@param state_vec  serialized state vector
@param context pointer
@return <0  if failure
*/
typedef ssize_t (*SEDEcallback_t)(size_t size, void *state_vec,  void *context);
struct context_s {SEDEcallback_t callback;};
/**
Macro which must be called with name @c context after @c typedef of 
@c context_t. It defines the struct @c context_s. The first field is
@c callback, which will be initialized by the user defined callback function 
named @c context_c during the call of SEDE_DECLARE.
*/
#define SEDE_TYPEDEF(context)  \
struct context##_s {SEDEcallback_t callback;context##_t data;};

/**
Macro which must be called with names @c context, @c context_c, and 
@c var after call SEDE_TYPEDEF(context) and 
definition of callback function named @c context_c.
 
It declares the variable @c var. The first field is
@c callback, which is initialized by the user defined callback function named
@c context_c.
*/
#define SEDE_DECLARE(context, context_c, var)  \
struct context##_s var[1] = {[0]={.callback=context_c}};


/** Macro which returns the context of type @c context_t belonging to @c var. */
#define SEDE_DATA(context, var)     (((struct context##_s*) var)->data)
/** Macro which returns the pointer to the in the context defined callback
function belonging to @c var. */
#define SEDE_CALLBACK(var) ((struct context_s*) var)->callback

/** 
    Writes a state by calling @c callback which is included in 
      @c wc.
    @param state_p *state_t
    @param wc  .data contextWrite_t
*/
int SEDEwrite(void *state_p, void *wc);

/** 
    Reads a state by calling @c callback which is included in 
      @c rc.
    @param state_p **state_t
    @param rc  .data contextRead_t
*/
int SEDEread(void **state_p, void *rc); 

/** 
    Read callback.
    @param size
    @param state_vec state vector of @c size bytes
    @param rc read context
*/
ssize_t Read_c(size_t size, void *state_vec, void *rc);

/** 
    Write callback.
    @param size
    @param state_vec state vector of size bytes
    @param wc  write context
*/
ssize_t Write_c(size_t size, void *state_vec, void *wc);
