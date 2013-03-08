/* $Id: array.h,v 1.2 2006/05/17 08:08:42 bertl Exp $ */
#ifndef ARRAY_H
#define ARRAY_H

/** @name Variable sized array list.
   Random read and sequential add
   The array is parametrized with the type {\tt file_t} 
   of the array.
*/



//@{
typedef void *array_t;
/** 
@memo Creates a new array
@param size initial size of buffer (number of objects)
@param width size of objects in buffer (number of bytes)
@param file in which array will be written, from which it will be loaded
@param vdb filters elements from @file which are represented in @c vdb
@return handler to array 
*/
#ifndef VECTOR_DB_C
#include "vector_db.h"
#endif

array_t ALcreate(int size, int width, file_t file, vdb_t vdb);

/**
    @param array handler
    @return 0 success
    @return <0 failure
*/
int ALdestroy(array_t array);


/**
@memo Adds an  object in front of {\tt array} 
@param array handler
@param obj input parameter containing an object.
@return 0 success
@return <0 failure, {\tt fifo} is full
*/
int ALadd(array_t array, void* obj);


/**
@memo Loads an object in {\tt obj} without removing this 
from {\tt array}
@param array handler
@param idx index
@param obj output parameter containing object
@return 0 success
@return <0 failure, {\tt array} is empty
*/
int ALget(array_t array, int idx, void* obj);

/**
@memo Replaces an object at index {\tt idx}  
@param array handler
@param idx index 
@param obj input parameter containing an object
@return 0 success
@return <0 failure, {\tt array} is empty
*/
int ALupdate(array_t array, int idx, void *obj);


/**
@param array handler
@return number of objects in {\tt array}
*/
int ALgetCount(array_t array);

/** 
@memo Returns a pointer to the  array (for direct access)
@param fifo handler
@return buffer
*/
void *ALgetArray(array_t array);
file_t ALgetFile(array_t array);
int ALgetWidth(array_t r);
//@}
#endif
