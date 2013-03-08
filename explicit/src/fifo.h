/* $Id: fifo.h,v 1.2 2006/05/17 08:08:42 bertl Exp $ */
#ifndef FIFO_H
#define FIFO_H
/** @name First in first out buffer.
   The buffer is parametrized with the type {\tt file_t} and 
   type {\tt dir_t}. It is possible to pop elements from the front
   of the queue and to put these elements back (unpop).
*/



//@{
typedef void *fifo_t;
/** 
@memo Creates a new fifo memory buffer
@param size initial size of buffer (number of objects)
@param width size of objects in buffer (number of bytes)
@param file in which buffer will be dumped
@param dir in which checkpoint information will be 
dumped
@return fifo handler to fifo buffer 
*/

fifo_t FIFOcreateMemo(int size, int width, file_t file, dir_t dir);

#ifdef LINUX
/** 
@memo Creates a new fifo file buffer
@param width size of objects in buffer (number of bytes)
@param file in which buffer will be dumped
@return fifo handler to fifo buffer 
*/
fifo_t FIFOcreateFile(int width, file_t file);
#endif

/**
    @param fifo handler
    @return 0 success
    @return <0 failure
*/
int FIFOdestroy(fifo_t fifo);

/**
    @param fifo handler
    @return 0 success
    @return <0 failure
*/
int FIFOreset(fifo_t fifo);

/**
@memo Puts an  object in front of {\tt fifo} in case {\tt obj} is unequal
to {\tt NULL}.
@param fifo handler
@param obj input parameter containing an object.
However if {\tt obj} is equal to {\tt NULL} 
then all objects which are popped will be removed.
@return 0 success
@return <0 failure, {\tt fifo} is full
*/
int FIFOput(fifo_t fifo, void* obj);

/**
@memo Loads tail object into {\tt obj} and removes it  
@param fifo handler
@param obj output parameter containing object 
({\tt NULL} permitted).
@return 1 success, {\tt fifo} is empty after this operation
@return 0 success
@return <0 failure, {\tt fifo} is empty
*/
int FIFOget(fifo_t fifo, void* obj);

/**
@memo Loads an object in {\tt obj} without removing this 
from {\tt fifo}
@param fifo handler
@param idx index relative to tail of {\tt fifo}
@param obj output parameter containing object
@return 0 success
@return <0 failure, {\tt fifo} is empty
*/
int FIFOgetElm(fifo_t fifo, int idx, void* obj);

/**
@memo Replaces an object at index {\tt idx}  
@param fifo handler
@param idx index relative to tail of {\tt fifo}
@param obj input parameter containing an object
@return 0 success
@return <0 failure, {\tt fifo} is empty
*/
int FIFOupdateElm(fifo_t fifo, int idx, void *obj);

/** 
@memo Undoes the last get operation. 
@param fifo handler
@return 0 success
@return <0 failure, {\tt fifo} is full
*/
int FIFOunget(fifo_t fifo);

/**
@param fifo handler
@return number of objects in {\tt fifo}
*/
int FIFOgetCount(fifo_t fifo);

/**
@param fifo handler
@return number of objects, popped objects included  
*/
int FIFOgetAllCount(fifo_t fifo);

/**
@memo Pops a frame consisting of {\tt number} objects from {\tt fifo} 
@param fifo handler
@param number input parameter
\begin{description}
    \item $\ge 0$ number of objects will be popped from the front
    \item $<0$ minus {\tt number} of objects will be popped 
       from the tail
\end{description} 
@return 1 succes,  empty after this operation
@return 0 succes,  not empty after this operation
@return <0 failure, empty before this operation
*/
int FIFOpop(fifo_t fifo, int number);

/**
@memo Pushes the last popped frame in front of the queue
@doc That frame consists of objects which are popped from the front of
{\tt fifo}. Objects which are popped from the tail of the stack are not
remembered.
@param fifo handler
@return 1 success, all frames are pushed after this operation
@return 0 success, not all elements are pushed
@return <0 failure, there are no frames to be pushed before this operation
*/
int FIFOunpop(fifo_t fifo);


/** 
@memo Returns a pointer to the  buffer (for direct access)
@param fifo handler
@return buffer
*/
void *FIFOgetArray(fifo_t fifo);
unsigned long FIFOgetByteSize(fifo_t fifo);
//@}
#endif
