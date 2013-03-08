/* $Id: vector_db.h,v 1.10 2007/06/29 13:30:57 bertl Exp $ */
#ifndef VDB_H
#define VDB_H

/** @file
   Interface to an indexed set of data records called a vector database.
   
   A vector database is parametrized with the type @c elm_t, @c file_t, 
   @c idx_t and, @c dir_t.
   Data records are fixed length arrays of sort @c *elm_t.
   The prefix @c VDB is an abbreviation of vector database.
   
   Data records can be put and indexes can be fetched immediately by respectively 
   @c VDBput and @c VDBgetIdx or they can be put and fetched with a
   certain delay by @c VDBrequestPut and @c VDBrequestGetIdx.
   In the latter case the requested index will be delivered via a 
   callback funcion @c gcb, abbreviation of get callback.
   This callback function will be invoked just after the moment of 
   putting/fetching of the data record into/from the database.
   
   An extra feature is that each index of a new data record is added
   to a queue. Indexes will be fetched from the front of the queue
   by @c VDBforceSome. These indexes are represented as a range  
   @c [ofs,len) which will be entered as argument of a callback 
   function @c rcb, abbreviation of range callback. A range callback 
   can only be performed if the data records belonging to all indexes
   of the entered range are actually put into the database.
    
   These callback functions will be invoked during the call of 
   @c VDBforceSome. @c VDBforceSome is obliged to fetch at least
   one index from the queue; if this is not possible then a put request
   must be performed which fills the queue; if this is also not possible 
   then @c VDBforceSome returns 0 without invoking a range callback, 
   otherwise @c VDBforceSome performs one or more range callbacks and 
   returns a number unequal to 0. 
   The execution of outstanding put and get requests can be forced 
   by @c VDBforceSome. The execution of put and get requests 
   happens in arbitrary order. 
    
   There is a possibility to submit a barrier request, @c VDBsetBarrier. 
   A barrier request will be performed by @c VDBforceSome after
   all new indexes arised from @c put -requests and -calls submitted before 
   are included in an argument of some already processed range callback.  
   Each new index arised from @c put -requests and -calls submitted after 
   the submission of a barrier request must be included in an argument of
   some range callback which will be invoked after the barrier request 
   is performed.  Performing a barrier request implies calling a user 
   defined callback function @c bcb, abbreviation of barrier callback.
   
   This interface accesses depending on the input parameter  
   @c channel of 
   @c VDBcreate one of two different types of databases, namely
   a server database, or a client database.
*/

/** This indicates the record type loaded by @c lcb */
typedef enum {VDBdata, /**< record contains data */
              VDBbarrier  /** record indicates barrier */  
             } 
VDBload_t;

/** This indicates the mode of VDBforceSome */
typedef enum {VDBall, /**< one or more data elements */
              VDBuntilMark,  /**< pending data records until mark (exclusive) */
              VDBoneMark /** pending data records until mark (inclusive) */ 
             } 
VDBforcemode_t;

typedef void *vdb_t;

/**
Range Callback Function.
 
This callback function will be invoked during the call of
@c VDBforceSome.  
The index of each new added data record with @c VDBrequestPut  
or @c VDBput is added to a queue. The contiguous indexes are repesented as a range 
<tt> [index,index+number) </tt>
which is expressed by the arguments @c index and @c number. 
The data records whose indexes are included in the range must have been 
actually put into the database. Each index is included exactly
once in one range.
It is garanteed that the calls of a range callback function are not nested.
Remark: The call @c VDBforceSome inside a range callback is not permitted
to avoid deadlocks. 
@param id database identifier 
@param index of first added data record since 
the last call of @c rcb
@param number of indexes of added data records since 
the last call of @c rcb
@return 
- 0 success, the calling @c VDforceSome returns with 0
- <0 the calling @c VDforceSome returns with this value 
*/
typedef int (*range_cbt)(int id, idx_t index, int number);

/**
Barrier Callback Function. 

All indexes of the data records belonging to put -requests and -calls
submitted before the call of the belonging @c VDBsetbarrier are
contained in arguments of already performed range callbacks.
Before handling the next requests this callback function is 
invoked. 
@param id of database 
@param tag supplied by user as second argument in @c VDBsetBarrier
*/
typedef int (*barrier_cbt)(int id, void *tag);

/**
Get Callback Function.
 
This callback function will be invoked during actually 
getting/putting a data record
from the database by respectively @c VDBrequestGetIdx
and @c VDBrequestPut.
@param id of database 
@param tag supplied by user in second argument of 
@c VDBrequestGetIdx or @c VDBrequestPut
@param index of data record supplied by user in third argument of 
@c VDBrequestGetIdx or @c VDBrequestPut
*/
typedef void (*get_cbt)(int id, void *tag, idx_t index);

/**
Load Callback Function.
 
This callback function will be repeatedly invoked if  
data records are read from a stream during invocation of @c VDBcreate.
Each time after a data record is read and before it will put into
the database this callback function is invoked. 
@param id of database 
@param content of the  file
@param number of data records in database
@param elm which will put into the database. If @c elm is equal to 
@c null then a barrier is found.
@return
- 1 invalid @c elm is not put into the database. 
- 0 continue with putting @c elm into the database and 
          reading the next record
- <0 stop reading next records and don't put @c elm into the 
        database. The files
will be truncated to the end position of the last entered data record.
*/
typedef int (*load_cbt)(int id, VDBload_t content, int number, elm_t *elm);
  
/**
Creates a new standalone-, server-, or client-, database.

@param id of database. 
@param width of data record expressed in number of elements of 
type @c elm_t
@param file from which data records are loaded 
and to which the putted ones will be written.
@param dir loads data records from @c dir instead of @c file.
@param channel provides communication. 
@c channel can have one of the 
following two possibilities
- @c null server database
- @c otherwise client database
@param gcb callback function which will be invoked during each actually 
    getting/putting a 
    data record from/into the database with respectively 
    @c VDBrequestGetIdx and @c VDBrequestPut. 
    @c null may be entered for this parameter.
@param rcb callback function which will be invoked during the call 
      of @c VDBforceSome if the queue of indexes is not empty 
      or there are pending data records. 
      @c null may be entered for this parameter.
@param bcb callback function which will be invoked during processing a 
    barrier. @c null may be entered for this parameter.
@param lcb callback function which will be repeatedly invoked after reading  
a data record from @c file and before putting it into the database.
@c null may be entered for this parameter. 
After reading each record and before eventually putting it 
into the database the callback function @c lcb will be called.
The lower bound of the first generated range is equal to 
the number of loaded data records.
@return vdb handler to created vector database 
*/
vdb_t VDBcreate(int id, int width, file_t file, dir_t dir, channel_t channel,  get_cbt gcb, range_cbt rcb,
    barrier_cbt bcb, load_cbt lcb);
    
/* 
  Reads records from the stream referred by parameter @c file 
  in @c VDBcreate and puts data records into the database.
  @param vdb database handle
int VDBread(vdb_t vdb);
*/

/**
   Truncates vector database.
   @param number of data records
   @param vdb database handle
   @return >=0 success, <0 failure
*/

int VDBtruncate(vdb_t vdb, int number);

/**
   Destroys vector database
   @param vdb database handler 
   @return 
   - >=0 success
   - <0 failure
*/
int VDBdestroy(vdb_t vdb);

/**
    Blocking - puts data record into 
    @param vdb database handler
    @param data record - input
    If @c data is equal to @c null,
    which may occur in server databases, 
    then data records will be received from clients.
    @param new - output: 
    - 0 not a new data record
    - 1 a new data record 
    @c null may be entered for this parameter
    @return
    - index of data record
    - -1 in case of error
*/
idx_t VDBput(vdb_t vdb, elm_t *data,  int *new);

/**
    Blocking - gets index of data record in database.
    @param vdb database handler
    @param data record - input
    @return 
    - index of data record if present
    - -1 if not present
*/
idx_t VDBgetIdx(vdb_t vdb, elm_t *data);

/** 
Blocking - gets data record from.

@param vdb database handler
@param data record - output.
@c null may be entered for this parameter.
@param index of data record - input
@return 0 success, <0 failure
*/
int VDBget(vdb_t vdb, elm_t *data, idx_t index);

/**
Returns number of data records in the database.

@param vdb database handler
@return number of data records in the database
*/
int VDBgetCount(vdb_t vdb);

/*
@param vdb database handler
@return tag belonging to last encountered barrier (@c null  
if no barrier is encountered)
void *VDBgetTag(vdb_t vdb);
*/

/** 
Nonblocking - requests to put a data record into.

If @c tag is unequal @c null the defined callback function 
@c gcb will be invoked after actually putting a data record into the 
database.
Even if the data record is already present and @c tag is unequal @c null the 
callback function @c gcb will be invoked.
@param vdb database handler
@param tag 2th argument in @c gcb
@param data record - input
@return 0 success
@return <0 failure
*/
int VDBrequestPut(vdb_t vdb, void *tag, elm_t *data);

/** 
Nonblocking - requests to fetch a data record from.

If @c tag is unequal @c null the defined callback function 
@c gcb will be invoked during actually fetching a data record from the database.
If argument @c idx of @c gcb is equal to -1 then @c data is not 
present.
@param vdb database handler
@param tag 2th argument in @c gcb 
@param data record - input
@return 0 success, <0 failure
*/
int VDBrequestGetIdx(vdb_t vdb, void *tag, elm_t *data);

/** 
Requests a barrier. 

All indexes arised from put -requests and -calls before this call
are included in an argument of some range callback. All those 
range callbacks are completed before the barrier request will 
be performed. Performing a barrier request implies calling @c bcb
(barrier callback function). 
@param vdb handler
@param tag 2th argument in @c bcb
@return 0 success, <0 failure
*/
int VDBsetBarrier(vdb_t vdb, void *tag);

/**
Invokes if possible at least one callback @c rcb with a nonempty 
range.

This call blocks. If needed, pending data records are put into the database.
This function is the only function which invokes callbacks @c rcb.
@param vdb database handler
@param mode 

- VDBuntilMark - try to process data records until the barrier record
- VDBoneMark   - try to process data records until the barrier record
                 and process that barrier record too.
- VDBall       - try to process one or more data records                
@return 1 if one or more callbacks @c rcb are invoked and all 
return a value greater equal to 0.
@return 
- 0 if no callback @c rcb is invoked. 
It is possible that pending barrier callbacks are 
invoked whereas there no range callbacks are invoked.
- <0 the last range callback returns this value and all 
previous callbacks return a value greater equal to 0.
*/
int VDBforceSome(vdb_t vdb, VDBforcemode_t mode);

/** Gets identifier of @c vdb. */
int VDBgetId(vdb_t vdb);

/** Executes commands from channel 
@param vdb handler
@param channel from which the input is read and output is send
@return 0>= success, <0 failure
*/
int VDBreact(vdb_t vdb, channel_t channel);

file_t VDBgetFile(vdb_t vdb);
int VDBdir(vdb_t vdb);
/* Returns number of data records in vdb */
int VDBupdateFile(vdb_t vdb);

/*
array_t VDBgetArray(vdb_t vdb);
void VDBsetArray(vdb_t vdb, array_t array);
*/

vdb_t VDBcreateExtra(int id, int keylength, int valwidth, file_t *vdbf, 
load_cbt lcb);
void VDBputExtra(vdb_t vdb, idx_t idx, void *obj);
int VDBaddExtra(vdb_t vdb,  void *obj);
void VDBgetExtra(vdb_t vdb,  void *obj, idx_t idx);
void VDBflush(vdb_t vdb, idx_t idx);
int VDBgetWidth(vdb_t vdb);
unsigned long VDBgetByteSize(vdb_t vdb);
float VDBgetMsgTime(vdb_t vdb); 
float VDBgetMsgMinTime(vdb_t vdb); 
float VDBgetMsgMaxTime(vdb_t vdb);
void VDBsetNewLevel(vdb_t vdb); 
void VDBreset(vdb_t vdb); 
unsigned long VDBgetMsgCount(vdb_t vdb);
void VDBsetMsgTimes(vdb_t vdb, GZfile f);
#endif
