/* $Id: term_db.h,v 1.6 2006/01/12 10:17:22 bertl Exp $ */
#ifndef TDB_H
#define TDB_H
/**
@file 
Interface to an indexed set of terms called a term database.

The term database is parametrized with @c term_t, @c file_t, @c idx_t and, 
@c dir_t.
The prefix @c TDB is an abbreviation of term database.
*/

typedef void *tdb_t;

/** Iterator callback function, used as argument in @c TDBrunThrough.

This function will repeatedly be invoked on each element of the 
database.
@param string representation of the term on which this function is invoked
@return
- <0 stop iterating 
- 0 continue 
*/

typedef int (*tdb_cb)(char *string);
 
/** 
Creates a new term database.

@param id of database. 
@param file from which data records are loaded during the call of @c TDBread
and to which these are written.
- @c null or @c read-only stand-alone database or client database
- @c write/read server database
@param shared directory which provides communication. 
If @c shared is equal to @c null then the created database is a stand-alone 
database.
- @c null stand-alone database
- @c otherwise server or client database
@return tdb handler to created term database 
*/
tdb_t TDBcreate(int id, file_t file, channel_t shared);

/** 
  Reads records from the stream referred by parameter @c file 
  in @c TDBcreate and puts data records into the database.
  @param tdb database handle
*/
int TDBread(tdb_t tdb);

/**
   Destroys term database.
   
   @return >=0 success, <0 failure
*/

int TDBdestroy(tdb_t tdb); 

/**
Puts term into the database.

    @param tdb database handler
    @param term input parameter. If @c term is equal to @c null,
    which may occur in server databases, 
    then terms will be received from clients.
    @param new output parameter
    - 0 not a new term 
    - 1 a new term
    @c null may be entered for this parameter.
    @return index of @c term
*/
idx_t TDBput(tdb_t tdb, term_t term, int *new);

/**
Gets term from the database.

@param tdb term database handler 
@param idx of term
@return term belonging to @c idx.
*/
term_t TDBget(tdb_t tdb, idx_t idx);

/**
Returns number of terms in the database.

@param tdb  database handler
@return number of elements in the database
*/
int TDBgetCount(tdb_t tdb);

/** Iterates through terms in database.

On each term in the database the callback function @c cb is invoked.
*/
int TDBrunThrough(tdb_t tdb, tdb_cb cb);

/** 
Gets the file descriptor of the control channel.
@param tdb  database handler
@return descriptor of control channel if @c tdb is server database, 
-1 otherwise
*/
int TDBgetChannel(tdb_t tdb);
/** 
Sets the channel.
@param vdb  database handler
@param channel the channel on which the messages flows
@return -1 on error
*/

int TDBreact(tdb_t tdb, channel_t channel);
int TDBsync(tdb_t tdb);
int TDBlessThanMaster(tdb_t tdb);
void TDBsetId(tdb_t tdb, int id);
float TDBgetMsgTime(tdb_t tdb);
float TDBgetMsgTime(tdb_t tdb); 
float TDBgetMsgMinTime(tdb_t tdb); 
float TDBgetMsgMaxTime(tdb_t tdb);
void TDBsetNewLevel(tdb_t tdb);
void TDBsetMsgTimes(tdb_t tdb, GZfile f);

unsigned long TDBgetMsgCount(tdb_t tdb);
#endif
