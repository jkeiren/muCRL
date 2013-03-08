/* $Id$ */

/**
@file stringindex.h
@brief Indexed set of strings.
*/


#ifndef STRING_INDEX_H
#define STRING_INDEX_H

/// String index handle.
typedef struct stringindex *string_index_t;

/// Create an index.
extern int SIcreate(string_index_t *si);

/// Destroy an index.
extern int SIdestroy(string_index_t *si);

/// Constant returned if lookup fails.
#define SI_INDEX_FAILED (-1)

/// Find if present.
extern int SIlookup(string_index_t si,const char*str);

/// Insert if not present.
extern int SIput(string_index_t si,const char*str,int *index);

/// Insert if not present at a specific position.
extern int SIputAt(string_index_t si,const char*str,int pos);

/// Delete the element str.
extern int SIdelete(string_index_t si,const char*str);

/// Delete all elements.
extern int SIreset(string_index_t si);

/// Get the string.
extern char* SIget(string_index_t si,int i);

/// Get the size of the defined range.
extern int SIgetSize(string_index_t si);

/// Get the number of strings.
extern int SIgetCount(string_index_t si);
#endif
