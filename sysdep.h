/* $Id: sysdep.h,v 1.18 2007/06/29 13:30:57 bertl Exp $ */
#ifndef SYS_DEP_H
#define SYS_DEP_H
#ifdef __cplusplus
extern "C"
{
#endif/*__cplusplus */
/** @file
    Interface to system dependent calls.
**/
#include <stdio.h>
#include <stdarg.h>
#ifdef HAVE_STDINT_H
#include <stdint.h>
#endif


typedef int (*EachFile)(char *path);

typedef void* GZfile; 

/** 
@defgroup deletes Enumeration of values 
permitted as argument @c delete in @c CreateEmptyDir. 
@{ */
#define DELETE_NONE 0x00
#define DELETE_FILE 0x01
#define DELETE_DIR  0x02
#define DELETE_ALL  0x03 
/** @} */

#ifdef _MSC_VER
#include "winsock2.h"  /* htons, ntohs, u_short; link library: ws2_32.lib */
#include <malloc.h>   /* _alloca */
typedef unsigned short uint16_t;
typedef unsigned int   uint32_t;
typedef unsigned long  uint64_t;
typedef short int16_t;
typedef int   int32_t;
typedef long  int64_t;
#endif


/** 
@defgroup macros Standardized solution for declaring local variable-sized arrays.
@param type of the elements
@param name of the array variable
@param size of the array expressed in the number of elements
*/
#ifdef VARARRAY
#define DECLA(type, name, size) type name[size]
#else
#define DECLA(type, name, size) type *name = (type*) ((size)>0?alloca((size)*sizeof(type)):NULL)
#endif
/** @} */
/** Removes file
* @return 0 success 
* @return <0 error
*/
extern int RemoveFile(const char *name);

/** Creates empty directory
* @return 0 success 
* @return <0 error
*/
extern int CreateDir(const char *name);

/** Removes empty directory
* @return 0 success 
* @return <0 error
*/
extern int RemoveDir(const char *name);

/** 
Creates a directory referred by @c path. 
@param path to the directory
@param delete
- DELETE_NONE no files, sockets, fifos, and subdirectories will be deleted
- DELETE_FILE only files, sockets, and fifos inside @c path will be deleted
- DELETE_DIR  only subdirectories of @c path will be deleted
- DELETE_ALL  directory @c path will be made empty
*/
extern int CreateEmptyDir(const char *path, int _delete);

/** Calls for each found file in @c dir callback function @c eachFile.
@param dir which contains the files
@param eachFile callback function which must return @c 0 if OK, and has one 
argument (sort @c char*) @c path to file. */

extern int ForEachFileInDir(const char *dir, EachFile eachFile);
extern int ForEachDirInDir(const char *path, EachFile eachDir);

/** Check for existence of a directory.
  * @return 1 if @c name is a directory
  * @return 0 otherwise
  */
extern int IsADir(const char *name);

/** Check for existence of a regular file.
  * @return 1 if @c name is a regular file
  * @return 0 otherwise
  */
extern int IsReg(const char *name);

/** Check the access mode of file pointer.
  * @return 1 if access mode of @c f is read-only 
  * @return 0 otherwise
  */
extern int ReadOnly(FILE *f);
extern int WriteOnly(FILE *f);
  
/** See posix call "popen". */
extern FILE *Popen(const char *command, const char *type);

/** See posix call "pclose". */
extern int Pclose(FILE *stream);

/** Redirects stream  to filter.
    See freopen
  * @param filter which is connected to @c stream
  * @param type "r" or "w"
  * @param stream which will be connected to @c filter
*/
extern FILE *Redirect(const char *filter, const char *type, FILE *stream);

/** Truncates @c file to @c size bytes.
See @c truncate
*/
extern int Truncate(const char *file, long size);

/** Truncates @c file to @c size bytes.
See @c truncate
*/
extern int Ftruncate(FILE *file, long size);

extern char *GetCwd(char *path, int size);
extern int ExecVp(const char *path, char *const argv[]);

/** Returns size in bytes of file referred by file descriptor fd */
extern int FileLen(FILE *f);

/** Returns stream and the name of an unique temporary file.
Input must be a character array of length len.
*/
extern FILE *TempFile(char *fname, int len);

/** Print a line for example lines in a help tekst */
extern int Pr(const char *format, ...);

/** Regular expressions */
typedef void* preg_t;
preg_t RegCompile(const char *regex);

/** Matches string against compiled pattern.
  * @return 1 if matches 
  * @return 0 otherwise
  */
int RegMatch(preg_t preg, const char *s);

/* System time registration */
typedef struct timer *mytimer_t;

extern mytimer_t createTimer();
extern void deleteTimer(mytimer_t timer);
extern void resetTimer(mytimer_t timer);
extern void startTimer(mytimer_t timer);
extern void stopTimer(mytimer_t timer);
extern void reportTimer(mytimer_t timer,char *msg);
extern float timerUser(mytimer_t timer);
extern float timerReal(mytimer_t timer);
extern float timerSys(mytimer_t timer);
#ifdef DEVELOPMENT
extern int GetTimeOfDay(void);
#endif

extern uint16_t HtoNS(uint16_t hostshort);

extern uint16_t NtoHS(uint16_t netshort);

extern uint32_t HtoNL(uint32_t hostlong);

extern uint32_t NtoHL(uint32_t netlong);

#if defined C99 && C99 == yes
   #if defined HAVE_DECL_STRDUP && !HAVE_DECL_STRDUP
   extern char *strdup(const char *s);
   #endif
   #if defined HAVE_DECL_GETENV && !HAVE_DECL_GETENV
       extern char *getenv(const char *name);
   #endif
   #if defined HAVE_DECL_SETENV && !HAVE_DECL_SETENV
       extern int setenv(const char *name, const char *value, int overwrite);
   #endif
   #if defined HAVE_DECL_PUTENV && !HAVE_DECL_PUTENV
       extern int putenv(const char *value);
   #endif
   #if defined HAVE_DECL_UNSETENV && !HAVE_DECL_UNSETENV
       extern int unsetenv(const char *value);
   #endif
#else
   #if defined HAVE_STRDUP && !HAVE_STRDUP
       extern char *strdup(const char *s);
   #endif
#endif
#ifdef DEVELOPMENT
typedef struct {
   float utime, stime;
   long ixrss,idrss,isrss, nvcsw, nivcsw;
   } MCRLUSAGE;
   
MCRLUSAGE *Rusage(void);

#endif

GZfile GZopen(const char *path, const char *mode);
GZfile GZdopen(int fd, const char *mode);
int GZclose (GZfile file);
int GZflush (GZfile file);
int GZeof (GZfile file);
char *GZgets (GZfile file, char *buf, int len);
int GZputs (GZfile file, const char *buf);
int GZputc (GZfile file, int c);
int GZgetc (GZfile file);
int GZread (GZfile file, void *buf, unsigned len);
int GZwrite (GZfile file, void *buf, unsigned len);
int GZrewind (GZfile file);
int GZlen(GZfile file);
int GZprintf (GZfile file, const char *format, ...);
#ifdef LINUX
int GZscanf (GZfile file, const char *format, ...);
#endif

/* Buffer backage */
typedef struct {
   size_t sizeloc, size;
   char *ptr;
   char **rptr;
   size_t *rsizeloc;
   } bfile_t;
 
bfile_t*  bopen_memstream(size_t initLength, char **ptr, size_t *sizeloc);
void bfputc(char c, bfile_t *f);
size_t bfwrite(void *ptr, size_t size, size_t nmemb, bfile_t  *f);
int bfflush(bfile_t *f);
int bfclose(bfile_t *f);
void brewind(bfile_t *f);
size_t blength(bfile_t *f);

#ifdef __cplusplus
}
#endif/* __cplusplus */
#endif
