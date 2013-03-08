/* $Id: utl.h,v 1.7 2007/06/29 13:30:57 bertl Exp $ */
#ifndef UTL_H
#define UTL_H
/** @name  Utilities
*/
//@{
#include <unistd.h>
#include <sys/types.h>
#include <stdio.h>
#include <stdarg.h>
#include <errno.h>
#include <stdlib.h>
#define MAXDIGITS 10
#define FNAMESIZE 1024
extern int errno;
/*
#define fflush fflush_unlocked
#define fread fread_unlocked
#define fwrite fwrite_unlocked
#define fputc fputc_unlocked
#define fgetc fgetc_unlocked
#define fgets fgets_unlocked
#define fputs fputs_unlocked
*/

/*
@name Definitions of error codes
*/
//@{
/*
@memo Buffer is full
*/
#define ERR_FULL -1
/*
@memo Buffer is empty
*/
#define ERR_EMPTY -2
/*
@memo Cannot read
*/
#define ERR_READ -3
/*
@memo Cannot write
*/
#define ERR_WRITE -4
/*
@memo File is not defined
*/
#define ERR_FILE_NULL -5
/*
@memo Directory is not defined
*/
#define ERR_DIR_NULL -6
/*
@memo Unspecified errer
*/
#define ERR_NULL -7
/*
@memo Version clash
*/
#define ERR_INCOMPAT -8
/*
@memo Parse error
*/
#define ERR_PARSE -9
//@}
/**
  @memo Initialises this package. 
  @doc Will be run at most once
  @param msg_fp output file pointer, if NULL then {\tt stderr} is assumed
  @param print_tag {\tt printmsg} header tag (if NULL no header tag will be written)
  @param error_tag {\tt errormsg} header tag (if NULL no header tag will be written)
  @param format extra info, which will be printed by message and error
  @return 0 success
  @return <0 failure
*/
int UTLinit(FILE *msg_fp, char *print_tag, char *error_tag, 
    const char *format,...);

void setLocal();   
void setBinary(void);
void setText(void);
/**
@return info belonging to the parameter errorcode
*/
char *errortxt(int errcode);

/**
@memo generates error message and exits
*/
void errormsg(const char *format, ...);

/**
@memo prints message
*/
void printmsg(const char *format, ...);

/**
@memo returns errcode
*/
int errcode(void);
/**
@memo generates an error
@param errcode the code of the error
@param format extra information
@return errcode negative number
*/
int mkerror(int errcode, const char *format, ...);
/**
@memo truncate files from a position indicated by ftell
@param fp file pointer
*/
void errorreset(void);
int readPair(FILE *f, int32_t *elm);
int writePair(FILE *f, int32_t *elm);
int readBinary(FILE *f, int32_t *elm,int n);
int writeBinary(FILE *f, int32_t *elm, int n);
/**
@memo reads a UTF data element
@param f file
@param data string containing the read data
@param size of {\tt data} in bytes
@return >=0 length of string
@return <0 error
*/
int readUTF(FILE *f, char *data, int size);
int readUTF32(FILE *f, char *data, int size);

/**
@memo writes data in UTF format
@param f file
@param data array which contains the data to be written
@param size  of {\tt data} in bytes
@return >=0 success
@return <0 error
*/
int writeUTF(FILE *f, char *data, int size);
int writeUTF32(FILE *f, char *data, int N);

/**
@memo prints in UTF format
@param f file
@param format of data
@return >=0 success
@return <0 error
*/
int printUTF(FILE *f, const char *format, ...);

/**
@memo reads an integer in UTF format
@param f file
@param r containing the read integer
@return >=0 size of int
@return <0 error
*/
int readintUTF(FILE *f, int *r);
int readlongUTF(FILE *f, long *r);


/**
@memo reads a UTF string
@param f file
@return string (volatile)
*/
char *readstringUTF(FILE *f);
char *readstringUTF32(FILE *f);

/**
@memo writes an integer in UTF format
@param f file
@param r containing the integer which must be written
@return >=0 success
@return <0 error
*/
int writeintUTF(FILE *f, int r);
int writelongUTF(FILE *f, long r);

int getRecordSize(void);
file_t UTLopen(char *dir, char *mode, const char *format, ...);
file_t path(dir_t dir, char *mode, const char *format,...);
#ifdef LINUX
int clientSocket(char *hostname, int port, int bsize);
int contactSocket(char *portname, int port, int cnt);
int serverSocket(int port, int bsize);
int Accept(int sd);
int Fileno(FILE *f);
#endif
//@}
#endif
