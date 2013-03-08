/* $Id: stringdbs.h,v 1.1 2004/01/29 13:17:32 bertl Exp $ */
#ifndef STRINGDBS_H
#define STRINGDBS_H

typedef struct stringdbs *stringdbs_t;

/*
 * Constants describing file formats.
 */
#define SD_AUTO 0
#define SD_PLAIN 1
#define SD_GZIP 2

extern int SDcreate(stringdbs_t *dbs,char *filename,int format);
extern int SDclone(stringdbs_t *newdbs,char *filename,int format,stringdbs_t olddbs);
extern int SDopen(stringdbs_t *dbs,char *filename,int format,int readonly);
extern int SDclose(stringdbs_t dbs);
extern char* SDerror();

extern int SDcount(stringdbs_t dbs);

#define SD_INDEX_FAILED (-1)
extern int SDindex(stringdbs_t dbs,char* string);
extern char* SDstring(stringdbs_t dbs,int index);

#endif
