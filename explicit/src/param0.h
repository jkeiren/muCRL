/* $Id: param0.h,v 1.8 2007/06/29 13:30:57 bertl Exp $ */
#include <stdio.h>
#include "aterm2.h"


   
typedef enum {VDB, TDB}  db_et;
typedef FILE *file_t;     
typedef char *dir_t;

typedef ATerm term_t;
typedef int idx_t;
typedef int32_t elm_t;
typedef struct {
     db_et type;
     } *db_e;

typedef struct {
     FILE *r, *w;
     } channel_r, *channel_t;

typedef struct {
   elm_t lab, smd;
   } act_t;
 

static char deadlockstring[]="#deadlock#";
  
#define DEADLOCK -11

#define PRIOWIDTH 1000

#define NWEIGHTS 10000

#define PROTOCOL 6  /* TCP */

/* #define PROTOCOL 17 UDP */
