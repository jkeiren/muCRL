/* $Id: dirsegment.c,v 1.3 2007/06/29 13:30:57 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "string.h"
#include <unistd.h>
#include "param0.h"
#include "utl.h"
#include "rw.h"
#include "step.h"
#include "seglts.h" 
#include "vector_db.h"
#include "data_io.h"
#include <assert.h>
#define SRC 0
#define DEST 1

static int segment, msegments, buffersize = 0;
static vdb_t vdb = NULL;

static int CheckSum(elm_t *dest) {
     if (!vdb) return dest[0];
     {
     int s=dest[0]+dest[1];
     /* fprintf(stderr,"%d %d s=%d mseg %d %d\n", dest[0], dest[1], s, msegments,
     s%msegments); */
     return s%msegments;
     }
     }
     
int main(int argc, char *argv[]) {
    char *statename = argv[4], *dirname = argv[3];
    elm_t src[2], act[2], dest[2];
    idx_t n = 0, ofs = 1, m = -1; 
    dir_client_t client;
    FILE *f;
    UTLinit(NULL, NULL, NULL, "Dirsegment");
    segment = atoi(argv[2]), msegments = atoi(argv[1]);
    client = SLTSCreateClient(msegments, dirname, segment);
    if (!getenv("MCRL_OPTIMAL")) {
       vdb = VDBcreate(0, 2,  NULL, NULL, NULL, NULL, NULL, NULL, NULL);
       }
    if (getenv("MCRL_BUFSIZE")) {
       int i;
       buffersize = atoi(getenv("MCRL_BUFSIZE"));
       // fprintf(stderr, "Buffer size: %d\n", buffersize);
       for (i=0;i<msegments;i++) {
          char *bb;
          if (!(bb=malloc(buffersize))) 
                       errormsg("IO buffer: size %d", buffersize);
          setbuffer(client->srcf[i],bb, buffersize);
          if (!(bb=malloc(buffersize))) 
                       errormsg("IO buffer: size %d", buffersize);
          setbuffer(client->lblf[i], bb, buffersize);
          if (!(bb=malloc(buffersize))) 
                       errormsg("IO buffer: size %d", buffersize);
          setbuffer(client->dstf[i], bb, buffersize);
          }
     }
     while (
          FREAD(src, sizeof(int32_t), 2, stdin)==2 &&
          FREAD(act, sizeof(int32_t), 2, stdin)==2 &&
          FREAD(dest, sizeof(int32_t), 2, stdin)==2
          ) {
         if (src[0]<0)  break;
         if (act[1]==DEST) { 
             int c_src = CheckSum(src);
             n = (vdb?VDBput(vdb, dest,  NULL):dest[1]-ofs);
             assert(n>=0);
             fwrite32(client->dstf[c_src],n);
             fwrite32(client->lblf[c_src],act[0]);
             if (n>m) m = n;
             }
         if (act[1]==SRC) {
             int c_dest = CheckSum(dest);
             n = (vdb?VDBput(vdb, src,  NULL):src[1]-ofs);
             assert(n>=0);
             fwrite32(client->srcf[c_dest],n);
             if (n>m) m = n;
             }    
         }
     f = fopen(statename,"w"); 
     fprintf(f,"%d\n", vdb?VDBgetCount(vdb):m+1); 
     exit(0);
     }
