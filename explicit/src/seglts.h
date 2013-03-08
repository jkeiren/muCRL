/* $Id: seglts.h,v 1.4 2006/05/17 08:08:42 bertl Exp $ */

#ifndef SEGLTS_H
#define SEGLTS_H



typedef struct {
   char **p;
   int n;
   } pathar_t;

typedef struct seginfo {
	char *info;
	int segment_count;
	int initial_seg;
	int initial_ofs;
	int label_count;
	int label_tau;
        int label_deadlock;
	int top_count;
	int *state_count;
	int **transition_count;
} *seginfo_t;

typedef struct dir_client {
  int n;
  char **src, **dst, **lbl;
  FILE **srcf, **dstf, **lblf;
} *dir_client_t;

typedef struct dir_server {
  int n;
  FILE *TermDB;
  } *dir_server_t;

typedef enum {SLTSsrc, SLTSlbl, SLTSdst} SLTSkind_t; 

extern int SLTSCreateInfo(seginfo_t *info,int segment_count);

extern int SLTSReadInfo(seginfo_t *info,char *name);

extern int SLTSWriteInfo(seginfo_t info, char *name);

extern void SLTSPrintInfo(seginfo_t info, FILE *f);

extern char *SLTSerror();

extern int SLTSWriteServer(dir_server_t s, seginfo_t info, FILE *termdb);

extern FILE *SLTSopen(dir_client_t r, int pos, SLTSkind_t kind);

extern int guess_nsegments(void);

extern int guess_nhosts(int *local);

extern dir_client_t SLTSCreateClient(int segment_count, char *name, int idx);

extern dir_server_t SLTSCreateServer(seginfo_t seginfo, char *name);

extern void CreateRestoreJob(char *outputfile, int nhosts, int argc, char **argv);

extern char *EnvironmentDest(int nhosts, int nsegments, int nskip);
        
extern void patharInit(char *absname);

extern int ForEachDirInHost(int nhosts, int nsegments, int local, int nskip, 
int private, int restore, int output, char *path, EachFile eachFile);
#endif

