/* $Id: dmp2dir.c,v 1.10 2008/04/28 14:14:10 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "string.h"
#include <unistd.h>
#include "param0.h"
#include "utl.h"
#include "rw.h"
#include "seglts.h" 
#include "vector_db.h"
#include "data_io.h"
#include "term_db.h"

#define SRC 0
#define DEST 1

static char  cwd[FNAMESIZE], datadir[FNAMESIZE], dmpdir[FNAMESIZE], adbdir[FNAMESIZE],
dirsegmentname[FNAMESIZE];
static long monitor = 1, ntransitions = 0, nsegments = 0, msegments = 0,
label_deadlock = -1, optimal = 1;
static long buffersize  = 0;
static dir_client_t *client;
static tdb_t adb;
dir_server_t server;
static seginfo_t info;
static FILE **dirsegment;
static char **outputname;

static int CheckSum(elm_t *dest) {
     if (optimal) return dest[0];
     {
     int s=dest[0]+dest[1];
     return s%msegments;
     }
     }
     
static void help() {
    Pr("Usage: dmp2dir [options] <input dmp directory>");
    Pr("Translates an \".dmp\"-directory, which is produced by");
    Pr("instantiators or instantiator1 to an \".dir\" directory");
    Pr("which can be read by the data reduction tools.");
    Pr("The name of the output directory is: \"<input>.dir\" in which");
    Pr("\"<input>\" is first part of the name of <input dmp-directory>:");
    Pr("\"<input>.dmp\"");
    Pr("");
    Pr("The following options can be used");
    Pr("-monitor\t\tdisplays progressing information");
    Pr("-nsegments <number>\tnumber of output segments (default equal to");
    Pr("\t\t\tnumber of input segments)");
    Pr("-bufsize <number>\toutput buffer size");
    }
    
static char *Act2String(int act, ATbool *isQuoted) {
      AFun afun = ATgetAFun(TDBget(adb, act));
      *isQuoted = ATisQuoted(afun);
      return ATgetName(afun);
      }
      
static int RowSum(int r) {
    int i, s=0;
    for (i=0;i<msegments;i++) 
         s+=info->transition_count[r][i];
    return s;  
    }
    
static int ColSum(int c) {
    int i, s=0;
    for (i=0;i<msegments;i++) 
         s+=info->transition_count[i][c];
    return s;  
    } 
           
static int DirWrite(FILE *srcf, FILE *actf, FILE *destf) {
     elm_t src[2], act[2], dest[2];
     int cnt = 0;
     /* Initial state */
      if (!readPair(srcf, src) || !readPair(actf, act) || 
           !readPair(destf, dest)) return -1;
      while (
          FREAD(src, sizeof(int32_t), 2, srcf)==2 &&
          FREAD(act, sizeof(int32_t), 2, actf)==2 &&
          FREAD(dest, sizeof(int32_t), 2, destf)==2
          )
          {
     // fprintf(stderr,"%d =?= %d cnt = %d\n", act[0], label_deadlock, cnt);
          if (src[0]>=0 && src[1]>=0 && act[0]!=label_deadlock) {
            int c_src = CheckSum(src), c_dest = CheckSum(dest);
            act[1] = SRC;
            FWRITE(src, sizeof(int32_t), 2, dirsegment[c_src]);
            FWRITE(act, sizeof(int32_t), 2, dirsegment[c_src]);
            FWRITE(dest, sizeof(int32_t), 2, dirsegment[c_src]);
            act[1] = DEST;
            FWRITE(src, sizeof(int32_t), 2, dirsegment[c_dest]);
            FWRITE(act, sizeof(int32_t), 2, dirsegment[c_dest]);
            FWRITE(dest, sizeof(int32_t), 2, dirsegment[c_dest]);
            info->transition_count[c_src][c_dest]++;
            cnt++;
            }
          }
     return cnt;
     }

static tdb_t ReadActions(void) {
        FILE *f;
        tdb_t tdb;
        strcpy(adbdir, dmpdir);
        strcat(adbdir,"/NODES/adb/file");
        if (!(f = fopen(adbdir, "r"))) {
            perror(adbdir); exit(1);
            };
        tdb = TDBcreate(0, f, NULL);
        return tdb;
        }
        
/* Counting the number of transitions */
static void CountingTransitions(void) {
    int i, j, len0 = strlen(dmpdir);
    for (i=0;i<nsegments;i++) {
        FILE *input;
        for (j=0;j<nsegments;j++) {
        sprintf(dmpdir+len0, "/stepper.%d/src/stepper.%d",  i, j);
        if (!(input=fopen(dmpdir,"r"))) {perror(dmpdir); exit(1);}
        ntransitions += (FileLen(input)/getRecordSize());
        fclose(input);
        }
     }
   printmsg("Number of segments: %d -> %d  Upperbound number of transitions: %ld", 
   nsegments, msegments, ntransitions);
/* End Counting the number of transitions */
   dmpdir[len0]='\0';
   }
           

                  
int main(int argc, char *argv[]) {
    char *lastarg = argv[argc-1], *pt;
    int len0, i, j; 
    elm_t eof[] = {-1,-1};
    term_t tau, deadlock;
    ATinit(argc, argv, (ATerm*) &argc);
    UTLinit(NULL, NULL, NULL, "Dmp2dir");
    tau = ATmake("<str>", "tau");
    deadlock = ATmake("<str>", deadlockstring);
    if (argc<=1 || !strcmp(argv[1],"-help")) {
	    help();
	    exit(0);
	    }
    for (i=1;i<argc-1;i++) {
       if (!strcmp(argv[i],"-monitor")) {
           monitor = 1;
           continue;
           }
       if (!strcmp(argv[i],"-nsegments")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                msegments = strtol(argv[i], &pt, 0);
                optimal = 0;
                if (*pt || msegments<=0) 
                errormsg("Option \"%s %s\" has illegal format", argv[i-1], argv[i]);
                continue;
                }
            errormsg("Option %s needs argument.",argv[i-1]);
            }
       
       if (!strcmp(argv[i],"-buffersize") || !strcmp(argv[i],"-bufsize")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                buffersize = strtol(argv[i], &pt, 0);
                if (*pt || buffersize<=0) 
                errormsg("Option \"%s %s\" has illegal format", 
                      argv[i-1], argv[i]);
                sprintf(cwd, "MCRL_BUFSIZE=%s", argv[i]);
                putenv(strdup(cwd));
                continue;
                }
            errormsg("Option %s needs argument.",argv[i-1]);
            }
       }
    if (optimal==1) {
        sprintf(cwd, "MCRL_OPTIMAL=1");
        putenv(strdup(cwd)); 
        printmsg("Memory optimizing mode is used");
        }
    strcpy(datadir, lastarg);
    if (!strchr(datadir,'/')) {      
       GetCwd(cwd, FNAMESIZE);
       strcat(cwd,"/");
       strcat(cwd, datadir);
       strcpy(datadir, cwd);
       }
    if (strrchr(datadir,'.') && !strcmp(strrchr(datadir,'.'),".dmp"))
       *(strrchr(datadir,'.'))='\0';      
    strcat(datadir,".dmp"); 
    if (!IsADir(datadir)) 
          errormsg("Input Directory \"%s\"", datadir);    
    patharInit(datadir);
    strcpy(dmpdir, datadir);
    adb = ReadActions();
    label_deadlock=TDBput(adb, deadlock, NULL);
    strcat(dmpdir,"/STEPPERS"); 
    *(strrchr(datadir,'.'))='\0';
    strcat(datadir,".dir");
    if (CreateEmptyDir(datadir,DELETE_ALL)<0) 
                   errormsg("Cannot create %s", datadir);
    sprintf(dirsegmentname, "PATH=.:%s;%s ", LIBEXECDIR, "dirsegment"); 
    len0 = strlen(dirsegmentname);
    nsegments = guess_nsegments();
    if (msegments == 0) msegments = nsegments;
    dirsegment = calloc(msegments, sizeof(FILE*));
    outputname = calloc(msegments, sizeof(char*));
    for (i=0;i<msegments;i++) { 
         sprintf(cwd,"%s/%snstates.%d", 
         getenv("TMPDIR")?getenv("TMPDIR"):"/tmp", getenv("USER"), i);
         outputname[i] = strdup(cwd);
         sprintf(dirsegmentname+len0,"%d %d %s %s", msegments, i, datadir, outputname[i]);
         if (!(dirsegment[i]=Popen(dirsegmentname,"w"))) 
            errormsg("Cannot start process %s", dirsegmentname);
         // flockfile(dirsegment[i]);
         } 
    client = (dir_client_t*) malloc(nsegments*sizeof(struct dir_client));
    SLTSCreateInfo(&info, msegments);
    CountingTransitions();
    len0 = strlen(dmpdir);
    for (i=0;i<nsegments;i++) {
         int cnt = 0;
         for (j=0;j<nsegments;j++) {
            FILE *actf, *destf, *srcf;
            sprintf(dmpdir+len0, "/stepper.%d/src/stepper.%d", j, i);
            if (!(srcf=fopen(dmpdir,"r"))) {perror(dmpdir); exit(1);}
            // flockfile(srcf);
            sprintf(dmpdir+len0, "/stepper.%d/act/stepper.%d", i, j);
            if (!(actf=fopen(dmpdir,"r"))) {perror(dmpdir); exit(1);}
            // flockfile(actf);
            sprintf(dmpdir+len0, "/stepper.%d/dest/stepper.%d", i, j);
            if (!(destf=fopen(dmpdir,"r"))) {perror(dmpdir); exit(1);}
            // flockfile(destf);
            cnt += DirWrite(srcf, actf, destf);
            // funlockfile(srcf);funlockfile(destf);funlockfile(actf);
            fclose(srcf); fclose(actf);fclose(destf);
            }
       if (monitor) 
            printmsg("Read in segment: %d  added transitions: %d",
            i, cnt);
       }
    for (i=0;i<msegments;i++) {
       writePair(dirsegment[i], eof);
       writePair(dirsegment[i], eof);
       writePair(dirsegment[i], eof);
       }
     for (i=0;i<msegments;i++) pclose(dirsegment[i]);
     for (i=0;i<msegments;i++) {
       FILE *f = NULL;
       if (!(f = fopen(outputname[i], "r"))) {
            perror(outputname[i]); exit(1);
            };
       fscanf(f,"%d", info->state_count+i);
       fclose(f);
       }
     info->label_deadlock= label_deadlock;
     ATwarning("deadlock: %d %t\n", label_deadlock, deadlock);
     info->label_tau= TDBput(adb, tau, NULL);
     ATwarning("tau: %d %t\n",info->label_tau , tau);
     info->label_count = TDBgetCount(adb);
     info->info="instantiator(1/s) output";
     info->top_count  = 1;
     server = SLTSCreateServer(info, datadir);
     for (i=0;i<info->label_count;i++) {  
            ATbool isQuoted;
            char *name =  Act2String(i, &isQuoted);
            fprintf(server->TermDB, "%s%s%s\n", isQuoted?"\"":"",
			    name,  isQuoted?"\"":"");
            }
     SLTSPrintInfo(info, stdout);
     exit(0);
     }
