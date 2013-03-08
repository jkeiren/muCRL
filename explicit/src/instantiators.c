/* $Id: instantiators.c,v 1.32 2007/11/22 12:39:46 bertl Exp $ */

#define _GNU_SOURCE
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "string.h"
#include <unistd.h>
#include "param0.h"
#include "utl.h"
#include "rw.h"
#include "step.h"
#include "discover.h" 
#include "seglts.h"            
#include "read.h"

static  int rewr = 0, norewr = 0, restore  = 0 , clean = 1, nsegments = 0,
private = 0, local = 0, verbose = 0, nhosts = 0, nskip = -1,
global = 0, output = 1, priority_f = 0, pterm = 0, detailed = 0,
jid;
static unsigned int spectrum = NWEIGHTS;
   
static char buf[PRIOWIDTH+50], outputfile[MCRLsize], absname[MCRLsize];
static char *pattern = NULL, *reject = NULL, *sselect = NULL, *spriority = NULL,
*action_deadlock=NULL; 
static void help() {
    Pr("Usage: instantiators [options] <input file>");
    Pr("The names of the hosts, which run the instantiators,");
    Pr("is read from file named in $PBS_NODEFILE, default ~/hosts");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\t\tyields this message");
    Pr("-version:\t\tget the version number of this release");
    Pr("");
    Pr("Output Options:");
    Pr("-action <regexp>:\tlist actions which satisfy regular expression");
    Pr("-deadlock:\t\tlist deadlocks");
    Pr("-all:\t\t\tlist all mentioned deadlocks and actions");
    Pr("-trace:\t\t\tlist also traces to mentioned actions and deadlocks");
    Pr("-no-lts:\t\tno labeled transition system will be written down");
   /* Pr("-server <host name>:\t\thost which runs the servers"); */
    Pr("");
    Pr("General options:");
    Pr("-nsegments <number>:\tnumber of segments");
    Pr("\t\t\tequal to number of instantiators");
    Pr("-norewr:\t\tno rewrite system on <input file>.so will be created");
    Pr("-port <number>:\t\tport number which the data base server must use");
    Pr("-local:\t\t\tone host runs all clients and servers");
    Pr("-timer:\t\t\ttime registration after each level");
    Pr("-progress <number>:\tprogress message after each <number> explored states");
    Pr("-private:\t\tlocal disks will be used");
    Pr("-db-local:\t\tall databases run on the same machine as the manager");
    Pr("-nskip <number>:\tskipped first lines of file containing host names");
    Pr("-bufsize <number>:\tthe size of the IO buffers. Choose a large <number>");
    Pr("-delay <number>:\tnumber of seconds waiting before the clients start");
    Pr("-tick:\t\t\tpostpone the \"tick\" transitions until no other transitions are");
    Pr("\t\t\tpossible.");
    Pr("-priority <regexp>:\tif transitions with labels satisfying");
    Pr("\t\t\t<regexp> are enabled, take only these transitions.");
    Pr("\t\t\tTake all transitions otherwise.");
    Pr("-detailed-option <term>:sort in each level the states such that");
    Pr("\t\t\tmCRL <expr> of type \"Nat\" or \"Pos\" increases");
    Pr("-detailed-expr:\t\tsort in each level the states such that");
    Pr("\t\t\t<expr> written in the first input line increases");
    Pr("\t\t\tThe value of <expr> must be in the range [%d,%d]",0, spectrum);
    Pr("-detailed-term:\t\tsort in each level the states such that");
    Pr("\t\t\t<term> written in the first input line increases");
    Pr("\t\t\tThe value of <term> must be in the range [%d,%d]",0, spectrum);
    Pr("-beam-width <number>:\tthe maximum <number> of states in a level");
    Pr("-beam-width+:\t\tround up - each node gets equal number of states");
    Pr("-beam-width++:\t\tround up - no truncation in states of equal weight");
    Pr("");
    Pr("-spectrum <number>:\t[0,number), the range of the detailed terms");
    Pr("-select <action>:\tfor each explored state create a partition of outgoing ");
    Pr("\t\t\ttransitions defined by the first argument of their actions.");
    Pr("\t\t\tIf there is a class having only <action> transitions,");
    Pr("\t\t\tselect the transitions in this class. Select all, otherwise.");
    Pr("Stepper options:");
    DIShelpMCRL();
    }
    

static void version(void)
    {
    char buf[100];
    /*
    P("$Id: instantiators.c,v 1.32 2007/11/22 12:39:46 bertl Exp $");
    */
    sprintf(buf,"instantiators: version %s",VERSION);
    Pr(buf);
    }

static int eachFile(char *name) {
    FILE *f = fopen(name, "r");
    if (!f) {
        printmsg("File %s cannot be opened", name);
        return -1;
        }
    printmsg("Restore: file \"%s\" contains %d records", name, 
    FileLen(f)/getRecordSize());
    fclose(f);
    return 0;
    }
    
static int eachDir(char *name) {
     int trunc = strlen(name), n;
     name = strcat(name,"/src");
     n = ForEachFileInDir(name, verbose?eachFile:NULL);
     if (n<0) errormsg("Cannot open %s", name);
     if (nsegments==0)  {
          nsegments = n;
          }
     else if (nsegments != n) 
        errormsg(
        "Corrupted restore dir %s: number of segments %d (expected %d)",
        name, n, nsegments); 
     name[trunc]='\0';  
     return 0;
     }

static char* argv2String(char **argv, int argc) {
     int i, cnt = 0;
     char  *r;
     for (i=0;i<argc;i++) cnt += (argv[i][0]?strlen(argv[i]):strlen(argv[i]+1));
     r =  (char*) malloc((cnt+argc+22)*sizeof(char));
     strcpy(r, "MCRL_ARGS=");
     for (i=0;i<argc;
       sprintf(r+strlen(r), "%s%s",argv[i][0]?"":".", argv[i]+
       (argv[i][0]?0:1)), i++)
     if (i>0) strcat(r," ");
     return r;
     }
     
static void Prepend2Path(void) {
     char *path = getenv("PATH");
     char *b = malloc(strlen(path)+256);
     sprintf(b,"PATH=.:%s:%s", EXECDIR, path);
     putenv(b);
     }

          
static char *NewString(const char *format, ...) {
   int n = strlen(format);
   char *r = NULL;
   const char *t;
   va_list ap;
   va_start(ap, format);
   for (t=format;(t=strchr(t,'%'));n+=strlen(va_arg(ap, char *)),t++);
   va_end(ap);
   va_start(ap, format);
   r = (char*) malloc((n+1)*sizeof(char));
   vsprintf(r, format, ap);
   va_end(ap);
   return r;
   }
       

static void MakeParameterEnvironment() {
    ATermList pars;
    char prefix[] = "MCRL_PARS=\"";
    int  len=strlen(prefix);
    for (pars = MCRLgetListOfPars();!ATisEmpty(pars);pars=ATgetNext(pars)) {
        ATerm par = ATgetFirst(pars);
        len += (strlen(ATgetName(ATgetAFun(ATgetArgument((ATermAppl) par,0))))
             +strlen(ATgetName(ATgetAFun(ATgetArgument((ATermAppl) par ,1))))+1);
        }
    len++;
    {char *var = calloc(len,sizeof(char));
    var=strncat(var,prefix, len);
    for (pars = MCRLgetListOfPars();!ATisEmpty(pars);
      pars=ATgetNext(pars), (var=strncat(var, ATisEmpty(pars)?"\"":" ", len))) {
      ATerm par = ATgetFirst(pars);
      var = 
      strncat(var, ATgetName(ATgetAFun(ATgetArgument((ATermAppl) par,0))), len);
      var = 
      strncat(var, ATgetName(ATgetAFun(ATgetArgument((ATermAppl) par ,1))), len);
    }
    /* ATwarning("MakeParametersEnvironment: %s", var); */
    putenv(strdup(var));
    }
    }
 
static char *AddPattern(char *pattern, char *name) {    
     if (!pattern) pattern = NewString("%s", name);
     else {
          char *aux =  NewString("%s|%s", pattern, name);
          free(pattern);
          pattern = aux;
          }
     return pattern;
     } 

#ifdef MCRL
static ATerm ParseTerm(char *e) {
      ATerm priority = MCRLparse(e);
      if (priority) { 
      if (MCRLgetSort(priority)) {
         char *s = ATgetName(MCRLgetSort(priority));
         if (strcmp(s, "Nat") && strcmp(s, "Pos")) 
             ATerror("Priority expression (sort %s) must have sort Nat or Pos\n",
                    s);   
         } else ATerror("\n");
         } 
      else {
           fprintf(stderr," in priority expression\n");exit(EXIT_FAILURE);
           }
      return priority;  
      }
#endif

static char *ReadInput(FILE *f) {
      char *b;
      int c;
      size_t n;
      bfile_t *pt =  bopen_memstream(0, &b, &n);
      while ((c=fgetc(f))!=EOF) {
         bfputc(c, pt);
         }
      bfputc('\0', pt);
      bfclose(pt);
      return b;
      }

static void PrintContactLine() {
     char b[200];
     FILE *f = fopen("cnct", "w");
     sprintf(b, "contact %d %s", jid, getenv("MCRL_MGRDHOST"));
     printmsg("Connection to this job by entering \"%s\"\n", b); 
     if (f) {
        fputs(b, f);
        fclose(f);
        }
     }
         	                                                                   
int main(int argc, char *argv[]) {
    if (argc==1) {help();exit(0);}
    {
    int i, j = 0;
    char *fname = strdup(argv[argc-1]), *ptr,  *args, *priority_l = NULL; 
    char *carg[]={"mgrstart", NULL, NULL};
    char **newargv = (char**) calloc(argc+4, sizeof(char*)); 
    ATerm priority = NULL;
    UTLinit(NULL, NULL, NULL, "Instantiators");
    jid = getenv("PBS_JOBID")?atoi(getenv("PBS_JOBID")):getpid();
    sprintf(buf,"MCRL_JID=%d.jid",jid);
    putenv(strdup(buf));
    newargv[j++] = argv[0];
    if (fname[0]=='~') 
        errormsg("'~' is not permitted as first character of \"%s\"", fname);
    if ((ptr=strrchr(fname,'.')) && !strcmp(ptr,".tbf")) *ptr='\0';
    if (fname[0]=='/') sprintf(absname,"%s", fname);
    else  {
        if (!GetCwd(absname, 256)) errormsg("Cannot return absolute path");
        sprintf(absname+strlen(absname),"/%s", fname);
        }
    for (i=0;i<argc;i++) 
       if (!strcmp(argv[i],"-norewr") || !strcmp(argv[i],"-no-rewr")
         /* || !strcmp(argv[i],"-restore") */ ) norewr = 1;
    for (i=0;i<argc;i++) 
       if (!strcmp(argv[i],"-alt")) {rewr = 1;norewr=0;}
    if (!rewr) {
      newargv[j++] = "-alt";
      newargv[j++] = "rw";
      }
    if (norewr) {
      newargv[j++] = "-read-so";
      newargv[j++] = strdup(absname);
      }
    if (!rewr && !norewr) {
      newargv[j++] = "-read-so";
      newargv[j++] = strdup(absname);
      }     
    ATinit(argc, argv, (ATerm*) &argc); 
    if (!getenv("MCRL_DEADLOCKSTRING")) {
       sprintf(buf,"MCRL_DEADLOCKSTRING=%s", deadlockstring);
       putenv(strdup(buf));
       }
    if (!strcmp(argv[1],"-help")) {
	    help();
	    exit(0);
	    }
	if (!strcmp(argv[1],"-version")) {
	    version();
	    exit(0);
	    }
    for (i=1;i<argc; i++) {
        /*
        if (!strcmp(argv[i],"-restore")) {
            restore = 1; clean = 0; 
            putenv("MCRL_RESTORE=1");
	    continue;
	    }
        */
        if (!strcmp(argv[i],"-timer")) {
            putenv("MCRL_TIMER=1");
	    continue;
	    }
        if (!strcmp(argv[i],"-private")) {
            private = 1;
	    continue;
	    }
       if (!strcmp(argv[i],"-local")) {
            putenv("MCRL_LOCAL=1");
            local = 1;
	    continue;
	    }
       if (!strcmp(argv[i],"-verbose")) {
            putenv("MCRL_VERBOSE=1");
            verbose = 1;
	    continue;
	    }
       if (!strcmp(argv[i],"-log")) {
            putenv("MCRL_LOG=1");
	    continue;
	    }
       if (!strcmp(argv[i],"-global") || !strcmp(argv[i],"-db-local")) {
            putenv("MCRL_GLOBAL=1");
            global = 1;
	    continue;
	    }
       if (!strcmp(argv[i],"-text")) {
            putenv("MCRL_TEXT=1");
	    continue;
	    }
        if (!strcmp(argv[i],"-memory-model")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                sprintf(buf,"MCRL_MEMORY=%s", argv[i]);
                putenv(strdup(buf));
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
        if (!strcmp(argv[i],"-old")) {
            putenv("MCRL_OLD=1");
	    continue;
	    }        
       if (!strcmp(argv[i],"-no-lts")) {
            output = 0;
	    continue;
	    }
       if (!strcmp(argv[i],"-mgrd-host")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                sprintf(buf,"MCRL_MGRDHOST=%s", argv[i]);
                putenv(strdup(buf));
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
       if (!strncmp(argv[i], "-detailed-term", 14)) {
            if (!pterm) {
               int d = strlen(argv[i])-13;
               if (d>detailed) detailed = d;
               priority_f = 1;
               pterm = 1;
               }
             continue;
             }
       if (!strncmp(argv[i],"-detailed-option", 16)) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
               if (!pterm) {
                   int d = strlen(argv[i])-15;
                   if (d>detailed) detailed = d;
                   priority_l = argv[i];
                   pterm = 1;
                   }
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
       if (!strncmp(argv[i], "-detailed-expr", 14)) {
            if (!pterm) {
              int d = strlen(argv[i])-13;
              if (d>detailed) detailed = d;
              priority_f = 1;
              pterm  = 2;
              }
            continue;
            }
       if (!strncmp(argv[i],  "-detailed-input", 15)) {
            if (!pterm) {
              priority_f = 1;
              detailed = strlen(argv[i])-14;
              pterm  = 2;
              }
            continue;
            }
       if (!strcmp(argv[i],"-norewr") || !strcmp(argv[i],"-no-rewr")) continue;
       if (!strcmp(argv[i],"-mgrd-port")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                sprintf(buf,"MCRL_MGRDPORT=%s", argv[i]);
                putenv(strdup(buf));
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
       if (!strcmp(argv[i],"-port")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                sprintf(buf,"MCRL_MGRPORT=%s", argv[i]);
                putenv(strdup(buf));
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
       if (!strcmp(argv[i],"-progress")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *endptr = NULL;
                int progress = strtol(argv[i],&endptr,10);
                if (progress<0) errormsg("-progress %d is negative number");
                sprintf(buf,"MCRL_PROGRESS=%s", argv[i]);
                if (*endptr != '\0') errormsg("Number expected after \"-progress\"");
                putenv(strdup(buf));
                }
            else
                errormsg("Integer expected after %s\n",argv[i-1]);
            continue;
            } 
      if (!strcmp(argv[i],"-nskip")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *endptr = NULL;
                nskip = strtol(argv[i],&endptr,10);
                if (*endptr != '\0') errormsg("Number expected after \"-nskip\"");
                sprintf(buf, "NSKIP=%d",nskip);
                putenv(strdup(buf));
                }
            else
                errormsg("Integer expected after %s\n",argv[i-1]);
            continue;
            }
      if (!strcmp(argv[i],"-sleep")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *endptr = NULL;
                int sleep = strtol(argv[i],&endptr,10);
                if (*endptr != '\0') errormsg("Number expected after \"%s\"",
                    argv[i]);
                sprintf(buf, "MCRL_SLEEP=%d",sleep);
                putenv(strdup(buf));
                }
            else
                errormsg("Integer expected after %s\n",argv[i-1]);
            continue;
            }
      if (!strcmp(argv[i],"-spectrum")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *endptr = NULL;
                long n = strtol(argv[i],&endptr,10);
                if (*endptr != '\0') errormsg("Number expected after \"-spectrum\"");
                if (n<1) errormsg("ub of frek. segment [0,ub] must be >=1"); 
                sprintf(buf, "MCRL_SPECTRUM=%d",n);
                putenv(strdup(buf));
                }
            else
                errormsg("Integer expected after %s\n",argv[i-1]);
            continue;
            }
       if (!strncmp(argv[i],"-beam-width", 11) || !strncmp(argv[i],"-beam_width", 11)) {
            int d = strlen(argv[i])-10;
            if (d>detailed) detailed = d;
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *endptr = NULL;
                long beamwidth= strtol(argv[i][0]=='~'?argv[i]+1:argv[i],&endptr,10);
                if (*endptr != '\0') 
                errormsg("Number expected after \"-beam_width\"");
                sprintf(buf, "MCRL_BEAMWIDTH=%s",argv[i]);
                putenv(strdup(buf));
                }
            else
                errormsg("Integer expected after %s\n",argv[i-1]);
            continue;
            }              
        if (!strcmp(argv[i],"-nsegments")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                nsegments = atoi(argv[i]);
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
         if (!strcmp(argv[i],"-tick")) {putenv("MCRL_TICK=1"); continue;}
         if (!strcmp(argv[i],"-buffersize") || !strcmp(argv[i],"-bufsize")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                sprintf(buf, "MCRL_BUFSIZE=%s",argv[i]);
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
        // errormsg("Illegal option  %s", argv[i]);
        if (!strcmp(argv[i],"-action")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
	        pattern = AddPattern(pattern, argv[i]);
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
        if (!strcmp(argv[i],"-action-deadlock")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
	        action_deadlock = AddPattern(action_deadlock, argv[i]);
                putenv("MCRL_TRACE=1");
                putenv("MCRL_ALL=1");
                putenv("MCRL_DEADLOCK=1");
	        pattern = AddPattern(pattern, getenv("MCRL_DEADLOCKSTRING"));
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
        if (!strcmp(argv[i],"-reject")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
	        reject = AddPattern(reject, argv[i]);
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
        if (!strcmp(argv[i],"-select")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
	        sselect = AddPattern(sselect, argv[i]);
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
        if (!strcmp(argv[i],"-priority")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
	        spriority = AddPattern(spriority, argv[i]);
                continue;
                }
            errormsg("Option %s needs argument.\n",argv[i-1]);
            }
        if (!strcmp(argv[i],"-trace")) {putenv("MCRL_TRACE=1");continue;}
        if (!strcmp(argv[i],"-stop")) {putenv("MCRL_STOP=1");continue;}
        if (!strcmp(argv[i],"-all")) {putenv("MCRL_ALL=1");continue;}
        if (!strcmp(argv[i],"-deadlock")) {
	      putenv("MCRL_DEADLOCK=1");
	      pattern = AddPattern(pattern, getenv("MCRL_DEADLOCKSTRING"));
	      continue;
	      }
        j=MCRLcopyOption(newargv, argv, argc, i, j);
	}
    if (!getenv("MCRL_MGRDHOST")) {
    	 char thisHost[100];
    	 gethostname(thisHost, 100);
         /*
         sprintf(buf,"MCRL_MGRDHOST=%s", local?thisHost:
         (getenv("PBS_O_HOST")?getenv("PBS_O_HOST"):thisHost));
         */
         sprintf(buf,"MCRL_MGRDHOST=%s", thisHost);
         putenv(strdup(buf)); 
         }
    if (!getenv("MCRL_MEMORY")) {
         sprintf(buf,"MCRL_MEMORY=%s", "global-tree");
         putenv(strdup(buf)); 
         }
    else if (strcmp(getenv("MCRL_MEMORY"),"local-tree") &&
         strcmp(getenv("MCRL_MEMORY"),"vector") && 
	 strcmp(getenv("MCRL_MEMORY"),"global-tree")) 
	    errormsg("Illegal memory model option: %s",getenv("MCRL_MEMORY"));
    if (!getenv("MCRL_MGRDPORT")) {
         PrintContactLine();
         sprintf(buf,"MCRL_MGRDPORT=%d",(jid%10000+30000));
         putenv(strdup(buf));
         }
    if (!getenv("MCRL_MGRPORT")) {
         sprintf(buf,"MCRL_MGRPORT=%d", 1970);
         putenv(strdup(buf));
         }
    if (!getenv("MCRL_SPECTRUM")) {
         sprintf(buf,"MCRL_SPECTRUM=%d", spectrum);
         putenv(strdup(buf));
         }
    if (getenv("MCRL_RESTORE") && !getenv("MCRL_OLD")) {
        errormsg("Not possible to restore from new dumped format");
        }
    carg[1] = strdup(absname);
    strcat(absname, ".dmp");
    if (output==1) putenv("MCRL_OUTPUT=1");
    else if (restore==1) {
         printmsg("Flag -restore ignored");
         restore = 0;unsetenv("MCRL_RESTORE");
         }
    if (restore == 1 && !IsADir(absname)) {
        errorreset();
        printmsg("Directory: %s not found; flag -restore ignored", absname);
        restore = 0;unsetenv("MCRL_RESTORE");
        }
    patharInit(absname);
    if (nsegments==0 && restore==1) nsegments = guess_nsegments();
    if (local==0) {
       nhosts = guess_nhosts(&local);
       if (nskip<0) nskip = (nhosts>7?1:0);
       if (nsegments==0) nsegments = nhosts - nskip;
       if (nsegments==0) {nsegments = 2; nskip = 0;}
       if (nhosts>(nsegments+nskip))  nhosts = nsegments+nskip;
       }
      else {if (nsegments==0) {nhosts = nsegments = 2; nskip = 0;}
            else {nhosts =nsegments; nskip=0;}
	   }
    if (nhosts==0) nhosts = nsegments;
    MCRLsetOutputFile(outputfile);
    if (pattern) { 
         sprintf(buf, "MCRL_ACTION=%s", pattern);
         putenv(strdup(buf));
         } 
    if (action_deadlock) { 
         sprintf(buf, "MCRL_ACTION_DEADLOCK=%s", action_deadlock);
         putenv(strdup(buf));
         } 
    if (reject) { 
         sprintf(buf, "MCRL_REJECT=%s", reject);
         if (getenv("MCRL_SELECT")) errormsg("No both -reject and -select option permitted");
         putenv(strdup(buf));
         } 
    if (sselect) { 
         sprintf(buf, "MCRL_SELECT=%s", sselect);
         if (getenv("MCRL_REJECT")) errormsg("No both -reject and -select option permitted");
         putenv(strdup(buf));
         }
    if (spriority) { 
         sprintf(buf, "MCRL_FIRST=%s", spriority);
         putenv(strdup(buf));
         }  
    args = argv2String(newargv, j);
    if (putenv(args)<0) errormsg("putenv");         
    DISsetArgumentsMCRL(NULL, &j, &newargv, NULL);
#ifdef MCRL
    if (!rewr && !norewr) {
        int i;
	for (i=0;i<j;i++) {
	     if (!strcmp(newargv[i],"-read-so")) newargv[i]="-write-so";
             }
        if (!MCRLinitRW(j, newargv)) exit(1);
	}
    else  {
       RWsetArguments(&j, &newargv);
       if (!MCRLinitOnly(j, newargv)) exit(1);
       } 
    if (MCRLgetNumberOfPars()>1) {
       sprintf(buf,"MCRL_NPARS=%d",  MCRLgetNumberOfPars());
       putenv(strdup(buf));
       }
    else {
       errorreset();
       errormsg("Number of process parameters must be greater than 1");
       }
    MCRLdeclareVars(MCRLgetListOfPars());
    if (priority_f) {
            if (pterm==2) {
                priority = ParseFile(stdin);
                if (!priority) { 
                    fprintf(stderr,"\n"); 
                    errormsg("Error in input following option -detailed-input");
                    }
                 }
          if (pterm==1) {
             char *e = ReadInput(stdin);
             priority = ParseTerm(e);
             if (!priority) { 
                fprintf(stderr,"\n"); 
                errormsg("Error in input following option -detailed-input");
                }
             }
          } 
    else
        if (priority_l) priority = ParseTerm(priority_l);
    if (priority) {
       sprintf(buf,"MCRL_PRIORITY=%s", ATwriteToString(priority));
       // ATwarning("Parsed: %s\n",buf);
       putenv(strdup(buf));
       sprintf(buf,"MCRL_DETAILED=%d", detailed);
       putenv(strdup(buf));
       }
#endif
    MakeParameterEnvironment();
    putenv(strdup(buf));
    if (clean) {
           if (restore == 0 && output == 1)  {
                if (CreateEmptyDir(absname, DELETE_ALL)==0)
                    printmsg("Directory %s is emptied", absname);
                else
                    errormsg("At Creating empty directory %s", absname);
                }
           else  {
                 if (CreateEmptyDir(absname, DELETE_NONE)==0) {
                    if (output==0) printmsg("Directory %s is loaded", absname);
              else printmsg("No labeled transition system  will be written");
                    }
                 else
                 errormsg("At loading directory %s\n", absname);
                 }
            }
    if (nsegments==0) errormsg("Number of segments==0"); 
    if (ForEachDirInHost(nhosts, nsegments, local, nskip, private, restore, 
    output, buf, eachDir)<0) exit(1);
    sprintf(buf,"MCRL_NSEGMENTS=%d", nsegments);
    putenv(strdup(buf));
    putenv(EnvironmentDest(nhosts, nsegments, nskip));
    if (restore==0 && local==0 && output==1) 
          CreateRestoreJob(outputfile, nhosts, argc, argv);
    Prepend2Path();
    if (ExecVp(carg[0], carg)==-1) {
        perror(carg[0]);
        exit(EXIT_FAILURE);
        };
    }
    exit(EXIT_SUCCESS);
    }
