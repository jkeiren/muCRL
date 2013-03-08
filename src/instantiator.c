
/* $Id: instantiator.c,v 1.10 2007/02/19 16:01:38 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdio.h>
#include <limits.h>
#include "lts.h"
#include "rw.h"
#include "svc.h"
#include "svcerrno.h"
#include <string.h>
#include <errno.h>
#ifdef DYNLINK
#include <dlfcn.h>
#endif
typedef void (*INIT)(void);
typedef void (*FINAL)(void);
typedef void (*AFTERSTEP) (int state, int n);

typedef struct {
  INIT init;
  LTScallback instep;
  AFTERSTEP afterstep;
  FINAL final;
  } TASK;
   
typedef struct {
   ATerm *action;
   int *from;
   int nr;
   int *actid;
} BACK;

static TASK *task = NULL;

static char *who = "Instantiator", cmd[MCRLsize];
static ATbool stop = ATfalse; /* Stop trace searching if all traces are found */
static char *targets = NULL;
#ifdef DYNLINK
static char *userFile = NULL;
static void *handle = NULL;
typedef void (*USEROPEN) (int root, char *filename);
typedef void (*USERCLOSE) (int states, int transitions);
typedef void (*USERWRITETRANS) (int src, ATerm label, int dest);
typedef void (*USERWRITESTATE) (int src, int count);

static USEROPEN UserOpen = NULL;
static USERCLOSE UserClose = NULL;
static USERWRITETRANS UserWriteTrans = NULL;
static USERWRITESTATE UserWriteState = NULL;
#endif

static FILE  *output = NULL, *invariant = NULL;
static ATermList  actions = NULL;

#define P(msg)  fprintf(stderr,"%s\n",msg)

static char outputfile[MCRLsize];

static BACK back = {NULL,NULL, 0};

static unsigned int explored = 0, visited = 0, transitions = 0, 
                    max_explored = ULONG_MAX, level = 0; 
static SVCbool svc_num = 0;
static SVCfile svcFile[1];
static SVCparameterIndex parameterIndex = 0;
static int actid = 0;

static ATbool monitor = ATfalse, cadp = ATfalse,  verbose = ATfalse,
              explore = ATfalse, reduce = ATfalse;

static void helpmsg(ATbool all) 
    {  
    Pr("Usage: instantiator [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\t\tyields this message");
    Pr("-help-all:\t\tyields all help information");
    Pr("-version:\t\tgets the version number of this release");
    Pr("-max <number>:\t\t<number>*1000 is the upperbound of the number of states");
    Pr("\t\t\twhich will be explored");
    Pr("-max-enum <number>:\t<number> is the upperbound of help variables");
    Pr("\t\t\tused during enumeration");
    Pr("-reduce:\t\tthe LPE which is the same as the original LPE except that");
    Pr("\t\t\tonly the summands used during state space generation are present");
    Pr("\t\t\tis written on stdout");
    Pr("-i:\t\t\ttau replaced by i (Needed for CADP)");
    Pr("-deadlock:\t\twrites an action trace to each deadlock state in text file");
    Pr("\t\t\t\"<inputname>.trc/<n>\"and writes report of this in .dlk file");
    Pr("\t\t\tThese files can be loaded in the simulator.");
    Pr("-trace <action>[,<action>]*");
    Pr("\t\t\twrites one action trace to each action in the list of actions");
    Pr("\t\t\tin text file \"<inputname>.trc/<actionname>\". These files");
    Pr("\t\t\tcan be loaded in the simulator.");
    Pr("-traces <action>[,<action>]*");
    Pr("\t\t\tsee -trace. However more traces per action will be written.");
    Pr("-o <filename>:\t\twrites output to <filename>.<ext> in which <ext>");
    Pr("\t\t\tis determined by a chosen option (default:<ext> equal to \"aut\")");
    Pr("-monitor:\t\tprints progressing information during run");
    Pr("-explore:\t\tlike -monitor. In addition encountered deadlocks will be printed.");
    Pr("-:\t\t\twalks through the state graph. However no transition");
    Pr("\t\t\tsystem on file is generated.");
    Pr("-check:\t\t\tlike -. In addition type correctness of transition system will be checked");
    Pr("-aut:\t\t\twrites transition system in .aut format (default)");
#ifdef SVC 
    Pr("-svc-term:\t\twrites transition system in SVC format");
    Pr("-svc-num:\t\tsee -svc-term, however states are represented by numbers");
    Pr("\t\t\t(instead of statevectors).");
#endif
    Pr("-user <filename>.so:\tlinks user defined callback functions to the instantiator.");
    Pr("\t\t\tThese C-functions must be defined in <filename>.c .");
    Pr("\t\t\tSee the example in labelfreq.c .");
    Pr("-invariant <file>:\tchecks the invariants written in <file>");
    Pr("\t\t\tduring instantiation. Output like the flag -deadlock");
    SThelp();
    if (all) {
       RWhelp();
       MCRLhelp();
       }   
    }
    
static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    Pr("");
    exit(1);
    }

static void Version(void) {
    char buf[100];
    sprintf(buf,"%s: version %s",who, VERSION);
    Pr(buf);
    }   

#define mmax(x,y) ((x)<(y)?(y):(x))

#define INITIAL_SIZE 100

static void Suffix(char *filename, char *suffix) {
     char *lastdot = strrchr(filename,'.');
     if (!lastdot || strcmp(lastdot, suffix)) strcat(filename, suffix);
     }
     
static void EndMessage() {
     ATwarning("Finished.");
     if (monitor) {
          int n = ATgetLength(MCRLgetListOfSummands()),
          cnt = LTSnumberOfUsedSummands();
          if (cnt<n) 
          ATwarning("Number of summands: %d - Number of used summands: %d",
              n, cnt);
          }
     ATwarning("Explored %d states, generated %d transitions, and %d levels",
          explored, transitions, level);
     if (task && task->final) task->final();       
#ifdef INSTRUMENTED
     LTSreport(); 
#endif 
     ATwarning("Number of used Aterms: %d", AT_getAllocatedCount());
     }
     
#ifdef DYNLINK     
/* BEGIN TRANSITION USER */
    
static void StepTransitionUser(int from,  ATerm action, 
     int to) {
     (*UserWriteTrans) (from, action, to);
     visited = mmax(visited, to);
     }
     
static void FinalTransitionUser(void) {
     (*UserClose) (explored, transitions);
     }
      
static void InitTransitionUser(void) {
     
     UserOpen=(USEROPEN) dlsym(handle,"Open");
     if (UserOpen==NULL) ATerror("Loading Open fails: %s", dlerror());
     UserClose=(USERCLOSE) dlsym(handle,"Close");
     if (UserClose==NULL) ATerror("Loading Close fails: %s", dlerror());
     UserWriteTrans=(USERWRITETRANS) dlsym(handle,"WriteTrans");
     if (UserWriteTrans==NULL) ATerror("Loading WriteTrans fails: %s", dlerror());
     UserWriteState=(USERWRITESTATE) dlsym(handle,"WriteState");
     if (UserWriteState==NULL) ATerror("Loading WriteState fails: %s", dlerror());
     (*UserOpen) (0, outputfile);
     }
     
static void AfterStepUser(int src, int cnt) {
     (*UserWriteState) (src, cnt);
     }
     
static TASK taskTransitionUser = {InitTransitionUser, StepTransitionUser, 
     AfterStepUser , FinalTransitionUser};     
#endif

/* END TRANSITION USER */
     
/* --- BEGIN TRACE DETECTION --- */


static void reset_from(BACK back, int from, int nr) {
     int i = from;
     for (i=from;i<nr;i++) {
         back.action[i] = NULL;
         back.from[i] = -1;
         back.actid[i] = -1;
         }
     }

static BACK enlarge_back(BACK back, int to) {
      while (back.nr <= to+1) {
       long old_nr=back.nr;
       if (old_nr==0) {
            back.nr = INITIAL_SIZE;
            if (!(back.action = (ATerm*) calloc(back.nr,sizeof(ATerm))))
                   ATerror("Cannot allocate action array (%d)", back.nr);
            if (!(back.from = (int*) calloc(back.nr,sizeof(int))))
                   ATerror("Cannot allocate from array (%d)", back.nr);
            if (!(back.actid = (int*) calloc(back.nr,sizeof(int))))
                   ATerror("Cannot allocate from array (%d)", back.nr);      
            }
       else {
            ATunprotectArray(back.action);
            back.nr *= 2;
            /* if (monitor) ATwarning("Enlarge trace array %d",back.nr); */
            if (!(back.action = (ATerm*) realloc(back.action, back.nr*sizeof(ATerm))))
                   ATerror("Cannot reallocate term array (%d)", back.nr);
            if (!(back.from = (int*) realloc(back.from, back.nr*sizeof(int))))
                   ATerror("Cannot reallocate term array (%d)", back.nr);
            if (!(back.actid = (int*) realloc(back.actid, back.nr*sizeof(int))))
                   ATerror("Cannot reallocate term array (%d)", back.nr);
            }
       reset_from(back, old_nr, back.nr);
       ATprotectArray(back.action, back.nr);
       }
       return back;
}

static void TraceMessage(char *intro, char *action, char *verb, char *filename) {
       char buf[256];
       if (filename)
       snprintf(buf,256, 
       "%s %s %s.\nFull trace is written in \"%s\". Trace of actions:",
            intro, action, verb, filename);
       else
       snprintf(buf,256, "%s %s %s. Trace found in initial state",
            intro, action, verb);
       fprintf(output, "%s\n", buf);
       if (monitor) ATwarning("%s", buf);
       fflush(output);
       }
       
static void PrintTrace(int to) {
    ATermList  actnames = ATmakeList0(); 
    int init = LTSgetInitialState();
    for (;to!=init;to=back.from[to]) {  
         actnames = ATinsert(actnames, back.action[to]); 
    }
    ATfprintf(output, "%t\n",actnames);
}

static void PrintTraceSim(char *filename, int to) {
    int init = LTSgetInitialState();
    ATermList transitions = ATempty;
    for (;to!=init;to=back.from[to]) {
         transitions = ATinsert(transitions, ATmake("t(<term>,<term>)",
             back.action[to], (ATerm) ATmakeInt(to)));  
         }
    if (!LTSsaveTrace(filename, transitions, 0))
       ATerror("Error in saving trace");
    for (;!ATisEmpty(transitions);transitions= ATgetNext(transitions))
         ATfprintf(output, "%t\n",ATgetArgument((ATermAppl) 
         ATgetFirst(transitions), 0));
    ATfprintf(output,"\n");
    }
    
static void PrintTraceSimPlusOneStep(char *filename, int to, ATerm target,
     int target_to) {
    int init = LTSgetInitialState();
    ATermList transitions = ATmakeList1(ATmake("t(<term>,<term>)",
    target, (ATerm) ATmakeInt(target_to)));
    for (;to!=init;to=back.from[to]) {
         transitions = ATinsert(transitions, ATmake("t(<term>,<term>)",
             back.action[to], (ATerm) ATmakeInt(to)));  
         }
    if (!LTSsaveTrace(filename, transitions, 1))
       ATerror("Error in saving trace");
    for (;!ATisEmpty(transitions);transitions= ATgetNext(transitions))
         ATfprintf(output, "%t\n",ATgetArgument((ATermAppl) 
         ATgetFirst(transitions), 0));
    ATfprintf(output,"\n"); fflush(output); 
    }
    
static void TraceFileName(char *buf) {    
    static int cnt = 0;
    snprintf(buf, 256, "%s.trc", outputfile);
    if (CreateEmptyDir(buf, DELETE_NONE)<0) 
          ATerror("Error in creation directory %s",buf);
    snprintf(buf+strlen(buf), 80-strlen(buf), "/%d", cnt++);
    }
     
static ATermList CheckActions(ATermList trace_actions, BACK back, int from, 
  ATerm act, int to){
  char buf[256];
  ATermList r = trace_actions;
  buf[0]='\0';
  for (;!ATisEmpty(trace_actions);trace_actions=ATgetNext(trace_actions))
     {ATerm trace_action = ATgetFirst(trace_actions); 
     if (ATisEqual(act,trace_action)) {
        snprintf(buf, 256, "%s.trc", outputfile);
        if (CreateEmptyDir(buf, DELETE_NONE)<0) 
           ATerror("Error in creation directory %s",buf);
        if (stop) {
            snprintf(buf+strlen(buf), 80-strlen(buf), "/%s", 
                  ATwriteToString(MCRLprint(act))); 
            }
        else {
            static int *cnt = NULL;
            int n = ATindexOf(r, ATgetFirst(trace_actions), 0);
            if (!cnt) cnt = calloc(ATgetLength(r),sizeof(int));
            if (!cnt) ATerror("Malloc error");
            snprintf(buf+strlen(buf), 80-strlen(buf), "/%s.%d", 
                  ATwriteToString(MCRLprint(act)), 
                  cnt[n]);
            cnt[n]++;
            }
        TraceMessage("Action", ATwriteToString(MCRLprint(act)), "encountered", buf);
        PrintTraceSimPlusOneStep(buf, from, act, to);
        return stop? ATremoveAll(r, ATgetFirst(trace_actions)): r;
        }
     }
     return r;      
}

static void WriteTraceToState(int to, char *buf) {
     PrintTraceSim(buf, to); 
     }
     
static void FinalTrace(void) {
     fprintf(output,"Searching for traces has been finished.\n");
     fprintf(output,"Explored %d states and generated %d transitions\n",
     explored, transitions);
     fclose(output);
     if (ATgetLength(actions)==0) 
          ATwarning("All actions are encountered");
     else {
        ATwarning("The following %s not encountered during state space search:",
        ATgetLength(actions)<=1?"action is":"actions are");
        for (;!ATisEmpty(actions);actions=ATgetNext(actions)) {
           ATfprintf(stderr,"%t\n", MCRLprint(ATgetFirst(actions)));
           }
        }
     ATwarning("Traces have been written in \"%s.dlk\"", outputfile);
     }
          
static void StepTrace(int from,  ATerm action, int to) {
     back = enlarge_back(back, to);
     if (back.from[to]==-1) { 
         back.action[to] = action; back.from[to] = from;
         back.actid[to]= actid;
         }
     actid++;
     if (to>0) {
          actions = CheckActions(actions, back, from, action, to);
          if (ATisEmpty(actions)) {
             EndMessage();
             exit(0);
             }
          } 
     visited = mmax(visited, to);
     }
          
static void InitTrace(void) {
     actid = 0;
     back = enlarge_back(back,0);
     Suffix(outputfile,".dlk"); 
     if (!(output = fopen(outputfile,"w")))
           ATerror("File %s cannot be opened", outputfile);
     ATfprintf(output,"Searching traces to one of the actions in:\n%t\n",
            actions);
     ATwarning("Traces will be written in \"%s\"", outputfile);
     outputfile[strlen(outputfile)-4]='\0';
     }
     
static void AfterStepTrace(int state, int n) {
     char buf[80];
     actid = 0;
     buf[0]='\0';
     if (explore && n==0) {
        if (state>0) TraceFileName(buf);
        TraceMessage("Deadlock","is", "encountered",buf[0]?buf:NULL);
        if (state>0) {
            /* PrintTrace(state); */
            fprintf(output, "Deadlock in state %d\n", state);
            WriteTraceToState(state, buf);
            }
        }
     }
     

                
static TASK taskTrace = {InitTrace, StepTrace, AfterStepTrace, FinalTrace};         
/* --- END TRACE DETECTION --- */

/* BEGIN NOTHING */
    
static void StepNothing(int from,  ATerm action, int to) {
     visited = mmax(visited, to);
     }
               
static TASK taskNothing = {NULL, StepNothing, NULL, NULL};

/* END NOTHING */

/* BEGIN TRANSITION AUT */
    
static void StepTransitionAut(int from,  ATerm action, int to) {
     ATerm actionterm = (cadp && ATisEqual(action, MCRLterm_tau)?
              MCRLterm_i: action);
     fprintf(output, "(%d,",from);
     ATfprintf(output,"%t",actionterm); 
     fprintf(output,",%d)\n",to);
     fflush(output);
     visited = mmax(visited, to);
     }
     
static void FinalTransitionAut(void) {
     rewind(output);
     fprintf (output, "des (0, %d, %d)", transitions, explored);
     fclose(output);
     }
      
static void InitTransitionAut(void) {
     Suffix(outputfile,".aut");
     if (!(output = fopen(outputfile,"w")))
           ATerror("File %s cannot be opened", outputfile);
     fprintf (output, "des (0, ?, ?)                     \n");
     fflush(output);
     }
     
     
static TASK taskTransitionAut = {InitTransitionAut, StepTransitionAut, 
       NULL, FinalTransitionAut};

/* END TRANSITION AUT */

/* BEGIN DEADLOCK */

static int dlk_cnt=0;

static void InitDeadlock(void) {
     actid = 0;
     back = enlarge_back(back,0);  
     Suffix(outputfile,".dlk"); 
     if (!(output = fopen(outputfile,"w")))
           ATerror("File %s cannot be opened", outputfile);
     ATwarning("Traces to deadlock states will be written in \"%s\"", outputfile);
     outputfile[strlen(outputfile)-4]='\0';
     fprintf(output,"Searching deadlocks\n"); 
     }
                                           
static void StepDeadlock(int from,  ATerm action, int to) {
     back = enlarge_back(back,to); 
     if (back.from[to]==-1) { 
         back.action[to] = action;
         back.from[to] = from; 
         back.actid[to] = actid;
         }
     actid++;
     if (ATisEqual(LTSgetState(to), MCRLterm_terminated)) { 
     if (monitor) ATwarning("Action %t in state %d leads to termination", action, to);
       ATfprintf(output, "Action %t in state %d leads to termination\n",
       action, to);
       }
     visited = mmax(visited, to);
     }
     
static void AfterStepDeadlock(int state, int n) {
     char buf[80];
     actid = 0;
     buf[0]='\0';
     if (n==0) {
        dlk_cnt++;
        if (state>0) TraceFileName(buf);
        TraceMessage("Deadlock","is", "encountered",buf[0]?buf:NULL);
        if (state>0) {
            /* PrintTrace(state); */
            WriteTraceToState(state, buf);
            }
        }
     }
          
static void FinalDeadlock(void) {
     if (dlk_cnt>0) {
       ATwarning("Encountered %d deadlock states", dlk_cnt);
       ATwarning("Traces to deadlock states have been written in \"%s.dlk\"", 
       outputfile);
     }
     else {
         ATwarning("No deadlock states are found");
         fprintf(output,"No deadlock states are found.\n");
         }
     fprintf(output,"Searching for deadlock has been finished.\n");
     fprintf(output,"Explored %d states and generated %d transitions\n",
     explored, transitions);
     fclose(output);
     }
     
static TASK taskDeadlock = {InitDeadlock, StepDeadlock, AfterStepDeadlock, 
       FinalDeadlock};
            
/* END DEADLOCK */
 
/* BEGIN INVARIANT */

static ATermList offending_smds = NULL, offended_invariants = NULL;

static int number_of_invariants;
static int *offends;

static void InitInvariant(void) {
     ATprotect((ATerm*) &actions);
     ATprotect((ATerm*) &offending_smds);
     ATprotect((ATerm*) &offended_invariants);
     offending_smds = ATempty; offended_invariants = ATempty;
     back = enlarge_back(back,0); 
     Suffix(outputfile,".dlk"); 
     if (!(output = fopen(outputfile,"w")))
           ATerror("File %s cannot be opened", outputfile);
     outputfile[strlen(outputfile)-4]='\0';
     number_of_invariants = MCRLparseInvariants(invariant);      
     fprintf(output,"Start testing  of %d Invariant%s\n", number_of_invariants,
            number_of_invariants>1?"s":"");
     ATwarning("Start testing %d Invariant%s", number_of_invariants,
            number_of_invariants>1?"s":"");
     ATwarning(
     "Traces to states offending the invariants are written in \"%s.dlk\"", 
     outputfile);
     if (!(offends=calloc(MCRLgetNumberOfSummands(), sizeof(int))))
          ATerror("Cannot allocate array offends: %d",
               MCRLgetNumberOfSummands());       
     }
                                           
static void StepInvariant(int from,  ATerm action, int to) {
     int n = LTSgetSmdIndex();
     ATerm t = (ATerm) ATmakeInt(n +1);
     if (ATindexOf(offending_smds, t, 0)<0)
     offending_smds = ATinsert(offending_smds, t);
     back = enlarge_back(back,to); 
     if (back.from[to]==-1) {
         back.actid[to] = actid; 
         back.action[to] = action;
         back.from[to] = from; 
         }
     actid++;
     if (ATisEqual(LTSgetState(to), MCRLterm_terminated)) { 
     if (monitor) ATwarning("Action %t in state %d leads to termination", action, to);
       ATfprintf(output, "Action %t in state %d leads to termination\n",
       action, to);
       }
     visited = mmax(visited, to);
     }

static void PrintHoldingSummands(void) {
     int n = MCRLgetNumberOfSummands(), i, cnt = 0;
     char *buf = (char*) malloc(n*8*sizeof(char)), *pt = buf;
     for (i=0;i<n;i++)
     if (offends[i]==0) {
          pt += sprintf(pt, "%s%d",  cnt>0?",":"", i+1);
          cnt++;
          }
     if (cnt>0) {
       ATwarning("All invariants hold in summands [%s]", buf);
       fprintf(output, "All invariants hold in summands [%s]\n", buf);
       }
     free(buf);
     }
          
static void AfterStepInvariant(int state, int n) {
     char buf[80];
     int i;
     buf[0] = '\0';
     for (i=0;i<number_of_invariants;i++) 
     if (!ATisEqual(RWrewrite(MCRLgetInvariant(i)), MCRLterm_true)) {
       if (ATindexOf(offended_invariants, (ATerm) ATmakeInt(i+1), 0)<0)
        offended_invariants = 
           ATinsert(offended_invariants, (ATerm) ATmakeInt(i+1));
        if (!ATisEmpty(offending_smds)) {
           offending_smds = ATreverse(offending_smds);
           if (state>0) {
               /* PrintTrace(state); */
               TraceFileName(buf);
               WriteTraceToState(state, buf);
               }
           TraceMessage("Invariant(s) in summands", 
           ATwriteToString((ATerm) offending_smds),
                     "offended", buf[0]?buf:NULL); 
           }
           for (;!ATisEmpty(offending_smds);
                  offending_smds = ATgetNext(offending_smds)) {
           offends[ATgetInt((ATermInt) ATgetFirst(offending_smds))] = 1;
           }
     }
     offending_smds = ATempty;
     actid = 0;
     }
          
static void FinalInvariant(void) {
     if (ATgetLength( offended_invariants)>0) 
     ATfprintf(output, 
     "Not all invariants hold. List of offended invariants %t.\n", 
          offended_invariants);
     else 
       ATfprintf(output,"All invariants hold.\n");
     fprintf(output,"Searching for offended invariants has been finished.\n");
     fprintf(output,"Explored %d states and generated %d transitions\n",
     explored, transitions);
     offended_invariants = ATreverse(offended_invariants);
     if (monitor) 
        ATwarning("Searching for offended invariants has been finished.");
     if (ATisEmpty(offended_invariants)) 
         ATwarning("Yes! all invariants hold for all summands!"); 
     else {
     ATwarning("Not all invariants hold. List of offended invariants %t", 
          offended_invariants);
        PrintHoldingSummands();
        }
     fclose(output);
     }
     
static TASK taskInvariant = {InitInvariant, StepInvariant, AfterStepInvariant, 
       FinalInvariant};
            
/* END INVARIANT */
 
/* BEGIN TRANSITION SVC */

#ifdef SVC                    
static void StepTransitionSVC(int from, ATerm action, int to) {
     SVCbool new;
     ATerm actionterm = (cadp && ATisEqual(action, MCRLterm_tau)?
          MCRLterm_i: action);
     SVClabelIndex labelIndex = SVCnewLabel(svcFile, actionterm, &new);
     ATerm froms = svc_num? (ATerm) ATmakeInt(from):LTSgetPrintState(from), 
           tos = svc_num?(ATerm) ATmakeInt(to):LTSgetPrintState(to);
     SVCstateIndex toIndex = SVCnewState(svcFile, tos, &new), 
                  fromIndex =SVCaterm2State(svcFile, froms); 
     parameterIndex = SVCnewParameter(svcFile, 
             (ATerm) ATmakeInt(LTSgetSmdIndex()+1), &new);
     SVCputTransition(svcFile, fromIndex, labelIndex, toIndex,
          parameterIndex);
     visited = mmax(visited,to);
     }

static void InitTransitionSVC(void) {
     SVCbool new;
     Suffix(outputfile,".svc");
     if (SVCopen(svcFile,  outputfile, SVCwrite, &svc_num)<0)
            ATwarning("%s",SVCerror(SVCerrno));
     SVCsetCreator(svcFile , who);
     SVCsetVersion(svcFile , VERSION);
     SVCsetInitialState(svcFile ,SVCnewState(svcFile, 
            (svc_num?(ATerm) ATmakeInt(0):
     LTSgetPrintState(LTSgetInitialState())), &new));
     }
     
static void FinalTransitionSVC(void) {     
     SVCclose(svcFile);
     }
      
static TASK taskTransitionSVC = {InitTransitionSVC, StepTransitionSVC, NULL,  
                                 FinalTransitionSVC}; 
                                                                        
/* END TRANSITION SVC */
#endif

/* BEGIN CHECK */
                    
static void StepCheck(int from, ATerm action, int to) {
     ATermList froms = (ATermList) LTSgetState(from),
     params = MCRLgetListOfPars();
     if (ATgetLength(params)!=ATgetLength(froms)) {
     ATerror("Different length of lists (p %d != s %d). (summand %d)",
         ATgetLength(params), ATgetLength(froms),LTSgetSmdIndex());
     }
     for (;!ATisEmpty(params);params=ATgetNext(params),
          froms=ATgetNext(froms))
           {ATerm param = ATgetFirst(params);
           if (MCRLgetSort(ATgetFirst(froms))!=ATgetAFun(ATgetArgument(param, 1))) {
           ATerror("parameter %t  term %t sort %s (summand %d)",
           param, ATgetFirst(froms),  ATgetName(MCRLgetSort(ATgetFirst(froms))),
           LTSgetSmdIndex()+1); 
           }
           }     
     visited = mmax(visited,to);
     }

static void InitCheck(void) {
     ATwarning("Checking sorts state vectors will be started");
     }
     
static void FinalCheck(void) {     
     ATwarning("Checking sorts state vectors is ended successfully");
     }
      
static TASK taskCheck = {InitCheck, StepCheck, NULL,  
                                 FinalCheck}; 
                                                                        
/* END TRANSITION SVC */    
                   

static void Monitor(void) {
     if (explored % 1000 == 0) 
     ATwarning("Explored %d and visited %d states and %d transitions at level %d",
          explored, visited+1, transitions, level);
}

static void PrintDeadlock(int state) {
     if (explore) ATwarning("Deadlock in state %d", state);
     }


     
static void Instantiator(void) {
   int visited0 = visited, nlevel =0, nlevel2 = 0;
   for (explored=0;explored<max_explored && explored<=visited;explored++) {
     int r = 0;
     if (monitor) Monitor();
     r = LTSstep(explored);
     if (r<0) ATerror("Error.");
     if (r==0) PrintDeadlock(explored);
     if (task && task->afterstep) task->afterstep(explored, r);  
     transitions += r; nlevel += r; nlevel2++;
     if (explored==visited0) {          
         if (verbose||monitor) 
         ATwarning("level %d number of states %d number of transitions %d",
         level,  nlevel2, nlevel);
         nlevel = 0; nlevel2  =0;
         level++;visited0 = visited;
         } 
      }
    LTSfinish(explored);
    EndMessage();
    }
                   
static void WarningHandler(const char *format, va_list args) {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }
     
static void ErrorHandler(const char *format, va_list args) {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     exit(-1);
     }

static void setTask(TASK *taskPar) {
     if (task) ATerror("Illegal combination of flags");
     task = taskPar;
     }   
                  
int main(int argc, char *argv[])
     {
     int i, j = 0;
     char **newargv = (char**) calloc(argc + 3, sizeof(char*));
     if (!newargv) ATerror("Cannot allocate array argv"); 
     newargv[j++] = argv[0]; 
#ifdef DYNLINK
     newargv[j++]="-alt"; newargv[j++]="rw";
#endif
     ATinit(argc, argv, (ATerm*) &argc);
     ATsetWarningHandler(WarningHandler);
     ATsetErrorHandler(ErrorHandler);
     MCRLsetOutputFile(outputfile);
     for (i=1;i<argc;i++) {
          help(argv[i]);
          if (!strcmp(argv[i],"-version"))
               {
               Version();
               exit(0);
               }
          
          if (!strcmp(argv[i],"-monitor"))
               {
               monitor = ATtrue;
               continue;
               }
          if (!strcmp(argv[i],"-explore")) {
               explore = ATtrue;
               monitor = ATtrue;
               continue;
               }
          if (!strcmp(argv[i],"-verbose")) {
            verbose = ATtrue;
             /* continue; */
            }
         if (!strcmp(argv[i],"-")) {
               setTask(&taskNothing);
               continue;
               }
         if (!strcmp(argv[i],"-deadlock")) {
               setTask(&taskDeadlock);
               explore = ATtrue;
               continue;
               }
         if (!strcmp(argv[i],"-aut")) {
               setTask(&taskTransitionAut);
               continue;
               }
         if (!strcmp(argv[i],"-check")) {
               setTask(&taskCheck);
               continue;
               }
         if (!strcmp(argv[i],"-invariant")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *name = argv[i];
                if (invariant) ATerror("flag -invariant already present");
                invariant = fopen(name,"r");
                if (!invariant) ATerror("Cannot open file %s", name);
                setTask(&taskInvariant); 
                continue;
                }
            ATerror("Option %s needs argument.\n",argv[i-1]);
            }
#ifdef DYNLINK
         if (!strcmp(argv[i],"-user")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                userFile = argv[i];
                setTask(&taskTransitionUser);
                sprintf(cmd, "sleep 1;%s %s %s %s %s", MAKE, userFile,
                        "DEBUG=\\#",  "OPTION=-g", "1>&2");
                ATwarning("%s",cmd); 
                if (system(cmd)>0)
                    ATerror("Fail: make %s", userFile);
                sprintf(cmd,"./%s",userFile);
                handle=dlopen(cmd,RTLD_NOW);
                if (handle==NULL) 
                    ATerror("Loading %s fails: %s",cmd , dlerror()); 
                continue;
                }
            else
               ATerror("After flag -user <file>.so expected");
               }
#endif
         if (!strcmp(argv[i],"-trace")) {
               if ((++i)<argc && strncmp(argv[i],"-",1)) {
                ATprotect((ATerm*) &actions);
                targets = argv[i];
                setTask(&taskTrace);
                stop = ATtrue; 
                continue;
                }
            else
               ATerror("After flag -trace list of terms expected");
            }
          if (!strcmp(argv[i],"-traces")) {
               if ((++i)<argc && strncmp(argv[i],"-",1)) {
                ATprotect((ATerm*) &actions);
                targets = argv[i];
                setTask(&taskTrace); 
                continue;
                }
            else
               ATerror("After flag -trace list of terms expected");
            }
#ifdef SVC
          if (!strcmp(argv[i],"-svc-term") || !strcmp(argv[i],"-svc-all")) {
               setTask(&taskTransitionSVC);
               continue;
               }
          if (!strcmp(argv[i],"-svc-num") || !strcmp(argv[i],"-svc")) {
               svc_num = 1;
               setTask(&taskTransitionSVC);
               continue;
               }
#endif
          if (!strcmp(argv[i],"-i")) {
               cadp = ATtrue;
               continue;
               }
          if (!strcmp(argv[i],"-reduce")) {
               reduce = ATtrue;
               continue;
               }
          if (!strcmp(argv[i],"-max")) {
               if ((++i)<argc && strncmp(argv[i],"-",1)) {
                  char *endptr = NULL;
                  max_explored = strtol(argv[i],&endptr,10) * 1000;
                  if (*endptr != '\0') ATerror("Number expected after \"-max\"");
                  }
            else
  ATerror("Integer (max number of explorations) expected after %s\n",argv[i-1]);
            continue;
            }

          newargv[j++] = argv[i];
          } 
    LTSsetArguments(&j,&newargv);
    STsetArguments(&j,&newargv);
    if (!MCRLinitRW(j, newargv)) exit(1);   
    if (!task) task = &taskTransitionAut;      
    if (targets) {
         actions = MCRLparseActions(targets);
         if (!actions) exit(1);
         }
     /* ----- Start of initialisation ---- */
  
    
    LTSinitialize(task->instep); 
    if (task && task->init) task->init(); 
    Instantiator();
    if (reduce) {
        MCRLsetListOfSummands(LTSgetUsedSummands());
        MCRLoutput();
        }
    exit(EXIT_SUCCESS);
    }
