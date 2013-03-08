/* $Id: server.c,v 1.6 2005/06/17 15:05:48 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include "param0.h"
#include "utl.h"
#include "rw.h"
#include "xlts.h"
#include "explore.h"
#include "step.h"
#include "ltree.h"
#include <string.h>
#define DSIZE 100


step_t InitStepper(void);
void Reset(void);
void Home(void);
void Undo(void);
void Down(void);
void Redo(int current);
void Forward(void);
void Back(void);
void Child(void);
void Parent(void);
void StepState(int state);
void SetMarker(idx_t join);
void LevelUp(void);
void LevelDown(void);
idx_t Explore(void);
void SendLabels(void);
void Clear(void);
void Search(int n, int *sels); 
int LoadTraces(void);
int SaveTraces(void);
int SaveTransitions(void);
void SetSendState(int send_state);
void UpdateState(int row, char *term);

FILE *tty;
static char d[DSIZE];
static step_t st;

char *hello = "hello", *goodbye = "goodbye", 
*stepstate = "stepstate", 
*finish = "#", *smdheader = "smd", *treeheader = "tree", *treesmdheader =
"treesmd", *reset = "reset", *redo = "redo", *undoheader = "undo", 
*parentheader = "parent", *markheader = "mark", *displayheader = "display", 
*MCRLtrue = "true", *MCRLfalse = "false",  *info = "info", *childheader = "child",
*left = "left", *right = "right",  *button="#button", *levelup = "levelup",
*leveldown = "leveldown", *exploreheader = "explore",
*msg_error = "error:", *msg_print = "msg:", *depthcontent = "depthcontent",
*home = "home", *labelheader = "labels", *searchheader = "search",
*continueheader="continue", *clearheader = "clear", *saveheader = "save",
*saveautheader = "saveaut", *state = "state", *updatestate = "updatestate";

char *ltsfile = NULL, *trc = NULL, *outtrc = NULL, *autfile = NULL;   
static int isAnswer = 1, isOkay = 0;
static char *filename;

/* error messages will be transformed to UTF format
   and sent to the JAVA stderr */
ATermList names, stateList = NULL;
ATermTable trace;
           
void LastMessage(void) {
     /* fprintf(tty,"Lastmessage %d isok %d\n", isAnswer, isOkay); */
     printUTF(stdout,goodbye);
     printUTF(stdout,isAnswer?MCRLtrue:MCRLfalse);
     printUTF(stdout,isOkay?MCRLtrue:MCRLfalse);
     printUTF(stdout,finish);
     fflush(stdout);
     }
        
static void ServerLoop(void) {
    int n;
    while (1) {
       if (readUTF(stdin, d, DSIZE)<0) errormsg("readutf");
       // fprintf(tty, "Okay fread was %s\n", d);
       if (strcmp(hello, d)==0) {
          if ((st=InitStepper())==NULL) {
             fprintf(tty,"Start up no succes\n");
             exit(1);
             }
          Reset();
          if (ltsfile) Explore();
          if (trc) if (LoadTraces()<0) errormsg("LoadTraces");
          // fprintf(tty, "Okay Redo was %s\n", d);
          Redo(0); 
          }
       else
       if (strcmp(stepstate, d)==0) {
          int state;
          if (readintUTF(stdin, &state)<0) errormsg("readintUTF");
          StepState(state);
          }
       else
       if (strcmp(reset, d)==0) {
          Reset();
          Redo(0);
          }
       else
       if (strcmp(home, d)==0) {
          Home();
          Redo(0);
          }
       else
       if (strcmp(undoheader, d)==0) {
          Undo();
          }
       else
       if (strcmp(parentheader, d)==0) {
          Down();
          }
       else
       if (strcmp(childheader, d)==0) {
          Child();
          }
       else
       if (strcmp(redo, d)==0) {
          int rank;
          if (readintUTF(stdin, &rank)<0) errormsg("readintUTF");
          Redo(rank);
          }
       else
       if (strcmp(right, d)==0) {
          Forward();
          }
       else
       if (strcmp(left, d)==0) {
          Back();
          }
       else
       if (strcmp(levelup, d)==0) {
          LevelUp();
          }
       else
       if (strcmp(leveldown, d)==0) {
          LevelDown();
          }
       else
       if (strcmp(exploreheader, d)==0) { 
          Redo(Explore());
          // Redo(0);
          }
       else
       if (strcmp(labelheader, d)==0) {
          SendLabels();
          }
       else
       if (strcmp(clearheader, d)==0) {
          Clear();
          }
       else
       if (strcmp(saveheader, d)==0) {
          SaveTraces();
          }
       else
       if (strcmp(saveautheader, d)==0) {
          SaveTransitions();
          }
       else
       if (strcmp(continueheader, d)==0) {
          int n;
          if (readintUTF(stdin, &n)<0) errormsg("readintUTF");
          }
       else
       if (strcmp(searchheader, d)==0) {
          int n, i;
          if (readintUTF(stdin, &n)<0) errormsg("readintUTF");
          if (n>0) {
             DECLA(int, sels, n);
             for (i=0;i<n;i++) {
                if (readintUTF(stdin, sels+i)<0) errormsg("readintUTF");
                }
             Search(n, sels);
             }
          }
       else if (strcmp(markheader, d)==0) {
          int join;
          if (readintUTF(stdin, &join)<0) errormsg("readintUTF");
          SetMarker(join);
          }
       else if (strcmp(state, d)==0) {
          int send_state;
          if (readintUTF(stdin, &send_state)<0) errormsg("readintUTF");
          SetSendState(send_state);
          }
       else if (strcmp(updatestate, d)==0) {
          int row; char *term;
          if (readintUTF(stdin, &row)<0) errormsg("readintUTF");
	  term = readstringUTF(stdin);
          // fprintf(stderr,"row = %d\n", row);
          UpdateState(row, term);
          }
       else if (strcmp(goodbye, d)==0) {
           if (readUTF(stdin, d, DSIZE)<0) errormsg("readutf");
           /* fprintf(tty,"Break\n"); */
           if (!strcmp(d, MCRLtrue)) isAnswer = 0;
           isOkay = 1;
           break;
           }
       if ((n=readUTF(stdin, d, DSIZE))<0) {
           fprintf(tty,"Ilegal exit\n");
           exit(1); /* Reads End token */
           }
       d[n]= '\0';
       // fprintf(tty, "Okay fread was %s\n", d);
       }
     printmsg("stepping through %s is finished",filename);
     
    }
     
static void WarningHandler(const char *format, va_list args) {
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     fflush(stderr);
     }
         
static void ErrorHandler(const char *format, va_list args) {
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     fflush(stderr);
     }

ATermList getListOfParNames() {
     ATermList r = ATempty, pars = MCRLgetListOfPars();
     for (;!ATisEmpty(pars);pars=ATgetNext(pars))
       r = ATinsert(r, ATgetArgument((ATermAppl) ATgetFirst(pars), 0));
     return ATreverse(r);
     } 
                      
int main(int argc, char *argv[]) {
    int i = 0, j = 0;
    char **newargv = (char**) calloc(argc, sizeof(char*)), *suffix;
#ifdef USE_SVC
     lts_stack_bottom=&argc;
#endif
    atexit(LastMessage);
    sleep(1);
    filename = argv[argc-1];
    tty = fopen("/dev/tty", "w");
    // fprintf(tty, "Server started %s\n", filename);
    // system("pwd >/dev/tty");
    newargv[i++] = argv[j++]; 
    for (;i<argc;i++) 
    if (strncmp(argv[i],"-at-",4)) {newargv[j++] = argv[i];}
    UTLinit(stderr, msg_print, msg_error, "");
    ATinit(argc, argv, (ATerm*) &argc);
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    ATprotect((ATerm*) &names); names = ATempty;
    ATprotect((ATerm*) &stateList);
    trace = ATtableCreate(50,70);
    if ((suffix=strrchr(filename,'.')) && !strcmp(suffix,".trc")) {
       trc = filename;
       newargv[j-1][strlen(newargv[j-1])-4]='\0';
       if (!MCRLinitializeXX(&j, &newargv)) errormsg("File cannot be opened");
       if (!RWinitialize(MCRLgetAdt())) {fprintf(tty, "Error RWinitialize\n"); 
              exit(1);}
       STsetArguments(&j,&newargv); stateList = getListOfParNames();
       } 
    else if ((suffix=strrchr(filename,'.')) && !strcmp(suffix,".tbf")) {
       RWsetArguments(&j, &newargv);
       if (!MCRLinitializeXX(&j, &newargv)) errormsg("File cannot be opened");
       if (!RWinitialize(MCRLgetAdt())) {fprintf(tty, "Error RWinitialize\n"); 
              exit(1);}
       STsetArguments(&j,&newargv); stateList = getListOfParNames();
       }
    else {
       // for (i=0;i<j;i++) fprintf(tty,"%s\n", newargv[i]);
       ltsfile = filename;
       }
    outtrc = strdup(filename);
    autfile = strdup(filename);
    strcpy(outtrc+strlen(outtrc)-4,".trc");
    strcpy(autfile+strlen(autfile)-4,".aut");
    // fprintf(tty,"Server starts\n");
    ServerLoop();
    exit(0);
    }
