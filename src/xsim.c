/* $Id: xsim.c,v 1.3 2004/10/19 14:42:34 uid523 Exp $ */
#include <stdio.h>
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif   
#include <limits.h>
#include "tcl.h"
#include "tk.h"
char *who="Simulator";
#include "aterm1.h"
#include "aterm2.h"
extern int main();
Tcl_Interp *interp;
/*
int *tclDummyMainPtr = (int*) main;
*/
#ifndef CONST84
#define CONST84 
#endif

int ReadLin(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char *argv[]);

int Step(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char *argv[]);

int State(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char *argv[]);

int Highlight(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char *argv[]);

int Choice(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char *argv[]);

int Reset(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char *argv[]);

int Undo(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char *argv[]);

int Redo(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char *argv[]);

int EvaluateExpr(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char
*argv[]);

int LastAction(ClientData clientData, Tcl_Interp *interp, int argc, CONST84 char
*argv[]);

int DisplayStatefuns(ClientData clientData, Tcl_Interp *interp,
    int argc, CONST84 char *argv[]);

int SaveTrace(ClientData clientData, Tcl_Interp *interp,
	    int argc, CONST84 char *argv[]);

int LoadTrace(ClientData clientData, Tcl_Interp *interp,
	    int argc, CONST84 char *argv[]);

int PrintTrace(ClientData clientData, Tcl_Interp *interp,
		    int argc, CONST84 char *argv[]);

int ReleaseFiles(ClientData clientData, Tcl_Interp *interp,
		    int argc, CONST84 char *argv[]);

int Current(ClientData clientData, Tcl_Interp *interp,
	int argc, CONST84 char *argv[]);

int StateView(ClientData clientData, Tcl_Interp *interp,
    int argc, CONST84 char *argv[]);
    
int EndStateView(ClientData clientData, Tcl_Interp *interp,
	int argc, CONST84 char *argv[]);
        
int PutState(ClientData clientData, Tcl_Interp *interp,
	int argc, CONST84 char *argv[]);
                        
void Protect(void);

ATbool compile = ATtrue; 

void ReleaseFile(void);

void TimerProc(ClientData clientData);

void SIMhelp(ATbool all);

#define P(msg)  fprintf(stderr,"%s\n",msg)

static void helpmsg(ATbool all) 
    {  
    P("Usage: msim [options] [input file]");
    P("");
    P("The following options can be used");
    P("-help:\t\t\tyields this message");
    P("-help-all:\t\tyields all help information");
    P("-version:\t\tgets the version number of this release");
    SIMhelp(all);
    }
    
static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    P("");
    helpmsg(!strcmp(s,"-help-all"));
    P("");
    P("");
    exit(1);
    }

static void Version(void)
    {
    char buf[100];
    sprintf(buf,"%s: version %s",who, VERSION);
    P(buf);
    }
#undef P

int Tcl_AppInit(Tcl_Interp *tcl_interp)
    {
    if (Tcl_Init(tcl_interp) == TCL_ERROR)
	{
	return TCL_ERROR;
	}
    Tk_Init(tcl_interp);
    interp = tcl_interp;
    {
    Tcl_CreateCommand(tcl_interp, "readlin", ReadLin, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "step", Step, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "choice", Choice, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "highlight", Highlight, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "state", State, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "reset", Reset, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "undo", Undo, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "redo", Redo, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "rewrite", EvaluateExpr, NULL, NULL); 
    Tcl_CreateCommand(tcl_interp, "lastaction", LastAction, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "savetrace", SaveTrace, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "loadtrace", LoadTrace, NULL, NULL); 
    Tcl_CreateCommand(tcl_interp, "printtrace", PrintTrace, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "releasefiles", ReleaseFiles, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "current", Current, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "stateview", StateView, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "endstateview", EndStateView, NULL, NULL);
    Tcl_CreateCommand(tcl_interp, "putstate", PutState, NULL, NULL);
    }
#ifdef GRAPPA
    Tcl_CreateTimerHandler(100,TimerProc, NULL);
#endif
    return TCL_OK;
    }

int main(int argc, char *argv[])
    {
    int i;
    ATinit(argc, argv,(ATerm*) &argc); 
     for (i=1;i<argc;i++) {
          help(argv[i]);
          if (!strcmp(argv[i],"-version"))
               {
               Version();
               exit(0);
               }
     }
    if ( (argc < 2) || (argv[argc-1][0] == '-') )
    {
	    fprintf(stderr,"msim: File name expected as last argument\n");
	    exit(1);
    }

    Tk_Main(argc, argv, Tcl_AppInit);
    exit(0);
    }
