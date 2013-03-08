/* $Id: simu.c,v 1.9 2006/08/24 14:36:09 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "lts.h"
#include <string.h>
#include <stdlib.h>
#include "tcl.h"
#include "tk.h"
#include <errno.h>

#ifndef CONST84
#define CONST84
#endif

static char tempname[256];

FILE *Stategraph(int argc, CONST84 char* argv[]);

char* ctau_name;
static ATbool newTraceFormat = ATfalse;
static FILE *in;
static char *fileName;

#define BUFLEN 1024

static char buf[BUFLEN], filename[BUFLEN]; 
static int reset = 0, stateno = -1;
static ATermList states = NULL, actions = NULL, summands = NULL; 

static ATerm  trm0 = NULL; 
static ATermList history = NULL;
extern ATbool compile; 

extern Tcl_Interp *interp;

static FILE *erf = NULL;

/* history [ current, [[state, action ]......[stateno, emptylist]]] */

static void RemoveTempFile(void) {
   if (tempname[0]!='\0') RemoveFile(tempname);
   }
          
static ATerm make_term  (ATerm t);
   
static ATermList make_terms (ATermList terms)
{
  ATermList args = ATmakeList0(); 
  for (;!ATisEmpty(terms);terms=ATgetNext(terms))
       {
       ATerm term = ATgetFirst(terms);
       args = ATinsert(args,  make_term(term));
       }
  return ATreverse(args);
}

static ATerm make_term (ATerm t)
 {
 ATermList args = ATgetArguments((ATermAppl) t);
 char *name =  MCRLgetName(t);
 Symbol s = ATmakeSymbol(name, ATgetLength(args), ATfalse);
 return (ATerm) ATmakeApplList(s, make_terms(args));
 }

static ATerm  make_action(ATerm actname, ATermList actargs)
     {
     char *name = ATgetName(ATgetSymbol(actname));
     return (ATerm) ATmakeApplList(ATmakeSymbol(name, ATgetLength(actargs),
         ATfalse), make_terms(actargs));
     }
     
void AddTransitions(int from,  ATerm action, int to)
     {
     states = ATappend(states, (ATerm) ATmakeInt(to));
     summands = ATappend(summands, (ATerm) ATmakeInt(LTSgetSmdIndex()));
     actions = ATappend(actions, action);
     }   

static ATermList StartHistory(void)
       { 
        return ATmakeList2(trm0,
	  (ATerm) ATmakeList1((ATerm) ATmakeList3(trm0, trm0, trm0)));
       }
       
static void Protect();

static void WarningHandler(const char *format, va_list args)
     {
     if (!erf) erf = TempFile(tempname, 256);
     if (erf) {
        int n;
        ATvfprintf(erf, format, args);
        fprintf(erf,"%c",'\0');
        fclose(erf);erf = NULL;
        erf = fopen(tempname, "r");
        n = fread(buf, sizeof(char), BUFLEN, erf);
        /* fprintf(stderr,"QQQ n = %d %s\n", n, buf); */
        if (n==0) return;
        if (n>=0 && buf[n-1]=='\n') buf[n-1]='\0';
        Tcl_AppendResult(interp, ": ", NULL);
        Tcl_AppendResult(interp, buf, NULL);
        fclose(erf); erf = NULL;
        }
     else {
         ATvfprintf(stderr, format, args);
         fprintf(stderr,"\n");
         }
     }  

#ifdef GRAPPA


static FILE *startStateview(char *filename) {
     int argc = 3;
     char *argv[3];
     argv[0] = "stategraph",
     argv[1] =  "-stateview",
     argv[2] =  filename;
     Tcl_SetVar(interp,"client","1",0);
     return Stategraph(argc, (CONST84 char**) argv);
     }
     
static void putStates(int stateno) {
     ATermList states =  (ATermList) LTSgetState(stateno);
     /* ATfprintf(stdout, "QQQ %t", states);
     fflush(stdout);
     */
     uint16_t n = HtoNS(ATgetLength(states));
     fwrite(&n, 1, sizeof(short), in);
     if (ferror(in)) {in = NULL; return;}
     else fflush(in);
     for (;!ATisEmpty(states);states=ATgetNext(states)) {
          char *state = ATwriteToString(MCRLprint(ATgetFirst(states)));
          int s = strlen(state)+sizeof(short)+2;
          uint16_t m = HtoNS(strlen(state)+2);
          DECLA(char, utf, s+1);
          memcpy(utf, &m, sizeof(short));
          sprintf(utf+sizeof(short), "[%s]", state); 
          fwrite(utf, s, sizeof(char), in);
          if (ferror(in)) {in = NULL;return;}
          }
     fflush(in);
     }
          
static void putState(int state) {
     char tag[] = "state", utf[sizeof(tag)+sizeof(short)]; 
     uint16_t m  = HtoNS(strlen(tag));
     memcpy(utf, &m, sizeof(short)); 
     memcpy(utf+sizeof(short), tag, strlen(tag)); 
     fwrite(utf, sizeof(utf)-1, sizeof(char), in);
     if (ferror(in)) in = NULL;
     else {
       fflush(in);
       putStates(state);
       } 
     }
     
static void putEdge(int summand) {
     char tag[] = "edge", utf[sizeof(tag)+sizeof(short)];
     uint16_t m  = HtoNS(strlen(tag)), n = HtoNS(summand);
     memcpy(utf, &m, sizeof(short)); 
     memcpy(utf+sizeof(short), tag, strlen(tag)); 
     fwrite(utf, sizeof(utf)-1, sizeof(char), in);
     fflush(in);
     fwrite(&n, 1, sizeof(short), in);
     if (ferror(in)) in = NULL;
     else
        fflush(in);
     }
     
static void putFinish(void) {
     char tag[] = "finish", utf[sizeof(tag)+sizeof(short)];
     uint16_t m  = HtoNS(strlen(tag));
     memcpy(utf, &m, sizeof(short)); 
     memcpy(utf+sizeof(short), tag, strlen(tag)); 
     fwrite(utf, sizeof(utf)-1, sizeof(char), in);
     if (ferror(in)) in = NULL;
     else
     fflush(in);
     }

static int putAlert(void) {
     char tag[] = "alert", utf[sizeof(tag)+sizeof(short)];
     uint16_t m  = HtoNS(strlen(tag));
     int r;
     memcpy(utf, &m, sizeof(short)); 
     memcpy(utf+sizeof(short), tag, strlen(tag)); 
     fwrite(utf, sizeof(utf)-1, sizeof(char), in);
     r = ferror(in);
     if (r) {
        clearerr(in);
        in = NULL;
        }
     else
        fflush(in);
     return r;
     }
          
static void putReset(void) {
     char tag[] = "reset", utf[sizeof(tag)+sizeof(short)]; 
     uint16_t m  = HtoNS(strlen(tag));
     memcpy(utf, &m, sizeof(short)); 
     memcpy(utf+sizeof(short), tag, strlen(tag)); 
     fwrite(utf, sizeof(utf)-1, sizeof(char), in);
     if (ferror(in)) in = NULL;
     else
        fflush(in);
     }
      
void TimerProc(ClientData clientData) {
  if (in && putAlert()) {
      CONST84_RETURN char *value = Tcl_GetVar(interp,"client",0);
      /* ATfprintf(stdout,"value:%s\n", value);
      fflush(stdout); */
      if (strcmp(value,"")) Tcl_SetVar(interp,"client","",0);
      }
   /*
  if (in) ATfprintf(stdout, "aap: %d", putAlert());
  else ATfprintf(stdout, "Not yet");
  fflush(stdout);
  */
  Tcl_CreateTimerHandler(500,TimerProc, NULL);
  }        
#endif

int ReadLin(ClientData clientData, Tcl_Interp *interp,
    int argc,CONST84 char *argv[])
    {
    int i, j = 0;
    static ATbool first = ATtrue; 
    CONST84 char **argvPtr;
    int argcPtr;
    char **newargv = NULL;
    ATermList sums = NULL;
    if (first) {
      tempname[0]='\0';
      atexit(RemoveTempFile);
      ATsetWarningHandler(WarningHandler);
      }
    Tcl_ResetResult(interp);
    if (Tcl_SplitList(interp, argv[argc-1], &argcPtr, &argvPtr)
         == TCL_ERROR) 
         {
         fprintf(stderr,"System no list arg\n");
         exit(1);
         }; 
    newargv = (char**) calloc(argcPtr + 1, sizeof(char*));
    if (!newargv) ATerror("Cannot allocate array argv"); 
    newargv[j++] = "msim";
    for (i=2;i<argcPtr;i++) { 
          newargv[j++] = (char*) argvPtr[i];    
          }
    LTSsetArguments(&j,&newargv);
    if (!MCRLinitRW(j, newargv)) return TCL_ERROR;
    for (sums=MCRLgetListOfSummands();!ATisEmpty(sums); sums= ATgetNext(sums)) {
        RWdeclareVariables(MCRLgetListOfVars(ATgetFirst(sums)));
        }  
    RWdeclareVariables(MCRLgetListOfPars());
    LTSinitialize(AddTransitions);
    if (first) {
	Protect();
	first = ATfalse;
	}
    fileName = newargv[j-1];
    states = actions = summands = ATmakeList0();
    reset = 0; stateno = 0;
    history = StartHistory();
    return TCL_OK;
    }

int StateView(ClientData clientData, Tcl_Interp *interp,
    int argc,CONST84 char *argv[]) {
#ifdef GRAPPA
ATwarning("startStateview\n");
    in = startStateview(fileName);
ATwarning("endStateview\n");
    if (in) putState(stateno);
#else
    ATwarning("There is no stateview installed"); 
#endif
    return TCL_OK;
    }
#define SIZETABLE 1024

static ATermList DoStepState(int stateval) {
     states = actions = summands = ATmakeList0();
     /* ATfprintf(stdout,"stateval = %d\n", stateval); */
     {
     int code = LTSstep(stateno), i=0;
     if (code<0) return NULL;
     for (;!ATisEmpty(states) && !ATisEmpty(actions);states = ATgetNext(states),
     actions = ATgetNext(actions), i++) 
     if (ATgetInt((ATermInt) ATgetFirst(states)) == stateval) {
        ATermList rec = ATmakeList3(ATgetFirst(states), 
             ATgetFirst(actions), (ATerm) ATmakeInt(i));
        /* ATfprintf(stdout,"QQ %t\n", rec); */  
        history = ATmakeList2(ATelementAt(history,0), 
         (ATerm) ATinsert((ATermList) ATelementAt(history,1), (ATerm) rec));
         stateno  = stateval;
        return rec;
        }
     return NULL;
     }
     }
     
static ATermList DoStep(int act) {
     states = actions = summands = ATmakeList0();
     {
     int code = LTSstep(stateno), i = 0;
     if (code<0) return NULL;
     for (;!ATisEmpty(states) && !ATisEmpty(actions);states = ATgetNext(states),
     actions = ATgetNext(actions), i++)
     if (i == act) {
        ATermList rec = ATmakeList3(ATgetFirst(states), 
             ATgetFirst(actions), (ATerm) ATmakeInt(i));
            /* ATfprintf(stderr,"QQ %t\n", rec); */
        history = ATmakeList2(ATelementAt(history,0), 
         (ATerm) ATinsert((ATermList) ATelementAt(history,1), (ATerm) rec));
         stateno  = ATgetInt((ATermInt) ATgetFirst(states));
        return rec;
        }
     return NULL;
     }
     }
               
int Step(ClientData clientData, Tcl_Interp *interp,
    int argc,CONST84 char *argv[])
    {
    Tcl_ResetResult(interp);
    states = actions = summands = ATmakeList0();
         {
         int code = LTSstep(stateno); 
         /* char buf[BUFLEN+1];  */
         if (code<0) return TCL_ERROR;
         /* terminated code == -1; */
         if (code==0) 
	     {
             if (ATisEqual(LTSgetState(stateno), MCRLterm_terminated))
	         Tcl_AppendElement(interp, "#terminated");
	     return TCL_OK;
	     }
              {
              ATermList acts = actions;
              /*
              ATfprintf(stderr,"actions = %lx %t\n",actions, actions);
              ATfprintf(stderr,"acts = %lx %t\n",acts, acts);
              */
              for (;!ATisEmpty(acts); acts=ATgetNext(acts))
                  {ATerm act = ATgetFirst(acts);
                  /* sprintf(buf, "%s",ATgetName(ATgetAFun((act)))); */
                  Tcl_AppendElement(interp, ATgetName(ATgetAFun((act))));
                  }  
              }
         }
    return TCL_OK;
    }
               
#define NDOTS 10

#define SPACE 0

#define STARTLEN BUFLEN-SPACE

static ATermList StatesSet(void)
    {
    ATermList result = ATmakeList0();
    ATermList sal = (ATermList) ATelementAt(history,1);
    int current = ATgetInt((ATermInt) ATelementAt(history,0)),i; 
    for (i=0;!ATisEmpty(sal) && i<=current;sal = ATgetNext(sal),i++);
    for (;!ATisEmpty(sal);sal = ATgetNext(sal))
    if (ATindexOf(result,
        ATgetFirst((ATermList) ATgetFirst(sal)), 0) < 0)
	result = ATinsert(result, ATgetFirst((ATermList) ATgetFirst(sal)));
    return result;
    }

int State(ClientData clientData, Tcl_Interp *interp,
    int argc,CONST84 char *argv[])
    {
    ATermList pars = MCRLgetListOfPars();
    ATerm state = LTSgetState(stateno);
    ATermList statevals = ATgetType(state)==AT_LIST?(ATermList) state:NULL;
    Tcl_ResetResult(interp);
    if (!statevals) {
      Tcl_AppendElement(interp, "terminated");
      return TCL_OK;
    }
    {
    ATermList oldstates = StatesSet() /* List of state numbers */;
    ATbool new = (ATindexOf(oldstates, (ATerm) ATmakeInt(stateno), 0)<0);
    char buf[BUFLEN+1], temp[BUFLEN+1], *start = buf + SPACE;
    sprintf(buf, "new state: %s  number of visited states: %d", 
	new?"+ ":"- ", ATgetLength(oldstates) + (new?1:0));
    Tcl_AppendElement(interp, buf);
    for (;!ATisEmpty(statevals) && !ATisEmpty(pars) ;
         statevals=ATgetNext(statevals), pars = ATgetNext(pars))
        {ATerm stateval = ATgetFirst(statevals);
        ATerm par = ATgetFirst(pars);
	int n;
	strncpy(start, MCRLgetName(ATgetArgument(par,0)), STARTLEN);
        strncat(start,": ", STARTLEN);
        strncat(start, ATgetName(ATgetSymbol((ATgetArgument(par,1)))), STARTLEN);
	n = strlen(start);
	if (STARTLEN-n>3)
	    {
	    strcat(start," = ");
	    n+=3;
	    }
	strncpy(temp,ATwriteToString(make_term(stateval)), STARTLEN - n);
        temp[STARTLEN - n]='\0';
	if (strlen(temp) == STARTLEN-n && strlen(temp)>NDOTS) 
	    {
	    int i, pt;
	    for (pt=STARTLEN-n,i=0, pt>=2;i<NDOTS;i++,--pt) temp[pt]='.';
            temp[i]='\0';
	    }
	strcat(start, temp);
	Tcl_AppendElement(interp, buf);
	}
     }
    return TCL_OK;
    }

int Choice(ClientData clientData, Tcl_Interp *interp,
    int argc,CONST84 char *argv[])
    {
    long choice;
    ATerm action = NULL, summand = NULL;
    ATermInt stateval = NULL;
    ATermList sal = (ATermList) ATelementAt(history,1);
    int current = ATgetInt((ATermInt) ATelementAt(history,0));
    int i;
    Tcl_ResetResult(interp);
    for (i=0;i<current;i++) sal = ATgetNext(sal);
    Tcl_ExprLong(interp, argv[1], &choice);
    stateval = (ATermInt) ATelementAt(states, choice);
    action = ATelementAt(actions, choice);
    summand = ATelementAt(summands, choice);
    /* fprintf(stdout,"summand(%d)\n", ATgetInt((ATermInt) summand)); */
    if (!stateval || !action || !summand)
	{
        return TCL_OK;
        /*
	ATerror("Something wrong with choice %d %t\n",
	choice, states);
	abort();
        */
	}
    history = ATmakeList2(trm0, 
	(ATerm) ATinsert(sal, 
             (ATerm) ATmakeList3((ATerm) stateval, action, 
             (ATerm) ATmakeInt(choice)))
        );
    stateno  = ATgetInt(stateval);
#ifdef GRAPPA
    if (in) {
           putEdge(ATgetInt((ATermInt) summand));
           putState(stateno);
           }
#endif 
    return TCL_OK;
    }
    
int Highlight(ClientData clientData, Tcl_Interp *interp,
    int argc,CONST84 char *argv[])
    {
#ifdef GRAPPA
    long choice;
    ATerm summand = NULL;
    if (!in) return TCL_OK;
    Tcl_ExprLong(interp, argv[1], &choice);
    summand = ATelementAt(summands, choice);
    if (summand)
        putEdge(ATgetInt((ATermInt) summand));
#endif
    return TCL_OK;
    }
       
int EvaluateExpr(ClientData clientData, Tcl_Interp *interp,
     int argc,CONST84 char *argv[])
     {
     Tcl_ResetResult(interp);
     {
     char *e = (char*) argv[1];
     ATerm result = MCRLparse(e);
     if (!result) 
          {
          return TCL_ERROR;
          }
     result = RWrewrite(result); 
     Tcl_SetResult(interp, ATwriteToString(make_term(result)), TCL_VOLATILE);
     }
     return TCL_OK;
    }
    
int LastAction(ClientData clientData, Tcl_Interp *interp,
     int argc,CONST84 char *argv[])
     {
     ATermList sal = (ATermList) ATelementAt(history,1);
     int current = ATgetInt((ATermInt) ATelementAt(history,0)),i;
     for (i=0;i<current;i++) sal = ATgetNext(sal);
     {
     ATerm lastaction = ATelementAt((ATermList) ATgetFirst(sal),1);
     if (ATgetType(lastaction)==AT_INT) 
         Tcl_SetResult(interp, "init", TCL_VOLATILE);
     else {
         ATerm lastsummand =  ATelementAt((ATermList) ATgetFirst(sal),2);
         sprintf(buf, "%s [%d]",ATgetName(ATgetAFun(lastaction)),
                 ATgetInt((ATermInt) lastsummand)+1);
         Tcl_SetResult(interp, buf, TCL_VOLATILE);
     }
     }
    return TCL_OK;
    }

int Reset(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[])
    {
    stateno = reset;
    history = StartHistory();
#ifdef GRAPPA
    if (in) {
        putReset();
        putState(stateno);
        }
#endif  
    return TCL_OK;
    }

int Undo(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[])
    {
    ATermList sal = (ATermList) ATelementAt(history,1), salpt = sal;
    int current = ATgetInt((ATermInt) ATelementAt(history,0)),i;
    if (current>=ATgetLength(sal)-1) return TCL_ERROR;
    current++;
    for (i=0;i<current;i++) salpt = ATgetNext(salpt);
    stateno = ATgetInt((ATermInt) ATgetFirst((ATermList) ATgetFirst(salpt)));
    history = ATmakeList2(ATmake("<int>",current), (ATerm) sal);
#ifdef GRAPPA
    if (in) putState(stateno);
#endif
    if (current==ATgetLength(sal)-1) return TCL_ERROR;  /* To disable button */
    return TCL_OK;
    }
    
int Redo(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[])
    {
    ATermList sal = (ATermList) ATelementAt(history,1), salpt = sal;
    int current = ATgetInt((ATermInt) ATelementAt(history,0)),i;
    if (current<=0) return TCL_ERROR;
    current--;
    for (i=0;i<current;i++) salpt = ATgetNext(salpt);
    stateno = ATgetInt((ATermInt) ATgetFirst((ATermList) ATgetFirst(salpt)));
    history = ATmakeList2(ATmake("<int>",current), (ATerm) sal);
    /* fprintf(stderr, "Current = %d\n", current); */
#ifdef GRAPPA
    if (in) putState(stateno);
#endif
    if (current==0) return TCL_ERROR; /* To disable button */

    return TCL_OK;
    }
    
int Current(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[])
    {
    ATermList sal = (ATermList) ATelementAt(history,1);
    int current = ATgetInt((ATermInt) ATelementAt(history,0));
    sprintf(buf,"%d", current);
    Tcl_SetResult(interp, buf, TCL_VOLATILE);
    if (current==0 || current == ATgetLength(sal)-1) return TCL_ERROR;
    return TCL_OK; 
    }
    
int SaveTrace(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[])
    {
    static int cnt = 0;
    int current;
    char *dirname = (char*) argv[1];
    static char filename[80]; 
    FILE *fp;
    ATermList sal = (ATermList) ATelementAt(history,1),
    transitions = ATempty;
    sprintf(filename, "%s.trc", dirname);
    if (CreateEmptyDir(filename, DELETE_NONE)<0) 
         ATerror("Error in creation directory %s",filename);
    sprintf(filename+strlen(filename), "/%d", cnt++);
    fp = fopen(filename, "w");
    if (!fp) 
	{
	sprintf(buf,"Open for writing: %s",filename);
	Tcl_SetResult(interp, buf, TCL_VOLATILE);
	return TCL_ERROR;
	}
    sprintf(buf,"%s", filename);
    Tcl_SetResult(interp, buf, TCL_VOLATILE);
    fclose(fp);
    for (sal = ATgetNext(ATreverse(sal));!ATisEmpty(sal);sal=ATgetNext(sal)) {
        transitions = ATinsert(transitions, ATmake("t(<term>,<term>)",
            ATelementAt((ATermList) ATgetFirst(sal), 1),
            ATelementAt((ATermList) ATgetFirst(sal), 0)));
        }
    current = ATgetInt((ATermInt) ATelementAt(history,0));
    if (LTSsaveTrace(filename, ATreverse(transitions), current)) 
        return TCL_OK;
    return TCL_ERROR;
    }

int PrintTrace(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[])
    {
    char *filename = (char*) argv[1];
    FILE *fp = fopen(filename, "w");
    if (!fp) 
	{
	sprintf(buf,"Open for writing: %s",filename);
	Tcl_SetResult(interp, buf, TCL_VOLATILE);
	return TCL_ERROR;
	}
    sprintf(buf,"msg:Trace printed on: %s",filename);
    Tcl_SetResult(interp, buf, TCL_VOLATILE);
    {
    ATermList sal = (ATermList) ATelementAt(history,1), salpt = NULL;
    int current = ATgetInt((ATermInt) ATelementAt(history,0)),i; 
    for (i=0;!ATisEmpty(sal) && i<current ;sal = ATgetNext(sal), i++);
    sal = ATreverse(sal);
    salpt = ATgetNext(sal);
    for (;!ATisEmpty(salpt);salpt = ATgetNext(salpt))
	{
	ATermList rec = (ATermList) ATgetFirst(salpt);
	ATfprintf(fp, "%t\n", ATelementAt(rec, 1));
	}
    salpt = sal;
    /*
    for (;!ATisEmpty(salpt);salpt = ATgetNext(salpt))
	{
	ATermList rec = (ATermList) ATgetFirst(salpt);
	ATfprintf(fp, "%t\n", ATelementAt(rec, 0));
	}
    */
    }
    fclose(fp);
    return TCL_OK;
    }

int LoadTrace(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[]) {
    static char actname[1024];
    char *filename = (char*) argv[1];
    int actid = -1, i;
    ATermList sal = ATempty, salpt = ATempty;
    FILE *fp = fopen(filename, "r");
    if (!fp) 
	{
	sprintf(buf,"err: open for reading: %s",filename);
	Tcl_SetResult(interp, buf, TCL_VOLATILE);
	return TCL_ERROR;
	}
    states = actions = summands = ATmakeList0();
    reset = 0; stateno = 0;
    history = StartHistory();
    sal = (ATermList) ATelementAt(history, 1);
    newTraceFormat = ATfalse;
    for (i=0;fscanf(fp, "%d %s", &actid, actname)==2;i++) 
    if (i!=0 || actname[0]!='#')
        {
        ATermList r = DoStep(actid);
        char *s = r?ATgetName(ATgetAFun(ATelementAt(r, 1))):NULL;
        /* fprintf(stderr, "QQQ %s %s\n", actname, s); */
        if (!r || strcmp(s, actname)) {
           if (s)
           sprintf(buf,"Expected action \"%s\" != encountered action \"%s\"",
                actname, s?s:"deadlock");
           else
           sprintf(buf,"Expected action \"%s\" != encountered deadlock",
                actname);
	   Tcl_SetResult(interp, buf, TCL_VOLATILE);
	   return TCL_ERROR;
           }
        sal = ATinsert(sal, (ATerm) r);
        }
    else {newTraceFormat = ATtrue; fclose(fp); break;}
    if (newTraceFormat) {
        ATermList trace = LTSgetTrace(filename, &actid); 
        if (!trace) return TCL_ERROR;
        /* ATfprintf(stdout, "QQQ trace = %t\n", trace); */
        for (;!ATisEmpty(trace);trace = ATgetNext(trace)) {
          int stateval = ATgetInt((ATermInt) ATgetArgument((ATermAppl)
              ATgetFirst(trace), 1));
          ATerm action = MCRLprint(ATgetArgument((ATermAppl)ATgetFirst(trace), 0));
           ATermList r = DoStepState(stateval);
           sprintf(actname,"\"%s\"", ATwriteToString(action));
             if (r) {
                ATerm s = ATelementAt(r, 1);
                if (strcmp(actname, ATwriteToString(s))) {
                sprintf(buf,"Expected action %s != encountered action %s",
                              actname, ATwriteToString(s));
                Tcl_SetResult(interp, buf, TCL_VOLATILE);
	        return TCL_ERROR;
                }
                }
             else {
                sprintf(buf,"Expected action \"%s\" != encountered deadlock",
                  ATwriteToString(action));
                Tcl_SetResult(interp, buf, TCL_VOLATILE);
	        return TCL_ERROR;
             }
           sal = ATinsert(sal, (ATerm) r);  
           }
        }
     /* actid plays the role of  current */
     
    if (actid<0 || actid >= ATgetLength(sal)) {
       sprintf(buf,"Illegal format of trace file");
       Tcl_SetResult(interp, buf, TCL_VOLATILE);
       return TCL_ERROR;
       }
    for (i=0, salpt = sal;i<actid;i++) salpt = ATgetNext(salpt);
    stateno = ATgetInt((ATermInt) ATgetFirst((ATermList) ATgetFirst(salpt)));
    history = ATmakeList2((ATerm) ATmakeInt(actid), (ATerm) sal);
    sprintf(buf,"%d",ATgetLength(sal));
    Tcl_SetResult(interp, buf, TCL_VOLATILE);
#ifdef GRAPPA
    if (in) {
       putReset();
       putState(stateno);
       }
#endif
    return TCL_OK;
    }
     
static void Protect()
    {
    ATprotect((ATerm *) &states);
    ATprotect((ATerm *) &actions);
    ATprotect((ATerm *) &summands);
    ATprotect((ATerm *) &history);
    ATprotect(&trm0);
    trm0= ATmake("<int>",0);
    }
    
int ReleaseFiles(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[])
     {
     if (erf) 
          {
          fclose(erf);
          RemoveFile(filename);
          }

     return TCL_OK;
     }
     
int EndStateView(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[])
     {
#ifdef GRAPPA
    if (in) putFinish();
#endif
     return TCL_OK;
     }

int PutState(ClientData clientData, Tcl_Interp *interp,
	int argc,CONST84 char *argv[])
     {
#ifdef GRAPPA
    if (!in) return TCL_OK;
    putState(stateno);
#endif
    return TCL_OK;
    }

void SIMhelp(ATbool all)
{
	LTShelp();
	if ( all )
	{
		RWhelp();
		MCRLhelp();
	}
}
