/* $Id: svcupdate.c,v 1.5 2007/02/19 16:01:38 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#ifdef SVC


#include <stdio.h>
#include "rw.h"
#include "svc.h"
#include "svcerrno.h"
/*#include <ctype.h>*/
#include <stdlib.h>
#define DB_SIZE 256

static ATermList ParseFile(FILE *f);

typedef struct {
     ATerm lhs, rhs, lhs2, rhs2;
     ATerm* cond;
     AFun  header;
     int len;
     } match_t;

typedef struct {
     ATerm *ar;
     } db_t;
     
static db_t db;
    
static match_t *match;
static ATermList protect = NULL;
    
static char *who = "svcupdate";
static FILE *editfile = NULL;

static int match_size, cnt =0,   monitor = 0, npars, changed=0;

static char *inFilename=NULL, *outFilename=NULL, buf[256];
static SVCbool indexed;
static SVCfile inFile, outFile;
static SVCstateIndex fromState, toState;
static SVClabelIndex label;
static SVCparameterIndex parameter;
     
static void WarningHandler(const char *format, va_list args)
     {
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
     
static void helpmsg(ATbool all) {
    Pr("Usage: svcupdate [options] <input>.svc <output>.svc");
    Pr("The following options can be used");
    Pr("-help:\t\tyields this message");
    Pr("-version:\tgets the version number of this release");
    Pr("-edit <file>:\tThis flag is obligatory.");
    Pr("\t\t<file> contains the conditional substitution rules.");
    Pr("\t\tThe format of a rule is:");
    Pr("\t\t<match_action_term>'->'<new_action_term> ['<|'<condition_terms>]");
    Pr("\t\t<condition_terms>::=<condition_term> ('&'<condition_term>)*");
    Pr("\t\t<condition_term>::=<matching variable>'='<term>");
    Pr("\t\tMatching variables are named  #1, #2, ...");
    Pr("\t\tThe matched subterms will be assigned");
    Pr("\t\tto them in the matching phase. These variables can be used in");
    Pr("\t\t<new_action_term>. The first encountered match will be applied.");
    Pr("\t\tCondition_terms have the following format: #<pos>=<term>");
    Pr("\t\t<pos> is the position number of <term> in the state vector");
    Pr("-monitor:\tdisplays updates during run");
    } 
        
static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("Renaming of actions directed by conditional substitution rules.");
    Pr("The updated \".svc\" file will be written on the file named in the");
    Pr("last argument.");
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    exit(EXIT_SUCCESS);
    }
        
static void version(void)
    {
    char buf[100];
    sprintf(buf,"%s: version %s",who, VERSION);
    Pr(buf);
    }


static AFun ATerm2Symbol(ATerm t) {
    AFun s = ATgetAFun(t);
    int n = ATgetArity(s), m = 0, i;
    if (n==0) return s;
    {
    DECLA(AFun, a, n);
    for ((m=strlen(ATgetName(s))+3+n),i=0;i<n;i++) {
         a[i] = ATerm2Symbol(ATgetArgument((ATermAppl)t, i));
         m+=strlen(ATgetName(a[i]));
         }
    {
    DECLA(char, b, m);
    strcpy(b,ATgetName(s)); 
    strcat(b,"(");
    for (i=0;i<n;i++) { 
        if (i>0) strcat(b,",");
        strcat(b, ATgetName(a[i]));
        }
    strcat(b,")");
    return ATmakeAFun(b, 0, ATtrue);
    }
    }
    }

static ATerm ATerm2ATerm(ATerm t) {
    AFun s = ATgetAFun(t);
    char *c = ATgetName(s);
    int n = ATgetArity(s), i;
    if (c[0]=='#') {
         int m = strlen(c), d;
         for (i=1;i<m && isdigit(c[i]);i++); 
         if (n>0 || i<m || (d=atoi(c+1))<=0 || d>DB_SIZE) 
              ATerror("Illegal substitution variable %t", t);
          return (ATerm) ATmakeInt(d-1);
          }
    {
    DECLA(ATerm, a, n);
    for (i=0;i<n;i++) a[i] = ATerm2ATerm(ATgetArgument((ATermAppl) t, i));
    s = ATmakeAFun(c, n, ATfalse);
    return (ATerm) ATmakeApplArray(s, a);
    }
    }

static int Arity(char *s) {
    int d = 0, n = 0;
    for (;s;s = strpbrk(s+1,",()")) {
    switch (*s) {
       case '(': d++; break;
       case ')': d--; if (d==0) return n+1; break;
       case ',': if (d==0) return 0; 
                 if (d==1) n++; 
		 break;
       }
     }
    return n;
    }
    
static ATerm String2ATerm(char *s) {
    char *t = s, *q = s;
    // fprintf(stderr,"s= %s\n", s);
    s = strpbrk(s,",()");
    if (!s) return (ATerm) ATmakeAppl0(ATmakeAFun(t, 0, ATfalse));
    {
    int n = Arity(s), d  = 0, i= 0;
    AFun f;
    DECLA(ATerm, a, n);
    for (;1;t=s+1, s=strpbrk(t,",()")) {
    switch (*s) {
       case ',': if (d==1) {
                     *s = 0;
                     a[i++] = String2ATerm(q);
                     q = s+1;
                     } 
                 break;    
       case '(': if (d==0) {
                    *s = 0;
                    f = ATmakeAFun(t, n, ATfalse);
                    // ATfprintf(stderr,"f= %a %d\n", f, n);
                    q = s+1;
                    }
                 d++; 
		 break;
       case ')': d--;
                 if (d==0) {
		     *s=0; 
		     a[i++] = String2ATerm(q);
		     return (ATerm) ATmakeApplArray(f, a);
		     }
		 break;
       }
     }     
    }
    }

static int NumberOfLeftVars(ATerm t) {
    int d = 0, i, n;
    if (ATgetType(t)==AT_INT) {
        char buf[80];
        int v = ATgetInt((ATermInt) t);
        sprintf(buf,"#%d", v+1);
        if (db.ar[v]) 
            ATerror("Duplicate matching variable in lhs: %s", buf);
        db.ar[v] = t;
        return 1;
        }
    n = ATgetArity(ATgetAFun(t));
    for (i=0;i<n;i++) d+= NumberOfLeftVars(ATgetArgument((ATermAppl) t, i));
    return d;
    }
    
static int NumberOfRightVars(ATerm t) {
    int d = 0, i, n;
    if (ATgetType(t)==AT_INT) {
        char buf[80];
        int v = ATgetInt((ATermInt) t);
        sprintf(buf,"#%d", v+1);
        if (!db.ar[v]) 
        ATerror("Illegal matching variable in rhs: %s", buf);
        db.ar[v] = t;
        return 1;
        }
    n = ATgetArity(ATgetAFun(t));
    for (i=0;i<n;i++) d+= NumberOfRightVars(ATgetArgument((ATermAppl) t, i));
    return d;
    }
        
static void CheckLeftVars(match_t  *mch) {
    int cnt, i;
    memset(db.ar, 0, DB_SIZE*sizeof(ATerm));
    cnt  = NumberOfLeftVars(mch->lhs2);
    for (i=0;i<cnt;i++) 
    if (!db.ar[i]) {
        char buf[80];
        sprintf(buf,"#%d", i+1);
        ATerror("Matching variable %s is missing", buf);
        }
    }
    
static ATerm ATerm2Int(ATerm t) {
     int i, n, d;
     char *c = ATgetName(ATgetAFun(t));
     for (i=1, n = strlen(c);i<n && isdigit(c[i]);i++); 
         if (c[0]!='#' || i<n || (d=atoi(c+1))<=0 || d>npars) 
              ATerror("Illegal position %s", c);
     return (ATerm) ATmakeInt(d-1);
     }
     
static ATerm ATerm2String(ATerm action) {
      return (ATerm) ATmakeAppl0(ATmakeAFun(ATwriteToString(action), 0,
      ATtrue));
      }
                           
static void FillTable(ATermList ts) {
    int i = 0;
    db.ar = (ATerm*) calloc(DB_SIZE, sizeof(ATerm));
    ATprotectArray(db.ar, DB_SIZE);
    match_size = ATgetLength(ts);
    match = calloc(match_size, sizeof(match_t));
    if (!match) ATerror("Cannot allocate match (%d)", match_size);
    for (i=0;!ATisEmpty(ts);ts=ATgetNext(ts), i++) {
        ATerm t  = ATgetFirst(ts);
        int n = ATgetArity(ATgetAFun(t))-2, j;
        match[i].lhs = (ATerm) ATmakeAppl0(
                          ATerm2Symbol(ATgetArgument((ATermAppl) t, 0)));
        match[i].rhs = (ATerm) ATmakeAppl0(
                          ATerm2Symbol(ATgetArgument((ATermAppl) t, 1)));
	match[i].lhs2 = ATerm2ATerm(ATgetArgument((ATermAppl) t, 0));
        CheckLeftVars(match+i);
	match[i].rhs2 = ATerm2ATerm(ATgetArgument((ATermAppl) t, 1));
        NumberOfRightVars(match[i].rhs2);
	match[i].header = ATgetAFun(match[i].lhs2);
	ATprotect(&match[i].lhs);
	ATprotect(&match[i].rhs);
	ATprotect(&match[i].lhs2);
	ATprotect(&match[i].rhs2);
        match[i].len = n;
        if (n>0 &&  SVCgetIndexFlag(&inFile)) 
           ATerror(
        "Not permitted to use updating conditions at indexed SVC file"
        );
        if (n>0) {
           match[i].cond = malloc(n*sizeof(ATerm));
           for (j=0;j<n;j++) match[i].cond[j] = 
           j%2?ATerm2ATerm(ATgetArgument((ATermAppl) t, j+2)):
               ATerm2Int(ATgetArgument((ATermAppl) t, j+2)); 
           }
        }
    }
    
static ATbool Match(ATerm p, ATerm t) {
    int i, n;
    if (ATgetType(p)==AT_INT) {
         db.ar[ATgetInt((ATermInt) p)] = t;
         return ATtrue; 
         }
    if ((n=ATgetArity(ATgetAFun(p)))!=ATgetArity(ATgetAFun(t))) 
       return ATfalse;
    for (i=0;i<n;i++)  
    if (!Match(ATgetArgument((ATermAppl) p, i),
                          ATgetArgument((ATermAppl) t, i))) 
                return ATfalse;
    if (ATgetAFun(p)==ATgetAFun(t)) return ATtrue;
    return ATfalse;
    }
    
static ATerm Subs(ATerm t) {
     int n;
     if (ATgetType(t)==AT_INT) 
       return db.ar[ATgetInt((ATermInt) t)];
     if ((n=ATgetArity(ATgetAFun(t)))==0) return t;
     {
     int i;
     DECLA(ATerm, b, n);
     for (i=0;i<n;i++) {
          b[i] = Subs(ATgetArgument((ATermAppl) t, i)); 
          }
     return (ATerm) ATmakeApplArray(ATgetAFun(t), b);
     }
     }


        
static ATbool IsEqual(match_t *match, ATerm state, int i) {    
     ATerm dt = match->cond[i], t = match->cond[i+1],
     s = ATgetType(state)==AT_LIST?ATelementAt((ATermList) state, 
          ATgetInt((ATermInt) dt)): state;
     if (ATisEqual(s,t)) return ATtrue;
     if (ATgetType(s)==AT_INT) {
         int i, n;
         char *c = ATgetName(ATgetAFun(t));
         for (n=strlen(c), i=0;i<n && isdigit(c[i]);i++);
          if (i==n && atoi(c)==ATgetInt((ATermInt) s)) return ATtrue;
         }
     return ATfalse;
     }
     
static ATerm NewAction(match_t *match, ATerm action, ATerm state)  {
    int i;
    if (strncmp(ATgetName(match->header),
                ATgetName(ATgetAFun(action)),strlen(ATgetName(match->header)))) 
        return NULL;
    for (i=0;i<match->len;i+=2)
       if (!IsEqual(match, state, i)) return NULL;
    if (ATgetArity(ATgetAFun(action))==0 && ATisEqual(action, match->lhs)) return match->rhs;
    // ATfprintf(stderr,"Before %t\n", action);
    action = String2ATerm(strdup(ATgetName(ATgetAFun(action))));
    // ATfprintf(stderr,"After %t\n", action);
    if (!Match(match->lhs2, action)) return NULL;
    return ATerm2String(Subs(match->rhs2));
    } 
       
ATerm UseFirstMatchingRule(ATerm action, ATerm state) {
     int i;
     /* ATwarning("UseFirstMatchingRule:%t", action); */
     for (i=0;i<match_size;i++) {
        ATerm t = NewAction(match+i, action, state); 
        if (t!=NULL) {
             if (monitor) ATwarning("Line %d rule %d: %t->%t",
                  cnt+1, i, action, t);
             changed++;
             return t;
             }
         }
     return action;
     }
    
static ATerm Action(ATerm actname, ATermList  actargs) {
      return 
      (ATerm) ATmakeApplList(
      ATmakeAFun(ATgetName(ATgetSymbol(actname)),ATgetLength(actargs), ATtrue),
      actargs);
      }         

static void InitTransitionSVC(void) {
     SVCbool _new;
     ATerm initState = 
         SVCstate2ATerm(&inFile, SVCgetInitialState(&inFile));
     npars = SVCnumParameters(&inFile);
     SVCsetCreator(&outFile , who);
     SVCsetVersion(&outFile , VERSION);
     SVCsetInitialState(&outFile ,SVCnewState(&outFile, initState, 
     &_new));
     }
                          
int main(int argc, char *argv[]) {
    int i;
    SVCbool  _new;
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    ATinit(argc, argv, (ATerm*) &argc);
    for (i=1;i<argc;i++) {
    help(argv[i]);
    if (!strcmp(argv[i],"-version")) {
	version();
	exit(0);
	}
    }
    if (argc<3 || argv[argc-2][0]=='-' || argv[argc-1][0]=='-' ||
    !strrchr(argv[argc-2],'.') ||  !strrchr(argv[argc-1],'.') || 
    strcmp(strrchr(argv[argc-2],'.'),".svc") ||
    strcmp(strrchr(argv[argc-1],'.'),".svc")) ATerror(
    "Last two arguments must be \"<input>.svc\" and \"<output>.svc\"");
    inFilename = argv[argc-2]; outFilename = argv[argc-1];
    for (i=1;i<argc;i++) {
    if (!strcmp(argv[i],"-monitor")) {
	monitor = 1;
	continue;
	}
    if (!strcmp(argv[i],"-edit")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *name = argv[i];
                if (editfile) ATerror("flag -edit already present");
                editfile = fopen(name,"r");
                if (!editfile) ATerror("Cannot open file %s", name);
                continue;
                }
            ATerror("Option %s needs argument.\n",argv[i-1]);
            }
    }
    if (!editfile) {
            help("help");
            ATerror("Flag -edit <file_name> must be present");
            }
    if (SVCopen(&inFile, inFilename, SVCread, &indexed) <0) {
        sprintf(buf,"%s: %s", inFilename, SVCerror(SVCerrno));
        ATerror(buf); 
        }
    /*
    if (indexed==1) {
        sprintf(buf, "\"%s\" must contain state vectors", inFilename);
        ATerror(buf);
        }
    */
    if (SVCopen(&outFile, outFilename, SVCwrite, &indexed)<0) {
        sprintf(buf,"%s: %s", outFilename, SVCerror(SVCerrno));
        ATerror(buf); 
        }         
    ATprotect((ATerm*) &protect);
    protect = ParseFile(editfile);
    InitTransitionSVC();
    FillTable(protect);
    while (SVCgetNextTransition(
          &inFile, &fromState, &label, &toState, &parameter)) {
          ATerm from = SVCstate2ATerm(&inFile,fromState), 
                action = SVClabel2ATerm(&inFile,label), 
                to = SVCstate2ATerm(&inFile,toState),
                par = SVCparameter2ATerm(&inFile, parameter),
                newaction = NULL;
          fromState=SVCnewState(&outFile, from , &_new);
          toState=SVCnewState(&outFile, to, &_new);
          newaction = UseFirstMatchingRule(action, from);
          label=SVCnewLabel(&outFile, newaction, &_new);
          parameter=SVCnewParameter(&outFile, par, &_new);
          SVCputTransition(&outFile, fromState, label, toState, parameter);
          cnt++; 
          }                                       

   if (SVCclose(&inFile)<0){
      fprintf(stderr, "File trailer corrupt...\n");
      return -1;
      }
   if (SVCclose(&outFile)<0) {
      fprintf(stderr, "Write error during closing\n");
      return -1;
      }
    if (1) {
        ATwarning("Number of transitions: %d", 
            SVCnumTransitions(&outFile));
        ATwarning("Number of changed transitions: %d", changed);
        }
    exit(EXIT_SUCCESS); 
    }
    
#include "edit.h"

#else
int main(int argc, char *argv[]) {
    fprintf(stderr,"The SVC library is not available\n");
    }
#endif
