/* $Id: rw.c,v 1.9 2006/06/23 15:03:16 bertl Exp $ */
 
extern TASKS JITTYtasks, SUBStasks;
#ifdef DYNLINK
extern TASKS RWWtasks, RWtasks;
#endif

static TASKS *tasks = NULL;

void RWhelp(void) {
     Pr("General options of the REWRITER are:");
     Pr("-no-hash:\t\tno hash tables are used during rewriting");
     Pr("-hash:\t\t\tuses hash tables during rewriting (default)");
     Pr("-case:\t\t\tuses implicit distribution rules on case functions."); 
     Pr("\t\t\tRecommended after structelm.");
     Pr("-alt <rewriter>:\t<rewriter> stands for the rewriter which will be used.");
     Pr("\t\t\tThe following rewriters are available:");
     Pr("\t\t\t\"jitty\"\tuses interpreting rewriter with just in time rewriting strategy");
     Pr("\t\t\t\"innermost\"\tuses interpreting rewriter with innermost strategy");
     Pr("\t\t\t\"no\"\t\tuses only substitution mechanism (no rewriter)");
#ifdef DYNLINK
     Pr("\t\t\t\"rww\"\t\tuses the old compiling rewriter (innermost, however");
     Pr("\t\t\t\t\tthe case functions will be evaluated with jitty strategy)"); 
     Pr("\t\t\t\"rw\"\t\tuses the recent compiling rewriter (10%s faster than rww)","%"); 
#endif
     Pr("Default the interpreting rewriter will be used with jitty strategy,");
#ifdef DYNLINK
     Pr("except for the instantiator (default the recent compiling rewriter).");
     Pr("");
     RWtasks.RWhelp();
#endif 
     JITTYtasks.RWhelp();
     }
     
static ATermTable norm = NULL;
ATerm RWrewrite(ATerm t);

static ATbool caseFlag = ATfalse;

static RWREWRITE rewrite;
static RWREWRITELIST rewritelist;
            
void RWsetArguments(int *argc, char ***argv) {
     int i, j=0;
     char **newargv = (char**) calloc(*argc + 3, sizeof(char*));
     if (!newargv) ATerror("Cannot allocate array argv");
     newargv[j++] = (*argv) [0];
     for(i=1;i<*argc;i++) {
       if (!strcmp((*argv)[i],"-alt")) {
            if ((++i)<*argc && strncmp((*argv)[i],"-",1))
                {
                char *code = (*argv)[i];
                if (!strcmp(code,"innermost")) {
		  tasks = &JITTYtasks;
		  newargv[j++]="-innermost";
		  ATwarning("-alt innermost is obsolete; please use -alt jitty -innermost instead");
		}
		else if (!strcmp(code,"strictleft")) {
		  tasks = &JITTYtasks;
		  newargv[j++]="-strictleft";
		  ATwarning("-alt strictleft is obsolete; please use -alt jitty instead");
		}
	        else if (!strcmp(code,"jitty")) {
		  tasks = &JITTYtasks;
		}
	        else if (!strcmp(code,"no")) {
		  tasks = &SUBStasks;
		}
#ifdef DYNLINK
                else
                if (!strcmp(code,"rww")) tasks = &RWWtasks;
                else if (!strcmp(code,"rw")) { 
                  tasks = &RWtasks;
                  }   
#endif
                else
                if (!strcmp(code,"rww"))
                   ATwarning("Compiling rewriter is not available");
                else
                ATerror("Unknown rewriter or strategy");
                continue;
                }
            ATerror("Option %s needs argument.\n",(*argv)[i-1]);
            }
       if (!strcmp((*argv)[i],"-case")) { 
#ifdef DYNLINK
            if (!tasks) tasks = &RWWtasks;     
#endif        
            caseFlag = ATtrue;
#ifdef DYNLINK
            if (tasks != &RWWtasks && tasks != &RWtasks) continue;
#else
            continue;
#endif
	    }
	   j=MCRLcopyOption(newargv, *argv, *argc, i, j);
        }
        if (!tasks) {
	  tasks = &JITTYtasks;
	}
        *argc = j;  *argv = newargv;
        tasks->RWsetArguments(argc, argv);
     }
     
void SUsetArguments(int *argc, char ***argv) {
     tasks = &SUBStasks;
     tasks->RWsetArguments(argc, argv);
     }

static ATerm CaseRewrite(ATerm t);

static ATerm CaseRewriteStep(ATerm t) {
     ATerm result;
     do {
         result = t;
         t = tasks->RWrewrite(MCRLcaseDistribution(CaseRewrite, result));
         }
     while (!ATisEqual(t, result));
     return result;
     }
     
static ATerm CaseRewrite(ATerm t) {
     AFun f = ATgetAFun(t);
     int n = ATgetArity(f);
     ATerm u;
     // ATwarning("%t", t);
     if (n==0) return tasks->RWrewrite(t);
     u = ATtableGet(norm, t);
     if (u) return u;
     {
     int i; 
     ATerm *a = calloc(n, sizeof(ATerm));
     ATbool changed = ATfalse; 
     ATprotectArray(a, n);
     for (i=0;i<n;i++) {
        ATerm arg = ATgetArgument((ATermAppl) t, i);
        a[i] = CaseRewrite(arg);
        if (!ATisEqual(a[i], arg)) changed = ATtrue;
        }
     u = CaseRewriteStep(changed?(ATerm) ATmakeApplArray(f, a):t);
     ATtablePut(norm, t, u);
     ATunprotect(a); free(a);
     return u;        
     }
     }
          
static ATermList CaseRewriteList(ATermList ts) {
     ATermList r = ATempty; 
     for (;!ATisEmpty(ts);ts=ATgetNext(ts)) {
         ATerm t = ATgetFirst(ts);
         r = ATinsert(r, CaseRewrite(t));
         }
     return ATreverse(r); 
     }
          
ATbool RWinitialize(ATerm adt) {
     if (!caseFlag 
#ifdef DYNLINK
     || tasks == &RWWtasks || tasks == &RWtasks
#endif
     ) {
         rewrite = tasks->RWrewrite;
         rewritelist = tasks->RWrewriteList;
         }
     else {
         rewrite = CaseRewrite;
         rewritelist = CaseRewriteList;
         norm = ATtableCreate(100, 50); 
         }
     return tasks->RWinitialize(adt);
     }
     
ATbool SUinitialize(ATerm adt) {
     rewrite = tasks->RWrewrite;
     rewritelist = tasks->RWrewriteList;
     return tasks->RWinitialize(adt);
     }
          
void RWassignVariable(AFun var, ATerm t, ATerm tsort, int level) {
     if (norm) ATtableReset(norm);
     tasks->RWassignVariable(var, t, tsort, level);
     }
     
ATerm RWgetAssignedVariable(AFun var) {
     return tasks->RWgetAssignedVariable(var);
     }
     
void RWresetVariables(int level) {
     tasks->RWresetVariables(level);
     }
     
void RWdeclareVariables(ATermList variable_names) {
     if (ATisEmpty(variable_names)) return;
     tasks->RWdeclareVariables(variable_names);
     if (!currentAdt) return;
     if (ATgetArity(ATgetAFun(ATgetFirst(variable_names)))==0)
         MCRLdeclareVarNames(variable_names);
     else
         MCRLdeclareVars(variable_names);
     }
     
ATerm RWrewrite(ATerm t) {
     return rewrite(t);
     }
     
ATermList RWrewriteList(ATermList l) {
     return rewritelist(l);
     }
     
void RWsetAutoCache(ATbool b) {
     if (tasks->RWsetAutoCache) tasks->RWsetAutoCache(b);
     }
      
void RWflush(void) {
     if (norm) ATtableReset(norm);
     if (tasks->RWflush) tasks->RWflush();
     }                              

static ATbool RWisRewriterNeeded(void) {
     return tasks!=NULL && tasks != &SUBStasks;
     }
