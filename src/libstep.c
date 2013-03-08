
/* $Id: libstep.c,v 1.9 2008/10/29 08:43:07 uid526 Exp $ */
#include "rw.h"
#include "step.h"
#include <string.h>
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#define NOTOCCURS -10000

#define BUFLEN 1024



static char buf[BUFLEN];

static int *frek = NULL, nSummands;
static int maxnodes = 10000, nodecnt = 0;

static ATerm *cond; 
static ATbool abstract = ATfalse, optimize = ATfalse, argSet = ATfalse,
sumelm = ATtrue;
// static ST_ORDER  order = enumOccurrenceOrdering;
static ST_ORDER  order = noOrdering;

typedef struct
     {
     ATerm actname;
     ATermList actargs, sumvars;
     ATermList state, nextstate;
     ATerm cond, cond0;
     }  GLOBAL;
     
typedef struct
   {
   Symbol name, val, sort;
   ATerm valterm;
   int n;
   } SVAR;
typedef struct {
     int n, *v;
     } SMD;
     
static SMD *smds = NULL; 
    
typedef struct {
     int n, k, *v;
     } POS; 
      
typedef struct nodestruct {
     /* ATerm t; */
     int nsmd, *smds;
     ATermIndexedSet db;
     struct nodestruct *nodes;
     int nnode;
     } NODEREC, *NODE; 
     
static POS pos;
static NODE toptree;
static float number_of_summands = 0;
         
typedef struct
     {
     ATerm actname;
     ATermList actargs, sumvars, procargs;
     ATerm cond;
     int nSumvars;
     SVAR *sumvar;
     } SUMMAND;
      
typedef struct
     {
     Symbol locvar, sumvar;
     } QUEUE;

static QUEUE *q;
              
static GLOBAL g;

static SUMMAND *summand = NULL;
     
static int newvarpt = 0, nPars = 0, smd_index=0,
max_enum = 2500; 
static char *varstring = "#v";
static ATermTable db_hash = NULL;
static ATbool first = ATtrue;
#define ERRORLENGTH 1024
#define NREC 10000
#define MAXARGS 60

static ATerm *systemLabel, *systemDest, *currentSource;
static ATerm *userLabel, *userDest, *systemSource;
static STcallback systemCallback;
static STcallback userCallback;
static ATermList pars = NULL;
static ATerm *newvar = NULL;


/* begin confluence reduction.
 */

static ST_REDUCING CRreducing = noReducing;

static ATermTable repr_map = NULL;
static ATermList next_list = NULL;
static ATermList label_list = NULL;
static ATerm confluent_action=NULL;
static ATerm conf_label=NULL;

static int confluence_states_explored=0;
static int confluence_states_generated=0;
static int confluence_transitions_explored=0;
static int confluence_transitions_generated=0;

static void ConfluenceStatistics(){
	ATwarning("Confluence reduction explored %d states and %d transitions",confluence_states_explored,confluence_transitions_explored);
	ATwarning("Confluence reduction generated %d states and %d transitions",confluence_states_generated,confluence_transitions_generated);
}

static ATerm Fold(ATerm *vector,int ofs,int len){
	if (len==1) return vector[ofs];
	else {
		int half=len>>1;
		return (ATerm) ATmakeAppl2(MCRLsym_pair, Fold(vector,ofs,half),Fold(vector,ofs+half,len-half));
	}
}

static void Unfold(ATerm *vector,int ofs,int len,ATerm folded){
	if (len==1) {
		vector[ofs]=folded;
	} else {
		int half=len>>1;
		Unfold(vector,ofs,half,ATgetArgument(folded,0));
		Unfold(vector,ofs+half,len-half,ATgetArgument(folded,1));
	}
}

static void listWriterCallback(void){
	next_list=ATinsert(next_list,Fold(systemDest,0,nPars));
	label_list=ATinsert(label_list,conf_label);
}

static ATbool confluentSubset(ATerm l){
	return ATisEqual(l,MCRLterm_tau_c);
}

static ATbool otherSubset(ATerm l){
	return !ATisEqual(l,MCRLterm_tau_c);
}

ATermInt min2(ATermInt t1,ATermInt t2){
	return (ATgetInt(t1)<ATgetInt(t2))?(t1):(t2);
}


static ATermList confluent_transitions(ATerm state) {
	next_list=ATmakeList0();
	label_list=ATmakeList0();
	Unfold(systemSource,0,nPars,state);
	if (STstepSubset(systemSource,confluentSubset)<0) ATerror("Error in confluent_transitions");
	confluence_states_explored++;
	confluence_transitions_generated+=ATgetLength(next_list);
	return next_list;
}

static ATerm find_tarjan(ATerm state) {
	ATerm result,current,newstate;
	ATermInt zero;
	ATermTable number;
	ATermTable unexplored;
	ATermTable backtrack;
	ATermTable low;
	ATermList todo,transition_list;
	int count=0;

	number=ATtableCreate(1024,75);
	unexplored=ATtableCreate(1024,75);
	backtrack=ATtableCreate(1024,75);
	low=ATtableCreate(1024,75);
	current=state;
	state=0;
	zero=ATmakeInt(0);
	ATtablePut(number,current,(ATerm)zero);
	for(;;){
		if ((ATermInt)ATtableGet(number,current)==zero) {
			count++;
			ATtablePut(number,current,(ATerm)ATmakeInt(count));
			ATtablePut(low,current,(ATerm)ATmakeInt(count));
			transition_list=confluent_transitions(current);
			ATtablePut(unexplored,current,(ATerm)transition_list);
			result=0;
			for(;!ATisEmpty(transition_list);transition_list=ATgetNext(transition_list)) {
				newstate=ATgetFirst(transition_list);
				if (!ATtableGet(number,newstate))
					ATtablePut(number,newstate,(ATerm)zero);
				if (!result) result=ATtableGet(repr_map,newstate);
			}
			if (result) break;
		}
		transition_list=(ATermList)ATtableGet(unexplored,current);
		if (ATisEmpty(transition_list)) {
			if (ATtableGet(number,current)==ATtableGet(low,current)) {
				result=current;
				break;
			}
			newstate=ATtableGet(backtrack,current);
			ATtablePut(low,newstate,(ATerm)min2((ATermInt)ATtableGet(low,current),
							    (ATermInt)ATtableGet(low,newstate)));
			current=newstate;
		} else {
			newstate=ATgetFirst(transition_list);
			confluence_transitions_explored++;
			ATtablePut(unexplored,current,(ATerm)ATgetNext(transition_list));
			if (((ATermInt)ATtableGet(number,newstate))==zero) {
				ATtablePut(backtrack,newstate,current);
				current=newstate;
			} else if (ATgetInt((ATermInt)ATtableGet(number,newstate))<
					ATgetInt((ATermInt)ATtableGet(number,current))) {
				ATtablePut(low,current,(ATerm)min2((ATermInt)ATtableGet(low,current),
								   (ATermInt)ATtableGet(low,newstate)));
			}
		}
		
	}
	for(todo=ATtableKeys(number);!ATisEmpty(todo);todo=ATgetNext(todo)){
		if(!ATtableGet(repr_map,ATgetFirst(todo))){
			confluence_states_generated++;
			ATtablePut(repr_map,ATgetFirst(todo),result);
		}
	}
	ATtableDestroy(number);
	ATtableDestroy(backtrack);
	ATtableDestroy(unexplored);
	ATtableDestroy(low);
	return result;
}


static ATerm find_repr(ATerm state) {
	ATerm result;
	if ((result=ATtableGet(repr_map,state))) return result;
	return find_tarjan(state);
}

static ATerm min2states(ATerm s1,ATerm s2){
	return (ATcompare(s1,s2)<0)?s1:s2;
}

static ATerm find_new_repr(ATerm state) {
	ATerm result,current,newstate;
	ATermInt zero;
	ATermTable number;
	ATermTable unexplored;
	ATermTable backtrack;
	ATermTable low;
	ATermTable least;
	ATermList transition_list;
	int count=0;

	number=ATtableCreate(1024,75);
	unexplored=ATtableCreate(1024,75);
	backtrack=ATtableCreate(1024,75);
	low=ATtableCreate(1024,75);
	least=ATtableCreate(1024,75);
	current=state;
	state=0;
	zero=ATmakeInt(0);
	ATtablePut(number,current,(ATerm)zero);
	confluence_states_generated++;
	for(;;){
		if ((ATermInt)ATtableGet(number,current)==zero) {
			count++;
			ATtablePut(number,current,(ATerm)ATmakeInt(count));
			ATtablePut(low,current,(ATerm)ATmakeInt(count));
			ATtablePut(least,current,current);
			transition_list=confluent_transitions(current);
			ATtablePut(unexplored,current,(ATerm)transition_list);
			for(;!ATisEmpty(transition_list);transition_list=ATgetNext(transition_list)) {
				newstate=ATgetFirst(transition_list);
				if (!ATtableGet(number,newstate))
					ATtablePut(number,newstate,(ATerm)zero);
					confluence_states_generated++;
			}
		}
		transition_list=(ATermList)ATtableGet(unexplored,current);
		if (ATisEmpty(transition_list)) {
			if (ATtableGet(number,current)==ATtableGet(low,current)) {
				result=current;
				break;
			}
			newstate=ATtableGet(backtrack,current);
			ATtablePut(low,newstate,(ATerm)min2((ATermInt)ATtableGet(low,current),
							    (ATermInt)ATtableGet(low,newstate)));
			ATtablePut(least,newstate,(ATerm)min2states(ATtableGet(least,current),
							    ATtableGet(least,newstate)));
			current=newstate;
		} else {
			newstate=ATgetFirst(transition_list);
			confluence_transitions_explored++;
			ATtablePut(unexplored,current,(ATerm)ATgetNext(transition_list));
			if (((ATermInt)ATtableGet(number,newstate))==zero) {
				ATtablePut(backtrack,newstate,current);
				current=newstate;
			} else if (ATgetInt((ATermInt)ATtableGet(number,newstate))<
					ATgetInt((ATermInt)ATtableGet(number,current))) {
				ATtablePut(low,current,(ATerm)min2((ATermInt)ATtableGet(low,current),
								   (ATermInt)ATtableGet(low,newstate)));
			}
		}
		
	}
	result=ATtableGet(least,result);
	ATtableDestroy(number);
	ATtableDestroy(backtrack);
	ATtableDestroy(unexplored);
	ATtableDestroy(low);
	ATtableDestroy(least);
	return result;
}


void CRRhelp(void) {
    Pr("-confluent <action>");
    Pr("-conf-table <action>");
    Pr("-conf-compute <action>");
    Pr("\t\t\tset action as the confluent tau action and");
    Pr("\t\t\tenable tau confluence reduction.");
    Pr("\t\t\t-conf-table uses a table of known representatives to choose unique");
    Pr("\t\t\trepresentatives, this is the fastest method but it may use a lot of");
    Pr("\t\t\tmemory");
    Pr("\t\t\t-conf-compute uses an order to choose unique representatives,");
    Pr("\t\t\tthis may use a lot of CPU time, but the memory requirements are");
    Pr("\t\t\tnegligable");
    Pr("\t\t\t-confluent is provided for backwards compatibility and currently");
    Pr("\t\t\tequivalent to -conf-table");
    Pr("\t\t\tWARNING: This tool does not check if the given action is confluent");   
    }

/* end confluence reduction.
 */


void SThelp(void) { 
    Pr("-O:\t\t\tless runtime by performing an extra pre processing step,");
    Pr("\t\t\twhich includes building an optimalization tree");
    Pr("\t\t\tWorks optimally on \".tbf files\" which are output of");
    Pr("\t\t\t\"mcrl -nocluster -regular -newstate\".");
    Pr("-optimize <nodes>\tlike -O, <nodes> is the maximum number");
    Pr("-no-sumelm\t\tno use of sum variable elimination during enumeration");
    Pr("\t\t\tof nodes in the optimalization tree");
    Pr("-order <label>:\t\tdefinition kind of ordening of sum variables");
    Pr("\t\t\tin a summand in which <label> stands for:");
    Pr("\t\t\t\"no\",\"enum_big_freq\",\"big_freq\", or \"min_depth\"");
    Pr("\t\t\t\"big_freq\" means that the sumvariable which occurs at most");
    Pr("\t\t\tin the condition of that summand will be enumerated first.");
    Pr("\t\t\tDefault is \"enum_big_freq\" which means that first the variables");
    Pr("\t\t\tof enumerated type will be enumerated (conform \"big_freq\") and");
    Pr("\t\t\tthen the others (conform \"big_freq\").");
    Pr("\t\t\t\"min_depth\" means that the sumvariable which occurs at the lowest");
    Pr("\t\t\tdepth in condition will be enumerated first");
    Pr("-after-case:\t\tsame as \"order min_depth\". Advised after \"rewr -case\",");
    Pr("\t\t\tthen there occurs many expanded case functions in condition");
    CRRhelp();
    } 

    
static int maxx(int x, int y)
     {return x<y?y:x;}
     
/* Optimizer code */
ATbool NewPar(int k) {
      int i;
      for (i=0;i<pos.n;i++) 
      if (pos.v[i]==k) return ATfalse;
      return ATtrue;
      }
      
static int SelectParameter(void) {
      ATermList pars = MCRLgetListOfPars(), sums = MCRLgetListOfSummands();
      int k = 0, ns = MCRLgetNumberOfSummands(), 
          npars = MCRLgetNumberOfPars(), r = -1, ncons0 = -1;
      float d0 = 10.0E5;
      for (;!ATisEmpty(pars);pars=ATgetNext(pars), k++) {
         ATerm par = ATgetFirst(pars);
         ATerm name = ATgetArgument((ATermAppl) par, 0);
         AFun sort = MCRLgetSort(name);
         if (NewPar(k) && (MCRLgetType(sort)==MCRLenumeratedsort
            /* || MCRLgetType(sort)==MCRLconstructorsort */)) {
            ATermList cons = MCRLgenerateElementsOfFiniteSort(sort);
            if (!cons) continue;
            {
            float m = (float) ns/ATgetLength(cons), d = 0;
            int ncons = ATgetLength(cons);
            /* if (ncons<5) continue; */
            for (;!ATisEmpty(cons);cons=ATgetNext(cons)) {
              int i, cnt = 0;  
              RWassignVariable(ATgetAFun(name), ATgetFirst(cons), NULL, 0);
              for (i=0;i<ns;i++) 
              if (!ATisEqual(RWrewrite(cond[i]), MCRLterm_false)) cnt++;
              d+= (m-cnt)*(m-cnt);
              }
             d /= (ncons*ncons);
             if (d < d0) {d0 = d; r=k; ncons0= ncons;}
             RWassignVariable(ATgetAFun(name), name, NULL, 0);
             }
       }
     }
     if (r>=0) {
         pos.v[pos.n++]=r; 
         /* ATwarning("QQ %.2f  k = %d", d0, r);
         ATwarning("Parameter %t is chosen",
         ATelementAt(MCRLgetListOfPars(), r));
         */
         }
     return ncons0;
   }

static void PrintChosenParameters(void) {
   int i;
   ATermList pars = MCRLgetListOfPars();
   ATwarning("The chosen parameters are:");
   for (i=0;i<pos.n;i++) {
        ATerm t = ATelementAt(pars, pos.v[i]);
        ATfprintf(stderr,"%t:%t ", MCRLprint(ATgetArgument((ATermAppl)t, 0)), 
            ATgetArgument((ATermAppl)t, 1));
        }
   fprintf(stderr,"\n");
   }
   
static void ChooseParameters(void) {
   int i;
   int r = 1, r0 = 1, s, t =1;
   for (i=0;(s=SelectParameter())>=0;i++) {
       r *= s;
       t += r;
       if (t > maxnodes) {pos.n--; break;}
       r0 = t;
       }
   PrintChosenParameters();
   /*
   ATwarning("Estimated number of nodes: %d Number of parameters: %d", 
   r0, pos.n);
   */
   }          
static NODE Match(NODE node, int depth) {
{
     int k = depth<pos.n && node->db? 
          ATindexedSetGetIndex(node->db, currentSource[pos.v[depth]]):-1;
     if (k<0) {
       return node;
       }
     return Match(node->nodes+k, depth+1);
}
     }
     
static float MakeBranch(NODE r,  int depth, int *minu, int *maxu) {
     float mean = r->nsmd;
     *minu = 1000000; *maxu = 0;
     if (depth>=pos.n)  {
         *minu = r->nsmd; *maxu = r->nsmd;
         return mean;
         }
     {
     DECLA(int, stack, r->nsmd);
     int i;
     ATerm par = ATelementAt(MCRLgetListOfPars(), pos.v[depth]);
     ATerm name = ATgetArgument((ATermAppl) par, 0);
     ATermList cons = MCRLgenerateElementsOfFiniteSort(MCRLgetSort(name));
     r->nnode = ATgetLength(cons);
     r->nodes = (NODE) calloc(r->nnode, sizeof(NODEREC));
     nodecnt+= r->nnode;
     r->db = ATindexedSetCreate(ATgetLength(cons),100);
     for (mean = 0, i=0;i<r->nnode;i++, cons=ATgetNext(cons)) {
        int j;
        ATbool new; ATindexedSetPut(r->db, ATgetFirst(cons), &new);
        RWassignVariable(ATgetAFun(name), ATgetFirst(cons), NULL, 0);
        for (j=0;j<r->nsmd;j++) {
        if (!ATisEqual(RWrewrite(cond[r->smds[j]]), MCRLterm_false)) 
                     stack[r->nodes[i].nsmd++] = r->smds[j];
        }
        if (r->nodes[i].nsmd>0)  {
           int m, M;
           r->nodes[i].smds = (int*) malloc(r->nodes[i].nsmd *sizeof(int));
           memcpy(r->nodes[i].smds, stack, r->nodes[i].nsmd*sizeof(int));
           mean+=MakeBranch(r->nodes+i, depth+1, &m, &M);
           if (m<*minu) *minu = m; if (M>*maxu) *maxu = M;
           }
        RWassignVariable(ATgetAFun(name), name, NULL, 0);
        }
        mean /= r->nnode;
        return mean;
     }
     }        
         
static SMD *MakeTable(void) {
     int n = MCRLgetNumberOfSummands(), i;
     ATermList s1 = MCRLgetListOfSummands();
     SMD *r = (SMD*) calloc(n, sizeof(SMD));
     DECLA(int, stack, n);
     float red = 0;
     for (i=0;!ATisEmpty(s1);s1=ATgetNext(s1),i++) {
       int j ;
       ATerm procarg = ATgetArgument((ATermAppl) ATgetFirst(s1) ,3);
       if (!ATisEqual(procarg, MCRLterm_terminated)) {
         ATermList pars = (ATermList) ATgetArgument((ATermAppl) MCRLgetProc(),1),
                   args = (ATermList) ATgetArgument((ATermAppl) procarg,0),
       s2 = (ATermList) ATgetArgument((ATermAppl) MCRLgetProc(),2);
       for (;!ATisEmpty(pars);pars = ATgetNext(pars),args = ATgetNext(args)) {
         RWassignVariable(ATgetSymbol(ATgetArgument(ATgetFirst(pars),0)) ,
         ATgetFirst(args), NULL, 0);
         }
       for (j=0;!ATisEmpty(s2);s2 = ATgetNext(s2),j++) { 
         if (!ATisEqual(RWrewrite(ATgetArgument((ATermAppl) 
             ATgetFirst(s2), 4)), 
            MCRLterm_false)) stack[r[i].n++] = j;          
         }
       if (r[i].n>0) {
           r[i].v = (int*) malloc(r[i].n*sizeof(int));
           memcpy(r[i].v, stack, r[i].n*sizeof(int));
           red += r[i].n; 
           }    
       }
     }
     ATwarning("Reduction in number of summands: %f", red / (n*n));
     return r;
   }
             
static NODE MakeTree(void) {
     ATermList sums = MCRLgetListOfSummands();
     NODE r = (NODE) calloc(1, sizeof(NODEREC));
     int i, nsmd = MCRLgetNumberOfSummands(), minu =0, maxu =0;
     float mean;
     nodecnt = 1;
     r->nsmd = nsmd; r->smds = (int*) malloc(nsmd*sizeof(int));
     pos.v = (int*) calloc(MCRLgetNumberOfPars(), sizeof(int));
     pos.n = 0;
     for (i=0;i<nsmd;i++) r->smds[i] = i;
     cond = (ATerm*) calloc(nsmd,sizeof(ATerm));
     for (i=0;!ATisEmpty(sums);sums=ATgetNext(sums),i++) {
         ATerm sum = ATgetFirst(sums);
         cond[i] = ATgetArgument((ATermAppl) sum, 4);
         }
     ChooseParameters();
     mean = MakeBranch(r,  0, &minu, &maxu);
     ATwarning("Estimated average number of summands: %.2f (min = %d max = %d)", 
     mean, minu, maxu);  
     ATwarning("Number of nodes in optimalization tree: %d", nodecnt);
     return r;
     }
     
/* End optimizer code */

static ATermList FillNewVars(void) {
     ATermList result = ATmakeList0();
     ATerm t = ATmake("v(<term>,<term>)", MCRLterm_bool, MCRLterm_bool);
     int i;
     static char varname[80], *varpt;
     strcpy(varname, varstring);
     varpt = varname + strlen(varname);
     if (!newvar) newvar = (ATerm*) calloc(max_enum, sizeof(ATerm));
     if (!newvar) ATerror("Cannot allocate newvar (size = %d)", max_enum);
     ATprotectArray(newvar, max_enum);
     for (i=0;i<max_enum;i++) {
          sprintf(varpt,"%d#", i);
          newvar[i] = (ATerm) ATmakeAppl0(ATmakeSymbol(varname, 0, ATtrue));
          result = ATinsert(result, 
            (ATerm) ATsetArgument((ATermAppl) t, newvar[i], 0));
          }
     return result;
     }    
                  
static void Initialize() {
    int i;
    if (first) {
	 ATprotect((ATerm*) &pars);
	 ATprotect(&g.actname);
	 ATprotect((ATerm*) &g.actargs);
	 ATprotect((ATerm*) &g.sumvars);
	 ATprotect((ATerm*) &g.state);
	 ATprotect((ATerm*) &g.nextstate);
	 ATprotect( &g.cond);ATprotect( &g.cond0);
	 first = ATfalse;
         }
    if (summand) {
           for (i=0;i<nSummands;i++) {
	       SUMMAND *s = summand+i;
	       if (s->sumvar) free(s->sumvar);
	       }
	free(summand);
        }
    if (newvar) {
        ATunprotect(newvar);
        free(newvar); newvar = NULL;
        }
    nSummands = ATgetLength(MCRLgetListOfSummands());
    pars =  (ATermList) ATgetArgument((ATermAppl) MCRLgetProc(),1);
    nPars = MCRLgetNumberOfPars();
    if (frek) free(frek);
    if (!(frek=calloc(nSummands,sizeof(int)))) {
                   ATerror("Cannot allocate frek");
                   exit(1);
                   }
    }    
                        
static int MakeVarList(SUMMAND *smd) {
     int n = smd->nSumvars, i = 0;
     if (!smd->sumvar) return 0;
     for (i=0;i<n;i++) /* Bert Lisser */ {
          Symbol val = smd->sumvar[i].val;
          q[i].sumvar = smd->sumvar[i].name;
	  q[i].locvar = val;
          MCRLassignSort(val, smd->sumvar[i].sort);
	  RWassignVariable(smd->sumvar[i].name, smd->sumvar[i].valterm, NULL, 1);
          }
     return n; 
     } 
                    
static ATerm MakeTerm(ATerm constructor, int *top, Symbol sumvar) {
     int i = 0, arity = ATgetArity(ATgetSymbol(constructor)), pt = newvarpt; 
     ATerm result = NULL;
     if (newvarpt + arity >= max_enum) {
          ATfprintf(stderr,"Cannot enumerate all solutions for ");
          for (;!ATisEmpty(g.sumvars);g.sumvars = ATgetNext(g.sumvars)) {
               ATerm sumvar = ATgetFirst(g.sumvars);
               ATfprintf(stderr,"%t:%t ",MCRLprint(
               ATgetArgument((ATermAppl) sumvar, 0)),
               MCRLprint(ATgetArgument((ATermAppl) sumvar, 1)));
               }
          ATfprintf(stderr, "in %t\n",MCRLprint(g.cond0));
          ATwarning("Error during enumeration");
          return NULL;
          }
     for (i=0; i<arity; i++, pt++,(*top)++) {
          Symbol newsym = ATgetSymbol(newvar[pt]), 
          arg = ATgetSymbol(ATgetArgument((ATermAppl) constructor, i));        
          MCRLassignSort(newsym, arg);
          q[*top].locvar = newsym; q[*top].sumvar = sumvar;
          }
     result =  (ATerm) 
          ATmakeApplArray(ATgetSymbol(constructor), newvar + newvarpt);
     newvarpt += arity;
     return result;                   
     }
         
static ATermList OccursInCond(ATerm cond, SVAR *svar, int depth, int n)
     {
     ATermList result = ATmakeList0();
     int i = 0, m = ATgetArity(ATgetSymbol(cond));
     if (m==0)
          {
          for (i=0;i<n;i++)
               {
               SVAR *svar_i = svar +i;
               if (ATgetSymbol(cond) == svar_i->name) 
                    result = ATinsert(result, (ATerm) ATmakeInt(-depth));
               else
                    result = ATinsert(result, (ATerm) ATmakeInt(NOTOCCURS));
               }
          return ATreverse(result);
          }
     if (db_hash)
          {
          result = (ATermList) ATtableGet(db_hash, cond);
          if (result) return result;
          }
     result = OccursInCond(ATgetArgument((ATermAppl) cond, 0), svar, depth+1, n); 
     for (i=1;i<m;i++)
          {
          ATermList plus = OccursInCond(ATgetArgument((ATermAppl)cond, i), 
          svar, depth+1, n), r = ATmakeList0();
          for (;!ATisEmpty(plus)&&!ATisEmpty(result);
          plus=ATgetNext(plus), result = ATgetNext(result))
          r = ATinsert(r, (ATerm) ATmakeInt(
          maxx(ATgetInt((ATermInt) ATgetFirst(result)), 
          ATgetInt((ATermInt) ATgetFirst(plus)))));
          result = ATreverse(r);
          }
     if (db_hash) ATtablePut(db_hash, cond, (ATerm) result);
     return result;
     }
     
static ATermList OccursCount(ATerm cond, SVAR *svar, int depth, int n)
     {
     ATermList result = ATmakeList0();
     int i = 0, m = ATgetArity(ATgetSymbol(cond));
     if (m==0) {
          for (i=0;i<n;i++)
               {
               SVAR *svar_i = svar +i;
               if (ATgetSymbol(cond) == svar_i->name) 
                    result = ATinsert(result, (ATerm) ATmakeInt(1));
               else
                    result = ATinsert(result, (ATerm) ATmakeInt(0));
               }
          return ATreverse(result);
          }
     if (db_hash) {
          result = (ATermList) ATtableGet(db_hash, cond);
          if (result) return result;
          }
     result = OccursCount(ATgetArgument((ATermAppl) cond, 0), svar, depth+1, n); 
     for (i=1;i<m;i++)
          {
          ATermList plus = OccursCount(ATgetArgument((ATermAppl)cond, i), 
          svar, depth+1, n), r = ATmakeList0();
          for (;!ATisEmpty(plus)&&!ATisEmpty(result);
          plus=ATgetNext(plus), result = ATgetNext(result))
          r = ATinsert(r, (ATerm) ATmakeInt(
          ATgetInt((ATermInt) ATgetFirst(result)) + 
          ATgetInt((ATermInt) ATgetFirst(plus))));
          result = ATreverse(r);
          }
     if (db_hash) ATtablePut(db_hash, cond, (ATerm) result);
     return result;
     }
          
static ATbool Order(SVAR *x, SVAR *y) {
     return (order < 3 && MCRLgetType(x->sort) > MCRLgetType(y->sort)) || x->n > y->n; 
     }  
            
static void Reorder(SVAR *svar, int n) { 
     int i = 0;
     for (i=1;i<n;i++) {
          int j = i;
          SVAR v = svar[i];
          while (j>0 && Order(&v,svar+j-1)) { 
              svar[j] = svar[j-1];
              j--;
              }
          svar[j] = v;
          }
     }

static SVAR *ProtectAndAllocateRecord(SUMMAND *s, int n) {
     /*
     ATprotect((ATerm*) &(s->sumvars));
     ATprotect(&(s->cond));
     ATprotect((ATerm*) &(s->procargs));
     ATprotect(&(s->actname));
     ATprotect((ATerm*) &(s->actargs));
     */
     if (n>0) {
        SVAR *svar = (SVAR*) calloc(n, sizeof(SVAR));
	/* ATprotect(&(svar->valterm)); */
        s->sumvar = svar;
        } else  s->sumvar = NULL; 
     return s->sumvar;
     } 
         

static int FillSummand(ATermList sums) {
     /* Returns the maximum number of sum variables */
     int i = 0, mmax = 0;
     DECLA(int, stack, nSummands);
     summand = (SUMMAND*) calloc(nSummands, sizeof(SUMMAND));
     for (i=0;i<nSummands;i++, sums = ATgetNext(sums)) {
          ATerm sum = ATgetFirst(sums);
          SUMMAND *summand_i = summand+i;
          ATerm procarg = ATgetArgument((ATermAppl) sum ,3);
          ATermList sumvars = (ATermList) ATgetArgument((ATermAppl) sum ,0);
          int n = ATgetLength(sumvars);
          SVAR *svar = ProtectAndAllocateRecord(summand_i, n);
          summand_i->sumvars = sumvars;
          summand_i->nSumvars = n;
          summand_i->cond =  ATgetArgument((ATermAppl) sum, 4);
          summand_i->procargs = ATisEqual(procarg, MCRLterm_terminated)? NULL:
                               (ATermList) ATgetArgument(procarg,0);
          summand_i->actname = ATgetArgument((ATermAppl) sum ,1);
          summand_i->actargs = (ATermList) ATgetArgument((ATermAppl) sum ,2);
          if (svar) {
               int j = n-1;
               ATermList freq = NULL, vals = ATempty;
               RWdeclareVariables(sumvars);
               for (;!ATisEmpty(sumvars);sumvars=ATgetNext(sumvars),j--)
                    {ATerm v = ATgetFirst(sumvars), val = NULL;
                    svar[j].name = ATgetSymbol(ATgetArgument(v,0));
		    strcpy(buf,varstring);strcat(buf,ATgetName(svar[j].name));
		    svar[j].val = ATmakeAFun(buf,0,ATtrue);
                    svar[j].sort = ATgetSymbol(ATgetArgument(v,1));
                    svar[j].n = 0;
		    val = (ATerm) ATmakeAppl0(svar[j].val);
		    svar[j].valterm = val;
		    vals = ATinsert(vals, ATmake("v(<term>,<term>)",
		           val ,ATgetArgument(v,1)));
		    
                    }
               if (ATgetLength(vals)> mmax) mmax = ATgetLength(vals);
	       RWdeclareVariables(vals);
               db_hash = db_hash?db_hash:ATtableCreate(50,75);
               freq = order==levelOrdering? 
               OccursInCond(summand_i->cond, svar, 0, n):
               OccursCount(summand_i->cond, svar, 0, n);
               ATtableReset(db_hash);
               for (j=0;!ATisEmpty(freq);freq=ATgetNext(freq),j++) {
                    svar[j].n = ATgetInt((ATermInt) ATgetFirst(freq));
               } 
               if (order != noOrdering) Reorder(svar, n);
	       /*
               {
               for (j=0;j<n;j++)  fprintf(stderr, "(%s, %s, %d),",
          ATgetName(svar[j].name), ATgetName(svar[j].sort), svar[j].n); 
               if (n) fprintf(stderr,"\n"); 
               }
               */
               }
          }
     return mmax;
     }              
          
     
static ATerm Action(ATerm actname, ATermList  actargs) {
      return (ATerm) ATmakeAppl0(ATmakeSymbol(ATwriteToString(MCRLprint(
      (ATerm) ATmakeApplList(
      ATmakeSymbol(ATgetName(ATgetSymbol(actname)),ATgetLength(actargs), ATtrue),
      actargs))),0, ATtrue));
      }
      
static void RewriteList(ATermList ts, ATerm *dest) {
   int i;
   for (i=0; i<nPars;i++,ts = ATgetNext(ts)) {
      dest[i] = RWrewrite(ATgetFirst(ts));
      /* ATwarning("QQ: i= %d dest = %t %d ", i, dest[i], dest); */
   }
}

/* static PrintQ(int b, int t) {
int i;
for (i=b;i<t;i++) ATwarning("Queu: %s %s", ATgetName(q[i].locvar),
ATgetName(MCRLgetSortSym(q[i].locvar)));
}
*/

ATerm STcurrentSummand(void) {
    ATermList  dests = ATempty;
    int i = 0;
    ATerm nextState = NULL;
    AFun smd = ATmakeAFun("smd",5,ATfalse);
    for (i=nPars-1;i>=0;i--) dests = ATinsert(dests, systemDest[i]);
    nextState = (ATerm) ATmakeAppl1(MCRLsym_i,(ATerm) dests);
    return (ATerm) ATmakeAppl5(smd, (ATerm) g.sumvars, g.actname, 
           (ATerm) RWrewriteList(g.actargs),  nextState, g.cond);
    }

static ATermList Intersection(ATermList t1s, ATermList t2s) {
     ATermList result = ATempty;
     for (;!ATisEmpty(t1s);t1s=ATgetNext(t1s)) {
          ATerm t1 = ATgetFirst(t1s);
          if (ATindexOf(t2s, t1,0)>=0) result = ATinsert(result, t1);
          }
     /* ATwarning("Intersection %t\n",result); */
     return result;
     }

static ATermList Union(ATermList t1s, ATermList t2s) {
     ATermList result = t2s;
     /* ATwarning("Arguments union %t %t",t1s,t2s); */
     for (;!ATisEmpty(t1s);t1s=ATgetNext(t1s)) {
          ATerm t1 = ATgetFirst(t1s);
          if (ATindexOf(t2s, t1,0)<0) result = ATinsert(result, t1);
          }
     return result;
     }

static ATermList TestEqual(Symbol var, ATerm  cond) {
     Symbol bsym = ATgetSymbol(cond);
     ATermList result = ATempty;
     if (ATgetArity(bsym)==2 && !strncmp(ATgetName(bsym),"eq#",3)) {
        if (ATgetAFun(ATgetArgument((ATermAppl) cond, 0))==var) {
               return ATmakeList1(ATgetArgument((ATermAppl) cond, 1));
               }
          if (ATgetAFun(ATgetArgument((ATermAppl) cond, 1))==var) {
               return ATmakeList1(ATgetArgument((ATermAppl) cond, 0));
               }
          return ATempty;
        }
        if (bsym == MCRLsym_and) result = Union(
          TestEqual(var, ATgetArgument((ATermAppl) cond , 0)),
          TestEqual(var, ATgetArgument((ATermAppl) cond , 1)));
     else
     if (bsym == MCRLsym_or) result =  Intersection(
          TestEqual(var, ATgetArgument((ATermAppl) cond , 0)),
          TestEqual(var, ATgetArgument((ATermAppl) cond , 1)));
     return result;
     }

static void Stabilize(ATermList sumvars) {
           int ok;
           do {
           ATermList v = sumvars;
           for (ok=1;!ATisEmpty(v);v=ATgetNext(v)) {
             ATermAppl w = (ATermAppl) ATgetArgument((ATermAppl) ATgetFirst(v), 0); 
             AFun z = ATgetAFun(w);
             ATerm old =  RWgetAssignedVariable(z);
             ATerm current = RWrewrite(old);
             if (!ATisEqual(old, current)) {
                  ok = 0;
                  RWassignVariable(z,  current , NULL, 1); 
           //  ATfprintf(stderr, "%t=%t\n", w, MCRLprint(RWgetAssignedVariable(z)));
                  }
             }
           } while (!ok);
}
     
static int _Enumerate(int bottom, int top,  ATerm cond, int check) {
     /* Computes the next states from an input state and an input summand */ 
     int result = 0;
     /* ATwarning("QQQ _Enumerate bottom = %d top = %d cond = %t", 
     bottom, top, cond); */
     if (bottom == top) {
          if (!ATisEqual(cond, MCRLterm_true)) {
              if (!abstract) {
                  ATwarning("Condition %t does not evaluate to %t or %t (summand %d)", 
	          MCRLprint(cond), MCRLprint(MCRLterm_true), 
                  MCRLprint(MCRLterm_false),
                  smd_index+1);
	          return -1;
              }
              else {
                  if (!ATisEqual(
                     MCRLremainingVars(cond, g.sumvars), g.sumvars)) {  
                  ATwarning("Condition %t contains sumvariables %t (summand %d)", 
                  MCRLprint(cond), g.sumvars, smd_index+1);
                  return -1;
                  }
             }
          }
          g.cond = cond; /* Needed for decluster */
          if (check) Stabilize(g.sumvars);
	  RewriteList(g.nextstate, systemDest);
          *systemLabel = Action(g.actname, RWrewriteList(g.actargs));
          result++;
          if (systemCallback) systemCallback();
          return result;  
          } 
          {
          Symbol var = q[bottom].locvar, sumvar = q[bottom].sumvar,
          sortVar = MCRLgetSortSym(var);
          ATermList constructors = MCRLgetConstructors(sortVar), r;
          ATerm cond0 = cond, t0 = RWgetAssignedVariable(sumvar);
          if (MCRLgetType(sortVar)==MCRLsort) {
               ATwarning(
               "The sort \"%s\" of variable \"%t\" is infinite and cannot be enumerated",
                    ATgetName(MCRLgetSortSym(sumvar)), 
			MCRLprint(ATmake("<str>",ATgetName(sumvar))));
	       return -1;
               }
          bottom++;
          if (sumelm && !ATisEmpty((r = TestEqual(var, cond0)))) {
            ATerm t = ATgetFirst(r);
            RWassignVariable(var,  t, NULL, 2);             
               cond = RWrewrite(cond0);    
               if (!ATisEqual(cond, MCRLterm_false)) {
                    ATerm t =  RWrewrite(t0);
		    int r = -1; 
                    RWassignVariable(sumvar,  t , NULL, 1); 
                    r = _Enumerate(bottom, top, cond, 1);
		    if (r<0) return -1;
		    result += r;
                    }
                RWassignVariable(sumvar,  t0 , NULL,1);
            }
          else {
          int top0 =top;
          for (;!ATisEmpty(constructors);constructors=ATgetNext(constructors)) {
               ATerm constructor =  ATgetFirst(constructors);    
               constructor = MakeTerm(constructor, &top, sumvar);
               if (!constructor) return -1;  
               constructor = RWrewrite(constructor); 
               RWassignVariable(var,  constructor , NULL, 2);             
               cond = RWrewrite(cond0);    
               if (!ATisEqual(cond, MCRLterm_false)) {
                    ATerm t =  RWrewrite(t0);
		    int r = -1; 
                    RWassignVariable(sumvar,  t , NULL, 1); 
                    r = _Enumerate(bottom, top, cond, check);
		    if (r<0) return -1;
		    result += r;
                    }
               RWassignVariable(sumvar,  t0 , NULL,1);
               top = top0;
               }
            }
          cond = cond0;
	  RWresetVariables(2);              
         }    
     return result;   
     }
          
static int Enumerate(SUMMAND *smd) {
     int top = MakeVarList(smd), result = 0;
     ATermList ls = NULL;
     /* ATwarning("QQQ: Enumerate"); */
     newvarpt = 0;
     g.actname = smd->actname;
     g.actargs = smd->actargs;
     g.sumvars = smd->sumvars;
     ls = g.sumvars;
     if (!smd->procargs) {
          systemDest[0] = NULL;
          if (systemCallback) systemCallback();
	  return 0; 
	  /* Terminated */
	  }
     else {
          g.cond0 = smd->cond;
          g.cond  = RWrewrite(g.cond0);
          g.nextstate = smd->procargs;   
          if (!ATisEqual(g.cond, MCRLterm_false)) {
              int code =  _Enumerate(0, top, g.cond, 0);
              if (code < 0) return code;     
              result +=  code;
              } 
          }
     RWresetVariables(1); 
     /* for (;!ATisEmpty(ls);ls=ATgetNext(ls)) 
     ATwarning("%t = %t",ATgetFirst(ls), 
         RWgetAssignedVariable(ATgetAFun(ATgetArgument(ATgetFirst(ls),0))));
	 */
     return result; 	          
     }
      
static void SubstituteInPars(ATermList pars, ATerm* src) {
     int i;
     for (i=0;i<nPars;i++, pars = ATgetNext(pars)) {
         RWassignVariable(ATgetSymbol(ATgetArgument(ATgetFirst(pars),0)) ,src[i], 
         NULL, 0);
         }
     } 


void STsetArguments(int *argc, char ***argv) { 
     int i, j=0;
     char **newargv = (char**) calloc(*argc + 1, sizeof(char*));
     if (!newargv) ATerror("Cannot allocate array argv"); 
     newargv[j++] = (*argv)[0];
     for(i=1;i<*argc;i++) {
        if (!strcmp((*argv)[i],"-confluent")||!strcmp((*argv)[i],"-conf-table")) {
               CRreducing = tarjanReducing;
	       if ((++i)<*argc && strncmp((*argv)[i],"-",1)) {
			ATprotect(&confluent_action);
	            confluent_action=ATmake("<str>",(*argv)[i]);
                    continue;
                    }
               ATerror("Option %s needs argument.\n",(*argv)[i-1]);
               }
	if (!strcmp((*argv)[i],"-conf-compute")) {
               CRreducing = newReducing; 
               if ((++i)<*argc && strncmp((*argv)[i],"-",1)) {
			ATprotect(&confluent_action);
	            confluent_action=ATmake("<str>",(*argv)[i]);
                    continue;
                    }
               ATerror("Option %s needs argument.\n",(*argv)[i-1]);
               }
        if (!strcmp((*argv)[i],"-abstract")) {
	    abstract = ATtrue;
	    continue;
	}
        if (!strcmp((*argv)[i],"-max-enum")) {
               if ((++i)<(*argc)) {
                  char *endptr = (*argv)[i];
                  max_enum = strtol((*argv)[i],&endptr,10);
                  if (*endptr != '\0') 
                  ATerror("Number expected after \"-max-enum\"");
                  if (max_enum<=0) ATerror("max_enum %d is not positive", 
                  max_enum);
                  }
            continue;
         }
         if (!strcmp((*argv)[i],"-optimize")) {
            if ((++i)<(*argc) && strncmp((*argv)[i],"-",1)) {
                char *endptr = NULL;
                maxnodes = strtol((*argv)[i],&endptr,10);
                if (*endptr != '\0') ATerror("Number expected after \"-optimize\"");
                optimize = ATtrue;
                }
            else
                ATerror("Integer (optimize) expected after %s\n",(*argv)[i-1]);
            continue;
            }               
        if (!strcmp((*argv)[i],"-O"))
               {
               optimize = ATtrue;
               maxnodes = 10000;
               continue;
               }
        if (!strcmp((*argv)[i],"-no-sumelm"))
               {
               sumelm = ATfalse;
               continue;
               }
        if (!strcmp((*argv)[i],"-order")) {
         if ((++i)<*argc && strncmp((*argv)[i],"-",1)) {
         char *code = (*argv)[i];
         if (!strcmp(code,"no"))
              order = noOrdering;
         else 
         if (!strcmp(code,"enum_big_freq"))
              order = enumOccurrenceOrdering;
         else
         if (!strcmp(code,"big_freq")) 
              order = occurrenceOrdering;
         else
         if (!strcmp(code,"min_depth"))
              order = levelOrdering;
         else
         ATerror("Illegal order key");
         argSet = ATtrue;
         continue;
         }
           ATerror("Option %s needs argument.\n",(*argv)[i-1]);
        }
        if (!strcmp((*argv)[i],"-after-case"))
               {
	       /* case functions are in front of condition */
               order = levelOrdering;
               continue;
               }
        newargv[j++] = (*argv)[i];
     }
     *argc = j;  *argv = newargv; 
     }
     
void STinitialize(ST_ORDER order0, ATerm* label, ATerm* dest, 
     STcallback callback) {
     ATermList vs = NULL;
     int maxSumvars, n;
     if (!argSet) order = order0;
     Initialize(label, dest);
	if (CRreducing == noReducing) {
		systemCallback=callback;
		systemLabel=label;
		systemDest=dest;
	} else {
		ATwarning("tau confluence reduction enabled in stepper");
		if (confluent_action) MCRLterm_tau_c=confluent_action;
		if (repr_map) ATtableDestroy(repr_map);
		if (CRreducing == tarjanReducing) {
			repr_map = ATtableCreate(NREC, 95);
		}
		ATprotect((ATerm*)&next_list);
		ATprotect((ATerm*)&label_list);
		systemSource=calloc(nPars, sizeof(ATerm));
		ATprotectArray(systemSource, nPars);
		systemDest=calloc(nPars, sizeof(ATerm));
		ATprotectArray(systemDest, nPars);
		ATprotect(&conf_label);
		systemLabel=&conf_label;
		systemCallback=listWriterCallback;
		userCallback=callback;
		userLabel=label;
		userDest=dest;
		atexit(ConfluenceStatistics);
	}
     RWdeclareVariables((ATermList) ATgetArgument((ATermAppl) MCRLgetProc(),1));
     vs = FillNewVars();
     RWdeclareVariables(vs);
     maxSumvars = FillSummand(MCRLgetListOfSummands());
     n = maxSumvars + max_enum;
     q = (QUEUE*) calloc(n, sizeof(QUEUE));
     if (!q) ATerror("Cannot allocate queu (%d elements)", n);
     RWsetAutoCache(ATtrue);
     if (optimize) {
	if (CRreducing != noReducing) ATerror("fix me please!");
         toptree = MakeTree();
     }     
     }
 
int STstep(ATerm* src) {
	int result;
        currentSource=src;
	if (CRreducing == noReducing) {
		if (optimize) {
	         NODE t = Match(toptree,0);
	         if (t) {
	           int j;
	            number_of_summands += t->nsmd;
	            /* fprintf(stderr,"nsmd %d\n", t->nsmd);
	            for (j=0;j<t->nsmd;j++) fprintf(stderr,"%d ", t->smds[j]);
	            fprintf(stderr,"\n"); */
	            result = STstepSmd(src, t->smds, t->nsmd);
	            /* ATwarning("result = %d", result); */
	            return result;
	           }
		} else {
			return STstepSubset(src,NULL);
		}
	}
	next_list=ATmakeList0();
	label_list=ATmakeList0();
	result=STstepSubset(src,otherSubset);
	if (result<0) ATerror("Error in STstep");
	{
		  ATbool new;
		  ATermList next_walk=next_list;
 		  ATermList label_walk=label_list;
		  for(;!ATisEmpty(next_walk);
		     next_walk=ATgetNext(next_walk),label_walk=ATgetNext(label_walk)){
			switch(CRreducing){
				case tarjanReducing:
				Unfold(userDest,0,nPars,find_repr(ATgetFirst(next_walk)));
				break;
				case newReducing:
				Unfold(userDest,0,nPars,find_new_repr(ATgetFirst(next_walk)));
				break;
				default:
					ATerror("unimplemented form of confluence reduction in STstep");
			}
			*userLabel=ATgetFirst(label_walk);
			userCallback();
		  }
	}
	return result;
     }

float STgetNumberOfSummands() {return number_of_summands;}

int STstepSubset(ATerm* src, STmemberFunction member) {
     int result = 0, code = -1;
     currentSource=src;
     SubstituteInPars(pars, src);
     for (smd_index=0;smd_index<nSummands;smd_index++) {
	  if (member && !member((summand + smd_index)->actname)) continue;
          code = Enumerate(summand + smd_index);
          if (code>0) frek[smd_index]++;
          if (code <0) return code; /* error */
          result += code;
          }    
     return result;    
     }
     
int STstepSmd(ATerm* src, int *smds, int nsmd) {
     return STstepSubsetSmd(src, smds, nsmd, NULL);
     }

int STstepSubsetSmd(ATerm* src, int *smds, int nsmd, STmemberFunction member) {
     int result = 0, code = -1, i = 0;
     currentSource=src;
     SubstituteInPars(pars, src);
     for (;i<nsmd;i++) {
          smd_index = smds[i];
	  if (member && !member((summand + smd_index)->actname)) continue;
          code = Enumerate(summand + smd_index);
          if (code>0) frek[smd_index]++;
          if (code <0) return code; /* error */
          result += code;
          }    
     return result;    
     }
     
void STsetCallback(STcallback callback) {
	if (CRreducing==noReducing) {
		systemCallback = callback;
	} else {
		userCallback = callback;
	}
}

void STsetLabelAddress(ATerm* label) {
	if (CRreducing==noReducing) {
		systemLabel = label;
	} else {
		userLabel = label;
	}
}

void STsetDestAddress(ATerm* dest) {
	if (CRreducing==noReducing) {
		systemDest = dest;
	} else {
		userDest = dest;
	}
}

int STnumberOfUsedSummands(void) {
   int i, cnt = 0;
   for (i=0;i<nSummands;i++) if (frek[i]!=0) cnt++;
   return cnt;
   }

ATermList STgetUsedSummands(void) {
   ATermList r = ATempty, s = MCRLgetListOfSummands();
   int i;
   for (i=0;i<nSummands&&!ATisEmpty(s);i++,s=ATgetNext(s)) 
      if (frek[i]!=0) r = ATinsert(r, ATgetFirst(s));
   return ATreverse(r); 
   }

void STsetInitialState(){
	RewriteList((ATermList)ATgetArgument((ATermAppl) MCRLgetProc(),0),systemDest);
	switch(CRreducing){
		case noReducing:
		return;
		case tarjanReducing:
		Unfold(userDest,0,nPars,find_repr(Fold(systemDest,0,nPars)));
		return;
		case newReducing:
		Unfold(userDest,0,nPars,find_new_repr(Fold(systemDest,0,nPars)));
		return;
	}
	ATerror("Confluence reduction unimplemnted in STsetInitialState");
}

int STgetSmdIndex(void) {
     return smd_index;
}


static ATbool occurterm(ATerm t,ATerm st){
	int i,N;
	if (ATisEqual(t,st)) return ATtrue;
	N=ATgetArity(ATgetAFun(t));
	for(i=0;i<N;i++){
		if (occurterm(ATgetArgument(t,i),st)) return ATtrue;
	}
	return ATfalse;
}

static ATbool occurlist(ATermList l, ATerm t){
	for(;!ATisEmpty(l);l=ATgetNext(l)){
		if (occurterm(ATgetFirst(l),t)) return ATtrue;
	}
	return ATfalse;
}

int STgetSummandCount(void){
	return nSummands;
}

ATerm STgetLabel(int smd){
	return (summand+smd)->actname;
}

int STgetProjection(int *proj,int smd){
	SUMMAND* summand_smd=summand+smd;
	ATermList p,pa;
	ATerm v;
	int i,j,count=0;

	for(i=0,p=pars;i<nPars;i++,p=ATgetNext(p)){
		v=ATgetArgument(ATgetFirst(p),0);
		if (occurlist(summand_smd->actargs,v)||occurterm(summand_smd->cond,v)){
			proj[count]=i;
			count++;
			continue;
		}
		for(j=0,pa=summand_smd->procargs;j<nPars;j++,pa=ATgetNext(pa)){
			if(i==j){
				if (!ATisEqual(ATgetFirst(pa),v)) break;
			} else {
				if(occurterm(ATgetFirst(pa),v)) break;
			}
		}
		if (j<nPars){
			proj[count]=i;
			count++;
			continue;
		}
	}
	return count;
}
