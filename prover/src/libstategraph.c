/* $Id: libstategraph.c,v 1.9 2008/09/25 10:24:53 vdpol Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "aterm2.h"
#include <sys/types.h>
#include <sys/stat.h>
#include "signature.h"
#include "usechange.h"
#include "rw.h"
#include <math.h>
#include <assert.h>

// VERSION assumed to be defined with -DVERSION=\"...\"

typedef ATerm (PLAINGRAPH) (ATerm, FILE*);

static LPO_t lpo;
static ATerm LPO2gen=NULL, datatype=NULL;

int Npars, Nsums;
static char VERBOSE=0;
static char TEST = 0;      // print all decisions
static char VISUALIZE = 0; // generate control flow graphs in dot format
static char VIEW = 0;      // generate control flow graphs in dot format
                           // suited for previewing with grappa
static char SUMMANDS = 0;  // print summands on labels during visualization
static char STATES = 0;    // print state values during visualization
static char INVARIANT=0;   // generate invariants automatically (rudimentary)
static char CONSTANT=0;    // constant propagation, based on invariant.

extern Symbol andF;
extern Symbol orF;
extern Symbol notF;
extern Symbol iteF;

static char NOCHANGE=0;




static void parse_argument_line(int *argc,char **argv[]) {
  int i;
  int newargc=1;
  char** newargv=(char**)calloc(*argc,sizeof(char*));
  newargv[0]=*argv[0];

  for (i=1;i<*argc;i++) {
   if (!strcmp((*argv)[i],"-verbose")) {
      VERBOSE=1;
      newargv[newargc++] = (*argv)[i];
    }
   else if (!strcmp((*argv)[i],"-test"))
     { TEST=1;
       VERBOSE=1;
     }
   else if (!strcmp((*argv)[i],"-invariant"))
      INVARIANT=1; 
   else if (!strcmp((*argv)[i],"-constant"))
      CONSTANT=1; 
    else if (!strcmp((*argv)[i],"-show"))
      VISUALIZE=1; 
    else if (!strcmp((*argv)[i],"-show-summands")) {
      SUMMANDS=1;
      VISUALIZE=1;
    }
    else if (!strcmp((*argv)[i],"-show-states")) {
      STATES=1; 
      VISUALIZE=1;
    }
#ifdef GRAPPA
    else if (!strcmp((*argv)[i],"-stateview")) {
      /* NOCHANGE=1; */ 
      VIEW=1;
    }
#endif
    else if (!strcmp((*argv)[i],"-minchange"))
      NOCHANGE=1; 
    else
      newargv[newargc++]=(*argv)[i];
  }
  *argv=newargv;
  *argc=newargc;
}

static ATermList compatible_intersection(ATermList L1, ATermList L2) {
  /* TODO: use eq() to check compatibility */
  /* In particular [5,4,2] and [5,3,2] should yield [5,2], (because eq(5,3)=F etc.) but
                   [5,4] and [5,x] should yield [5,x]
  */
  if (ATisEmpty(L1)) return L1;
  return L2;
}

static ATermList set_union(ATermList L1, ATermList L2) {
  /* returns union of L1 and L2, removing duplicates,
   * but assuming that L1 and L2 are unique already.
   */
  ATermList L=L1;
  for (;!ATisEmpty(L2);L2=ATgetNext(L2)) {
    ATerm head = ATgetFirst(L2);
    if (ATindexOf(L1,head,0) == -1)
      L = ATinsert(L,head);
  }
  return L;
}

char closed_term(ATerm term) {
  int n = ATgetArity(ATgetSymbol(term));
  if (n==0)
    switch (MCRLgetType(ATgetSymbol(term))) {
    case MCRLfunction: 
    case MCRLconstructor: return 1;
    default: return 0;
    }
  else {
    ATermList l;
    for (l=ATgetArguments((ATermAppl)term);!ATisEmpty(l);l=ATgetNext(l))
      if (!closed_term(ATgetFirst(l)))
	return 0;
    return 1;
  }
}

static ATerm destination(ATerm next, ATerm parameter, ATerm source) {
  /* RWdeclareVars(ATmakeList1(parameter)); */
  RWassignVariable(ATgetSymbol(parameter),source,NULL,1);
  next = RWrewrite(next);
  RWresetVariables(1);
  return next;
}

ATermList sources(ATerm guard, ATerm parameter) {
  /* the result is a list of values [v1,v2..] for parameter, or NULL.
     guard => parameter=v1 OR parameter=v2 OR ...
     if the list = []: FALSE (this means: guard is contradictory)
     if the list = NULL: TRUE (this means: guard allows any value for parameter)
  */

  ATerm g1,g2;
  ATermList s1,s2;

  //  ATfprintf(stderr,"%t\n",guard);
  if (guard == prFALSE) return ATmakeList0();
  
  if (ATgetSymbol((ATermAppl)(guard))==iteF)
    return sources(prOR(prAND(ATgetArgument(guard,0),ATgetArgument(guard,1)),
                          prAND(prNOT(ATgetArgument(guard,0)),ATgetArgument(guard,2))),parameter);

  if (ATgetSymbol((ATermAppl)(guard))==andF) {
    g1=ATgetArgument((ATermAppl)guard,0);
    g2=ATgetArgument((ATermAppl)guard,1);
    s1 = sources(g1,parameter);
    s2 = sources(g2,parameter);
    if (!s1) return s2;
    if (!s2) return s1;
    return compatible_intersection(s1,s2);
  }
  
  if (ATgetSymbol((ATermAppl)(guard))==orF) {
    g1=ATgetArgument((ATermAppl)guard,0);
    g2=ATgetArgument((ATermAppl)guard,1);
    s1 = sources(g1,parameter);
    if (!s1) return s1;
    s2 = sources(g2,parameter);
    if (!s2) return s2;
    return set_union(s1,s2);
  }
  
  if (MCRLgetType(ATgetSymbol(guard))==MCRLeqfunction) {
    g1=ATgetArgument((ATermAppl)guard,0);
    g2=ATgetArgument((ATermAppl)guard,1);
    if (g1==parameter)
      return ATmakeList1(RWrewrite(g2));
    else if (g2==parameter)
      return ATmakeList1(RWrewrite(g1));
    else
      return NULL;
  }

  if (guard==parameter)
    return ATmakeList1(prTRUE);

  if (guard==prNOT(parameter))
    return ATmakeList1(prFALSE);
  
  return NULL;
}

static char *Removed;
static ATermIndexedSet *Relevant;
static ATerm *New_Next, *New_Init;
static ATermIndexedSet Parnames, Sumnames;

static char **RulesArray;              // summands ruled by clusters
static ATermIndexedSet ClusterIndex;   // assigns numbers to clusters
static ATermTable *AL, *AS, *AT;       // quick access to clusters

/*  AL[cl]: table mapping summand label to list of edges of cluster cl
    AS[cl]: table mapping source state to list of edges of cluster cl
    AT[cl]: table mapping target state to list of edges of cluster cl

    RulesArray[cl][i]: summand i is ruled by cluster cl
    Relevant[k]: set of <pair(cluster,value)> in which parameter k is relevant

    Removed[i]: summand i is considered (to be) removed
 */

void Initialize(LPO_t lpo, ATerm datatype,
		int argc, char *argv[]) {
  ATermList K;
  ATerm signature;
  int i,j;

  RWdeclareVariables(LPOgetParList(lpo));
  
  if (!ATmatch(datatype,"d(<term>,<term>))",
	       &signature,NULL))
    ATerror("Expect datatype");
  SignatureSetArguments(&argc,&argv);
  SignatureInitialize();
  Declare_vars(LPOgetParList(lpo)); // had to add this to get their sort in prEQ...
  // Init_signature(signature,argc,argv); // in order to use OR,AND,TRUE,FALSE,...
  UCinitialize(lpo); // this makes functions from usechange.h available

  Parnames = ATindexedSetCreate(127,50);
  Sumnames = ATindexedSetCreate(127,50);
  
  for (j=0;j<Npars;j++) {
    ATbool b;
    ATindexedSetPut(Parnames,LPOgetParName(lpo,j),&b);
  }

  K = LPOgetSumList(lpo);
  for (i=0;i<Nsums;i++) {
    ATermAppl smd = (ATermAppl)ATgetFirst(K);
    ATermList V = (ATermList)ATgetArgument(smd,0);
    ATbool b;
    K=ATgetNext(K);
    for (;!ATisEmpty(V);V=ATgetNext(V))
      ATindexedSetPut(Sumnames,ATgetArgument((ATermAppl)ATgetFirst(V),0),&b);
  }
}

ATermTable AdjacencySource(ATerm edges) {
  ATermTable X = ATtableCreate(100,50);
  ATerm edge;
  while (ATmatch(edges,"[<term>,<list>]",&edge,&edges)) {
    ATerm src;
    ATermList OutList;
    ATmatch(edge,"edge(<term>,<term>,<term>)",&src,NULL,NULL);
    OutList = (ATermList)ATtableGet(X,src);
    if (!OutList)
      ATtablePut(X,src,(ATerm)ATmakeList1(edge));
    else
      ATtablePut(X,src,(ATerm)ATinsert(OutList,edge));
  }
  return X;
}

ATermTable AdjacencyTarget(ATerm edges) {
  ATermTable X = ATtableCreate(100,50);
  ATerm edge;
  while (ATmatch(edges,"[<term>,<list>]",&edge,&edges)) {
    ATerm trg;
    ATermList OutList;
    ATmatch(edge,"edge(<term>,<term>,<term>)",NULL,NULL,&trg);
    OutList = (ATermList)ATtableGet(X,trg);
    if (!OutList)
      ATtablePut(X,trg,(ATerm)ATmakeList1(edge));
    else
      ATtablePut(X,trg,(ATerm)ATinsert(OutList,edge));
  }
  return X;
}

ATermTable AdjacencyLabel(ATerm edges) {
  ATermTable X = ATtableCreate(100,50);
  ATerm edge;
  while (ATmatch(edges,"[<term>,<list>]",&edge,&edges)) {
    ATerm lab;
    ATermList OutList;
    ATmatch(edge,"edge(<term>,<term>,<term>)",NULL,&lab,NULL);
    OutList = (ATermList)ATtableGet(X,lab);
    if (!OutList)
      ATtablePut(X,lab,(ATerm)ATmakeList1(edge));
    else
      ATtablePut(X,lab,(ATerm)ATinsert(OutList,edge));
  }
  return X;
}

ATerm SourcesTargets(ATermTable AL, int label) {
  return ATtableGet(AL,(ATerm)ATmakeInt(label));
}

ATerm SourcesLabels(ATermTable AT, ATerm trg) {
  return ATtableGet(AT,trg);
}

ATerm LabelsTargets(ATermTable AS, ATerm src) {
  return ATtableGet(AS,src);
}

ATerm Sources(ATermTable AL, int label) {
  ATermList Result=ATempty;
  ATerm src, L = SourcesTargets(AL,label);
  if (!L) return NULL;
  while (ATmatch(L,"[edge(<term>,<term>,<term>),<list>]",&src,NULL,NULL,&L))
    if (ATindexOf(Result,src,0) == -1)
      Result=ATinsert(Result,src);
  return (ATerm)Result;
}

ATerm Targets(ATermTable AL, int label) {
  ATermList Result=ATempty;
  ATerm trg, L = SourcesTargets(AL,label);
  if (!L) return NULL;
  while (ATmatch(L,"[edge(<term>,<term>,<term>),<list>]",NULL,NULL,&trg,&L))
    if (ATindexOf(Result,trg,0) == -1)
      Result=ATinsert(Result,trg);
  return (ATerm)Result;
}

ATerm Target(ATermTable AL, ATerm src, int label) {
  ATermList Result=ATempty;
  ATerm src2,trg2, L=SourcesTargets(AL,label);
  if (!L) return NULL;
  while (ATmatch(L,"[edge(<term>,<term>,<term>),<list>]",&src2,NULL,&trg2,&L))
    if (src==src2 && ATindexOf(Result,trg2,0)==-1)
      Result=ATinsert(Result,trg2);
  assert(ATgetLength(Result)<=1);
  return (ATerm)Result;
}

ATermTable AdjacencyList2 (ATerm edges) {
  ATermTable X = ATtableCreate(100,50);
  ATerm edge;
  while (ATmatch(edges,"[<term>,<list>]",&edge,&edges)) {
    ATerm src;
    ATermList OutList;
    ATmatch(edge,"edge(<term>,<term>)",NULL,&src);
    OutList = (ATermList)ATtableGet(X,src);
    if (!OutList)
      ATtablePut(X,src,(ATerm)ATmakeList1(edge));
    else
      ATtablePut(X,src,(ATerm)ATinsert(OutList,edge));
  }
  return X;
}

ATermList parameterlist(ATerm indices) {
  int i;
  ATermList Result=ATempty;
  while (ATmatch(indices,"[<int>,<list>]",&i,&indices))
    if (i==Npars)
      Result = ATinsert(Result,ATmake("default_pc"));
    else
      Result = ATinsert(Result,MCRLprint(LPOgetParName(lpo,i)));
  return ATreverse(Result);
}

int Remove_sums(ATermList *Clusters) {
  int i,N=0;
  ATerm start,cname,edges;
  ATermList Newclusters=ATmakeList0();
  
  Removed = (char*)calloc(Nsums,sizeof(char));
  for (i=0;i<Nsums;i++)
    Removed[i]=0;
  
  while (ATmatch((ATerm)*Clusters,
		 "[cluster(<term>,<term>,<term>),<list>]",
		           &cname,   &start,&edges,Clusters)) {
    int c = ATindexedSetGetIndex(ClusterIndex,cname);
    ATermTable X = AS[c];
    char* Rules = RulesArray[c];
    char* Rul2 = (char*)calloc(Nsums,sizeof(char));
    for (i=0;i<Nsums;i++)
      Rul2[i]=Rules[i];
    
    /* Step 1: Compute reachable part of X, and reset visited summands to 0.
     * This is implemented as a depth-first search with search stack Todo,
     * starting in node "start" 
     */
    {
    ATermList Todo = ATmakeList1(start);
    ATermList Newedges = ATmakeList0();
    ATermIndexedSet Reachable = ATindexedSetCreate(2*Nsums,50);
    ATbool new;
    ATindexedSetPut(Reachable,start,&new);
    while (!ATisEmpty(Todo)) {
      ATerm edge;
      ATermList Next = (ATermList)ATtableGet(X,ATgetFirst(Todo));
      if (!Next) Next = ATmakeList0();
      Todo = ATgetNext(Todo);
      while (ATmatch((ATerm)Next,"[<term>,<list>]",&edge,&Next)) {
	ATerm trg;
	int sum;
	if (!ATmatch(edge,"edge(<term>,<int>,<term>)",NULL,&sum,&trg))
	  ATerror("wrong edge format\n");
	Rul2[sum]=0;
	Newedges = ATinsert(Newedges,edge);
	ATindexedSetPut(Reachable,trg,&new);
	if (new) Todo = ATinsert(Todo,trg);
      }
    }
    Newclusters = ATinsert(Newclusters, ATmake("cluster(<term>,<term>,<term>)",
					       cname,start,Newedges));
    ATindexedSetDestroy(Reachable);
    }

    /* Step 2: Remove all unvisited summands, i.e. those still marked 1.*/

    for (i=0;i<Nsums;i++)
      if (Rul2[i]) {
	if (!Removed[i]) N++;
	if (VERBOSE) ATfprintf(stderr,"Summand %d removed in cluster %t\n",
			    i+1,parameterlist(cname));
	Removed[i]=1;
      }
    free(Rul2);
  }
  *Clusters = ATreverse(Newclusters);
  return N;
}

ATermList params(ATerm term) {
  /* Returns the parameters (state variables) that occur in term */
  ATermList Args, Result;
  int j;
  j = (int)ATindexedSetGetIndex(Parnames,term);
  if ( j>= 0)
    return ATmakeList1((ATerm)ATmakeInt(j));

  Args = ATgetArguments((ATermAppl)term);
  Result=ATmakeList0();
  while (!ATisEmpty(Args)) {
    Result = set_union(params(ATgetFirst(Args)),Result);
    Args=ATgetNext(Args);
  }
  return Result;
}

void Find_relevance(ATerm Belongs, ATermList Clusters) {
  int k;
  
  ATerm Todo = (ATerm)ATempty;
  ATermTable B = AdjacencyList2(Belongs);

  Relevant = (ATermIndexedSet*)calloc(Npars,sizeof(ATermIndexedSet));

  /* Step 1: Mark all parameters k in cluster j, which are directly
     used in action label or condition of summand i, to be relevant in
     state t, being the value of j determined by the condition of
     summand i.  Also put [t,k] on the Todo list for the breadth first
     search (i.e., k is relevant in state t).
  */

  for (k=0;k<Npars;k++) {
    ATerm clusters = ATtableGet(B,(ATerm)ATmakeInt(k));
    if (clusters) { // i.e., k is not a control flow parameter
      int i;
      Relevant[k] = ATindexedSetCreate(27,75);
      for (i=0;i<Nsums;i++) 
	if (!Removed[i] && Used_in_act_or_guard(lpo,i,k)) {
	  ATerm L=clusters;
	  ATerm cluster;
	  while (ATmatch(L,"[edge(<term>,<term>),<list>]",&cluster,NULL,&L)) {
	    ATerm src,sources;
	    int cl=ATindexedSetGetIndex(ClusterIndex,ATgetArgument((ATermAppl)cluster,0));
	    assert(cl>=0);
	    sources = Sources(AL[cl],i);
	    if (!sources) sources=(ATerm)ATempty;
	    while (ATmatch(sources,"[<term>,<list>]", &src,&sources)) {
	      ATbool b;
	      if (TEST) {
		ATerm cname;
		ATmatch(cluster,"cluster(<term>,<term>,<term>)",&cname,NULL,NULL);
		ATfprintf(stderr,
			  "%t is directly relevant in summand %d, where %t=%t",
			  MCRLprint(LPOgetParName(lpo,k)),i+1,
			  parameterlist(cname),MCRLprintList((ATermList)src));
	      }
	      ATindexedSetPut(Relevant[k],ATmake("pair(<term>,<term>)",cluster,src),&b);
	      if (b) {
		Todo = ATmake("[<int>,<term>,<term>,<list>]",k,cluster,src,Todo);
		if (TEST) fprintf(stderr," (new)");
	      }
	      if (TEST) fprintf(stderr,"\n");
	    }
	  }
	}
    }
  }
  
  /* Step 2: Start the breadth first search from Todo: Let (t,k) with
     with k in cluster j be relevant, i.e. parameter k is relevant
     when j=t).  then mark all (state,l) as relevant, where parameter
     l is used in any summand i leading to j=t, for updating parameter
     k, and state is the value of cluster[l] according to the
     condition of summand i.
   */
  
  { int k; ATerm cluster; ATerm trg;
  // work on first triple (k,cluster,trg) in Todo list, as long as non-empty
  while (ATmatch(Todo,"[<int>,<term>,<term>,<list>]",
		 &k,&cluster,&trg,&Todo)) {
    ATerm src,edges;
    int sum;
    int cl = ATindexOf(Clusters,cluster,0);
    if (TEST) {
      ATerm cname;
      ATmatch(cluster,"cluster(<term>,<term>,<term>)",&cname,NULL,NULL);
      ATfprintf(stderr,"%t,%t,%t\n",
		MCRLprint(LPOgetParName(lpo,k)),
		parameterlist(cname),
		MCRLprintList((ATermList)trg));
    }
    // Consider all edges (src,sum,tar) with target tar=t
    edges=SourcesLabels(AT[cl],trg);
    if (!edges) edges=(ATerm)ATempty;
    while (ATmatch(edges,"[edge(<term>,<int>,<term>),<list>]",
		   &src,&sum,NULL,&edges)) {
      ATerm par;
      ATerm P=(ATerm)params(LPOgetNext(lpo,sum,k));
      if (TEST) fprintf(stderr," %d:",sum+1);
      // Consider all parameters p in Next(sum,k):
      while (ATmatch(P,"[<term>,<list>]",&par,&P)) {
	ATerm L = ATtableGet(B,par);
	ATerm cluster2;
	int p = ATgetInt((ATermInt)par);
	if (!L) L=(ATerm)ATempty;
	if (TEST) ATfprintf(stderr," %t",MCRLprint(LPOgetParName(lpo,p)));
	// Consider all clusters c to which p belongs
	while (ATmatch(L,"[edge(<term>,<term>),<list>]",&cluster2,NULL,&L)) {
	  if (TEST) {
	    ATerm cname;
	    ATmatch(cluster2,"cluster(<term>,<term>,<term>)",&cname,NULL,NULL);
	    ATfprintf(stderr," -> %t ",parameterlist(cname));
	  }
	  if (cluster2==cluster) {
	    ATbool b;
	    if (TEST) 
	      ATfprintf(stderr,": %t is relevant in %t (same cluster)",
			MCRLprint(LPOgetParName(lpo,p)),MCRLprintList((ATermList)src));
	    ATindexedSetPut(Relevant[p],ATmake("pair(<term>,<term>)",cluster,src),&b);
	    if (b) {
	      Todo = ATmake("[<int>,<term>,<term>,<list>]"
			    ,   p  ,cluster,src  , Todo);
	      if (TEST) fprintf(stderr," (new)");
	    }
	  }
	  else {
	    ATermList L=(ATermList)ATtableGet(B,(ATerm)ATmakeInt(k));
	    if (ATindexOf(L,ATmake("edge(<term>,<int>)",cluster2,k),0)==-1) { 
	      /* k doesn't belong to cluster2 */
	      ATerm sources,src2;
	      int cl2 = ATindexedSetGetIndex(ClusterIndex,ATgetArgument((ATermAppl)(cluster2),0));
	      assert(cl2>=0);
	      sources=Sources(AL[cl2],sum);
	      if (!sources) sources=(ATerm)ATempty;
	      while (ATmatch(sources,"[<term>,<list>]",&src2,&sources)) {
		ATbool b;
		if (TEST)
		  ATfprintf(stderr,": %t relevant in %t (other cluster)",
			    MCRLprint(LPOgetParName(lpo,p)),MCRLprintList((ATermList)src2));
		ATindexedSetPut(Relevant[p],ATmake("pair(<term>,<term>)",cluster2,src2),&b);
		if (b) {
		  Todo = ATmake("[<int>,<term>,<term>,<list>]"
				,   p, cluster2, src2,  Todo);
		  if (TEST) fprintf(stderr," (new)");
		}
	      }
	    }
	    else if (TEST) fprintf(stderr," (neglected)");
	  }
	}
      }
      if (TEST) fprintf(stderr,"\n");
    }
  }
  }
  ATtableDestroy(B);
}

char Rel1(int sum, ATerm cl, int k,ATermTable AL) {
  /* Check if some destination value of cl in summand i is relevant for k
   */
  ATerm targets,trg;
  targets = Targets(AL,sum);
  if (!targets) targets=(ATerm)ATempty;
  while (ATmatch(targets,"[<term>,<list>]",&trg,&targets)) {
    if (ATindexedSetGetIndex(Relevant[k],ATmake("pair(<term>,<term>)",cl,trg))>=0)
      return 1;
  }
  return 0;
}

char Rel2(int i, ATerm Bclusters, int k) {
  /* Check if Rel1(i,cl,k) holds for all clusters cl 
   * that rule i and to which k belongs.
   * Note: if k is cluster parameter, it belongs to nothing, so 1 is returned.
   */
  ATerm cluster;
  if (!Bclusters) Bclusters=(ATerm)ATempty; // only applies when k is a cluster parameter
  // for all clusters to which k belongs:
  while (ATmatch(Bclusters,"[edge(<term>,<term>),<list>]",&cluster,NULL,&Bclusters)) {
    int c=ATindexedSetGetIndex(ClusterIndex,ATgetArgument((ATermAppl)cluster,0));
    assert(c>=0);
    if (RulesArray[c][i] && !Rel1(i,cluster,k,AL[c])) {
      if (TEST) ATfprintf(stderr,"%t is irrelevant in summand %d\n", 
			  MCRLprint(LPOgetParName(lpo,k)),i+1);
      return 0;
    }
  }
  if (TEST) ATfprintf(stderr,"%t is relevant in summand %d\n",
		      MCRLprint(LPOgetParName(lpo,k)),i+1);
  return 1;
}

char Rel0(ATermTable B, int k) {
  /* check if for all clusters cl to which k belongs,
   * its initial value is relevant for k
   */
  ATerm L = ATtableGet(B,ATmake("<int>",k));
  ATerm cluster;
  if (!L) L=(ATerm)ATempty; // only applies if k is cluster parameter
  while (ATmatch(L,"[edge(<term>,<term>),<list>]",&cluster,NULL,&L)) {
    ATerm init;
    ATmatch(cluster,"cluster(<term>,<term>,<term>)",NULL,&init,NULL);
    if (ATindexedSetGetIndex(Relevant[k],
			     ATmake("pair(<term>,<term>)",cluster,init)) < 0)
      return 0;
  }
  return 1;
}

void COPY_RELEVANT_INFORMATION(ATermList Clusters,ATerm Belongs) {
  int i,k;
  ATermTable B = AdjacencyList2(Belongs);

  New_Init=(ATerm*)calloc(Npars,sizeof(ATerm));
  ATprotectArray(New_Init,Npars);

  for (k=0;k<Npars;k++) {
    if (Rel0(B,k))
      New_Init[k]=LPOgetInit(lpo,k);
  }

  New_Next=(ATerm*)calloc(Npars*Nsums,sizeof(ATerm));
  ATprotectArray(New_Next,Npars*Nsums);

  for (k=0;k<Npars;k++) {
    ATerm Bclusters = ATtableGet(B,(ATerm)ATmakeInt(k));
    for (i=0;i<Nsums;i++)
      if (!Removed[i] && Rel2(i,Bclusters,k))
	  New_Next[i*Npars+k] = LPOgetNext(lpo,i,k);
  }
  ATtableDestroy(B);
}

static ATerm closeTerm(ATerm t) {
  int j;
  
  if (ATindexedSetGetIndex(Sumnames,t)>=0)
    return NULL; // sum variable
  
  j=ATindexedSetGetIndex(Parnames,t);
  if (j>=0) { // parameter
    if (New_Init[j])
      return New_Init[j];
    else
      return NULL;
  }
  
  { 
    ATerm Args[64];
    Symbol f = ATgetSymbol((ATermAppl)t);
    int N = ATgetArity(f);
    if (N>64) ATerror("Arity > 64");
    for (j=0;j<N;j++) {
      Args[j]=closeTerm(ATgetArgument((ATermAppl)t,j));
      if (!Args[j]) break;
    }
    if (j==N)
      return (ATerm)ATmakeApplArray(f,Args);
    else
      return NULL;
  }
}

static char is_value(ATerm t) {
  /* returns 1 if t consists of constructorsymbols only; 0 otherwise */
  if (MCRLgetTypeTerm(t)!=MCRLconstructor)
    return 0;
  else {
    int i,n=ATgetArity(ATgetSymbol(t));
    for (i=0; i<n; i++)
      if (!is_value(ATgetArgument(t,i))) 
	return 0;
    return 1;
  }
}

int Inits() {
  char progress=1;
  int k,N=0;

  while (progress--)
    for (k=0;k<Npars;k++) {
      int i;
      if (!New_Init[k])
	for (i=0;i<Nsums;i++) {
	  if (!Removed[i] && New_Next[i*Npars+k]) { // relevant 
	    ATerm t = closeTerm(New_Next[i*Npars+k]);
	    if (t) {
	      t = RWrewrite(t);
	      if (is_value(t)) {
		New_Init[k]=t;
		progress=1;
		if (t != LPOgetInit(lpo,k)) N++;
		break;
	      }
	    }
	  }
	}
    }
  
  for (k=0;k<Npars;k++)
    if (!New_Init[k])
      New_Init[k]=LPOgetInit(lpo,k);
  
  return N;
}

int Nexts() {
  int i,k,N=0;

  for (i=0;i<Nsums;i++) 
    if (!Removed[i]) {
      ATerm* new_next = New_Next+i*Npars;
      for (k=0;k<Npars;k++)
	if (!new_next[k]) {
	  if (NOCHANGE)
	    new_next[k]=LPOgetParName(lpo,k);
	  else
	    new_next[k]=New_Init[k];
	  if (new_next[k] != LPOgetNext(lpo,i,k)) N++; 
	}
    }
  return N;
}

ATerm New_LPO() {
  ATermList L,init;
  ATermList parameters=LPOgetParList(lpo);
  ATermList sums = LPOgetSumList(lpo);
  int i,j;

  init=ATmakeList0();
  for (j=Npars-1;j>=0;j--)
    init = ATinsert(init,New_Init[j]);
  
  L=ATreverse(sums);
  sums=ATmakeList0();
  for (i=Nsums-1;i>=0;i--) {
    if (!Removed[i]) {
      ATerm sum = ATgetFirst(L);
      ATermList new_next = ATmakeList0();
      for (j=Npars-1;j>=0;j--)
	new_next=ATinsert(new_next,New_Next[i*Npars+j]);
      sum = (ATerm)ATsetArgument((ATermAppl)sum,ATmake("i(<term>)",new_next),3);
      sums = ATinsert(sums,sum);
    }
    L=ATgetNext(L);
  }
  
  return ATmake("initprocspec(<term>,<term>,<term>))", init,parameters,sums);
}

ATermList check_eq_and_add(ATermList l, ATerm t) {
  ATermList k;
  char found=0;
  for (k=l; !found && !ATisEmpty(k); k=ATgetNext(k)) {
    ATerm E = RWrewrite(prEQ(ATgetFirst(k),t));
    if (E==prTRUE) found=1;
    else if (E!=prFALSE) {
      if (TEST) ATfprintf(stderr,"   %t =?= %t\n",MCRLprint(ATgetFirst(k)),MCRLprint(t));
      return NULL;
    }
  }
  return (found ? l : ATinsert(l,t));
}

ATermList CHECK_CLUSTERS() {
  int i,j;
  ATermList Clusters=ATmakeList0();

  for (j=0; j<Npars; j++) {
    char still_cluster=1;
    ATermList Values=ATmakeList1(RWrewrite(LPOgetInit(lpo,j)));
    /* Note: initial value will always stay at the end of Values */
    ATermList Edges = ATmakeList0();
    for (i=0; still_cluster && i<Nsums; i++) {
      ATermList l=sources(LPOgetGuard(lpo,i),LPOgetParName(lpo,j)); 
      if (!l) {
	if (Changed(lpo,i,j)) {
	  if (TEST) ATfprintf(stderr,"   parameter %t no cluster in summand %d (sources T)\n",
			    MCRLprint(LPOgetParName(lpo,j)),i+1);
	  still_cluster = 0;
	}
      }
      else {
	for (; still_cluster && !ATisEmpty(l); l=ATgetNext(l)) {
	  ATerm t=ATgetFirst(l);
	  if (!closed_term(t)) {
	    if (TEST) 
	      ATfprintf(stderr,"   parameter %t no cluster in %d (source not closed)\n",
		      MCRLprint(LPOgetParName(lpo,j)),i+1);
	    still_cluster=0;
	  }
	  else {
	    Values = check_eq_and_add(Values,t);
	    if (!Values) {
	      if (TEST) ATfprintf(stderr,"   parameter %t no cluster (eq undecided)\n",
				MCRLprint(LPOgetParName(lpo,j)));
	      still_cluster=0;
	    }
	    else {
	      ATerm s = destination(LPOgetNext(lpo,i,j),LPOgetParName(lpo,j),t);
	      Edges = (ATermList)ATmake("[edge([<term>],<int>,[<term>]),<list>]",
					t,i,s,Edges);
	      if (!closed_term(s)) {
		if (TEST) 
		  ATfprintf(stderr,"   parameter %t no cluster in %d (dest not closed)\n",
			    MCRLprint(LPOgetParName(lpo,j)),i+1);
		still_cluster=0;
	      }
	      else {
		Values = check_eq_and_add(Values,s);
		if (!Values) {
		  if (TEST) ATfprintf(stderr,"   parameter %t no cluster (eq undecided)\n",
				    MCRLprint(LPOgetParName(lpo,j)));
		  still_cluster=0;
		}
	      }
	    }
	  }
	}
      }
    }
    if (still_cluster) {
      Edges =ATreverse(Edges);
      if (VERBOSE) 
	ATfprintf(stderr,"Detected cluster: %t (%d values, %d edges)\n",
		MCRLprint(LPOgetParName(lpo,j)),ATgetLength(Values),ATgetLength(Edges));
      Clusters = (ATermList)ATmake("[cluster([<int>],[<term>],<term>),<list>]",
				   j,ATgetLast(Values),Edges,Clusters);
    }
  }
  return ATreverse(Clusters);
}

ATerm CHECK_BELONGS(ATermList Clusters) {
  ATermList Edges=ATmakeList0();
  while (!ATisEmpty(Clusters)) {
    int j,i,c;
    ATerm cluster,cname;
    char* Rules;
    ATmatch((ATerm)Clusters, "[<term>,<list>]", &cluster,&Clusters);
    ATmatch(cluster,"cluster(<term>,<term>,<term>)",&cname,NULL,NULL);
    c=ATindexedSetGetIndex(ClusterIndex,cname);
    Rules = RulesArray[c];
    for (j=0; j<Npars ; j++) {
      char belongs = 1;
      for (i=0; i<Nsums; i++)
	if (!Removed[i] && (Used(lpo,i,j) || Changed(lpo,i,j)) && !Rules[i]) {
	  belongs = 0;
	  if (TEST) ATfprintf(stderr,"%t doesn't belong to %t in summand %d\n",
			      MCRLprint(LPOgetParName(lpo,j)),parameterlist(cname),i+1);
	  break;
	}
      if (belongs) {
	if (TEST) ATfprintf(stderr,"%t belongs to %t\n",
			    MCRLprint(LPOgetParName(lpo,j)),parameterlist(cname));
	Edges = ATinsert(Edges,ATmake("edge(<term>,<int>)",cluster,j));
      }
    }
  }
  return (ATerm)Edges;
}

char Is_cluster(int i) {
  if (ATindexedSetGetIndex(ClusterIndex,ATmake("[<int>]",i))==-1)
    return 0;
  else
    return 1;
}

ATerm RESTRICT_BELONGS(ATerm Belongs) {
  ATerm edge;
  ATermList Result=ATmakeList0();
  while (ATmatch((ATerm)Belongs,"[<term>,<list>]",&edge,&Belongs)) {
    int j;
    ATmatch(edge,"edge(<term>,<int>)",NULL,&j);
    if (!Is_cluster(j))
      Result = ATinsert(Result,edge);
  }
  assert(ATisEmpty(Belongs));
  return (ATerm)ATreverse(Result);
}

char* RuleArray (ATerm edges) {
  char *Rules = (char*)calloc(Nsums,sizeof(char));
  ATerm edge;
  int i;
  for (i=0;i<Nsums;i++) Rules[i]=0;
  
  while (ATmatch((ATerm)edges, "[<term>,<list>]", &edge,&edges)) {
    int sum;
    ATmatch(edge,"edge(<term>,<int>,<term>)",NULL,&sum,NULL);
    Rules[sum]=1;
  }
  return Rules;
}

void CONSTRUCT_GLOBAL_INFO(ATermList Clusters) {
  int i=0;
  ATbool b;
  ATerm cluster,edges,cname;

  RulesArray = (char**)calloc(1000,sizeof(char*));
  AL = (ATermTable*)calloc(1000,sizeof(ATermTable));
  AS = (ATermTable*)calloc(1000,sizeof(ATermTable));
  AT = (ATermTable*)calloc(1000,sizeof(ATermTable));
  
  ClusterIndex=ATindexedSetCreate(100,50);
  while (ATmatch((ATerm)Clusters,"[<term>,<list>]",
		 &cluster,&Clusters)) {
    ATmatch(cluster,"cluster(<term>,<term>,<term>)",&cname,NULL,&edges);
    i = ATindexedSetPut(ClusterIndex,cname,&b);
    assert(b);
    RulesArray[i] = RuleArray(edges);
    AL[i] = AdjacencyLabel(edges);
    AS[i] = AdjacencySource(edges);
    AT[i] = AdjacencyTarget(edges);
  }
}

void ADD_DUMMY_CLUSTER(ATermList* Clusters, ATerm* Belongs) {
  ATermTable B = AdjacencyList2(*Belongs);
  ATerm dummy_cluster;
  ATerm Edges=(ATerm)ATempty;
  int i,k;
  ATbool b;

  /* Construct dummy-cluster (one boolean parameter, each summand T->T) */
  for (i=Nsums-1; i>=0; i--)
    Edges=ATmake("[edge([<term>],<int>,[<term>]),<list>]",prTRUE,i,prTRUE,Edges);
  dummy_cluster= ATmake("cluster([<int>],[<term>],<term>)",Npars,prTRUE,Edges);
  for (k=0;k<Npars;k++) {
    if (!Is_cluster(k) && !ATtableGet(B,(ATerm)ATmakeInt(k)))
      *Belongs=ATmake("[edge(<term>,<int>),<list>]",dummy_cluster,k,*Belongs);
  }
  *Clusters=ATappend(*Clusters,dummy_cluster);
  i=ATindexedSetPut(ClusterIndex,ATgetArgument((ATermAppl)dummy_cluster,0),&b);
  RulesArray[i]=RuleArray(Edges);
  AL[i]=AdjacencyLabel(Edges);
  AS[i]=AdjacencySource(Edges);
  AT[i]=AdjacencyTarget(Edges);
}

#define ATConcat(t1,t2) ((ATerm)ATconcat((ATermList)(t1),(ATermList)(t2)))

int PRODUCT(ATerm C1, ATerm C2,ATerm *C) {
  ATerm par1,par2,par;
  ATerm start1,start2,start;
  ATerm edges1,edges2,edges=(ATerm)ATempty;
  ATermTable AS1,AS2,AL1,AL2;
  char* Rules1,*Rules2;
  char* Rules = (char*)calloc(Nsums,sizeof(char));
  int i1 = ATindexedSetGetIndex(ClusterIndex,ATgetArgument((ATermAppl)C1,0));
  int i2 = ATindexedSetGetIndex(ClusterIndex,ATgetArgument((ATermAppl)C2,0));
  int i,N=0;
  ATbool new;

  ATmatch(C1,"cluster(<term>,<term>,<term>)",
	  &par1,&start1,&edges1);
  ATmatch(C2,"cluster(<term>,<term>,<term>)",
	  &par2,&start2,&edges2);
  par = ATConcat(par1,par2);
  start = ATConcat(start1,start2);

  AS1=AS[i1];
  AS2=AS[i2];
  AL1=AL[i1];
  AL2=AL[i2];
  Rules1 = RulesArray[i1];
  Rules2 = RulesArray[i2];

  /* There are four tasks:
   * 1. summands ruled by neither 1 nor 2 are not ruled by the product.
   * 2. summands ruled by both 1 and 2 should be merged
   * 3. summands ruled by 1, but not by 2 are duplicated
   * 4. summands ruled by 2, but not by 1 are duplicated
   */

  /* Task 1 */

  for (i=0;i<Nsums;i++)
    Rules[i]=Rules1[i] || Rules2[i];
  
  { 
    ATermList TODO = ATmakeList2(start1,start2);
    ATermIndexedSet Visited = ATtableCreate(2*Nsums,50);
    ATindexedSetPut(Visited,(ATerm)ATmakeList2(start1,start2),&new);
    while (!ATisEmpty(TODO)) {
      ATerm src1 = ATgetFirst(TODO);
      ATerm src2 = ATgetFirst(ATgetNext(TODO));
      ATerm trg1,trg2, Out1,Out2;
      int sum1,sum2;
      
      TODO = ATgetNext(ATgetNext(TODO));
      Out1 = LabelsTargets(AS1,src1);
      if (!Out1) Out1=(ATerm)ATempty;
      /* iterate all edges of component 1 */
      while (ATmatch(Out1,"[edge(<term>,<int>,<term>),<list>]",
		     NULL,&sum1,&trg1,&Out1)) {

	if (Rules2[sum1]) { 	/* Task 2 */
	  Out2 = Target(AL2,src2,sum1);
	  if (!Out2) Out2=(ATerm)ATempty;
	  /* iterate over all sum1-successors of src2 in component 2 */
	  while (ATmatch(Out2,"[<term>,<list>]",&trg2,&Out2)) {
	    edges = ATmake("[edge(<term>,<int>,<term>),<list>]",
			   ATConcat(src1,src2),sum1,ATConcat(trg1,trg2),edges);
	    Rules[sum1]=0;
	    ATindexedSetPut(Visited,(ATerm)ATmakeList2(trg1,trg2),&new);
	    if (new)
	      TODO = ATinsert(ATinsert(TODO,trg2),trg1);
	  }
	}
	else { /* Task 3 */
	  edges = ATmake("[edge(<term>,<int>,<term>),<list>]",
			   ATConcat(src1,src2),sum1,ATConcat(trg1,src2),edges);
	  Rules[sum1]=0;
	  ATindexedSetPut(Visited,(ATerm)ATmakeList2(trg1,src2),&new);
	  if (new)
	    TODO = ATinsert(ATinsert(TODO,src2),trg1);
	}
      }
      /* Task 4 */
      Out2 = LabelsTargets(AS2,src2);
      if (!Out2) Out2=(ATerm)ATempty;
      /* iterate all edges of component 2 that are not in component 1 */
      while (ATmatch(Out2,"[edge(<term>,<int>,<term>),<list>]",
		     NULL,&sum2,&trg2,&Out2))
	if (!Rules1[sum2]) {
	  edges = ATmake("[edge(<term>,<int>,<term>),<list>]",
			 ATConcat(src1,src2),sum2,ATConcat(src1,trg2),edges);
	  Rules[sum2]=0;
	  ATindexedSetPut(Visited,(ATerm)ATmakeList2(src1,trg2),&new);
	  if (new)
	    TODO = ATinsert(ATinsert(TODO,trg2),src1);
	}
    }
    if (TEST) 
      ATwarning("Computed graph of %t: %d values, %d edges",
		parameterlist(par),ATgetLength(ATindexedSetElements(Visited)),
		ATgetLength(edges));
    ATindexedSetDestroy(Visited);
  }
  
  for (i=0;i<Nsums;i++)
    if (Rules[i]) {
      if (!Removed[i]) N++;
      if (VERBOSE) ATfprintf(stderr,"Summand %d removed in cluster %t\n",
			  i+1,parameterlist(par));
      Removed[i]=1;
    }
  if (TEST) ATfprintf(stderr,"Removed %d more summands",N);

  free(Rules);
  *C = ATmake("cluster(<term>,<term>,<term>)",par,start,edges);
  return N;
}

int PRODUCTS(ATermList Clusters,ATermList Neigh) { 
  ATerm C1,C2;
  int Total=0;
  while (ATmatch((ATerm)Neigh,"[neighbor(<term>,<term>),<list>]",
		 &C1,&C2,&Neigh)) {
    ATerm C;
    int N=PRODUCT(C1,C2,&C);
    // if (TEST && VISUALIZE) DOT(ATmakeList1(C),stdout);
    if (!TEST) fprintf(stderr,".");
    Total += N;
  }
  if (!TEST) fprintf(stderr,"\n");
  return Total;
}

void PRODUCTS3(ATermList Clusters) {
  int i,j,k,l,N;
  N = ATgetLength(Clusters);
  for (i=0;i<N;i++)
    for (j=i+1;j<N;j++) {
      ATerm C;
      int ind;
      ATbool b;
      PRODUCT(ATelementAt(Clusters,i),ATelementAt(Clusters,j),&C);
      ind=ATindexedSetPut(ClusterIndex,ATgetArgument((ATermAppl)C,0),&b);
      AL[ind]=AdjacencyLabel(ATgetArgument((ATermAppl)C,2));
      AS[ind]=AdjacencySource(ATgetArgument((ATermAppl)C,2));
      RulesArray[ind]=RuleArray(ATgetArgument((ATermAppl)C,2));
      //      fprintf(stderr,"(%d,%d):\n",i,j);
      for (k=j+1;k<N;k++)
	for (l=k+1;l<N;l++) {
	  ATerm D;
	  int ind2,M;
	  PRODUCT(ATelementAt(Clusters,k),ATelementAt(Clusters,l),&D);
	  ind2=ATindexedSetPut(ClusterIndex,ATgetArgument((ATermAppl)D,0),&b);
	  AL[ind2]=AdjacencyLabel(ATgetArgument((ATermAppl)D,2));
	  AS[ind2]=AdjacencySource(ATgetArgument((ATermAppl)D,2));
	  RulesArray[ind2]=RuleArray(ATgetArgument((ATermAppl)D,2));
	  M=PRODUCT(C,D,&D);
	  fprintf(stderr,"(%d,%d,%d,%d) -> %d\n",i,j,k,l,M);
	}
    }
}

int PRODUCTS8(ATermList Clusters) {
  ATerm C12,C34,C56,C78,C1234,C5678,C12345678;
  int ind12,ind34,ind56,ind78,ind1234,ind5678;
  ATbool b;
  assert(ATgetLength(Clusters)>=8);
  
  PRODUCT(ATelementAt(Clusters,0),ATelementAt(Clusters,1),&C12);
  PRODUCT(ATelementAt(Clusters,2),ATelementAt(Clusters,3),&C34);
  PRODUCT(ATelementAt(Clusters,4),ATelementAt(Clusters,5),&C56);
  PRODUCT(ATelementAt(Clusters,6),ATelementAt(Clusters,7),&C78);

  ind12 = ATindexedSetPut(ClusterIndex,ATgetArgument((ATermAppl)C12,0),&b);
  ind34 = ATindexedSetPut(ClusterIndex,ATgetArgument((ATermAppl)C34,0),&b);
  ind56 = ATindexedSetPut(ClusterIndex,ATgetArgument((ATermAppl)C56,0),&b);
  ind78 = ATindexedSetPut(ClusterIndex,ATgetArgument((ATermAppl)C78,0),&b);

  AL[ind12]=AdjacencyLabel(ATgetArgument((ATermAppl)C12,2));
  AS[ind12]=AdjacencySource(ATgetArgument((ATermAppl)C12,2));
  RulesArray[ind12]=RuleArray(ATgetArgument((ATermAppl)C12,2));
  
  AL[ind34]=AdjacencyLabel(ATgetArgument((ATermAppl)C34,2));
  AS[ind34]=AdjacencySource(ATgetArgument((ATermAppl)C34,2));
  RulesArray[ind34]=RuleArray(ATgetArgument((ATermAppl)C34,2));
  
  AL[ind56]=AdjacencyLabel(ATgetArgument((ATermAppl)C56,2));
  AS[ind56]=AdjacencySource(ATgetArgument((ATermAppl)C56,2));
  RulesArray[ind56]=RuleArray(ATgetArgument((ATermAppl)C56,2));
  
  AL[ind78]=AdjacencyLabel(ATgetArgument((ATermAppl)C78,2));
  AS[ind78]=AdjacencySource(ATgetArgument((ATermAppl)C78,2));
  RulesArray[ind78]=RuleArray(ATgetArgument((ATermAppl)C78,2));
  
  PRODUCT(C12,C34,&C1234);
  PRODUCT(C56,C78,&C5678);
	 
  ind1234 = ATindexedSetPut(ClusterIndex,ATgetArgument((ATermAppl)C1234,0),&b);
  ind5678 = ATindexedSetPut(ClusterIndex,ATgetArgument((ATermAppl)C5678,0),&b);

  AL[ind1234]=AdjacencyLabel(ATgetArgument((ATermAppl)C1234,2));
  AS[ind1234]=AdjacencySource(ATgetArgument((ATermAppl)C1234,2));
  RulesArray[ind1234]=RuleArray(ATgetArgument((ATermAppl)C1234,2));

  AL[ind5678]=AdjacencyLabel(ATgetArgument((ATermAppl)C5678,2));
  AS[ind5678]=AdjacencySource(ATgetArgument((ATermAppl)C5678,2));
  RulesArray[ind5678]=RuleArray(ATgetArgument((ATermAppl)C5678,2));

  PRODUCT(C1234,C5678,&C12345678);
  return 0;
}

char Disjoint(const char* R1, const char* R2) {
  int i;
  for (i=0;i<Nsums;i++)
    if (R1[i] && R2[i]) return 0;
  return 1;
}

ATermList Neighbors(ATermList Clusters) {
  ATermList neigh=ATmakeList0();
  int i,j;
  for (i=0; i<ATgetLength(Clusters);i++)
    for (j=i+1; j<ATgetLength(Clusters);j++) {
      ATerm C1 = ATelementAt(Clusters,i);
      ATerm C2 = ATelementAt(Clusters,j);
      char* Rules1 = RulesArray[i];
      char* Rules2 = RulesArray[j];
      if (!Disjoint(Rules1,Rules2)) {
	neigh = (ATermList)ATmake("[neighbor(<term>,<term>),<list>]",C1,C2,neigh);
      }
    }
  return ATreverse(neigh);
}

ATermList DATA_DEPENDENCIES() {
  int i,j;
  ATbool new;
  ATermIndexedSet X = ATindexedSetCreate(1000,50);
  for (i=0;i<Nsums;i++)
    for (j=0;j<Npars;j++) {
      ATermList L = params(LPOgetNext(lpo,i,j));
      int x;
      while (ATmatch((ATerm)L,"[<int>,<list>]",&x,&L)) {
	ATindexedSetPut(X,ATmake("edge(<int>,<int>)",x,j),&new);
      }
    }
  return ATindexedSetElements(X);
}

static ATerm ClusterGraph(ATerm Cluster, FILE *fp) {
   int k = 0;
/* Returns this cluster. Argument 2 is a list of edges
   which has the same sequence as the written edges in the .dot file. 
   These written edges are tagged with their sequence numbers. The action name 
   of each edge is replaced by a list of summands belonging to that edge 
*/
    ATerm  cluster = ATgetArgument((ATermAppl) Cluster, 0),
           start =  ATgetArgument((ATermAppl) Cluster, 1);
    ATermList edges = (ATermList) ATgetArgument((ATermAppl) Cluster, 2),
    result = ATempty;       
    ATermTable X = ATtableCreate(100,75);
    /* Step 1: compress edges with the same source, target and action labels.
     *         X will be a function of the form  
     *         (source,action-label,target) -> [list of summands] 
     */
    ATerm src,trg, edge;
    int sum;
    /* for all edges of this cluster do */
    while (ATmatch((ATerm) edges,"[edge(<term>,<int>,<term>),<list>]",
                                        &src ,&sum , &trg, &edges)) {
      ATerm key = ATmake("edge(<term>,<term>,<term>)",
			 src,LPOgetAct(lpo,sum),trg);
      ATermList L = (ATermList)ATtableGet(X,key);
      if (!L) 
	L = (ATermList)ATmake("[<int>]",sum);
      else
	L = (ATermList)ATmake("[<int>,<list>]",sum,L);
      ATtablePut(X,key,(ATerm)L);
    }  
    /* Step 2: generate DOT output for parameter names and initial state */
    fprintf(fp,"digraph Cluster {\n");
    ATfprintf(fp,"\"Control flow %t\" [shape=box] ;\n",parameterlist(cluster));
    ATfprintf(fp,"\"%t\" [peripheries=2] ;\n",
    MCRLprintList(RWrewriteList((ATermList)start)));
    /* Step 3: generate DOT output for all compressed edges in X */
    edges = ATtableKeys(X);
    while (ATmatch((ATerm)edges,"[<term>,<list>]",&edge,&edges)) {
      ATermList L = ATreverse((ATermList)ATtableGet(X,edge));
      ATerm src, act, tar;
      ATmatch(edge,"edge(<term>,<term>,<term>)",&src,&act,&tar);
      result = ATinsert(result, (ATerm) 
             ATsetArgument((ATermAppl) edge, (ATerm) L, 1));
      ATfprintf(fp,"\"%t\" -> \"%t\" [label=\"%t",
      MCRLprintList(RWrewriteList((ATermList)src)), 
      MCRLprintList(RWrewriteList((ATermList)tar)), 
                MCRLprint(act));
      if (SUMMANDS) { /* generate formatted list of summands */
	
	int i=1,nl = ceil(sqrt(ATgetLength(L))),c;
	fprintf(fp,"\\n (");
	/* for all summand labels do */
	while (ATmatch((ATerm)L,"[<int>,<list>]",&c,&L)) {
	  fprintf(fp,"%d",c+1);
	  if (!ATisEmpty(L)) {
	    fprintf(fp," ");
	    if (i==nl) {
	      fprintf(fp,"\\n");i=0;
	    }
	  }
	  i++;
	}
	assert(ATisEmpty(L));
	fprintf(fp,")");
      }
      fprintf(fp,"\",tag = %d] ;\n", k++);
    }
    assert(ATisEmpty(edges));
    fprintf(fp,"}\n");
    ATtableDestroy(X);
    return (ATerm) 
    ATsetArgument((ATermAppl) Cluster, (ATerm) 
    ATreverse(result), 2);
    }
    
static void DOT(ATermList Clusters, FILE* fp) {
  for (;!ATisEmpty(Clusters);Clusters=ATgetNext(Clusters))
         ClusterGraph(ATgetFirst(Clusters), fp);
  }

void DOT2(ATermList Belongs, FILE* fp) {
  fprintf(fp,"digraph Belongs {\n");
  fprintf(fp,"\"Control over Data\" [shape=box]\n");
  while (!ATisEmpty(Belongs)) {
    int c,j;
    ATerm cluster;
    if (!ATmatch(ATgetFirst(Belongs),"edge(<term>,<int>)",&cluster,&j))
      ATerror("unexpected edge '%t'\n",ATgetFirst(Belongs));
    if (!ATmatch(cluster,"cluster([<int>],<term>,<term>)",&c,NULL,NULL))
      ATerror("cannot draw belongs graph for cluster >1 %t",cluster);
    Belongs = ATgetNext(Belongs);
    ATfprintf(fp,"\"%t\" -> \"%t\" ;\n",
	      (c==Npars ? ATmake("default_pc") : MCRLprint(LPOgetParName(lpo,c))),
	      MCRLprint(LPOgetParName(lpo,j)));
  }
  fprintf(fp,"}\n");
}

void DOT3(ATermList Neigh, ATermList Clusters, FILE* fp) {
  ATerm node=NULL;
  fprintf(fp,"graph Neighbors {\n");
  fprintf(fp,"\"Components & \\nInterconnections\" [shape=box]\n");
  while (!ATisEmpty(Neigh)) {
    ATerm src,trg;
    if (!ATmatch(ATgetFirst(Neigh),
		 "neighbor(cluster(<term>,<term>,<term>),cluster(<term>,<term>,<term>))",
		 &src,NULL,NULL,&trg,NULL,NULL))
      ATerror("%t\n",Neigh);
    Neigh = ATgetNext(Neigh);
    ATfprintf(fp,"\"%t\" -- \"%t\" ;\n",parameterlist(src),parameterlist(trg));
  }
  
  while (ATmatch((ATerm)Clusters,"[<term>,<list>]",&node,&Clusters))
    ATfprintf(fp,"\"%t\" [shape=box]", parameterlist(ATgetArgument(node,0)));
  fprintf(fp,"}\n");
}

static ATermList GrappaLabels(ATermList Clusters) {
  return Clusters;
  }
  
static ATerm Grappa(ATerm pair, FILE* fp) {
  ATerm node=NULL;
  ATermList Neigh = (ATermList) ATgetArgument((ATermAppl) pair, 0),
  Clusters = (ATermList) ATgetArgument((ATermAppl) pair, 1);
  int i =0;
  
  fprintf(fp,"graph Neighbors {\n");
  fprintf(fp,"\"Components & \\nInterconnections\" [shape=box]\n");
  while (!ATisEmpty(Neigh)) {
    ATerm src,trg, lab;
    if (!ATmatch(ATgetFirst(Neigh),
		 "neighbor(cluster(<term>,<term>,<term>),cluster(<term>,<term>,<term>))",
		 &src,NULL,NULL,&trg,NULL,NULL))
      ATerror("%t\n",Neigh);
    Neigh = ATgetNext(Neigh);
    /* ATwarning("QQ2 %t", src); */
    ATfprintf(fp,"\"%t\" -- \"%t\";\n",
    parameterlist(src),parameterlist(trg));
  }
  while (ATmatch((ATerm)Clusters,"[<term>,<list>]",&node,&Clusters))
    ATfprintf(fp,"\"%t\" [shape=box, tag=%d]", 
         parameterlist(ATgetArgument(node,0)), i++);
  fprintf(fp,"}\n");
  return ATmake("<int>",0);
}

static ATerm PlainGraph(ATerm args, PLAINGRAPH proc) {
    char cmd[256], buf[256], fname[256];
    ATerm result = NULL, extra = NULL;
    int siz;
    FILE *fromDot = TempFile(fname, 256);
    if (!fromDot) {
        perror(fname);
        return NULL;
        }
    fclose(fromDot);
    snprintf(cmd,256, "dot >%s", fname);
       {
       FILE *toDot = Popen(cmd, "w");
       if (!toDot) {
           perror("Cannot start \"dot\"");
           return NULL;
           }
       extra = proc(args, toDot);
       Pclose(toDot);
       }
       fromDot = fopen(fname,"r");
       if (!fromDot) {
         perror(fname);
         return NULL;
         }
       {
       fseek(fromDot, 0, SEEK_END);
       siz = ftell(fromDot);
       rewind(fromDot);
       }
       {
       char *data = (char*) calloc(siz+1, sizeof(char));
       int d = fread(data, sizeof(char), siz, fromDot);
       if (d!=siz) {
           sprintf(buf, "There are %d characters read - expected %d",
           d, siz);
           perror(buf);
           return NULL;
           }
       /* result = <dot output belonging to a graph, extra information
                    about that graph (result of parameter proc)> */
       result =  ATmake("pair(<term>,<term>)",
           ATmake("<str>",  data),extra);
       /* ATwarning("result = %t", result); */
       free(data); 
       }
    fclose(fromDot);
    RemoveFile(fname);
    return result;    
    }
    
static ATermList StateGraphs(ATermList Clusters) {
    ATermList result = ATempty;
    for (;!ATisEmpty(Clusters);Clusters=ATgetNext(Clusters)) {
         result = ATinsert(result, 
             PlainGraph(ATgetFirst(Clusters), ClusterGraph)); 
        }
    /* ATwarning("QQ: Cluster edges summands %t", ATreverse(result)); */
    return ATreverse(result);
    }
        
void DOT4(ATermList Belongs, FILE* fp) {
  fprintf(fp,"digraph Dependencies {\n");
  fprintf(fp,"\"Data Dependencies\" [shape=box]\n");
  while (!ATisEmpty(Belongs)) {
    int c,j;
    if (!ATmatch(ATgetFirst(Belongs),"edge(<int>,<int>)",&c,&j))
      ATerror("unexpected edge '%t'\n",ATgetFirst(Belongs));
    Belongs = ATgetNext(Belongs);
    ATfprintf(fp,"\"%t\" -> \"%t\" ;\n",
	      MCRLprint(LPOgetParName(lpo,c)),
	      MCRLprint(LPOgetParName(lpo,j)));
  }
  fprintf(fp,"}\n");
}


ATermTable AdjacencyList1 (ATermList Clusters, ATerm Belongs) {
  ATermTable X = ATtableCreate(100,50);
  ATerm edge,c;
  while (ATmatch(Clusters,"[cluster([<term>],<term>,<term>),<list>]",&c,NULL,NULL,&Clusters))
    ATtablePut(X,c,ATempty);
  
  while (ATmatch(Belongs,"[<term>,<list>]",&edge,&Belongs)) {
    ATerm src;
    if (!ATmatch(edge,"edge(cluster([<term>],<term>,<term>),<term>)",&c,NULL,NULL,&src))
      ATerror("error");
    ATtablePut(X,c,(ATerm)ATinsert((ATermList)ATtableGet(X,c),src));
  }
  return X;
}

static ATermList myOR(ATermList x,ATermList y) {
  /* Interpret x and y as conjunctions; basically take intersection
     encodings: [] means TRUE, prFALSE means FALSE (no list, sorry)
  */
  ATerm eq;
  ATermList Result=ATempty;
  if (y==prFALSE) return x;
  while (ATmatch(x,"[<term>,<list>]",&eq,&x))
    if (ATindexOf(y,eq,0)>=0)
      Result=ATinsert(Result,eq);
  return ATreverse(Result);
}

static ATerm Conjunction(ATermList x) {
  /* Interpret x as a conjunction; basically take intersection
     encodings: [] means TRUE, prFALSE means FALSE (no list, sorry)
  */
  ATerm Result=prTRUE, par,val;
  if (x==prFALSE) return x;
  while (ATmatch(x,"[eq(<term>,<term>),<list>]",&par,&val,&x))
    Result = prAND(prEQ(par,val),Result);
  return RWrewrite(Result);
}

void INVARIANTS(ATermList Clusters,ATermList Belongs) {
  /* Clusters: ATermList of cluster([parameter_index],initial_value,transitions)
     here a transition is of the form: edge([source],summand,[target]) 
     Belongs: ATermList of edges: edge(cluster:ATerm,par:int) (cf. DOT2)

     Currently all generated invariants are of the form:
       if pc=value then ... && parameter=value && ...
     Invariants: each (cluster,state)-pair is mapped to a list of equalities
 */
  int c,i,k,changed=1;
  ATerm cluster,init,trg,Invariant=prTRUE;
  ATermList edges,OldClusters=Clusters;
  ATermTable B = AdjacencyList1(Clusters,Belongs);
  ATermTable Invariants = ATtableCreate(100,50);
  
  ATwarning("Propagating constants based on invariants");
 while(changed) {
  ATfprintf(stderr,".");
  changed=0;
  Clusters=OldClusters;
  for (;ATmatch(Clusters,"[<term>,<list>]",&cluster,&Clusters);) {
    ATermTable Inv = ATtableCreate(30,50);
    ATermList prop;

    if (!ATmatch(cluster,"cluster([<int>],<term>,<term>)",&c,&init,&edges)) 
      ATerror("only clusters of one parameter expected");

    if (c != Npars) { // dummy cluster pc_default
      int ci = ATindexedSetGetIndex(ClusterIndex,ATgetArgument(cluster,0));
      ATermList L, Keys;
      ATerm value;

      //all states in cluster get invariant FALSE by default
      for(L=edges;ATmatch(L,"[edge(<term>,<int>,<term>),<list>]",NULL,&i,&trg,&L);)
	ATtablePut(Inv,trg,prFALSE);
      
      // initial cluster state gets invariant derived from initial lpo state
      L=ATtableGet(B,ATmakeInt(c));
      if (TEST) ATfprintf(stderr,"cluster %t: parameters: %t\n", 
			  MCRLprint(LPOgetParName(lpo,c)),L);
      prop=ATempty;
      for (;ATmatch(L,"[<int>,<list>]",&k,&L);) 
	prop = ATinsert(prop,ATmake("eq(<term>,<term>)",
				    LPOgetParName(lpo,k),LPOgetInit(lpo,k)));
      ATtablePut(Inv,init,prop);
      
      // all cluster states get as invariant disjunction of incoming edges
      for(;ATmatch(edges,"[edge(<term>,<int>,<term>),<list>]",NULL,&i,&trg,&edges);) {
	ATermList L = ATtableGet(B,ATmakeInt(c));
	ATermList prop=ATempty;
	for (;ATmatch(L,"[<int>,<list>]",&k,&L);) {
	  ATerm nextk=LPOgetNext(lpo,i,k);
	  if (closed_term(nextk))
	    prop=ATinsert(prop,ATmake("eq(<term>,<term>)",LPOgetParName(lpo,k),nextk));
	}
	ATtablePut(Inv,trg,myOR(prop,ATtableGet(Inv,trg)));
      } /* for all edges in this cluster */
      Keys = ATtableKeys(Inv);
      while (ATmatch(Keys,"[<term>,<list>]",&value,&Keys)) {
	ATtablePut(Invariants,ATmake("pair(<term>,<term>)",cluster,ATgetFirst((ATermList)value)),
		   ATtableGet(Inv,value));
	Invariant = prAND(prIMPLIES(prEQ(LPOgetParName(lpo,c),ATgetFirst((ATermList)value)),
				    Conjunction(ATtableGet(Inv,value))),
			  Invariant);
      } /* end while more invariants to process */
    } /* end if */
    ATtableDestroy(Inv);
  } /* end for all clusters */
  assert(ATisEmpty(Clusters));
  
  /* propagate invariant forward over control flow edges */
  for (i=0;i<Nsums;i++) {
    ATerm cluster;
    Clusters=OldClusters;
    while (ATmatch(Clusters,"[<term>,<list>]",&cluster,&Clusters)) {
      int ci = ATindexedSetGetIndex(ClusterIndex,ATgetArgument(cluster,0));
      int c = ATgetInt((ATermInt)ATgetFirst((ATermList)ATgetArgument(cluster,0)));
      if ((c!=Npars) && RulesArray[ci][i]) {
	ATermList sources = Sources(AL[ci],i);
	ATerm I=prFALSE,src;

	/* collect the invariant for src */
	while (ATmatch(sources,"[[<term>],<list>]",&src,&sources)) {
	  ATerm t = ATtableGet(Invariants,ATmake("pair(<term>,<term>)",cluster,src)); 
	  if (t) I=myOR(t,I);
	  else ATfprintf(stderr,"ignored: %t\n",src);
	}
	if (TEST) ATfprintf(stderr,"%d:%t=%t -> %t\n",
			    i,MCRLprint(LPOgetParName(lpo,c)),MCRLprint(src),I);

	/* update summand with the invariant */
	{ ATerm par,val;
	  while (ATmatch(I,"[eq(<term>,<term>),<list>]",&par,&val,&I)) {
	    int k = ATindexedSetGetIndex(Parnames,par);
	    if (Used(lpo,i,k)||!Changed(lpo,i,k)) {
	      changed=1;
	      if (VERBOSE) ATfprintf(stderr,"Summand %d (component %t) --> %t:=%t\n",
			i+1,MCRLprint(LPOgetParName(lpo,c)),MCRLprint(par),MCRLprint(val));
	      RWassignVariable(ATgetSymbol(par),val,NULL,1);
	    } /* end if */
	    LPOrewriteSum(lpo,i);
	    RWresetVariables(1);
	  } /* end while more invariants */
	} /* end block */
      } /* end if */
    } /* end while more clusters */
  } /* end for all summands */
  /* TODO: can this be done more efficient? */

  if (!changed && INVARIANT) {
    ATprintf("%t\n",MCRLprint(RWrewrite(Invariant)));
    exit(0);
  }

  UCdestroy(lpo);
  UCinitialize(lpo);
  ATtableReset(Invariants);
  Invariant=prTRUE;

 } /* end while changed */
 ATfprintf(stderr,"\n");
}

FILE *Stategraph(int argc, char *argv[]) { 
  int N;
  ATermList Clusters, Neigh;
  ATerm Belongs;
  

parse_argument_line(&argc,&argv);

  ATprotect(&LPO2gen);
  ATprotect(&datatype);
 
  if (!MCRLgetProc()) 
       if (!MCRLinitRW(argc,argv)) ATerror("Error with MCRLinitialize");
  
  LPO2gen=MCRLgetProc();
  datatype=MCRLgetAdt();

  lpo = LPOfrom2gen(LPO2gen);
  Npars = LPOnPars(lpo);
  Nsums = LPOnSums(lpo);

  Initialize(lpo,datatype,argc,argv);
  ATwarning("Read %d summands and %d parameters", LPOnSums(lpo),LPOnPars(lpo));

 Clusters =  CHECK_CLUSTERS();
 CONSTRUCT_GLOBAL_INFO(Clusters);

 ATwarning("Identified %d clusters",ATgetLength(Clusters)); 
 // if (TEST && VISUALIZE) DOT(Clusters,stdout);

 N = Remove_sums(&Clusters);
 ATwarning("Removed %d summands",N);

 Neigh=Neighbors(Clusters);
 if (VISUALIZE) DOT3(Neigh,Clusters,stdout);
#ifdef GRAPPA
 if (VIEW) { 
      /* Write [Main, [clusters], taf] */
      ATerm lab = (ATerm) GrappaLabels(Clusters);
      ATerm clustergraph = PlainGraph(
            ATmake("pair(<term>, <term>)", Neigh, Clusters), Grappa);
      ATermList stategraphs = StateGraphs(Clusters);
      char fname[256], cmd[256];
      FILE *toJava = TempFile(fname, 256), *in;
      if (!toJava) {
         perror(fname);
         return NULL;
         }
      snprintf(cmd,256, "PATH=../prover/src:%s:$PATH;%s %s", DATADIR, STATEVIEW, fname);
      /* ATwarning("cmd=%s", cmd);  */ 
      in = Popen(cmd,"w");
      if (!in) {perror(cmd);return NULL;}
      /* [
         pair(clustergraph, 0), pair(stategraphs, stategraph_extras), 
         mcrlspecs]
         ] */  
      ATwriteToSharedTextFile(
      (ATerm) ATmakeList3(clustergraph, (ATerm) stategraphs, MCRLgetSpec()), 
      toJava);
      /* fprintf(in,".");  */
      fclose(toJava);
      /* RemoveFile(fname); */
      return in;
      }
#endif
 if (VISUALIZE) DOT(Clusters,stdout);

 // PRODUCTS8(Clusters);
 // exit(0);

 N = PRODUCTS(Clusters,Neigh);
 ATwarning("Removed %d more summands",N);

 ATwarning("Computing data-flow");
 Belongs  =  CHECK_BELONGS(Clusters);
 // if (VISUALIZE) DOT2((ATermList)Belongs,stdout);
 Belongs  = RESTRICT_BELONGS(Belongs);
 ADD_DUMMY_CLUSTER(&Clusters,&Belongs);

 if (VISUALIZE) DOT2((ATermList)Belongs,stdout);
 
 if (VISUALIZE) {
   ATermList C = DATA_DEPENDENCIES();
   DOT4(C,stdout);
 }

 if (INVARIANT||CONSTANT) INVARIANTS(Clusters,Belongs); // doesn't return if CONSTANT

 ATwarning("Doing Data Flow Analysis");
 Find_relevance(Belongs,Clusters);
 ATwarning("Building Result LPO");
 COPY_RELEVANT_INFORMATION(Clusters,Belongs);
 N = Inits();
 ATwarning("Changed initial value of %d parameters",N);
 // New_Init[j] contains new initial value of parameter j
 N = Nexts();
 ATwarning("Changed %d next state parameters in the remaining summands",N);
 // New_Next[i*Npars+j] contains the new j'th parameter of summand i
 
 if (!VISUALIZE && !VIEW) {
   MCRLsetProc(New_LPO());
   MCRLoutput();
   ATwarning("Written %d summands",ATgetLength(MCRLgetListOfSummands()));
 }
 return NULL;
}
