/* $Id: datatypes.c,v 1.7 2005/12/13 15:53:05 jfg Exp $ */
#define debug (0)
/* This file describes a C implementation of the abstract datatype
   describing abstract data types with both functions and constructors
   in Dams and Groote, A specification of an instantiator, for use in
   the context with the Toolbus.
   
   For every function described in Dams and Groote, a function of type
   `ATerm ' is generated. Type `ATerm ' is the type of terms that can be
   handled by the toolbus, and is described in Klint, A Guide to
   Toolbus Programming.  We use in particular functions ATmake,
   ATmatch, TBread, TBwrite, ATfprintf, TBsprintf 
 */
   
/* PREAMBLE */

#define rg_verbose (0)
#include "tmcrl.h"
#include "aterm2.h"

static ATerm dummyterm=NULL;
static char *dummystring=NULL;
static ATermTable comm_hashtable; /* hashtable for communication function */
static ATerm comm_term=NULL;
static ATerm emv_term=NULL;
static ATerm emt_term=NULL;
static ATerm delta_term=NULL;
static ATerm tau_term=NULL, tau_action=NULL;
static ATerm terminated_term=NULL;
static ATerm eml_term=NULL, eme_term=NULL, emf_term=NULL, ems_term=NULL;
static AFun ins2_symbol, ins3_symbol, ins4_symbol, t_symbol, alt_symbol,
            seq_symbol, par_symbol, lmer_symbol,cond_symbol,
            sum_symbol,com_symbol,bound_symbol,at_symbol,hide_symbol,
            rename_symbol,encap_symbol,name_symbol,smd_symbol,e_symbol,
            i_symbol, f_symbol,v_symbol;


/* static int noclash(ATerm vars, ATerm funcs);
static int eqterml(ATerm l1, ATerm l2);
static int nodoubles(ATerm t, ATerm vars);
static int notin(char *n, ATerm t, ATerm t1); */

static ATerm conc_tl(ATerm t, ATerm t1); 
static ATerm occursin(ATerm name,ATerm pars);
static int existvariablename(char *c);
static ATerm uniqueterm(char *sort, char *err_mes);
static ATerm maketerms(ATerm pars);
static int canterminatebody(ATerm t);
static int occursintermlist(char *s, ATerm l);
static int occursinvar(char *s, ATerm l);
static int occursinpCRLterm(char *s, ATerm p, int strict);
static char *getvarname(char *s,ATerm f);
static int existsand(char *);
static int existsnot(char *);
static ATerm construct_renaming(ATerm pars1, ATerm pars2,
                ATerm *pars3, ATerm *pars4);
static ATerm subtract(ATerm varlist0, ATerm varlist1, ATerm varlist2);
static void alphaconversion(int n, ATerm parameters);
/* static ATerm ignore(arglist *ignorelist,ATerm list); */


extern int to_file;
extern int to_toolbus;
extern int regular;
extern int regular2;
extern int cluster;
extern int nocluster;
extern int binary;
extern int oldstate;
extern int newtbf;
extern int statenames;

extern FILE *outfile;
int time_operators_used=0;
static arglist *seq_varnames=NULL;

char scratch1[ERRORLENGTH];
char scratch2[ERRORLENGTH];
char scratch3[ERRORLENGTH];

void rg_error(char *s, ATerm t)
{ 
  fprintf(stderr,"mcrl: %s\n",s);
  if (t!=NULL) ATfprintf(stderr,"Problematic term \"%t\" \n", t); 
  #ifdef NDEBUG
      exit(1);
  #else
      abort();
  #endif
}


/* Below we provide the basic functions to store and retrieve
   information about the signature of a datatype */

typedef struct enumeratedtype {
  int size;
  int sortnumber;
  arglist *elementnames; 
  arglist *functions;
  char * equality;
  struct enumeratedtype *next;
} enumeratedtype;

static enumeratedtype *enumeratedtypelist=NULL;

static enumeratedtype *create_enumeratedtype
                (int n,specificationbasictype *spec);

typedef struct sortdatatype {
  string *sortname;
  int constructor; } sortdatatype;
  
sortdatatype sortdata[MAXSORT+1];

typedef enum { none, map, func, act, proc, variable } objecttype;
typedef enum { unknown, mCRL, mCRLdone, mCRLbusy, mCRLlin, pCRL, 
            GNF, GNFalpha, GNFbusy,error } processstatustype;

typedef struct objectdatatype {
  string *objectname;
  arglist *args;
  arglist *representedprocesses;
  ATerm representedprocess;
  int targetsort; /* for actions target sort is used to
                        indicate the process representing this action.
*/
  ATerm processbody;
  ATerm parameters;
  processstatustype processstatus;
  objecttype object; 
  int canterminate; } objectdatatype;
  
objectdatatype objectdata[MAXOBJECT+1];

typedef struct searchtype {
  char indexch;
  int indexn;
  struct searchtype *nextindex;
  struct searchtype *nextitem;
  int n; } searchtype;

searchtype *sortroot=NULL;
int lastoccupiedsortnumber=0;

searchtype *objectroot=NULL;
int lastoccupiedobjectnumber=0;

searchtype *variablenameroot=NULL;
int lastoccupiedvariablenamenumber=0;

/* searchtype *actprocroot=NULL;
int lastoccupiedactprocnumber=0; */

arglist *emptyarglistlist=NULL;

static int strequal(char *s1,char *s2)
{ 
  return (strcmp(s1,s2)==0);
}

/* int termlistequal(ATerm l1, ATerm l2); */

/* static int termequal(ATerm t1, ATerm t2)
{ / * return t_equal(t1,t2); * /
  return ATisEqual(t1,t2);
  / * ATerm l1=NULL,l2=NULL;
  char *s1=NULL,*s2=NULL;
  if (!ATmatch(t1,"t(<str>,<term>)",&s1,&l1))
     rg_error("Expect ATerm  (1)",t1);
  if (!ATmatch(t2,"t(<str>,<term>)",&s2,&l2))
     rg_error("Expect ATerm  (2)",t2);
  if (strequal(s1,s2))
     return termlistequal(l1,l2);
  return 0;  * /
} */

static int termlistequal(ATerm l1, ATerm l2)
{ return ATisEqual(l1,l2);
  /* ATerm t1=NULL, t2=NULL;
  if (ATmatch(l1,"ins(<term>,<term>)",&t1,&l1))
     { if (ATmatch(l2,"ins(<term>,<term>)",&t2,&l2))
          return ((termequal(t1,t2))&&(termlistequal(l1,l2)));
       return 0;
     }
  if (l2==emt_term)
     { return 1;}
  return 0; */
}

static int variablesequal(ATerm t1, ATerm t2, /* XXXXXXXXXXXXXXX */
		ATerm *renamingvariablelist,
		ATerm *renamingtermlist)
{ /* return t_equal(t1,t2); */
  char *s1=NULL,*s2=NULL,*s3=NULL,*s4=NULL;
  /* ATfprintf(stdout,"XXXX %t -- %t\n",t1,t2); */
  *renamingvariablelist=emv_term;
  *renamingtermlist=emt_term;
  for(;ATmatch(t1,"ins(<str>,<str>,<term>)",&s1,&s2,&t1);)
    { if (!ATmatch(t2,"ins(<str>,<str>,<term>)",&s3,&s4,&t2))
         return 0;
      if ((!strequal(s2,s4)))
         return 0;
      else 
	 { if (!strequal(s1,s3))
	   { *renamingvariablelist=ATmake("ins(<str>,<str>,<term>)",
                 s1,s2,
		*renamingvariablelist);	
	     *renamingtermlist=ATmake("ins(t(<str>,emt),<term>)",
	        s3,
	        *renamingtermlist);
	 } }
    }
  if (t2==emv_term) 
  { /* ATfprintf(stdout,"Vars %t\nTerms %t\n:",
		    *renamingvariablelist,*renamingtermlist); */
    return 1;
  }	  
  return 0; 
}

static int eqarglist(arglist *a,arglist *b)
{ if (a==NULL)
   { if (b==NULL) 
        return 1;
     else return 0; }
  if (b==NULL)
     return 0;
  if (a->n==b->n) 
     return eqarglist(a->next,b->next);
  return 0;
}
 
static void printarglist(arglist *a)
{ if (a==0) 
   { fprintf(stderr,"*\n"); 
     return; }
  fprintf(stderr,"%d ",a->n);
  printarglist(a->next);
} 

void release_arglist(arglist *c)
/* releases a whole list of arguments */
{ 
  c->next = emptyarglistlist;
  emptyarglistlist = c;
  c->n=0;
}

void release_totalarglist(arglist *c)
/* releases a whole list of arguments */
{ arglist *d;
  for( ; (c!=NULL) ; )
     { d=c->next;
       c->next = emptyarglistlist;
       emptyarglistlist = c;
       c->n=0;
       c=d;
     }
}

arglist *new_arglist(int s, arglist *a)
{
  arglist *c;
  
  if (emptyarglistlist == NULL) {
    { c = (arglist *)malloc(sizeof(arglist));
      if (c==NULL) return NULL;}
  } else {
    c = emptyarglistlist;
    emptyarglistlist = emptyarglistlist->next;
  }
  c->next=a;
  c->n=s;
  return c;
}


searchtype *emptysearchtypelist=NULL;

static void release_searchtype(searchtype *c)
{
  c->nextindex = emptysearchtypelist;
  emptysearchtypelist = c;
  c->indexch='\1';
  c->indexn=0;
  c->nextitem=NULL;
  c->n=0;
}

static searchtype *new_searchtype(char indexch, int indexn,
            searchtype *nextindex, searchtype *nextitem, int n)
{
  searchtype *c;
  
  if (emptysearchtypelist == NULL) {
    { c = (searchtype *)malloc(sizeof(searchtype));
      if (c==NULL) return NULL;}
  } else {
    c = emptysearchtypelist;
    emptysearchtypelist = emptysearchtypelist->nextindex;
  }
  c->indexch=indexch;
  c->indexn=indexn;
  c->nextindex=nextindex;
  c->nextitem=nextitem;
  c->n=n;
  return c;
}

string *emptystringlist =NULL;

static void release_string(string *c)
{
  
  c->next = emptystringlist;
  emptystringlist = c;
  strncpy(&c->s[0],"",MAXLEN);
}

string *new_string(char *s)
{
  string *c;
  
  if (emptystringlist == NULL) {
    { c = (string *)malloc(sizeof(string));
      if (c==NULL) return NULL;}
  } else {
    c = emptystringlist;
    emptystringlist = emptystringlist->next;
  }
  c->next=NULL;
  strncpy(&c->s[0],s,MAXLEN);
  return c;
}
  
static int terminated(char *c, arglist *a, searchtype *w)
{ if (w==NULL) return 1;
  if ((a==NULL) && (c[1]=='\0')) return 1;
  if ((c[0]=='\0') && (a->next==NULL)) return 1;
  return 0;
}

static void increment(char **c, arglist **a)
{ if (**c=='\0')
     *a=(*a)->next; /* **a cannot be NULL */
  else (*c)+=1;
}

static int less(searchtype *w, char *c, arglist *a)
{ 
  if (w==NULL) return 0;
  if (w->indexch=='\0')
     { 
       if (*c=='\0')
          return (a->n<w->indexn);
       else return 0;
     }
  else 
    { 
      if (*c=='\0')
         return 1;
      else return(w->indexch<*c);
    }
}

static int equal(char *c, arglist *a, searchtype *w)
{ if (w==NULL) return 0;
  if (*c=='\0') return (a->n==w->indexn);
  return (*c==w->indexch);
}

static int exist(char *c, arglist *a, searchtype *walker)
/* Delivers 0 if sort does not exists. Otherwise a number>0
   indicating the index of the sort */
{ arglist *help;
  if rg_verbose fprintf(stderr,"Exist %s? ",c);
  if rg_verbose for (help=a; (help!=NULL) ; help=help->next)
               { fprintf(stderr,"%d ",help->n);}
  for( ; (less(walker,c,a)) ; walker=walker->nextindex){};
  for ( ; (equal(c,a,walker) && !terminated(c,a,walker)) ; )
      { /* at this point walker!=NULL */
        walker=walker->nextitem;
        increment(&c,&a);
        for( ; (less(walker,c,a)) ; walker=walker->nextindex){};
      }
  if (walker==NULL) 
     { if rg_verbose fprintf(stderr,"No\n");
       return 0; }
  if (equal(c,a,walker)) 
     {  if rg_verbose fprintf(stderr,"Yes: %d\n",walker->n);
     return walker->n; }
 if rg_verbose fprintf(stderr,"Nono\n");
  return 0;
}

static int veryterminated(char *c, searchtype *w)
{ if (w==NULL) return 1;
  if (c[1]=='\0') return 1;
  if (c[0]=='\0') return 1;
  return 0;
}

static void veryincrement(char **c)
{ (*c)+=1; }

static int veryless(searchtype *w, char *c)
{ 
  if (w==NULL) return 0;
  if (w->indexch=='\0')
     return 0;
  else 
    { if (*c=='\0')
         return 0;
      else return(w->indexch<*c);
    }
}

static int veryequal(char *c, searchtype *w)
{ if (w==NULL) return 0;
  if (*c=='\0') return 1;
  return (*c==w->indexch);
}

static int existatall(char *c, searchtype *walker)
/* Delivers 0 if sort does not exists. Otherwise a number>0
   indicating the index of the sort */
{ 
  if rg_verbose fprintf(stderr,"Existatall %s? ",c);
  for( ; (veryless(walker,c)) ; walker=walker->nextindex){};
  for ( ; (veryequal(c,walker) && !veryterminated(c,walker)) ; )
      { /* at this point walker!=NULL */
        walker=walker->nextitem;
        veryincrement(&c);
        for( ; (veryless(walker,c)) ; walker=walker->nextindex){};
      }
  if (walker==NULL) 
     { if rg_verbose fprintf(stderr,"No\n");
       return 0; }
  if (veryequal(c,walker)) 
     {  if rg_verbose fprintf(stderr,"Yes: %d\n",walker->n);
        return 1; }
 if rg_verbose fprintf(stderr,"Nono\n");
  return 0;
}

static int delete(char *c, arglist *a, searchtype *walker)
/* Delivers 0 if sort does not exists. Otherwise delivers 1
   if item is succesfully removed */
{ arglist *help;
  if rg_verbose fprintf(stderr,"Delete %s? ",c);
  if rg_verbose for (help=a; (help!=NULL) ; help=help->next)
     { fprintf(stderr,"%d ",help->n);}
  for( ; (less(walker,c,a)) ; walker=walker->nextindex){};
  for ( ; (equal(c,a,walker) && !terminated(c,a,walker)) ; )
      { /* at this point walker!=NULL */
        walker=walker->nextitem;
        increment(&c,&a);
        for( ; (less(walker,c,a)) ; walker=walker->nextindex){};
      }
  if (walker==NULL)
     { if rg_verbose fprintf(stderr,"No\n");
       return 0; }
  if (equal(c,a,walker))
     { release_string(objectdata[walker->n].objectname);
       objectdata[walker->n].objectname=NULL;
       release_totalarglist(objectdata[walker->n].args);
       objectdata[walker->n].args=NULL;
       objectdata[walker->n].targetsort=0;
       objectdata[walker->n].object=none;
       if (lastoccupiedobjectnumber==walker->n)
           lastoccupiedobjectnumber--;
       else fprintf(stderr,"spoiling an objectposition\n");
       walker->n=0;
       if rg_verbose fprintf(stderr,"Gone\n");
       return 1;}
  return 0;
}

static int insert_rec(char *c, arglist *a, searchtype **start, int n)
/* Delivers 0 if sort cannot be added when sort exists.
   Delivers -1 if there are too many sorts.
   Delivers -2 if there is no room to store the
   sort. Otherwise a number>0
   indicating the index of the sort */
{ 
  searchtype *walker=NULL, *backwalker=NULL;
  for (walker=*start ; (less(walker,c,a)) ; walker=walker->nextindex )
      { backwalker=walker; }
  if (equal(c,a,walker))
     { if (terminated(c,a,walker)) 
          { if (walker->n>0) return 0; /*sortname does exist */ 
            walker->n=n; return n;
          }
       else { increment(&c,&a);
              return insert_rec(c,a,&walker->nextitem,n); }
     }
  /* !equal(c,a,walker) */     
  if (walker==NULL)
     { if (backwalker==NULL)
          *start=walker=new_searchtype(c[0],((*c=='\0')?a->n:0),NULL,NULL,0);
       else walker=backwalker->nextindex=

       new_searchtype(c[0],((*c=='\0')?a->n:0),NULL,NULL,0);
       if (walker==NULL) return -2; 
     }
  /* walker!=NULL */
  if (backwalker==NULL)

*start=walker=new_searchtype(c[0],((*c=='\0')?a->n:0),walker,NULL,0);
  else walker=backwalker->nextindex=
  new_searchtype(c[0],((*c=='\0')?a->n:0),walker,NULL,0);
  if (walker==NULL) return -2; 

  if (terminated(c,a,walker))
     { walker->n =n;
       return n; }
  increment(&c,&a);
  return insert_rec(c,a,&walker->nextitem,n);
}

static int is_used(char *c)
{ if (exist(c,NULL,sortroot)>0) return 1;
  if (existatall(c,objectroot)>0) return 1;
  if (existvariablename(c)>0) return 1;
  return 0;
}


int existsort(char *c)
/* Delivers 0 if sort does not exists. Otherwise a number>0
   indicating the index of the sort */
{ return exist(c,NULL,sortroot); }


int insertsort(char *c, int constructorsort)
/* Delivers 0 if sort cannot be added when sort exists.
   Delivers -1 if there are too many sorts. 
   Returns -2 if there is no room to store the string.
   Otherwise a number>0
   indicating the index of the sort */
{ int n;
  if (lastoccupiedsortnumber==MAXSORT)
     return -1;
  n=insert_rec(c,NULL,&sortroot,lastoccupiedsortnumber+1);
  if rg_verbose fprintf(stderr,"Insertsort: %s # %d\n",c,n);
  if (n<=0)
     return n;
  sortdata[n].sortname=new_string(c);
  if (sortdata[n].sortname==NULL) return -2;
  lastoccupiedsortnumber=n;
  sortdata[n].constructor=constructorsort;
  return n;
}

static int existvariablename(char *c)
/* Delivers 0 if sort does not exists. Otherwise a number>0
   indicating the index of the sort */
{ return exist(c,NULL,variablenameroot); }


int insertvariablename(char *c)
/* Delivers 0 if variablenamr exists.
   Otherwise a number>0
   indicating the index of the new variablename */
{ int n;
  n=insert_rec(c,NULL,&variablenameroot,lastoccupiedsortnumber+1);
  if rg_verbose fprintf(stderr,"Insertvariablename: %s # %d\n",c,n);
  if (n<=0)
     return n;
  lastoccupiedvariablenamenumber=n;  
  return n;
} 

static int upperpowerof2(int i)
/* function yields n for the smallest value n such that 
   2^n>=i. This constitutes the number of bits necessary
   to represent a number smaller than i. i is assumed to
   be at least 1. */
{ int n=0;
  int powerof2=1;
  for( ; powerof2< i ; n++)
  { powerof2=2*powerof2; }
  return n;
}

int makeconstructorsort(int n)
/* Delivers 0 if operation fails because sort n does not exist */
{ if ((n<=MAXSORT) && (n>0)) 
     {sortdata[n].constructor=1; return 1;}
  else return 0;   
}

static void remove_searchtype(searchtype *node,int sort)
{ if (node!=NULL)
     { if (node->n>0)
          { if (sort)
               { release_string(sortdata[node->n].sortname);
                 sortdata[node->n].sortname=NULL;
                 sortdata[node->n].constructor=0; }
            else 
               { release_string(objectdata[node->n].objectname);
                 release_totalarglist(objectdata[node->n].args);
                 objectdata[node->n].objectname=NULL;
                 objectdata[node->n].args=NULL;
                 objectdata[node->n].targetsort=0;
                 objectdata[node->n].object=none; }}
                 
       remove_searchtype(node->nextindex,sort);
       remove_searchtype(node->nextitem,sort);
       release_searchtype(node);
     }
}

static int existsobject(char *c, arglist *a) 
/* Delivers 0 if object does not exists. Otherwise a number>0
   indicating the index of the object */
{ return exist(c,a,objectroot); }

static int insertobject(char *c, arglist *a, int t, objecttype
object)
/* Delivers 0 if object cannot be added when sort exists.
   Delivers -1 if there are too many objects.
   Delivers -2 if there is no room to add new objects.
   Otherwise a number>0 indicating the index of the object.
   The string is copied to a save space in memory. The arglist is re-used */
{ int n;
  arglist *help;
 
  if (lastoccupiedobjectnumber==MAXOBJECT)
     return -1;
  n=insert_rec(c,a,&objectroot,lastoccupiedobjectnumber+1);
  if rg_verbose fprintf(stderr,"Insertobject: %s ",c);
  if rg_verbose for (help=a; (help!=NULL) ; help=help->next)
     { fprintf(stderr,"%d ",help->n);}
  if rg_verbose fprintf(stderr, "# %d",n);
  if rg_verbose fprintf(stderr, " (type %d)\n",object);
  if (n<=0)
     return n;
  else { objectdata[n].objectname=new_string(c);
         if (objectdata[n].objectname==NULL)
            return -2;
         lastoccupiedobjectnumber=n;
         objectdata[n].object=object;
         objectdata[n].args=a;
         objectdata[n].targetsort=t;
         objectdata[n].processstatus=unknown;
         objectdata[n].parameters=NULL;
         objectdata[n].processbody=NULL;
         objectdata[n].canterminate=0; }
  return n;
}

static int deleteobject(char *c, arglist *a)
/* Delivers 0 if object does not exists. If object is
   succesfully removed, return 1. */
{ return delete(c,a,objectroot); 
}

void resetvariables(ATerm vars)
{ /* remove the variables in reverse order */
  char *string1=NULL; /* ,*string2=NULL; */
  /* ATfprintf(stderr,"RESET: %t\n",vars); */

  /* if (ATmatch(vars,"ins(<str>,<str>,<term>)",&string1,&string2,&vars)) */
  if (ATgetAFun(vars)==ins3_symbol)
     { string1=ATgetName(ATgetAFun(ATgetArgument(vars,0)));
       vars=ATgetArgument(vars,2);
       resetvariables(vars);
       if (!deleteobject(string1,NULL))
             rg_error("Cannot remove a declared variable",vars);
       return; }
  if (vars!=emv_term) 
       rg_error("Expect a variablelist",vars);
}

int declarevariables(ATerm t, char *emsg)
{ 
  int n,tn;
  char *str1,*str2;
  /* ATfprintf(stderr,"DECLARE: %t\n",t); */
  if (t==NULL) return 1;
  /* for( ; ATmatch(t,"ins(<str>,<str>,<term>)",&str1,&str2,&t) ; ) */
  for( ; ATgetAFun(t)==ins3_symbol ; )
     { str1=ATgetName(ATgetAFun(ATgetArgument(t,0)));
       str2=ATgetName(ATgetAFun(ATgetArgument(t,1)));
       t=ATgetArgument(t,2);

       tn=existsort(str2);
       if (tn==0)
          { sprintf(emsg,"Variable `%s' has unknown sort `%s'",str1,str2);
            return 0; }

       n=insertobject(str1,NULL,tn,variable);
       if (n<=0)
       { switch (n)
         { case 0: sprintf(emsg,"Variable `%s' is already declared as another object",str1);
                    break;
           case -1: sprintf(emsg,"Too many functions and variables to store variable `%s'",str1);
                     break;
           case -2: sprintf(emsg,"No memory to store variable `%s'",str1);
                     break;
           default: rg_error("Unexpected errorcode",NULL);
         }
         return 0;
       }
     }
  if (t!=emv_term)
     rg_error("Declarevariables expects variablelist",t); 
  return 1;  
}

/****      Term to String    *************************************/
 
static void sterm_rec(ATerm t, char *s, int *restlength);

static void loccat(char *s1, char *s2, int *length)
{ if (*length>0)
     { strncat(s1,s2,*length);
       *length-=strlen(s2); }
}

static void stermlist_rec(ATerm t, char *s, int *restlength)
{ /* expects a non empty sequence of terms */
  ATerm head=NULL, tail=NULL;
  if (!ATmatch(t,"ins(<term>,<term>)",&head,&tail)) 
     rg_error("expect non empty termlist",t);
  sterm_rec(head,s,restlength);
  if (tail==emt_term)  return;
  loccat(s,",",restlength);
  stermlist_rec(tail,s,restlength); 
}

static void sterm_rec(ATerm t, char *s, int *restlength)
{ ATerm arg=NULL;
  char *name;
  if (!ATmatch(t,"t(<str>,<term>)",&name,&arg))
     rg_error("Expect Term",t);
  loccat(s,name,restlength);
  if (arg==emt_term) return;
  loccat(s,"(",restlength);
  stermlist_rec(arg,s,restlength);
  loccat(s,")",restlength);
}

static void sterm(ATerm t, char *s)
{ /* prints at most PRINTEDTERMLENGTH characters of the
     ATerm  t in string s */
  int max=PRINTEDTERMLENGTH;
  strcpy(s,"");
  sterm_rec(t,s,&max); }
  
/************ existvar****************************************************/

int existvar(char *str, int *sort)
{ int f;
  f=existsobject(str,NULL);
  if (f>0) 
     { *sort=objectdata[f].targetsort;
       return f;}
  return 0; 
}

/************ exists******************************************************/

int existfuncmapvar(char *str, arglist *sorts, int *sort)
/* Checks whether a function or variable exists with
   name str and arguments sorts. The target sort is in sort */
{ int f;
  f=existsobject(str,sorts);
  if (f==0) return 0;
  if ((objectdata[f].object ==map)||(objectdata[f].object==func)
         ||(objectdata[f].object==variable))
         { *sort=objectdata[f].targetsort;
           return 1; }
  return 0;
  
}


/************ WELLTYPED1**************************************************/


static int welltyped1(ATerm t, int *sort,char *culprit)
{  /* t refers to a closed ATerm  of type Term, 
              and sig is a ATerm  of type Signature */
   char *str;
   ATerm tlist=NULL;
   arglist *sorts=NULL;
   
   /* if (ATmatch(t,"t(<str>,<term>)",&str,&tlist)) */
   if (ATgetAFun(t)==t_symbol)
      { str=ATgetName(ATgetAFun(ATgetArgument(t,0)));
        tlist=ATgetArgument(t,1);
        if (!welltyped2(tlist,&sorts,culprit)) return(0);
        if (existfuncmapvar(str,sorts,sort))
         { release_totalarglist(sorts);
           return(1); }
        release_totalarglist(sorts);
        sprintf(culprit,"%s",str);
        return(0);
      }
   else { rg_error("Welltyped1 receives a ATerm  that is not of type Term",t);}
   return(0);
}

/************ WELLTYPEDOPEN1 ***********************************************/

static int welltypedopen1(ATerm t, ATerm vars1, ATerm vars2, int
*sort, char *emsg)
{ char *culprit1=scratch1;
  char *culprit2=scratch2;
  if (!declarevariables(vars1,emsg))
     return 0;
  if (!declarevariables(vars2,emsg))
     { resetvariables(vars1);
       return 0;}
  if (!welltyped1(t,sort,culprit1))
     { sterm(t,culprit2);
       sprintf(emsg,"Function %s in `%s' has been incorrectly used",culprit1,culprit2);
       resetvariables(vars2);
       resetvariables(vars1);
       return 0; }
  resetvariables(vars2);
  resetvariables(vars1);
  return 1;
}

/************ WELLTYPED2 ************************************************/

int welltyped2(ATerm t, arglist **sorts,char *culprit)
{ /* t refers to a closed ATerm  of type Termlist; In case t is well typed,
     the function yields true and sorts refers to a ATerm  of type stringlist,
     giving the type of t. 

     If welltyped returns TBtrue, then sorts must still be released. */
      
  ATerm tm=NULL, tlist=NULL;
  int sort;
   
  *sorts=NULL;    
  if (t==emt_term) return(1); 
  else if /* (ATmatch(t,"ins(<term>,<term>)",&tm,&tlist)) */
          (ATgetAFun(t)==ins2_symbol)
     { tm=ATgetArgument(t,0);
       tlist=ATgetArgument(t,1);
       if (!welltyped1(tm,&sort,culprit)) return(0);
       if (!welltyped2(tlist, sorts,culprit)) return(0);
       *sorts=new_arglist(sort,*sorts);  /* CHECK OP NULL */
       return(1);
     } 
  else rg_error("Welltyped2 receives a ATerm  that is not of type Termlist",t);
  return(0);
}

/************ WELLTYPEDOPEN2 ****************************************/

int welltypedopen2(ATerm t, ATerm vars1, ATerm vars2, arglist **sort,
char *emsg)
{ char *culprit1=scratch1;
  char *culprit2=scratch2;
  if (!declarevariables(vars1,emsg))
     return 0;
  if (!declarevariables(vars2,emsg))
     { resetvariables(vars2);
       return 0;}
  if (!welltyped2(t,sort,culprit1))
     { sterm(t,culprit2);
       sprintf(emsg,"Function %s in ATerm  %s not well typed",
            culprit1,culprit2);
       resetvariables(vars2);
       resetvariables(vars1);
       return 0; }
  resetvariables(vars2);
  resetvariables(vars1);
  return 1;
}


/************ WELLTYPED
****************************************************/

int welltyped(ATerm t, char *emsg)
{  /* t refers to a closed ATerm  of sort Term, 
              and sig is a ATerm  of sort signature */
  char *culprit1=scratch1; 
  char *culprit2=scratch2; 
  int tmp;
  
  if (welltyped1(t,&tmp,culprit1))
     return 1;
  else { sterm(t,culprit2);
         sprintf(emsg,"Function %s in %s is incorrectly used",
      culprit1,culprit2);
         return 0; }
}

/************ consTFexist
****************************************************/

static int consTFexist(void)
{ int n;
  n=existsobject("T",NULL);
  if (n<=0) return 0;
  if (objectdata[n].object!=func) return 0;
  n=existsobject("F",NULL);
  if (n<=0) return 0;
  if (objectdata[n].object!=func) return 0;
  return 1;
  
}

/************ Boolexist
****************************************************/

static int Boolexist(void)
{ return (existsort("Bool")>0);
}

/************ checksig
****************************************************/

static int checksig(char *emsg)
{ /* uniquetarget, sortsexist, boolsexist */
  char *culprit;

  culprit=scratch1;
  if (!Boolexist())
     { sprintf(emsg,"Sort `Bool' does not exist");
       return(0);}
  if (!consTFexist())
     { sprintf(emsg,"Constructor T or F of sort Bool does not exist");
       return(0);}
  return(1);
}

/************ correcteqs ************************************/

static int correcteqs(ATerm eqs, char *emsg)
{  ATerm vars=NULL, t1=NULL, t2=NULL, tail=NULL;
   int sort1,sort2;
   char *culprit1=scratch1, *culprit2=scratch2,*culprit3=scratch3;
  
   if (ATmatch(eqs,"eme")) return(1);
   if (!ATmatch(eqs,"ins(e(<term>,<term>,<term>),<term>)",&vars,&t1,&t2,&tail)) 
           rg_error("correcteqs expects ATerm  of sort equation",eqs);
   if (!declarevariables(vars,emsg))
      return 0;
   if (!welltyped1(t1,&sort1,culprit3)) 
      { sterm(t1,culprit1);
        sterm(t2,culprit2);
        sprintf(emsg,
          "Function %s in lefthandside of the equation %s=%s is badly used", 
             culprit3,culprit1,culprit2);
        return(0);}
   if (!welltyped1(t2,&sort2,culprit3)) 
      { sterm(t1,culprit1);
        sterm(t2,culprit2);
        sprintf(emsg,
          "Function %s in righthandside of the equation %s=%s is badly used",
             culprit3,culprit1,culprit2);
       return(0);}
   if (sort1!=sort2) 
      { sterm(t1,culprit1);
        sterm(t2,culprit2);
        sprintf(emsg,
          "The sorts of the terms in the equation %s=%s differ",
             culprit1,culprit2);
        return(0);}
   /* if (!nodoubles(t1))  Vraag of dit nog steeds nodig is 
      { sterm(t1,culprit1);
        sterm(t2,culprit2);
        sprintf(emsg,
          "The equation %s=%s is not left linear",
             culprit1,culprit2);

       return(0);} */
       
    resetvariables(vars);
    return(correcteqs(tail,emsg));
}


/************ conc_tl
***************************************************/

ATerm conc_tl_rec(ATerm t, ATerm t1)   
/* returns the termlist obtained by concatenating t and t1 */
{ATerm head=NULL,tail=NULL;
 if (t==emt_term)
   return(t1);
 /* if (ATmatch(t,"ins(<term>,<term>)",&head,&tail))
     return(ATmake("ins(<term>,<term>)",head,conc_tl_rec(tail,t1))); */
 if (ATgetAFun(t)==ins2_symbol)
 { head=ATgetArgument(t,0);
   tail=ATgetArgument(t,1);
   return (ATerm)ATmakeAppl2(ins2_symbol,head,conc_tl_rec(tail,t1));
 }
 rg_error("conc_tl expects ATerm  list in first argument",t);
 return(0);
}

ATerm conc_tl(ATerm t1, ATerm t2)   
/* returns the termlist obtained by concatenating t1 and t2 */
{ 
  ATerm t=NULL;
  
  t=conc_tl_rec(t1,t2);
  return t;
}

/************ join_var **********************************************/

ATerm join_var_rec(ATerm t1, ATerm t2)
{ ATerm s1=NULL, s2=NULL;
  if (t1==emv_term)
      return t2;
  if (ATmatch (t1, "ins(<term>,<term>,<term>)",&s1,&s2,&t1))
     {  if (occursin(s1,t2)==NULL)
        return ATmake("ins(<term>,<term>,<term>)", 
             s1,s2, join_var_rec(t1,t2));
     }
  rg_error ("expect variablelist",t1);
  return NULL;
}

ATerm join_var (ATerm t1, ATerm t2)
{ ATerm t=NULL;
  t=join_var_rec(t1,t2);
  return t;
}

/************ conc_var **********************************************/

ATerm conc_var_rec(ATerm t1, ATerm t2)
{ /* char *s1=NULL, *s2=NULL; */
  ATerm s1=NULL, s2=NULL;
  /* if (ATmatch (t1, "emv")) */
  if (t1==emv_term)
      return t2;
  /* if (ATmatch (t1, "ins(<str>,<str>,<term>)",&s1,&s2,&t1)) */
  if (ATgetAFun(t1)==ins3_symbol)
  { s1=ATgetArgument(t1,0);
    s2=ATgetArgument(t1,1);
    t1=ATgetArgument(t1,2);
    /*  return ATmake("ins(<str>,<str>,<term>)", 
             s1,s2, conc_var_rec(t1,t2)); */
    return (ATerm)ATmakeAppl3(ins3_symbol,s1,s2,conc_var_rec(t1,t2));
  }
  rg_error ("expect variablelist",t1);
  return NULL;
}

ATerm conc_var (ATerm t1, ATerm t2)
{ ATerm t=NULL;
  t=conc_var_rec(t1,t2);
  return t;
}

/************ make_arglist **************************************************/

static int make_arglist(ATerm sorts,arglist **args, 
             char *emsg,char *fsymbol)
{ char *str;
  ATerm tl=NULL;
  arglist *argtl;
  int n;
  
  if (ATmatch(sorts,"ems")||(sorts==emv_term))
     { *args=NULL;
       return 1;
     }
  else if (!ATmatch(sorts,"ins(<str>,<term>)",&str,&tl))
          if
     (!ATmatch(sorts,"ins(<str>,<str>,<term>)",&dummystring,&str,&tl))
             rg_error("make_arglist expects sortlist",sorts); 
  n=existsort(str);
  if (n==0)
     { 
       sprintf(emsg,"Sort `%s' in function/constructor/process/action `%s' is not declared",str,fsymbol);
       return 0;
     }
  if (make_arglist(tl,&argtl,emsg,fsymbol))
     { *args=new_arglist(n,argtl);
       return 1;
     }
  else return 0;
}

/************ storesig
****************************************************/

static int storesig(ATerm sig, char *emsg)
{ char *str1,*str2;
  ATerm sorts=NULL, constr=NULL, funct=NULL, tempterm=NULL, fn=NULL;
  int err=0;
  arglist *args;
  
  if (!ATmatch(sig,"s(<term>,<term>,<term>)",&sorts,&constr,&funct))
     rg_error("storesig expects signature",sig);
/* First store sorts */
  for( ; ATmatch(sorts,"ins(<str>,<term>)",&str1,&tempterm) ;
sorts=tempterm)
     { err=insertsort(str1,0);
       if (err<=0)
          { switch (err) 
             { case 0:  sprintf(emsg,"Sort `%s' appears more than once",str1);
                        break;
               case -1: sprintf(emsg,"Too many sorts while storing sort `%s'",str1);
                        break;
               case -2: sprintf(emsg,"Out of memory while storing sort `%s'",str1);
                        break;
               default: rg_error("Unspecified errorcode",NULL);   
             }
             return 0;
          }
      }
   if (!ATmatch(sorts,"ems"))
      rg_error("Expect a sortlist",sorts);       
          
/* Now store the constructors */
 
  for( ; ATmatch(constr,"ins(<term>,<term>)",&fn,&tempterm) ; constr=tempterm)
     { if (!ATmatch(fn,"f(<str>,<term>,<str>)",&str1,&sorts,&str2))
          rg_error("Expect a function",fn);
       if (!make_arglist(sorts,&args,emsg,str1))
          return 0;
       err=existsort(str2);
       if (err==0)
          { sprintf(emsg,"Constructor `%s' has unknown targetsort `%s'",str1,str2);
            return 0; }
       makeconstructorsort(err);
       err=insertobject(str1,args,err,func);
       if (err<=0)
        { switch (err) 
           { case 0:  sprintf(emsg,"Function `%s' appears twice",str1);
                      break;
             case -1: sprintf(emsg,"Too many functions while storing constructor `%s'",str1);
                      break;
             case -2: sprintf(emsg,"Out of memory while storing constructor `%s'",str1);
                      break;
             default: rg_error("Unspecified errorcode",NULL);   
           }
            return 0;
         } 
      
     }
   if (!ATmatch(constr,"emf"))
      rg_error("Expect a functionlist",constr);
                 
/* Finally store the functions */
  for( ; ATmatch(funct,"ins(<term>,<term>)",&fn,&tempterm) ;
funct=tempterm)
     { if (!ATmatch(fn,"f(<str>,<term>,<str>)",&str1,&sorts,&str2))
          rg_error("Expect a function",fn);
       if (!make_arglist(sorts,&args,emsg,str1))
          return 0;
       err=existsort(str2);
       if (err==0)
          { sprintf(emsg,"Function `%s' has unknown targetsort `%s'",str1,str2);
            return 0; }  
       err=insertobject(str1,args,err,map);
       if (err<=0)
        { switch (err) 
           { case 0:  sprintf(emsg,"Functionname `%s' appears twice",str1);
                      break;
             case -1: sprintf(emsg,"Too many functions while storing function `%s'",str1);
                      break;
             case -2: sprintf(emsg,"Out of memory while storing function `%s'",str1);
                      break;
             default: rg_error("Unspecified errorcode",NULL);   
           }
            return 0;
         } 
      
     }
   if (!ATmatch(constr,"emf"))
      rg_error("Expect a functionlist",funct);
   return 1;
}


/************ ssc ****************************************************/

int storeact(ATerm acts,char *emsg)
{ ATerm sorts=NULL,auxterm=NULL;
  int err=0;
  arglist *args;
  char *name;
    for(auxterm=acts ; 
    (ATmatch(auxterm,"ins(<str>,<term>,<term>)",&name,&sorts,&auxterm)) ;
)
    { if (!make_arglist(sorts,&args,emsg,name))
          return 0;
      err=insertobject(name,args,0,act);
       if (err<=0)
        { switch (err)
           { case 0:  sprintf(emsg,"Action name `%s' is already in use ",name);
                      break;
             case -1: sprintf(emsg,"Too many names while storing action `%s'",name);
                      break;
             case -2: sprintf(emsg,"Out of memory while storing action `%s' ",name);    
                      break;
             default: rg_error("Unspecified errorcode",NULL);
           }
            return 0;
         } 
    } 
  return 1;
} 


/************ void
print_namelist****************************************/
void print_namelist (FILE *f,ATerm t)
{ char *s1=NULL;

  if (ATmatch(t,"ins(<str>,<term>)",&s1,&t))
     {fprintf (f, "%s ", s1);
      print_namelist (f,t);
      return;
     }
  if (!ATmatch (t, "ems"))
     rg_error ("expect stringlist", t);
}
/************ void
print_parlist****************************************/
void print_varlist (FILE *f,ATerm t, char *divider)
{ char *s1= NULL, *s2= NULL;

  if (ATmatch (t, "ins(<str>,<str>,<term>)", &s1,&s2,&t))
     {fprintf (f, "%s%s:%s",
          divider, s1,s2);
      print_varlist (f,t," ");
      return;
     }
  if (t!=emv_term)
     rg_error ("expect variable list", t);
}

/************ print_parlist**************************************/
static void print_parlist (FILE *f,ATerm t, char *divider,
             long *pos)
{ char *s1= NULL, *s2= NULL;

  if (ATmatch (t, "ins(<str>,<str>,<term>)",&s1,&s2,&t))
   { fprintf(f,"%s",divider);
     (*pos)+=strlen(divider);
     if ((*pos)>LINEBREAKLIMIT)
      { fprintf(f,"\n          ");
        *pos=10;
      }
     fprintf (f, "%s:%s",s1,s2);
     (*pos)+=strlen(s1)+strlen(s2)+1;
     print_parlist (f,t,",",pos);
     return;
     }
  if (t!=emv_term)
     rg_error ("expect variable list", t);
}
/*********void print_term**********************************************/
void print_term (FILE *f,ATerm t, long *pos);

static void print_termlist (FILE *f,ATerm tl,char *divider,
                long *pos)
{ ATerm t=NULL;

  if (ATmatch (tl, "ins(<term>,<term>)",&t,&tl))
   { 
     fprintf (f, "%s",divider);
     (*pos)+=strlen(divider);
     print_term (f,t,pos);
     print_termlist (f,tl,",",pos);
     return;
   }
  if (tl!=emt_term)
     rg_error ("expect termlist (1)", tl);
}

/**********void print_term*********************************************/
void print_term (FILE *f,ATerm t, long *pos)
{ char *string1;
  ATerm tl= NULL;
  if (ATmatch (t, "t(<str>,emt)",&string1))
     { if ((*pos)>LINEBREAKLIMIT)
        { fprintf(f,"\n          ");
          *pos=10;
        }
       fprintf (f,"%s", string1);
       (*pos)+=strlen(string1);
       return;
     }
  if (ATmatch (t,"t(<str>,<term>)",&string1,&tl))
     { if ((*pos)>LINEBREAKLIMIT)
        { fprintf(f,"\n          ");
          *pos=10;
        }
       fprintf (f, "%s",string1);
       (*pos)+=strlen(string1);
       print_termlist (f,tl,"(",pos);
       fprintf (f,")");
       return;
     }
  rg_error ("expect ATerm ",t);
}

/********void print LPO**********************************************/
void printLPO (FILE *outfile, ATerm t)
{ ATerm init=NULL, pars=NULL, summands=NULL;
  ATerm sums=NULL, actargs=NULL,procargs=NULL,
        condition=NULL;
  char*s=NULL, *s1=NULL, *s2=NULL;
  int closing_brackets=0;
  long pos=0;

  if (!to_file) return;
  if (!ATmatch (t,"initprocspec(<term>,<term>,<term>)",
          &init, &pars, &summands))
     { rg_error ("expect init procspec", t); }


  fprintf (outfile,"\n\nproc X");
  pos=7;
  if (pars==emv_term)
     fprintf(outfile,"=\n");
  else
   { print_parlist (outfile,pars, "(",&pos);/*assume pars non empty*/
     fprintf (outfile,")=\n");}
  pos=0;
    
  if (ATmatch(summands,"eml"))
   { fprintf(outfile,"delta\n");
     return;
   }
  for (;(ATmatch (summands,
      "ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
         &sums, &s, &actargs, &procargs, &condition,
                     &summands));)
  { for (closing_brackets=0;
        (ATmatch (sums, "ins(<str>,<str>,<term>)", &s1,&s2,&sums)); 
          closing_brackets++)
    { fprintf(outfile,"sum(%s:%s,", s1,s2);
      pos+=6+strlen(s1)+strlen(s2);
    }
    fprintf(outfile,s);
    pos+=strlen(s);
    if (actargs!=emt_term)
     { print_termlist(outfile, actargs, "(",&pos);
       fprintf(outfile,")");
       pos++;
     }

  if (ATmatch (procargs, "i(<term>)",&procargs))
     { fprintf (outfile, ".\n  X");
       pos=3;
       if (procargs!=emt_term)
        { print_termlist (outfile,procargs, "(",&pos);
          fprintf (outfile, ")");
          pos++;
        }
     }

  else if (!ATmatch (procargs, "terminated"))
       rg_error ("expect Ntermlist", procargs);

  fprintf (outfile, "\n    <|");
  pos=7;
  print_term (outfile,condition,&pos);
  fprintf (outfile, "|> delta");

  for ( ;(closing_brackets >0); closing_brackets--)
      { fprintf (outfile, ")");}

  if (!ATmatch (summands, "eml"))
      fprintf (outfile, "+\n\n");
 }
 fprintf(outfile,"\n\n");

 if (to_file) fprintf (outfile, "\n\ninit X");
 pos=7;
 if (init!=emt_term)
  { print_termlist (outfile,init, "(",&pos); /*assume init non empty*/
    fprintf(outfile,")");
  }
 fprintf(outfile,"\n");
}




/************ ssc ****************************************************/



int storeprocs(ATerm procs,char *emsg)
{ ATerm sorts=NULL,auxterm=NULL,body=NULL;
  int n=0;
  arglist *args=NULL;
  char *name=NULL;
    for(auxterm=procs ; 

(ATmatch(auxterm,"ins(proc(<str>,<term>,<term>),<term>)",&name,&sorts,&body,&auxterm)) ; )
    { if (!make_arglist(sorts,&args,emsg,name))
          return 0;
      n=insertobject(name,args,0,proc);
       if (n<=0)
        { switch (n)
           { case 0:  sprintf(emsg,"Process name `%s' is already in use",name);
                      break;
             case -1: sprintf(emsg,"Too many names while storing process name `%s'",name);
                      break;
             case -2: sprintf(emsg,"Out of memory while storing process name `%s' ",name);    
                      break;
             default: rg_error("Unspecified errorcode",NULL);
           }
            return 0;
         } 
        objectdata[n].processbody=body;
        objectdata[n].parameters=sorts;
    } 
  return 1;
}

/************ welltypedprocs ******************************************/

arglist *determine_process_status_rec(int n,processstatustype status,
              char *err_mes,int *err);

processstatustype determine_process_statusterm(ATerm body, 
                processstatustype status,char *err_mes)
/* determine whether a process is a mCRL process, with hide, rename,
   encap and parallel processes around process names.
   If a process contains, only alt, seq, names, conds and sums,
   delta and tau then the process is a pCRL.
   otherwise, i.e. if the process contains lmer, com, bound and
   at, or have parallel, encap, hide and rename operators in
   combination with other operators this system delivers unknown and
   an appropriate message is left in emsg */

{ processstatustype s1=unknown, s2=unknown;
  ATerm t1=NULL, t2=NULL, t=NULL;
  char *str1=NULL,*str2=NULL;
  int n;
  int err=0;

  if (ATmatch(body,"alt(<term>,<term>)",&t1,&t2))
   { if (status==mCRL) 
        return pCRL;
     s1=determine_process_statusterm(t1,pCRL,err_mes);
     if (s1==error) return error;
     s2=determine_process_statusterm(t2,pCRL,err_mes);
     if (s1==error) return error;
     if ((s1==mCRL)||(s2==mCRL))
      { sprintf(err_mes,"(1) Mixing pCRL with mCRL operators");
        return error; }
     return pCRL;
   }
  if (ATmatch(body,"seq(<term>,<term>)",&t1,&t2))
   { if (status==mCRL) 
        return pCRL;
     s1=determine_process_statusterm(t1,pCRL,err_mes);
     if (s1==error) return error;
     s2=determine_process_statusterm(t2,pCRL,err_mes);
     if (s2==error) return error;
     if ((s1==mCRL)||(s2==mCRL))
      { sprintf(err_mes,"(2) Mixing pCRL with mCRL operators");
        return error; }
     return pCRL;
   }
  if (ATmatch(body,"par(<term>,<term>)",&t1,&t2))
   { if (status==pCRL)
      { sprintf(err_mes,"parallel operator in the scope of pCRL operators");
        return error; }
     s1=determine_process_statusterm(t1,mCRL,err_mes);
     if (s1==error) return error;
     s2=determine_process_statusterm(t2,mCRL,err_mes);
     if (s2==error) return error;
     if ((s1==pCRL)||(s2==pCRL))
       { sprintf(err_mes,"(4) Mixing pCRL with mCRL operators");
         return error; }
     return mCRL;
   }
  if (ATmatch(body,"lmer(<term>,<term>)",&t1,&t2))
   { sprintf(err_mes,"Cannot linearize as specification contains a leftmerge");
     return error; }
  if (ATmatch(body,"cond(<term>,<term>,<term>)",&t1,&t,&t2))
   { if (status==mCRL) 
        return pCRL;
     s1=determine_process_statusterm(t1,pCRL,err_mes);
     if (s1==error) return error;
     s2=determine_process_statusterm(t2,pCRL,err_mes);
     if (s2==error) return error;
     if ((s1==mCRL)||(s2==mCRL))
      { sprintf(err_mes,"(6) Mixing pCRL with mCRL operators");
        return error; }
     return pCRL;
   }
  if (ATmatch(body,"sum(<str>,<str>,<term>)",&str1,&str2,&t1))
   { if (status==mCRL) 
        return pCRL;
     s1=determine_process_statusterm(t1,pCRL,err_mes);
     if (s1==error) return error;
     if (s1==mCRL)
      { sprintf(err_mes,"(7) Mixing pCRL with mCRL operators");
        return error; }
     return pCRL;
   }
  if (ATmatch(body,"com(<term>,<term>)",&t1,&t2))
   { sprintf(err_mes,"Cannot linearize a specification containing a communication merge");
     return error; }
  if (ATmatch(body,"bound(<term>,<term>)",&t1,&t2))
   { sprintf(err_mes,"Cannot linearize a specification containing the bounded initialization operator");
     return error; }
  if (ATmatch(body,"at(<term>,<term>)",&t1,&t2))
   { sprintf(err_mes,"Cannot linearize a specification containing the at operator");
     return error; }
  if (ATmatch(body,"name(<str>,<int>,<term>)",&str1,&n,&t2))
   { if (objectdata[n].object==act) 
           return pCRL;
     if (objectdata[n].object==proc) 
      { determine_process_status_rec(n,status,err_mes,&err);
          if (err) return error;
        return status; }
     rg_error("Strange object on my path",NULL);
   }
  if ((ATmatch(body,"delta"))||(ATmatch(body,"tau")))
     return pCRL;
  if ((ATmatch(body,"hide(<term>,<term>)",&t,&t1))||
      (ATmatch(body,"rename(<term>,<term>)",&t,&t1))||
      (ATmatch(body,"encap(<term>,<term>)",&t,&t1)))
   { if (status==pCRL) 
      { sprintf(err_mes,"renaming operators in the scope of pCRL operators");
        return error; }
     s1=determine_process_statusterm(t1,mCRL,err_mes);
     if (s1==error) return error;
     if (s1==pCRL)
      { sprintf(err_mes,"Mixing pCRL with mCRL operators");
        return error; }
     return mCRL;
   }
  rg_error("Unmatching process ATerm ",body);
  return error;
} 

arglist *pcrlprocesses=NULL;

arglist *determine_process_status_rec(int n,processstatustype status,
         char *err_mes, int *err)
{ processstatustype s;
  s=objectdata[n].processstatus;
  if debug ATfprintf(stderr,"determine_process_status %t\n",
            objectdata[n].processbody);
  if (s==unknown) 
   { objectdata[n].processstatus=status;
     if (status==pCRL)
        { pcrlprocesses=new_arglist(n,pcrlprocesses); 
          if (determine_process_statusterm(objectdata[n].processbody,
                          pCRL,err_mes)==error)
           { *err=1;
             return NULL; }
          return pcrlprocesses;
        }
     /* status==mCRL */

s=determine_process_statusterm(objectdata[n].processbody,mCRL,err_mes);
     if (s==error)
      { *err=1;
        return NULL; }
     if (s!=status)
        { /* s==pCRL and status==mCRL */
          objectdata[n].processstatus=s;
          pcrlprocesses=new_arglist(n,pcrlprocesses);
          s=determine_process_statusterm(objectdata[n].processbody,
                           pCRL,err_mes);     
          if (s==error)
           { *err=1;
             return NULL; }
          return pcrlprocesses;
        }
     return pcrlprocesses;
   }
  if (s==mCRL)
   { if (status==pCRL)
      { objectdata[n].processstatus=status;
        pcrlprocesses=new_arglist(n,pcrlprocesses);
        if (determine_process_statusterm(objectdata[n].processbody,
                           pCRL,err_mes)==error)   
         { *err=1;
           return NULL; }
      }
     return pcrlprocesses;
   }
  return pcrlprocesses;
}

arglist *determine_process_status(int n,processstatustype status,
          char *err_mes, int *err)
{ pcrlprocesses=NULL;
  return determine_process_status_rec(n,status,err_mes,err);}


/************ welltypedprocs ******************************************/

static ATerm welltypedbody(ATerm body,char *name, char *emsg)
/* checks whether the body is welltyped, and 
   replaces every "name(%s,%t)" by "name(%s,%d,%t)" where
   the new second argument is the sequence number of the ATerm .
   returns NULL and an errormessage (emsg) in case of a problem
   otherwise returns a pointer to the new ATerm .*/
{ 
  char *culprit1=scratch1, *culprit2=scratch2,
       *s1=NULL, *s2=NULL, *s3=NULL, *s4=NULL;
  ATerm t1=NULL, t2=NULL, t=NULL, t3=NULL, 
        walker=NULL, walker1=NULL;
  int n=0,oldtargetsort=0, i=0;
  int found=0, stop=0;
  arglist *args=NULL;
  /* if (ATmatch(body,"alt(<term>,<term>)",&t1,&t2)) */
  if (ATgetAFun(body)==alt_symbol)
   { t1=ATgetArgument(body,0);
     t2=ATgetArgument(body,1);
     t1=welltypedbody(t1,name,emsg);
       if (t1==NULL) 
        t3=NULL;
       else 
        { t2=welltypedbody(t2,name,emsg);
          if (t2==NULL) 
           t3=NULL;
          else t3=ATmake("alt(<term>,<term>)",t1,t2); 
        }
     }
  else
  /* if (ATmatch(body,"seq(<term>,<term>)",&t1,&t2)) */
    if (ATgetAFun(body)==seq_symbol)
     { t1=ATgetArgument(body,0);
       t2=ATgetArgument(body,1);
       t1=welltypedbody(t1,name,emsg);
       if (t1==NULL) 
          t3=NULL;
       else 
        { t2=welltypedbody(t2,name,emsg);
          if (t2==NULL) 
             t3=NULL; 
          else t3=ATmake("seq(<term>,<term>)",t1,t2); 
        }
     }
  else
  /* if (ATmatch(body,"par(<term>,<term>)",&t1,&t2)) */
    if (ATgetAFun(body)==par_symbol)
     { t1=ATgetArgument(body,0);
       t2=ATgetArgument(body,1);

       t1=welltypedbody(t1,name,emsg);
       if (t1==NULL) 
          t3=NULL;
       else 
        { t2=welltypedbody(t2,name,emsg);
          if (t2==NULL) 
             t3=NULL; 
          else t3=ATmake("par(<term>,<term>)",t1,t2); 
        }
     }
  else
  /* if (ATmatch(body,"lmer(<term>,<term>)",&t1,&t2)) */
    if (ATgetAFun(body)==lmer_symbol)
     { t1=ATgetArgument(body,0);
       t2=ATgetArgument(body,1);

       t1=welltypedbody(t1,name,emsg);
       if (t1==NULL) 
          t3=NULL;
       else 
        { t2=welltypedbody(t2,name,emsg);
          if (t2==NULL) 
             t3=NULL; 
          else t3=ATmake("lmer(<term>,<term>)",t1,t2); 
        }
     }
  else
  /* if (ATmatch(body,"cond(<term>,<term>,<term>)",&t1,&t,&t2)) */
     if (ATgetAFun(body)==cond_symbol)
     { t1=ATgetArgument(body,0);
       t=ATgetArgument(body,1);
       t2=ATgetArgument(body,2);

     if (!welltyped1(t,&n,culprit1))
      { sterm(t,culprit2);
          sprintf(emsg,"The function %s in the condition %s in the body of process %s is incorrectly used",culprit1,culprit2,name);
          t3=NULL; }
     else if (n!=existsort("Bool"))
      { sterm(t,culprit1);
        sprintf(emsg,"The condition %s in the body of process %s has type %s instead of Bool", culprit1,name,sortdata[n].sortname->s);
        t3=NULL; }
     else 
      { t1=welltypedbody(t1,name,emsg);
        if (t1==NULL) 
           t3=NULL;
        else 
         { t2=welltypedbody(t2,name,emsg);
           if (t2==NULL) 
              t3=NULL; 
           else t3=ATmake("cond(<term>,<term>,<term>)",t1,t,t2);
         }
      }
   }
  else
  /* if (ATmatch(body,"sum(<str>,<str>,<term>)",&s1,&s2,&t1)) */
    if (ATgetAFun(body)==sum_symbol)
     { s1=ATgetName(ATgetSymbol(ATgetArgument(body,0)));
       s2=ATgetName(ATgetSymbol(ATgetArgument(body,1)));
       t1=ATgetArgument(body,2);

       oldtargetsort=0;
       stop=0;
       n=existsobject(s1,NULL);
       if (n>0)
        { 
          if (objectdata[n].object!=variable)
           { sprintf(emsg,"Variable %s is already declared as another object",s1);
               stop=1;
               t3=NULL; }
          else
           { oldtargetsort=objectdata[n].targetsort;
             objectdata[n].targetsort=existsort(s2);
             if (objectdata[n].targetsort<=0)
              { sprintf(emsg,"Sort %s has not been declared",s2);
                stop=1;
                t3=NULL;
              }
           } 
        }
       else
        { if (declarevariables(ATmake("ins(<str>,<str>,emv)",s1,s2),emsg)==0)
          {  
            stop=1;
            t3=NULL; 
          }
        }
       if (!stop)
        { 
          t1=welltypedbody(t1,name,emsg);
          if (t1==NULL) 
             t3=NULL;
          else 
           { if (oldtargetsort==0)
                  resetvariables(ATmake("ins(<str>,<str>,emv)",s1,s2));
             else objectdata[n].targetsort=oldtargetsort;
             t3=ATmake("sum(<str>,<str>,<term>)",s1,s2,t1);
           }
        }    
     }
  else
  /* if (ATmatch(body,"com(<term>,<term>)",&t1,&t2)) */
  if (ATgetAFun(body)==com_symbol)
     { t1=ATgetArgument(body,0);
       t2=ATgetArgument(body,1);

       t1=welltypedbody(t1,name,emsg);
       if (t1==NULL) 
          t3=NULL;
       else 
        { t2=welltypedbody(t2,name,emsg);
          if (t2==NULL) 
             t3=NULL;
          t3=ATmake("com(<term>,<term>)",t1,t2); 
        }
     }
  else
  /* if (ATmatch(body,"bound(<term>,<term>)",&t1,&t2)) */
    if (ATgetAFun(body)==bound_symbol)
     { t1=ATgetArgument(body,0);
       t2=ATgetArgument(body,1);

      if (existsort("Time")<=0)
          { sprintf(emsg,"Operator << is used, but Time not declared");
            t3=NULL; 
          }
       else
        { t1=welltypedbody(t1,name,emsg);
          if (t1==NULL)
             t3=NULL;
          else 
           { t2=welltypedbody(t2,name,emsg);
             if (t2==NULL) 
                t3=NULL;
             else t3=ATmake("bound(<term>,<term>)",t1,t2); 
           }
        }
     }
  else
  /* if (ATmatch(body,"at(<term>,<term>)",&t1,&t)) */
  if (ATgetAFun(body)==at_symbol)
     { t1=ATgetArgument(body,0);
       t=ATgetArgument(body,1);

     if (!welltyped1(t,&n,culprit1))
      { sterm(t,culprit2);
          sprintf(emsg,"The function %s in the time expression %s in the body of process %s is incorrectly used",culprit1,culprit2,name);
          t3=NULL; 
      }
     else
     if (n!=existsort("Time"))
      { sterm(t,culprit1);
        sprintf(emsg,"The time expression %s in the body of process %s has type %s instead of Time", culprit1,name,sortdata[n].sortname->s);
        t3=NULL;
      }
     else
      {  t1=welltypedbody(t1,name,emsg);
         if (t1==NULL) 
            t3=NULL;
         else t3=ATmake("at(<term>,<term>)",t1,t);
      }
   }
  else
  /* if (ATmatch(body,"name(<str>,<term>)",&s1,&t1)) */
    if (ATgetAFun(body)==name_symbol)
     { s1=ATgetName(ATgetAFun(ATgetArgument(body,0)));
       t1=ATgetArgument(body,1);

     if (!welltyped2(t1,&args,culprit1))
      { sterm(ATmake("t(<str>,<term>)",s1,t1),culprit2);
           sprintf(emsg,"The function %s in action or process %s in %s is incorrectly used",
                culprit1,culprit2,name);
        t3=NULL; }
     else 
      { n=existsobject(s1,args);
        release_totalarglist(args);
        if (n<=0)
          { sterm(ATmake("t(<str>,<term>)",s1,t1),culprit1);
            sprintf(emsg,"Action or process %s in %s has not been declared",culprit1,name);
            t3=NULL; }
        else
         { if
((objectdata[n].object==proc)||(objectdata[n].object==act))
            t3=ATmake("name(<str>,<int>,<term>)",s1,n,t1);
           else 
            { sprintf(emsg,"String %s occurring in %s is neither a process nor an action",s1,name);
              t3=NULL; }}
      }
   }
  else
  if (body==delta_term)
   { t3=body; }
  else
  if (body==tau_term)
   { t3=body; }
  else
  /* if (ATmatch(body,"hide(<term>,<term>)",&t1,&t2)) */
    if (ATgetAFun(body)==hide_symbol)
     { t1=ATgetArgument(body,0);
       t2=ATgetArgument(body,1);

      found=1;
      for(walker=t1; (found&&
          /*   (ATmatch(walker,"ins(<str>,<term>)",&s1,&walker))) ;) */
            (ATgetAFun(walker)==ins2_symbol)) ;)
         { s1=ATgetName(ATgetAFun(ATgetArgument(walker,0)));
           walker=ATgetArgument(walker,1);
           found=0;
           for(i=1 ; ((i<=lastoccupiedobjectnumber)&&(found==0)) ; i++)
            { if ((objectdata[i].object==act)&&
                      (strequal(s1,objectdata[i].objectname->s)))
	       { found=1; } 
            }
           if (!found)
	     { sprintf(emsg,"Action %s in hide set has not been declared",s1);
	       t3=0; }
	 }
      if (found)
       { t2=welltypedbody(t2,name,emsg);
         if (t2==NULL) 
            t3=NULL;
         else t3=ATmake("hide(<term>,<term>)",t1,t2);
       }
    }
  else
  /* if (ATmatch(body,"rename(<term>,<term>)",&t1,&t2)) */
    if (ATgetAFun(body)==rename_symbol)
     { t1=ATgetArgument(body,0);
       t2=ATgetArgument(body,1);

       stop=0;
       for(walker=t1; 
        /* (!stop&&(ATmatch(walker,"ins(<str>,<str>,<term>)",
                         &s1,&s2,&walker))) ;) */
           (!stop&&(ATgetAFun(walker)==ins3_symbol)) ; )
          { s1=ATgetName(ATgetAFun(ATgetArgument(walker,0)));
            s2=ATgetName(ATgetAFun(ATgetArgument(walker,1)));
            walker=ATgetArgument(walker,2);
            for(walker1=walker ; 
                /* (!stop&&(ATmatch(walker1,"ins(<str>,<str>,<term>)",
                     &s3,&s4,&walker1))) ; ) */
               (!stop&&(ATgetAFun(walker1)==ins3_symbol)) ; )
            { s3=ATgetName(ATgetAFun(ATgetArgument(walker1,0)));
              s4=ATgetName(ATgetAFun(ATgetArgument(walker1,1)));
              walker1=ATgetArgument(walker1,2);

              if (strequal(s1,s3))
                { sprintf(emsg,"Action %s occurs twice in the left hand side of a renaming",s1);
                  stop=1;
                  t3=0; }
             }
            if (!stop)
             { found=0;
               for(i=1 ; (!stop&& (i<=lastoccupiedobjectnumber)) ; i++)
                { if ((objectdata[i].object==act)&&
                          (strequal(s1,objectdata[i].objectname->s)))
	           { found=1;
                     n=existsobject(s2,objectdata[i].args);
                     if (n<=0)
                      { sprintf(emsg,"Sorts of action %s and %s in renaming do not match",s1,s2);
                        stop=1;
                        t3=0; }
                     else
                     if (objectdata[n].object!=act)
                      { sprintf(emsg,"Action %s renames to %s but %s is not necessarily an action for all argument sorts of %s",s1,s2,s2,s1);
                        stop=1;
                        t3=NULL; }
                   }
                }
               if (!found)
	         { sprintf(emsg,"Action %s in renaming set has not been declared",s1);
                   stop=1;
	           t3=NULL; }
             }
	  }
       if (!stop)
         { t2=welltypedbody(t2,name,emsg);
           if (t2==NULL) 
              t3=NULL;
           else 
             { t3=ATmake("rename(<term>,<term>)",t1,t2);
             }
         }
     }
  else
  /* if (ATmatch(body,"encap(<term>,<term>)",&t1,&t2)) */
    if (ATgetAFun(body)==encap_symbol)
     { t1=ATgetArgument(body,0);
       t2=ATgetArgument(body,1);

       found=1;
       for(walker=t1; 
         /* (found&&(ATmatch(walker,"ins(<str>,<term>)",&s1,&walker))) ;) */
          (found&&(ATgetAFun(walker)==ins2_symbol)) ; )
          { s1=ATgetName(ATgetAFun(ATgetArgument(walker,0)));
            walker=ATgetArgument(walker,1);
            found=0;
            for(i=1 ; ((i<=lastoccupiedobjectnumber)&&(found==0)) ; i++)
            { if ((objectdata[i].object==act)&&
                       (strequal(s1,objectdata[i].objectname->s)))
	        { found=1; } 
             }
            if (!found)
	     { sprintf(emsg,"Action %s in encap set has not been declared",s1);
               t3=NULL;
             }
	  }
       if (found)
        { t2=welltypedbody(t2,name,emsg);
          if (t2==NULL) 
             t3=NULL;
          else t3=ATmake("encap(<term>,<term>)",t1,t2);
        }
     }
  else rg_error("Process does not match format",NULL);
  
  return t3;
}



/************ welltypedprocs
*********************************************/

int welltypedprocs(ATerm procs,char *emsg)
  /* check that processes are well typed and and add process
       or action number in "name(%s,%t)" as second argument */
{
  ATerm auxterm=NULL, body=NULL, sorts=NULL;
  char *name=NULL;
  arglist *args=NULL;
  int n=0;
  for(auxterm=procs ; 

(ATmatch(auxterm,"ins(proc(<str>,<term>,<term>),<term>)",&name,&sorts,&body,&auxterm)) ; )
    { if (!make_arglist(sorts,&args,emsg,name))
          return 0;
      n=existsobject(name,args);
      if (n<=0) rg_error("Existing name has gone",NULL);
      release_totalarglist(args);
      if (declarevariables(sorts,emsg)==0)
         return 0;
      objectdata[n].processbody=
             welltypedbody(objectdata[n].processbody,name,emsg);
      if (objectdata[n].processbody==NULL) return 0;
      resetvariables(sorts);
      objectdata[n].processstatus=unknown;
    }
  /* fprintf(stdout,"Processes are ok!\n"); */
  return 1;
}


/************ check whether communication function is associative ********/
int check_communications(specificationbasictype *spec,char *err_mes)
{ /* We check whether the communications are properly declared */
  ATerm walker1=NULL, walker2=NULL, walker3=NULL, walker4=NULL;
  ATerm n1=NULL, n2=NULL, n3=NULL, n4=NULL, n5=NULL, n6=NULL;
  ATerm n7=NULL, n8=NULL, n9=NULL, n10=NULL, n11=NULL, n12=NULL;
  int i=0,n=0;
  int n1detected=0,n2detected=0;
  int found;

  for(walker1=spec->comms; 
       /* (ATmatch(walker1,"ins(<str>,<str>,<str>,<term>)",
                   &n1,&n2,&n3,&walker1)) ; ) */
       ATgetAFun(walker1)==ins4_symbol ; )
    { n1=ATgetArgument(walker1,0);
      n2=ATgetArgument(walker1,1);
      n3=ATgetArgument(walker1,2);
      walker1=ATgetArgument(walker1,3);
      for(walker2=walker1;
       /* (ATmatch(walker2,"ins(<str>,<str>,<str>,<term>)",
                &n4,&n5,&n6,&walker2)) ;) */
          ATgetAFun(walker2)==ins4_symbol ; )
    { n4=ATgetArgument(walker2,0);
      n5=ATgetArgument(walker2,1);
      n6=ATgetArgument(walker2,2);
      walker2=ATgetArgument(walker2,3);

      if (((n1==n4)&&(n2==n5))||
              ((n2==n4)&&(n1==n5)))
       { sprintf(err_mes,
             "Communications %s|%s=%s and %s|%s=%s are declared twice",
             ATgetName(ATgetAFun(n1)),ATgetName(ATgetAFun(n2)),
             ATgetName(ATgetAFun(n3)),ATgetName(ATgetAFun(n4)),
             ATgetName(ATgetAFun(n5)),ATgetName(ATgetAFun(n6))); 
         return 0; }}
      n1detected=0;
      n2detected=0;
      for (i=1 ; i<=lastoccupiedobjectnumber ; i++)
        { if (objectdata[i].object==act)
           { if (strequal(ATgetName(ATgetAFun(n1)),
                            objectdata[i].objectname->s))
             { n1detected=1; 
               n=existsobject(ATgetName(ATgetAFun(n2)),objectdata[i].args);
               if (n<=0)
                 { sprintf(err_mes,"Communicating actions %s and %s are not declared with similar sorts",ATgetName(ATgetAFun(n1)),ATgetName(ATgetAFun(n2)));
                   return 0; }
               else if (objectdata[i].object!=act)
                     { sprintf(err_mes,"String %s occurs in communication but is not an action",ATgetName(ATgetAFun(n2)));
                   return 0; }
               n=existsobject(ATgetName(ATgetAFun(n3)),objectdata[i].args);
               if (n<=0)
                 { sprintf(err_mes,"Action %s communicates to %s but is not declared with similar sorts",ATgetName(ATgetAFun(n1)),ATgetName(ATgetAFun(n3)));
                   return 0; }
               else if (objectdata[i].object!=act)
                     { sprintf(err_mes,"String %s occurs in communication but is not an action",ATgetName(ATgetAFun(n3)));
                   return 0; }
           }
           { if (strequal(ATgetName(ATgetAFun(n2)),objectdata[i].objectname->s))
             { n2detected=1;
               n=existsobject(ATgetName(ATgetAFun(n1)),objectdata[i].args);
               if (n<=0)
                 { sprintf(err_mes,"Communicating actions %s and %s are not declared with similar sorts",ATgetName(ATgetAFun(n1)),ATgetName(ATgetAFun(n2)));
                   return 0; }
               else if (objectdata[i].object!=act)
                     { sprintf(err_mes,"String %s occurs in communication but is not an action",ATgetName(ATgetAFun(n1)));
                   return 0; }
               n=existsobject(ATgetName(ATgetAFun(n3)),objectdata[i].args);
               if (n<=0)
                 { sprintf(err_mes,"Action %s communicates to %s but is not declared with similar sorts",ATgetName(ATgetAFun(n2)),ATgetName(ATgetAFun(n3)));
                   return 0; }
               else if (objectdata[i].object!=act)
                     { sprintf(err_mes,"String %s occurs in communication but is not an action",ATgetName(ATgetAFun(n3)));
                   return 0; }
             }
           }
           }
        }
     if (n1detected==0)
      { sprintf(err_mes,"Action %s has not been declared",ATgetName(ATgetAFun(n1)));
        return 0; }
     if (n2detected==0)
      { sprintf(err_mes,"Action %s has not been declared",ATgetName(ATgetAFun(n2)));
        return 0; }

  /* check for all comms that
     if n1|n2=n4, n4|n3=n5, then there is n6 s.t. n2|n3=n6, n1|n6=n5,
     implying communication associativity */
  for(walker2=spec->comms; 
      /* (ATmatch(walker2,"ins(<str>,<str>,<str>,<term>)",
                    &n4,&n5,&n6,&walker2)) ; ) */
          ATgetAFun(walker2)==ins4_symbol ; )
    { n4=ATgetArgument(walker2,0);
      n5=ATgetArgument(walker2,1);
      n6=ATgetArgument(walker2,2);
      walker2=ATgetArgument(walker2,3);

      if ((n3==n4)||(n3==n5))
       { found=0;
         for (walker3=spec->comms ;
              /* (ATmatch(walker3,"ins(<str>,<str>,<str>,<term>)",
                       &n7,&n8,&n9,&walker3)) ; ) */
          ATgetAFun(walker3)==ins4_symbol ; )
          { n7=ATgetArgument(walker3,0);
            n8=ATgetArgument(walker3,1);
            n9=ATgetArgument(walker3,2);
            walker3=ATgetArgument(walker3,3);

          if ((((n7==n1)||((n7==n2)))&&
                 (((n3==n4)&&(n8==n5))||
                  ((n3==n5)&&(n8==n4))))||
              (((n8==n1)||(n8==n2))&&
                 (((n3==n4)&&(n7==n5))||
                  ((n3==n5)&&(n7==n4)))))
            { for (walker4=spec->comms ;
               /* (ATmatch(walker4,"ins(<str>,<str>,<str>,<term>)",
                           &n10,&n11,&n12,&walker4)) ; ) */
               ATgetAFun(walker4)==ins4_symbol ; )
               { n10=ATgetArgument(walker4,0);
                 n11=ATgetArgument(walker4,1);
                 n12=ATgetArgument(walker4,2);
                 walker4=ATgetArgument(walker4,3);

                 if ((n6==n12)&&
                   ((((n8!=n1))&&((n7!=n1)))||
                    (((n10==n9)&&(n11==n2))||
                     ((n10==n2)&&(n11==n9))))&&
                   ((((n8!=n2))&&((n7!=n2)))||
                    (((n10==n9)&&(n11==n1))||
                     ((n10==n1)&&(n11==n9)))))
                 found=1;
            }  } }
         if (found==0)
            { if ((n3==n4))
                  sprintf(err_mes,"The communication %s|%s|%s is not associative",
   ATgetName(ATgetAFun(n1)),ATgetName(ATgetAFun(n2)),ATgetName(ATgetAFun(n5)));
              else sprintf(err_mes,"The communication %s|%s|%s is not associative",
  ATgetName(ATgetAFun(n1)),ATgetName(ATgetAFun(n2)),ATgetName(ATgetAFun(n4)));
              return 0; }
       } 
    }
   }
  return 1;
}

/************ check_time_operators *************************************/

int check_time_operators(char *emsg)
{ int n=0,m=0,b=0;
  arglist *a=NULL;
  if (time_operators_used==0) return 1;
  n=existsort("Time");
  if (n<=0)
   { sprintf(emsg,"Operators @ and/or << are used, but sort `Time' is not declared");
     return 0; }
  m=existsobject("time0",a);
  if (m<=0)
   { sprintf(emsg,"Operators @ and/or << are used, but constant `time0' is not declared");
     return 0; }
  if ((objectdata[m].object!=func)&&(objectdata[m].object!=map))
   { sprintf(emsg,"Operators @ and/or << are used, but object `time0' is not a func or map");
     return 0; }
  if (objectdata[m].targetsort!=n)
   { sprintf(emsg,"Operators @ and/or << are used, but constant `time0' is not of sort `Time'");
     return 0; }
  a=new_arglist(n,new_arglist(n,NULL));
  b=existsort("Bool");
  m=existsobject("le",a);
  if (m<=0)
   { sprintf(emsg,"Operators @ and/or << are used, but function `le' is not declared");
     return 0; }
  if (objectdata[m].object!=map)
   { sprintf(emsg,"Operators @ and/or << are used, but object `le' is not a map");
     return 0; }
  if (objectdata[m].targetsort!=b)
   { sprintf(emsg,"Operators @ and/or << are used, but function `le' does not have targetsort `Bool'");
     return 0; }
  release_totalarglist(a);
  return 1;
}

/************ check_empty_constructor_sorts
******************************/

int check_empty_constructor_sorts(char *err_mes)
{ /* First change the fields of constructor sorts that are not
     empty from 1 to 2, until no changes are being made. Then change
     the value 2 back to 1, and check in the meantime whether a 
     remaining value 1 exists. If so, this is an empty sort */
  arglist *a=NULL;
  int stable=0, emptyargs=0;
  int i=0,n=0;

  for(stable=0 ; stable==0 ; )
   { stable=1;
     for(i=1 ; i<=lastoccupiedobjectnumber; i++)
      { if (objectdata[i].object==func)
         { emptyargs=0;
           for(a=objectdata[i].args ; ((a!=NULL)&&(emptyargs==0)) ;
a=a->next)
            { if (sortdata[a->n].constructor==1)
                 emptyargs=1; 
            }
           if (emptyargs==0)
            { n=objectdata[i].targetsort;
              if (sortdata[n].constructor==1)
               { sortdata[n].constructor=2;
                 stable=0; }
            }

         }
      }
   }
  for(i=1; i<=lastoccupiedsortnumber; i++)
    { if (sortdata[i].constructor==1)
       { sprintf(err_mes,"Sort `%s' is an empty constructor sort",
                    sortdata[i].sortname->s);
         return 0; }
      if (sortdata[i].constructor==2)
         sortdata[i].constructor=1;
    }
  return 1;
}


/************ sscproc ****************************************************/

int sscproc(specificationbasictype *spec, char *emsg)
{ /* Store actions and processes in the dataobject array,
     check whether their bodies are SSC, store the initial process
     under the name init, check whether it is SCC and deliver the index
     of the initial process, if everything is ok, otherwise return -1 if
    init is not defined, and return 0 if an error occurred */


  int n=-1;

  if (!welltypedprocs(spec->procs,emsg)) n=0;

  else 
   {  
     if (spec->init!=NULL)
     { /* "init" is a name that cannot be used in the input, so
             using it as the initial process is safe */
       n=insertobject("init",NULL,0,proc);
       spec->init=welltypedbody(spec->init,"initial process",emsg);
       if (spec->init==NULL) n=0;
       else
        { objectdata[n].processbody=spec->init;
          objectdata[n].parameters=emv_term;
          objectdata[n].processstatus=unknown;
          if (objectdata[n].processstatus==error) n=0;
     }  }
     else n=-1;
   }
  spec->init=NULL;
  spec->procs=NULL;
  
  if (n==0) return 0;
  if (check_communications(spec,emsg)==0) return 0;
  if (check_empty_constructor_sorts(emsg)==0) return 0;
  if (check_time_operators(emsg)==0) return 0;
  return n;
}

/************ ssc ****************************************************/

int ssc(specificationbasictype *spec, char *errormessage)
{   /* uniquetarget
       sortsexist
       correcteqs (done)
       consTFexist  */
  ATerm sig=NULL, eqs=NULL;

  
 /*  if (!ATmatch(d,"d(<term>,<term>)",&sig,&eqs)) 
         rg_error("ssc expects ATerm  of type datatype",d); */
  sig=ATmake("s(<term>,<term>,<term>)",
        spec->sorts,spec->funcs,spec->maps);
  eqs=spec->eqns;
  if (!storesig(sig,errormessage)) return(0);
  if (!storeact(spec->acts,errormessage)) return(0);
  if (!storeprocs(spec->procs,errormessage)) return(0);

  if (!checksig(errormessage)) return(0);
  if (!correcteqs(eqs,errormessage)) return(0);
  return(1);
}

/************ correctopenterm
********************************************/ 
int correctopenterm(ATerm t, char *emsg)
{
  ATerm tm=NULL, vars=NULL;
  int dummy;
  
  if (!ATmatch(t,"o(<term>,<term>)",&tm,&vars))
        rg_error("correctopenterm expects ATerm  of sort openterm",t);
  return welltypedopen1(tm,vars,NULL,&dummy,emsg);
}

/* #include "datatypes.h" */


static char *fresh_name(char *name)
{ /* it still has to be checked whether a name is already being used 
     in that case a new name has to be generated */
  string *str;
  int i;
  str=new_string(name);
  for( i=0 ; (is_used(str->s)) ; i++)
    { sprintf(str->s,"%s%d",name,i); }
  /* check that name does not already exist, otherwise,
     add some suffix and check again */
  return str->s;
}

static char *extended_fresh_name(char *name,ATerm pars)
{ /* it still has to be checked whether a name is already being used
     in that case a new name has to be generated */
  string *str;
  int i;
  str=new_string(name);
  for( i=0 ; ((is_used(str->s))||
                 (occursin(ATmake("<str>",str->s),pars))) ; i++)
    { sprintf(str->s,"%s%d",name,i); }
  /* check that name does not already exist, otherwise,
     add some suffix and check again */
  return str->s;
}


/****************  substitute_data and substitute_datalist***********/

static void initialize_formats(void)
{ 
  ins2_symbol=ATmakeAFun("ins",2,ATfalse);
  ins3_symbol=ATmakeAFun("ins",3,ATfalse);
  ins4_symbol=ATmakeAFun("ins",4,ATfalse);
  t_symbol=ATmakeAFun("t",2,ATfalse);
  alt_symbol=ATmakeAFun("alt",2,ATfalse);
  seq_symbol=ATmakeAFun("seq",2,ATfalse);
  par_symbol=ATmakeAFun("par",2,ATfalse);
  lmer_symbol=ATmakeAFun("lmer",2,ATfalse);
  cond_symbol=ATmakeAFun("cond",3,ATfalse);
  sum_symbol=ATmakeAFun("sum",3,ATfalse);
  com_symbol=ATmakeAFun("com",2,ATfalse);
  bound_symbol=ATmakeAFun("bound",2,ATfalse);
  at_symbol=ATmakeAFun("at",2,ATfalse);
  hide_symbol=ATmakeAFun("hide",2,ATfalse);
  rename_symbol=ATmakeAFun("rename",2,ATfalse);
  encap_symbol=ATmakeAFun("encap",2,ATfalse);
  name_symbol=ATmakeAFun("name",2,ATfalse);
  smd_symbol=ATmakeAFun("smd",5,ATfalse);
  e_symbol=ATmakeAFun("e",3,ATfalse);
  i_symbol=ATmakeAFun("i",1,ATfalse);
  f_symbol=ATmakeAFun("f",3,ATfalse);
  v_symbol=ATmakeAFun("v",2,ATfalse);

  ATprotectAFun(ins2_symbol);
  ATprotectAFun(ins3_symbol);
  ATprotectAFun(ins4_symbol);
  ATprotectAFun(t_symbol);
  ATprotectAFun(alt_symbol);
  ATprotectAFun(seq_symbol);
  ATprotectAFun(par_symbol);
  ATprotectAFun(lmer_symbol);
  ATprotectAFun(cond_symbol);
  ATprotectAFun(sum_symbol);
  ATprotectAFun(com_symbol);
  ATprotectAFun(bound_symbol);
  ATprotectAFun(at_symbol);
  ATprotectAFun(hide_symbol);
  ATprotectAFun(rename_symbol);
  ATprotectAFun(encap_symbol);
  ATprotectAFun(name_symbol);
  ATprotectAFun(smd_symbol);
  ATprotectAFun(e_symbol);
  ATprotectAFun(i_symbol);
  ATprotectAFun(f_symbol);
  ATprotectAFun(v_symbol);

  ATprotect(&comm_term);
  ATprotect(&emv_term);
  ATprotect(&emt_term);
  ATprotect(&eml_term);
  ATprotect(&delta_term);
  ATprotect(&tau_action);
  ATprotect(&tau_term);
  ATprotect(&terminated_term);
  ATprotect(&eme_term);
  ATprotect(&emf_term);
  ATprotect(&eme_term);
  emv_term=ATmake("emv");
  emt_term=ATmake("emt");
  eml_term=ATmake("eml");
  delta_term=ATmake("delta");
  tau_term=ATmake("tau");
  tau_action=ATmake("<str>","tau");
  terminated_term=ATmake("terminated");
  eme_term=ATmake("eme");
  emf_term=ATmake("emf");
  ems_term=ATmake("ems");
  
}

static ATerm substitute_variable_rec(ATerm vars, ATerm pars,ATerm s_term)
{ 
  ATerm s1_term=NULL;
  ATerm t=NULL;
  if (pars==emt_term) 
   { if (vars==emv_term) 
        return NULL;
     else rg_error("Non matching vars and pars list",NULL);
   }
  /* if (ATmatch(vars,"ins(<str>,<str>,<term>)",&s1,&dummystring,&vars)) */
  s1_term=ATgetArgument(vars,0);
  vars=ATgetArgument(vars,2);
  /* if (!(ATmatch(pars,"ins(<term>,<term>)",&t,&pars))) */
  t=ATgetArgument(pars,0);
  pars=ATgetArgument(pars,1);
  /* rg_error("argument and parameterlist lengths do not match",NULL); */
  if (s_term==s1_term)
   { return t; }
  return substitute_variable_rec(vars,pars,s_term);
  /*    
  rg_error("Non matching vars and pars list",NULL);
  return NULL; */
}


static ATerm substitute_datalist_rec(ATerm vars, ATerm pars, ATerm tl);

static ATerm substitute_data_rec(ATerm vars, ATerm pars,ATerm t)
{ ATerm fnameterm=NULL;
  ATerm arg=NULL, t1=NULL, t3=NULL;
  
  /* if (ATmatch(t,"t(<str>,<term>)",&fname,&arg)) */

  /* ATfprintf(stderr,"vars %t\npars %t\nt %t\n\n", vars,pars,t); */
  fnameterm=ATgetArgument(t,0);
  arg=ATgetArgument(t,1);
  if (arg==emt_term)
   { t1=substitute_variable_rec(vars,pars,fnameterm);
        
     if (t1==NULL)
      { return t; }
     return t1;
   }
 else 
  { t3=(ATerm)ATmakeAppl2(t_symbol,fnameterm,
          substitute_datalist_rec(vars,pars,arg));
          
    return t3; 
  }
/* rg_error("Expect a data ATerm  of the form t(_,_)",t); */
  return NULL;
}

static ATerm substitute_datalist_rec(ATerm vars, ATerm pars,ATerm tl) 
{ 
  ATerm t1=NULL, t3=NULL;
  
  /* ATfprintf(stdout,"substitutelist %t\n",tl);  */
  if (tl==emt_term) return tl;
  /* if (ATmatch(tl,"ins(<term>,<term>)",&t1,&tl)) */
  t1=ATgetArgument(tl,0);
  tl=ATgetArgument(tl,1);
  t3=(ATerm)ATmakeAppl2(ins2_symbol,
           substitute_data_rec(vars,pars,t1),
                    substitute_datalist_rec(vars,pars,tl)); 
      
  return t3; 
}

static ATerm substitute_datalist(ATerm vars, ATerm pars,ATerm tl) 
{ /* ATfprintf(stderr,"vars %t\npars %t\n\n",vars,pars);  */
  if (pars==emt_term) return tl;
  return substitute_datalist_rec(vars,pars,tl);
}

static ATerm substitute_data(ATerm vars, ATerm pars,ATerm t)
{
  if (pars==emt_term) return t;
  return substitute_data_rec(vars,pars,t);
}


static ATerm substitute_pCRLproc(ATerm vars, ATerm pars,ATerm p)
{ char *s1=NULL, *s2=NULL, *newvar=NULL;
  int n;
  ATerm p1=NULL,p2=NULL, p3=NULL;
 
  if (ATmatch(p,"alt(<term>,<term>)",&p1,&p2))
     { p3=ATmake("alt(<term>,<term>)",
                substitute_pCRLproc(vars,pars,p1),
                substitute_pCRLproc(vars,pars,p2)); 
       
       return p3;
     }
  if (ATmatch(p,"seq(<term>,<term>)",&p1,&p2))
     { p3=ATmake("seq(<term>,<term>)",
                substitute_pCRLproc(vars,pars,p1),
                substitute_pCRLproc(vars,pars,p2)); 
       
       return p3;
     }
  if (ATmatch(p,"cond(<term>,<term>,<term>)",&p1,&p2,&p3))
     { p3=ATmake("cond(<term>,<term>,<term>)",
                substitute_pCRLproc(vars,pars,p1),
                substitute_data(vars,pars,p2),
                substitute_pCRLproc(vars,pars,p3));
       
       return p3;
     }
  if (ATmatch(p,"sum(<str>,<str>,<term>)",&s1,&s2,&p1))
   { if (occursintermlist(s1,pars)||occursinvar(s1,vars))
      { newvar=getvarname(s1,emv_term);
        p1=substitute_pCRLproc(
              ATmake("ins(t(<str>,emt),emt)",newvar),
                     ATmake("ins(<str>,<str>,emv)",s1,s2),p1);
        s1=newvar; }
     p3=ATmake("sum(<str>,<str>,<term>)",s1,s2,
                substitute_pCRLproc(vars,pars,p1)); 
     
     return p3;
    }
  if (ATmatch(p,"name(<str>,<int>,<term>)",&s1,&n,&p1))
     { p3=ATmake("name(<str>,<int>,<term>)",s1,n,
                substitute_datalist(vars,pars,p1)); 
       
       return p3;
     }
  if (ATmatch(p,"delta"))
     { 
        
       return p; }
  if (ATmatch(p,"tau"))
     {  
       return p; }
  rg_error("Expect pCRL process",p);
  return NULL;
}

ATerm substitute_parlist(char *arg, char *par,ATerm l)
{ char *s1=NULL, *s2=NULL;
  ATerm t3=NULL;
  if (ATmatch(l,"ins(<str>,<str>,<term>)",&s1,&s2,&l))
   { if (strequal(par,s1))
        t3=ATmake("ins(<str>,<str>,<term>)",arg,s2,l);
     else t3=ATmake("ins(<str>,<str>,<term>)",s1,s2,
          substitute_parlist(arg,par,l));
   }
  else if (l==emv_term) 
        t3=l;
  else rg_error("Expect variablelist",l);
  
  return t3;
}

/********************************************************************/
/*                                                                  */
/*   BELOW THE PROCEDURES ARE GIVEN TO TRANFORM PROCESSES TO        */
/*   LINEAR PROCESSES.                                              */
/*                                                                  */
/*                                                                  */
/*                                                                  */
/********************************************************************/



typedef enum { first, later } variableposition;

/****************  tovarheadGNF  *********************************/

static ATerm untype(ATerm t)
{ ATerm result=NULL;
  char *str; 
  
  if (ATmatch(t,"ins(<str>,<str>,<term>)", &str,&dummystring,&t)) 
   result=ATmake("ins(t(<str>,emt),<term>)",str,untype(t));
 else result=emt_term;

  
  return result;
}

typedef enum { alt, sum, /* cond,*/ seq, name } state;



static ATerm parameters_that_occur_in_body
        (ATerm parameters,ATerm  body)
{ char *varname, *varsort;       
  if (parameters==emv_term)
      return parameters;
  else
    { if (!ATmatch(parameters,"ins(<str>,<str>,<term>)",
                   &varname,&varsort,&parameters))
         rg_error("Expect variable list",parameters);
      else                
       { parameters=parameters_that_occur_in_body(parameters,body);
         if (occursinpCRLterm(varname,body,0))
          { /* ATfprintf(stderr,"%s:%s occurs \n", varname,varsort); */
             return ATmake("ins(<str>,<str>,<term>)",
                          varname,varsort,parameters); }
         else 
          { if debug ATfprintf(stderr,"%s:%s does not occur \n", varname,varsort);
            return parameters; }
       }
    }
  return NULL;
}        

static int newprocess(ATerm parameters, ATerm body,
              processstatustype ps)
{ arglist *args=NULL;
  int n=0;
  char *string1=NULL;
  string1=fresh_name("P");
  parameters=parameters_that_occur_in_body(parameters, body);
  if (make_arglist(parameters,&args,scratch2,string1)<=0)
     rg_error("Cannot make arglist",NULL);
  n=insertobject(string1,args,0,proc);
  if (n<=0) 
   { if (n==0) rg_error("Cannot store a process, as it exists already",NULL);
     if (n==-1) 
        rg_error("Cannot store a process, as there are too many objects stored",NULL);
     if (n==-2) rg_error("Out of memory. Cannot store a process",NULL);
   } 
  objectdata[n].processbody=body;
  objectdata[n].parameters=parameters;
  objectdata[n].processstatus=ps;
  objectdata[n].canterminate=canterminatebody(body);
  if (debug) 
     ATfprintf(stderr,"New process %s(%t)=%t\n",string1,parameters,body); 
  return n;
}


char *getvarname(char *s,ATerm f)
{ 
  s=fresh_name(s);
  insertvariablename(s);
  return s; 
}

ATerm make_pars(arglist *arg,ATerm freevars)
{ ATerm t3=NULL;
  
  if (arg==NULL)
     t3=emv_term;
  else t3=ATmake("ins(<str>,<str>,<term>)",
      getvarname(sortdata[arg->n].sortname->s,freevars),
      sortdata[arg->n].sortname,
            make_pars(arg->next,freevars));  
  
  return t3;
}


/* the following variables give the indices of the processes that
represent tau
     and delta, respectively */
     
int tau_process=0;
int delta_process=0;

ATerm bodytovarheadGNF(ATerm body, state s,ATerm freevars, 
            variableposition v, char *err_mes)
{ /* it is assumed that we only receive processes with
     operators alt, seq, sum, cond, name, delta, tau in it */

  ATerm body1=NULL,body2=NULL,t3=NULL,condition=NULL;
  char *string1=NULL,*string2=NULL;
  int n,m;
  /* ATfprintf(stderr,"bodytovarheadGNF %t\n",body); */
  

  if (ATmatch(body,"alt(<term>,<term>)",&body1,&body2))
   { if (alt>=s)
      { body1=bodytovarheadGNF(body1,alt,freevars,first,err_mes);
      if (body1==NULL) 
           t3=NULL;
        else 
         { body2=bodytovarheadGNF(body2,alt,freevars,first,err_mes);
           if (body2==NULL) t3=NULL;
           else t3=ATmake("alt(<term>,<term>)",body1,body2);
      }  }
     else
      { body1=bodytovarheadGNF(body,alt,freevars,first,err_mes);
        if (body1==NULL) t3=NULL;
        else 
         { n=newprocess(freevars,body1,pCRL);
           t3=ATmake("name(<str>,<int>,<term>)",objectdata[n].objectname
                         ,n,untype(objectdata[n].parameters));
      }  }
   }
  else
  if (ATmatch(body,"sum(<str>,<str>,<term>)",&string1,&string2,&body1))
   { if (sum>=s)
      { if (occursinvar(string1,freevars))
         { char *newvar=NULL;
           newvar=getvarname(string1,emv_term);
           body1=substitute_pCRLproc(
              ATmake("ins(<str>,<str>,emv)",string1,string2),
              ATmake("ins(t(<str>,emt),emt)",newvar),
	      body1);
           string1=newvar; 
         }
        body1=bodytovarheadGNF(body1,sum,
           ATmake("ins(<str>,<str>,<term>)",
                 string1,string2,freevars),first,err_mes);
        if (body1==NULL) 
           t3=NULL;
        else
          t3=ATmake("sum(<str>,<str>,<term>)",string1,string2,body1);
       }
      else
       { body1=bodytovarheadGNF(body,alt,freevars,first,err_mes);
       if (body1==NULL) 
             t3=NULL;
         else
          { n=newprocess(freevars,body1,pCRL);
            t3=ATmake("name(<str>,<int>,<term>)", 
                  objectdata[n].objectname ,n,
                     untype(objectdata[n].parameters));
       }  }
   }
  else
  if (ATmatch(body,"cond(<term>,<term>,<term>)",&body1,&condition,&body2))
  { if ((s<=sum) && ((body1==ATmake("delta"))||(body2==ATmake("delta"))))
    { if (body2==ATmake("delta"))
      { body1=bodytovarheadGNF(body1,seq,freevars,first,err_mes);
        if (body1==NULL) 
           t3=NULL;
        else t3=ATmake("cond(<term>,<term>,delta)",body1,condition);
      }
      else /* body1==ATmake("delta") */
      { if (!existsnot(err_mes))
           { t3=NULL; }
        else
        { body2=bodytovarheadGNF(body2,seq,freevars,first,err_mes);
          if (body2==NULL) 
             t3=NULL;
          else t3=ATmake("cond(<term>,t(<str>,ins(<term>,emt)),delta)",
                      body2,"not",condition); 
    } } }
    else if (alt==s) /* body1!=delta and body1!=delta */
    { body1=bodytovarheadGNF(body1,seq,freevars,first,err_mes);
      if (body1==NULL) 
         t3=NULL;
      else 
      { body2=bodytovarheadGNF(body2,seq,freevars,first,err_mes);
        if (body2==NULL) 
           t3=NULL;
        else
        { if (!existsnot(err_mes))
          { t3=NULL; }
          else t3=ATmake(
        "alt(cond(<term>,<term>,delta),cond(<term>,t(<str>,ins(<term>,emt)),delta))",
                      body1,condition,body2,"not",condition); }
    }  }  
    else
    { body1=bodytovarheadGNF(body,alt,freevars,first,err_mes);
      if (body1==NULL) 
         t3=NULL;
      else 
      { n=newprocess(freevars,body1,pCRL);
        t3=ATmake("name(<str>,<int>,<term>)",
          objectdata[n].objectname,n,untype(objectdata[n].parameters)); 
   } } }
  else
  if (ATmatch(body,"seq(<term>,<term>)",&body1,&body2))
   { if (seq>=s)
      { body1=bodytovarheadGNF(body1,name,freevars,v,err_mes);
        if (body1==NULL) 
           t3=NULL;
        else
         { body2=bodytovarheadGNF(body2,seq,freevars,later,err_mes);
           if (body2==NULL) 
              t3=NULL;
           else t3=ATmake("seq(<term>,<term>)",body1,body2);
      }  }
     else
      { body1=bodytovarheadGNF(body,alt,freevars,first,err_mes);
        if (body1==NULL) 
           t3=NULL;
        else
         { n=newprocess(freevars,body1,pCRL);
           t3=ATmake("name(<str>,<int>,<term>)",
                objectdata[n].objectname,n,
                       untype(objectdata[n].parameters));
 }  }  }
  else
  if (ATmatch(body,"name(<str>,<int>,<term>)",&string1,&n,&body1))
   { if (v==first) 
        t3=body; 
     else
      { if (objectdata[n].object==proc) 
           t3=body;
        else /* YY */
         { if (objectdata[n].object==act)
            { if (objectdata[n].targetsort<=0)
               { body2=make_pars(objectdata[n].args,freevars);
                 /* ATfprintf(stderr,"HIER1 %s\n%t\n%t\n",
                        string1,body2,freevars); */
                 m=newprocess(body2,
                   ATmake("name(<str>,<int>,<term>)",
                              string1,n,maketerms(body2)),GNF);
                 objectdata[n].targetsort=m;
                 t3=ATmake("name(<str>,<int>,<term>)",
                        objectdata[m].objectname,m,body1); 
               }
              else
               { /* fprintf(stdout,"Oude actie voor process\n"); */
                 t3=ATmake("name(<str>,<int>,<term>)",
                    objectdata[objectdata[n].targetsort].objectname,
                        objectdata[n].targetsort,body1); 
            }  }
           else rg_error("Expect action or process",NULL);
   }  }  }
  else
  if (ATmatch(body, "tau"))
   { if (v==first) 
        t3=body; 
     else
      { if (tau_process==0)
         { n=newprocess(emv_term,body,pCRL);
           tau_process=n; }
        else n=tau_process;
        t3=ATmake("name(<str>,<int>,<term>)",
             objectdata[n].objectname,n,
                  untype(objectdata[n].parameters));

   }  }
   else
   if (ATmatch(body,"delta"))
   { if (v==first) 
        t3=body; 
     else
      { if (delta_process==0)
         { n=newprocess(emv_term,body,pCRL);
           delta_process=n; }
        else n=delta_process;
        t3=ATmake("name(<str>,<int>,<term>)",
             objectdata[n].objectname,n,
                    untype(objectdata[n].parameters));
   }  }
  else rg_error("Unexpected process format",body);

  
  /* ATfprintf(stderr,"Body to vaher end %t\n",t3); */
  return t3;
}


int procstovarheadGNF(arglist *procs,char *err_mes)
{ /* transform the processes in procs into newprocs */
  ATerm t=NULL;
  for( ; (procs!=NULL) ; procs=procs->next )
   { 
     t=bodytovarheadGNF(objectdata[procs->n].processbody,alt, 
                objectdata[procs->n].parameters,first,err_mes);
     objectdata[procs->n].processbody=t;
     if (NULL==t)
       return 0;
     if (debug) ATfprintf(stderr, "procstovarheadGNF %t\n", t);
   }
  return 1;
}

/**************** towards real GREIBACH normal form **************/

typedef enum { terminating,infinite} terminationstatus;


static int occursinterm(char *s, ATerm t)
{ char *string1=NULL;
  ATerm l=NULL;
  /* ATfprintf(stderr,"TERM: %t\n",t); */

  string1=ATgetName(ATgetAFun(ATgetArgument(t,0)));
  l=ATgetArgument(t,1);

  /* if (ATmatch(t,"t(<str>,emt)",&string1)) */
  if (l==emt_term)
     { if (streq(s,string1)) 
           return 1; 
        else return 0;}
  /* if (ATmatch(t,"t(<str>,<term>)",&string1,&l)) */
     { return occursintermlist(s,l); }
  /* rg_error("Expect a ATerm ", t);
  return 0; */
}


static int occursintermlist(char *s, ATerm l)
{ 
  ATerm t=NULL;
  /* ATfprintf(stderr,"s: %s    TERMLIST: %t\n",s,l);  */
  if (l==emt_term) return 0;
  /* if (ATmatch(l,"ins(<term>,<term>)",&t,&l)) */
  t=ATgetArgument(l,0);
  l=ATgetArgument(l,1);
  return (occursinterm(s,t)||occursintermlist(s,l)); 
/*   rg_error("Expect a termlist", l);
  return 0; */
}

static int occursinvar(char *s, ATerm l)
{ char *string1=NULL;
  if (l==emv_term) return 0;
  if (ATmatch(l,"ins(<str>,<str>,<term>)",&string1,&dummystring,&l))
     { if (streq(s,string1)) return 1;
       return occursinvar(s,l); }
  rg_error("Expect a variablelist", l);
  return 0;
}

static int occursinpCRLterm(char *s, ATerm p, int strict)
{ char *string1=NULL, *string2=NULL;
  ATerm t1=NULL, t2=NULL;
  int n=0;
 if (ATmatch(p,"alt(<term>,<term>)",&t1,&t2))
   { return (occursinpCRLterm(s,t1,strict)||occursinpCRLterm(s,t2,strict));
   }
  if (ATmatch(p,"seq(<term>,<term>)",&t1,&t2))
   { return (occursinpCRLterm(s,t1,strict)||occursinpCRLterm(s,t2,strict));
   } 
  if (ATmatch(p,"cond(<term>,<term>,delta)",&t1,&t2))
   { return (occursinpCRLterm(s,t1,strict)||occursinterm(s,t2));
   }
  if (ATmatch(p,"sum(<str>,<str>,<term>)",&string1,&string2,&t1))
   { if (strict)
        return (occursinpCRLterm(s,t1,strict)||strequal(s,string1));
     /*  below appears better? , but leads
        to errors. Should be investigated. */
      else return ((occursinpCRLterm(s,t1,strict))&&(!strequal(s,string1))); 
   }
  if (ATmatch(p,"name(<str>,<int>,<term>)",&string1,&n,&t1))
   { return occursintermlist(s,t1);
   }
  if (ATmatch(p,"delta"))
   { return 0; }
  if (ATmatch(p,"tau"))
   { return 0; }
  rg_error("Unexpected process format in occursinCRLterm",p);
  return 0;
}

ATerm putbehind(ATerm body1,ATerm body2)
{ ATerm t1=NULL, t2=NULL, t3=NULL;
  char *string1=NULL, *string2=NULL, *newvar=NULL;
  int n;

  

  if (ATmatch(body1,"alt(<term>,<term>)",&t1,&t2))
   { t3=ATmake("alt(<term>,<term>)",
             putbehind(t1,body2),putbehind(t2,body2)); }
  else 
  if (ATmatch(body1,"seq(<term>,<term>)",&t1,&t2))
   {
t3=ATmake("seq(<term>,<term>)",t1,putbehind(t2,body2));
   }
  else
  if (ATmatch(body1,"cond(<term>,<term>,delta)",&t1,&t2))
   { t3=ATmake("cond(<term>,<term>,delta)",
                  putbehind(t1,body2),t2);
   }
  else
  if (ATmatch(body1,"sum(<str>,<str>,<term>)",&string1,&string2,&t1))
   { /* we must take care that no variables in body2 are
        inadvertently bound */
     if (occursinpCRLterm(string1,body2,1))
      { newvar=getvarname(string1,emv_term);
        t1=substitute_pCRLproc(
            ATmake("ins(<str>,<str>,emv)",string1,string2),
            ATmake("ins(t(<str>,emt),emt)",newvar),
	    t1);
        string1=newvar; }
     t3=ATmake("sum(<str>,<str>,<term>)",string1,string2,
                       putbehind(t1,body2));
   }
  else
  if (ATmatch(body1,"name(<str>,<int>,<term>)",&string1,&n,&t1))
   { t3=ATmake("seq(<term>,<term>)",body1,body2);
   }
  else
  if (ATmatch(body1,"delta"))
   { t3=body1;
   }
  else
  if (ATmatch(body1,"tau"))
   { t3=ATmake("seq(tau,<term>)",body2);
   }
  else rg_error("Unexpected process format",body1);

  
  return t3;
}

ATerm distribute_condition(ATerm body1,
                ATerm condition,char *err_mes)
{ ATerm t1=NULL, t2=NULL, t3=NULL;
  char *string1=NULL, *string2=NULL, *newvar=NULL;
  int n;

  
  if (ATmatch(body1,"alt(<term>,<term>)",&t1,&t2))
   { t1=distribute_condition(t1,condition,err_mes);
     if (t1==NULL) 
        t3=NULL;
     else
      { t2=distribute_condition(t2,condition,err_mes);
        if (t2==NULL) 
           t3=NULL;
        else t3=ATmake("alt(<term>,<term>)",t1,t2);}
   }
  else
  if (ATmatch(body1,"seq(<term>,<term>)",&t1,&t2))
   { t3=ATmake("cond(<term>,<term>,delta)",body1,condition);
   }
  else
  if (ATmatch(body1,"cond(<term>,<term>,delta)",&t1,&t2))
   { if (existsand(err_mes))

     t3=ATmake("cond(<term>,t(<str>,ins(<term>,ins(<term>,emt))),delta)",
           t1,"and",t2,condition);
     else 
      { 
        t3=NULL; }
   }
  else
  if (ATmatch(body1,"sum(<str>,<str>,<term>)",&string1,&string2,&t1))
   { /* we must take care that no variables in body2 are
        inadvertently bound */
     if (occursinterm(string1,condition))
      { newvar=getvarname(string1,emv_term);
        t1=substitute_pCRLproc(
              ATmake("ins(<str>,<str>,emv)",string1,string2),
              ATmake("ins(t(<str>,emt),emt)",newvar),    
	      t1);
 
        string1=newvar; }
     t1=distribute_condition(t1,condition,err_mes);
     if (t1==NULL) 
        t3=NULL;
     else t3=ATmake("sum(<str>,<str>,<term>)",string1,string2,t1);
   }
  else
  if (ATmatch(body1,"name(<str>,<int>,<term>)",&string1,&n,&t1))
   { t3=ATmake("cond(<term>,<term>,delta)",body1,condition);
   }
  else
  if (ATmatch(body1,"delta"))
   { t3=body1;
   }
  else
  if (ATmatch(body1,"tau"))
   { t3=ATmake("cond(tau,<term>,delta)",condition);
   }
  else rg_error("Unexpected process format",body1);

  
  return t3;
}

ATerm distribute_sum(char *name,char *sort,ATerm body1)
{ ATerm t1=NULL, t2=NULL, t3=NULL;
  char *string1=NULL, *string2=NULL;
  int n;

  
  if (ATmatch(body1,"alt(<term>,<term>)",&t1,&t2))
   { t3=ATmake("alt(<term>,<term>)",
         distribute_sum(name,sort,t1),
           distribute_sum(name,sort,t2));
   }
  else
  if (ATmatch(body1,"seq(<term>,<term>)",&t1,&t2))
   { t3=ATmake("sum(<str>,<str>,<term>)",name,sort,body1);
   }
  else
  if (ATmatch(body1,"cond(<term>,<term>,delta)",&t1,&t2))
   { t3=ATmake("sum(<str>,<str>,<term>)",name,sort,body1);
   }
  else
  if (ATmatch(body1,"sum(<str>,<str>,<term>)",&string1,&string2,&t1))
   { t3=ATmake("sum(<str>,<str>,<term>)",name,sort,body1);
   }
  else
  if (ATmatch(body1,"name(<str>,<int>,<term>)",&string1,&n,&t1))
   { t3=ATmake("sum(<str>,<str>,<term>)",name,sort,body1);
   }
  else
  if (ATmatch(body1,"delta"))
   { t3=body1;
   }
  else
  if (ATmatch(body1,"tau"))
   { t3=body1;
   }
  else rg_error("Unexpected process format",body1);
  
  
  return t3;
}


ATerm substitute(
       ATerm args,ATerm parameters,ATerm body1)
{ ATerm t1=NULL, t2=NULL, t3=NULL;
  char *string1=NULL, *string2=NULL, *newvar=NULL;
  int n;

  
  if (ATmatch(body1,"alt(<term>,<term>)",&t1,&t2))
   { t3=ATmake("alt(<term>,<term>)",
         substitute(args,parameters,t1),
           substitute(args,parameters,t2));
   }
  else
  if (ATmatch(body1,"seq(<term>,<term>)",&t1,&t2))
   { t3=ATmake("seq(<term>,<term>)",
         substitute(args,parameters,t1),
           substitute(args,parameters,t2));
   }
  else
  if (ATmatch(body1,"cond(<term>,<term>,delta)",&t1,&t2))
   { t3=ATmake("cond(<term>,<term>,delta)",
         substitute(args,parameters,t1),
           substitute_data(parameters,args,t2));
   }
  else
  if (ATmatch(body1,"sum(<str>,<str>,<term>)",&string1,&string2,&t1))
   { if (occursintermlist(string1,args)||
                      occursinvar(string1,parameters))
     { newvar=getvarname(string1,emv_term);
       t1=substitute(ATmake("ins(t(<str>,emt),emt)",newvar),
       ATmake("ins(<str>,<str>,emv)",string1,string2),t1); string1=newvar; } 
     t3=ATmake("sum(<str>,<str>,<term>)",string1,string2,
                 substitute(args,parameters,t1));
   }
  else
  if (ATmatch(body1,"name(<str>,<int>,<term>)",&string1,&n,&t1))
   { t3=ATmake("name(<str>,<int>,<term>)",string1,n,
              substitute_datalist(parameters,args,t1));
   }
  else
  if (ATmatch(body1,"delta"))
   { t3=body1;
   }
  else
  if (ATmatch(body1,"tau"))
   { t3=body1;
   }
  else
  rg_error("Unexpected process format",body1);

  
  return t3;
}


static long exists_variable_for_sequence(arglist *process_names,
        ATerm process_body)
{ arglist *walker;

  if (regular2)
   { for(walker=seq_varnames; (walker!=NULL);
         walker=walker->next)
       { if (eqarglist(process_names,
             objectdata[walker->n].representedprocesses))
         return walker->n;
       }
    return 0;  
   }
  else
   { for(walker=seq_varnames; (walker!=NULL);
         walker=walker->next)
       { if (ATisEqual(process_body,
             objectdata[walker->n].representedprocess))
         return walker->n;
       }
    return 0;  
   }
}

static int procstorealGNFrec(int n, variableposition v, 
       arglist **todo, char *err_mes, int regular);


static arglist *extract_names(ATerm sequence)
{ char *string1=NULL;
  int n=0;
  ATerm args=NULL;
  if (ATmatch(sequence,"name(<str>,<int>,<term>)",
         &string1,&n,&args))
   { return new_arglist(n,NULL);
   }
  if (ATmatch(sequence,"seq(name(<str>,<int>,<term>),<term>)",
         &string1,&n,&args,&sequence))
   { if (objectdata[n].canterminate)
       return new_arglist(n,extract_names(sequence));
     else return new_arglist(n,NULL);
   }
  rg_error("Expect sequence of process names (1)",sequence);
  return NULL;
}

static ATerm parscollect(ATerm oldbody, ATerm *newbody)
{ char *string1=NULL;
  int n=0;
  ATerm args=NULL, pars1=NULL, pars2=NULL;
  /* ATfprintf(stderr,"parscollect %t\n", oldbody); */

  if (ATmatch(oldbody,"name(<str>,<int>,<term>)",
        &string1,&n,&args))
   { *newbody=ATmake("name(<str>,<int>,<term>)",
            string1,n,maketerms(objectdata[n].parameters));
     return objectdata[n].parameters;
   }     
  if (ATmatch(oldbody,"seq(name(<str>,<int>,<term>),<term>)",
           &string1,&n,&args,&oldbody))
   { ATerm pars=parscollect(oldbody,newbody);
     
     construct_renaming(pars,objectdata[n].parameters,&pars1,&pars2);
     /* ATfprintf(stderr,"pars %t\nnewpars %t\npars1 %t\n\n",
                  pars, objectdata[n].parameters,pars1); */
     *newbody=ATmake("seq(name(<str>,<int>,<term>),<term>)",
                 string1,n,maketerms(pars1),*newbody);
     /* ATfprintf(stderr,"newbody %t\n",*newbody); */
     return conc_var(pars1,pars);
   }
  rg_error("Expect a sequence of process names (2)",oldbody);
  return NULL;
}

static ATerm argscollect(ATerm t)
{ char *string1=NULL;
  int n=0;
  ATerm args=NULL;
  
  if (ATmatch(t,"name(<str>,<int>,<term>)",
                &string1,&n,&args))
    return args;
  if (ATmatch(t,"seq(name(<str>,<int>,<term>),<term>)",
         &string1,&n,&args,&t))
   { return conc_tl(args,argscollect(t));
   }
  rg_error("Expect a sequence of process names (3)",t);
  return NULL;      
}

static ATerm create_regular_invocation(ATerm sequence,
         arglist **todo,ATerm freevars)
{ arglist *process_names=NULL;
  char *string1;
  int n=0;
 
  ATerm rest=NULL, args=NULL;
  process_names=extract_names(sequence);
	if (process_names->next==NULL)
	{ /* length of list equals 1 */
	      release_totalarglist(process_names);
	   if (ATmatch(sequence,"name(<str>,<int>,<term>)",
	         &string1,&n,&args))
	      return sequence;
	   else 
	   if (ATmatch(sequence,
	           "seq(name(<str>,<int>,<term>),<term>)",
	         &string1,&n,&args,&rest))
	      return ATmake("name(<str>,<int>,<term>)",string1,n,args);
	   rg_error("Expect a sequence of process names",sequence);
	 }
	/* There is more than one process name in the sequence,
	   so, we must replace them by a single name */

	/* We first start out by searching whether
	   there is already a variable with a matching sequence
	   of variables */
        n=exists_variable_for_sequence(process_names,
                     sequence);
	if (n==0)
	 { /* There does not exist an appropriate variable,
	      so, make it and return its index in n */
	   ATerm newbody=NULL;   
	   if (regular2)
	    { ATerm pars=parscollect(sequence,&newbody);
	      n=newprocess(pars,newbody,pCRL);
              objectdata[n].representedprocesses=process_names;
	    }
	   else 
	    { n=newprocess(freevars,sequence,pCRL);
              objectdata[n].representedprocess=sequence;
	    }
	   seq_varnames=new_arglist(n,seq_varnames);
	   *todo=new_arglist(n,*todo);
	 }
	/* now we must construct arguments */
	if (regular2)
	   args=argscollect(sequence);
	else
	   args=maketerms(objectdata[n].parameters);
	return ATmake("name(<str>,<int>,<term>)",
	           objectdata[n].objectname->s,n,args);
}

static ATerm to_regular_form(ATerm t,arglist **todo,ATerm freevars)
/* t has the form of the sum, and condition over actions 
   each followed by a sequence of variables. We replace
   this variable by a single one, putting the new variable
   on the todo list, to be transformed to regular form also. */
{ ATerm body1=NULL, body2=NULL;
  char *string1=NULL, *string2=NULL;
  int n=0;
  if (ATmatch(t,"alt(<term>,<term>)",&body1,&body2))
     { body1=to_regular_form(body1,todo,freevars);
       body2=to_regular_form(body2,todo,freevars);
       return ATmake("alt(<term>,<term>)",body1,body2);
     } 
  else 
  if (ATmatch(t,"seq(name(<str>,<int>,<term>),<term>)",
           &string1,&n,&t,&body1))
     { /* the sequence of variables in 
               body1 must be replaced */
       body1=create_regular_invocation(body1,todo,freevars);
       return ATmake("seq(name(<str>,<int>,<term>),<term>)",
                string1,n,t,body1);
     } 
  else
  if (ATmatch(t,"seq(tau,<term>)",&body1))
     { /* the sequence of variables in 
               body1 must be replaced */
       body1=create_regular_invocation(body1,todo,freevars);
       return ATmake("seq(tau,<term>)",body1);
     } 
  else
  if (ATmatch(t,"cond(<term>,<term>,delta)",&body1,&t))
     { body1=to_regular_form(body1,todo,freevars);
       return ATmake("cond(<term>,<term>,delta)",body1,t);
     } 
  else
  if (ATmatch(t,"sum(<str>,<str>,<term>)",
               &string1,&string2,&body1))
     { body1=to_regular_form(body1,todo,
             ATmake("ins(<str>,<str>,<term>)",
                   string1,string2,freevars));
       return ATmake("sum(<str>,<str>,<term>)",
                 string1,string2,body1);
     }
  else
  if (ATmatch(t,"name(<str>,<int>,<term>)",&string1,&n,&body1))
     { return t;    
     }
  else
  if (ATmatch(t,"delta"))
     { return t;
     }
  else
  if (ATmatch(t,"tau"))
     { return t;
     }
  else rg_error("To regular form expects GNF",t);
  return NULL;
}


static ATerm procstorealGNFbody(
            ATerm body, variableposition v,
            arglist **todo, char *err_mes, 
            int *error, int regular, 
            processstatustype mode,
            ATerm freevars)
/* This process delivers the transformation of body
   to GNF with actions as a head symbol, or it
   delivers NULL if body is not a pCRL process.
   If regular=1, then an attempt is made to obtain a
   GNF where one action is always followed by a
   variable. */
{ 
  ATerm body1=NULL, body2=NULL, t3=NULL, t=NULL;
  char *string1=NULL, *string2=NULL;
  int n;
  *error=0;

  if (ATmatch(body,"alt(<term>,<term>)",&body1,&body2))
     { body1=procstorealGNFbody(body1,first,
                 todo,err_mes,error,regular,mode,freevars);
       if (*error) 
          t3=NULL;
       else 
        { body2=procstorealGNFbody(body2,first,todo,
               err_mes,error,regular,mode,freevars);
          if (*error) 
             t3=NULL;
          else t3=ATmake("alt(<term>,<term>)",body1,body2);
        }
     }
  else 
  if (ATmatch(body,"seq(<term>,<term>)",&body1,&body2))
     { body1=procstorealGNFbody(body1,v,
                   todo,err_mes,error,regular,mode,freevars);
       if (*error) 
          t3=NULL;
       else
        { body2=procstorealGNFbody(body2,later,
                   todo,err_mes,error,regular,mode,freevars);
          if (*error) 
             t3=NULL;
          else 
           { t3=putbehind(body1,body2);
             if ((regular) && (v==first))   
              { /* We must transform t3 to regular form */
                t3=to_regular_form(t3,todo,freevars);
              }
           }
     }  } 
  else
  if (ATmatch(body,"cond(<term>,<term>,delta)",&body1,&t))
     { body1=procstorealGNFbody(body1,first,
                   todo,err_mes,error,regular,mode,freevars);
       if (*error) 
          t3=NULL;
       else 
        { body1=distribute_condition(body1,t,err_mes);
          if (body1==NULL)
           { *error=1;
             t3=NULL; }
          else t3=body1;
     }  }
  else
  if (ATmatch(body,"sum(<str>,<str>,<term>)",&string1,&string2,&body1))
     { body1=procstorealGNFbody(body1,first,
                   todo,err_mes,error,regular,mode,
                     ATmake("ins(<str>,<str>,<term>)",
                        string1,string2,freevars));
       if (*error) 
          t3=NULL;
       else t3=distribute_sum(string1,string2,body1);
     }
  else
  if (ATmatch(body,"name(<str>,<int>,<term>)",&string1,&n,&t))
     { if (objectdata[n].object==act)
          { t3=body; }
       else
       if (v==later)
          { if ((!regular)||(mode=mCRL)) *todo=new_arglist(n,*todo);
            /* single = in `mode=mCRL' is important, otherwise crash 
               I do not understand the reason for this at this moment
               JFG (9/5/2000) */
            t3=body;
          }
       else
       if (objectdata[n].processstatus==mCRL)
          { *todo=new_arglist(n,*todo);
            t3=NULL; }
       /* The variable is a pCRL process and v==first, so,
          we must now substitute */
       else
       if (!procstorealGNFrec(n,first,todo,err_mes,regular))
        { *error=1;
          t3=NULL; }
       else 
        { 
          t3=substitute(t,objectdata[n].parameters,
                       objectdata[n].processbody);
          if (regular)
             t3=to_regular_form(t3,todo,freevars);
        }     
     }
  else
  if (ATmatch(body,"delta"))
     { t3=body;
     }
  else
  if (ATmatch(body,"tau"))
     { t3=body;
     }
  else
  if (ATmatch(body,"par(<term>,<term>)",&body1,&body2))
     { body1=procstorealGNFbody(body1,later,
                     todo,err_mes,error,regular,mode,freevars);
      if (!*error) 
         body2=procstorealGNFbody(body2,later,
                     todo,err_mes,error,regular,mode,freevars);
      t3=NULL;
     }
  else
  if ((ATmatch(body,"hide(<term>,<term>)",&t,&body1))||
      (ATmatch(body,"rename(<term>,<term>)",&t,&body1))||
      (ATmatch(body,"encap(<term>,<term>)",&t,&body1)))
     { body1=procstorealGNFbody(body1,later,
                   todo,err_mes,error,regular,mode,freevars);
       t3=NULL;
     }
  else
  rg_error("Unexpected process format",body);

  
  return t3;
}


int procstorealGNFrec(int n, variableposition v, arglist **todo,
             char *err_mes, int regular)
/* Do a depth first search on process variables and substitute
   for the headvariable of a pCRL process, in case it is a process, 
   such that we obtain a Greibach Normal Form. All pCRL processes will
   be labelled with GNF to indicate that they are in
   Greibach Normal Form. */

{ ATerm t=NULL;
  int error=0;
  
  if (objectdata[n].processstatus==pCRL)
     { /* ATfprintf(stderr,"TOGNFbusy %t\n",
             objectdata[n].processbody); */
       objectdata[n].processstatus=GNFbusy;
       t=procstorealGNFbody(objectdata[n].processbody,first,
              todo,err_mes,&error,regular,pCRL,
                objectdata[n].parameters);
       if (error) return 0;
       if ((t==NULL)||(objectdata[n].processstatus!=GNFbusy))
            rg_error("Something wrong with recursion",NULL);
       objectdata[n].processbody=t;
       objectdata[n].processstatus=GNF;
  if debug ATfprintf(stdout,"DEFINE LINEAR EQUATION: %d\n%s(%t)=%t\n\n",
           objectdata[n].processstatus,
            objectdata[n].objectname->s,objectdata[n].parameters,t); 
     }
  else if (objectdata[n].processstatus==mCRL)
     { objectdata[n].processstatus=mCRLbusy;
       t=procstorealGNFbody(objectdata[n].processbody,first,todo,
             err_mes, &error,regular,mCRL,objectdata[n].parameters);
       /* if t is not equal to NULL,
          the body of this process is itself a processidentifier */
       
       if (error) return 0;
       objectdata[n].processstatus=mCRLdone; 
     }
  else if ((objectdata[n].processstatus==GNFbusy) && (v==first))
         { sprintf(err_mes,"Unguarded recursion in process %s",
                 objectdata[n].objectname->s);
           return 0; }
  else if (objectdata[n].processstatus==GNFbusy)
          {;} 
  else if (objectdata[n].processstatus==GNF)
       { /* do nothing */ ;}
  else if (objectdata[n].processstatus==mCRLbusy)
       { sprintf(err_mes,"Unguarded recursion without pCRL operators");
        return 0; }
  else if (objectdata[n].processstatus==mCRLdone)
       {;}
  else { ATfprintf(stderr,"HUH: %s(%t)\n",objectdata[n].objectname,
                  objectdata[n].parameters);
         fprintf(stderr,"HUH: %d\n",objectdata[n].processstatus);
         rg_error("Strange process type",NULL); } 
  return 1;
}



int procstorealGNF(int n, char *rec_mes,int regular)
{ arglist *todo=NULL,*a=NULL;
  todo=new_arglist(n,NULL);
  for(; (todo!=NULL) ; )
    { n=todo->n;
      a=todo;
      todo=todo->next;
      release_arglist(a);
      if debug
         ATfprintf(stderr,"procstorealGNF: %d %t\n%t\n\n",
            n,objectdata[n].parameters,objectdata[n].processbody); 
      if (!procstorealGNFrec(n,first,&todo,rec_mes,regular))
         return 0;
    }
  return 1;
}




/**************** GENERATE LPE **********************************/
/*                                                              */
/*                                                              */
/*                                                              */
/*                                                              */
/*                                                              */
/*                                                              */
/****************************************************************/


/**************** Make pCRL procs  ******************************/

arglist *pCRLprocs=NULL;

int alreadyinpCRLprocs(int n)
{ arglist *walker=NULL;
  for(walker=pCRLprocs ; (walker!=NULL) ; walker=walker->next)
     { if (walker->n==n) return 1; }
  return 0;
}

void makepCRLprocs(ATerm t)
{ ATerm t1=NULL,t2=NULL;
  char *string1=NULL, *string2=NULL;
  int n;
  
  if ((ATmatch(t,"alt(<term>,<term>)",&t1,&t2))||
      (ATmatch(t,"seq(<term>,<term>)",&t1,&t2)))
   { makepCRLprocs(t1);
     makepCRLprocs(t2); 
     return; }
  if ((ATmatch(t,"cond(<term>,<term>,delta)",&t1,&t2))||
      (ATmatch(t,"sum(<str>,<str>,<term>)",&string1,&string2,&t1)))
   { makepCRLprocs(t1); 
     return; }
  if (ATmatch(t,"name(<str>,<int>,<term>)",&string1,&n,&t1))
   { if (objectdata[n].object==act) return;
     /* so it is a process */
     if (alreadyinpCRLprocs(n)) return;
     pCRLprocs=new_arglist(n,pCRLprocs);
     makepCRLprocs(objectdata[n].processbody);
     return;
   }
  if ((ATmatch(t,"delta"))||
      (ATmatch(t,"tau")))
   { return; }
  rg_error("unexpected process format",t);
}

/**************** Collectparameterlist ******************************/

int alreadypresent(char **s1,char *s2,ATerm vl,int n)
{ char *string1=NULL, *string2=NULL;
  if (vl==emv_term) return 0;
  if (ATmatch(vl,"ins(<str>,<str>,<term>)",&string1,&string2,&vl))
   { if(strequal((*s1),string1))
      { if (!strequal(s2,string2)) 
         { string1=fresh_name(*s1);
           insertvariablename(string1);
           objectdata[n].processbody=
               substitute_pCRLproc(
                   ATmake("ins(<str>,<str>,emv)",*s1,s2),
	           ATmake("ins(t(<str>,emt),emt)",string1),
                   objectdata[n].processbody);
            objectdata[n].parameters=

           substitute_parlist(string1,*s1,objectdata[n].parameters);
           (*s1)=string1;
           
           return 0;
         }
        else return 1;
      }
     return alreadypresent(s1,s2,vl,n);
   }
  rg_error("Expect variablelist",vl);
  return 0;
}

ATerm joinparameters(ATerm par1,ATerm par2,int n)
{ char *string1=NULL, *string2=NULL;
  ATerm t3=NULL;
  if (par2==emv_term) 
   { t3=par1;
   }
  else
  if (ATmatch(par2,"ins(<str>,<str>,<term>)",&string1,&string2,&par2))
   { if (alreadypresent(&string1,string2,par1,n))
      { t3=joinparameters(par1,par2,n);
      }
     else 
      { t3=ATmake("ins(<str>,<str>,<term>)",string1,string2,
               joinparameters(par1,par2,n));
    } }
  else rg_error("Want variablelist",par2);
  return t3;
}

ATerm collectparameterlist(void)
{ arglist *walker=NULL;
  ATerm parameters=NULL;
  parameters=emv_term;
  for (walker=pCRLprocs ; (walker!=NULL) ; walker=walker->next)
    { parameters=

joinparameters(parameters,objectdata[walker->n].parameters,walker->n);
    }
  return parameters;
}

/**************** makenewsort  **********************************/

char *makenewsort(char *s, int constructorsort, specificationbasictype *spec)
{ int n=0;
  s=fresh_name(s);
  n=insertsort(s,constructorsort);
  if (to_file) fprintf(outfile,"sort %s\n",s);
  spec->sorts=ATmake("ins(<str>,<term>)",s,spec->sorts);
  return s;
}

void printparsorts(FILE *f,ATerm t,char *divider)
{ char *s=NULL;
  for( ; (ATmatch(t,"ins(<str>,<term>)",&s,&t)) ; )
      { fprintf(f,"%s%s",divider,s);
        divider="#";
      }
}


char *makenewobject(char *s, ATerm args, char *target, objecttype o,
                     specificationbasictype *spec, int exactstring)
{ arglist *a=NULL;
  int n=0;
  if (!exactstring) s=fresh_name(s);
  if (make_arglist(args,&a,scratch2,s)<=0)
       rg_error("Cannot make arglist",NULL);
  n=existsort(target);
  if (n==0)
     rg_error("Invalid sort",NULL);
  insertobject(s,a,n,o);
  if (o==func)
   { spec->funcs=ATmake(
                  "ins(f(<str>,<term>,<str>),<term>)",s,args,target,spec->funcs);
    if (to_file) 
      { fprintf(outfile,"func %s:" ,s);
        printparsorts(outfile,args,"");
        fprintf(outfile,"->%s\n",target);
      }
   }
  if (o==map)
   { spec->maps=ATmake(
                  "ins(f(<str>,<term>,<str>),<term>)",s,args,target,spec->maps);
     if (to_file) 
      { fprintf(outfile,"map  %s:" ,s);
        printparsorts(outfile,args,"");
        fprintf(outfile,"->%s\n",target);
      }
   }
  return s;
}

/**************** Collectsumlist  **********************************/

static int existsor(char *err_mes)
{ arglist *a=NULL;
  int n;
  int result=0;
  n=existsort("Bool");
  a=new_arglist(n,new_arglist(n,NULL));
  result=existsobject("or",a);
  if (!result)
    sprintf(err_mes,
       "Need function or:Bool#Bool->Bool to linearise");
  release_totalarglist(a);
  return result;
}

static int existsand(char *err_mes)
{ arglist *a=NULL;
  int n;
  int result=0;
  n=existsort("Bool");
  a=new_arglist(n,new_arglist(n,NULL));
  result=existsobject("and",a);
  if (!result)
    sprintf(err_mes,
       "Need function and:Bool#Bool->Bool to linearise");
  release_totalarglist(a);
  return result;
}

static int existsnot(char *err_mes)
{ arglist *a=NULL;
  int n;
  int result=0;
  n=existsort("Bool");
  a=new_arglist(n,NULL);
  result=existsobject("not",a);
  if (!result)
    sprintf(err_mes,
       "Need function not:Bool->Bool to linearise");
  release_totalarglist(a);
  return result;
}

int existseq(int n,char *err_mes)
{ arglist *a=NULL;
  int result=0;
  a=new_arglist(n,new_arglist(n,NULL));
  result=existsobject("eq",a);
  release_totalarglist(a);
  if ((result>0)&&
     ((objectdata[n].object==func)||(objectdata[n].object==map))&&
     (objectdata[result].targetsort==existsort("Bool")))
    return 1;
  
  sprintf(err_mes,"Need function eq:%s#%s->Bool to linearise",
           sortdata[n].sortname->s,sortdata[n].sortname->s);
  return 0;
}

ATerm localequationvariables=NULL;

static void declare_equation_variables(ATerm t1)
{ ATerm dummyterm=NULL;
  ATerm dummystring=NULL;

  if (localequationvariables!=NULL)
      {rg_error("Cannot declare variables as previous section is not yet closed",
                localequationvariables);}
  localequationvariables=t1;
  if (to_file)
   { if (ATmatch(localequationvariables,
            "ins(<str>,<str>,<term>)",&dummystring,&dummystring,&dummyterm))
      { print_varlist(outfile,localequationvariables,"var  ");
        fprintf(outfile,"\n"); }
     fprintf(outfile,"rew  ");
   }  
}

static void end_equation_section(void)
{ if (localequationvariables==NULL)
     rg_error("Cannot open an non ended equation section",NULL);
  
  localequationvariables=NULL;
}

static void newequation(ATerm t2, ATerm t3, specificationbasictype *spec)
{ 
  if (localequationvariables==NULL)
     rg_error("Variables must be declared first!",t2);
  
  spec->eqns=ATmake("ins(e(<term>,<term>,<term>),<term>)",
                     localequationvariables,t2,t3,spec->eqns);
  if (to_file)
   { long pos=4;
     print_term(outfile,t2,&pos);
     fprintf(outfile,"=");
     pos++;
     print_term(outfile,t3,&pos);
     fprintf(outfile,"\n"); }
}


typedef struct 
   { 
     char *stacksort;
     ATerm sorts;
     ATerm get;
     char *push;
     char *emptystack;
     char *empty; 
     char *pop;

     
     char *getstate; } stackoperations;

     
typedef struct stacklisttype
   {
     stackoperations *opns;  
     ATerm parameterlist;      
     char *stackvar;
     struct stacklisttype *next;
     int no_of_states; 
     /* the boolean state variables occur in reverse
        order, i.e. the least significant first, whereas
        in parameter lists, the order is reversed. */
     ATermList booleanStateVariables; } stacklisttype;

typedef struct
  { char *elementsort;
    char *one;
    char *x2plus1;
    char *x2plus0;
    char *eqelement; } controlstateoperations;
    
/* the following datatype is needed to store the functions describing 
   and manipulating the control states of the processes */
   
static controlstateoperations *controlstate=NULL; 

static void declare_control_state(
               specificationbasictype *spec, arglist * pCRLprocs)
{ char *var0=NULL, *var1=NULL;

  
  if (controlstate==NULL)
   { if (oldstate)
     { /* if the sort State has not been declared, it must be declared */
        
       controlstate=malloc(sizeof(controlstateoperations));
       controlstate->elementsort=makenewsort("State",1,spec);
       controlstate->one=makenewobject("one",ATmake("ems"),
                 controlstate->elementsort,func,spec,0);
       controlstate->x2plus1=makenewobject("x2p1",ATmake("ins(<str>,ems)",
                 controlstate->elementsort),controlstate->elementsort,func,spec,0);
       controlstate->x2plus0=makenewobject("x2p0",ATmake("ins(<str>,ems)",
             controlstate->elementsort),controlstate->elementsort,func,spec,0);

       controlstate->eqelement=makenewobject("eq",ATmake("ins(<str>,ins(<str>,ems))",
             controlstate->elementsort,controlstate->elementsort),"Bool",map,spec,1);
       var0=getvarname("sv",emv_term);
       var1=getvarname("sv",emv_term);
       declare_equation_variables(ATmake("ins(<str>,<str>,ins(<str>,<str>,emv))",
             var0,controlstate->elementsort,var1,controlstate->elementsort));
         
       newequation(ATmake("t(<str>,ins(t(<str>,emt),ins(t(<str>,emt),emt)))",
             controlstate->eqelement,var0,var0), ATmake("t(<str>,emt)","T"),spec);
       newequation(
          ATmake("t(<str>,ins(t(<str>,emt),ins(t(<str>,ins(t(<str>,emt),emt)),emt)))",
             controlstate->eqelement,controlstate->one,controlstate->x2plus1,var1),
             ATmake("t(<str>,emt)","F"),spec);
       newequation(
          ATmake("t(<str>,ins(t(<str>,emt),ins(t(<str>,ins(t(<str>,emt),emt)),emt)))",
              controlstate->eqelement,controlstate->one,controlstate->x2plus0,var1),
                   ATmake("t(<str>,emt)","F"),spec);
       newequation(
          ATmake("t(<str>,ins(t(<str>,ins(t(<str>,emt),emt)),ins(t(<str>,emt),emt)))",
              controlstate->eqelement,controlstate->x2plus1,var0,controlstate->one),
                   ATmake("t(<str>,emt)","F"),spec);
       newequation(
          ATmake("t(<str>,ins(t(<str>,ins(t(<str>,emt),emt)),ins(t(<str>,emt),emt)))",
              controlstate->eqelement,controlstate->x2plus0,var0,controlstate->one),
                   ATmake("t(<str>,emt)","F"),spec);
       newequation(                        
             ATmake("t(<str>,ins(t(<str>,ins(t(<str>,emt),emt)),ins(t(<str>,ins(t(<str>,emt),emt)),emt)))",
                controlstate->eqelement,controlstate->x2plus1,var0,controlstate->x2plus0,var1),
                    ATmake("t(<str>,emt)","F"),spec);
       newequation(
            ATmake("t(<str>,ins(t(<str>,ins(t(<str>,emt),emt)),ins(t(<str>,ins(t(<str>,emt),emt)),emt)))",
              controlstate->eqelement,controlstate->x2plus0,var0,controlstate->x2plus1,var1),
                    ATmake("t(<str>,emt)","F"),spec);

       newequation(
             ATmake("t(<str>,ins(t(<str>,ins(t(<str>,emt),emt)),ins(t(<str>,ins(t(<str>,emt),emt)),emt)))",
                 controlstate->eqelement,controlstate->x2plus0,var0,controlstate->x2plus0,var1),
             ATmake("t(<str>,ins(t(<str>,emt),ins(t(<str>,emt),emt)))",
                            controlstate->eqelement,var0,var1),spec);

       newequation(
            ATmake("t(<str>,ins(t(<str>,ins(t(<str>,emt),emt)),ins(t(<str>,ins(t(<str>,emt),emt)),emt)))",
            controlstate->eqelement,controlstate->x2plus1,var0,controlstate->x2plus1,var1),
            ATmake("t(<str>,ins(t(<str>,emt),ins(t(<str>,emt),emt)))",
                         controlstate->eqelement,var0,var1),spec);
       end_equation_section();
    }
    else /* We do not want the old state encoding with "one", "x2p1" and "x2p0",
            but an enumerated type or, with -binary a binary state encoding */
    if (binary)
    { /* No types and equations need to be declared */

    }
    else /* we want an enumerated type encoding */
    { int i=0;
      for(i=0 ; pCRLprocs!=NULL; i++){pCRLprocs=pCRLprocs->next;};
      /* i is the number of states */
      create_enumeratedtype(i,spec);
     
    }
  }
}  
/* All datatypes for different stacks that are being generated
   are stored in the following list, such that it can be investigated
   whether a suitable stacktype already exist, before generating a new
one */
   
static stacklisttype *stacklist=NULL;   


void makepushargsvarsrec(ATerm *t1,ATerm *t2, ATerm sorts)
{ char *sort=NULL, *v=NULL;
  
  if (!ATmatch(sorts,"ins(<str>,<term>)",&sort,&sorts))
     return;
  makepushargsvarsrec(t1,t2,sorts);
  
  v=getvarname("v",emv_term);
  *t1=ATmake("ins(t(<str>,emt),<term>)",v,*t1);
  *t2=ATmake("ins(<str>,<str>,<term>)",v,sort,*t2);
  
}

void makepushargsvars(ATerm *t1,ATerm *t2, 
         char *var0, stacklisttype *stack)
 /* t1 contains push(var0,v1,..,vn,stackvar), t2 the list of variables
state,
     var0,v1,...,vn,stackvar*/
{ 
  ATerm t=NULL, v=NULL;
  
  t=ATmake("ins(t(<str>,emt),emt)",stack->stackvar);

v=ATmake("ins(<str>,<str>,emv)",stack->stackvar,stack->opns->stacksort);
 makepushargsvarsrec(&t,&v,stack->opns->sorts);
  *t1=ATmake("t(<str>,ins(t(<str>,emt),<term>))",stack->opns->push,var0,t);
  *t2=ATmake("ins(<str>,<str>,<term>)",var0,controlstate->elementsort,v);
  
}

static int matchsorts(ATerm p1,ATerm p2)
{ char *s1,*s2,*s3,*s4;
  
  if (ATmatch(p1,"ins(<str>,<str>,<term>)",&s1,&s2,&p1))
    { if (ATmatch(p2,"ins(<str>,<str>,<term>)",&s3,&s4,&p2))
       { /* fprintf(stderr,"STR %s %s\n",s2,s4); */
         if (strcmp(s2,s4)==0)
             return matchsorts(p1,p2);
           else return 0;
        }
       else return 0;
    }
   if (p2==emv_term)
      return 1;
   else return 0;
}

static stackoperations *find_suitable_stack_operations
           (ATerm parameters,stacklisttype *stacklist)
{ /* ATfprintf(stderr,"Find suitable stack operations %t\n",parameters); */
  if (stacklist==NULL) 
   { /* fprintf(stderr,"\nNOTOK\n"); */
     return NULL; }
  if (matchsorts(parameters, stacklist->parameterlist))
   { /* fprintf(stderr,"\nOK\n"); */
     return stacklist->opns; }
  else return
find_suitable_stack_operations(parameters,stacklist->next);
}

stacklisttype *new_stack(ATerm parameterlist,
       specificationbasictype *spec, int regular,arglist *pCRLprocs)
{ ATerm walker=NULL, tempsorts=NULL;
  ATerm t1=NULL, t2=NULL, t3=NULL;
  char *string1=NULL, *string2=NULL, *string3=NULL;
  char *s1=NULL, *s2=NULL, *var0=NULL; char* s3;
  stacklisttype *stack;
  int no_of_states=0,i=0;
  arglist *last;

 
  for(no_of_states=0 ; pCRLprocs!=NULL ; pCRLprocs=pCRLprocs->next) {
    no_of_states++;
    last = pCRLprocs;
  }

  s3 = ( (statenames && objectdata[last->n].objectname->s) ?
	 objectdata[last->n].objectname->s : "s");
  
  stack=malloc(sizeof(stacklisttype));
  if (stack==NULL)
     rg_error("Cannot malloc stackdata",NULL);
  stack->parameterlist=NULL;
  ATprotect(&stack->parameterlist);
  stack->parameterlist=parameterlist;
  stack->stackvar=fresh_name(s3);

  insertvariablename(stack->stackvar);
  stack->no_of_states=no_of_states;
  stack->booleanStateVariables=ATempty;
  ATprotect((ATerm *)&stack->booleanStateVariables);
  if ((binary==1) && (oldstate==0))
  { i=upperpowerof2(no_of_states);
    for( ; i>0 ; i--)
    { char *name=fresh_name("bst");
      insertvariablename(name);
      stack->booleanStateVariables=
           ATinsert(stack->booleanStateVariables,ATmake("<str>",name));
    }
  }
  stack->next=stacklist;
  
  if (regular)
     stack->opns=NULL;
  else  
  {
    stack->opns=find_suitable_stack_operations(parameterlist,stacklist);
    stacklist=stack;

    if (stack->opns==NULL)
     {
       stack->opns=malloc(sizeof(stackoperations));
       if (stack->opns==NULL)
          rg_error("Cannot malloc stackoperations",NULL);
       if (to_file) fprintf(outfile,"\n");

       stack->opns->sorts=NULL;
       ATprotect(&(stack->opns->sorts));
       stack->opns->get=NULL;
       ATprotect(&(stack->opns->get));
       stack->opns->stacksort=makenewsort("Stack",1,spec);
       stack->opns->sorts=ATmake("ems");
       stack->opns->get=ATmake("ems");
       for(walker=parameterlist ; 
            ATmatch(walker,"ins(<str>,<str>,<term>)",
              &string1,&string2,&walker) ; )
      {
        stack->opns->sorts=ATmake("ins(<str>,<term>)",
                      string2,stack->opns->sorts); 
        string3=new_string("get")->s;
        string3=strcat(string3,string1);
        string3=makenewobject(string3,
            ATmake("ins(<str>,ems)",
                stack->opns->stacksort),string2,map,spec,0);

        stack->opns->get=ATmake(
                  "ins(<str>,<term>)",string3,stack->opns->get); 
      }
    /* reverse stack->get */
    walker=stack->opns->get;
    for (stack->opns->get=ATmake("ems"); 
             (ATmatch(walker,"ins(<str>,<term>)",&string1,&walker));

    stack->opns->get=ATmake("ins(<str>,<term>)",
            string1,stack->opns->get)){}; 
    /* construct the sort of the push operator */
    walker=stack->opns->sorts;
    for (tempsorts=ATmake("ins(<str>,ems)", stack->opns->stacksort); 
         (ATmatch(walker,"ins(<str>,<term>)",&string1,&walker));
               tempsorts=ATmake("ins(<str>,<term>)",string1,tempsorts)){};
    if (oldstate)
    { tempsorts=ATmake("ins(<str>,<term>)",
               controlstate->elementsort,tempsorts);
    }
    else if (binary)
    { ATerror("Cannot combine stacks with binary\n");
    }
    else /* enumerated type */
    { ATerror("Cannot combine stacks with an enumerated type\n");
    }
    /* reverse stack->sorts */
    walker=stack->opns->sorts;
    for (stack->opns->sorts=ATmake("ems"); 
         (ATmatch(walker,"ins(<str>,<term>)",&string1,&walker));

    stack->opns->sorts=ATmake("ins(<str>,<term>)",string1,stack->opns->sorts)){}; 
    /* XX insert equations for get mappings */

    if (oldstate)
    { stack->opns->getstate=
        makenewobject("getstate",ATmake("ins(<str>,ems)",
	   stack->opns->stacksort), controlstate->elementsort,map,spec,0);
    }
    else if (binary)
    { ATerror("Cannot combine stacks with binary\n");
    }
    else /* enumerated type */
    { ATerror("Cannot combine stacks with an enumerated type\n");
    }

    stack->opns->push=makenewobject("push",tempsorts,stack->opns->stacksort,func,spec,0);
    stack->opns->emptystack=makenewobject("emptystack",
          ATmake("ems"),stack->opns->stacksort,func,spec,0);

stack->opns->empty=makenewobject("isempty",ATmake("ins(<str>,ems)",stack->opns->stacksort),
                           "Bool",map,spec,0);
  /* insert equations for isempty */

stack->opns->pop=makenewobject("pop",ATmake("ins(<str>,ems)",stack->opns->stacksort),
                        stack->opns->stacksort,map,spec,0);
  /* insert equations for pop */
  /* Generate equations for get, pop and isempty */
  var0=getvarname("svr",emv_term);
  makepushargsvars(&t1,&t2,var0,stack);
  declare_equation_variables(t2);
  newequation(

ATmake("t(<str>,ins(t(<str>,emt),emt))",stack->opns->empty,stack->opns->emptystack),
      ATmake("t(<str>,emt)","T"),spec);
  /* t1 contains push(var0,v1,..,vn,stackvar), t2 the list of variables
state,
     var0,v1,...,vn,stackvar*/
  newequation(
      ATmake("t(<str>,ins(<term>,emt))",stack->opns->empty,t1),
      ATmake("t(<str>,emt)","F"),spec);
  newequation(
      ATmake("t(<str>,ins(<term>,emt))",stack->opns->pop,t1),
      ATmake("t(<str>,emt)",stack->stackvar),spec);
  newequation(
      ATmake("t(<str>,ins(<term>,emt))",stack->opns->getstate,t1),
     ATmake("t(<str>,emt)",var0),spec);
  ATmatch(t2,"ins(<str>,<str>,<term>)",&dummystring,&dummystring,&t3);
  for(walker=stack->opns->get;
       (ATmatch(walker,"ins(<str>,<term>)",&s1,&walker)) ; )
      {   ATmatch(t3,"ins(<str>,<str>,<term>)",&s2,&dummystring,&t3);
        newequation(
            ATmake("t(<str>,ins(<term>,emt))",s1,t1),
            ATmake("t(<str>,emt)",s2),spec);
      }
    end_equation_section();

    }
  }
  
  return stack;
}

ATerm getvar(char *name,stacklisttype *stack)
{ ATerm walker=NULL, t1=NULL;
  char *string1=NULL,*string2=NULL;
  t1=stack->opns->get;
  for(walker=stack->parameterlist ;
        ATmatch(walker,"ins(<str>,<str>,<term>)",
                 &string1,&dummystring,&walker) ; )
    { if (!ATmatch(t1,"ins(<str>,<term>)",&string2,&t1))
          rg_error("incompatible list lengths",NULL);
      if (strequal(string1,name))
          return
ATmake("t(<str>,ins(t(<str>,emt),emt))",string2,stack->stackvar); }
  return ATmake("t(<str>,emt)",name);
}

ATerm sumlist=NULL;

static ATerm processencoding_rec(int i)
{ ATerm t3=NULL;
  
  if (i==1) 
     t3=ATmake("t(<str>,emt))",controlstate->one);
  else
   {if ((i % 2)==0)
       t3=ATmake("t(<str>,ins(<term>,emt))",controlstate->x2plus0,
              processencoding_rec(i/2));
    else
       t3=ATmake("t(<str>,ins(<term>,emt))",controlstate->x2plus1,
               processencoding_rec((i-1)/2));
   }
  return t3;
}

static ATerm processencoding(int i,ATerm t,specificationbasictype *spec,
                                   stacklisttype *stack)
{
  if (oldstate)
  { return ATmake("ins(<term>,<term>)",processencoding_rec(i),t);
  }

  i=i-1; /* below we count from 0 instead from 1 as done in the 
            first version of the prover */

  if (binary==0)
  { arglist *l=NULL;
    enumeratedtype *e=NULL;
    e=create_enumeratedtype(stack->no_of_states,spec);
    l=e->elementnames;
    for( ; i>0 ; i--){l=l->next;}
    return ATmake("ins(t(<str>,emt),<term>)",objectdata[l->n].objectname,t); 
  }
  /* else a sequence of boolean values needs to be generated,
     representing the value i, when there are l->n elements */
  { 
    int k=upperpowerof2(stack->no_of_states);
    for( ; k>0 ; k--)
    { if ((i % 2)==0)
      { t=ATmake("ins(t(\"F\",emt),<term>)",t);
        i=i/2;
      }
      else 
      { t=ATmake("ins(t(\"T\",emt),<term>)",t);
        i=(i-1)/2;
      }
    }
    return t;  
  }
}

ATerm correctstatecond(int n, arglist *pCRLproc,
          stacklisttype *stack, int regular, specificationbasictype *spec)
{ 
  int i;
  ATerm t3=NULL;
 
  
  for(i=1 ; (pCRLproc->n!=n) ; pCRLproc=pCRLproc->next)
     { /* printf("pCRLproc: %d\n",pCRLproc->n); */
       i++; }
  /* i is the index of the current process */
  /* ATfprintf(stderr,"AAAA: %t %s %s\n",
        processencoding(i,ATmake("emt"),spec,stack),stack->stackvar,controlstate->eqelement); 

  fflush(stderr); */
  if ((oldstate))
  { if (regular)
        t3=ATmake(
            "t(<str>,ins(t(<str>,emt),<term>))",
            controlstate->eqelement,
            stack->stackvar,
            processencoding(i,ATmake("emt"),spec,stack));
    else          
       t3=ATmake(
            "t(<str>,ins(t(<str>,ins(t(<str>,emt),emt)),<term>))",
            controlstate->eqelement,
             stack->opns->getstate,
             stack->stackvar,
             processencoding(i,ATmake("emt"),spec,stack));
    return t3;
  } 
  if (binary==0) /* Here a state encoding using enumerated types
                    must be declared */
  { enumeratedtype *e=create_enumeratedtype(stack->no_of_states,spec); 
    if (regular)
        t3=ATmake(
            "t(<str>,ins(t(<str>,emt),<term>))",
            e->equality,
            stack->stackvar,
            processencoding(i,ATmake("emt"),spec,stack));
    else
       t3=ATmake(
            "t(<str>,ins(t(<str>,ins(t(<str>,emt),emt)),<term>))",
             e->equality,
             stack->opns->getstate,
             stack->stackvar,
             processencoding(i,ATmake("emt"),spec,stack));
    return t3;
  }
  /* in this case we must encode the condition using
     boolean variables */

  

  { ATermList vars=stack->booleanStateVariables;

    i=i-1; /* start counting from 0, instead from 1 */
    for(  ; !ATisEmpty(vars) ; vars=ATgetNext(vars))
    { if ((i % 2)==0)
      { if (t3==NULL)
            t3=ATmake("t(\"not\",ins(t(<term>,emt),emt))",ATgetFirst(vars));
        else t3=ATmake("t(\"and\",ins(t(\"not\",ins(t(<term>,emt),emt)),ins(<term>,emt)))",
                     ATgetFirst(vars),t3);
        i=i/2;
      }
      else
      { if (t3==NULL)
            t3=ATmake("t(<term>,emt)",ATgetFirst(vars));
        else t3=ATmake("t(\"and\",ins(t(<term>,emt),ins(<term>,emt)))",
                     ATgetFirst(vars),t3);
        i=(i-1)/2;
      }

    }
    assert(i==0);
  }
  return t3;
}

ATerm adapt_termlist_to_stack( ATerm tl, stacklisttype
                                     *stack,ATerm vars);

ATerm adapt_term_to_stack(ATerm t, stacklisttype *stack,
ATerm vars)
{ ATerm t1=NULL, t3=NULL;
  ATerm fname=NULL;
  
  if(ATmatch(t,"t(<term>,emt)",&fname))
    { if (occursin(fname,vars)!=NULL)
         t3=t;
      else t3=getvar(ATgetName(ATgetAFun(fname)),stack); }
  else
  if(ATmatch(t,"t(<term>,<term>)",&fname,&t1))
    t3=ATmake("t(<term>,<term>)",fname,
            adapt_termlist_to_stack(t1,stack,vars));
  else rg_error("Expect ATerm ",NULL);
  
  return t3;
}

ATerm adapt_termlist_to_stack(
            ATerm tl, stacklisttype *stack, ATerm vars)
{ ATerm t1=NULL, t2=NULL, t3=NULL;

  
  if(ATmatch(tl,"ins(<term>,<term>)",&t1,&t2))

t3=ATmake("ins(<term>,<term>)",adapt_term_to_stack(t1,stack,vars),
          adapt_termlist_to_stack(t2,stack,vars));
  else 
   { if(tl!=emt_term)
        rg_error("expect termlist(2)",NULL);
     else t3=tl; }

  
  return t3;
}

ATerm find(ATerm s, ATerm pars, ATerm args, 
               stacklisttype *stack,ATerm vars, 
               char *err_mes, int regular)
{ ATerm string1term=NULL, string2term=NULL;
  ATerm t=NULL, t3=NULL;
  
  
  if (pars==emv_term) 
   { string1term=occursin(s,stack->parameterlist);
     if (string1term==NULL)
        t3=ATmake("t(<term>,emt)",s); 
     else t3=uniqueterm(ATgetName(ATgetAFun(string1term)),err_mes);
   }
  else
  /* if (ATmatch(pars,"ins(<term>,<term>,<term>)",
                       &string1term,&string2term,&pars)) */
     { string1term=ATgetArgument(pars,0);
       string2term=ATgetArgument(pars,1);
       pars=ATgetArgument(pars,2);

       /* if (!ATmatch(args,"ins(<term>,<term>)", &t,&args)) */
       if (ATgetAFun(args)!=ins2_symbol)
          rg_error("parameters and arguments must match",NULL);
       t=ATgetArgument(args,0);
       args=ATgetArgument(args,1);
       if (s==string1term)
          { if (regular)
               t3=t;
            else
               t3=adapt_term_to_stack(t,stack,vars);
          }
       else t3=find(s,pars,args,stack,vars,err_mes,regular);
     }
  /* else 
   { 
     rg_error("(1) expect parameterlist",pars); } */
  /* ATfprintf(stderr,"FIND: %t\n",t3); */
  return t3;
}


ATerm findarguments(ATerm pars,ATerm parlist, 
           ATerm args, ATerm t2,
           stacklisttype *stack, ATerm vars, char *err_mes, int regular)
{ ATerm string1term=NULL, string2term=NULL;
  ATerm t=NULL,t1=NULL, t3=NULL;
  
  if (parlist==emv_term)
   { 
     t3=t2; }
  else 
     /* if (ATmatch(parlist,
        "ins(<term>,<term>,<term>)",
                 &string1term,&string2term,&parlist)) */
     { string1term=ATgetArgument(parlist,0);
       string2term=ATgetArgument(parlist,1);
       parlist=ATgetArgument(parlist,2);
       t=find(string1term,pars,args,stack,vars,err_mes,regular);
       if (t==NULL) 
          t3=NULL;
       else
        { t1=findarguments(pars,parlist,args,
                       t2,stack,vars,err_mes,regular);
          if (t1==NULL) 
             t3=NULL;
          /* else t3=ATmake("ins(<term>,<term>)",t,t1); */
          else t3=(ATerm)ATmakeAppl2(ins2_symbol,t,t1);
     }  }
    /* else rg_error("(1) expect parameterlist",pars); */
  
  /* ATfprintf(stderr,"FINDARG: %t\n",t3); */
  return t3;
}


ATerm push(int n,ATerm args,ATerm t2,
         stacklisttype *stack,
          arglist *pCRLprcs, ATerm vars, char *err_mes, 
          int regular,int singlestate,specificationbasictype *spec)
{ 
  int i;
  ATerm t=NULL, t3=NULL;
  
  t=findarguments(objectdata[n].parameters, 
            stack->parameterlist,args,t2,stack,vars,err_mes,regular);
  for(i=1 ; (pCRLprcs->n!=n) ; pCRLprcs=pCRLprcs->next)
     { i++; }
  if (regular)   
    { if (singlestate)
         t3=t;
      else 
         t3=processencoding(i,t,spec,stack); 
    }
  else
    { t3=ATmake("t(<str>,<term>)",
             stack->opns->push,processencoding(i,t,spec,stack)); }
  /* ATfprintf(stderr,"PUSH: %t\n\n",t3); */
  return t3;
}


ATerm make_procargs(
        ATerm t,stacklisttype *stack,arglist *pcrlprcs,
        ATerm vars,char *err_mes, int regular, int singlestate,
        specificationbasictype *spec)
{ /* t is a sequential composition of process variables */
  ATerm t1=NULL, t2=NULL, t3=NULL;
  ATerm result=NULL;
  char *string1=NULL;
  int n;

  
  if (ATmatch(t,"seq(name(<str>,<int>,<term>),<term>)",&string1,&n,&t1,&t2))
   { if (regular)
         rg_error("Process is not regular, as it has stacking vars",t);
     else    
     { if (objectdata[n].canterminate==1)
        { t3=make_procargs(t2,stack,pcrlprcs,
                        vars,err_mes,regular,singlestate,spec);
          if (t3==NULL) 
             result=NULL;
          else 
           { t3=push(n,t1,t3,stack,pcrlprcs,vars,err_mes,regular,singlestate,spec);
             if (t3==NULL) 
                result=NULL;
             else result=ATmake("ins(<term>,emt)",t3);
        }  }
       else 
        { t3=push(n,t1,ATmake(
               "ins(t(<str>,emt),emt)",stack->opns->emptystack),
                            stack,pcrlprcs,vars,err_mes,regular,singlestate,spec);
          if (t3==NULL) 
             result=NULL;
          else result=ATmake("ins(<term>,emt)",t3);
        }
   } }
  else
  if (ATmatch(t,"name(<str>,<int>,<term>)",&string1,&n,&t1))
   { if (regular)
       { result=push(n,t1,emt_term,
                       stack,pcrlprcs,vars,err_mes,regular,singlestate,spec);
       }
     else   
     { if (objectdata[n].canterminate==1)
         { t3=push(n,t1,ATmake(
                  "ins(t(<str>,ins(t(<str>,emt),emt)),emt)",
                     stack->opns->pop,stack->stackvar),
                            stack,pcrlprcs,vars,err_mes,regular,singlestate,spec);
           if (t3==NULL) 
              result=NULL;
           else result=ATmake("ins(<term>,emt)", t3);
         }
        else 
         { t3= push(n,t1,ATmake("ins(t(<str>,emt),emt)",
                  stack->opns->emptystack),stack,pcrlprcs,
                                 vars,err_mes,regular,singlestate,spec);
          if (t3==NULL) 
              result=NULL;
           else result=ATmake("ins(<term>,emt)",t3);
         }
   } }
  else rg_error("Expect seq or name",t);

  /* ATfprintf(stderr,"PROCARGS: %t\n\n",result); */
  return result;
}


ATerm occursin(ATerm name,ATerm pars)
{ 
  /* ATerm string1term=NULL, string2term=NULL; */

  /* for ( ; ATmatch(pars,"ins(<term>,<term>,<term>)",
                   &string1term,&string2term,&pars) ; ) */
  for ( ; (ATgetAFun(pars)==ins3_symbol) ; )
    { 
      if (ATgetArgument(pars,0)==name) 
                return ATgetArgument(pars,1); 
      pars=ATgetArgument(pars,2);
    }
  return NULL;
}

ATerm uniquetermrec( int n, int maxNesting);

ATerm uniquetermlistrec(arglist *arg, int maxNesting)
{ ATerm t1=NULL, t2=NULL, t3=NULL;
  if (arg==NULL) 
  { t3=emt_term;
  }
  else
  { 
    t1=uniquetermrec(arg->n,maxNesting);
    if (t1==NULL) 
    { t3=NULL;
    }
    else
    { t2=uniquetermlistrec(arg->next,maxNesting);
      if (t2==NULL) 
      { t3=NULL;
      }
      else 
      { t3=ATmake("ins(<term>,<term>)",t1,t2);
      }
    }
  } 
   
  return t3;
}

ATerm uniquetermrec(int n, int maxNesting)
{ int i;
  ATerm t=NULL;
  
  for (i=1 ; (i<=lastoccupiedobjectnumber) ; i++ )
      { if (((objectdata[i].object==map)||
               (objectdata[i].object==func))&&
            (objectdata[i].targetsort==n)&&
            (objectdata[i].args==NULL))
         { return ATmake("t(<str>,emt)",objectdata[i].objectname);
         }
      }
  
  /* No constant term has been found */

  if (maxNesting>=0)
  { for (i=1 ; (i<=lastoccupiedobjectnumber) ; i++ )
    { if (((objectdata[i].object==map)||
             (objectdata[i].object==func))&&
             (objectdata[i].targetsort==n))
      { t=uniquetermlistrec(objectdata[i].args,maxNesting-1);
        if (t!=NULL) 
        { return ATmake("t(<str>,<term>)",objectdata[i].objectname,t);
      }  }
    }
  }
  
  return NULL;
}

ATerm uniqueterm(char *sort, char *err_mes)
{ /* first try to locate a constant of required sort */
  int n,  maxNesting=0;
  ATerm t=NULL;
  n=existsort(sort);
  if (n<=0) 
   { sprintf(err_mes,"Sort `%s' does not exist",sort);
     return NULL; }
  for(maxNesting=1 ; maxNesting<200 ; maxNesting=maxNesting*2)
  { t=uniquetermrec(n,maxNesting);
    if (t!=NULL)
    { return t;
    }
  }

  if (t==NULL)
   { sprintf(err_mes,"Cannot find a term  of sort `%s'",
                    sortdata[n].sortname->s); }
  return t;
} 

static ATerm pushdummyrec(
     ATerm totalpars, ATerm pars, 
          stacklisttype *stack, char *err_mes, int regular)
{ char *sort=NULL;
  ATerm nameterm=NULL, t3=NULL;
  if (ATmatch(totalpars,"ins(<term>,<str>,<term>)",&nameterm,&sort,&totalpars))
    { if (occursin(nameterm,pars)!=NULL)
          t3=ATmake("ins(t(<term>,emt),<term>)",nameterm,
                  pushdummyrec(totalpars,pars,stack,err_mes,regular));
       else
        { ATerm temp=NULL;
          temp=uniqueterm(sort,err_mes);
          if (temp==NULL) return NULL;
          t3=ATmake("ins(<term>,<term>)",temp,
               pushdummyrec(totalpars,pars,stack,err_mes,regular));
        }
     }
  else
   if (regular)
      t3=emt_term;
   else t3=ATmake("ins(t(<str>,emt),emt)",
              stack->opns->emptystack);
  
  return t3;
}


static ATerm pushdummy(ATerm parameters,
      stacklisttype *stack,char *err_mes, int regular)
{ 
  return pushdummyrec(stack->parameterlist,
              parameters,stack,err_mes,regular);
}

ATerm make_initialstate(int n, 
       stacklisttype *stack,arglist *pcrlprcs, char *err_mes,
       int regular, int singlecontrolstate,specificationbasictype *spec)
{ ATerm t=NULL, t3=NULL;
  int i;
   
  for(i=1 ; (pcrlprcs->n!=n) ; pcrlprcs=pcrlprcs->next)
     { i++; }
  /* i is the index of the initial state */

  t=pushdummy(objectdata[n].parameters,stack,err_mes,regular);
  if (t==NULL) 
     t3=NULL;
  else 
   if (regular)
    { if (singlecontrolstate)
         t3=t;
      else 
         t3=processencoding(i,t,spec,stack); 
    }
   else t3=ATmake("ins(t(<str>,<term>),emt)",
        stack->opns->push,
        processencoding(i,t,spec,stack));
  return t3;
}

int proctermlistequal(ATerm t1,ATerm t2)
{ if (ATmatch(t1,"terminated")||ATmatch(t2,"terminated"))
   { if (ATmatch(t1,"terminated")&&ATmatch(t2,"terminated"))
        return 1;
     else return 0;
   }
  if (!ATmatch(t1,"i(<term>)",&t1))
     rg_error("Expect NTermList (1)",t1);
  if (!ATmatch(t2,"i(<term>)",&t2))
     rg_error("Expect NTermList (2)",t2);
  return termlistequal(t1,t2);
}


ATerm insert_summand(ATerm sumlist, ATerm variablelist, 
               char *actionname,
               ATerm actargs, ATerm procargs, ATerm condition,
               char *err_mes)
{ /* insert a new summand in sumlist; first try whether there is already
    a similar summand, such that this summand can be added with minimal
     increase of size. Otherwise add a fully new summand */
  ATerm newsumlist=NULL, variablelist1=NULL, actargs1=NULL, procargs1=NULL,
       condition1=NULL,procargs2=NULL,actargs2=NULL;
  char *actionname1=NULL;
  int isalreadyadded=0;
  for(newsumlist=ATmake("eml");
        (ATmatch(sumlist,"ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
         &variablelist1,&actionname1,&actargs1,
                    &procargs1,&condition1,&sumlist));)
  { ATerm renamingvariablelist=emv_term,
	  renamingtermlist=emt_term;
    if ((isalreadyadded==0)&&
        (strequal(actionname,actionname1))&&
	(variablesequal(variablelist,variablelist1, /* XXXXXXXXXXXX */
		    &renamingvariablelist,&renamingtermlist)))
    { if (ATmatch(procargs,"terminated"))
         procargs2=procargs;
      else
      { procargs2=ATmake("i(<term>)",
              substitute_datalist(renamingvariablelist,renamingtermlist,
		                      ATgetArgument(procargs,0)));
      }
      actargs2=substitute_datalist(renamingvariablelist,renamingtermlist,actargs); 
      if (termlistequal(actargs1,actargs2)&&
	  proctermlistequal(procargs1,procargs2))
       { isalreadyadded=1;
         if (existsor(err_mes)) 
            condition1=ATmake("t(<str>,ins(<term>,ins(<term>,emt)))",
		"or",
		condition1,
	        substitute_data(renamingvariablelist,renamingtermlist,condition));
         else 
         { return NULL;
         }
    }  }
    newsumlist=ATmake( 
            "ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
           variablelist1,actionname1,actargs1,procargs1,
                 condition1,newsumlist);
  }
  if (!isalreadyadded)
    newsumlist=ATmake(
       "ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
       variablelist,actionname,actargs,procargs,condition,newsumlist); 
  
  return newsumlist;
}

static int add_summands(int n, ATerm t, ATerm pars, 
                    arglist *pCRLprocs, stacklisttype *stack,
                    int canterminate, char *err_mes, int regular,
                    int singlestate, specificationbasictype *spec)
{ ATerm variablelist=NULL;
  ATerm actargs=NULL;
  ATerm procargs=NULL;
  ATerm condition1=NULL,condition2=NULL;
  char *actionname=NULL;
  ATerm t1=NULL,t2=NULL,t3=NULL;
  ATerm emptypops=NULL,notemptypops=NULL;
  int m=0, n3=0;
  char *name=NULL, *sort=NULL;
  
  /* remove the sum operators */
  for( variablelist=emv_term;
       ATmatch(t,"sum(<str>,<str>,<term>)",&name,&sort,&t) ; )
       { variablelist=ATmake("ins(<str>,<str>,<term>)",
                  name,sort,variablelist);
       }
  
  /* translate the condition */       
  if (ATmatch(t,"cond(<term>,<term>,delta)",&t,&condition1))
   { if (existsand(err_mes))
      { if (!((regular)&&(singlestate)))
          condition1=ATmake(
             "t(<str>,ins(<term>, ins(<term>,emt)))","and",
             correctstatecond(n,pCRLprocs,stack,regular,spec),
             ((regular)?condition1:      
           adapt_term_to_stack(condition1,stack,variablelist)));
      }
     else { 
            
            return 0; }
   }
  else 
   { if ((regular)&&(singlestate))
        condition1=ATmake("t(<str>,emt)","T");
     else 
        condition1=correctstatecond(n,pCRLprocs,stack,regular,spec);
   }

  if debug ATfprintf(stderr,"CONDITION ADD %t\n",condition1);


  if (ATmatch(t,"delta"))
   { n3=1; }
  else if (ATmatch(t,"seq(<term>,<term>)",&t1,&t2))
   { /* only one summand is needed */
     if (ATmatch(t1,"delta")) 
        n3=1;
     else
      {if (ATmatch(t1,"tau"))
             { actionname="tau";
               actargs=emt_term; }
       else if
            (!ATmatch(t1,"name(<str>,<int>,<term>)",
                               &actionname,&m,&actargs))
                 rg_error("Expect an action here",t1);
                 
       t3=make_procargs(t2,stack,
                pCRLprocs,variablelist,err_mes,regular,singlestate,spec);
                
      if (t3==NULL) 
          n3=0;
       else 
        { procargs=ATmake("i(<term>)",t3);
          if (!regular)
            { actargs=adapt_termlist_to_stack(
                        actargs,stack,variablelist);          
            }            
          sumlist=insert_summand(sumlist,
                   variablelist,actionname,actargs,procargs,
                             condition1,err_mes);
          if (sumlist==NULL)
             n3=0;
          else n3=1;
    } } }
  else 
  if (regular)
     { /* For regular processes, we assume
          that processes do not terminate */
        sprintf(err_mes,
            "Cannot transform terminating regular processes");  
        n3=0;  
     }
  else   
     { /* in this case we have two possibilities: the process
          can or cannot terminate after the action. So, we must
          generate two conditions. For regular processes, we assume
          that processes do not terminate */
       /* first we generate the non terminating summands */

       if (ATmatch(t,"delta")) 
          { 
            return 1;}
       if (ATmatch(t,"tau"))
             { actionname="tau";
               actargs=emt_term; }
       else if
         (!ATmatch(t,"name(<str>,<int>,<term>)",
                       &actionname,&m,&actargs))
            rg_error("Expect an action here",t);
            
       if (canterminate==1)
         { 
           emptypops=ATmake(
             "t(<str>,ins(t(<str>,ins(t(<str>,emt),emt)),emt))",
                 stack->opns->empty,stack->opns->pop,stack->stackvar);


          notemptypops=ATmake(
                       "t(<str>,ins(<term>,emt))","not",emptypops);
          if (!existsnot(err_mes))
           { 
                 
                 return 0; }
          else if (!existsand(err_mes)) 
           { 
                 
                 return 0; }
          else
             condition2=ATmake(
                     "t(<str>,ins(<term>, ins(<term>,emt)))",
                   "and",
                   notemptypops,
                   condition1); }
       else condition2=condition1;
       actargs=adapt_termlist_to_stack(actargs,
                     stack,variablelist);
       procargs=ATmake(
                 "i(ins(t(<str>,ins(t(<str>,emt),emt)),emt))",
                      stack->opns->pop,stack->stackvar);

            sumlist=insert_summand(sumlist,
                    variablelist,actionname,actargs,procargs,
                             condition2,err_mes);
       if (sumlist==NULL)
        { 
          
          return 0; }
       else n3=1;

       if (canterminate==1)
       { if (existsand(err_mes))
            condition2=ATmake("t(<str>,ins(<term>, ins(<term>,emt)))",
                "and",
                   emptypops,
                   condition1); 
         else { 
                return 0; }

         sumlist=insert_summand(sumlist,variablelist,
                  actionname,actargs,
                         ATmake("terminated"),condition2,err_mes); 
         if (sumlist==NULL)
            n3=0;
         else n3=1;
        }
     }
 
  return n3;
}


static int collectsumlistterm(int n, ATerm body, 
           ATerm pars, stacklisttype *stack,int canterminate,
           char *err_mes, int regular,int singlestate,
           specificationbasictype *spec)
{ ATerm t1=NULL, t2=NULL;
  int result=1;
  
  if debug  ATfprintf(stdout,"Collectsumlist: %s = %t\n",
        objectdata[n].objectname,objectdata[n].processbody); 
  if (ATmatch(body,"alt(<term>,<term>)",&t1,&t2))
     { if (!collectsumlistterm(n,t1,pars,stack,
                 canterminate,err_mes,regular,singlestate,spec))
             result=0;
       else
       if (!collectsumlistterm(n,t2,pars,stack,
                          canterminate,err_mes,regular,singlestate,spec))
             result=0;
       else
       result=1; }
  else 
   { if (add_summands( n, body,
           pars,pCRLprocs,stack,canterminate,err_mes,regular,singlestate,spec))
        result=1; 
     else result=0; }
     
  return result;
}

ATerm collectsumlist(arglist *pCRLprocs, ATerm pars, 
            stacklisttype *stack,int canterminate, 
            char *err_mes,int regular, int singlestate,specificationbasictype *spec)
{ arglist *walker=NULL;
  
  sumlist=eml_term;
  

  for(walker=pCRLprocs ; (walker!=NULL) ; walker=walker->next)
    { if (!collectsumlistterm(walker->n,
          objectdata[walker->n].processbody,pars,stack,
         (canterminate&&objectdata[walker->n].canterminate),err_mes,
                 regular,singlestate,spec))
       { 
         return NULL;}}
  if (debug) ATfprintf(stderr,"Collected sums %t\n",sumlist);

  
  return sumlist;
}


/**************** Cluster Actions **********************************/


static enumeratedtype *create_enumeratedtype
                (int n,specificationbasictype *spec)
{ enumeratedtype *w=NULL;
  char new_name[100];
  char *tempname;
  int j=0;
  for(w=enumeratedtypelist; ((w!=NULL)&&(w->size!=n));
                w=w->next){};
  if (w==NULL)
   { w=malloc(sizeof(enumeratedtype));
     w->size=n;
     if (n==2)
      { w->sortnumber=existsort("Bool"); 
        w->elementnames=
              new_arglist(existsobject("T",NULL),
              new_arglist(existsobject("F",NULL),NULL));
	w->equality="eq";
	if (!existseq(existsort("Bool"),scratch1))
	{ makenewobject("eq",ATmake("ins(\"Bool\",ins(\"Bool\",ems))"),
	                 "Bool",map,spec,1);
          { /* Generate equations */
            arglist *l1=NULL, *l2=NULL;
            char *v=NULL;
            declare_equation_variables(ATmake("emv"));
            newequation(ATmake("t(\"eq\",ins(t(\"T\",emt),ins(t(\"T\",emt),emt)))"),
		ATmake("t(\"T\",emt)"),spec);
            newequation(ATmake("t(\"eq\",ins(t(\"F\",emt),ins(t(\"T\",emt),emt)))"),
		ATmake("t(\"F\",emt)"),spec);
            newequation(ATmake("t(\"eq\",ins(t(\"T\",emt),ins(t(\"F\",emt),emt)))"),
		ATmake("t(\"F\",emt)"),spec);
            newequation(ATmake("t(\"eq\",ins(t(\"F\",emt),ins(t(\"F\",emt),emt)))"),
		ATmake("t(\"T\",emt)"),spec);
	    end_equation_section();
	  }
        }
      }
     else 
      { sprintf(new_name,"Enum%d",n);
        w->sortnumber=existsort(makenewsort(fresh_name(new_name),1,spec)); 
        w->elementnames=NULL;
        w->equality="eq";
        /* enumeratedtypes[i].elements=ATmake("ems"); */
        for(j=0 ; (j<n) ; j++)
         { /* Maak hier een naamlijst van sort elementen. */
           sprintf(new_name,"e%d-%d",j,n);
           tempname=makenewobject(fresh_name(new_name),ATmake("ems"),
                       sortdata[w->sortnumber].sortname->s,func,spec,0);
                                
           w->elementnames=new_arglist(
                existsobject(tempname,NULL),w->elementnames);
         }
        makenewobject("eq",ATmake("ins(<str>,ins(<str>,ems))",
               sortdata[w->sortnumber].sortname->s,sortdata[w->sortnumber].sortname->s),
                       "Bool",map,spec,1);

        { /* Generate equations */
          arglist *l1=NULL, *l2=NULL;
          char *v=NULL;
          v=getvarname("v_enum",emv_term);

          declare_equation_variables(ATmake("ins(<str>,<str>,emv)",
                   v,sortdata[w->sortnumber].sortname->s));
          newequation(ATmake("t(\"eq\",ins(t(<str>,emt),ins(t(<str>,emt),emt)))",v,v),
                 ATmake("t(\"T\",emt)"),spec);
          for(l1=w->elementnames ; l1!=NULL ; l1=l1->next)
          {  for(l2=w->elementnames ; l2!=NULL ; l2=l2->next)
             { if (l1->n!=l2->n)
                { newequation(ATmake("t(\"eq\",ins(t(<str>,emt),ins(t(<str>,emt),emt)))",
                     objectdata[l1->n].objectname->s,
                     objectdata[l2->n].objectname->s),ATmake("t(\"F\",emt)"),spec);
                }
             }
          }
          end_equation_section();
        }
      }
     w->functions=NULL;
     w->next=enumeratedtypelist;
     enumeratedtypelist=w;
   } 
  return w;
}

static char *find_case_function(enumeratedtype *e,char *sort)
{ int n=0;
  arglist *w=NULL;
  n=existsort(sort);
  for(w=e->functions; (w!=NULL); w=w->next)
    { if (objectdata[w->n].targetsort==n)
       return objectdata[w->n].objectname->s;
    };
  rg_error("Searching for nonexisting case function",NULL);
  return NULL;
}

static void declare_a_enumeratedtype(enumeratedtype *e, 
       char *functionname, 
       char *sortname, specificationbasictype *spec)
{ int j=0;
  
  char *v=NULL, *v1=NULL, *auxname1=NULL, *auxname2=NULL;
  ATerm auxvars=NULL, vars=NULL, args=NULL;
  ATerm xxxterm=NULL;
  arglist *w=NULL;

  xxxterm=emt_term;
  vars=emv_term;
  args=emt_term;
  v1=getvarname("x",emv_term);
  for(j=0; (j<e->size); j++)
   { v=getvarname("y",emv_term);
     vars=ATmake("ins(<str>,<str>,<term>)",v,sortname,vars);
     args=ATmake("ins(t(<str>,emt),<term>)",v,args);  
     xxxterm=ATmake("ins(t(<str>,emt),<term>)",v1,xxxterm);
   }

   /* I generate here an equation of the form
      C(e,x,x,x,...x)=x for a variable
        x. */
  v=getvarname("e",emv_term);
  declare_equation_variables(
          ATmake("ins(<str>,<str>,ins(<str>,<str>,emv))",
              v,sortdata[e->sortnumber].sortname->s,
              v1,sortname));
  newequation(
    ATmake("t(<str>,ins(t(<str>,emt),<term>))",
           functionname,
           v,
           xxxterm),
        ATmake("t(<str>,emt)",v1),spec);
  end_equation_section();

  declare_equation_variables(vars);
  auxvars=vars;

  for(w=e->elementnames; (w!=NULL) ; w=w->next)
    { 
      ATmatch(auxvars,"ins(<str>,<str>,<term>)",&auxname1,&auxname2,&auxvars);

      newequation(
           ATmake("t(<str>,ins(t(<str>,emt),<term>))",
               functionname,
               objectdata[w->n].objectname->s,
               args),
           ATmake("t(<str>,emt)",auxname1),spec);
    }
  end_equation_section(); 
  
}


static void create_function_on_enumeratedtype(int sort,
        enumeratedtype *e,specificationbasictype *spec)
{ arglist *w=NULL;
  char new_name[60];
  char *tempstring;
  ATerm args=NULL;
  int j=0;
  
  /* first find out whether the function exists already, in which
       case nothing need to be done */
  for(w=e->functions; ((w!=NULL) &&
          (objectdata[w->n].targetsort!=sort));
           w=w->next);
  if (w==NULL)
     { /* The function does not exist;
            Create a new function of enumeratedtype e, on sort */
       
       args=ATmake("ems");
       w=NULL;
       for(j=0; (j<e->size) ; j++)
          {
            args=ATmake("ins(<str>,<term>)",
                   sortdata[sort].sortname->s,args);
             w=new_arglist(sort,w);}
             /* ATfprintf(stderr,"CRF %s %t\n", 
                  sortdata[e->sortnumber].sortname,args); */
            args=ATmake("ins(<str>,<term>)",
                sortdata[e->sortnumber].sortname,args);
             w=new_arglist(e->sortnumber,w);

             sprintf(new_name,"C%d-%s",e->size,
                      sortdata[sort].sortname->s);   
             tempstring=makenewobject(fresh_name(new_name),
                        args,sortdata[sort].sortname->s,map,spec,0);
             e->functions=new_arglist(existsobject(tempstring,w),e->functions);
             release_totalarglist(w);
             declare_a_enumeratedtype(e,tempstring,
                      sortdata[sort].sortname->s,spec);
     }
  
}

typedef struct enumtype {
 
  enumeratedtype *etype;
  char *var;
  struct enumtype *next;
} enumtype;

enumtype *enumeratedtypes=NULL;

static enumtype *generate_enumerateddatatype(int n, char *action,
         arglist *fsorts, arglist *gsorts, 
         specificationbasictype *spec)
{ 
  
  enumtype *et=NULL;
  arglist *w=NULL;
  
  et=malloc(sizeof(enumtype));
  et->next=enumeratedtypes;
  enumeratedtypes=et;
  et->var= fresh_name("e");
  insertvariablename(et->var);
  
  et->etype=create_enumeratedtype(n,spec);
  
  for(w=fsorts; (w!=NULL); w=w->next)
     { create_function_on_enumeratedtype(w->n,
             et->etype,spec);
     }
     
  for(w=gsorts; (w!=NULL); w=w->next)
     { create_function_on_enumeratedtype(w->n,
             et->etype,spec);
     }

  create_function_on_enumeratedtype(existsort("Bool"),
             et->etype,spec);

  
  return (et);
}

/************** Merge summands using enumerated type ***********************/


static int count_summands(ATerm t)
{ ATerm t1=NULL, t2=NULL;
  if (ATmatch(t,"ins(<term>,<term>)",&t1,&t2))
     return count_summands(t2)+1;
  else return 0;
}


static int mergeoccursin(char **var, char *sort, ATerm v,
               ATerm *matchinglist,ATerm *pars, ATerm *args)
{ 
  char *var1=NULL, *sort1=NULL;
  ATerm auxmatchinglist=NULL;
  
  int result=0;

  
  /* First find out whether var:sort can be matched on a
  term in the matching list */
  
  /* first find out whether the variable occurs in the matching
     list, so, they can be joined */
  auxmatchinglist=emv_term;
  for( ; (ATmatch(*matchinglist,"ins(<str>,<str>,<term>)",
                         &var1,&sort1,matchinglist));)
    { if (streq(sort,sort1))
       { /* sorts match, so, we join the variables */
         result=1;
         if (!streq(*var,var1))
          { *pars=ATmake("ins(<str>,<str>,<term>)",
                        *var,sort,*pars);
            *args=ATmake("ins(t(<str>,emt),<term>)",
                        var1,*args); }
         /* copy remainder of matching list */
         for( ; (ATmatch(*matchinglist,"ins(<str>,<str>,<term>)",
                         &var1,&sort1,matchinglist));)
            {auxmatchinglist=ATmake("ins(<str>,<str>,<term>)",
                      var1,sort1,auxmatchinglist);}
       }
      else
       { auxmatchinglist=ATmake("ins(<str>,<str>,<term>)",
                      var1,sort1,auxmatchinglist);
       }
    }
  
  /* turn auxmatchinglist back in normal order, and put result
     in *matchinglist */
  for( ; (ATmatch(auxmatchinglist,"ins(<str>,<str>,<term>)",
                         &var1,&sort1,&auxmatchinglist));)
     { *matchinglist=ATmake("ins(<str>,<str>,<term>)",
                      var1,sort1,*matchinglist);}
  if (result==0)
   { /* in this case no matching argument has been found.
     So, we must find out whether *var is an allowed string.
     And if not, we must replace it by a new one. */
     for( ; (ATmatch(v,"ins(<str>,<str>,<term>)",&var1,&sort1,&v)) ; )
       { if (strequal(*var,var1))
          { *var=getvarname(*var,NULL);
            *var=fresh_name(*var);
            insertvariablename(*var);

/* HUH?     *matchinglist=ATmake("ins(<str>,<str>,<term>)",
                      *var,sort,*matchinglist); */
            *pars=ATmake("ins(<str>,<str>,<term>)",
                        var1,sort,*pars);
            *args=ATmake("ins(t(<str>,emt),<term>)",
                        *var,*args);
            v=emv_term;
          }
       }
   }

  return result;
}



static ATerm extend(ATerm c, ATerm cl)
{ ATerm head=NULL, tail=NULL;
  if (cl==emt_term)
    return emt_term;
  if (ATmatch(cl,"ins(<term>,<term>)",&head,&tail))
    return ATmake("ins(t(<str>,ins(<term>,ins(<term>,emt))),<term>)",
             "and",c,head,extend(c,tail));
  rg_error("Expect termlist (32)",cl);
  return NULL;

}

static ATerm extend_conditions(char *string1, char *string2,
       ATerm conditionlist,char *errmes)
{ ATerm newcondition=NULL;
  ATerm unique=NULL;
  
  if (!existseq(existsort(string2),errmes))
     return NULL;
  if (!existsand(errmes))
     return NULL;
  unique=uniqueterm(string2,errmes);
  if (unique==NULL)
     return NULL;
  newcondition=ATmake("t(<str>,ins(t(<str>,emt),ins(<term>,emt)))",
            "eq",string1,unique);
  /* ATfprintf(stderr,"NEWCONDITION: %t\nEXSEND%t\n\n",newcondition,
            extend(newcondition,conditionlist)); */
  return extend(newcondition,conditionlist);        
}   


static ATerm transform_matching_list(ATerm matchinglist,
         char *errmes)
{ char *s1=NULL, *s2=NULL;
  ATerm unique=NULL, aux1=NULL, aux2=NULL;
  if (matchinglist==emv_term)
     return ATmake("t(\"T\",emt)");
  if (ATmatch(matchinglist,"ins(<str>,<str>,<term>)",
           &s1,&s2,&matchinglist,errmes))
   { unique=uniqueterm(s2,errmes);
     if (unique==NULL)
        return NULL;
     aux1=transform_matching_list(matchinglist,errmes);
     if (aux1==NULL)
        return NULL;
     if (!existseq(existsort(s2),errmes))
        return NULL;
     aux2=ATmake("t(<str>,ins(t(<str>,emt),ins(<term>,emt)))",
            "eq",s1,unique);
     return ATmake("t(<str>,ins(<term>,ins(<term>,emt)))",
               "and",aux1,aux2);
   }
  rg_error("Erroneous matchinglist",matchinglist);
  return NULL;
}


static ATerm addcondition(ATerm matchinglist, 
      ATerm conditionlist, char *errmes)
{ ATerm extra_condition=NULL;
  extra_condition=transform_matching_list(matchinglist,errmes);
  if (extra_condition==NULL)
     return NULL;
  return ATmake("ins(<term>,<term>)",
          extra_condition,conditionlist);
}

static ATerm merge_var(ATerm v1, ATerm v2, 
        ATerm *renamings, ATerm *conditionlist,char *errmes)
{ 
  ATerm result=NULL;
  ATerm renamingargs=NULL, renamingpars=NULL;
  ATerm matchinglist=NULL;
  char *var=NULL, *sort=NULL;
  

  renamingargs=emt_term;
  renamingpars=emv_term;
  matchinglist=v2;

  /* If the sequence of sum variables is reversed,
   * the variables are merged in the same sequence for all
   * summands (due to a suggestion of Muck van Weerdenburg) */

  if (v2==emv_term)
  { ATerm v3=NULL;
    for(v3=emv_term ; (ATmatch(v1,"ins(<str>,<str>,<term>)",&var,&sort,&v1)) ; )
    { v3=ATmake("ins(<str>,<str>,<term>)",var,sort,v3);
    }
    v1=v3;
  }

  result=v2;
  for( ; (ATmatch(v1,"ins(<str>,<str>,<term>)",&var,&sort,&v1)) ; )
    { if (!mergeoccursin(&var,sort,v2,
            &matchinglist,&renamingpars,&renamingargs))
      { /* ATfprintf(stderr,"NOTOCCURSIN %s:%s CL %t\n",var,sort,*conditionlist);
*/
        result=ATmake("ins(<str>,<str>,<term>)",
                    var,sort,result);
        *conditionlist=extend_conditions(var,sort,*conditionlist,errmes);
        if (*conditionlist==NULL)
           return NULL; 
      }
    }
  /* ATfprintf(stderr,"Matchinglist: %t\nConditionlist %t\n",
                   matchinglist,*conditionlist); */
  *conditionlist=addcondition(matchinglist,*conditionlist,errmes);
  if (*conditionlist==NULL)
     return NULL;
  *renamings=ATmake("ins(<term>,<term>,<term>)",
               renamingpars,renamingargs,*renamings);
  
  return result;
}

static ATerm make_binary_sums(int n, char *enumtypename, 
       ATerm *condition, ATerm tail,char *errmes)
{ ATerm result=NULL;
  char *sumvar;
  
  assert(n>1);
  *condition=NULL;
 
  n=n-1;
  for(result=tail ; (n>0) ; n=n/2)
    { sumvar=getvarname("e",NULL);
      result=ATmake("ins(<str>,<str>,<term>)",sumvar,enumtypename,result);
      if ((n % 2)==0)
       { if ((*condition)==NULL)
          { /* if (!existsnot(errmes)) return NULL; */
            *condition=ATmake("t(<str>,emt)",sumvar);
          }
         else 
          { if (!existsand(errmes)) return NULL;
            /* if (!existsnot(errmes)) return NULL; */
            *condition=ATmake(
                "t(<str>,ins(t(<str>,emt),ins(<term>,emt)))",
                    "and",sumvar,*condition);
          }      
       }
     else
       { if ((*condition)==NULL)
          { *condition=ATmake("t(<str>,emt)","T");
          }
         else 
          { if (!existsor(errmes)) return NULL;
            /* if (!existsnot(errmes)) return NULL; */
            *condition=ATmake(
                "t(<str>,ins(t(<str>,emt),ins(<term>,emt)))",
                    "or",sumvar,*condition);
          }      
       }
    }
  return result;
}

static char *getcasefunction(char *thesort,enumtype *e)
{ 
  return find_case_function(e->etype, thesort);
}

static ATerm construct_binary_case_tree_rec(
         int n, ATerm sums, ATerm *terms, char *termsort,
         enumtype *e, char *errmes)
{ ATerm t=NULL,t1=NULL;
  char *casevar,*sort;

  assert(*terms!=emt_term);

  if (n<=0)
   { if (!ATmatch(*terms,"ins(<term>,<term>)",
            &t,terms))
        rg_error("Expect termlist",*terms); 
     return t;
   }

  if (!ATmatch(sums,"ins(<str>,<str>,<term>)",
                &casevar,&sort,&sums))
   { rg_error("Expect sumlist",sums); }
  t=construct_binary_case_tree_rec(n / 2,sums,terms,termsort,e,errmes);
  if (t==NULL) return NULL;

  if (*terms==emt_term)
   { return t; }
  else 
   { t1=construct_binary_case_tree_rec(n / 2,sums,terms,termsort,e,errmes);
     if (t1==NULL) return NULL;
     if (ATisEqual(t,t1)) 
        return t;
     return ATmake("t(<str>,ins(t(<str>,emt),ins(<term>,ins(<term>,emt))))",
              getcasefunction(termsort,e),casevar,t,t1);
   }
}

static ATerm construct_binary_case_tree(
     int n, ATerm sums, ATerm terms, char *termsort, enumtype *e,char *errmes)
{ 
  return construct_binary_case_tree_rec(n-1,sums,&terms,termsort,e,errmes);
}

static int collect_sum_arg_arg_cond(
     enumtype *e,int n,ATerm sumlist,
     arglist *fsorts, arglist *gsorts,
     ATerm *resultsum, ATerm *resultf,
     ATerm *resultg, ATerm *resultc,
     char *errmes)
{ 
  ATerm walker=NULL;
  ATerm sum=NULL, f=NULL, f_aux=NULL, g=NULL, c=NULL;
  ATerm auxresult=NULL, auxresult1=NULL; 
  char *action=NULL;
  int i=0, fcnt=0;
  ATerm rename_list=NULL, auxrename_list=NULL;
  ATerm auxpars=NULL, auxargs=NULL;
  ATerm equalterm=NULL;
  ATerm fffunct=NULL;
  ATerm conditionlist=NULL;
  ATerm binarysumcondition=NULL;
  arglist *ffunct=NULL;
  int equaluptillnow=1;
     /* rename list is a list of pairs of variable and
        term lists */

  auxresult=emv_term;
  rename_list=emv_term;
  conditionlist=emt_term;
  for(walker=sumlist; 
      ATmatch(walker,
        "ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
           &sum,&action,&f,&g,&c,&walker) ; )
  { auxresult=merge_var(sum,auxresult,&rename_list,&conditionlist,errmes); 
    /* ATfprintf(stderr,"CONDITIONLIST %t\n",conditionlist); */
    if (auxresult==NULL) 
       return 0;}
  
    if (binary)
      { *resultsum=make_binary_sums(n,sortdata[e->etype->sortnumber].sortname->s,
                          &binarysumcondition,auxresult,errmes);
        if ((*resultsum)==NULL) return 0;
      }
    else     
      *resultsum=ATmake("ins(<str>,<str>,<term>)",
             e->var,sortdata[e->etype->sortnumber].sortname->s,auxresult);

  /* Change the order of the rename list */
  for(auxrename_list=emv_term;
        (ATmatch(rename_list,"ins(<term>,<term>,<term>)",
              &auxpars,&auxargs,&rename_list)) ; )
    { auxrename_list=ATmake("ins(<term>,<term>,<term>)",
              auxpars,auxargs,auxrename_list); }
  rename_list=auxrename_list;


  /* we construct the resulting condition */
  auxresult=emt_term;
  auxrename_list=rename_list;
  equalterm=NULL;
  equaluptillnow=1;
  for(walker=sumlist; 
       ATmatch(walker,"ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
           &sum,&action,&f,&g,&c,&walker) ; )
   { if (!ATmatch(auxrename_list,"ins(<term>,<term>,<term>)",
               &auxpars,&auxargs,&auxrename_list))
       rg_error("Rename list too short (1)",auxrename_list); 
     auxresult1=substitute_data(auxpars,auxargs,c); 
     if (equalterm==NULL)
        equalterm=auxresult1;
     else 
       { if (equaluptillnow==1)
         equaluptillnow=(auxresult1==equalterm); }
     auxresult=ATmake("ins(<term>,<term>)", auxresult1,auxresult);
   }
   if (binary==1)
    { *resultc=construct_binary_case_tree(n,
                  *resultsum,auxresult,"Bool",e,errmes);
      if (*resultc==NULL) return 0;
      if (!existsand(errmes)) return 0;
      *resultc=ATmake(
         "t(<str>,ins(<term>,ins(<term>,emt)))",
              "and",binarysumcondition,*resultc);        
      if (*resultc==NULL) return 0;       
      *resultc=ATmake(
         "t(<str>,ins(<term>,ins(<term>,emt)))",
              "and",construct_binary_case_tree(n,
                     *resultsum,conditionlist,"Bool",e,errmes),*resultc);
    }
   else
    { 
      if (!existsand(errmes)) return 0;
      if (equaluptillnow==1)
        *resultc=ATmake(
           "t(<str>,ins(t(<str>,ins(t(<str>,emt),<term>)),ins(<term>,emt)))",
                "and",find_case_function(e->etype,"Bool"),
                     e->var,conditionlist,equalterm);        
      else 
      { 
        *resultc=ATmake("t(<str>,ins(t(<str>,emt),<term>))",
            find_case_function(e->etype,"Bool"),e->var,auxresult);
        *resultc=ATmake(
           "t(<str>,ins(t(<str>,ins(t(<str>,emt),<term>)),ins(<term>,emt)))",
                "and",find_case_function(e->etype,"Bool"),
                     e->var,conditionlist,*resultc);        
      }
    }
  
  /* now we construct the arguments of the invoked
     process, i.e. the new function g */
  *resultg=emt_term;
  fcnt=0;
  for(ffunct=gsorts ; (ffunct!=NULL) ; ffunct=ffunct->next)
    { 
      auxresult=emt_term;
      auxrename_list=rename_list;
      equalterm=NULL;
      equaluptillnow=1;
      for(walker=sumlist; 

      ATmatch(walker,"ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
             &sum,&action,&f,&g,&c,&walker) ; )
        { 
          if (!ATmatch(g,"i(<term>)",&g))
           { if (ATmatch(g,"terminated"))
              { rg_error("Cannot properly handle terminating processes",NULL); }
             else rg_error("Expect process argument",g);
           }
          if (!ATmatch(auxrename_list,"ins(<term>,<term>,<term>)",
                       &auxpars,&auxargs,&auxrename_list))
                 rg_error("Rename list too short (3)",auxrename_list);
          for(i=0;(i<fcnt); i++)
            { if (!ATmatch(g,"ins(<term>,<term>)",&f_aux,&g))
                 rg_error("expect termlist of sufficient length1",g); 
            }
          if (!ATmatch(g,"ins(<term>,<term>)",&g,&f_aux))
             rg_error("expect termlist with at least one term",g);
          
          auxresult1=substitute_data(auxpars,auxargs,g); 
          if (equalterm==NULL)
             equalterm=auxresult1;
          else 
           if (equaluptillnow==1)
              equaluptillnow=(equalterm==auxresult1);

          auxresult=ATmake("ins(<term>,<term>)",auxresult1,auxresult);
        }
     if (equaluptillnow)
         *resultg=ATmake("ins(<term>,<term>)",equalterm,*resultg);
     else
      { if (binary==0)
         { *resultg=ATmake("ins(t(<str>,ins(t(<str>,emt),<term>)),<term>)",
             find_case_function(e->etype,
                    sortdata[ffunct->n].sortname->s),
                       e->var,auxresult,*resultg);
         }
        else 
         { ATerm temp=construct_binary_case_tree(n,*resultsum,
                     auxresult,sortdata[ffunct->n].sortname->s,e,errmes);
           if (temp==NULL)
              return 0;
           *resultg=ATmake("ins(<term>,<term>)",temp,*resultg);
         }
      }
      fcnt++;
    }
  /* Now turn *resultg around */
  fffunct=*resultg;
  for( *resultg=emt_term ; (ATmatch(fffunct,"ins(<term>,<term>)",
                       &auxresult,&fffunct));)
     { *resultg=ATmake("ins(<term>,<term>)",auxresult,*resultg); }
  *resultg=ATmake("i(<term>)",*resultg);

  /* now we construct the arguments of the action */

  
  
  
  *resultf=emt_term;
  fcnt=0;
  for( ffunct=fsorts ; (ffunct!=NULL) ; ffunct=ffunct->next)
    { 
      auxresult=emt_term;
      auxrename_list=rename_list;
      equalterm=NULL;
      equaluptillnow=1;
      for(walker=sumlist; 
         ATmatch(walker,
           "ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
             &sum,&action,&f,&g,&c,&walker) ; )
        { 
	  if (!ATmatch(auxrename_list,"ins(<term>,<term>,<term>)",
                       &auxpars,&auxargs,&auxrename_list))
                 rg_error("Rename list too short (3)",auxrename_list);
          
          for(i=0;(i<fcnt); i++)
            { if (!ATmatch(f,"ins(<term>,<term>)",&f_aux,&f))
                 rg_error("expect termlist of sufficient length",f); 
            }
          if (!ATmatch(f,"ins(<term>,<term>)",&f,&f_aux))
             rg_error("Expect termlist with at least one term",f);
          
          auxresult1=substitute_data(auxpars,auxargs,f); 
          if (equalterm==NULL)
             equalterm=auxresult1;
          else 
           if (equaluptillnow==1)
              equaluptillnow=(equalterm==auxresult1);

          auxresult=ATmake("ins(<term>,<term>)",auxresult1,auxresult);
        }
     if (equaluptillnow)
         *resultf=ATmake("ins(<term>,<term>)",equalterm,*resultf);
     else
      if (binary==0)
       { *resultf=ATmake("ins(t(<str>,ins(t(<str>,emt),<term>)),<term>)",
             find_case_function(e->etype,
                    sortdata[ffunct->n].sortname->s),
                       e->var,auxresult,*resultf);
       }
      else
       { ATerm temp=construct_binary_case_tree(n,*resultsum,
                    auxresult,sortdata[ffunct->n].sortname->s,e,errmes);
         if (temp==NULL) return 0;
         *resultf=ATmake("ins(<term>,<term>)",temp,*resultf);
       }
      fcnt++;
    }
  /* Now turn *resultf around */
  fffunct=*resultf;
  for( *resultf=emt_term ; (ATmatch(fffunct,"ins(<term>,<term>)",
                       &auxresult,&fffunct));)
     { *resultf=ATmake("ins(<term>,<term>)",auxresult,*resultf); }

  return 1;
}

static ATerm cluster_actions(ATerm sums,ATerm pars,
                 specificationbasictype *spec, char *errmes)
{ 
  
  ATerm w1=NULL, w2=NULL, w3=NULL, result=NULL;
  ATerm t0=NULL, t1=NULL, t2=NULL, t3=NULL, t4=NULL;
  char  *action=NULL, *action1=NULL;
  arglist *sortlist1=NULL, *sortlist2=NULL;
  enumtype *enumeratedtype=NULL; 
  int n=0;
   /* We cluster first the summands with the action
      occurring in the first summand of sums. 
      These summands are first stored in w1. 
      The remaining summands are stored in w2. */
      
  
  
  result=eml_term;


  for( ; (sums!=eml_term) ;  )
    { 
      w1=eml_term;
      w2=eml_term;
      if (!ATmatch(sums,"ins(<term>,<term>)",&t0,&sums))
         rg_error("Expect sum list",sums);
      if (!ATmatch(t0,"smd(<term>,<str>,<term>,<term>,<term>)",
                   &t1,&action,&t2,&t3,&t4))
         rg_error("Expect summand (1)",t0);
      w1=ATmake("ins(<term>,<term>)",t0,w1);
      if (declarevariables(pars,scratch1)<=0)
         { fprintf(stderr,"%s\n",scratch1);
           rg_error("(1a) Problematic variables",pars);}
      if (declarevariables(t1,scratch1)<=0)
          { fprintf(stderr,"%s\n",scratch1);
            rg_error("(a) Problematic variables",t1);}
      if (!welltyped2(t2,&sortlist1,scratch1))
          { fprintf(stderr,"%s\n",scratch1);
            rg_error("Bad internal typing (a)",t2);}
      resetvariables(t1);
      resetvariables(pars);
      for(w3=sums; (w3!=ATmake("eml")) ; )
        { if (!ATmatch(w3,"ins(<term>,<term>)",&t0,&w3))
               rg_error("Expect sum list",w3);
          if (!ATmatch(t0,"smd(<term>,<str>,<term>,<term>,<term>)",
                   &t1,&action1,&t2,&t3,&t4))
               rg_error("Expect summand (2)",t0);
          if (strequal(action,action1))
           { 
             if (declarevariables(pars,scratch1)<=0)
              { fprintf(stderr,"%s\n",scratch1);
                rg_error("(1b) Problematic variables",pars);}
             if (declarevariables(t1,scratch1)<=0)
              { fprintf(stderr,"%s\n",scratch1);
                rg_error("(b) Problematic variables",t1);}
             if (!welltyped2(t2,&sortlist2,scratch1))
              { fprintf(stderr,"%s\n",scratch1);
                rg_error("Bad internal typing (b)",t2);}
             resetvariables(t1);
             resetvariables(pars);
             if (eqarglist(sortlist1,sortlist2))
                w1=ATmake("ins(<term>,<term>)",t0,w1);
             else w2=ATmake("ins(<term>,<term>)",t0,w2);
             release_totalarglist(sortlist2);
             sortlist2=NULL;
           }
          else w2=ATmake("ins(<term>,<term>)",t0,w2);
        }
      sums=w2;
      /* In w1 we now find all the summands labelled with
         `action'. We must now construct its clustered form. */
      n=count_summands(w1);
      /* ATfprintf(stderr,"COUNT: %d %s\n%t\n",n,action,w1); */
      if (n>1)
       { arglist *w;
         if (!make_arglist(pars,&w,scratch1,"Konijnenhol"))
            rg_error("Cannot create arglist",pars);

         if (binary==0)
          { enumeratedtype=generate_enumerateddatatype(n,action,
                   sortlist1,w,spec); }
         else 
          { enumeratedtype=generate_enumerateddatatype(2,action,
                   sortlist1,w,spec); }

         if (!collect_sum_arg_arg_cond(
                    enumeratedtype,n,w1,sortlist1,w,
                    &t1,&t2,&t3,&t4,errmes)) 
            return NULL;
         /* ATfprintf(stderr,"sum: %t\nactarg %t\nprocarg %t\ncond%t\n\n",
                    t1,t2,t3,t4); */
         result=ATmake(
                  "ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
                         t1,action,t2,t3,t4,result);
         release_totalarglist(w);
       }
      else 
       { ATmatch(w1,"ins(<term>,eml)",&t1);
         result=ATmake("ins(<term>,<term>)",t1,result);
       }
      sortlist1=NULL;
    }

  
  return result;
}

/**************** Cluster final result ******************************/

static ATerm clusterfinalresult(ATerm t3,specificationbasictype *spec,char *err_mes)
{ ATerm init=NULL, parameters=NULL, sums=NULL;
  if (!ATmatch(t3,"initprocspec(<term>,<term>,<term>)",
               &init, &parameters, &sums))
     rg_error("Expect initprocspec.", t3);

  sums=cluster_actions(sums,parameters,spec,err_mes);
  if (sums==NULL)
     return NULL;
  return ATmake("initprocspec(<term>,<term>,<term>)",
             init,parameters,sums);
}

/**************** GENERATE LPEpCRL **********************************/

/* The variable regular indicates that we are interested in generating 
   a LPO assuming the pCRL term under consideration is regular */

static ATerm generateLPEpCRL(int n, int canterminate,
              specificationbasictype *spec,char *err_mes,int regular)
/* A pair of initial state and linear process equation must be extracted
   from the underlying GNF */
{ ATerm parameters=NULL,sums=NULL,initial=NULL;
  stacklisttype *stack=NULL;
  int singlecontrolstate=0;
  ATerm t3=NULL;

  

  pCRLprocs=new_arglist(n,NULL);

  if (debug) ATfprintf(stderr,"Body: %t\n",objectdata[n].processbody);

  makepCRLprocs(objectdata[n].processbody);
  /* now pCRLprocs contains a list of all process id's in this
     pCRL process */
  /* collect the parameters, but assume that variables
     have a unique sort */
  if debug printarglist(pCRLprocs);
  if (pCRLprocs->next==NULL)
     singlecontrolstate=1;
  parameters=collectparameterlist();
  alphaconversion(n,parameters);
  if ((!singlecontrolstate)||(!regular)) 
         declare_control_state(spec,pCRLprocs);
  stack=new_stack(parameters,spec,regular,pCRLprocs);
  initial=make_initialstate(n,stack,pCRLprocs,err_mes,
                              regular,singlecontrolstate,spec);
  if (initial==NULL)
     t3=NULL;
  else 
   { 
     if debug printarglist(pCRLprocs);
     sums=collectsumlist(pCRLprocs,parameters,stack,
           (canterminate&&objectdata[n].canterminate),err_mes,regular,
               singlecontrolstate,spec);
     if (sums==NULL)
        t3=NULL;
     else
     { if (debug) ATfprintf(stderr,"SUMS1: %t\n",sums);
       if (regular)
        { if (!nocluster) /* XXXXXX */
           { if (oldstate)
             { sums=cluster_actions(sums,
                 ((!singlecontrolstate)?
                    ATmake("ins(<str>,<str>,<term>)",
                     stack->stackvar,controlstate->elementsort,
                          stack->parameterlist):
                          stack->parameterlist),spec,err_mes); 
                if (sums==NULL)
                return NULL;
             } else if (binary)
             { ATermList l=NULL;
               ATerm vars=stack->parameterlist;
               for(l=stack->booleanStateVariables; !ATisEmpty(l) ; l=ATgetNext(l))
               { vars=ATmake("ins(<str>,\"Bool\",<term>)",ATgetName(ATgetAFun(ATgetFirst(l))),vars);
               }
               sums=cluster_actions(sums,vars,spec,err_mes);
                if (sums==NULL)
                return NULL;
             } else /* enumerated type */
             { enumeratedtype *e=create_enumeratedtype(stack->no_of_states,spec);
               sums=cluster_actions(sums,
                 ((!singlecontrolstate)?
                    ATmake("ins(<str>,<str>,<term>)",
                     stack->stackvar,sortdata[e->sortnumber].sortname->s,
                          stack->parameterlist):
                          stack->parameterlist),spec,err_mes);
                if (sums==NULL)
                return NULL;

             }
             
           }
        }
       else
        { if (!nocluster)
           { sums=cluster_actions(sums,
               ATmake("ins(<str>,<str>,emv)",
                 stack->stackvar,stack->opns->stacksort),spec,err_mes); 
          if (sums==NULL)
            return NULL; }
        }
       if (debug) ATfprintf(stderr,"SUMS2: %t\n",sums);
       if (sums==NULL) 
         t3=NULL;
       else 
       { if (regular)
         { if (oldstate)
           { t3=ATmake("initprocspec(<term>,<term>,<term>)",
             initial,
             (singlecontrolstate?
                   stack->parameterlist:
                 ATmake("ins(<str>,<str>,<term>)", 
                   stack->stackvar,controlstate->elementsort,
                   stack->parameterlist)),sums); 
           } else if (binary)
           { ATermList l=NULL;
               ATerm vars=stack->parameterlist;
               for(l=stack->booleanStateVariables; !ATisEmpty(l) ; l=ATgetNext(l))
               { vars=ATmake("ins(<str>,\"Bool\",<term>)",ATgetName(ATgetAFun(ATgetFirst(l))),vars);
               }

             t3=ATmake("initprocspec(<term>,<term>,<term>)",
                              initial,vars,sums);
           } else /* normal enumerated type */
           { enumeratedtype *e=create_enumeratedtype(stack->no_of_states,spec);
             t3=ATmake("initprocspec(<term>,<term>,<term>)",
             initial,
             (singlecontrolstate?
                   stack->parameterlist:
                 ATmake("ins(<str>,<str>,<term>)",
                   stack->stackvar,sortdata[e->sortnumber].sortname->s,
                   stack->parameterlist)),sums);
           }
         }
         else
          t3=ATmake("initprocspec(<term>,<term>,<term>)",
           initial,
           ATmake("ins(<str>,<str>,emv)", 
                 stack->stackvar,stack->opns->stacksort),sums); 
       }
     }
   }
  
  return t3;
}


/**************** hiding *****************************************/

int isinset(ATerm action, ATerm set)
{ /* ATerm a=NULL;
     for ( ; (ATmatch(set,"ins(<str>,<term>)",&a,&set)) ; )
     { if (strequal(a,action)) return 1; } */
  for ( ; ATgetAFun(set)==ins2_symbol ; )
  { if (ATgetArgument(set,0)==action) return 1;
    set=ATgetArgument(set,1);
  }
  return 0;
}

ATerm hidecomposition(ATerm t1, ATerm t2)
{ /* t1 is a set of names, and t2 a set of summands */
  ATerm t3=NULL, init=NULL, pars=NULL;
  /* ATerm sums=NULL, actargs=NULL, procargs=NULL, cond=NULL; */
  ATerm action=NULL;
  
  
  if (!ATmatch(t2,"initprocspec(<term>,<term>,<term>)",&init,&pars,&t2))
     rg_error("Expect initprocspec (1)",t2);
  t3=ATmake("eml");
  /* for( ; (ATmatch(t2,"ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
          &sums,&action,&actargs,&procargs,&cond,&t2)) ; )
     { if (isinset(action,t1))
          t3=ATmake("ins(smd(<term>,<str>,emt,<term>,<term>),<term>)",
              sums,"tau",procargs,cond,t3);
       else t3=ATmake("ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
             sums,action,actargs,procargs,cond,t3);
     } */

  for( ; t2!=eml_term ; )
  {  ATerm smd=ATgetArgument(t2,0);
     action=ATgetArgument(smd,1);
     if (isinset(action,t1))
     { smd=(ATerm)ATmakeAppl5(smd_symbol,ATgetArgument(smd,0),
            tau_action, emt_term,ATgetArgument(smd,3),
            ATgetArgument(smd,4));
     }
     else
     { smd=(ATerm)ATmakeAppl5(smd_symbol,ATgetArgument(smd,0),action,
            ATgetArgument(smd,2),ATgetArgument(smd,3),
            ATgetArgument(smd,4));
     }
     t3=(ATerm)ATmakeAppl2(ins2_symbol,smd,t3);
     t2=ATgetArgument(t2,1);
  }
  t3=ATmake("initprocspec(<term>,<term>,<term>)",init,pars,t3);
  
  return t3;
}

/**************** encapsulation *************************************/

ATerm encapcomposition(ATerm t1, ATerm t2)
{  /* t1 is a set of names, and t2 a set of summands */
  ATerm t3=NULL, init=NULL, pars=NULL;
  /* ATerm sums=NULL, actargs=NULL, procargs=NULL, cond=NULL; */
  ATerm action=NULL;
  
  
  if (!ATmatch(t2,"initprocspec(<term>,<term>,<term>)",&init,&pars,&t2))
     rg_error("Expect initprocspec (2)",t2);
  t3=eml_term;
  /* for( ; (ATmatch(t2,"ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
          &sums,&action,&actargs,&procargs,&cond,&t2)) ; )
     { if (!isinset(action,t1))
          t3=ATmake("ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
              sums,action,actargs,procargs,cond,t3);
     } */
  for( ; t2!=eml_term ; )
  {  ATerm smd=ATgetArgument(t2,0);
     action=ATgetArgument(smd,1);
     if (!isinset(action,t1))
     { smd=(ATerm)ATmakeAppl5(smd_symbol,ATgetArgument(smd,0),action,
            ATgetArgument(smd,2),ATgetArgument(smd,3),
            ATgetArgument(smd,4));
       t3=(ATerm)ATmakeAppl2(ins2_symbol,smd,t3);
     }
     t2=ATgetArgument(t2,1);
  }
  t3=ATmake("initprocspec(<term>,<term>,<term>)",init,pars,t3);
  
  return t3;
}

/**************** renaming ******************************************/

char *rename_action(char *a,ATerm r)
{ char *a1=NULL, *a2=NULL;
  for ( ; (ATmatch(r,"ins(<str>,<str>,<term>)",&a1,&a2,&r)) ; )
     { if (strequal(a,a1)) 
        { 
          return a2; 
     }  } 
  return a;
}

ATerm renamecomposition(ATerm t1, ATerm t2)
{  /* t1 is a set of renamings, and t2 a set of summands */
  ATerm t3=NULL, init=NULL, pars=NULL;
  ATerm sums=NULL, actargs=NULL, procargs=NULL, cond=NULL;
  char *action=NULL;
  
  
  if (!ATmatch(t2,"initprocspec(<term>,<term>,<term>)",
                 &init,&pars,&t2))
     rg_error("Expect initprocspec (3)",t2);
  t3=ATmake("eml");
  for( ; (ATmatch(t2,"ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
          &sums,&action,&actargs,&procargs,&cond,&t2)) ; )
     { t3=ATmake("ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
              sums,rename_action(action,t1),actargs,procargs,cond,t3);
     }
  t3=ATmake("initprocspec(<term>,<term>,<term>)",init,pars,t3);
  
  return t3;

}

/**************** equalargs ****************************************/

static int autoapplysubstitution(ATerm *subargs, ATerm *subpars)
{ ATerm oldargs=NULL, newargs=NULL;
  
  oldargs=NULL;
  newargs=*subargs;  
  
  do
  { 
    oldargs=newargs;
    newargs=substitute_datalist(*subpars,oldargs,oldargs);
  }
  while (oldargs!=newargs);
  *subargs=newargs;

  return 1;
}


static int occursinvarandremove(char *s, ATerm *vl)
{ int result=0;
  char *s1=NULL, *s2=NULL;
  
  

  
  if (!ATmatch(*vl,"ins(<str>,<str>,<term>)",&s1,&s2,vl))
     result=0;
  else
   { if (strequal(s1,s))
      result=1; 
     else
      { result=occursinvarandremove(s,vl);
        *vl=ATmake("ins(<str>,<str>,<term>)",s1,s2,*vl);
      }
   }

  return result;
}

static int sumelimination(ATerm u1, ATerm u2,
                       ATerm *sumlist, ATerm *subargs,
                       ATerm *subpars)
{ char *s1=NULL;
  int result=0;
  
  

  if ((ATmatch(u1,"t(<str>,emt)",&s1)) &&
       (occursinvarandremove(s1,sumlist)))
      { result=1;
        *subargs=ATmake("ins(<term>,<term>)", u2,*subargs);  

*subpars=ATmake("ins(<str>,<str>,<term>)",s1,"dummy",*subpars);
      }
  else
  if ((ATmatch(u2,"t(<str>,emt)",&s1)) &&
       (occursinvarandremove(s1,sumlist)))
      { result=1;
        *subargs=ATmake("ins(<term>,<term>)", u1,*subargs);  

*subpars=ATmake("ins(<str>,<str>,<term>)",s1,"dummy",*subpars);
      }
  
  return result;
}

int equalargs (ATerm t1, ATerm t2, 
           ATerm *sumlist, ATerm *condition, 
           ATerm *subargs, ATerm *subpars, char *err_mes)
{  /* returns -1 if an error occurs. err_mes contains the reason
      returns 0 if types of terms or length do not match
      returns 1 if result is a valid ATerm  in t3, and condition defined.
      returns 2 if condition is not defined, but result is valid */

  ATerm u1= NULL, u2= NULL;
  char *culprit1=scratch1, *culprit2=scratch2;
  int n1=0,n2=0,n3=0;
  
  if ((t1==emt_term) && (t2==emt_term))
     n3=2;
  else
  if ((ATmatch (t1,"ins(<term>,<term>)",&u1,&t1))
    &&(ATmatch (t2,"ins(<term>,<term>)",&u2,&t2)))
   { if ((welltyped1(u1,&n1,culprit1)) && (welltyped1(u2,&n2,culprit2)))
     { if (n1==n2)
         { n1=equalargs (t1,t2,sumlist,condition,
                               subargs,subpars,err_mes);
           if (n1<=0) 
              n3=n1;
           else
           { /* check whether u1 or u2 is a variable, for which
                the sum elimantion theorem can be applied */
             if (sumelimination(u1,u2,sumlist,subargs,subpars)>0)
               n3=n1;
             else 
               if (!existseq(n2,err_mes))
                { 
                  n3=-1; 
                }
               else
                { t2=ATmake("t(<str>,ins(<term>,ins(<term>,emt)))","eq",u1,u2);
                  if (n1==2)
                   { *condition=t2;
                     n3=1; 
                   }
                  else
                   if (existsand(err_mes))
                    { *condition=ATmake("t(<str>,ins(<term>,ins(<term>,emt)))",
                                   "and",t2,*condition);
                      n3=1; }
                   else
                    { 
                      n3=-1;
                    }
                }
          } }
         else n3=0; /* different types  */ 
       }
      else 
       { if (!welltyped1(u1,&n1,culprit1)) 
                     ATfprintf(stderr,"U1: %s %t\n",culprit1,u1);
         if (!welltyped1(u2,&n2,culprit2)) 
                     ATfprintf(stderr,"U2: %s %t\n",culprit2,u2);
         rg_error("Typing wrong",NULL);
       }
   }
  return n3;
}

/* static int may_communicate (char *a1, specificationbasictype *spec)
 Replaced. This code is too inefficient. 
{ ATerm walker=NULL;
  char *act1=NULL, *act2=NULL, *act3=NULL;
  for (walker=spec->comms;
       (ATmatch (walker, "ins(<str>,<str>,<str>,<term>)",
            &act1,&act2,&act3, &walker));)
  {   if ((strequal (a1,act1))|| (strequal (a1,act2)))
	  { 
            return 1;}
  }
  return 0;
} */


/* static char *can_communicate (char *a1,char *a2,
           specificationbasictype *spec)
 Replace, as this is also too efficient, as turned out when
 studying the Woerden-Harmelen case study 
{ ATerm walker=NULL;
  char *act1=NULL, *act2=NULL, *act3=NULL;
  for (walker=spec->comms;
       (ATmatch (walker, "ins(<str>,<str>,<str>,<term>)",
            &act1,&act2,&act3, &walker));)
  {   if (((strequal (a1,act1))&& (strequal (a2,act2)))||
          ((strequal (a1,act2))&& (strequal (a2,act1))))
          { 
            return act3;}
  }
  return NULL;
} */

/**************** parallel composition ******************************/

ATerm maketerms(ATerm pars)
{ /* char *string1, *string2; */
  ATerm string1=NULL;
  ATerm t3=NULL;
  
  
  /* if (ATmatch(pars,"ins(<str>,<str>,<term>)",&string1,&string2,&pars))
     t3=ATmake("ins(t(<str>,emt),<term>)",string1,
                 maketerms(pars)); */
  if (ATgetAFun(pars)==ins3_symbol)
   { string1=ATgetArgument(pars,0);
     pars=ATgetArgument(pars,2);
     t3=(ATerm)ATmakeAppl2(t_symbol,string1,emt_term);
     t3=(ATerm)ATmakeAppl2(ins2_symbol,t3,maketerms(pars));
   }
  else t3=emt_term;
  
  return t3;
}

/********************** subtract **************************/
static ATerm subtract(ATerm varlist0, ATerm varlist1, ATerm varlist2)
{ /* deliver varlist1, where all variables occuring in varlist0 and
     varlist2 are removed */
  ATerm term1=NULL, term2=NULL;
  if (varlist1==emv_term)
     return varlist1;
  if (ATmatch(varlist1,"ins(<term>,<term>,<term>)",
                &term1,&term2,&varlist1))
   { if ((occursin(term1,varlist2)!=NULL)&&
         (occursin(term1,varlist0)!=NULL))
      { return subtract(varlist0,varlist1,varlist2);
      }
     return ATmake("ins(<term>,<term>,<term>)",
                term1,term2,subtract(varlist0,varlist1,varlist2));
   }
  rg_error("Expect variable list (17)",varlist1);
  return NULL;

}

/********************** construct renaming **************************/

ATerm construct_renaming(ATerm pars1, ATerm pars2, 
                ATerm *pars3, ATerm *pars4)
{ /* check whether the variables in pars2 are unique,
     wrt to those in pars1, and deliver:
     - in pars3 a list of renamed parameters pars2, such that
       pars3 is unique with respect to pars1;
     - in pars4 a list of parameters that need to be renamed;
     - as a return result, new values for the parameters in pars4.
       This allows using substitute_data(list) to rename
       action and process arguments and conditions to adapt
       to the new parameter names.
   */
     
  ATerm string1term=NULL, string2term=NULL; 
  char *string3=NULL;
  ATerm t=NULL, t1=NULL, t2=NULL;
  
  
  /* if (ATmatch(pars2,"ins(<term>,<term>,<term>)",
            &string1term,&string2term,&pars2)) */
     if (ATgetAFun(pars2)==ins3_symbol)
     { string1term=ATgetArgument(pars2,0);
       string2term=ATgetArgument(pars2,1);
       pars2=ATgetArgument(pars2,2);

       if (occursin(string1term,pars1)!=NULL)
        { string3=extended_fresh_name(
               ATgetName(ATgetAFun(string1term)),pars1); 
          insertvariablename(string3);
          t1=ATmake("ins(t(<str>,emt),<term>)",string3,
                  construct_renaming(pars1,pars2,&t,&t2));
          
          *pars4=ATmake("ins(<term>,<term>,<term>)",string1term,string2term,t2);
          *pars3=ATmake("ins(<str>,<term>,<term>)",string3,string2term,t);
      
        }
       else 
        { t1=construct_renaming(pars1,pars2,&t,pars4);
          *pars3=ATmake("ins(<term>,<term>,<term>)",
                            string1term,string2term,t);
        }

     }
  else
   { *pars3=emv_term;
     t1=emt_term; 
     *pars4=emv_term;
   }
  
  return t1;
}

/**************** calc length *************************************/

static int calc_length(ATerm t)
{ int l=0;
  
  for(l=0 ; (t!=eml_term) ; l++)
  { t=ATgetArgument(t,1); }
  return l;
}

/**************** parallel composition ******************************/

ATerm combinesumlist(
   ATerm t1, ATerm t2, ATerm par1, ATerm par2,ATerm par3,
   ATerm rename_list, specificationbasictype *spec, char *err_mes/* ,
   arglist *ignorelist*/)
/* this function does not work for terminating processes */


{ ATerm  t3=NULL,walker1=NULL, walker2=NULL;
  /* char *act1=NULL,*act2=NULL,*act3=NULL; */
  ATerm act1term=NULL, act2term=NULL, act3term=NULL;
  ATerm sums1=NULL,sums2=NULL,sums1new=NULL, sums2new=NULL,
        allsums=NULL,
        actargs1=NULL,actargs2=NULL,actargs1new=NULL,
        procargs1=NULL,procargs2=NULL,procargs3=NULL,
        condition1=NULL,condition2=NULL,condition3=NULL, condition4=NULL,
        rename1_list=NULL, rename2_list=NULL, allpars=NULL,
        oldallsums=NULL, sumel_args=NULL, sumel_pars=NULL,
        sums1renaming=NULL, sums2renaming=NULL;
  int n=0;
  /* YY */
  ATermTable sums2_hashtable=NULL; /* sums2_hashtable stores lists
                                      of summands of proc2, 
                                      per action label. */
  ATermList listwalker2=NULL;

  /* ATfprintf(stderr,"COUNT NO SUMMANDS IN 1: %d\n",calc_length(t1));
  ATfprintf(stderr,"COUNT NO SUMMANDS IN 2: %d\n",calc_length(t2)); */
  sums2_hashtable=ATtableCreate(64,90);
  
  allpars=conc_var(par1,par3);
  sumel_pars=emv_term;
  /* ATfprintf(stderr,"XX1: %t\n",t1);  
  ATfprintf(stderr,"XX2: %t\n",t2);  */
  t3=eml_term;
  /* first we enumerate the summands of t1 */

   /* for (walker1=t1;
          ATmatch(walker1,
              "ins(smd(<term>,<str>,<term>,i(<term>),<term>),<term>)",
          &sums1, &act1,&actargs1,&procargs1, &condition1,&walker1);) */

   for (walker1=t1; (walker1!=eml_term); 
                  walker1=ATgetArgument(walker1,1)) 
   { ATerm smd=NULL;

     smd=ATgetArgument(walker1,0);
     sums1=ATgetArgument(smd,0);
     act1term=ATgetArgument(smd,1);
     actargs1=ATgetArgument(smd,2);
     procargs1=ATgetArgument(smd,3);
     if (procargs1==terminated_term)
       { ATerror("Cannot deal with terminating processes\n"); }
     else procargs1=ATgetArgument(procargs1,0);  
     condition1=ATgetArgument(smd,4);
     
     
     rename1_list=construct_renaming(allpars,sums1,&sums1new,&sums1renaming);
     /* ATfprintf(stderr,"REN1: %t\n",rename1_list); */

     t3=ATmake("ins(smd(<term>,<term>,<term>,i(<term>),<term>),<term>)",
       sums1new,act1term,
       substitute_datalist(sums1renaming,rename1_list,actargs1),
       conc_tl(substitute_datalist(sums1renaming,rename1_list,procargs1),
               maketerms(par3)), 
       substitute_data(sums1renaming,rename1_list,condition1), t3);
   }

  /* second we enumerate the summands of t2; en passant, we
     enter the summands in sums2_hashtable */

  /* for (walker2=t2;
          ATmatch(walker2,
              "ins(smd(<term>,<str>,<term>,i(<term>),<term>),<term>)",
          &sums2, &act2,&actargs2,&procargs2, &condition2,&walker2);) */

   for (walker2=t2; walker2!=eml_term;
         walker2=ATgetArgument(walker2,1) )
   { /* YY */
     ATerm smd=NULL; 
     ATermList list=NULL;
     
     smd=ATgetArgument(walker2,0);
     act2term=ATgetArgument(smd,1);

     /* put this summand in the hashtable */
     list=(ATermList)ATtableGet(sums2_hashtable,act2term);
     if (list==NULL)
      { list=ATempty; }
     ATtablePut(sums2_hashtable,act2term,(ATerm)ATinsert(list,smd));
     
     /* act2=ATgetName(ATgetAFun(act2term)); */
     sums2=ATgetArgument(smd,0);
     actargs2=ATgetArgument(smd,2);
     procargs2=ATgetArgument(smd,3);
     if (procargs2==terminated_term)
       { ATerror("Cannot deal with terminating processes\n"); }
     else procargs2=ATgetArgument(procargs2,0);
     condition2=ATgetArgument(smd,4);
     
     
     rename2_list=construct_renaming(allpars,sums2,&sums2new,&sums2renaming);
     /* ATfprintf(stderr,"REN2 %t\n",rename2_list); */
     t3=ATmake("ins(smd(<term>,<term>,<term>,i(<term>),<term>),<term>)",
       sums2new,act2term,
       substitute_datalist(par2,rename_list,
                substitute_datalist(sums2renaming,rename2_list,actargs2)),
       conc_tl(maketerms(par1),
           substitute_datalist(par2,rename_list,
                substitute_datalist(sums2renaming,rename2_list,
                     /* ignore(ignorelist,*/ procargs2))), 
       substitute_data(par2,rename_list,
                substitute_data(sums2renaming,rename2_list,condition2)),t3);
   }

  /* thirdly we enumerate all communications */

  /* for (walker1=t1;
       ATmatch (walker1, 
               "ins(smd(<term>,<str>,<term>,i(<term>),<term>),<term>)",
         &sums1, &act1, &actargs1, &procargs1,
              &condition1, &walker1); ) */
   for (walker1=t1; (walker1!=eml_term);
                  walker1=ATgetArgument(walker1,1))
   { ATerm smd=NULL; 
     ATermList commlist=NULL;

     smd=ATgetArgument(walker1,0);
     act1term=ATgetArgument(smd,1);
     /* if (may_communicate(act1,spec)) replaced by more efficient code */
     
     commlist=(ATermList)ATtableGet(comm_hashtable,act1term);
     if (commlist!=NULL) /* so action act1 may communicate... */
   { /* act1=ATgetName(ATgetAFun(act1term)); */
     sums1=ATgetArgument(smd,0);
     actargs1=ATgetArgument(smd,2);
     procargs1=ATgetArgument(smd,3);
      if (procargs1==terminated_term)
       { ATerror("Cannot deal with terminating processes\n"); }
     else procargs1=ATgetArgument(procargs1,0);
     condition1=ATgetArgument(smd,4);


     rename1_list=construct_renaming(allpars,sums1,&sums1new,&sums1renaming);
     /* ATfprintf(stderr,"REN3 %t\n",rename1_list); */
     /* ATfprintf(stderr,"SUMS1 %t\nSUMS3 %t\nRename1_list %t\n\n",
                    sums1,sums1new,rename1_list);
      ATfprintf(stderr,"CONDITION1 %t\n",condition1); */

    actargs1 = substitute_datalist(sums1renaming,rename1_list,actargs1);
    procargs1=substitute_datalist(sums1renaming,rename1_list,procargs1);
    condition1= substitute_data(sums1renaming,rename1_list,condition1);
    /* ATfprintf(stderr,"NEW CONDITION1 %t\n\n",condition1); */

    /* Traverse the communications in commlist, and search,
       using sums2_hashtable only those summands in the second
       LPO with an action that must communicate */

    for( ; (!ATisEmpty(commlist)) ; commlist=ATgetNext(commlist))
    { /* YY */
      ATerm pair=NULL;
      pair=ATgetFirst(commlist);
      act2term=ATgetArgument(pair,0);
      act3term=ATgetArgument(pair,1);
      listwalker2=(ATermList)ATtableGet(sums2_hashtable,act2term);
      if (listwalker2==NULL)
       { listwalker2=ATempty; }
    
    /* for (walker2=t2;
       ATmatch (walker2,
            "ins(smd(<term>,<str>,<term>,i(<term>),<term>),<term>)",
        &sums2, &act2, &actargs2, &procargs2, &condition2, &walker2);) */

    for ( ;
       (!ATisEmpty(listwalker2)) ; listwalker2=ATgetNext(listwalker2) )
    { ATerm smd=NULL;
      smd=ATgetFirst(listwalker2);
      /* ATfprintf(stderr,"SMD: %t\n",smd); */
      /* act2=ATgetName(ATgetAFun(ATgetArgument(smd,1))); 
      
      act3=can_communicate (act1,act2,spec);
      if (act3!=NULL)
      { */
        sums2=ATgetArgument(smd,0);
        actargs2=ATgetArgument(smd,2);
        procargs2=ATgetArgument(smd,3);
        if (procargs2==terminated_term)
         { ATerror("Cannot deal with terminating processes\n"); }
        else procargs2=ATgetArgument(procargs2,0);
        condition2=ATgetArgument(smd,4); 

     /* ATfprintf(stderr,"SUMS2 %t\n",sums2);
     ATfprintf(stderr,"CONDITION2 %t\n",condition2); */
        rename2_list=construct_renaming(
               conc_var(sums1new,allpars),sums2,&sums2new,&sums2renaming);
                     /* ^-- omgewisseld */
        /* ATfprintf(stderr,"REN4 %t\n",rename2_list); */
        actargs2=substitute_datalist(par2,rename_list,
              substitute_datalist(sums2renaming,rename2_list,actargs2));
        procargs2=substitute_datalist(par2,rename_list,
              substitute_datalist(sums2renaming,rename2_list,
                     /* ignore(ignorelist,*/ procargs2));
        condition2=substitute_data(par2,rename_list,
              substitute_data(sums2renaming,rename2_list,condition2));

        allsums=conc_var(sums1new,sums2new);
        procargs3=conc_tl(procargs1,procargs2);
        if (existsand(err_mes))
           condition4=ATmake("t(<str>,ins(<term>, ins(<term>,emt)))",
                  "and", condition1,condition2);
        else return NULL;
       /* ATfprintf(stderr,"NEWCONDITION %t\n\n",condition4); */
        if (declarevariables(allpars,scratch1)<=0)
          { fprintf(stderr,"%s\n",scratch1);
            rg_error("(1) Problematic variables",par1);}
        if (declarevariables(allsums,scratch1)<=0)
          { fprintf(stderr,"%s\n",scratch1);
            rg_error("(3) Problematic variables",allsums);}
        oldallsums=allsums;
        sumel_args=emt_term;
        sumel_pars=emv_term;
        n=equalargs(actargs1,actargs2,
              &allsums,&condition3,&sumel_args,&sumel_pars,err_mes);
        if (n>0) 
           autoapplysubstitution(&sumel_args,&sumel_pars);
  

        resetvariables(oldallsums);
        resetvariables(par3);
        resetvariables(par1);
        if (n==-1) return NULL;
        /* if n==0 nothing needs to be done */
        condition4=substitute_data(sumel_pars,sumel_args,condition4);
        actargs1new=substitute_datalist(sumel_pars,sumel_args,actargs1);
        procargs3=substitute_datalist(sumel_pars,sumel_args,procargs3);
        if (n==1)
         { condition3=substitute_data(sumel_pars,sumel_args,condition3); 
           if (existsand(err_mes)) 
              condition4=ATmake("t(<str>,ins(<term>, ins(<term>,emt)))",
                "and",condition3, condition4);
           else
            { 
              return NULL;
            }

          t3=ATmake("ins(smd(<term>,<term>,<term>,i(<term>),<term>),<term>)",
             allsums, act3term, actargs1new, procargs3, condition4, t3);}
        else
        if (n==2)
         { 
           t3=ATmake("ins(smd(<term>,<term>,<term>,i(<term>),<term>),<term>)",
             allsums, act3term, actargs1new, procargs3, condition4, t3);}

      /* } */
    }}
  }}

  /* ATfprintf(stdout,"XX3: %t\n",t3);  */
  
  ATtableDestroy(sums2_hashtable);
  /* ATfprintf(stderr,"COUNT NO SUMMANDS: %d\n",calc_length(t3)); */
  return t3;
}

/* static ATerm ignore(arglist *ignorelist,ATerm list)
{ ATerm t=NULL;
  if (ignorelist==NULL)
   { if (list==emt_term)
        return list;
     else rg_error("Length error",list);
   }
  if (ATmatch(list,"ins(<term>,<term>)",&t,&list))
   { if (ignorelist->n==1)
       return ignore(ignorelist->next,list);
     else return ATmake("ins(<term>,<term>)",t,
                       ignore(ignorelist->next,list));
   }
  rg_error("Expect termlist (18)",list);
  return NULL;
} */

ATerm parallelcomposition(ATerm t1, ATerm t2, int canterminate,
       specificationbasictype *spec,char *err_mes)

{ 
  ATerm init1=NULL, pars1=NULL;
  ATerm init2=NULL, pars2=NULL;
  ATerm /* init3=NULL,*/ pars3=NULL;
  ATerm renaming=NULL;
  ATerm result=NULL;
  ATerm t=NULL, pars2renaming=NULL;
  
  /* arglist *ignore_list=NULL; */
  
  if (!ATmatch(t1,"initprocspec(<term>,<term>,<term>)",
               &init1,&pars1,&t1))
    rg_error("Expect initprocspec (4)",t1);
  if (!ATmatch(t2,"initprocspec(<term>,<term>,<term>)",
               &init2,&pars2,&t2))
    rg_error("Expect initprocspec (5)",t2);

  renaming=construct_renaming(pars1,pars2,&pars3,&pars2renaming); 


  fprintf(stderr,"Parallel composition is being translated... ");

  result=combinesumlist(t1,t2,pars1,pars2renaming,pars3,
                    renaming,spec,err_mes/* ,ignore_list*/);
  /* release_totalarglist(ignore_list); */
  
  if (result!=NULL)
     t=ATmake("initprocspec(<term>,<term>,<term>)",
           conc_tl(init1,init2),
           conc_var(pars1,pars3),
           result);
  fprintf(stderr,"done.\n"); 
  return t;
}

/**************** single name          ******************************/


ATerm namecomposition(int n, ATerm args, ATerm t)
{ ATerm init=NULL,pars=NULL,sums=NULL;
  ATerm t3=NULL;
  
  
  if (ATmatch(t,"initprocspec(<term>,<term>,<term>)",
          &init,&pars,&sums))
     { 
       /* ATfprintf(stderr,"args %t\npars %t\nsubs %t\n\n\n",
                   args,pars,
                   substitute_datalist(objectdata[n].parameters,args,init)); 
       ATfprintf(stderr,"ppars %t\ninitold %t\n\n",
                   objectdata[n].parameters,init);  */

       t3=ATmake("initprocspec(<term>,<term>,<term>)",
          substitute_datalist(objectdata[n].parameters,args,init),
          pars,sums); }
  else rg_error("Expect initprocspec (6)",t);
  
  return t3;
}


/**************** GENERATE LPEmCRL **********************************/


/*
 * The following functions encode the hide, encap and rename operators
 * as generalized parallel compositions, used in the multi LPO format.
 */

static ATerm encode_hide(ATerm hide_list,ATerm proc){
	ATermList op_list;
	op_list=ATmakeList0();
	for(;hide_list!=ems_term;hide_list=ATgetArgument(hide_list,1)){
		op_list=ATinsert(op_list,ATmake("pair(<term>,\"tau\")",ATgetArgument(hide_list,0)));
	}

	return ATmake("par(<term>,[],[],<term>,initprocspec(emt,emv,eml))",op_list,proc);
}

static ATerm encode_encap(ATerm encap_list,ATerm proc){
	ATermList op_list;
	op_list=ATmakeList0();
	for(;encap_list!=ems_term;encap_list=ATgetArgument(encap_list,1)){
		op_list=ATinsert(op_list,ATmake("pair(<term>,\"delta\")",ATgetArgument(encap_list,0)));
	}

	return ATmake("par(<term>,[],[],<term>,initprocspec(emt,emv,eml))",op_list,proc);
}

static ATerm encode_rename(ATerm rename_list,ATerm proc){
	ATermList op_list;
	ATerm emr_term;

	emr_term=ATmake("emr");
	op_list=ATmakeList0();
	for(;rename_list!=emr_term;rename_list=ATgetArgument(rename_list,2)){
		op_list=ATinsert(op_list,ATmake("pair(<term>,<term>)",
			ATgetArgument(rename_list,0),ATgetArgument(rename_list,1)));
	}

	return ATmake("par(<term>,[],[],<term>,initprocspec(emt,emv,eml))",op_list,proc);
}

static ATerm generateLPEmCRL(int n,int canterminate,
       specificationbasictype *spec,char *err_mes, int regular,int keep_structure);

static ATerm generateLPEmCRLterm( ATerm t,int canterminate,
       specificationbasictype *spec,char *err_mes,int regular,int keep_structure) 

{ ATerm t1=NULL, t2=NULL;
  ATerm t3=NULL;
  char *string1=NULL;
  int n;
  
  if(ATmatch(t,"name(<str>,<int>,<term>)",&string1,&n,&t1))
    { 	t2=generateLPEmCRL(n,canterminate,spec,err_mes,regular,0);
     if (t2==NULL) 
         t3=NULL;
      else {
		t3=namecomposition(n,t1,t2);
		if (keep_structure)
			t3=ATmake("leaf(<str>,<term>)",string1,t3);
	}
    }
  else
  if(ATmatch(t,"par(<term>,<term>)",&t1,&t2))
    {	t1=generateLPEmCRLterm(t1,canterminate,spec,err_mes,regular,keep_structure);
	if (t1==NULL) 
         t3=NULL;
      else 
       { t2=generateLPEmCRLterm(t2,canterminate,spec,err_mes,regular,keep_structure);
         if (t2==NULL) 
            t3=NULL;
         else 
          {
		if (keep_structure)
			t3=ATmake("par([],<term>,[],<term>,<term>)",comm_term,t1,t2);
		else t3=parallelcomposition(t1,t2,canterminate,spec,err_mes);
    }  }}
  else
  if (ATmatch(t,"hide(<term>,<term>)",&t1,&t2))
   {	t2=generateLPEmCRLterm(t2,canterminate,spec,err_mes,regular,keep_structure);
	if (t2==NULL) 
        	t3=NULL;
     else {
        	if (keep_structure) t3=encode_hide(t1,t2);
		else t3=hidecomposition(t1,t2);
	}
   }
  else
  if (ATmatch(t,"encap(<term>,<term>)",&t1,&t2))
   { 	t2=generateLPEmCRLterm(t2,canterminate,spec,err_mes,regular,keep_structure);
	if (t2==NULL) 
          t3=NULL;
     else if (keep_structure) t3=encode_encap(t1,t2);
	else t3=encapcomposition(t1,t2);
   }
  else
  if (ATmatch(t,"rename(<term>,<term>)",&t1,&t2))
   { 	t2=generateLPEmCRLterm(t2,canterminate,spec,err_mes,regular,keep_structure);
 	if (t2==NULL) 
          t3=NULL;
     else if (keep_structure) t3=encode_rename(t1,t2);
	else t3=renamecomposition(t1,t2);
   }
  else rg_error("Expect mCRL term",t);

  return t3;
}

/**************** GENERATE LPEmCRL **********************************/

ATerm generateLPEmCRL(
          int n, int canterminate,
          specificationbasictype *spec,char *err_mes,int regular,int keep_structure)
/* generates a pair of a initial argument list and a
   linear process expression, representing the initial ATerm .
   If regular=1, then a regular version of the pCRL processes
   must be generated 

*/
{ ATerm t3=NULL;
  
  
  if debug ATfprintf(stderr,"generateLPEmCRL %t\n",
                objectdata[n].processbody);
  if ((objectdata[n].processstatus==GNF)||
      (objectdata[n].processstatus==pCRL)||
      (objectdata[n].processstatus==GNFalpha))
   { t3=generateLPEpCRL(n,
        (canterminate&&objectdata[n].canterminate),spec,err_mes,regular);
	if (keep_structure) t3=ATmake("leaf(<str>,<term>)","X",t3);
   }
  else /* process is a mCRLdone ATerm */
   if ((objectdata[n].processstatus==mCRLdone)||
              (objectdata[n].processstatus==mCRLlin)||
              (objectdata[n].processstatus==mCRL))
    { objectdata[n].processstatus=mCRLlin;
      t3=generateLPEmCRLterm(objectdata[n].processbody,
             (canterminate&&objectdata[n].canterminate),spec,err_mes,
             regular,keep_structure); 
    }
 else
   { fprintf(stderr,"LASTSTATUS: %d\n",objectdata[n].processstatus);
     rg_error("We may not end here",NULL); }
  
  return t3;
}

/*********************** initialize_data **************/
int firsttime=1;

void initialize_data(void)
{ int i;
  time_operators_used=0;
  release_totalarglist(seq_varnames);
  seq_varnames=NULL;
  controlstate=NULL;
  enumeratedtypes=NULL;
  enumeratedtypelist=NULL;
  stacklist=NULL;
  if (firsttime) 
   { ATprotect(&sumlist);
     ATprotect(&localequationvariables);
     initialize_formats();
   }
  else
   { remove_searchtype(objectroot,0);
     remove_searchtype(sortroot,1); 
     lastoccupiedvariablenamenumber=0;
   }  
   
   
  lastoccupiedvariablenamenumber=0;
  lastoccupiedobjectnumber=0;
  lastoccupiedsortnumber=0;
  variablenameroot=NULL;
  objectroot=NULL;
  sortroot=NULL;
  for( i=0 ; i<=MAXSORT ; i++)
    { sortdata[i].sortname=NULL;
      sortdata[i].constructor=0;}
  for( i=0 ; i<=MAXOBJECT ; i++)
    { objectdata[i].objectname=NULL;
      objectdata[i].args=NULL;
      objectdata[i].representedprocess=NULL;
      if (firsttime) ATprotect(&(objectdata[i].representedprocess));
      objectdata[i].representedprocesses=NULL;
      objectdata[i].targetsort=0;
      objectdata[i].processbody=NULL;
      if (firsttime) ATprotect(&(objectdata[i].processbody));
      objectdata[i].parameters=NULL;
      if (firsttime) ATprotect(&(objectdata[i].parameters));
      objectdata[i].processstatus=unknown;
      objectdata[i].object=none;
      objectdata[i].canterminate=0; }
  firsttime=0;
}

/**************** alphaconversion ********************************/


static ATerm alphaconversionterm(
             ATerm t,ATerm parameters,ATerm varlist,ATerm tl)
{ ATerm t1=NULL, t2=NULL, t3=NULL;
  char *s1=NULL, *s2=NULL;
  int n=0;
  
  
  /* ATfprintf(stderr,"ALPHA %t -- %t\n",t,parameters); */
  if (ATmatch(t,"alt(<term>,<term>)",&t1,&t2))
   { t3=ATmake("alt(<term>,<term>)",
              alphaconversionterm(t1,parameters,varlist,tl),
              alphaconversionterm(t2,parameters,varlist,tl));
   }  
  else
  if (ATmatch(t,"seq(<term>,<term>)",&t1,&t2))
   { t3=ATmake("seq(<term>,<term>)",
              alphaconversionterm(t1,parameters,varlist,tl),
              alphaconversionterm(t2,parameters,varlist,tl));
   }  
  else
  if (ATmatch(t,"par(<term>,<term>)",&t1,&t2))
   { alphaconversionterm(t1,parameters,varlist,tl),
     alphaconversionterm(t2,parameters,varlist,tl); 
     t3=NULL;}  
  else
  if (ATmatch(t,"cond(<term>,<term>,delta)",&t1,&t2))
   { t3=ATmake("cond(<term>,<term>,delta)",
              alphaconversionterm(t1,parameters,varlist,tl),
              substitute_data(varlist,tl,t2));
   }  
  else
  if (ATmatch(t,"sum(<str>,<str>,<term>)",&s1,&s2,&t1))
   { if (occursin(ATmake("<str>",s1),parameters)!=NULL)
      { varlist=ATmake("ins(<str>,<str>,<term>)",s1,s2,varlist);
        /* ATfprintf(stderr,"NEW %s\n",s1); */
        s1=fresh_name(s1);
        insertvariablename(s1);
        tl=ATmake("ins(t(<str>,emt),<term>)",s1,tl); }
    parameters=ATmake("ins(<str>,<str>,<term>)",s1,s2,parameters);
    t3=ATmake("sum(<str>,<str>,<term>)",s1,s2,
              alphaconversionterm(t1,parameters,varlist,tl));
   }  
  else
  if (ATmatch(t,"name(<str>,<int>,<term>)",&s1,&n,&t1))
   { if (objectdata[n].object==proc)
          alphaconversion(n,parameters);
     t3=ATmake("name(<str>,<int>,<term>)",s1,n,
              substitute_datalist(varlist,tl,t1));
   }  
  else
  if (ATmatch(t,"delta"))
     t3=t; 
  else
  if (ATmatch(t,"tau"))
     t3=t; 
  else
  if (ATmatch(t,"hide(<term>,<term>)",&t1,&t2))
   { alphaconversionterm(t2,parameters,varlist,tl);
     t3=NULL;
   }  
  else
  if (ATmatch(t,"rename(<term>,<term>)",&t1,&t2))
   { alphaconversionterm(t2,parameters,varlist,tl);
     t3=NULL;
   }  
  else
  if (ATmatch(t,"encap(<term>,<term>)",&t1,&t2))
   { alphaconversionterm(t2,parameters,varlist,tl);
     t3=NULL;
   }  
  else
  rg_error("Unexpected process format",t);
  
  return t3;
}

static void alphaconversion(int n, ATerm parameters)
{ 
  
  
  /* if debug ATfprintf(stderr,"Alphaconversion: %d %t\n",
           objectdata[n].processstatus,objectdata[n].processbody); */

  if (objectdata[n].processstatus==GNF)
   { objectdata[n].processstatus=GNFalpha;
     objectdata[n].processbody=
       alphaconversionterm(objectdata[n].processbody,
            parameters,emv_term,emt_term);
   }
  else
  if (objectdata[n].processstatus==mCRLdone)
   { alphaconversionterm(objectdata[n].processbody,
            parameters,emv_term,emt_term);
     
   }
  else 
  if (objectdata[n].processstatus==GNFalpha)
     return;
  else rg_error("Unknown type in alphaconversion",ATmake("<int>",
                       objectdata[n].processstatus)); 
  return;
}

/***** determinewhetherprocessescanterminate(init); **********/

int canterminatemCRL(int n);

int canterminatemCRLbody(ATerm t)
{ ATerm t1=NULL, t2=NULL;
  int n=0;
  if (ATmatch(t,"par(<term>,<term>)",&t1,&t2))
     return (canterminatemCRLbody(t1)&&canterminatemCRLbody(t2));
  if (ATmatch(t,"name(<str>,<int>,<term>)",&dummystring,&n,&dummyterm))
     return (canterminatemCRL(n));
  if (ATmatch(t,"hide(<term>,<term>)",&dummyterm,&t1))
     return (canterminatemCRLbody(t1));
  if (ATmatch(t,"rename(<term>,<term>)",&dummyterm,&t1))
     return (canterminatemCRLbody(t1));
  if (ATmatch(t,"encap(<term>,<term>)",&dummyterm,&t1))
     return (canterminatemCRLbody(t1));
  rg_error("expect mCRL ATerm ",t);
  return 0;
}

int canterminatemCRL(int n)
{ if (objectdata[n].processstatus==mCRL)

objectdata[n].canterminate=canterminatemCRLbody(objectdata[n].processbody);
  return (objectdata[n].canterminate);
}

int canterminatebody(ATerm t)
{ ATerm t1=NULL, t2=NULL;
  int n=0;
  if (ATmatch(t,"alt(<term>,<term>)",&t1,&t2))
      return (canterminatebody(t1)||canterminatebody(t2));
  if (ATmatch(t,"seq(<term>,<term>)",&t1,&t2))
      return (canterminatebody(t1)&&canterminatebody(t2));
  if (ATmatch(t,"cond(<term>,<term>,<term>)",&t1,&dummyterm,&t2))
      return (canterminatebody(t1)||canterminatebody(t2));
  if (ATmatch(t,"sum(<str>,<str>,<term>)",&dummystring, &dummystring,
&t1))
      return (canterminatebody(t1));
  if (ATmatch(t,"name(<str>,<int>,<term>)",&dummyterm,&n,&dummystring))
     { if (objectdata[n].object==act) return 1;
       else return (objectdata[n].canterminate);
     }
  if (ATmatch(t,"delta"))
      return 0;
  if (ATmatch(t,"tau"))
      return 1;
  rg_error("Unexpected pCRL process",t);
  return 0;
}

void determinewhetherprocessescanterminate(arglist *pcrlprocs,int n)
/* delivers 1 if the process can terminate
   and delivers 2 if the process cannot terminate.
   For each process this status is stored in the variable
   canterminate */
{ int stable=0;
  arglist *walker=NULL;
  for(; (!stable); )
    { stable=1;
      for(walker=pcrlprocs; (walker!=NULL); walker=walker->next)
       { if (objectdata[walker->n].canterminate==0)
            { if(canterminatebody(objectdata[walker->n].processbody))
                { stable=0;
                  objectdata[walker->n].canterminate=1;
                }
            }
       }
    }

  canterminatemCRL(n);
}

/**************** store_comm_in_hashtable *******************************/

static void insert_comm_in_hashtable(ATerm act1, ATerm act2, ATerm act3)
{ 
  ATermList list=NULL, listwalker=NULL; 
  ATerm pair=NULL, act2alt=NULL, act3dummy=NULL;

  /* First determine whether for act1 already a pair starting with
     act2 is stored in the hashtable. If so this is an error */

  list=(ATermList)ATtableGet(comm_hashtable,act1);
  if (list==NULL)
   { list=ATempty; }
  else 
   { for(listwalker=list ; (!ATisEmpty(listwalker)) ; 
                 listwalker=ATgetNext(listwalker) )
     { pair=ATgetFirst(listwalker);
       if (ATmatch(pair,"pair(<term>,<term>)",&act2alt,&act3dummy))
        { if (act2==act2alt)
          { if (act3==act3dummy)
             { return; }
            else 
             ATerror("Communication hashtable left pair not unique: %t\n",act2);
          }
        }
       else ATerror("Expect pair: %t\n",pair);
     }
   }
  
  /* list is ok. Insert the new communciation and replace list
     in the hashtable */
    
  ATtablePut(comm_hashtable,act1,
      (ATerm)ATinsert(list,ATmake("pair(<term>,<term>)",
             act2,act3)));


}

static void store_comm_in_hashtable(specificationbasictype *spec)
{
  /* for each action a, a list of pairs <b_i,c_i> is stored
     in the hashtable if gamma(a,b_i)=c_i (c_i not delta).
     In this list each b_i at most occurs once.
     This can be used to determine: 1) whether an action a
     can communicate at all. If not, it does not occur in the
     hashtable. 2. To quickly find for each a those b_i's
     with which it can communicate. This improvement has been
     made, because the previous linearizer, using sequential
     search through lists of communications, was far too slow
     to handle the Euris safety system of Woerden Harmelen. */

  ATerm walker=NULL;
  ATerm act1=NULL, act2=NULL, act3=NULL;

  comm_hashtable=ATtableCreate(32,75);
  if (comm_hashtable==NULL)
     ATerror("Cannot create communication hashtable");
  
  /* YY */

  for (walker=spec->comms;
       (ATmatch (walker, "ins(<term>,<term>,<term>,<term>)",
            &act1,&act2,&act3, &walker));)
  { insert_comm_in_hashtable(act1,act2,act3);
    insert_comm_in_hashtable(act2,act1,act3);
  }


/*
 * In order to translate a mCRL parallel to a generalized composition,
 * we need the composition function in the correct format. Below,
 * we compute this function and store it in comm_term.
 */

	comm_term=(ATerm)ATmakeList0();
  	for(walker=(ATerm)ATtableKeys(comm_hashtable);
		!ATisEmpty((ATermList)walker);
		walker=(ATerm)ATgetNext((ATermList)walker)){
		comm_term=(ATerm)ATinsert((ATermList)comm_term,ATmake("comm(<term>,<term>)",
			ATgetFirst((ATermList)walker),
			ATtableGet(comm_hashtable,ATgetFirst((ATermList)walker))));
	}

}


/**************** transform **************************************/

ATerm transform(int init, specificationbasictype *spec,char *err_mes,int keep_structure)
{ arglist *pcrlprocesslist;
  int err=0;
  ATerm t3=NULL;

  /* Store communications in a global hash table: comm_hashtable */

  store_comm_in_hashtable(spec);
  
  /* Then select the BPA processes, and check that the others
     are proper parallel processes */
  pcrlprocesslist=determine_process_status(init,mCRL,err_mes,&err);

  if (err==1) return NULL;
  if (pcrlprocesslist==NULL) 
   { sprintf(err_mes,"There are no pCRL processes to be linearized");
     return NULL; }
  determinewhetherprocessescanterminate(pcrlprocesslist,init);
  /* Second, transform into GNF with possibly variables as a head,
     but no actions in the tail */
  if (!procstovarheadGNF(pcrlprocesslist,err_mes))
        return NULL; 
  release_totalarglist(pcrlprocesslist);
  /* Third, transform to GNF by subsitution, such that the
     first variable in a sequence is always an actionvariable */
  if (!procstorealGNF(init,err_mes,regular))
        return NULL; 
  
  /* if debug fprintf(stderr,"Start alpha conversion\n");
  alphaconversion(init); This is now done in generateLPEmCRL */
  

  if (debug) fprintf(stderr,"Start generating LPE\n");
  /* Now, generate LPE */

  /* the last argument indicates that we are interested in 
     treating the pCRL processes as if they are regular, 
     instead of translating them using stacks */

  t3=generateLPEmCRL(
           init,objectdata[init].canterminate,spec,err_mes,regular,keep_structure);
  if ((t3!=NULL) && (cluster))
     t3=clusterfinalresult(t3,spec,err_mes);
  ATtableDestroy(comm_hashtable);
  return t3;
}

/******************* 2gen  **********************************/

/* Below a int of functions are added that translate the 
   "classical" term format as described in Dams and Groote to
   a format where all strings are unique, by attaching the type of
   an object after a "#", e.g. "max" becomes "max#nat#nat".
   Furthermore, terms and lists are translated to the aterm format.
   E.g. instead of a term "t("max",ins(t("0",emt),......" a term
   "max"("0",...." is given, and instead of a list "ins("Bool",
   ins("nat",...., emt)))))", a aterm list ["Bool","nat"...] is
   produced. 
 
   The reason for this translation of internal LPO format is
   that we believe that parsing of this format is done substantially
   faster, than parsing of the old format. Given that parsing
   has become an actual bottleneck in large specifications, we
   feel forced to make such an adaptation. Jan Friso Groote 27/12/99. 

   It would be a good idea to adapt the lineariser such that it
   internally also uses the new format. However, as the old format must
   also be provided for the moment, and it is a huge amount of work
   to adapt the system to the new format, this is postponed to a
   later moment in time */


/**********************  extend_name_with_sorts */

static char *buffer=NULL;
static unsigned int buffer_length=0;

static char *extend_name_with_sorts(char *n,ATermList sorts)
{ unsigned int resultlength;
  char *sort;
  ATermList sorts1=NULL;

  /* first determine length of result */
  sorts1=sorts;
  if (newtbf && ATisEmpty(sorts1))
    {
    resultlength = strlen(n)+2;
    }
  else
  for( resultlength=strlen(n)+1; (!ATisEmpty(sorts1)); sorts1=ATgetNext(sorts1))
  { /* if (!ATmatch(ATgetFirst(sorts1),"<str>",&sort)) 
    { rg_error("Expect string",ATgetFirst(sorts1));
    } */
    sort=ATgetName(ATgetAFun(ATgetFirst(sorts1)));
    resultlength=resultlength+strlen(sort)+1;
  }

  if (resultlength>buffer_length)
  { if (buffer==NULL)
    { buffer=malloc(resultlength+64);
      buffer_length=resultlength+64;
    }
    else 
     { buffer=realloc(buffer,resultlength*2);
       buffer_length=resultlength*2;
     }
    if (buffer==NULL)
    { rg_error("Cannot extend string buffer",NULL);
    }
  }

  sorts1=sorts;
  if (newtbf && ATisEmpty(sorts1))
    {
    strcpy(buffer,n);
    strcat(buffer,"#");
    }
  else
  for( strcpy(buffer,n); (!ATisEmpty(sorts1)); sorts1=ATgetNext(sorts1))
  { /* if (!ATmatch(ATgetFirst(sorts1),"<str>",&sort))
    { rg_error("Expect string",ATgetFirst(sorts1));
    } */
    sort=ATgetName(ATgetAFun(ATgetFirst(sorts1)));
    strcat(buffer,"#");
    strcat(buffer,sort);
  }

  return buffer;
}

static char *extend_name_with_sorts_arglist(char *n,arglist *sorts)
{ unsigned int resultlength;
  arglist *sorts1;

  /* first determine length of result */
  sorts1=sorts;
  if (newtbf && !sorts1)
    {
    resultlength = strlen(n)+2;
    }
  else
  for( resultlength=strlen(n)+1; (sorts1!=NULL); sorts1=sorts1->next)
  { 
    resultlength=resultlength+strlen(sortdata[sorts1->n].sortname->s)+1;
  }

  if (resultlength>buffer_length)
  { if (buffer==NULL)
    { buffer=malloc(resultlength+64);
      buffer_length=resultlength+64;
    }
    else
     { buffer=realloc(buffer,resultlength*2);
       buffer_length=resultlength*2;
     }
    if (buffer==NULL)
    { rg_error("Cannot extend string buffer",NULL);
    }
  }

  sorts1=sorts;
  if (newtbf && !sorts1)
    {
    strcpy(buffer,n);
    strcat(buffer,"#");
    }
  else
  for( strcpy(buffer,n); (sorts1!=NULL); sorts1=sorts1->next)
  { 
    strcat(buffer,"#");
    strcat(buffer,sortdata[sorts1->n].sortname->s);
  }

  return buffer;
}


/**********************  translate_terms */

static ATermList translate_variables_2gen_rec(ATerm t)
{ /* ATerm var=NULL,sort=NULL; */
  ATermList u=NULL;

  /* if (!ATmatch(t,"ins(<term>,<term>,<term>)",&var,&sort,&t))  */
  if (ATgetAFun(t)!=ins3_symbol)
  { 
#ifndef NDEBUG
    if (t!=emv_term)
     { rg_error("Expect empty variable list",t);
     }
#endif
    return ATempty; 
  }
  
  u=translate_variables_2gen_rec(ATgetArgument(t,2));
  u=ATinsert(u,(ATerm)ATmakeAppl2(v_symbol,
       (ATerm) ATmakeAppl0(
       ATmakeSymbol(
       extend_name_with_sorts (ATgetName(ATgetSymbol(ATgetArgument(t, 0))),ATempty)
	   , 0, ATtrue)) 
       ,ATgetArgument(t,1)));
  return u;
}

static ATermList translate_variables_2gen(ATerm t)
{ 
  return translate_variables_2gen_rec(t);
}

/**********************  translate_terms */

static ATerm translate_term_2gen(ATerm t, int *sort);

static ATermList translate_termlist_2gen(ATerm tlist, arglist **sorts)
{
  ATerm tm=NULL;
  ATermList new_tlist=NULL;
  int sort;

  *sorts=NULL;
  if (tlist==emt_term) return ATempty;
  else /* if (ATmatch(tlist,"ins(<term>,<term>)",&tm,&tlist)) */
     if (ATgetAFun(tlist)==ins2_symbol)
     { tm=ATgetArgument(tlist,0);
       tlist=ATgetArgument(tlist,1);
       tm=translate_term_2gen(tm,&sort);
       new_tlist=translate_termlist_2gen(tlist, sorts);
       *sorts=new_arglist(sort,*sorts);  
       return ATinsert(new_tlist,tm);
     }
  else rg_error("Expect termlist",tlist);
  return NULL;
}

static ATerm translate_term_2gen(ATerm t, int *sort)
{ char *str;
  ATerm tlist=NULL,result=NULL;
  ATermList args=NULL;
  arglist *sorts=NULL;

  /* if (ATmatch(t,"t(<str>,<term>)",&str,&tlist)) */
  if (ATgetAFun(t)==t_symbol)
   { str=ATgetName(ATgetAFun(ATgetArgument(t,0)));
     tlist=ATgetArgument(t,1);
     args=translate_termlist_2gen(tlist,&sorts);
     if (!existfuncmapvar(str,sorts,sort))
     { rg_error("Unknown function symbol",t); }
     result=(ATerm)ATmakeApplList(
         ATmakeAFun(extend_name_with_sorts_arglist(str,sorts),
                    ATgetLength(args),ATtrue),
         args);
     release_totalarglist(sorts);
     return result;
   }
   else { rg_error("Cannot translate term",t);}
   return(0);
}

/**********************  translate_sorts */

static ATermList translate_sorts_2gen_rec(ATerm t)
{ /* ATerm t1,stringterm; */
  /* if (ATmatch(t,"ins(<term>,<term>)",&stringterm,&t1)) */
  if (ATgetAFun(t)==ins2_symbol)
   { return ATinsert(translate_sorts_2gen_rec(ATgetArgument(t,1)),
                 ATgetArgument(t,0));
   }
#ifndef NDEBUG
  if (t!=ems_term)
   { rg_error("Expect empty sort list",t);
   }
#endif
  return ATempty;
}

ATermList translate_sorts_2gen(ATerm t)
{ ATermList u=NULL;
  u=translate_sorts_2gen_rec(t);
  /* ATfprintf(stderr,"sorts: %t\n",u); */
  return u;
}

/**********************  translate_funcs */

ATermList translate_funcs_2gen(ATerm t)
{ ATermList u=ATempty,new_argumentsorts=NULL;
  ATerm argumentsorts=NULL,targetsort=NULL, function=NULL;
  char *functionname,*new_functionname;
  /* for( ; ATmatch(t,"ins(f(<str>,<term>,<term>),<term>)",
           &functionname,&argumentsorts,&targetsort,&t) ; ) */
  for( ; ATgetAFun(t)==ins2_symbol ; )
  { function=ATgetArgument(t,0);
    t=ATgetArgument(t,1);
    functionname=ATgetName(ATgetAFun(ATgetArgument(function,0)));
    argumentsorts=ATgetArgument(function,1);
    targetsort=ATgetArgument(function,2);
    new_argumentsorts=translate_sorts_2gen_rec(argumentsorts);
    new_functionname=extend_name_with_sorts(functionname,new_argumentsorts);
     /* Warning: new_function_name sits in a buffer that is
        overwritten at the next call of extend_name_with_sorts */
    u=ATinsert(u,(ATerm)ATmakeAppl3(f_symbol,
          (ATerm)ATmakeAppl0(ATmakeAFun(new_functionname,0,ATtrue)),
          (ATerm)new_argumentsorts,
          targetsort));
  }

#ifndef NDEBUG
  if (t!=emf_term)
   { rg_error("Expect empty function list",t);
   }
#endif

  /* ATfprintf(stderr,"functions: %t\n",u); */
  return u;
}

/**********************  translate_eqns */

ATermList translate_eqns_2gen(ATerm t)
{ ATermList u=ATempty, new_variablelist=NULL;
  ATerm eqn=NULL, lhs=NULL,rhs=NULL,variablelist=NULL,
             new_lhs=NULL,new_rhs=NULL;
  int sort;

  /* for( ; ATmatch(t,"ins(e(<term>,<term>,<term>),<term>)",
           &variablelist,&lhs,&rhs,&t) ; ) */
  for( ; ATgetAFun(t)==ins2_symbol ; )
  { eqn=ATgetArgument(t,0);
    t=ATgetArgument(t,1);
    variablelist=ATgetArgument(eqn,0);
    lhs=ATgetArgument(eqn,1);
    rhs=ATgetArgument(eqn,2);
    new_variablelist=translate_variables_2gen(variablelist);
    if (!declarevariables(variablelist,scratch1))
     { 
       ATerror("Cannot declare variables: %s\n",scratch1);
     }
    new_lhs=translate_term_2gen(lhs,&sort);
    new_rhs=translate_term_2gen(rhs,&sort);
    resetvariables(variablelist);    
    u=ATinsert(u,(ATerm)ATmakeAppl3(e_symbol,(ATerm)new_variablelist,
        new_lhs,new_rhs));
  }

#ifndef NDEBUG
  if (t!=eme_term)
   { rg_error("Expect empty function list",t);
   }
#endif

  /* ATfprintf(stderr,"equations: %t\n",u); */
  return u;
}

/**********************  translate_lpo */

ATerm translate_lpo_2gen(ATerm t)
{ ATerm initstate=NULL, parameters=NULL, summands=NULL,
                new_t=NULL, smd=NULL;
  ATerm sums=NULL,act_arg=NULL,X_arg=NULL,condition=NULL;
  ATermList new_sums=NULL, new_act_arg=NULL;
  ATerm new_X_arg=NULL, new_condition=NULL;
  ATermList new_initstate=NULL, new_parameters=NULL, new_summands=NULL;
  arglist *sorts=NULL;
  ATerm action=NULL;
  int sort;

/* ATfprintf(stderr,"LPO: %t\n",t); */

/*  fprintf(stderr,"mcrl: Flag -2gen is not fully implemented yet.\n\
Output can contain an erroneous or partially defined LPO\n");
*/

  if (!ATmatch(t,"initprocspec(<term>,<term>,<term>)",
         &initstate,&parameters,&summands)) 
   {
	/* If we are translating a multi LPO then initprocspec is not the only option,
         * generalized parallel compositions and leaf are also possible.
         */
	ATerm op1,op2,comm,p1,p2;
	char *s;
	if(ATmatch(t,"leaf(<str>,<term>)",&s,&p1)){
		return ATmake("leaf(<str>,<term>)",s,translate_lpo_2gen(p1));
	}
	if(ATmatch(t,"par(<term>,<term>,<term>,<term>,<term>)",&op1,&comm,&op2,&p1,&p2)){
		return ATmake("par(<term>,<term>,<term>,<term>,<term>)",op1,comm,op2,
			translate_lpo_2gen(p1),translate_lpo_2gen(p2));
	}
	/* we really do have an illegal term :-( */
	rg_error("Expect initprocspec",t);
   }
  t=NULL;
  new_initstate=translate_termlist_2gen(initstate,&sorts);
  if (!declarevariables(parameters,scratch1))
     { ATerror("Cannot declare variables: %s\n",scratch1);
     }
  new_parameters=translate_variables_2gen(parameters);
  
  for( new_summands=ATempty; 
   /*  (ATmatch(summands,
         "ins(smd(<term>,<str>,<term>,<term>,<term>),<term>)",
         &sums,
         &action,
         &act_arg,
         &X_arg,
         &condition,
         &summands)) ;  */
       (ATgetAFun(summands)==ins2_symbol) ; )
  { smd=ATgetArgument(summands,0);
    summands=ATgetArgument(summands,1);
    sums=ATgetArgument(smd,0);
    action=ATgetArgument(smd,1);
    act_arg=ATgetArgument(smd,2);
    X_arg=ATgetArgument(smd,3);
    condition=ATgetArgument(smd,4);
    if (!declarevariables(sums,scratch1))
     { 
       ATerror("Cannot declare variables: %s\n",scratch1);
     }
    new_sums=translate_variables_2gen(sums);
    new_act_arg=translate_termlist_2gen(act_arg,&sorts);
    new_condition=translate_term_2gen(condition,&sort);
    /* if (ATmatch(X_arg,"i(<term>)",&X_arg)) */
    if (ATgetAFun(X_arg)==i_symbol)
    { new_X_arg=(ATerm)ATmakeAppl1(i_symbol,
           (ATerm)translate_termlist_2gen(
               ATgetArgument(X_arg,0),&sorts));
    }
    else new_X_arg=terminated_term;

    new_summands=ATinsert(new_summands,
        (ATerm)ATmakeAppl5(smd_symbol,
            (ATerm)new_sums,
            action,
            (ATerm)new_act_arg,
            (ATerm)new_X_arg,
            new_condition));
    resetvariables(sums);
  }
  resetvariables(parameters);

#ifndef NDEBUG
  if (summands!=eml_term)
   { rg_error("Expect empty summand list",summands);
   }
#endif


  new_t=ATmake("initprocspec(<term>,<term>,<term>)",
          new_initstate,new_parameters,new_summands);
/* ATfprintf(stderr,"body: %t\n",new_t); */
  return new_t;
}


