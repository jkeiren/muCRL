/* $Id: pp.c,v 1.7 2006/07/12 09:59:50 bertl Exp $ */
#include <stdio.h>

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdlib.h>
#include <string.h>
#include "mcrl.h"
#define DBSIZE 100
#define LINEBREAKLIMIT 80
#define SPACE  "     "
#define ERRORLENGTH 1024
#define BUFLEN 256

static int cursor, rmargin = LINEBREAKLIMIT-5; 
static ATermList procvars = NULL, summands = NULL;
static ATbool print_actions = ATtrue, adt_only = ATfalse, mcrl2 = ATfalse;
static ATerm *actId;
static char *who = "pp";
static ATerm genExpr(ATerm t);

static void helpmsg(ATbool all) 
    {
    Pr("Usage: pp [options] [input file]");
    Pr("");
    Pr("The following options can be used");
    Pr("-help:\t\t\tyields this message");
    Pr("-help-all:\t\tyields all help information");
    Pr("-version:\t\tget the version number of this release");
    Pr("-mcrl2:\t\t\tconverts to mcrl2 format and writes to <stdout>");
    Pr("-no-actions:\t\tno actions declaration part will be printed");
    Pr("-adt-only:\t\tonly the adt part will be printed");
    Pr("-params <name>[,<name>]*:\tprints the arguments of parameters <name>");
    Pr("-conds <ranges>:\tprints the conditions of all pointed summands.");
    Pr("\t\t\tIf <ranges> is the symbol % then all conditions will be printed.");
    Pr("\t\t\t<ranges> is <range>[,<range>]*,");
    Pr("\t\t\twhere <range> is <number>|<number>-<number>.");
    if (all) MCRLhelp();
    }

static void help(char *s) {
    if (strcmp(s,"-help") && strcmp(s,"-help-all")) return;
    Pr("");
    helpmsg(!strcmp(s,"-help-all"));
    Pr("");
    Pr("This tool pretty prints linear mcrl specifications in tbf format");
    Pr("");
    exit(0);
    }

static void version(void)
    {
    /*
    Pr("$Id: pp.c,v 1.7 2006/07/12 09:59:50 bertl Exp $");
    */
    char buf[100];
    sprintf(buf, "Pretty printer:version %s", VERSION);
    Pr(buf);
    }
     
/************ void
print_names****************************************/
void print_names (FILE *f, ATermList names)
{
  for (;!ATisEmpty(names);names=ATgetNext(names))
       {
       fprintf(f, "%s ",MCRLgetName(ATgetFirst(names)));
       }
}
  
/************ newline ****************************************/
static int newline(FILE *f, int lmargin)
     {
     int i;
     fprintf(f,"\n");
     for (i=0;i<lmargin;i++) fprintf(f," ");
     return lmargin;
     }
     
static int print_vars (FILE *f,ATermList vars, int lmargin)
{ 
  for (;!ATisEmpty(vars);vars=ATgetNext(vars),
  !ATisEmpty(vars)? (cursor += fprintf(f,",")):0)
       {
       ATerm var = ATgetFirst(vars);
       ATerm name = ATgetArgument((ATermAppl) var, 0); 
       if (cursor>LINEBREAKLIMIT)  cursor = newline(f, lmargin);
       cursor += fprintf(f, "%s", MCRLgetName(name));
       }
  return cursor; 
}

static int print_pars (FILE *f,ATermList vars,  int lmargin)
{ 
  for (;!ATisEmpty(vars);vars=ATgetNext(vars),
  !ATisEmpty(vars)? (cursor += fprintf(f,",")):0)
       {
       ATerm var = ATgetFirst(vars);
       ATerm sort = ATgetArgument((ATermAppl) var, 1);
       ATerm name = ATgetArgument((ATermAppl) var, 0); 
       if (cursor>LINEBREAKLIMIT)  cursor = newline(f,lmargin);
       cursor += fprintf(f, "%s:", MCRLgetName(name));
       cursor += fprintf(f, "%s", MCRLgetName(sort)); 
       }
  return cursor; 
}

static int print_actionnames (FILE *f,ATermList names,  char sep, int lmargin)
{ 
  for (;!ATisEmpty(names);names=ATgetNext(names),
  !ATisEmpty(names)? (cursor += fprintf(f,"%c", sep)):0)
       {
       ATerm name = ATgetFirst(names); 
       if (cursor>LINEBREAKLIMIT)  cursor = newline(f,lmargin);
       cursor += fprintf(f, "%s", MCRLgetName(name));
       }
  return cursor; 
}

static int print_sums(FILE *f,ATermList vars,  int lmargin)
{ 
  for (;!ATisEmpty(vars);vars=ATgetNext(vars),
       cursor+=fprintf(f,","))
       {
       ATerm var = ATgetFirst(vars);
       ATerm sort = ATgetArgument((ATermAppl) var, 1);
       ATerm name = ATgetArgument((ATermAppl) var, 0); 
       cursor += fprintf(f, "sum(");
       if (cursor>LINEBREAKLIMIT)  cursor = newline(f, lmargin);
       cursor += fprintf(f, "%s:", MCRLgetName(name));
       cursor += fprintf(f, "%s",  MCRLgetName(sort));
       }
  return cursor; 
}

static int print_sorts(FILE *f, ATermList sorts,  int lmargin)
{
     for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts),
               !ATisEmpty(sorts)? (fprintf(f ,"#")):0)
     {
     char *sort = MCRLgetName(ATgetFirst(sorts));
     if (cursor>LINEBREAKLIMIT)  cursor = newline(f, lmargin);
     cursor += fprintf(f, "%s", sort);
     }
  return cursor;
}

/*********void print_term**********************************************/
static int print_term (FILE *f, ATerm t,  int lmargin);

static int print_terms (FILE *f, ATermList terms, int lmargin)
{ 
  for (;!ATisEmpty(terms);terms=ATgetNext(terms),
       !ATisEmpty(terms)? (cursor += fprintf(f,",")):0)
       {
       ATerm term = ATgetFirst(terms);
       if (cursor>LINEBREAKLIMIT)  cursor = newline(f,lmargin);
       cursor = print_term(f, term, lmargin);
       }
  return cursor;
}

static int print_term (FILE *f, ATerm t, int lmargin)
{
 ATermList terms = ATgetArguments((ATermAppl) t);
 int n = ATgetLength(terms);
 char *name =  MCRLgetName(t);
 cursor += fprintf(f, "%s",name);
 if (n) 
      {
      cursor+= fprintf(f,"(");
      if (cursor>LINEBREAKLIMIT)  cursor = newline(f, lmargin);
      cursor = print_terms (f, terms, lmargin);
      cursor+= fprintf(f,")");
      }
 return cursor;
 }
 
     
/********void print LPO**********************************************/
static void PrintSummands(FILE *f, ATermList sums)
     {
     int lmargin = 0;
     int count=0;
     lmargin = cursor = strlen(SPACE); 
     if (ATisEmpty(sums)) 
          {
          fprintf(f,"delta\n");
          return;
          } 
     for (;!ATisEmpty(sums);sums=ATgetNext(sums),
          cursor = ATisEmpty(sums)?(fprintf(f,"\n"),0):
               fprintf(f,"+"),newline(f, 0))
          {ATerm sum = ATgetFirst(sums);
          ATermList pars = (ATermList) ATgetArgument((ATermAppl) sum,0);
          ATerm actname = ATgetArgument((ATermAppl) sum, 1);
          ATermList actargs = (ATermList) ATgetArgument((ATermAppl) sum,2);
          ATerm procarg = ATgetArgument((ATermAppl) sum, 3);
          ATerm cond = ATgetArgument((ATermAppl) sum,4);
          int n = ATgetLength(pars),i;
	  count++;
	  fprintf(f, "\n%s %d:","%",count);
          cursor = newline(f, 0);
          if (n)
               {
               cursor = print_sums(f, pars, lmargin);
               /* cursor = newline(f, lmargin); */
               }
          fprintf(f, "%s",MCRLgetName(actname));
          if (!ATisEmpty(actargs)) 
               {
               cursor += fprintf(f,"(");
               cursor = print_terms(f, actargs, lmargin);
               cursor += fprintf(f,")");
               }
          fprintf(f,".");
          cursor = newline(f, 1);
          if (ATisEqual(procarg, MCRLterm_terminated))
               {
               ATfprintf(f, "%t",procarg); 
               } 
          else
               {
               ATermList states = (ATermList) ATgetArgument((ATermAppl)
                    procarg,0);
               cursor += fprintf(f,"X");
               if (!ATisEmpty(states))
                    {
                    cursor += fprintf(f,"(");
                    cursor = print_terms(f, states, lmargin);
                    cursor += fprintf(f,")");
                    }
               }
          cursor = newline(f, 1);
          cursor+= fprintf (f, "<|");
          cursor = print_term (f, cond, lmargin);
          cursor+= fprintf (f, "|>delta");
          for (i=0;i<n;i++) cursor+= fprintf(f,")");
          }
     }
     
static void printLPO (FILE *f, ATerm proc)
     { 
     ATermList pars = (ATermList) ATgetArgument((ATermAppl) proc, 1);
     ATermList inits = (ATermList) ATgetArgument((ATermAppl) proc, 0);
     int lmargin = 0;
     cursor = (fprintf (f,"\n\n"),0);
     cursor += fprintf (f,"proc X");
     if (ATgetLength(pars) != ATgetLength(inits)) 
          {
     ATwarning("Warning: Number of  process parameters: %d\n",
     ATgetLength(pars));
     ATwarning("which is unequal to length of init state vector (=%d)\n",
          ATgetLength(inits));
          }
     if (!ATisEmpty(pars)) 
          {
          cursor += fprintf (f,"(");
          lmargin = cursor;
          cursor += print_pars(f, pars, lmargin);
          cursor += fprintf (f,")");
          } 
     cursor = (fprintf(f," = \n"),0);
     PrintSummands(f, (ATermList) ATgetArgument((ATermAppl) proc, 2));
     cursor = fprintf(f,"init X");
     if (!ATisEmpty(inits)) 
          {
          cursor += fprintf (f,"(");
          lmargin = cursor;
          cursor += print_terms(f, inits, lmargin);
          cursor += fprintf (f,")");
          }
     cursor = (fprintf(f,"\n"),0); 
     }    


 static ATermList actionSignatures(ATermTable db, ATerm proc) { 
    ATermList sums = (ATermList) ATgetArgument((ATermAppl) proc, 2);
    int i;     
    for (i=0;!ATisEmpty(sums);sums=ATgetNext(sums),i++)
          {ATerm sum = ATgetFirst(sums);
          ATerm actname = ATgetArgument((ATermAppl) sum, 1);
          ATermList actargs = (ATermList) ATgetArgument((ATermAppl) sum,2);
          ATermList types = ATempty, actnames = NULL, sortIds = ATempty,
          args = ATempty;
          MCRLdeclareVars(MCRLgetListOfVars(sum));  
          for (;!ATisEmpty(actargs);actargs=ATgetNext(actargs))
               {ATerm actarg = ATgetFirst(actargs);
               ATerm type = (ATerm) ATmakeAppl0(MCRLgetSort(actarg));
               types = ATinsert(types, type);
               args = ATinsert(args, genExpr(actarg));
               sortIds = 
                  ATinsert(sortIds, ATmake("<appl(<term>)>","SortId", type));
               }
           if (actId) actId[i] = ATmake("<appl(<term>)>", "MultAct",
                 ATmakeList1(ATmake("<appl(<term>,<term>)>","Action",
                 ATmake("<appl(<term>, <term>)>", 
                "ActId", actname, ATreverse(sortIds)),
                ATreverse(args))));
          if (ATisEqual(actname, MCRLterm_tau) || 
            ATisEqual(actname, MCRLterm_delta)) continue; 
          types = ATreverse(types); 
          if ((actnames= (ATermList) ATtableGet(db, (ATerm) types)))
               {
               if (ATindexOf(actnames, actname,0)<0) 
               ATtablePut(db, (ATerm) types, (ATerm) ATinsert(actnames,actname));
               }
          else
               ATtablePut(db, (ATerm) types, (ATerm) ATmakeList1(actname));
          
          }
     return ATtableKeys(db);
     }
     
static void printAct(FILE *f,  ATerm proc)
    {
    int lmargin = 0;
    ATermList keys = NULL;   
    ATermTable db = ATtableCreate(DBSIZE,50);
    if (!db) ATerror("Table of %d cannot be created",DBSIZE);
    keys = actionSignatures(db, proc);
    if (!ATisEmpty(keys)) fprintf(f,"act\n");
     for (;!ATisEmpty(keys);keys=ATgetNext(keys))
          {ATermList argsorts = (ATermList) ATgetFirst(keys);
          ATermList actnames = (ATermList) ATtableGet(db, (ATerm) argsorts);
          lmargin = cursor = fprintf(f,SPACE);
          if (ATisEmpty(argsorts))
               cursor = print_actionnames(f, actnames, ' ', lmargin);
          else
               {
               cursor = print_actionnames(f, actnames, ',', lmargin);
               cursor += fprintf(f, ":");
               cursor = print_sorts(f, argsorts , lmargin);
               }
          cursor = (fprintf(f,"\n"),0);
          } 
     ATtableDestroy(db);
     }              

ATermList translateSorts(ATermList ts) { 
      ATermList r = ATempty; 
      for (;!ATisEmpty(ts);ts=ATgetNext(ts)) {
          ATerm t = ATgetFirst(ts); 
          r = ATinsert(r,   ATmake("<appl(<term>)>", "SortId", t));
          }
      return ATreverse(r);
      }
                 
static ATerm genActs(ATerm proc) {
     ATermList keys = NULL, r = ATempty; 
     ATermTable db = ATtableCreate(DBSIZE,50);
     if (!db) ATerror("Table of %d cannot be created",DBSIZE);
     keys = actionSignatures(db, proc);
     for (;!ATisEmpty(keys);keys=ATgetNext(keys)) {
           ATermList argsorts = (ATermList) ATgetFirst(keys);
           ATermList actnames = (ATermList) ATtableGet(db, (ATerm) argsorts);
           for (;!ATisEmpty(actnames);actnames=ATgetNext(actnames)) {
             r = ATinsert(r, ATmake("<appl(<term>,<term>)>","ActId", 
             ATgetFirst(actnames),
             translateSorts(argsorts)));
             }
          }
     ATtableDestroy(db);
     return ATmake("<appl(<term>)>","ActSpec", ATreverse(r));
     }

    
static void PrintFunctions(FILE *fp, ATermList fs, int lmargin)
     {
     for (;!ATisEmpty(fs);fs=ATgetNext(fs),
     cursor = ATisEmpty(fs)?(fprintf(fp,"\n"),0):newline(fp,lmargin))
          {
          ATerm f = ATgetFirst(fs);
          ATermList args = (ATermList) ATgetArgument(f,1);
          cursor = fprintf(fp, SPACE);
          cursor += fprintf(fp, "%s:", 
               MCRLgetName(ATgetArgument(f,0))); /* name */
          cursor = print_sorts(fp, args, lmargin);
          cursor += fprintf(fp,"->%s", MCRLgetName(ATgetArgument(f,2))); 
               /* sort */
          }
     }
     
static void PrintVars(FILE *f, ATermList vars)
    { 
    int lmargin = 0;
    ATermTable db = ATtableCreate(DBSIZE,50);
    if (!db) ATerror("Table of %d cannot be created",DBSIZE);
    fprintf(f,"var\n");
    lmargin = cursor = fprintf(f,SPACE);
    for (;!ATisEmpty(vars);vars=ATgetNext(vars))
          {ATerm var = ATgetFirst(vars);
          ATerm sort = ATgetArgument((ATermAppl) var, 1);
          ATermList sortvars = (ATermList) ATtableGet(db, sort);
          if (!sortvars) sortvars = ATmakeList1(var);
          else sortvars = ATinsert(sortvars, var);
          ATtablePut(db, sort, (ATerm) sortvars);
          }
     {
     ATermList keys = ATtableKeys(db);
     for (;!ATisEmpty(keys);keys=ATgetNext(keys),
          cursor = ATisEmpty(keys)?(fprintf(f,"\n"),0):newline(f, lmargin))
          {ATerm key = ATgetFirst(keys);
          ATermList sortvars = ATreverse((ATermList) ATtableGet(db, key));
          print_vars(f, sortvars, lmargin);
          cursor += (fprintf(f, ":%s", MCRLgetName(key)),0);
          }           
     } 
     ATtableDestroy(db);
     }
      
void PrintEq(FILE *f, ATerm eq, int cnt)
     {
     int lmargin  = 0, i;
     ATerm left = ATgetArgument((ATermAppl) eq, 1);
     ATerm right = ATgetArgument((ATermAppl) eq, 2);
     lmargin = cursor = fprintf(f,SPACE);
     cursor = print_term(f, left, lmargin);
     cursor += fprintf(f," = ");
     cursor = print_term(f, right, lmargin);
     if (cursor%8!=0) {fprintf(f,"\t");cursor = (cursor/8+1)*8;}
     for (i=cursor;i<rmargin;i+=8) fprintf(f,"\t");
     cursor = (fprintf(f," %c %d\n",'%', cnt),0);
     /* cursor = (fprintf(f,"\n"),0); */
     }
              
static void printADT(FILE *f, ATerm adt)
    {
    int lmargin = 0, cnt = 0;
    ATerm sig = ATgetArgument((ATermAppl) adt,0);
    ATermList sorts = (ATermList) ATgetArgument((ATermAppl) sig,0); 
    cursor = (fprintf(f,"sort\n"),0);
    lmargin = cursor = fprintf(f,SPACE);
    print_names(f, sorts);
    cursor = (fprintf(f,"\n"),0);
    cursor = (fprintf(f,"func\n"),0);
    lmargin = cursor = fprintf(f,SPACE);
    PrintFunctions(f,(ATermList) ATgetArgument((ATermAppl) sig,1),lmargin);
    if (!ATisEmpty(ATgetArgument((ATermAppl) sig,2))) {
      cursor = (fprintf(f,"map\n"),0);
      lmargin = cursor = fprintf(f,SPACE);
      PrintFunctions(f, (ATermList) ATgetArgument((ATermAppl) sig,2),lmargin);
    }
    {
    ATermList eqs = (ATermList) ATgetArgument((ATermAppl) adt,1),
    previous_vars = NULL;
    for (cnt=1;!ATisEmpty(eqs);eqs=ATgetNext(eqs), cnt++)
         {ATerm eq = ATgetFirst(eqs);
         ATermList vars = (ATermList) ATgetArgument((ATermAppl) eq, 0);
         if (!previous_vars || !ATisEqual(vars, previous_vars)) 
              {
              if (!ATisEmpty(vars)) PrintVars(f, vars); 
              previous_vars = vars;
              cursor = (fprintf(f,"rew\n"),0);
              }
         PrintEq(f, eq, cnt);
         }
    }
    }
 
 static ATerm DataVarId(ATerm name, ATerm srt) {
    return ATmake("<appl(<str>,<term>)>", "DataVarId", MCRLgetName(name),
        ATmake("<appl(<term>)>", "SortId", srt)); 
    }
 
 static char *mcrl2Name(ATerm name) {
    char *s = MCRLgetName(name);
    if (ATisEqual(name, MCRLterm_false)) return "false";
    if (ATisEqual(name, MCRLterm_true)) return "true";
    if (!strcmp(s,"and")) return "&&";
    if (!strcmp(s,"or")) return "||";
    if (!strcmp(s, "eq")) return "==";
    return s;
    } 
      
 static ATerm OpId(ATerm name, ATerm srt) {
    return ATmake("<appl(<term>,<term>)>", "OpId", 
       ATmake("<str>", mcrl2Name(name)),
       (ATisQuoted(ATgetAFun(srt))?
       ATmake("<appl(<term>)>", "SortId", srt):
       srt)
       );
    } 
       
 static ATermList genVarNames (ATermList names) {   
  ATermList r = ATempty;
  MCRLdeclareVars(names);
  for (;!ATisEmpty(names);names=ATgetNext(names)) {
       r = ATinsert(r,DataVarId(
         ATgetArgument((ATermAppl) ATgetFirst(names), 0),
         ATgetArgument((ATermAppl) ATgetFirst(names), 1)
         ));
       }
  return ATreverse(r);
  }

static ATerm genSortNames (ATermList names) {   
  ATermList r = ATempty;
  for (;!ATisEmpty(names);names=ATgetNext(names)) {
       r = ATinsert(r, ATmake("<appl(<term>)>","SortId", 
          ATgetFirst(names)));
       }
  return (ATerm) ATreverse(r);
  }
        
static ATerm genSorts (ATermList names) {
  return ATmake("<appl(<term>)>", "SortSpec", genSortNames(names));
  }

static ATerm sortArrow(ATermList args, ATerm result) {
  if (ATgetLength(args)==0) return  ATmake("<appl(<term>)>","SortId", result);
  return ATmake("<appl(<term>,<term>)>",
  "SortArrow", 
  ATmake("<appl(<term>)>","SortId", ATgetFirst(args)), 
  sortArrow(ATgetNext(args), result));
  }
  
static ATerm sortArrowProd(ATermList args, ATerm result) {
  if (ATgetLength(args)==0) return  ATmake("<appl(<term>)>","SortId", result);
  return ATmake("<appl(<term>,<term>)>",
  "SortArrowProd", genSortNames(args),
      ATmake("<appl(<term>)>", "SortId", result));
  }

static ATerm genExpr(ATerm t);

static ATerm dataAppl(ATerm apply, ATermList args) {
  if (ATisEmpty(args)) return apply;
  return dataAppl(ATmake("<appl(<term>,<term>)>",  
       "DataAppl", apply, genExpr(ATgetFirst(args))), ATgetNext(args)); 
  }
   
static ATerm genFunctions(ATermList fs, char *tag) {
     ATermList r = ATempty;
     for (;!ATisEmpty(fs);fs=ATgetNext(fs)) {
          ATerm f = ATgetFirst(fs);
          ATermList args = (ATermList) ATgetArgument(f,1);
          r = ATinsert(r, OpId(ATgetArgument(f,0), 
              sortArrow(args, ATgetArgument(f,2))));
          }
     return ATmake("<appl(<term>)>", tag, ATreverse(r));
     }

static ATerm genDataApplProd(ATerm opId, ATerm t) {
     AFun sym = ATmakeAFun("DataApplProd", 2, ATfalse);
     ATermList args = ATempty; int i, n;
     for (i=0;i<n;i++) 
     args = ATinsert(args, genExpr(ATgetArgument((ATermAppl)t, i)));
     return (ATerm) ATmakeAppl(sym, opId, (ATerm) ATreverse(args));
     }
     
static ATerm genExpr(ATerm t) {
     AFun s = ATgetAFun(t);
     ATerm srt = (ATerm) ATmakeAppl0(MCRLgetSort(t));
     if (MCRLgetType(s)==MCRLvariable) {
         return DataVarId(t , srt);
         }
     {
     ATerm opId = OpId(t, sortArrow(ATgetArguments(
         (ATermAppl) MCRLgetFunction(s)), srt));
     // return genDataApplProd(opId, t);
     return dataAppl(opId, ATgetArguments((ATermAppl) t));
     }
     }

static ATerm isConditionalEq(ATerm lhs, ATerm rhs) {
     if (MCRLgetType(ATgetAFun(rhs))!=MCRLcasefunction) return NULL;
     if (ATisEqual(lhs, ATgetArgument((ATermAppl) rhs, 2))) return 
         (ATerm) ATgetArgument((ATermAppl) rhs, 0);
     return NULL;
     } 
        
static ATerm genEqs(ATermList eqs) {
     ATermList r = ATempty;
     for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
         ATerm eq = ATgetFirst(eqs);
         ATermList vars = genVarNames((ATermList) ATgetArgument((ATermAppl) eq, 0));
         ATerm lhs = ATgetArgument((ATermAppl) eq, 1),
               rhs = ATgetArgument((ATermAppl) eq, 2);
         ATerm t = isConditionalEq(lhs, rhs);
         if (t) {
           r = ATinsert(r, ATmake("<appl(<term>,<term>,<term>, <term>)>",
           "DataEqn", (ATerm) vars, genExpr(t), genExpr(lhs), genExpr(
                        ATgetArgument((ATermAppl) rhs, 1))));
         } else 
           r = ATinsert(r, ATmake("<appl(<term>,<appl>,<term>, <term>)>",
         "DataEqn", (ATerm) vars, "Nil", genExpr(lhs), genExpr(rhs)));
         }
     return ATmake("<appl(<term>)>","DataEqnSpec", r);
     } 

static ATermList genStateVector(ATermList pars, ATermList states) {
     ATermList r = ATempty;
     for (;!ATisEmpty(states);states=ATgetNext(states),pars = ATgetNext(pars)) {
         ATerm state = ATgetFirst(states), par = ATgetFirst(pars);
         if (!ATisEqual(state, ATgetArgument((ATermAppl) par, 0))) {
             r = ATinsert(r, ATmake("<appl(<term>,<term>)>", "Assignment",
             DataVarId(ATgetArgument((ATermAppl) par, 0),
             ATgetArgument((ATermAppl) par, 1)), genExpr(state))); 
             }
          }
      return ATreverse(r);
      }
      
static ATerm genSmd(ATermList pars, ATerm smd, int i) {  
     ATermList vars = genVarNames( 
         (ATermList) ATgetArgument((ATermAppl) smd, 0));    
     ATermList states = (ATermList) ATgetArgument((ATermAppl)
           ATgetArgument((ATermAppl) smd, 3), 0);
     ATerm cond = genExpr(ATgetArgument((ATermAppl) smd, 4));
     return ATmake("<appl(<term>,<term>, <term>,<appl>, <term>)>",
     "LPESummand", vars, cond, actId[i], "Nil", genStateVector(pars, states));
     }
     
static ATerm genLPE(ATerm proc) { 
     ATermList pars =  
              (ATermList) ATgetArgument((ATermAppl) proc, 1);
     ATermList smds = (ATermList) ATgetArgument((ATermAppl) proc, 2);
     ATermList r = ATempty;
     int i;
     for (i=0;!ATisEmpty(smds);smds = ATgetNext(smds),i++)
          r = ATinsert(r, genSmd(pars, ATgetFirst(smds), i));
     return ATmake("<appl(<term>,<term>,<term>)>", "LPE", ATempty, 
                    genVarNames(pars), ATreverse(r));
     }

static ATerm genInit(ATerm proc) {
     ATermList inits = (ATermList) ATgetArgument((ATermAppl) proc, 0);
     ATermList pars =  (ATermList) ATgetArgument((ATermAppl) proc, 1);
     return ATmake("<appl(<term>, <term>)>", "LPEInit", ATempty, 
          genStateVector(pars, inits));
     }
                             
static ATerm mCRL2term(ATerm adt) {
    ATerm sig = ATgetArgument((ATermAppl) adt,0);
    ATerm sorts = genSorts((ATermList) ATgetArgument((ATermAppl) sig,0)); 
    ATerm funcs = genFunctions((ATermList) ATgetArgument((ATermAppl) sig,1),
                  "ConsSpec");
    ATerm maps = genFunctions((ATermList) ATgetArgument((ATermAppl) sig,2),
                  "MapSpec");
    ATerm eqs = genEqs((ATermList) ATgetArgument((ATermAppl) adt,1));
    ATerm acts = genActs(MCRLgetProc());
    ATerm lpe = genLPE(MCRLgetProc());
    ATerm  init = genInit(MCRLgetProc());
    /*
    ATwarning("sorts: %t\n", sorts);
    ATwarning("funcs: %t\n", funcs);
    ATwarning("maps: %t\n", maps);
    ATwarning("eqs: %t\n", eqs);
    */
    return ATmake(
    "<appl(<term>,<term>,<term>,<term>, <term>,  <term>, <term>)>",
    "SpecV1", 
    sorts, funcs, maps, eqs, acts,lpe, init);
    }    

static void WarningHandler(const char *format, va_list args)
     {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }
         
static void ErrorHandler(const char *format, va_list args)
     {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     exit(-1);
     }

ATermList MakeParNames(ATermList pars) {
     ATermList parnames = ATmakeList0();   
     for (;!ATisEmpty(pars);pars=ATgetNext(pars))
       {ATerm par = ATgetFirst(pars);
        parnames = ATinsert(parnames, 
        ATmake("<str>",MCRLgetName(ATgetArgument((ATermAppl) par, 0))));
       }
       return ATreverse(parnames);
    } 

#define WIDTH 80
static int FillEntry(ATermList states, int pt, int *aux, int k, char *table, int size, 
     int *width, char **format) {
     int j = 0, n = 0;
     static char name[WIDTH];
     for (;j<k;j++, pt += (n+1)) {
        ATerm v = ATelementAt(states,aux[j]);
        /*
        ATerm type = (ATerm) ATmakeAppl0(MCRLgetSort(v));
        if (ATisEqual(type, MCRLterm_state)) {
           int m = MCRLstate2Number(v);
           if (m>0) sprintf(name,"#%d",m);
           else
               strncpy(name,ATwriteToString(MCRLprint(v)),WIDTH);
           }
        else
        */ 
        strncpy(name,ATwriteToString(MCRLprint(v)),WIDTH);
        n = strlen(name);
        if (pt+n>=size) 
            ATerror("Table Too small (Size %d)", 
                size);
        strcpy(table+pt, name); strcat(table+pt, "%");
        if (n>width[j]) width[j] = n;
     }
     return pt;
   }
         
static int FillTable(ATermList sums, int pt, int *aux, int k, char *table, 
     int size, int *width, char **format) {
     int i=0;
     for (;!ATisEmpty(sums);sums=ATgetNext(sums))
         {ATerm sum = ATgetFirst(sums);
         ATerm procarg = ATgetArgument((ATermAppl) sum, 3);
          if (!ATisEqual(procarg, MCRLterm_terminated)) {
             ATermList states = (ATermList) ATgetArgument((ATermAppl)
             procarg,0);
             MCRLdeclareVars(MCRLgetListOfVars(sum));
             pt =  FillEntry(states, pt, aux, k, table, size, width, format); 
         }
        }
     for (i=0;i<k;i++) {
         sprintf(format[i],"  %s%ds","%",width[i]);
         /* fprintf(stderr,"QQ:%s\n", format[i]); */   
     }
     return pt;     
}
              
static void PrintProcVars(void) {
     char dummy[20];
     ATermList sums = MCRLgetListOfSummands(), parnames = MakeParNames(
            MCRLgetListOfPars()), procvars0 = procvars;
     int k = ATgetLength(procvars), *aux = (int*) calloc(k, sizeof(int)), i = 0,
     *width = (int*) calloc(k, sizeof(int)), size = ATgetLength(sums)*WIDTH,
     pt = 0;
     char *table = (char*) calloc(size , sizeof(char)), 
     **format = NULL, *buf = NULL, *spt = NULL;
     if (!table) 
        ATerror("Table cannot be allocated (summands = %d))", ATgetLength(sums));
     procvars = ATreverse(procvars);
     format = (char**) calloc(k,sizeof(char*));
     buf = (char*) calloc(k*15,sizeof(char));
     for (i=0;i<k;i++) format[i] = buf+i*15;
     for (k=0, procvars = procvars0;
          !ATisEmpty(procvars);procvars=ATgetNext(procvars),k++)
          {ATerm procvar = ATgetFirst(procvars);
           aux[k] = ATindexOf(parnames, procvar, 0);
           if (aux[k]<0) ATerror("Parameter %t does not exist",procvar);
           width[k] = strlen(ATwriteToString(procvar));
          }
     pt = FillEntry(MCRLgetListOfInitValues(), 
          pt,  aux, k, table, size, width, format);    
     FillTable(sums, pt, aux, k, table, size, width, format);
     i = sprintf(dummy, "%s %-4d", "%", 0);
     for (;i>0;i--) fprintf(stderr," ");
     for (k=0, procvars = procvars0;
          !ATisEmpty(procvars);procvars=ATgetNext(procvars),k++)
          {ATerm procvar = ATgetFirst(procvars);
           fprintf(stdout,format[k], ATwriteToString(MCRLprint(procvar)));
          }
     /* for (i=0;i<k;i++) fprintf(stderr,"%s\n",format[i]); */
     spt = strtok(table, "%");
     fprintf(stdout,"\n");
     for (i=0;spt;i++) {
         int j = 0;
         if (i>0) fprintf(stdout, "%s %-4d", "%", i);
         else fprintf(stdout, "%s %-4s", "%", "I");
         for (;j<k;j++, spt = strtok(NULL,"%"))
                 fprintf(stdout, format[j], spt);
         fprintf(stdout,"\n");
         }
     free(aux); free(format); free(table);free(buf);free(width);       
     exit(0);
     }
     
static void PrintConditions(void) {
     ATermList sums = MCRLgetListOfSummands(), summands0 = summands;
     int nSummands = ATgetLength(sums);
     for (;!ATisEmpty(summands);summands=ATgetNext(summands)) {
         int k = ATgetInt((ATermInt) ATgetFirst(summands));
         if (k<1 || k > nSummands) ATerror("Illegal summand number (%d)",k);
     }
     summands = summands0;
     if (ATisEmpty(summands)) {
        int i;
        for (i=nSummands;i>0;i--) summands = ATinsert(summands, 
           (ATerm) ATmakeInt(i));
     }
     for (;!ATisEmpty(summands);summands=ATgetNext(summands)) {
         int k = ATgetInt((ATermInt) ATgetFirst(summands));
         ATerm sum = ATelementAt(sums, k-1);
         ATerm cond = ATgetArgument((ATermAppl) sum, 4);
         MCRLdeclareVars(MCRLgetListOfVars(sum));
         ATfprintf(stdout,"%s%d: %t (%s)\n", "% ",k, MCRLprint(cond), 
         ATgetName(MCRLgetSort(cond)));
         }
     exit(0);
     }
       
static ATermList ParseParameters(char* procpars) {
    ATermList result = ATmakeList0();
    char *procpar = strtok(procpars, ",");
    do  {
        if (strlen(procpar)>0) {
            result = ATinsert(result,  ATmake("<str>",procpar));
            }
    } while ((procpar = strtok(NULL, ",")));
    return ATreverse(result);
}

static ATermList ParseConditions(char* conditions) {
    ATermList result = ATmakeList0();
    char *condition = strtok(conditions, ",");
    if (!strcmp(conditions,"%")) return result;
    do  {
        char *endptr = NULL;
        int k = strtol(condition, &endptr, 10);
        if (endptr == condition+strlen(condition)) {
            result = ATinsert(result,  ATmake("<int>",k));
            }
        else if (endptr[0]=='-') {
            int l =  strtol(endptr+1, &endptr, 10), i;
            if (endptr == condition+strlen(condition)) {
                 for (i=k;i<=l;i++) 
                 result = ATinsert(result,  ATmake("<int>",i));
                 }
            else
                ATerror("A number of a summand is expected (not %s)",
                          condition);
            } 
        else ATerror("A number of a summand is expected (not %s)",
                          condition);
        } while ((condition = strtok(NULL, ",")));
    return ATreverse(result);
}
                                    
int main(int argc, char *argv[]) {
    int i, j = 0;
    ATbool new;
    char **newargv = (char**) calloc(argc + 2, sizeof(char*));
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0]; /* newargv[j++] = "-no-extra-rules"; */
    ATinit(argc, argv, (ATerm*) &argc);
    ATprotect((ATerm*) &procvars);
    ATprotect((ATerm*) &summands);
    for (i=1;i<argc;i++) {
        help(argv[i]);
        if (!strcmp(argv[i],"-version")) {
	    version();
	    exit(0);
	    }
        if (!strcmp(argv[i],"-params")) {
        if ((++i)<argc && strncmp(argv[i],"-",1)) {
            procvars = ParseParameters(argv[i]); 
            continue;
            }
            else
               ATerror("After flag -params row of process parameters expected");
        }
        if (!strcmp(argv[i],"-conds")) {
        if ((++i)<argc && strncmp(argv[i],"-",1)) {
            summands = ParseConditions(argv[i]); 
            continue;
            }
            else
               ATerror("After flag -conds row of summand numbers expected");
        }
        if (!strcmp(argv[i],"-no-actions")) {
	    print_actions = ATfalse;
            continue;
	    }
        if (!strcmp(argv[i],"-mcrl2")) {
	    mcrl2 = ATtrue;
            continue;
	    }
        if (!strcmp(argv[i],"-adt-only")) {
	    adt_only = ATtrue;
            continue;
	    }
        newargv[j++] = argv[i];
        }
    if (!MCRLinitOnly(j, newargv)) exit(1);
    MCRLdeclareVars(MCRLgetListOfPars());
    /*
    new = ATtrue;
    ATwarning("Result = %a", MCRLputIfFunction(ATmake("<str>","Bool"), &new));
    ATwarning("new = %d", new);
    */
    if (mcrl2)  {
        actId = (ATerm*) calloc(MCRLgetNumberOfSummands(), sizeof(ATerm));
        ATprotectArray(actId, MCRLgetNumberOfSummands());
        {
        ATerm t = mCRL2term(MCRLgetAdt());
        // ATwriteToSharedTextFile(t, stdout);
        ATwriteToTextFile(t, stdout);
        exit(0);
        }
        }
    if (procvars) PrintProcVars();
    if (summands) PrintConditions();    
    if (MCRLformat!=MCRLundefined) 
	MCRLoutput(); 
    else
	{
	printADT(stdout,  MCRLgetAdt());
	if (!adt_only) { 
            if (print_actions) 
            printAct(stdout, MCRLgetProc());
            printLPO(stdout, MCRLgetProc());
           }
	}
    exit(0);
    }


