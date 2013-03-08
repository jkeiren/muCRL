/* The rewriters part */
/* $Id: tasks.h,v 1.2 2002/10/28 16:03:04 bertl Exp $ */

typedef void (*RWSETARGUMENTS)(int *argc, char ***argv);
typedef ATbool (*RWINITIALIZE)(ATerm datatype);
typedef void (*RWASSIGNVARIABLE)(AFun var, ATerm t, ATerm tsort, int level);
typedef ATerm (*RWGETASSIGNEDVARIABLE)(AFun val);
typedef void (*RWRESETVARIABLES)(int level);
typedef void (*RWDECLAREVARS)(ATermList variable_names);
typedef ATerm (*RWREWRITE) (ATerm t);
typedef ATermList (*RWREWRITELIST) (ATermList l);
typedef void (*RWSETAUTOCACHE) (ATbool b);
typedef void (*RWFLUSH) (void);
typedef void (*RWHELP) (void);

typedef struct {
  RWSETARGUMENTS RWsetArguments;
  RWINITIALIZE RWinitialize;
  RWASSIGNVARIABLE RWassignVariable;
  RWGETASSIGNEDVARIABLE RWgetAssignedVariable;
  RWRESETVARIABLES RWresetVariables;
  RWDECLAREVARS RWdeclareVariables;
  RWREWRITE RWrewrite;
  RWREWRITELIST RWrewriteList;
  RWSETAUTOCACHE RWsetAutoCache;
  RWFLUSH RWflush;
  RWHELP RWhelp;
} TASKS;
