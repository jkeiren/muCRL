/* $Id: rw.h,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */

#ifndef TASKS_H
#define TASKS_H
#ifdef __cplusplus
extern "C"
{
#endif

#include "mcrl.h"

void RWsetArguments(int *argc, char ***argv);

ATbool RWinitialize(ATerm adt);

void SUsetArguments(int *argc, char ***argv);

ATbool SUinitialize(ATerm adt);

void RWassignVariable(AFun var, ATerm t, ATerm tsort, int level);
/* set var:=t at given level, which allows to
   reset variables at that level easily.
   t = NULL is permitted, it means that the variable is not instantiated.
   tsort = NULL is permitted. It means that the sort is not important
   (f.i. rewriting) . 
*/

ATerm RWgetAssignedVariable(AFun var);
/* get the substitution belonging to var 
If no substitution is defined then the name of var will be returned.
*/

void RWresetVariables(int level);
/* unassign the variables  at a given level */

void RWdeclareVariables(ATermList var_names);
/* introduce variables which possibly occur in open terms which are 
   candidates to be rewritten. The variables will be protected 
   Two fomats are permitted. [vname_1,...,vname_n] or
   [v(vname_1, sort_1),...,v(vname_n,sort_n)] 
*/
   
ATerm RWrewrite(ATerm t);
/* rewrite the term t, and substitute the terms
   assigned to variables in t at appropriate places. 
   The terms assigned to variables are assumed
   to be in normal form and will not be rewritten. 
   If something goes wrong, NULL is returned.
*/
   
ATermList RWrewriteList(ATermList l);
/* rewrite the list l of terms t_i, and substitute the terms
   assigned to variables in t_i at appropriate places. 
   The terms assigned to variables are assumed
   to be in normal form and will not be rewritten. 
   If something goes wrong, NULL is returned 
*/


void RWsetAutoCache(ATbool b);

void RWflush(void);

void RWhelp(void);

#ifdef __cplusplus
}
#endif/* __cplusplus */
#endif
