/* 
   $Id: unification_master.c,v 1.1 2004/01/22 15:43:14 bertl Exp $  
   Author and Copyright: Jaco van de Pol, CWI, Amsterdam, vdpol@cwi.nl
   tera version 2.0.c: a satisfiability checker for term algebra formulas. */

#include "unification.h"

/*******************************/
/* Unification: master variant */
/*******************************/

char UNIF = LINEAR; /* default algorithm */

ATbool ATisVariableLINEAR(ATerm t);
ATbool AToccursLINEAR(ATerm var, ATerm t);
ATerm ATsubstVarLINEAR(ATerm t, ATerm var, ATerm s); 
ATerm ATsubstituteLINEAR(ATerm t, const ATermSubst sigma);
ATbool ATunifyLINEAR(ATerm t1, ATerm t2, ATermSubst sigma);
ATbool ATunifySystemLINEAR(ATermStack system, ATermSubst sigma);
void ATsubstToStackLINEAR(ATermSubst sigma, ATermStack stack); 
ATbool ATisVariableNAIVE(ATerm t);
ATbool AToccursNAIVE(ATerm var, ATerm t);
ATerm ATsubstVarNAIVE(ATerm t, ATerm var, ATerm s); 
ATerm ATsubstituteNAIVE(ATerm t, const ATermSubst sigma);
ATbool ATunifyNAIVE(ATerm t1, ATerm t2, ATermSubst sigma);
ATbool ATunifySystemNAIVE(ATermStack system, ATermSubst sigma);
void ATsubstToStackNAIVE(ATermSubst sigma, ATermStack stack); 

ATbool ATisVariable(ATerm t) {
  return (UNIF==NAIVE ? ATisVariableNAIVE(t) : ATisVariableLINEAR(t) );
}

ATbool AToccurs(ATerm var, ATerm t) {
  return (UNIF==NAIVE ? AToccursNAIVE(var,t) : AToccursLINEAR(var,t) );
}

ATerm ATsubstVar(ATerm t, ATerm var, ATerm s) {
  return (UNIF==NAIVE ? ATsubstVarNAIVE(var,t,s) : ATsubstVarLINEAR(var,t,s) );
}

ATerm ATsubstitute(ATerm t, ATermSubst sigma) {
  return (UNIF==NAIVE ? ATsubstituteNAIVE(t,sigma) : ATsubstituteLINEAR(t,sigma) );
}

ATbool ATunifySystem(ATermStack system,ATermSubst sigma) {
  return (UNIF==NAIVE ? ATunifySystemNAIVE(system,sigma) : ATunifySystemLINEAR(system,sigma) );
}

ATbool ATunify(ATerm t1, ATerm t2, ATermSubst sigma) {
  return (UNIF==NAIVE ? ATunifyNAIVE(t1,t2,sigma) : ATunifyLINEAR(t1,t2,sigma) );
}

void ATsubstToStack(ATermSubst sigma, ATermStack stack) {
  if (UNIF==NAIVE)
    ATsubstToStackNAIVE(sigma,stack);
  else
    ATsubstToStackLINEAR(sigma,stack);
}
