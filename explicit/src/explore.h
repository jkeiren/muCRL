/* $Id: explore.h,v 1.15 2005/09/16 12:37:19 bertl Exp $ */
#ifndef EXPLORE_H
#define EXPLORE_H
#include "vector_db.h"
#include "term_db.h"
#include "xlts.h"

extern elm_t deadlock_state[];

/** @name Stepper
    Calculates outgoing transitions from the entered state.
    For each calculated transition the defined callback function 
    {\tt ecb} is invoked.
    {\tt explore.h} is parametrized with the type {\tt elm_t} and 
     type {\tt act_t}  
*/
//@{
typedef void *step_t;

/** 
@memo Callback function 
@doc This callback function will be called after a transition is calculated.
@param tag for example pointer to a struct which may contain the source state
@param act action identifier
@param dest destination state
@return <0 error
@return =0 continue
@return >0 abort
*/
typedef int (*expl_cbt)(void *tag, act_t *act, elm_t *dest);

/** 
@memo Callback function 
@doc This callback function will be invoked during the call of
{\tt STexploreInitialState} at each computation of the initialstate.
@param tag 
@param *elm array of length {\it number of parameters} which contains an 
initial state
@return <0 error
@return =0 continue
@return >0 abort
*/
typedef int (*init_cbt)(void *tag, elm_t *elm);

/** 
@memo Callback function 
@doc  This callback function is the last callback function which
will be invoked during the call of {\tt STexploreInitialState}.
@param tag
@param count number of initial states
@return <0 error
@return =0 continue
@return >0 abort
*/
typedef int (*fininit_cbt)(void *tag, int count);

/** 
@memo Callback function 
@doc This callback function is the last callback function which
will be invoked during the call of {\tt STexplore}.
@param tag for example pointer to struct which contains the user time
@param count number of transitions
@return <0 error
@return =0 continue
@return >0 abort
*/
typedef int (*finexpl_cbt)(void *tag, int count);

/** 
@memo Callback function 
@doc This callback function will be called after a transition is calculated.
@param user file to store extra log information
@param src source state
@param act action identifier
@param dest destination state
*/
typedef void (*log_cbt)(FILE *user, elm_t *tag, act_t *act, elm_t *dest);
typedef void (*read_cbt)(void *tag, elm_t *src);
/** 
@memo Creates a new stepper 
@doc Steps through mCRL specification
@param source directory which read
@param size length of state vectors
@param labels database 
@param leafs database 
@param nodes array of databases 
of length {\tt number of process parameters}. The first two elements
of the array are not used. 
@param ecb callback function which will be invoked during the call of 
{\tt STexplore} at each creation of a transition
@param icb callback function which will be invoked during the call of 
{\tt STexploreInitialState} if a initial state is computed
@param fecb callback function which will be invoked 
at return of {\tt STexplore}
@param ficb callback function which will be invoked 
at return of {\tt STexploreInitialState}
@param number of segments followed by directory names. In these directories
will be placed the log files.
@return handler
*/

step_t STcreateMCRL(int segment, char *source, int size,  tdb_t labels, tdb_t leafs, vdb_t *nodes, 
expl_cbt ecb, init_cbt icb, finexpl_cbt fecb, fininit_cbt ficb, log_cbt lcb,
int nunber, dir_t *destdir, char *args);

/** 
@memo Creates a new stepper 
@doc Steps through LTS written in .aut file
@param file from which the LTS must be read
@param labels database
@param ecb callback function which will be invoked during the call of 
{\tt STexplore} at each generation  of a new transition
@param icb callback function which will be invoked during the call of 
{\tt STexploreInitialState} if a initial state is computed
@param fecb callback function which will be invoked 
at return of {\tt STexplore} 
@param ficb callback function which will be invoked 
at return of {\tt STexploreInitialState} 
@args for the stepper
@return handler
*/
step_t STcreateAUT(char *file, tdb_t labels,  
expl_cbt ecb, init_cbt icb, finexpl_cbt fecb, fininit_cbt ficb);

/** 
@memo Explores a state
@doc The callback functions {\tt ecb} and {\tt fecb} are invoked
If there is an error then {\tt fecb} will be invoked with a negative value
in parameter {\tt count}
@param st handler
@param tag for example pointer to a struct which contains the source state
@param *elm array which must contain a state 
@return 0 success
@return <0 failure
*/
int STexplore(step_t st, void *tag, elm_t *elm);

/**
@memo Signals for dumping checkpoints
@param st stepper handler
@param cid checkpoint identifier
@return 0 success
@return <0 failure
*/
int STdumpCheckpoint(step_t st, int cid);

/**
@memo Restores the stepper information
@param st handler
@param cid checkpoint identifier
@return 0 success
@return <0 failure
*/
int STrestoreCheckpoint(step_t st, int cid, int count, void *tag );

/** 
@memo Puts the initial states into the databases
@doc The callback functions {\tt icb} and {\tt ficb} are invoked
@param st handler
@param count number of initial states
@param tag which with {\tt icb} is invoked
@return 0 success
@return <0 failure 
*/
int STexploreInitialState(step_t st, void *tag);
/**
@memo Destroys the stepper
@param st handler
@return 0 success
@return <0 failure
*/
int STdestroy(step_t st);

/**
@memo Folds vector of terms
@param st handler
@param terms vector of length {\it number of parameters}
@return key vector of length {\it size}
*/
elm_t *STfold(step_t st, term_t *terms);

/**
@memo Unfolds key vector
@param  st handler
@param key vector of length {\it size}
@return terms vector of length {\it number of parameters}
*/
term_t *STunfold(step_t st, elm_t *key);
int STendLevel(step_t step);
int STread(step_t step, step_t *sta, void *tag, read_cbt read_cb, int stepno);
int STreset(step_t st);
char *STid(step_t step);
int STconnect(step_t step, FILE** channel);
void STeofReached(step_t step);
int  STsend(step_t step, int stepno);
lts_t STgetLTS(step_t step);
FILE *STgetChannel(step_t step, int idx);
int STgetWidth(step_t step);

int STsync(step_t step);
dir_t *STgetDestDirs(step_t step);
dir_t *STgetSrcDirs(step_t step);
int STgetSrcFiles(step_t step, dir_t **dirs, int *siz);
int STgetDestFiles(step_t step, dir_t **dirs, int *siz);
void SThelpMCRL(void);
void STsetArgumentsMCRL(char *args, int *nargs, char ***argv);
int STsegment(step_t st, elm_t *dest);
FILE *STgetActFile(step_t step, int dest_segment);
FILE *STgetDestFile(step_t step, int dest_segment);
int STgetSegment(step_t step);
dir_t STgetSrcDir(step_t step);
int *STtruncateEqual(step_t st, FILE **f);
int STmapNodeId(int id, int pos, int n);
int *STdefineRdesteof(step_t step); 
int STcreateTickLevel(step_t step);
int STgetCountTickBuffers(step_t step);
int STproceedNextTickLevel(step_t step);
int STinRdestFile(step_t step);
int IsTick(act_t act);
//@}
#endif
