/* $Id: stepper.c,v 1.9 2005/10/11 07:38:28 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdio.h>
#include "param0.h"
#include "utl.h"
#include "fifo.h"
#include "explore.h"
#include "rw.h"
#include <string.h>
#include "ltree.h"
#include <assert.h>
// #define E(X) if ((err=X)<0) errormsg(""#X)
#define E(X) if ((err=X)<0) abort()
#define WIDTH 2
#define INITSIZE 50

static char *version = "#version_1.0"; 
extern FILE *tty;
extern char *hello, *goodbye, *finish, *steprank, *stepstate, *reset, 
*undoheader, *redo, *parentheader, *markheader, *home, 
*MCRLtrue, *MCRLfalse,  *left, *right,  *childheader, *displayheader, *levelup,
*leveldown, *exploreheader,
*smdheader, *info, *treeheader, *treesmdheader, *button, *depthcontent,
*labelheader, *continueheader, *clearheader, *saveheader, *saveautheader,
*state, *updatestate;
extern char *trc, *outtrc, *ltsfile, *autfile;
extern ATermList names, stateList;
extern ATermTable trace;

static char *last_act = "init";
static int last_smd = -1, marklabels = 0, deadlock = DEADLOCK, 
n_deadlocks = 1; /* Unvisible transition labeled #init# */

static void StepRank(int current);
static void TruncateUndoStack(int current);

void Undo(void);
void Redo(int);

typedef struct {
    act_t act;
    idx_t dest;
    } trans_t;
       
static vdb_t vdb, *nodes, act_db; 
static step_t st; // One stepper
static ltr_t ltr; // Leveled transition system (contains traces)
static fifo_t act_fifo,  dest_fifo,   trans_fifo, undo_fifo, act_db_fifo,
deadlock_fifo; 
static int  npars = 0, transitions = 0;
static tdb_t tdb, adb;
static int interrupted = 0, spanningtree=0, sendstate = 0; 

static void LevelUpButton(char *s) {
     printUTF(stdout,levelup);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     }
     
static void LevelDownButton(char *s) {
     printUTF(stdout,leveldown);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     }

static void ExploreButton(char *s) {
     printUTF(stdout,exploreheader);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     } 
              
static void UpButton(char *s) {
     printUTF(stdout,childheader);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     }
     
static void DownButton(char *s) {
     printUTF(stdout,parentheader);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     }
     
static void UndoButton(char *s) {
     printUTF(stdout,undoheader);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     } 
     
static void RedoButton(char *s) {
     printUTF(stdout,redo);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     }
                    
static void LeftButton(char *s) {
     printUTF(stdout,left);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     }
     
static void RightButton(char *s) {
     printUTF(stdout,right);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     }
     
static void ResetButton(char *s) {
     printUTF(stdout,reset);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     }
     
static void HomeButton(char *s) {
     printUTF(stdout,home);
     printUTF(stdout,s);
     printUTF(stdout,finish);
     fflush(stdout);
     }
     
static int TestFirstChild(trans_t *trans, int current, int leaf, int marked) {
     if (!leaf) return -1;  
     return 0;
     }
        
static void TestChild(int n) {
     int m = LTRrunFromParent(ltr, LTRgetCurrent(ltr), 
           (parent_cb) TestFirstChild);
     UpButton(m==n ?MCRLfalse:MCRLtrue);
     }
                    
static void Active(char *s) {
     int start, end, b = strcmp(s, MCRLfalse), 
     n = LTRrunFromParent(ltr, LTRgetCurrent(ltr), NULL);
     LTRgetBounds(ltr, &start, &end, NULL, NULL, NULL, NULL);
     LeftButton((!b || LTRgetCurrent(ltr)==start)?MCRLfalse:MCRLtrue);
     RightButton((!b || LTRgetCurrent(ltr)==end-1)?MCRLfalse:MCRLtrue);
     DownButton((!b || LTRgetCurrentLevel(ltr)==0)?MCRLfalse:MCRLtrue);
     if (!b) UpButton(MCRLfalse); else TestChild(n);
     LevelUpButton(!b || end==LTRgetNumberOfObjects(ltr)?MCRLfalse:MCRLtrue);
     LevelDownButton((!b || LTRgetCurrentLevel(ltr)==0)?MCRLfalse:MCRLtrue);
     ExploreButton(s);
     RedoButton(!b || FIFOgetAllCount(undo_fifo)-
     FIFOgetCount(undo_fifo)==0?MCRLfalse:MCRLtrue);
     UndoButton((!b || FIFOgetCount(undo_fifo)<=1)?MCRLfalse:MCRLtrue);
     /*
     fprintf(tty,"Undo fifo: count = %d <= %d undo %s redo %s\n", FIFOgetCount(undo_fifo),
     FIFOgetAllCount(undo_fifo), (!b || FIFOgetCount(undo_fifo)<=1)?MCRLfalse:MCRLtrue
     ,(!b || FIFOgetAllCount(undo_fifo)-FIFOgetCount(undo_fifo)==0)?
     MCRLfalse:MCRLtrue);
     */
     ResetButton(s);
     HomeButton(s);
     } 
         
static void InfoButton(void) {
     int  states, visited, transitions, 
     current_level = LTRgetCurrentLevel(ltr), n_deadlocks0 = 1, 
     n_deadlocks1 = n_deadlocks;
     if (current_level < FIFOgetCount(deadlock_fifo))
         FIFOgetElm(deadlock_fifo, current_level, &n_deadlocks1);
     if (current_level>0) FIFOgetElm(deadlock_fifo, current_level-1, 
           &n_deadlocks0);
     LTRgetLevelInfo(ltr, current_level,  &states, &visited, &transitions);
     printUTF(stdout,info);
     writeintUTF(stdout,current_level);
     writeintUTF(stdout,states);
     writeintUTF(stdout,visited);
     writeintUTF(stdout,transitions - (n_deadlocks1 - n_deadlocks0));
     LTRgetCumLevelInfo(ltr, current_level,  &states, &visited, 
     &transitions);
     writeintUTF(stdout,current_level);
     writeintUTF(stdout,states);
     writeintUTF(stdout,visited);
     writeintUTF(stdout,transitions - n_deadlocks1);
     LTRgetTotalLevelInfo(ltr, &states, &visited, &transitions);
     writeintUTF(stdout, LTRgetNumberOfAllLevels(ltr)-2);
     writeintUTF(stdout,states);
     writeintUTF(stdout,visited);
     writeintUTF(stdout,transitions - n_deadlocks);
     printUTF(stdout,finish);
     fflush(stdout);
     }
     
static void DepthContent(char *last_act, int last_smd, int cnt) {
     printUTF(stdout,depthcontent);
     printUTF(stdout, last_act);
     if (last_smd>0) writeintUTF(stdout, last_smd);
     else printUTF(stdout," ");
     writeintUTF(stdout, LTRgetCurrent(ltr));
     printUTF(stdout, cnt==0?MCRLtrue:MCRLfalse);
     printUTF(stdout,finish); 
     }
                   
static char *Act2String(int act) {
      return ATgetName(ATgetAFun(TDBget(adb, act)));
      }
      
static int String2Act(char *act) {
      ATerm t = (ATerm) ATmakeAppl0(ATmakeAFun(act, 0, ATtrue));
      return TDBput(adb, t,  NULL);
      }
      
static int PrintSummand(trans_t *trans, int current, int leaf, int marked) {
    printUTF(stdout,"#summand");
    writeintUTF(stdout, current);
    // fprintf(tty,"Summand: marked %d\n", marked);
    printUTF(stdout, marked==1?MCRLtrue:MCRLfalse);
    if (trans->act.smd>=0) writeintUTF(stdout, trans->act.smd+1);
    else printUTF(stdout," ");
    return 0;
    }

static int PrintBackSummand(trans_t *trans, int join, int current, int length,
    int leaf, int marked) {
    printUTF(stdout,"#summand");
    writeintUTF(stdout, -join-2); 
    printUTF(stdout, marked==1?MCRLtrue:MCRLfalse);   
    writeintUTF(stdout, trans->act.smd+1);
    return 0;
    }
          
static void PrintMarkers(void) {
     int n = LTRgetNumberOfMarks(ltr), i;
     trans_t trans;
     printUTF(stdout,markheader);
     // fprintf(tty,"PrintMarkers n = %d\n", n);
     for (i=0;i<n;i++) {
        LTRgetMarkElm(ltr, i, &trans);
        writeintUTF(stdout, LTRgetLengthOfMark(ltr, i));
        writeintUTF(stdout, LTRgetDepthOfMark(ltr, i));
        writeintUTF(stdout, trans.act.smd+1);
        // fprintf(tty,"PrintMarkers i = %d lab = %d\n", i, trans.act.lab);
        printUTF(stdout, trans.act.lab>=0?
             Act2String(trans.act.lab):"#init");
        writeintUTF(stdout, LTRgetStartOfMark(ltr, i));
        }
     printUTF(stdout,finish); 
     fflush(stdout);
     }
                                     
static int icb(void *tag, elm_t *from) {
     trans_t trans;
     act_t act = {-1,-1};
     VDBput(vdb, from,  NULL);
     trans.act = act; trans.dest = STgetLTS(st)?STgetLTS(st)->root:0;
     if (LTRput(ltr,  0, &trans, NULL)<0) errormsg("icb:LTRput");
     return 0;    
     }
                   
static int ecb(void *src, act_t *act, elm_t *dest) {
     int err =0;
     E(FIFOput(act_fifo, act));
     E(FIFOput(dest_fifo, dest));
     /* fprintf(tty, "ecb (%d %d)\n", dest[0], dest[1]);  */
     return err;
     } 
        
static int fecb(void *tag, int n_transitions) {
     elm_t elm[WIDTH];
     int parent = LTRgetCurrent(ltr);
     /* fprintf(tty,"fecb1: %d\n", n_transitions); */
     while (FIFOget(dest_fifo, elm)>=0) VDBrequestPut(vdb, (void*) 1, elm);
     if (n_transitions==0) {
        // Make label deadlock to itsself
        trans_t trans;
        char *lab = "#deadlock#";
        int val;
        n_deadlocks++;
        LTRgetElm(ltr, parent, &trans);
        deadlock = trans.act.lab =String2Act(lab);
        trans.act.smd = 0;
        LTRmakeJoin(ltr, parent, parent, &trans, &val);
        if (marklabels==1) { 
            int new;
            VDBput(act_db, &trans.act.lab,  &new);
            if (new==1) LTRmakeMark(ltr, -val-2, NULL);
            } 
        }
     transitions = n_transitions;
     // fprintf(tty, "fecb level %d current %d\n", LTRgetCurrentLevel(ltr),
     // parent);
     LTRfinishState(ltr, parent);
     // LTRgetCumLevelInfo(ltr, LTRgetCurrentLevel(ltr), NULL, &visited, NULL);
     // fprintf(tty, "visited = %d == %d == size db\n",
     // visited, VDBgetCount(vdb));
     /* fprintf(tty, "fecb2: %d\n", n_transitions); */
     return 0;
     }

static int compare(const void *dest, const void *r) {
      trans_t *t = (trans_t*) ((char*) r + sizeof(int));
      return *((int*) dest)-t->dest;
      } 

static idx_t SearchLinear(ltr_t ltr, int dest) {
       int i, n = LTRgetNumberOfObjects(ltr);
       // fprintf(tty, "obj==NULL: dest = %d Nobjects = %d\n",
       // dest, LTRgetNumberOfObjects(ltr));
       for (i=0;i<n;i++) {
          trans_t trans;
          LTRgetElm(ltr, i, &trans);
          if (trans.dest == dest) return i;
          }
      return -1;
      } 
      
static void UpdateUndoStackTree(int idx) {
      int i=0, n=FIFOgetAllCount(undo_fifo);
      for (;i<n;i++) {
          int v;
          FIFOgetElm(undo_fifo, i, &v);
          if (v>=idx) {
             v++;
             FIFOupdateElm(undo_fifo, i, &v);
             }
          }
      }
     
static idx_t Idx(idx_t dest) {
        char *bf = LTRgetArray(ltr), *obj =
        bsearch(&dest, bf ,LTRgetNumberOfObjects(ltr),
            sizeof(trans_t)+sizeof(int), compare); 
        // fprintf(tty, "Idx %d\n", (obj-bf)/(sizeof(trans_t)+sizeof(int)));    
        return  obj?(obj-bf)/(sizeof(trans_t)+sizeof(int))
              :SearchLinear(ltr, dest);
        }

static int NewLabel(int lab) {
        int new, n;
        static int act_fifo_size = 0, deadlock_fifo_size = 0;
        VDBput(act_db, &lab,  &new);
        n = VDBgetCount(act_db);
        for (;LTRgetCurrentLevel(ltr)>act_fifo_size; act_fifo_size++) {
              FIFOput(act_db_fifo, &n);
              }
           if (LTRgetCurrentLevel(ltr)==act_fifo_size) {
              FIFOput(act_db_fifo, &n); act_fifo_size++;
              }   
           else {
            FIFOupdateElm(act_db_fifo, LTRgetCurrentLevel(ltr), &n);
            }
        // fprintf(tty, "NewLabel new = %d level = %d count = %d %s n = %d\n",
        // new, LTRgetCurrentLevel(ltr), FIFOgetCount(act_db_fifo),
        // lab>=0?Act2String(lab):"", VDBgetCount(act_db));
        for (;LTRgetCurrentLevel(ltr)>deadlock_fifo_size; deadlock_fifo_size++) {
              FIFOput(deadlock_fifo, &n_deadlocks);
              }
           if (LTRgetCurrentLevel(ltr)==deadlock_fifo_size) {
              FIFOput(deadlock_fifo, &n_deadlocks); deadlock_fifo_size++;
              }   
           else {
            FIFOupdateElm(deadlock_fifo, LTRgetCurrentLevel(ltr),
            &n_deadlocks);
            }
        return new;
        }
                                      
static void gcb(int id, void *tag, idx_t dest) {
     trans_t trans; 
     int parent = LTRgetCurrent(ltr);
     trans.dest = dest;
     FIFOget(act_fifo, &trans.act);
     if (dest>LTRgetNumberOfObjects(ltr)) {
           fprintf(tty, "dest %d > %d n of objects\n",
           dest, LTRgetNumberOfObjects(ltr));
           abort();
           }
     if (dest==LTRgetNumberOfObjects(ltr)) {
         int err, idx, new;
         // fprintf(tty, "LTRput trans.dest %d parent %d dest = %d N = %d\n", 
         //  trans.dest, parent, dest,LTRgetNumberOfObjects(ltr) );
         if ((err=LTRput(ltr, parent, &trans, &idx))<0) errormsg("step:LTRput");
         if (err==1) UpdateUndoStackTree(idx);
         new = NewLabel(trans.act.lab);
         if (marklabels==1) { 
            if (new==1) LTRmakeMark(ltr, idx, NULL);
            } 
         }
     else if (spanningtree==0) {
        idx_t idx, val, new;
        if (trans.dest==dest) {
           idx=dest;
           }
        else idx = Idx(dest); 
        assert(idx>=0);
        LTRmakeJoin(ltr, idx, parent, &trans, &val);
        new = NewLabel(trans.act.lab);
        if (marklabels==1) { 
            if (new==1) LTRmakeMark(ltr, -val-2, NULL);
            } 
        }
        // fprintf(tty,"QQ: %d\n", idx);
     // fprintf(stderr,"%d %d %d\n", src, act, idx);
     }

static void Msg(char *title, int par) {
    return;
    /*
    int start, end, S, E, P, Q;
    LTRgetBounds(ltr, &start, &end, &S, &E, &P, &Q);
    LTRgetLevelInfo(ltr, LTRgetCurrentLevel(ltr),  NULL, NULL, NULL);
    fprintf(tty,
"%s: l=%d start=%d end=%d S=%d E=%d P=%d Q=%d current=%d par=%d lvs=%d\n", 
    title, LTRgetCurrentLevel(ltr), start, end, S, E, P,Q, LTRgetCurrent(ltr), par, 
    LTRgetNumberOfLeaves(ltr));
    */
    }

static void Truncat(void) {
     int visited, nactions;
     if (LTRgetCurrentLevel(ltr)>=LTRgetNumberOfAllLevels(ltr)-2) return; 
     LTRgetCumLevelInfo(ltr, LTRgetCurrentLevel(ltr), NULL, &visited, NULL);
     VDBtruncate(vdb, visited);
     if (visited != LTRgetNumberOfObjects(ltr)) 
     fprintf(tty, "visited = %d != %d N of Objects\n", visited,
          LTRgetNumberOfObjects(ltr));
     assert(visited==LTRgetNumberOfObjects(ltr));
     LTRtruncate(ltr);
     FIFOgetElm(act_db_fifo, LTRgetCurrentLevel(ltr), &nactions);
     FIFOgetElm(deadlock_fifo, LTRgetCurrentLevel(ltr), &n_deadlocks);
     // fprintf(tty, "Truncat: currentLevel = %d nactions = %d\n",
     // LTRgetCurrentLevel(ltr), nactions);
     VDBtruncate(act_db, nactions);
     PrintMarkers();
     }
                                            
step_t InitStepper() {
     int i;
     if (ltsfile) {
        adb = TDBcreate(0, NULL, NULL);
        vdb = VDBcreate(0, 1, NULL, NULL, NULL, gcb, NULL, NULL, NULL);
        if ((st = STcreateAUT(ltsfile, adb, ecb, icb, fecb, NULL))==NULL)
            return NULL;
        dest_fifo = FIFOcreateMemo(INITSIZE, sizeof(elm_t), NULL, NULL);
        }
     else {
        npars = MCRLgetNumberOfPars();
        nodes =  (vdb_t*) calloc(npars, sizeof(vdb_t));
        tdb = TDBcreate(0, NULL, NULL);
        adb = TDBcreate(0, NULL, NULL);
        for (i=2;i<npars;i++) 
        nodes[i] = VDBcreate(i, 2, NULL, NULL, NULL, NULL, NULL, NULL, NULL); 
        vdb = VDBcreate(0, npars>1?2:1, NULL, NULL, NULL, gcb, NULL, NULL, NULL);
        if ((st = STcreateMCRL(0, NULL, npars>1?2:1, adb, tdb, nodes, ecb, icb, fecb,
        NULL,NULL, 0, NULL, NULL)) == 0) return NULL;
        dest_fifo = FIFOcreateMemo(INITSIZE, sizeof(elm_t)*WIDTH, NULL, NULL);
        }
    act_db = VDBcreate(0, 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL);
    act_db_fifo = FIFOcreateMemo(INITSIZE, sizeof(int), NULL, NULL);
    deadlock_fifo = FIFOcreateMemo(INITSIZE, sizeof(int), NULL, NULL);
    act_fifo = FIFOcreateMemo(INITSIZE, sizeof(act_t), NULL, NULL);
    undo_fifo = FIFOcreateMemo(INITSIZE, sizeof(act_t), NULL, NULL);
    undo_fifo = FIFOcreateMemo(INITSIZE, sizeof(int), NULL, NULL);
    trans_fifo = FIFOcreateMemo(INITSIZE, sizeof(trans_t), NULL, NULL);
    ltr = LTRcreateMemo(sizeof(trans_t), NULL, NULL);
    return st;
    }
        
static void PrintParentAction(idx_t parent, int cnt) {
     trans_t trans;
     LTRgetElm(ltr, parent, &trans);
     if (trans.act.lab>=0) {
       char *actname = Act2String(trans.act.lab);
       DepthContent(actname, trans.act.smd+1, cnt);
       }
     else {
       DepthContent("#init#", 0, cnt);
       }
     }
     
static int PrintAction(trans_t *trans, int current, int leaf, int marked) {
    char *actname = trans->act.lab>=0?Act2String(trans->act.lab):"";
    printUTF(stdout, button);
    printUTF(stdout, actname);
    // fprintf(tty, "current = %d\n", current);
    writeintUTF(stdout, current);
    printUTF(stdout, marked==1?MCRLtrue:MCRLfalse);
    printUTF(stdout, leaf?"red": current==LTRgetCurrent(ltr)?"gray": "black");
    // printUTF(stdout, leaf?MCRLtrue:MCRLfalse);
    return 0;
    }
    
static int PrintBackAction(trans_t *trans, int join, int current, int length,
int leaf, int marked) {    
    char *actname = trans->act.lab>=0?Act2String(trans->act.lab):"";
    printUTF(stdout, button);
    printUTF(stdout, actname);
    writeintUTF(stdout, -join-2);
    printUTF(stdout, marked==1?MCRLtrue:MCRLfalse);
    // fprintf(tty, "%d > %d\n",LTRgetLevel(ltr, current), length); 
    printUTF(stdout, leaf?"red":
    LTRgetLevel(ltr, current)>length?"black": 
    trans->act.lab==deadlock?"magenta":"blue");
    // printUTF(stdout, MCRLfalse);
    return 0;
    }

static void SendError(ATerm par) {
     printUTF(stdout, "%s", ATwriteToString(MCRLprint(par)));
     printUTF(stdout, "%s ", "");
     printUTF(stdout, "%s ", "");
     }
               
static void SendState(idx_t idx, int update) {
    term_t *data;
    elm_t elm[2];
    int  i;
    ATermList pars;
    printUTF(stdout,update?updatestate:state);
    if (stateList) {
       VDBget(vdb, elm, idx);
       data = STunfold(st, elm);  
       for (i=0, pars = MCRLgetListOfPars();
             !ATisEmpty(pars);pars=ATgetNext(pars),i++) { 
           RWassignVariable(ATgetAFun(ATgetArgument(
	   (ATermAppl) ATgetFirst(pars),0)), data[i], NULL, 0);
           } 
      // ATfprintf(stderr,"%t\n", stateList);   
      for (pars = stateList;
             !ATisEmpty(pars);pars=ATgetNext(pars)) { 
          ATerm par = ATgetFirst(pars);
          if (ATisQuoted(ATgetAFun((ATermAppl) par))) {
            ATerm t = RWrewrite(par);
            if (t) {
              printUTF(stdout, "%s", ATwriteToString(MCRLprint(par)));
              printUTF(stdout, "%s", ATgetName(MCRLgetSort(par)));
              printUTF(stdout, "%s", ATwriteToString(MCRLprint(t)));
              }
            else SendError(par);
            }
          else SendError(par);
	 }
       }
    printUTF(stdout, finish);
    fflush(stdout);
    }

void SetSendState(int sendState) {
     sendstate = sendState;
     if (sendstate) SendState(LTRgetCurrent(ltr), 0);
     }

void UpdateState(int row, char *term) {
     ATerm t = MCRLparse(term);
     if (row>0) {
	  stateList = ATreplace(stateList, t?t:ATmake("<appl>", term), 
               row-1);
	  SendState(LTRgetCurrent(ltr), 0);
	  }
     else {
	stateList = ATinsert(stateList, t?t:ATmake("<appl>", term));
	SendState(LTRgetCurrent(ltr), 1);  
        }
     }
                               
static int SendActions(idx_t parent) {
    int cnt = 0;
    /* fprintf(tty,"1:Sendaction parent = %d\n", parent); */
    printUTF(stdout,displayheader);
    cnt += LTRrunFromParent(ltr, parent, (parent_cb) PrintAction);
    cnt += LTRrunJoinsFromParent(ltr, parent, (join_cb) PrintBackAction);
    printUTF(stdout, finish);
    printUTF(stdout, smdheader);
    LTRrunFromParent(ltr, parent, (parent_cb) PrintSummand);
    LTRrunJoinsFromParent(ltr, parent, (join_cb) PrintBackSummand);
    printUTF(stdout, finish);
    PrintParentAction(parent, cnt); 
    fflush(stdout);
    /* fprintf(tty,"21:Sendaction cnt = %d\n", cnt); */
    if (sendstate) SendState(parent, 0);
    return cnt;    
    }
  
void StepState(int state) {
     elm_t elm[WIDTH];
     VDBget(vdb, elm, state);
     /* fprintf(tty, "Step1 state = %d %d %d\n", state, elm[0], elm[1]); */ 
     if (STexplore(st, &state, elm)<0) errormsg("");
     /* fprintf(tty, "Step2 state = %d %d %d\n", state, elm[0], elm[1]); */
     }
         


void Down() {
     Redo(LTRgetParent(ltr, LTRgetCurrent(ltr)));
     }
                             
void Undo() {
     int parent;
     Msg("Undo1", FIFOgetCount(undo_fifo));
     FIFOpop(undo_fifo, 1);
     FIFOgetElm(undo_fifo, FIFOgetCount(undo_fifo)-1, &parent);
     LTRsetCurrent(ltr, parent);
     if (FIFOpop(undo_fifo,1)>=0) {
           int current;
           if (FIFOgetCount(undo_fifo)>0) {
             FIFOgetElm(undo_fifo, FIFOgetCount(undo_fifo)-1, &current);
             if (LTRgetParent(ltr, current)==parent) LTRsetCurrent(ltr, current);
             }
           FIFOunpop(undo_fifo);
           }
     SendActions(parent); 
     LTRsetCurrent(ltr, parent);
     InfoButton();
     Active(MCRLtrue);
     // fprintf(tty,"Undo test2 current = %d undo_fifo = %d\n",
     //   parent, FIFOgetCount(undo_fifo));
     }
/*
void PrintArray(void) {
     int *a = (int*) FIFOgetArray(undo_fifo), i,
     n = INITSIZE;
     for (i=0;i<n;i++) fprintf(tty, "%d ", a[i]);
     fprintf(tty,"\n");
     }
*/

static int CurrentValue(int current) { 
     int val1 = -1, val2 = -1, val0 = -1;
     if (FIFOgetCount(undo_fifo)>1) {
         FIFOgetElm(undo_fifo, FIFOgetCount(undo_fifo)-2, &val1);
         // fprintf(tty,"1:val1 = %d\n", val1);
         }
     if (val1==current) {
     if (FIFOgetCount(undo_fifo)>2) {
         FIFOgetElm(undo_fifo, FIFOgetCount(undo_fifo)-3, &val2);
         // fprintf(tty,"2:val0 = %d current = %d parent = %d\n", val0, current, 
         // LTRgetParent(ltr, val1));
         }
         }
     if (val2>=0 && LTRgetParent(ltr, val2)!=val1) val2 = -1;
     if (val2 == -1) {
         if (FIFOgetCount(undo_fifo)>0) {
         FIFOgetElm(undo_fifo, FIFOgetCount(undo_fifo)-1, &val0);
         // fprintf(tty,"1:val0 = %d pt = %d\n", val0, 
         // FIFOgetCount(undo_fifo)-1);
         }
         if (val0>=0 && LTRgetParent(ltr, val0)!=current) val0 = -1;
         }
     
    /* fprintf(tty,"val1 = %d current = %d parent = %d\n", val1, current,
           LTRgetParent(ltr, current)); */
     if (current>=0) {
        FIFOput(undo_fifo, NULL); 
        if (val1 ==current && LTRgetCurrent(ltr)==LTRgetParent(ltr, current)) 
             FIFOpop(undo_fifo, 1);
        else {
             FIFOput(undo_fifo, &current);
             // fprintf(tty, "FIFOput1 current = %d count = %d\n",
             // current, FIFOgetCount(undo_fifo));
             }
        }
     else if (current == -1) {
        if (FIFOgetAllCount(undo_fifo)-FIFOgetCount(undo_fifo)>=1) {
           FIFOgetElm(undo_fifo,FIFOgetCount(undo_fifo), &current);
        // fprintf(tty,"Redo1: current = %d count = %d\n", 
        // current, FIFOgetCount(undo_fifo));
            FIFOunpop(undo_fifo);
            }
        }
     else {
        int leaf = -current-2;
        current = LTRgetJoinDestination(ltr, leaf);
        FIFOput(undo_fifo, NULL);
        FIFOput(undo_fifo, &current);
        // fprintf(tty, "FIFOput2 current = %d count = %d\n",
        //     current, FIFOgetCount(undo_fifo));
        }
     if (val2>=0) LTRsetCurrent(ltr, val2);
     else
     if (val0>=0) LTRsetCurrent(ltr, val0);
     else LTRsetCurrent(ltr, current);
     // fprintf(tty, "CurrentVale count = %d\n", FIFOgetCount(undo_fifo));
     return current;
     }
     
                   
void Redo(int current) {
     Msg("Redo1 %d\n", current);
     current = CurrentValue(current);
     if (LTRisLeaf(ltr, current)) {
         StepRank(current);
         TruncateUndoStack(current); 
         };
     SendActions(current);
     if (LTRsetCurrent(ltr, current)<0) errormsg("Redo2");
     InfoButton();
     Active(MCRLtrue);
     Msg("Redo2", current);
     }
     
void Home() {
     while (LTRsetCurrent(ltr, LTRgetParent(ltr, LTRgetCurrent(ltr)))==0) {
        int current = LTRgetCurrent(ltr);
        FIFOput(undo_fifo, &current);
        }  
     }
       
void Reset() {
     FIFOreset(undo_fifo); 
     FIFOreset(trans_fifo);
     LTRreset(ltr);
     last_act = "init"; last_smd = -1;
     VDBtruncate(vdb, 0);
     VDBtruncate(act_db, 0);
     if (STexploreInitialState(st, NULL)<0) errormsg("Server");
     LTRsetCurrent(ltr, 0);
     errorreset();
     printmsg("reset");
     StepState(0);
     PrintMarkers();
     }
          
static int SearchFirstChild(trans_t *trans, int current, int leaf, int marked) {
     if (leaf) return 0;
     Redo(current);
     return -1;
     }
        
void Child() {
     LTRrunFromParent(ltr, LTRgetCurrent(ltr), (parent_cb) SearchFirstChild);
     }
     
               
void Forward() {
     FIFOreset(undo_fifo);
     Redo(LTRgetCurrent(ltr)+1);
     }
     
void Back() {
     FIFOreset(undo_fifo);
     Redo(LTRgetCurrent(ltr)-1);
     }
     
static void TruncateUndoStack(int current) {
     int pt = FIFOgetCount(undo_fifo)-1;
     for (;pt>=0;pt--) {
        int val;
        FIFOgetElm(undo_fifo, pt, &val);
        if (val > current) break;
        } 
     // fprintf(tty,"Truncate undostack N = %d\n", pt);
     if (pt>=0) FIFOpop(undo_fifo, -pt-1);
     // all elements of undo_fifo <= current
     // all levels(elements) <= level(current)
     }

#define INSPECT 1000  
#define DSIZE 100 
      
static int GenerateLevel(trans_t *trans, int current, int leaf, int marked) {
    static int cnt = 0;
    if (leaf) {
        StepRank(current);
        cnt++;
        /*
        fprintf(tty, "cnt = %d Genlevel: current = %d leaf = %d\n", 
        cnt, current, leaf);
        */
        }
    if (cnt>=INSPECT) {
        int n, err;
        char data[DSIZE];
        
        if ((n=readUTF(stdin, data, DSIZE))<0) exit(1); /* Reads End token */
        printUTF(stdout, continueheader);
        printUTF(stdout, finish);
        fflush(stdout);
        E(readUTF(stdin, data, DSIZE)); 
        if (strcmp(continueheader, data)==0) {
          int m;
          if (readintUTF(stdin, &m)<0) errormsg("readintUTF");
          if (m>0) {
              printmsg("interrupted"); 
              interrupted = 1;
              InfoButton();
              return -1;
              }
          }
        else errormsg("Read error %s", data);
        cnt = 0;
        InfoButton();
        }
    return 0;
    } 
                       
void LevelUp() {
     int current = LTRgetCurrent(ltr), end;
     interrupted = 0;
     if (current>= LTRgetNumberOfObjects(ltr)) return;
     FIFOreset(undo_fifo);
     LTRrunFromParent(ltr, -1, (parent_cb) GenerateLevel);
     LTRsetCurrent(ltr, current);
     LTRgetBounds(ltr, NULL, &end, NULL, NULL, NULL, NULL);
     PrintMarkers();
     if (end>= LTRgetNumberOfObjects(ltr)) {
         Redo(current);
         return;
         }
     Redo(end);
     }

     
idx_t Explore() {
     int end;
     FIFOreset(undo_fifo);
     interrupted = 0;
     marklabels = 1;
     LTRgetBounds(ltr, NULL, &end, NULL, NULL, NULL, NULL);
     while (end<LTRgetNumberOfObjects(ltr)) {
       // fprintf(tty, "end = %d\n", end);
       LTRsetCurrent(ltr, end);
       PrintMarkers();
       LTRrunFromParent(ltr, -1, (parent_cb) GenerateLevel);
       InfoButton();
       if (interrupted) break;
       LTRgetBounds(ltr, NULL, &end, NULL, NULL, NULL, NULL);
       };
     marklabels = 0;
     PrintMarkers();
     LTRgetBounds(ltr, &end, NULL, NULL, NULL, NULL, NULL);
     return end;
     }
     
void LevelDown() {
     FIFOreset(undo_fifo);
     LTRsetCurrent(ltr, LTRgetParent(ltr, LTRgetCurrent(ltr)));
     Truncat();
     Redo(LTRgetCurrent(ltr));
     }
                      
static void StepRank(int current) {
     trans_t trans;
     Msg("Steprank 1", current);
     if (current>=0) {
        LTRsetCurrent(ltr, current);
        } 
     else if (current == -1) {
        LTRsetCurrent(ltr,LTRgetCurrent(ltr));
        } else errormsg("System error");
     if (LTRget(ltr, &trans)<0) errormsg("Error ltrget");
     if (trans.act.lab>=0) {
         last_act = Act2String(trans.act.lab);
         last_smd = trans.act.smd;
         }
     Truncat(); 
     StepState(trans.dest);
     Msg("Steprank 2", current);
     }
          
void SetMarker(idx_t join) {
     LTRmakeMark(ltr, join,  NULL);
     PrintMarkers();
     }

static int SendLabel(char *name) {
     // fprintf(tty, "name = %s\n", name);
     printUTF(stdout, name);
     return 0;
     }
     
void SendLabels() {
     int i, n = VDBgetCount(act_db);
     printUTF(stdout, labelheader);
     // ATfprintf(tty, "QQ:%t\n", ATindexedSetElems(adb));
     for (i=0;i<n;i++) {
       int v;
       VDBget(act_db, &v, i);
       // fprintf(tty,"Value i= %d v = %d %s\n", i, v, Act2String(v));
       printUTF(stdout, Act2String(v));
       }
     for (i=0;i<n;i++) {
       int v;
       VDBget(act_db, &v, i);
       // fprintf(tty,"Value i= %d v = %d %s\n", i, v, Act2String(v));
       writeintUTF(stdout, v);
       }
     printUTF(stdout, finish);
     fflush(stdout);
     }

static int *labels, nlabels;

static int search(int idx, trans_t *trans) {
     int i;
     // fprintf(tty,"nlabels = %d\n", nlabels);
     for (i=0;i<nlabels;i++) {
       if (trans->act.lab==labels[i]) break;
       }
    /* if (i<nlabels) fprintf(tty,"Search %d %s target %d %s\n", 
    trans->act.lab, trans->act.lab>=0?Act2String(trans->act.lab):"",
    labels[i], labels[i]>=0?Act2String(labels[i]):"");*/
     if (i<nlabels) {
         if (idx>=0) LTRsetCurrent(ltr, LTRgetParent(ltr, idx));
         else {
           LTRsetCurrent(ltr, LTRgetJoinSource(ltr, -idx-2));
           }
         LTRmakeMark(ltr, idx, NULL);
         }
     return 0;
     }
     
void Search(int n, int *sels) {
     labels = sels; nlabels = n;
     LTRresetMarks(ltr);
     // fprintf(tty,"Search\n");
     LTRrunThroughObjects(ltr, (object_cb) search);
     PrintMarkers();
     }

void Clear(void) {
     LTRresetMarks(ltr);
     PrintMarkers();
     SendActions(LTRgetCurrent(ltr));
     }

int eachFile(char *path) {
     names = ATinsert(names, ATmake("<str>", path));
     return 0;
     }
              
int LoadTraces(void) {
     ATermList namespt;
     int nPars = MCRLgetNumberOfPars();
     if (ForEachFileInDir(trc, eachFile)<0) errormsg("for each file in dir");
     names = ATreverse(names);
     // ATfprintf(tty, "names = %t\n", names);
     for (namespt = names;!ATisEmpty(namespt);namespt=ATgetNext(namespt)) {
        FILE *fp; char version[80]; int current, npars;
        char *fname = ATgetName(ATgetAFun(ATgetFirst(namespt)));
        if (!(fp = fopen(fname,"r"))) return mkerror(ERR_NULL, fname);
        fscanf(fp, "%d %s", &npars, version);
        if (npars != nPars) errormsg(
        "Expected number of pars: %d != %d found number of pars",
        nPars, npars);
        ATtablePut(trace, ATgetFirst(namespt), (ATerm) MCRLparseTrace(fp, &current));
        fclose(fp);
        }
     while (!ATisEmpty(names)) {
       DECLA(ATerm, a, nPars);
       for (namespt = names;!ATisEmpty(namespt);namespt=ATgetNext(namespt)) {
          ATermList transitions = 
            ATgetNext((ATermList) ATtableGet(trace, ATgetFirst(namespt)));
          idx_t idx; int i; 
          for (i=0;i<nPars;i++, transitions=ATgetNext(transitions)) { 
             a[i] = ATgetFirst(transitions);
             }
          if (ATisEmpty(transitions)) spanningtree = 0;
          else spanningtree = 1;
          idx = VDBput(vdb, STfold(st,  a),  NULL);
          idx = Idx(idx);
          if (idx<0) {
                errorreset();
                printmsg(
                "Trace in file %s is ignored because",
                ATgetName(ATgetAFun(ATgetFirst(namespt))));
                names = ATremoveElement(names, ATgetFirst(namespt));
                ATtablePut(trace, ATgetFirst(namespt), (ATerm) ATempty);
                }
          else {  
               if (LTRisLeaf(ltr,idx)) StepRank(idx);
               if (ATisEmpty(transitions)) {
                   names = ATremoveElement(names, ATgetFirst(namespt));
                   LTRmakeMark(ltr, idx, NULL); 
                   } 
               ATtablePut(trace, ATgetFirst(namespt), (ATerm) transitions);
               // ATfprintf(tty, "TablePut %t\n", transitions);
               }
          }
       }
     // fprintf(tty,"LoadTraces finished\n");
     spanningtree = 0;
     PrintMarkers();
     return 0;
     } 

static FILE *tfp;
 
static int PrintStep(void *obj, idx_t current) {
    term_t *data;
    trans_t *trans = (trans_t*) obj;
    int n = MCRLgetNumberOfPars(), i;
    elm_t elm[2];
    idx_t dest = trans->dest;
    fprintf(tfp, "%s ", trans->act.lab>=0?
    Act2String(trans->act.lab):"init");
    VDBget(vdb, elm, dest);
    data = STunfold(st, elm);
    for (i=0;i<n;i++) { 
       // ATfprintf(tty,"%t\n", data[i]);
       ATfprintf(tfp, "%t ", MCRLprint(data[i]));
       }
    fprintf(tfp,"\n");
    return 0;
    }
 
static int DumpTrace(int code, int join, idx_t endpoint) {
     char name[256], *lastact;
     trans_t trans;
     if (join<0) {
         LTRgetJoinElm(ltr, -join-2, &trans);
         }
     else {
         LTRgetElm(ltr, join, &trans);
         }
     lastact = trans.act.lab>=0?Act2String(trans.act.lab):"#init";
     sprintf(name,"%s/%s.%d", outtrc, lastact, code);
     if (!(tfp=fopen(name,"w"))) errormsg("%s", name);
     fprintf(tfp,"%d %s\n", ltsfile?0:MCRLgetNumberOfPars(), version);
     LTRsetCurrent(ltr, endpoint);
     LTRrunThroughTrace(ltr, (trace_cb) PrintStep);
     if (strcmp(lastact, "#deadlock#")) {
         elm_t elm[2];
         term_t *data;
         idx_t dest = trans.dest;
         int n = MCRLgetNumberOfPars(), i;
         VDBget(vdb, elm, dest);
         data = STunfold(st, elm);
         fprintf(tfp, "%s ", lastact);
         for (i=0;i<n;i++) { 
           // ATfprintf(tty,"%t\n", data[i]);
           ATfprintf(tfp, "%t ", MCRLprint(data[i]));
         }
         fprintf(tfp,"\n");
         fprintf(tfp, "%d\n", 1);
         }
     else fprintf(tfp, "%d\n", 0);
     fclose(tfp);
     return 0;
     }
     
int SaveTraces(void) {
     if (CreateEmptyDir(outtrc, DELETE_ALL)<0)
     return mkerror(ERR_NULL, "Cannot create empty directory %s", outtrc);
     LTRrunThroughMarks(ltr, DumpTrace);
     // fprintf(tty,"Traces saved\n");
     errorreset();
     printmsg("traces are saved in file %s", outtrc);
     return 0;
     }
     
static FILE *afp;

static int saveTransition(int idx, trans_t *trans) {
    if (idx>=0) {
      if (trans->act.lab>=0) fprintf(afp,"(%d,\"%s\",%d)\n", LTRgetParent(ltr, idx), 
      Act2String(trans->act.lab), idx);
      }
    else {
      int leaf = -idx - 2;
      fprintf(afp, "(%d,\"%s\",%d)\n", 
      LTRgetJoinSource(ltr, leaf),
      trans->act.lab>=0?Act2String(trans->act.lab):"init",
      LTRgetJoinDestination(ltr, leaf));
      }
    return 0;
    }
      
int SaveTransitions(void) {
    int nstates, ntransitions;
    if (!(afp=fopen(autfile,"w"))) errormsg("%s", autfile);
    LTRgetTotalLevelInfo(ltr, &nstates, NULL, &ntransitions); 
    fprintf(afp,"des (0, %d, %d)\n", ntransitions-1, nstates);
    LTRrunThroughObjects(ltr, (object_cb) saveTransition);
    fclose(afp);
    printmsg("Transitions saved in %s", autfile);
    return 0;
    }
