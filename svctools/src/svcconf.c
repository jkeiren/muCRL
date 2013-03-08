/* SVC tools -- the SVC (Systems Validation Centre) tool set

   Copyright (C) 2000  Stichting Mathematisch Centrum, Amsterdam,
                       The  Netherlands

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

   $Id: svcconf.c,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $
   This is a local confluence checker conform the Groote/Pol
   algorithm.  (starting date: 2/12/99) */

#include "svcconf.h"

extern int SVCerrno;

static SVCbool indexed;

static SVCint no_states;
static SVCint no_transitions;
SVCstateIndex initial_state;

static SVCfile infile;

static SVCint stack=0;
static statetype *states;
static transitiontype *transitions;
static SVClabelIndex tau_label=0;

static int streq(char * s1,char *s2)
{ return (strcmp(s1,s2)==0);
}

static SVCint hashtablesizeMinus1=0;

static SVCint *hashtable;

#define HASHFACTOR 120  /* hashtable has size HASHFACTOR/100*no_transitions */
#define COMMENT    "reduced using local confluence by"
#define REDFILE_EXT ".red"
#define OUTFILE_EXT ".svc"
#define  INFILE_EXT ".svc"

static char *programName ;


static unsigned long approximatepowerof2(unsigned long n)
{ /* return for the 2^m-1 larger than n, but
     smallest size must at least be 127 */
  int i;
  n=n>>7;
  for(i=0 ; n>0 ; i++){n=n>>1;}
  for(n=127 ; i>0 ; i--)
   { n=(n<<1)|1;
   }

  return n;
}

#define SomePrime 23

static SVCint hashkey(SVCstateIndex from, 
           SVClabelIndex lab, SVCstateIndex to)
{ return (from*to*lab*SomePrime) & hashtablesizeMinus1;
}


static int in_hashtable(SVCstateIndex from, 
           SVClabelIndex lab, SVCstateIndex to)
{ 
  register SVCint t;


  for(t=hashtable[hashkey(from,lab,to)] ; (t!=0) ; )
    { if ((transitions[t].source==from) &&
          (transitions[t].target==to) &&
          (transitions[t].label==lab))
      { 
        return t;
      }
      t=transitions[t].hashtable_next;
    }

  return 0;
}

static void add_to_hashtable(SVCint i)
{ SVCint key;
  key=hashkey(transitions[i].source,
              transitions[i].label,
              transitions[i].target);
  transitions[i].hashtable_next=hashtable[key];
  hashtable[key]=i;
}

static void empty_hashtable(void)
{ SVCint i;
  for(i=0 ; i<=hashtablesizeMinus1 ; i++ )
  { hashtable[i]=0; }
}


/*******************  read_file  **********************/

static int read_file(char *filename)
{ SVCint i=0;
  SVCstateIndex to,from;
  SVClabelIndex label;
  SVCparameterIndex parameter;

  if (SVCopen(&infile,filename,SVCread, &indexed)!=0) { 
     fprintf(stderr,"Error opening file %s: %s \n",filename, SVCerror(SVCerrno));
     return 0; }
  no_states=SVCnumStates(&infile); 
  states=malloc((no_states+1)*sizeof(statetype));
  if (states==NULL)
   { fprintf(stderr,"\nInsufficient memory to store states from %s \n",filename);
     return 0; }
  for(i=0 ; i<=no_states ; i++)
  { states[i].list1=0;
    states[i].list2=0;
    states[i].old_index=0;
  }

  no_transitions=SVCnumTransitions(&infile); 
  transitions=malloc((no_transitions+1)*sizeof(transitiontype));

  if (transitions==NULL)
   { fprintf(stderr,"Insufficient memory to store transitions from %s \n",filename);
     return 0; }

  hashtablesizeMinus1=
       approximatepowerof2(1+(((no_transitions+1)*HASHFACTOR)/100));
  hashtable=calloc(hashtablesizeMinus1+1,sizeof(SVCint));

  if (hashtable==NULL)
   { fprintf(stderr,"Insufficient memory to create a hashtable for transitions from %s \n",filename);
     return 0; }

  for(i=1; i<=no_transitions ; i++)
  { if (SVCgetNextTransition(&infile,&from,&label,&to,&parameter)!=1)
     { fprintf(stderr,"Cannot retrieve all transitions from: %s\n",filename);
       fprintf(stderr,"Reason: %s\n",SVCerror(SVCerrno));
       return 0; }
    transitions[i].source=from+1;
    transitions[i].target=to+1;
    transitions[i].label=label;
#ifdef PARAMETER
    transitions[i].parameter=parameter;
#endif 
    transitions[i].candidate=1;
    transitions[i].stack_next=0;
    transitions[i].on_stack=0;
    transitions[i].list2_next=0;
    transitions[i].list1_next=0;
  }    

  tau_label=SVCaterm2Label(&infile,ATmake("i"));
  if (tau_label<0) {
    fprintf(stderr,"File (%s) doesn't contain internal steps (%s)\n",
	    filename,"i");
    return 0;
  }
  return 1;
}

/**************  compact_data  ******************/


static void mark_states_recursively(SVCstateIndex s)
{ 
  SVCint t;

  states[s].list2=1;
  
  for(t=states[s].list1 ; t!=0 ; )
  { if (states[transitions[t].target].list2==0)
    {  mark_states_recursively(transitions[t].target);
    }
    t=transitions[t].list1_next;
  }
}

static void mark_states(SVCstateIndex s)
{ 
  SVCint i;

  /* below we use the variable list2 to mark
     those states that are reachable from the initial
     state. First set list1 and list2 to 0 */

  for(i=1 ; i<=no_states ; i++)
   { states[i].list1=0; 
     states[i].list2=0; }

  /* now put all transitions as outgoing transitions in list1 */

  for(i=1 ; i<=no_transitions ; i++)
  { transitions[i].list1_next=states[transitions[i].source].list1;
    states[transitions[i].source].list1=i;
  }

  mark_states_recursively(s);
}

static void compact_data(void)
{ 
  SVCint i,back_index;
  SVCstateIndex new_source, new_target;
  SVClabelIndex new_label;

  empty_hashtable();
  mark_states(initial_state);

  /* each state has now in list2 a value equal 1, if
     it is reachable, or 0 otherwise */

  back_index=0;
  for(i=1 ; i<=no_states ; i++)
  { if (states[i].list2==1)
     { /* state survives */
       back_index++;
       states[i].list2=back_index; /* back_index is the new index of
                                      state i */
       states[back_index].old_index=states[i].old_index;
     }
  }

  no_states=back_index;
  initial_state=states[initial_state].list2;

  back_index=0;
  for( i=1 ; i<=no_transitions ; i++)
   { if (states[transitions[i].source].list2!=0)
      { 
        new_source=states[transitions[i].source].list2;
        new_target=states[transitions[i].target].list2;
        new_label=transitions[i].label;
        if (in_hashtable(new_source,new_label,new_target)==0)
         { back_index++;
           transitions[back_index].source=new_source;
           assert(new_source<=no_states);
           transitions[back_index].target=new_target;
           transitions[back_index].label=new_label;
#ifdef PARAMETER
           transitions[back_index].parameter=transitions[i].parameter;
#endif 
           add_to_hashtable(back_index);
         }
     }
   }
  no_transitions=back_index;

  states=realloc(states,(no_states+1)*sizeof(statetype));
  if (states==NULL)
    { ATerror("Reducing state array fails\n");
    }

  transitions=realloc(transitions,(no_transitions+1)*sizeof(transitiontype));
  if (transitions==NULL)
  { ATerror("Reducing transition array fails\n");
  } 
}

/**************  write_file  ******************/

static unsigned int write_file(char *outfilename)
{ SVCfile outfile;
  SVClabelIndex l;
  SVCparameterIndex p;
  SVCstateIndex s_new;
  SVCint i;
  char *stringptr, *comments;
  ATerm term;
  SVCbool new;
  ATerm t=NULL;


  if (SVCopen(&outfile,outfilename,SVCwrite, &indexed)!=0)
   { ATerror("Cannot open file %s: %s\n",outfilename, SVCerror(SVCerrno));
   }

  stringptr=SVCgetComments(&infile);
  comments=(char*)malloc(sizeof(char)*(strlen(COMMENT)+2+
                                       strlen(programName)+1+
                                       strlen(stringptr)+2));
  sprintf(comments, "%s; %s %s\n", stringptr, COMMENT, programName);
  SVCsetComments(&outfile,comments);
  free(comments);
  stringptr=SVCgetType(&infile);
  SVCsetType(&outfile,stringptr);
  stringptr=SVCgetVersion(&infile);
  SVCsetVersion(&outfile,stringptr);
  SVCsetCreator(&outfile,programName);


  
#ifndef PARAMETER
  p=SVCnewParameter(&outfile,ATmake("Dummy_parameter"),&new);
  if (p<0)
    ATerror("Cannot create dummy parameter in outfile");
#endif

  for(i=1 ; i<=no_states ; i++)
  { term=SVCstate2ATerm(&infile,(SVCstateIndex)states[i].old_index-1);
    if (term==NULL)
    { ATerror("Erroneous state index %ld in input file\nReason: %s\n",
           states[i].old_index,SVCerror(SVCerrno));
    }
    s_new=SVCnewState(&outfile,term,&new)+1;
    if ((s_new==0) || (new==0))
    { ATerror("Inserting state in outfile appears to be in error.\nReason: %s\n",
                    SVCerror(SVCerrno));
    }
    states[i].list2=s_new;
  }

  /* each state has now in list2 the index of
     the state in outfile, or 0 if the state is not 
     reachable */

  initial_state=states[initial_state].list2-1;
  SVCsetInitialState(&outfile,initial_state);

  for(i=1 ; i<=no_transitions ; i++)
   { if (states[transitions[i].source].list2!=0)
      { t=SVClabel2ATerm(&infile,transitions[i].label);
        l=SVCnewLabel(&outfile,t,&new);
        if (l<0)
	 { fprintf(stderr,"Cannot create extra label in %s\n",outfilename);
           fprintf(stderr,"Reason: %s\n",SVCerror(SVCerrno));
           return 0;
	 }
#ifdef PARAMETER
        t=SVCparameter2ATerm(&infile,transitions[i].parameter);
        p=SVCnewParameter(&outfile,t,&new);
        if (p<0)
	 { fprintf(stderr,"Cannot create extra parameter in %s\n",outfilename);
           fprintf(stderr,"Reason: %s\n",SVCerror(SVCerrno));
           return 0;
	 }
#endif
        if (SVCputTransition(&outfile,
             states[transitions[i].source].list2-1,l,
             states[transitions[i].target].list2-1,p)!=0)
         { fprintf(stderr,"Fail to add transition to %s",outfilename);
           fprintf(stderr,"Reason: %s\n",SVCerror(SVCerrno));
           return 0;
         }
      }
   }
  SVCclose(&infile);
  SVCclose(&outfile);
  return 1;
}

/**************  determine_confluent_taus  ****/

static int confluent(SVCint t, SVCint t_tau)
{ SVCint t_tau1,tr;
  SVCstateIndex s,s_tau;
  SVClabelIndex l;
  transitiontype trans;

  trans=transitions[t];
  s=trans.target;
  l=trans.label;
  s_tau=transitions[t_tau].target;  
  assert(transitions[t_tau].label==tau_label);
  assert(transitions[t].source==transitions[t_tau].source);

  if (l==tau_label) 
   { if (s==s_tau) 
        return 1;
     tr=in_hashtable(s,tau_label,s_tau);
     if ((tr>0) && (transitions[tr].candidate)) 
     { return 1; } 
   }

  if (in_hashtable(s_tau,l,s)>0)
     return 1;

  for (t_tau1=states[s].list2 ; (t_tau1!=0) ; )
  { trans=transitions[t_tau1];
    if ((trans.candidate) &&  /* 7/2/00 JFG */
        (in_hashtable(s_tau,l,trans.target)>0))
    { return 1;
    }
    t_tau1=trans.list2_next;
  }

  return 0;
}


static void check_backward_confluence(SVCint t)
{ SVCint t_tau,t_a, i;
  short some_transition_not_confluent=0;  

  /* First check confluence with respect to those
     tau transitions starting from the source of t */
  for( t_tau=states[transitions[t].source].list2 ;
       t_tau!=0 ; )
    { if ((transitions[t_tau].candidate==1) && 
          (confluent(t,t_tau)==0))
      { some_transition_not_confluent=1;
        transitions[t_tau].candidate=0;
      } 
      t_tau=transitions[t_tau].list2_next;
    }

  if (some_transition_not_confluent)
    { /* put all transitions ending in the source of
         t back on the stack */
      for( t_a=states[transitions[t].source].list1 ;
           t_a!=0 ; )
        { if (transitions[t_a].on_stack==0)
	  { transitions[t_a].on_stack=1;
            transitions[t_a].stack_next=stack;
            stack=t_a; 
          }
          t_a=transitions[t_a].list1_next;
           
        }
    }
}


static void determine_confluent_taus(void)
{ SVCint t;

  for( ; (stack!=0) ; )
    { t=stack;
      /* fprintf(stderr,"A: %ld-%ld->%ld (%ld)\n",transitions[t].source,
             transitions[t].label,transitions[t].target,t); */

      stack=transitions[t].stack_next;
      transitions[t].on_stack=0;
      check_backward_confluence(t);
    }
}


/**************  apply_tau_prioritisation  ****/

static void apply_tau_prioritisation(void)
{ SVCint t, back_index;
  SVCint i,j;

  /* First go trough all states, and put a
     1 in list2 if the state has a confluent
     tau_transition. Otherwise put a zero in 
     list2. En passant, set list1
     to 0, unless the state has a confluent list2,
     in which case this tau is put in list1. We assume
     all outgoing tau transitions are in list2 */

  for( i=1 ; i<=no_transitions ; i++)
  { transitions[i].list1_next=0;
  } 

  for( i=1 ; i<=no_states ; i++)
  { 
    for(t=states[i].list2 ; t!=0 ; )
    { assert(transitions[t].label==tau_label);
      if (transitions[t].candidate==1)
      { assert(transitions[t].list1_next==0);
        transitions[t].list1_next=1;
        states[i].list2=1;
        t=0;
      } 
      else
      { t=transitions[t].list2_next;
        states[i].list2=0;
      }
    }
  }

  /* second remove all transitions,
     as outgoing transitions, in all those states with
     the variable list2 set to 1. */

  back_index=0;
  for( i=1 ; i<=no_transitions ; i++)
  { if ((states[transitions[i].source].list2==0) || 
          /* state has no confluent outgoing tau */
        (transitions[i].list1_next==1))
          /* transition i is confluent outgoing tau */
    { back_index++;
      transitions[back_index].source=transitions[i].source;
      transitions[back_index].target=transitions[i].target;
      transitions[back_index].label=transitions[i].label;
#ifdef PARAMETER
      transitions[back_index].parameter=transitions[i].parameter;
#endif
    }
  }
  no_transitions=back_index; 
  transitions=realloc(transitions,(no_transitions+1)*sizeof(transitiontype));
  if (transitions==NULL)
  { ATerror("Reducing transition array fails\n");
  }
}

/**************  setup_data_structure();  *****/

static void setup_data_structure(void)
{ SVCint i;

  for(i=1; i<=no_states ; i++)
  { states[i].list1=0;
    states[i].list2=0;
  }
 
  stack=0;
  for(i=1; i<=no_transitions ; i++)
  { 
    transitions[i].candidate=1;
    transitions[i].stack_next=stack;
    stack=i;
    transitions[i].on_stack=1;

    /* outgoing tau transitions are stored in list2 */
    if (transitions[i].label==tau_label)
     { transitions[i].list2_next=states[transitions[i].source].list2;
       states[transitions[i].source].list2=i;
     }
    else
     { transitions[i].list2_next=0;
     }
    /* incoming transitions are stored in list1 */
    transitions[i].list1_next=states[transitions[i].target].list1;
    states[transitions[i].target].list1=i;
    /* add_to_hashtable(i); is al gebeurd */
  }    
}

/**************  remove_strongly_connected_tau_components();  ****/

static SVCstateIndex order_states(SVCstateIndex i, SVCstateIndex last)
{ SVCint t;

  if (states[i].old_index>0) 
  return last;
  
  states[i].old_index=1;
  for(t=states[i].list1; t!=0 ; )
  { last=order_states(transitions[t].target,last);
    t=transitions[t].list1_next;
  }
  states[i].list2=last;
  states[i].list1=0;
  return i;
}

static void collect_component(SVCstateIndex s, SVCstateIndex root)
{ SVCint t;
    
  if (states[s].old_index!=1) return;

  states[s].old_index=2;
  for(t=states[s].list1 ; t!=0 ; )
  { collect_component(transitions[t].source,root);
    t=transitions[t].list1_next;
  }
  states[s].list1=root;
 
}

static void remove_strongly_connected_tau_components(void)
{ SVCint i, back_index;
  SVCstateIndex laststate=0, auxState, new_source, new_target;
  SVClabelIndex new_label;

  /* first put the outgoing tau transitions of each state
     in list1 */

  for(i=1 ; i<=no_transitions ; i++)
  { if (transitions[i].label==tau_label)
     { transitions[i].list1_next=states[transitions[i].source].list1;
       states[transitions[i].source].list1=i;
     }
  }

  /* now carry out a depth first directed sweep through
     the states, to construct an ordering on the states 
     in the variable list2. It is assumed that the 
     variable old_index of all states contains 0. After passing
     through all states the variables states[i].old_index contains 1.
     Moreover, set states[i].list1 back to 0 */

  for(i=1 ; i<=no_states ; i++)
  { laststate=order_states(i,laststate);
  }

  /* now construct lists of backward tau transitions
     for each state in list1 */

  for(i=1 ; i<=no_transitions ; i++)
  { if (transitions[i].label==tau_label)
     { transitions[i].list1_next=states[transitions[i].target].list1;
       states[transitions[i].target].list1=i;
     }
  }
  
  /* now carry out a backward sweep, with a nested depth
     first search through the previously constructed list
     of states, and for all states register in the variable
     states[i].list1 to which component it belongs. We assume
     that the variable states[i].old_index are initially set to 1,
     and set this variable to 2 */


  for( ; laststate!=0 ; )
  { collect_component(laststate,laststate);
    laststate=states[laststate].list2;
  }

  /* finally, we must compact the list of states and
     transitions, removing all redundant states and transitions.
     First we do the states */

  back_index=0;
  for(i=1 ; i<=no_states ; i++)
  { if (states[i].list1==i)
     { /* state survives */
       back_index++;
       states[i].list2=back_index; /* back_index is the new index of
                                      state i */
     }
    else 
     { states[i].list2=0; 
     }
  } 

  initial_state=states[initial_state].list2;

  for(i=1 ; i<=no_states ; i++)
  { states[i].old_index=states[states[i].list1].list2; 
       /* states[i].old_index now contains the new index of the
          state that formerly had index i. list1 and list2
          now have become useless. */
  }
  
  /* We now set in states[i].list2 an old index, such that
     we can locate an old state description of this state */
  for(i=1 ; i<=no_states ; i++)
  { states[states[i].old_index].list2=i;  
  }

  /* We want the information in list2 in old_index. So, we
     exchange it. This step could have been avoided by being
     a little more careful in the previous steps. */
  for(i=1 ; i<=no_states ; i++)
  { auxState=states[i].old_index;
    states[i].old_index=states[i].list2;  
    states[i].list2=auxState;
    states[i].list1=0;
  }
  no_states=back_index;

  /* In states[i].list2 we find the new index of what
     was formerly state i. In states[i].old_index we find
     the number of a state that is mapped to new number i */
  
  /* Now we must relabel the transitions to match the new
     state numbering, and at the same time remove redundant
     transitions, i.e. the tau-loops and double transitions
     with similar labels from state tot state. */
  
  back_index=0;   
  for(i=1 ; i<=no_transitions ; i++)
  { new_source=states[transitions[i].source].list2;
    new_target=states[transitions[i].target].list2;
    new_label=transitions[i].label;
    if ((transitions[i].label!=tau_label) || (new_source!=new_target))
    { /* transition is still a candidate to survive */
      if (in_hashtable(new_source,new_label,new_target)==0)
      { /* now this transition must really survive */
        back_index++;
        transitions[back_index].source=new_source;
        assert(new_source<=no_states);
        transitions[back_index].target=new_target;
        transitions[back_index].label=new_label;
#ifdef PARAMETER
        transitions[back_index].parameter=transitions[i].parameter;
#endif
        add_to_hashtable(back_index); 
      } 
    }
  }
  no_transitions=back_index;
  states=realloc(states,(no_states+1)*sizeof(statetype));
  if (states==NULL)
    { ATerror("Reducing state array fails\n");
    }
  transitions=realloc(transitions,(no_transitions+1)*sizeof(transitiontype));
  if (transitions==NULL)
    { ATerror("Reducing transition array fails\n");
    }
}

/**************  apply_tau_sequence_reduction  ************/

static void calculate_transitive_closure(SVCint s)
{ if (states[s].list2==2) return;
  if (states[states[s].list1].list2==2) return;

  calculate_transitive_closure(states[s].list1);
  
  states[s].list1=states[states[s].list1].list1;
}

static void apply_tau_sequence_reduction(void)
{ SVCint i;

  for(i=1 ; i<=no_states ; i++)
  { states[i].list1=0;
    states[i].list2=0;
  }  

  /* assign to each state in list1 which state can be
     reached via a unique outgoing tau_step,
     if there is no more than one outgoing transition. Set
     list2 to 1 if this is the single transition, and
     set list2 to 2 and list1 to 0 if more or no transition exist. */

  for(i=1 ; i<=no_transitions ; i++)
    { if ((transitions[i].label==tau_label) &&
          (states[transitions[i].source].list2==0))
      {
        states[transitions[i].source].list1=transitions[i].target;
        states[transitions[i].source].list2=1;
      }
      else 
      { states[transitions[i].source].list2=2;
        states[transitions[i].source].list1=0;
      }
    }
  /* if list2 is still 0, there is no outgoing transition
     and it must be set to 2. */

  for(i=1 ; i<=no_states ; i++)
  { if (states[i].list2==0)
       states[i].list2=2;
  }  

  /* do a depth first search via the tau_transitions,
     and denote the farthest state that can be reached
     via a non_branching sequence of tau_transitions */  
  for(i=1 ; i<=no_states ; i++)
  { calculate_transitive_closure(i);
  }

  /* finally, we must adapt the target states of the transitions */

  for(i=1 ; i<=no_transitions ; i++)
  { if (states[transitions[i].target].list2==1)
    { transitions[i].target=states[transitions[i].target].list1; 
    }
  }
  
  if (states[initial_state].list2==1)
     initial_state=states[initial_state].list1;
}

/**************  help  ************************/



void usage(void)
{
  fprintf(stderr, "Use %s -help for options\n", programName);
}

void version(void)
{
  printf("Local confluence checker and state space reducer. Version %s\n", VERSION);
}void help(void)
{
  char * str =
"\n\
Local confluence checker and state space reducer\n\
===================================\n\n\
Usage: %s [options] [file]\n\
\n\
The following options can be used:\n\
\n\
-help:     yields this message\n\
-version:  get a version of the lineariser\n\
\n\
This program reads a state space in a file in SVC format. It\n\
first removes tau loops. Then it locates all tau transitions \n\
that are strongly confluent, and given these carries out\n\
a tau-prioritisation. After this non-branching sequences of\n\
tau's are compressed. The resulting file is written in file.red\n\
";

  fprintf(stderr, str, programName);
}



/**************  main  ************************/

int main (int argc, char *argv[])
{ 
  ATerm stack_bottom;
  int i;
  unsigned long old_no_states, old_no_transitions;
  char *infilename=NULL, *outfilename=NULL;
  SVCbool allocatedFileName = SVCfalse;
  programName=argv[0];
  for(i = 1; i < argc; i++){
    if(streq(argv[i], "-version")){
      version(); exit(0);
    } else if(streq(argv[i], "-help")){
      help(); exit(0);
    } else if((argv[i][0]=='-') && (argv[i][1]=='a') && (argv[i][2]=='t')){
      i++;
    } else if(argv[i][0]=='-'&& argv[i][1]=='o') {
      outfilename = argv[++i];
    } else if(argv[i][0]=='-'){
      fprintf(stderr,"Unknown option %s ignored\n",argv[i]);
    
    
    } else {
      infilename = argv[i];
      if (!outfilename) {
          outfilename=malloc(strlen(infilename)+5);
          allocatedFileName = SVCtrue;
          if (outfilename==NULL)
	     { ATerror("Cannot assign space for name of target file\n");
	      }
          strcpy(outfilename,infilename);
          if(!strcmp(outfilename+strlen(outfilename)-strlen(OUTFILE_EXT),OUTFILE_EXT)){
          outfilename[strlen(outfilename)-strlen(OUTFILE_EXT)]='\0';
          strcat(outfilename,REDFILE_EXT);
         strcat(outfilename,OUTFILE_EXT);
      } else {
         strcat(outfilename,REDFILE_EXT);
      }
     }
    }
  }
  if (infilename==NULL)
  { usage(); }

  ATinit(argc,argv,&stack_bottom);

  if (read_file(infilename)==0) exit(1);
  initial_state=SVCgetInitialState(&infile)+1;
  if (initial_state<=0)
   { ATerror("Input file has no initial state.\nReason: %s\n",
               SVCerror(SVCerrno));
   } 

  remove_strongly_connected_tau_components();
  do 
  { old_no_states=no_states;
    old_no_transitions=no_transitions;
    setup_data_structure();
    determine_confluent_taus();
    apply_tau_prioritisation();
    apply_tau_sequence_reduction();
    compact_data();
  }
  while ((old_no_states>no_states) || (old_no_transitions>no_transitions));

  write_file(outfilename);

  if (allocatedFileName) free(outfilename);
  return 0;
}





