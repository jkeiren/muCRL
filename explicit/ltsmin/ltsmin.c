/* $Id: ltsmin.c,v 1.3 2007/06/29 13:30:57 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

static char *cvs_id="$Id: ltsmin.c,v 1.3 2007/06/29 13:30:57 bertl Exp $";

#include <stdio.h>
#include <string.h>
#include "options.h"
#include "messages.h"
#include "xlts.h"
#include "setreductions.h"
#include "simona-red.h"
#include "ks.h"
#include "lowmem.h"
#ifdef USE_BCG
#include "bcg_user.h"
#endif
#include "memstat.h"

#define USAGE 0
#define CYCLE_REDUCTION 1
#define STRONG_REDUCTION_SET 2
#define BRANCHING_REDUCTION_SET 3
#define STRONG_REDUCTION_SIMONA 4
#define STRONG_REDUCTION_SET2 5
#define BRANCHING_REDUCTION_SET2 6
#define STRONG_REDUCTION_LOWMEM 7
#define BRANCHING_REDUCTION_SET3 8
#define INDIR_REDUCTION 9
#define TAU_STAR_A_REDUCTION 10
#define LOAD_STORE 11
#define TRACE_EQUIVALENCE_REDUCTION 12
#define DETERMINIZE_REDUCTION 13
#define WEAK_REDUCTION 14
#define COMPUTE_DIAMETER 15
#define STRONG_KANELLAKIS_SMOLKA 16

static char *outputname=NULL;
static int requiredargs=1;
static int action=STRONG_REDUCTION_LOWMEM, compare = 0;
// static int action=USAGE, compare = 0;

static int select_cycle_reduction(char* opt,char*optarg,void *arg){
	action=CYCLE_REDUCTION;
   if (requiredargs<1) requiredargs=1;
	return OPT_OK;
}

static int select_compute_diameter(char* opt,char*optarg,void *arg){
	action=COMPUTE_DIAMETER;
	if (requiredargs<1) requiredargs=1;
	return OPT_OK;
}

static int select_weak_reduction(char* opt,char*optarg,void *arg){
	action=WEAK_REDUCTION;
   if (requiredargs<1) requiredargs=1;
	return OPT_OK;
}

static int select_indir_reduction(char* opt,char*optarg,void *arg){
	action=INDIR_REDUCTION;
   if (requiredargs<1) requiredargs=1;
	return OPT_OK;
}

static int select_strong_reduction(char* opt,char*optarg,void *arg){
   if (requiredargs<1) requiredargs=1;
	if(optarg==NULL){
		action=STRONG_REDUCTION_LOWMEM;
		return OPT_OK;
	}
	if (!strcmp(optarg,"naive")) {
		action=STRONG_REDUCTION_SET;
		return OPT_OK;
	}
	if (!strcmp(optarg,"naive2")) {
		action=STRONG_REDUCTION_SET2;
		return OPT_OK;
	}
	if (!strcmp(optarg,"optimized")) {
		action=STRONG_REDUCTION_SIMONA;
		return OPT_OK;
	}
        if (!strcmp(optarg,"ks")) {
		action=STRONG_KANELLAKIS_SMOLKA;
		return OPT_OK;
	}
	if (!strcmp(optarg,"lowmem")) {
		action=STRONG_REDUCTION_LOWMEM;
		return OPT_OK;
	}
	Warning(1,"unknown strong bisimulation method: %s",optarg);
	return OPT_USAGE;
}

static int select_tau_star_a_reduction(char* opt,char*optarg,void *arg){
   if (requiredargs<1) requiredargs=1;
	action=TAU_STAR_A_REDUCTION;
	return OPT_OK;
}

static int select_trace_equivalence(char* opt,char*optarg,void *arg){
   if (requiredargs<1) requiredargs=1;
	action=TRACE_EQUIVALENCE_REDUCTION;
	return OPT_OK;
}

static int select_determinize(char* opt,char*optarg,void *arg){
   if (requiredargs<1) requiredargs=1;
	action=DETERMINIZE_REDUCTION;
	return OPT_OK;
}

static int select_branching_reduction(char* opt,char*optarg,void *arg){
   if (requiredargs<1) requiredargs=1;
	if(optarg==NULL){
		action=BRANCHING_REDUCTION_SET;
		return OPT_OK;
	}
	if (!strcmp(optarg,"set")) {
		action=BRANCHING_REDUCTION_SET;
		return OPT_OK;
	}
	if (!strcmp(optarg,"set2")) {
		action=BRANCHING_REDUCTION_SET2;
		return OPT_OK;
	}
	if (!strcmp(optarg,"iter")) {
		action=BRANCHING_REDUCTION_SET3;
		return OPT_OK;
	}
	Warning(1,"unknown branching bisimulation method: %s",optarg);
	return OPT_USAGE;
}

static int set_load_store(char* opt,char*optarg,void *arg){
   if (requiredargs<1) requiredargs=1;
	action=LOAD_STORE;
	return OPT_OK;
}

static int set_compare(char* opt,char*optarg,void *arg){
	requiredargs=2;
	compare = 1;
	return OPT_OK;
}

static int bfs_reorder=0;
static int randomize_stateno=0;
static int sort_lts=0;
static int postsort_lts=0;
static int tau_divergence_marking=0;

struct option options[]={
	{"",OPT_NORMAL,NULL,NULL,NULL,	"usage: ltsmin options input [output]",
               "Reduces labeled transition syst"},
#include "help.h"	
	{"",OPT_NORMAL,NULL,NULL,NULL,"options:"},
	{"-cycle",OPT_NORMAL,select_cycle_reduction,NULL,NULL,"apply tau cycle reduction"},
	{"-s",OPT_NORMAL,select_strong_reduction,NULL,"-s","apply strong bisimulation reduction"},
	{"-b",OPT_NORMAL,select_branching_reduction,NULL,"-b","apply branching bisimulation reduction"},
#ifdef TESTLTSMIN
	{"-copy",OPT_NORMAL,set_load_store,NULL,NULL,"copy the input to the output"},
   {"-cmp",OPT_NORMAL,set_compare,NULL,NULL, "if input1 equivalent input2 exit 0 else exit 1"},
#endif
	{"",OPT_NORMAL,NULL,NULL,NULL,"experimental options:"},
	{"-indir",OPT_NORMAL,select_indir_reduction,NULL,NULL,"apply tau indirection reduction"},
	{"-S",OPT_REQ_ARG,select_strong_reduction,NULL,"-S method",
		"apply alternative strong bisimulation reduction method",
		"method is naive, naive2, lowmem, ks, or optimized"},
	{"-B",OPT_REQ_ARG,select_branching_reduction,NULL,"-B method",
		"apply alternative branching bisimulation reduction method",
		"method is set, set2 or iter"},
	{"-tsa",OPT_NORMAL,select_tau_star_a_reduction,NULL,NULL,"tau star a reduction"},
	{"-det",OPT_NORMAL,select_determinize,NULL,NULL,"determinize the lts"},
	{"-trace",OPT_NORMAL,select_trace_equivalence,NULL,NULL,
			"compute smallest deterministic LTS, which is trace equivalence"},
	{"-w",OPT_NORMAL,select_weak_reduction,NULL,NULL,"apply weak bisimulation reduction"},
	{"-diam",OPT_NORMAL,select_compute_diameter,NULL,NULL,"compute diameter of LTS"},
        {"-div",OPT_NORMAL,set_int,&tau_divergence_marking,NULL,"preserve divergences when applying branching bisimulation reduction"},
	{"-c",OPT_NORMAL,set_int,&tau_cycle_elim,NULL,"apply tau cycle elimination before reduction",
			"possible preprocessing step for branching bisimulation."},
	{"-i",OPT_NORMAL,set_int,&tau_indir_elim,NULL,"apply tau indirection elimination before reduction",

			"preprocessing step for branching bisimulation."},
#ifdef TESTLTSMIN
	{"-bfs",OPT_NORMAL,set_int,&bfs_reorder,NULL,"reorder the lts into bfs exploration order", "use in combination with -copy only!"},
#endif
	{"-segments",OPT_REQ_ARG,parse_int,&lts_write_segments,"-segments <N>",
		"write output dir with N segments","has no influence if output is not a dir"},
#ifdef LINUX
	{"-randomize",OPT_NORMAL,set_int,&randomize_stateno,NULL,"randomize the state numbers",
		"this function requires /dev/random to work!"},
#endif
#ifdef TESTLTSMIN
	{"-sort",OPT_NORMAL,set_int,&sort_lts,NULL,"sorts the transitions per state","use in combination with -copy only!"},
#endif
	{"-postsort",OPT_NORMAL,set_int,&postsort_lts,NULL,
		"sorts the transitions per state before writing"},
	{"-statm",OPT_NORMAL,set_int,&memstat_enable,NULL,"enable peak memory checking"},
 	{0}
};

static void ReportTimer(mytimer_t timer, char *s) {
   reportTimer(timer, s);
   fprintf(stderr,"\n");
   }
   
int main(int argc,char **argv){
	int	unused;
	lts_t	lts = NULL, lts1=NULL, lts2=NULL;
	mytimer_t	timer;
   if (!strcmp(argv[0], "ltscmp")) 
       set_compare(NULL, NULL, NULL);
   if (!strncmp(argv[0], "ltscp", 5))
       set_load_store(NULL, NULL, NULL);
   if (!strcmp(argv[0], "ltscp -sort")) bfs_reorder = 1;
   if (!strcmp(argv[0], "ltscp -bfs"))  sort_lts = 1;
	verbosity=1;
	unused=parse_options(options,argc,argv);
	if ((unused+requiredargs+1)==argc && outputname==NULL){
		outputname=argv[unused+requiredargs];
		argc--;
	}
	if ((unused+requiredargs)!=argc||action==USAGE) {
		printoptions(options);
		exit(1);
	}
	timer=createTimer();
#ifdef USE_BCG
	BCG_INIT();
#endif
#ifdef USE_SVC
	lts_stack_bottom=&argc;
#endif
	/* depending on action read one or two transition systems */
	switch(action){
		case WEAK_REDUCTION:
		case CYCLE_REDUCTION:
		case INDIR_REDUCTION:
		case BRANCHING_REDUCTION_SET:
		case BRANCHING_REDUCTION_SET2:
		case BRANCHING_REDUCTION_SET3:
		case STRONG_REDUCTION_SET:
		case STRONG_REDUCTION_SET2:
		case STRONG_REDUCTION_SIMONA:
                case STRONG_KANELLAKIS_SMOLKA:
		case STRONG_REDUCTION_LOWMEM:
		case TAU_STAR_A_REDUCTION:
		case TRACE_EQUIVALENCE_REDUCTION:
		case DETERMINIZE_REDUCTION:
		case LOAD_STORE:
		case COMPUTE_DIAMETER:
			resetTimer(timer);
			startTimer(timer);
         if (compare) {
            lts1=lts_create();
			   lts_read(LTS_AUTO,argv[unused],lts1);
            Warning(1,"first LTS has %d states and % ld transitions",lts1->states,lts1->transitions);
            lts2=lts_create();
			   lts_read(LTS_AUTO,argv[unused+1],lts2);
             Warning(1,"second LTS has %d states and % ld transitions",lts2->states,lts2->transitions);
            lts=lts_create();
            lts_join(lts1, lts2, lts);
            lts_free(lts1); lts_free(lts2);
            }
         else {
			  lts=lts_create();
			  lts_read(LTS_AUTO,argv[unused],lts);
           Warning(1,"original LTS has %d states, % ld transitions, and %d labels",
                          lts->states,lts->transitions, lts->label_count);
           }
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reading took");
			break;
	}
	/* Check if we have an invisible label. */
	switch(action){
		case TAU_STAR_A_REDUCTION:
		case CYCLE_REDUCTION:
		case WEAK_REDUCTION:
		case INDIR_REDUCTION:
		case BRANCHING_REDUCTION_SET:
		case BRANCHING_REDUCTION_SET2:
		case BRANCHING_REDUCTION_SET3:
		case TRACE_EQUIVALENCE_REDUCTION:
			if (lts->tau<0) {
				Warning(1,"couldn't auto-detect label of invisible step.");
				Warning(1,"probably this LTS has no invisible steps.");
			}
	}
	MEMSTAT_CHECK;
	/* perform the computation */
	if (bfs_reorder){
			resetTimer(timer);
			startTimer(timer);
			lts_bfs_reorder(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"bfs reorder took");
	}
#ifdef LINUX
	if (randomize_stateno){
			resetTimer(timer);
			startTimer(timer);
			lts_randomize(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"randomizing took");
	}
#endif
	if (sort_lts){
			resetTimer(timer);
			startTimer(timer);
			lts_sort_alt(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"sorting took");
	}
        switch(action){
          case BRANCHING_REDUCTION_SET:
          case BRANCHING_REDUCTION_SET2:
          case BRANCHING_REDUCTION_SET3:
            resetTimer(timer);
            startTimer(timer);
            lts_divergence_marking(lts);
            stopTimer(timer);
            if(verbosity>0) ReportTimer(timer,"marking divergences took");
          default:
            break;
        }

	switch(action){
		case CYCLE_REDUCTION:
			resetTimer(timer);
			startTimer(timer);
			lts_tau_cycle_elim(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"cycle elimination took");
			break;
		case WEAK_REDUCTION:
			resetTimer(timer);
			startTimer(timer);
			set_reduce_weak(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case INDIR_REDUCTION:
			resetTimer(timer);
			startTimer(timer);
			lts_tau_indir_elim(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"indirection elimination took");
			break;
		case TAU_STAR_A_REDUCTION:
			resetTimer(timer);
			startTimer(timer);
			set_reduce_tau_star_a(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case BRANCHING_REDUCTION_SET:
			resetTimer(timer);
			startTimer(timer);
			set_reduce_branching(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case BRANCHING_REDUCTION_SET2:
			resetTimer(timer);
			startTimer(timer);
			set_reduce_branching2(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case BRANCHING_REDUCTION_SET3:
			resetTimer(timer);
			startTimer(timer);
			set_reduce_branching3(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case STRONG_REDUCTION_SET:
			resetTimer(timer);
			startTimer(timer);
			set_reduce_strong(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case STRONG_REDUCTION_SET2:
			resetTimer(timer);
			startTimer(timer);
			set2_reduce_strong(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case STRONG_REDUCTION_SIMONA:
			resetTimer(timer);
			startTimer(timer);
			simona_strong_reduce(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
                case    STRONG_KANELLAKIS_SMOLKA:
                        resetTimer(timer);
			startTimer(timer);
			ks(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case TRACE_EQUIVALENCE_REDUCTION:
			resetTimer(timer);
			startTimer(timer);
			Warning(1,"applying tau*a reduction");
			set_reduce_tau_star_a(lts);
			Warning(1,"LTS has %d states and % ld transitions",lts->states,lts->transitions);
			Warning(1,"determinizing");
			set_mkdet(lts);
			Warning(1,"LTS has %d states and % ld transitions",lts->states,lts->transitions);
			Warning(1,"applying strong bisimulation reduction");
			lowmem_strong_reduce(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case DETERMINIZE_REDUCTION:
			resetTimer(timer);
			startTimer(timer);
			set_mkdet(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case STRONG_REDUCTION_LOWMEM:
			resetTimer(timer);
			startTimer(timer);
			lowmem_strong_reduce(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case COMPUTE_DIAMETER:
			resetTimer(timer);
			startTimer(timer);
			printf("Diameter is %d\n",lts_diameter(lts));
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
	}
	MEMSTAT_CHECK;
        switch(action){
          case BRANCHING_REDUCTION_SET:
          case BRANCHING_REDUCTION_SET2:
          case BRANCHING_REDUCTION_SET3:
            resetTimer(timer);
            startTimer(timer);
            lts_remove_divergence_marking(lts);
            stopTimer(timer);
            if(verbosity>0) ReportTimer(timer,"removing divergence labels took");
          default:
            break;
        }
        MEMSTAT_CHECK;
	if (postsort_lts){
			resetTimer(timer);
			startTimer(timer);
			lts_sort_dest(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"sorting took");
	}
	/* write the output */
	switch(action){
		case WEAK_REDUCTION:
		case CYCLE_REDUCTION:
		case INDIR_REDUCTION:
		case TAU_STAR_A_REDUCTION:
		case BRANCHING_REDUCTION_SET:
		case BRANCHING_REDUCTION_SET2:
		case BRANCHING_REDUCTION_SET3:
		case STRONG_REDUCTION_SET:
		case STRONG_REDUCTION_SET2:
		case STRONG_REDUCTION_SIMONA:
		case STRONG_REDUCTION_LOWMEM:
		case TRACE_EQUIVALENCE_REDUCTION:
                case STRONG_KANELLAKIS_SMOLKA:
		case DETERMINIZE_REDUCTION:
			Warning(1,"reduced LTS has %d states and % ld transitions",lts->states, lts->transitions);
		case LOAD_STORE:
			if (outputname) {
				resetTimer(timer);
				startTimer(timer);
				lts_write(LTS_AUTO,outputname,lts);
				stopTimer(timer);
				if (verbosity>0) ReportTimer(timer,"writing took");
			}
			break;
	}
	MEMSTAT_CHECK;
	memstat_warn(1,maxmem,"memory use");
   if (compare) {
      if (lts_equivalent(lts)) {
           if (verbosity>0) Warning(1,"Labeled transitions systems are equivalent");
           exit(0);
           }
      else {
          if (verbosity>0) Warning(1,"Labeled transitions systems are NOT equivalent");
          exit(1);
          }
      }
	exit(0);
}

