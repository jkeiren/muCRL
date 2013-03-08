/* $Id: ltsmin.c,v 1.4 2007/07/13 11:44:42 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

static char *cvs_id="$Id: besmin.c,v 1.0 2009/06/30 11:44:42 timw Exp $";

#include <stdio.h>
#include <string.h>
#include "options.h"
#include "messages.h"
#include "xlts.h"
#include "besreductions.h"
#include "memstat.h"

#define USAGE 0
#define STRONG_REDUCTION_SET 1
#define OBLIVIOUS_REDUCTION_SET 2

static char *outputname=NULL;
static int requiredargs=1;
static int action=STRONG_REDUCTION_SET, compare = 0;
// static int action=USAGE, compare = 0;

static int select_strong_reduction(char* opt,char*optarg,void *arg){
   if (requiredargs<1) requiredargs=1;
	if(optarg==NULL){
		action=STRONG_REDUCTION_SET;
		return OPT_OK;
	}
	if (!strcmp(optarg,"strong")) {
		action=STRONG_REDUCTION_SET;
		return OPT_OK;
	}
	if (!strcmp(optarg,"oblivious")) {
		action=OBLIVIOUS_REDUCTION_SET;
		return OPT_OK;
	}
	Warning(1,"unknown strong bisimulation method: %s",optarg);
	return OPT_USAGE;
}


struct option options[]={
	{"",OPT_NORMAL,NULL,NULL,NULL,	"usage: besmin options input [output]",
               "Reduces Boolean Equation System"},
#include "help.h"	
	{"",OPT_NORMAL,NULL,NULL,NULL,"options:"},
	{"-S",OPT_REQ_ARG,select_strong_reduction,NULL,"-S method",
		"apply bisimulation reduction method",
		"method is strong, oblivious"},
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
#ifdef USE_SVC
	lts_stack_bottom=&argc;
#endif
	/* depending on action read one or two transition systems */
	switch(action){
		case STRONG_REDUCTION_SET:
		case OBLIVIOUS_REDUCTION_SET:
			lts=lts_create();
			lts_read(LTS_AUTO,argv[unused],lts);
			Warning(1,"original BES has %d equations, and size %ld",
			lts->states,lts->transitions+lts->states);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reading took");
			break;
	}
	MEMSTAT_CHECK;
	/* perform the computation */
	switch(action){
		case STRONG_REDUCTION_SET:
			resetTimer(timer);
			startTimer(timer);
			bes_reduce_strong(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;
		case OBLIVIOUS_REDUCTION_SET:
			resetTimer(timer);
			startTimer(timer);
			bes_reduce_oblivious(lts);
			stopTimer(timer);
			if (verbosity>0) ReportTimer(timer,"reduction took");
			break;

	}
	MEMSTAT_CHECK;

	/* write the output */
	switch(action){
		case STRONG_REDUCTION_SET:
			if (outputname) {
				resetTimer(timer);
				startTimer(timer);
				lts_write2(outputname,lts,0);
				stopTimer(timer);
				if (verbosity>0) ReportTimer(timer,"writing took");
			}
			break;
		case OBLIVIOUS_REDUCTION_SET:
			if (outputname) {
				resetTimer(timer);
				startTimer(timer);
				lts_write2(outputname,lts,1);
				stopTimer(timer);
				if (verbosity>0) ReportTimer(timer,"writing took");
			}
			break;
	}
	MEMSTAT_CHECK;
	memstat_warn(1,maxmem,"memory use");
	exit(0);
}

