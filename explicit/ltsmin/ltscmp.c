/* $Id: ltscmp.c,v 1.2 2004/11/23 12:36:17 uid523 Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif


static char *cvs_id="$Id: ltscmp.c,v 1.2 2004/11/23 12:36:17 uid523 Exp $";

#include <stdio.h>
#include <string.h>
#include "options.h"
#include "messages.h"
#include "xlts.h"

static char *outputname=NULL;
static int requiredargs=2, requiredopts = 0;

static int set_operation(char* opt, char *optarg, void *arg){
	requiredopts++; 
	return OPT_OK;
   }
   
     
struct option options[]={
	{"",OPT_NORMAL,NULL,NULL,NULL, "usage: ltscmp  options input1 input2",
   "Compares two labeled transition systems.",
   "Exits with 0 if they are equivalent, exits with 1 otherwise."},
#include "help.h"
	{"",OPT_NORMAL,NULL,NULL,NULL,"options:"},
	{"-cycle",OPT_NORMAL,NULL,NULL,NULL,"apply tau cycle reduction"},
	{"-s",OPT_NORMAL,set_operation,NULL,"-s","strong bisimulation equivalence"},
	{"-b",OPT_NORMAL,set_operation,NULL,"-b","branching bisimulation equivalence"},
	{"",OPT_NORMAL,NULL,NULL,NULL,"expirimental options:"},
	{"-indir",OPT_NORMAL,NULL,NULL,NULL,"apply tau indirection reduction"},
	{"-S",OPT_REQ_ARG,set_operation,NULL,"-S method",
		"strong bisimulation equivalence",
		"method is naive, naive2 or lowmem "},
	/* {"-B",OPT_REQ_ARG,set_operation,NULL,"-B method",
		"branching bisimulation equivalence",
		"method is set, set2 or iter"}, 
	{"-tsa",OPT_NORMAL,set_operation,NULL,NULL,"tau star equivalence"},
	{"-trace",OPT_NORMAL,set_operation,NULL,NULL,"trace equivalence"},
	{"-w",OPT_NORMAL,set_operation,NULL,NULL,"weak bisimulation equivalence"},
	
	{"-c",OPT_NORMAL,NULL,NULL,NULL,"apply tau cycle elimination before reduction",
			"possible preprocessing step for branching bisimulation equivalence."},
	{"-i",OPT_NORMAL,NULL, NULL, NULL,"apply tau indirection elimination before reduction",
			"experimental preprocessing step for branching bisimulation."},
   */
	{"-statm",OPT_NORMAL,NULL, NULL,NULL,"enable peak memory checking"},
 	{0}
};

int main(int argc,char **argv){
   char **newargv = (char**) calloc(argc + 4, sizeof(char*)), ltsmin[256];
	int unused = parse_options(options,argc,argv), j = 0, i;
   sprintf(ltsmin, "%s/%s", BINDIR, "ltsmin");
   newargv[j++] = "ltscmp";
#ifdef TESTLTSMIN 
   newargv[j++] = "-cmp";
#endif 
   if ((unused+requiredargs)!=argc || requiredopts>1) {
		printoptions(options);
		exit(1);
	}
   if (requiredopts==0) newargv[j++]="-s";
   for (i=1;i<argc;i++) {
       if (strcmp(argv[i],"-b")) newargv[j++]=argv[i];
       else {
            newargv[j++]= "-B";
            newargv[j++]= "set2";
            }
       }
   newargv[j]=NULL;
   /*
   for (i=0;i<j;i++)
        fprintf(stderr,"%s %s:\n",ltsmin,  newargv[i]); 
   */
   if (execv(ltsmin, newargv)<0) Fatal(1,1,"Cannot execute %s", ltsmin);
}
   
