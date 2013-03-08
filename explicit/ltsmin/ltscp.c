/* $Id: ltscp.c,v 1.3 2005/02/14 16:16:30 uid523 Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif


static char *cvs_id="$Id: ltscp.c,v 1.3 2005/02/14 16:16:30 uid523 Exp $";

#include <stdio.h>
#include <string.h>
#include "options.h"
#include "messages.h"
#include "xlts.h"

static char *outputname=NULL;
static int requiredargs=2, requiredopts = 0, bfs =0,
sort = 0;

static int set_bfs(char* opt,char*optarg,void *arg){
	requiredopts++;bfs = 1;
	return OPT_OK;
   }
   
static int set_sort(char* opt,char*optarg,void *arg){
	requiredopts++; sort = 1;
	return OPT_OK;
   } 
     
struct option options[]={
	{"",OPT_NORMAL,NULL,NULL,NULL, "usage: ltscp  options input output",
   "Copies labeled transition systems."},
#include "help.h"
   {"",OPT_NORMAL,NULL,NULL,NULL,"options:"},
   {"-bfs",OPT_NORMAL, NULL, NULL, NULL,"reorder the lts into bfs exploration order"},
   {"-sort",OPT_NORMAL, NULL, NULL, NULL,"sorts the transitions per state"},
   {"-postsort", OPT_NORMAL, NULL,NULL ,NULL,
		"sorts the transitions per state before writing"},
   {"-segments",OPT_REQ_ARG,NULL, NULL,"-segments <N>",
   "write output dir with N segments","has no influence if output is not a dir"},
 	{0}
};

int main(int argc,char **argv){
   char **newargv = (char**) calloc(argc + 4, sizeof(char*)), ltsmin[256];
	int unused = parse_options(options,argc,argv), j = 0, i;
   sprintf(ltsmin, "%s/%s", BINDIR, "ltsmin");
   if (sort)  newargv[j++] = "ltscp -sort";
   else if (bfs) newargv[j++] = "ltscp -bfs"; 
   else newargv[j++] = "ltscp"; 
   if ((unused+requiredargs)!=argc || requiredopts>1) {
		printoptions(options);
		exit(1);
	}
   for (i=1;i<argc;i++) 
   if (strcmp(argv[i],"-bfs")&&strcmp(argv[i],"-sort"))
      newargv[j++]=argv[i];
   newargv[j]=NULL;
   if (execv(ltsmin, newargv)<0) Fatal(1,1,"Cannot execute %s", ltsmin);
}
   
