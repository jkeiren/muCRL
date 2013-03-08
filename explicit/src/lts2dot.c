static char *cvs_id="$Id: lts2dot.c,v 1.3 2004/11/23 12:36:17 uid523 Exp $";
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#define USAGE 0
#define RUN 1
#define ATTRSIZE 512

#include <stdio.h>
#include "messages.h"
#include "options.h"
#include "xlts.h"
#include "string.h"

typedef enum {NO_SIZE, LETTER, A4} paper_t;
static lts_t	lts=NULL;
static int letter = 0, a4 = 0, showstatenames = 0,
showactionnames = 1, internal = 0;
static paper_t paper_size;

static char *outputname=NULL, *inputname=NULL, *firstname = NULL;
static int requiredargs=1, action=USAGE;
static char *spec = NULL;

static int select_showstatenames(char* opt,char*optarg,void *arg){
   if (!strcmp(optarg,"hide")) {
	showstatenames = 0;
        return OPT_OK;
	}
   if (!strcmp(optarg,"show")) {
	showstatenames = 1;
        return OPT_OK;
	}
    return OPT_USAGE;
   }
   
static int select_showactionnames(char* opt,char*optarg,void *arg){
   if (!strcmp(optarg,"hide")) {
	showactionnames = 0;
        return OPT_OK;
	}
   if (!strcmp(optarg,"show")) {
	showactionnames = 1;
        return OPT_OK;
	}
    return OPT_USAGE;
   }
      
static int version(char* opt,char*optarg, void *arg){
   printf("%s: %s\n", VERSION, cvs_id);
   return OPT_EXIT;
   }
   
static int help(char* opt,char*optarg, void *arg){
   return usage(opt, optarg, arg);
   }
     
struct option options[]={
{"",OPT_NORMAL,NULL,NULL,NULL,"Usage:\t\tlts2dot options file", 
"Description:\tConverts an Labeled Transition System read from file.ext",
"\t\tto the Graphviz format and saves it to file.dot"},
{"",OPT_NORMAL, NULL,NULL,NULL,"\t\tThe supported values for ext are: aut, svc"},
{"",OPT_NORMAL, NULL,NULL,NULL,"Options:"},
{"-v",OPT_NORMAL,inc_int,&verbosity,NULL,"increase the level of verbosity"},
{"-q",OPT_NORMAL,reset_int,&verbosity,NULL,"be silent"},
{"-help",OPT_NORMAL,help,NULL,NULL,"print this help message"},
{"-o",OPT_REQ_ARG,assign_string,&outputname,"-o outfile",
                  "redirect output to file"},
{"-spec",OPT_REQ_ARG,assign_string,&spec,"-spec dot_commands",
                  "commands to be inserted after the first \"{\" in output"},
{"-a4",OPT_NORMAL,set_int,&a4,"-a4", "fit to a4 size"},
{"-letter",OPT_NORMAL,set_int,&letter,"-letter", "fit to letter size"},
{"-statenames",OPT_REQ_ARG,select_showstatenames,NULL, "-statenames hide|show", 
           "show/hide names of states"},
{"-actionnames",OPT_REQ_ARG,select_showactionnames,NULL, "-actionnames hide|show", 
                                "show/hide names of actions"},
{"-internal",OPT_NORMAL,set_int, &internal, "-internal", 
                                "mark internal transitions"},
{"-version",OPT_NORMAL,version,NULL, NULL,"print version"},
{0}
};

static int PaperSize(int letter, int a4) {
   do  {
     if (!letter && !a4) break;
     if (letter && !a4) {paper_size = LETTER; break;}
     if (!letter && a4) {paper_size = A4; break;}
     Warning(0,"-a4 and -letter are both entered");
     return USAGE;
     }
   while (0);
   return RUN;
   }
   
static void Header(FILE *fpOut) { 
  fprintf(fpOut,"digraph \"%s\" {\n", firstname);
  if (spec) fprintf(fpOut,"%s\n", spec);
  switch (paper_size) {
     case NO_SIZE: break;
     case A4:fprintf(fpOut,"size=\"7,10.5\";\n"); break;
     case LETTER:fprintf(fpOut,"size=\"8.5,11\";\n"); break;
     }
  fprintf(fpOut,"center=TRUE;\n");
  fprintf(fpOut,"mclimit=2.0;\n");
  fprintf(fpOut,"nodesep=0.05;\n");
  if (!showstatenames)
      fprintf(fpOut,"node[width=0.25,height=0.25,label=\"\"];\n");
  fprintf(fpOut,"%d[peripheries=2];\n",lts->root);
  }

static char *Trunc(char *lab) {
  char *ptr;
  if ((ptr=strrchr(lab,'"')) && strlen(ptr)==1) *ptr='\0';
  return *lab=='"'?lab+1:lab; 
  }
   
int main(int argc, char *argv[]) { 
  FILE *fpOut=NULL;
  int unused, i;
#ifdef USE_SVC
     lts_stack_bottom=&argc;
#endif
#ifdef USE_BCG
	BCG_INIT();
#endif
  verbosity=1;
  unused=parse_options(options,argc,argv);
  action = PaperSize(letter, a4);
  if (outputname) {
    firstname = strrchr(outputname,'/');
    if (!firstname) firstname = outputname;
    else firstname++;
  } else
  if (argc >=2 && (unused+requiredargs)==argc){
      char *ptr;
      outputname = (char*) malloc(strlen(argv[unused])+5);
      outputname=strcpy(outputname, argv[unused]);
      if ((ptr=strrchr(outputname,'.'))) *ptr = '\0'; 
      else Fatal(1,0,"Extension missing at input file name %s", outputname);
      if (!(ptr=strrchr(outputname,'.')) || strcmp(ptr,".dot")) {
           strcat(outputname,".dot");
           firstname = strdup(outputname);
           ptr = strrchr(firstname,'/');
           if (!ptr) ptr = firstname; else ptr++;
           firstname = ptr;
           }	
      }
  if ((unused+requiredargs)!=argc||action==USAGE) {
        printoptions(options);
        exit(1);
	} 
   if (!(fpOut=fopen(firstname,"w"))) 
        FatalCall(1,0, "Cannot open %s", outputname);
   lts=lts_create();
   lts_read(LTS_AUTO,argv[unused],lts);
   
   Header(fpOut);
   for (i=0;i<lts->transitions;i++) { 
     char *lab = Trunc(lts->label_string[lts->label[i]]),
     actionAttr[ATTRSIZE], internAttr[ATTRSIZE];
     actionAttr[0]=internAttr[0]='\0';
     if (showactionnames) snprintf(actionAttr,ATTRSIZE, "[label=\"%s\"]", lab);
     if (internal) 
       snprintf(internAttr,ATTRSIZE, "[style=dotted,arrowhead=empty]");
     fprintf(fpOut, "%d->%d%s%s;\n",
     lts->src[i], lts->dest[i], actionAttr, lts->label[i]==lts->tau?
           internAttr:"");
     }
   fprintf(fpOut,"}\n");
   Warning(1,"\"%s\" contains an LTS with %d states, %d transitions, and %d labels",
   firstname, lts->states, lts->transitions, lts->label_count);
   fclose(fpOut);
   exit(0);
} /* main */

