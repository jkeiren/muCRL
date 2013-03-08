/* 
   SVC tools -- the SVC (Systems Validation Centre) tool set

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


   $Id: bsim.c,v 1.2 2006/02/14 08:08:15 bertl Exp $ */

#include "bsim.h"

int traceLevel = 0, optimal = 0, classes = 0; 

static 	struct tms tms_begin,tms_end;
static  long t_begin,t_end;

static void printTimes(void){
	long clk_tck=sysconf(_SC_CLK_TCK);
	float t_real=((float)(t_end-t_begin))/((float)clk_tck);
	float t_user=((float)(tms_end.tms_utime-tms_begin.tms_utime))/((float)clk_tck);
	float t_sys=((float)(tms_end.tms_stime-tms_begin.tms_stime))/((float)clk_tck);
	ATwarning("reduction took %5.3f real %5.3f user %5.3f sys\n",
			t_real,t_user,t_sys);
}

int main(int argc, char *argv[]) {
   ATerm bottom;
   ATinit(argc, argv, &bottom);

   switch(parseArgs(argc, argv, &traceLevel, &optimal, &classes)) {
      case ERR_ARGS:
         doHelp(argv[0]);
         exit(EXIT_ERR_ARGS);
         break;
      case ERR_FILE:
         exit(EXIT_ERR_FILE);
         break;
      case CMD_HELP:
         doHelp(argv[0]);
         exit(EXIT_OK);
         break;
      case CMD_VERSION:
         doVersion(argv[0]);
         exit(EXIT_OK);
      case CMD_REDUCE:
         exit(doReduce());
         break;
      case CMD_BRANCH_REDUCE:
           exit(doBranchReduce());
      case CMD_COMPARE:
         exit(doCompare());
         break;
      case CMD_BRANCH_COMPARE:
         exit(doBranchCompare());
         break;   
      default:
         exit(EXIT_OK);
   }


} /* main */



int parseArgs(int argc, char *argv[], int *traceLevel, int *optimal, int
*classes)
   {
   int c, ret, i, cautious = 0, nInputFiles = 0, branching = 0;
   extern int optind;
   char *inFilename=NULL, *outFilename = NULL;
   SVCbool indexed=1;
   *traceLevel = 1; *optimal = 0;
   while ((c = getopt(argc, argv, "hcsbvOCo:")) != EOF) 
      {
      switch(c)
         {        
         case 'c': cautious=1;
                   break;
         case 's': *traceLevel=0;
                   break;
         case 'b': branching=1;
                   break;
         case 'C': *classes=1;
                   break;
         case 'O': *optimal=1;
                   break;         
         case 'h': return CMD_HELP;
         case 'v': return CMD_VERSION;
         case 'o': outFilename=
                   (char*)malloc(sizeof(char)*(strlen(optarg)+
                   strlen(OUTFILE_EXT)+strlen(SVC_EXT)+1));
                   strcpy(outFilename, optarg);
                   break;
         case '?': return ERR_ARGS;
         }
      }
      nInputFiles = argc-optind;
      if (nInputFiles == 0) {
          doHelp(argv[0]);
	  return ERR_FILE;
      }
      ret = branching?CMD_BRANCH_REDUCE:CMD_REDUCE;
      for (i=0;i<MAX_INFILES && i<nInputFiles && ret != ERR_FILE; i++)
           {
           /* Open the one or more filenames given as arguments */
           int n = 
           sizeof(char)*strlen(argv[optind+i])+strlen(SVC_EXT)+2;
           inFilename = (char*) malloc(n);
           strcpy(inFilename, argv[optind+i]);
           if (!SVCopen(inFile+i, inFilename, SVCread, readIndex+i) || 
                (SVCerrno==EACCESS && 
                !SVCopen(inFile+i, strcat(inFilename,SVC_EXT), SVCread,
                readIndex+i)));         
           else 
                {
                fprintf(stderr, "%s: %s\n", argv[optind+i], SVCerror(SVCerrno));
                ret = ERR_FILE;
                }
           /* readIndex[i] = ATtrue; For the time being: 
           Ignorance of the presence of state vectors in SVC files */
           }
      if (ret == ERR_FILE) return ret;       
      if (nInputFiles == 2) 
           ret = (ret == CMD_REDUCE? CMD_COMPARE:CMD_BRANCH_COMPARE);
      else
           if (nInputFiles>2) ret = ERR_FILE;
      if (nInputFiles>1 || readIndex[0]) *classes = 0;    
      if (ret==CMD_REDUCE || ret == CMD_BRANCH_REDUCE)
           {
           if (!outFilename)
                { 
                char *end = strrchr(inFilename,'.');
                if (end) *end = '\0';
                outFilename=
                (char*)malloc(sizeof(char)*(strlen(inFilename)+
                strlen(OUTFILE_EXT)+strlen(SVC_EXT)+1));
                sprintf(outFilename,"%s%s%s",inFilename,OUTFILE_EXT,SVC_EXT);
                }
           else
                {
                char *tail = strrchr(outFilename,'.');
                if (!tail || strcmp(tail, SVC_EXT)) strcat(outFilename, SVC_EXT);
                }
           /* Open the output file */
           if (cautious && access(outFilename,F_OK)==0) 
                {
                fprintf(stderr, "%s: file already exists\n", outFilename);
                ret=ERR_FILE;
                } 
            else 
                {
                if (SVCopen(outFile, outFilename, SVCwrite, &indexed)<0)
                     {
                     fprintf(stderr, "%s: %s\n", outFilename, SVCerror(SVCerrno));
                     ret=ERR_FILE;
                     }
                SVCsetVersion(outFile , VERSION); 
                }
            }      
      return ret;
      } /* parseArgs */


void doHelp(char *cmd) {
   fprintf(stdout, "Usage: %s [-c][-v][-h][-s][-O][-o outfile] infile [infile2]\n", cmd);
   fprintf(stdout, "The files \"infile\" and \"infile2\" must have \".svc\" format\n");
   fprintf(stdout, "\n");
   fprintf(stdout, "Flags:\n");
   fprintf(stdout, "-c  Cautious mode: don't overwrite existing files\n");
   fprintf(stdout, "-v  Print version number\n");
   fprintf(stdout, "-b  Branching bisimulations w.r.t. \"tau\" or i\n");
   fprintf(stdout, "-h  Print this help info\n");
   fprintf(stdout, "-s  Silent: no logging is printed\n");
   fprintf(stdout, "-o  Output to `outfile'\n");
   fprintf(stdout, "-C  Print equivalence classes\n");
} /* doHelp */



void doVersion(char *progName) {

   fprintf(stdout, "%s %s (%s)\n", progName, VERSION, DATE);

} /* doVersion */



int doReduce(void) 
  {
  SVCstateIndex initState = ReadData(); 
  t_begin=times(&tms_begin);
  Reduce();
  t_end=times(&tms_end);
  if (traceLevel) printTimes();
  WriteData(initState,WITH_TAULOOPS);
  return 0; 
  }
  
int doBranchReduce(void) 
  {
  SVCstateIndex initState = ReadData();
  t_begin=times(&tms_begin);
  SCC();
  /* initState = ReturnEquivalenceClasses(initState, DELETE_TAULOOPS); */
  /* ATwarning("Number of states after deletion of tau loops: %d\n", nstate); */
  ReduceBranching();  
  t_end=times(&tms_end);
  if (traceLevel) printTimes();
  WriteData(initState, DELETE_TAULOOPS);
  return 0; 
  } 
   /* doCompare */
int doCompare(void) 
  {
  SVCstateIndex init1, init2;
  ReadCompareData(&init1, &init2);
  if (Compare(init1, init2)) return EXIT_NOTOK;
  if (traceLevel) ATwarning("Transition systems are strongly bisimilar\n");
  return EXIT_OK; 
  }
   /* doCompare */
int doBranchCompare(void) 
  {
  SVCstateIndex init1, init2;
  ReadCompareData(&init1, &init2);
  if (CompareBranching(init1, init2)) return EXIT_NOTOK;
  if (traceLevel) ATwarning("Transition systems are branching bisimilar\n");
  return EXIT_OK; 
  } /* doCompare */
