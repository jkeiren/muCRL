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

 $Id: svc2txt.c,v 1.2 2005/02/25 10:12:49 uid523 Exp $ */

#include "svc2txt.h"



int main(int argc, char *argv[]) {
   FILE *fpOut;
   int traceLevel;
   ATerm bottom;


   ATinit(argc, argv, &bottom);

   switch(parseArgs(argc, argv,&fpOut,&traceLevel)) {
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
      case CMD_CONVERT:
         exit(doConvert(fpOut, traceLevel));
         break;
      default:
         exit(EXIT_OK);
   }


} /* main */



int parseArgs(int argc, char *argv[], FILE **fpOut, int *traceLevel){
   int c, ret, cautious;
   extern int optind;
   char *inFilename=NULL, *outFilename=NULL;
   SVCbool indexed, allocatedFileName = SVCfalse; 


   *traceLevel=1;
   cautious=0;
   while ((c = getopt(argc, argv, "cho:sv")) != EOF) {
      switch(c){
         case 'c': cautious=1;
                   break;
         case 'h': return CMD_HELP;
         case 'o': outFilename=optarg;
                   break;
         case 's': *traceLevel=0;
                   break;
         case 'v': return CMD_VERSION;
         case '?': return ERR_ARGS;
      }
   }

   if (optind == argc-1) {

      /* Open the filename given as argument */

      inFilename = (char*)malloc(sizeof(char)*(strlen(argv[optind])+strlen(INFILE_EXT)+2));
      strcpy(inFilename, argv[optind]);

      if (SVCopen(&inFile, inFilename, SVCread, &indexed) ==0) {
         ret= CMD_CONVERT;
      } else {

         /* Open the filename given as argument with extension */

         if (SVCerrno==EACCESS){

            sprintf(inFilename,"%s%s", argv[optind],INFILE_EXT);

            if (SVCopen(&inFile, inFilename, SVCread, &indexed) >= 0) {
               ret= CMD_CONVERT;
            } else {
               fprintf(stderr, "%s: %s\n", argv[optind], SVCerror(SVCerrno));
               ret= ERR_FILE;
            }
         } else{
            fprintf(stderr, "%s: %s\n", argv[optind], SVCerror(SVCerrno));
            ret= ERR_FILE;
         }

      }

   } else {

      /* No filename is given as argument: this is an error */

      ret=ERR_ARGS;

   }

   if (ret==CMD_CONVERT) {
         if (outFilename==NULL){

            /* Remove the extension from the input filename */

            if(strlen(inFilename)>strlen(INFILE_EXT) &&
               strcmp(inFilename+strlen(inFilename)-strlen(INFILE_EXT),INFILE_EXT)==0) {
            inFilename[strlen(inFilename)-strlen(INFILE_EXT)]='\0';
         }

         /* Compose output filename */

         outFilename=(char*)malloc(sizeof(char)*(strlen(inFilename)+strlen(OUTFILE_EXT)+1));
	 allocatedFileName = SVCtrue;
         sprintf(outFilename,"%s%s",inFilename,OUTFILE_EXT);

      }

      if (cautious && access(outFilename,F_OK)==0) {
         fprintf(stderr, "%s: file already exists\n", outFilename);
         ret=ERR_FILE;
      } else {

         if ((*fpOut=fopen(outFilename,"w"))!=NULL) {
            ret= CMD_CONVERT;
         } else {
            fprintf(stderr, "%s: %s\n", outFilename,strerror(errno));
            ret= ERR_FILE;
         }
      }

   }

   free(inFilename);
   if (allocatedFileName) free(outFilename); 

   return ret;

} /* parseArgs */



void doHelp(char *cmd) {

   fprintf(stdout, "Usage: %s [-c][-v][-h][-o outfile] infile\n", cmd);
   fprintf(stdout, "\n");
   fprintf(stdout, "Flags:\n");
   fprintf(stdout, "-c  Cautious mode: don't overwrite existing files\n");
   fprintf(stdout, "-v  Print version number\n");
   fprintf(stdout, "-h  Print this help info\n");
   fprintf(stdout, "-s  Silent: no logging is printed\n");
   fprintf(stdout, "-o  Output to `outfile'\n");


} /* doHelp */



void doVersion(char *progName) {

   fprintf(stdout, "%s %s (%s)\n", progName, VERSION, DATE);

} /* doVersion */



int doConvert(FILE *fpOut, int traceLevel) {
   SVCstateIndex fromState, toState;
   SVClabelIndex label;
   SVCparameterIndex parameter;

   if (traceLevel>0) {
      fprintf(fpOut, "Svc version %s\n", SVCgetVersion(&inFile));
      fprintf(fpOut, " date          %s\n", SVCgetDate(&inFile));
      fprintf(fpOut, " version       %s\n", SVCgetVersion(&inFile));
      }
   fprintf(fpOut, " filename      %s\n", SVCgetFilename(&inFile));
   fprintf(fpOut, " type          %s\n", SVCgetType(&inFile));
   fprintf(fpOut, " creator       %s\n",  SVCgetCreator(&inFile));
   fprintf(fpOut, " states        %ld\n", SVCnumStates(&inFile));
   fprintf(fpOut, " transitions   %ld\n", SVCnumTransitions(&inFile));
   fprintf(fpOut, " labels        %ld\n", SVCnumLabels(&inFile));
   fprintf(fpOut, " parameters    %ld\n", SVCnumParameters(&inFile));
 ATfprintf(fpOut, " initial state %t\n", SVCstate2ATerm(&inFile,SVCgetInitialState(&inFile)));
   fprintf(fpOut, " comments      %s\n", SVCgetComments(&inFile));


   while (SVCgetNextTransition(&inFile, &fromState, &label, &toState, &parameter)) {
      ATfprintf(fpOut, "(%t, %t, %t)\n", SVCstate2ATerm(&inFile,fromState), 
                                         SVClabel2ATerm(&inFile,label), 
                                         SVCstate2ATerm(&inFile,toState));
   }

   if (SVCclose(&inFile)<0){
      fprintf(stderr, "File trailer corrupt...\n");
      return -1;
   }

   fclose(fpOut);
   return EXIT_OK;

} /* doConvert */
