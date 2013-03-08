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

   $Id: svcinfo.c,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */

#include "svcinfo.h"



int main(int argc, char *argv[]) {
   FILE *fpOut;
   ATerm bottom;


   ATinit(argc, argv, &bottom);

   switch(parseArgs(argc, argv,&fpOut)) {
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
      case CMD_INFO:
         exit(doInfo(fpOut));
         break;
      default:
         exit(EXIT_OK);
   }


} /* main */



int parseArgs(int argc, char *argv[], FILE **fpOut){
   int c, ret;
   extern int optind;
   char *inFilename=NULL;
   SVCbool indexed;


   while ((c = getopt(argc, argv, "hv")) != EOF) {
      switch(c){
         case 'h': return CMD_HELP;
         case 'v': return CMD_VERSION;
         case '?': return ERR_ARGS;
      }
   }

   if (optind == argc-1) {

      inFilename = (char*)malloc(sizeof(char)*(strlen(argv[optind])+strlen(INFILE_EXT)+2));
      strcpy(inFilename, argv[optind]);

      if (SVCopen(&inFile, inFilename, SVCread, &indexed) ==0) {
         ret= CMD_INFO;
      } else {

         /* Open the filename given as argument with extension */

         if (SVCerrno==EACCESS){

            sprintf(inFilename,"%s%s", argv[optind],INFILE_EXT);

            if (SVCopen(&inFile, inFilename, SVCread, &indexed) >= 0) {
               ret= CMD_INFO;
            } else {
               fprintf(stderr, "%s: %s\n", argv[optind], SVCerror(SVCerrno));
               ret= ERR_FILE;
            }
         } else{
            fprintf(stderr, "%s: %s\n", argv[optind], SVCerror(SVCerrno));
            ret= ERR_FILE;
         }

      }
      free(inFilename);

   } else {

      /* No filename is given as argument: this is an error */

      ret=ERR_ARGS;

   }

   if (ret==CMD_INFO) {

      *fpOut=stdout;
   }

   return ret;

} /* parseArgs */



void doHelp(char *cmd) {

   fprintf(stdout, "Usage: %s [-v][-h] infile\n", cmd);
   fprintf(stdout, "\n");
   fprintf(stdout, "Flags:\n");
   fprintf(stdout, "-v  Print version number\n");
   fprintf(stdout, "-h  Print this help info\n");

} /* doHelp */



void doVersion(char *progName) {

   fprintf(stdout, "%s %s (%s)\n", progName, VERSION, DATE);

} /* doVersion */



int doInfo(FILE *fpOut) {

   fprintf(stderr, "Svc version %s %s\n", SVCgetFormatVersion(&inFile),SVCgetIndexFlag(&inFile)?"(indexed)":"");
   fprintf(stderr, " filename      %s\n", SVCgetFilename(&inFile));
   fprintf(stderr, " date          %s\n", SVCgetDate(&inFile));
   fprintf(stderr, " version       %s\n", SVCgetVersion(&inFile));
   fprintf(stderr, " type          %s\n", SVCgetType(&inFile));
   fprintf(stderr, " creator       %s\n",  SVCgetCreator(&inFile));
   fprintf(stderr, " states        %ld\n", SVCnumStates(&inFile));
   fprintf(stderr, " transitions   %ld\n", SVCnumTransitions(&inFile));
   fprintf(stderr, " labels        %ld\n", SVCnumLabels(&inFile));
   fprintf(stderr, " parameters    %ld\n", SVCnumParameters(&inFile));
 ATfprintf(stderr, " initial state %t\n", SVCstate2ATerm(&inFile,SVCgetInitialState(&inFile)));
   fprintf(stderr, " comments      %s\n", SVCgetComments(&inFile));

   if (SVCclose(&inFile)<0){
      fprintf(stderr, "File trailer corrupt...\n");
      return -1;
   }

   fclose(fpOut);
   return EXIT_OK;

} /* doInfo */
