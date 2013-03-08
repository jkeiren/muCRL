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

 $Id: aut2svc.h,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */

#ifdef __cplusplus
extern "C" {
#endif 

#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include "aterm1.h"
#include "svcerrno.h"
#include "svc.h"

#define EXIT_OK 0
#define EXIT_ERR_ARGS -1
#define EXIT_ERR_FILE -2
#define EXIT_ERR_INPUT -3

#define ERR_ARGS 1
#define ERR_FILE 2
#define CMD_HELP 3
#define CMD_VERSION 4
#define CMD_CONVERT 5

#define INFILE_EXT  ".aut"
#define OUTFILE_EXT ".svc"


extern int  errno;
extern FILE *yyin;
       SVCfile outFile;

char *programName=NULL;



int  parseArgs(int, char **, FILE **, SVCfile *, int *);
void doHelp(char *);
void doVersion(char *);
int  doConvert(FILE *, SVCfile *, int);

int yyparse(void);
#ifdef __cplusplus
}
#endif 

