/* $Id: mgr.c,v 1.11 2006/11/22 15:26:50 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#ifdef LINUX
#define MGR_C
#include <unistd.h>
#include <stdio.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/select.h>
#include <sys/types.h> 
#include "param0.h"
#include "utl.h"
#include "mgr.h"
#define DBSIZE 80

static char *finish = "#";
static FILE *control = NULL, *answer = NULL;
static char hostname[DBSIZE], portname[DBSIZE];
static int port, sd, sd2, port2;

static void printExit(int client) {
   control = fdopen(client,"w");
   printUTF(control, "abort");
   printUTF(control, finish);
   fflush(control);
   }
        
int main(int argc, char *argv[]) {
     int aux, mgr;
     UTLinit(NULL, NULL, NULL, "mgr");
     aux = atoi(portname);
     if (argc!=3) errormsg("Enter \"mgr <job_id> <host_name>\""); 
         {
         int aux1 = atoi(argv[1]);
         if (aux1!=0) {sprintf(portname,"%s", argv[1]);aux=aux1;}
         else errormsg("Enter \"mgr <job_id> <host_name>\""); 
         sprintf(hostname,"%s", argv[2]);
         }
     /* To mgrd */ 
     port = aux%10000+30000;
     port2 = port+30000;
     printmsg("clientsocket %s %d", hostname, port);
     if ((sd = clientSocket(hostname, port,0))<0) errormsg("Illegal sd");
     if (sd<0) 
         errormsg("Cannot open client socket (%s, %d)", hostname, port);
     control =fdopen(sd,"w");  answer =fdopen(sd,"r");
     if (!control) errormsg("Manager daemon is not active");
     errorreset();
     if (gethostname(hostname, 256)<0) strcpy(hostname,"localhost");
     printUTF(control, hostname); fflush(control);
     if (readintUTF(answer, &port2)<0) 
           errormsg("readUTF %s %d", hostname, port);
 /* printmsg("Hostname %s send  answered %d", hostname, port2); */
     fclose(control);
     sd2 = serverSocket(port2,0);
     if (sd2<0) errormsg("Cannot open socket (%s, %d)", hostname, port2);
     mgr = Accept(sd2);
     if (mgr<0) errormsg("Illegal accept");
     printExit(mgr);
     sleep(2);
     exit(EXIT_SUCCESS);
     }
#else
main(){}
#endif
