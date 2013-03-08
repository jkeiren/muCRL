/* $Id: mgrd.c,v 1.8 2007/02/19 16:01:38 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#define MGRD_C
#include <stdio.h>
#include <param0.h>
#include "utl.h"
#include <errno.h>
#include "mgr.h"
#include "label.h"
#include <sys/stat.h>
#include <sys/select.h>
#include <sys/types.h> 
#include <sys/socket.h> 
#include <string.h>
#define MAXFDS 10


static char hostname[256], clientname[256], cmd[256];
static int mgrdPort, contactPort;
static int local = 0;
static void Acknowledge() {  
    fputc('a', stdout); fflush(stdout); 
    }

static int firstContact(char *s) {
    return 20000+100*s[0]+s[strlen(s)-1];
    }
        
static void AcceptMgr(int socket, int *mgr, FILE **inmgr, FILE **outmgr) {
    *mgr = Accept(socket);
// fprintf(stderr,"accept1\n");
    if (*mgr<0) errormsg("Illegal accept 1"); 
    *inmgr = fdopen(*mgr,"r");
    // fprintf(stderr,"before accept2 %d\n", dbs);
    *outmgr = fdopen(*mgr, "w");
// fprintf(stderr,"m and d accepted\n");
    }
    
static void ExchangeContactMessage(int contact,FILE *outmgr) {
    FILE *in = fdopen(contact,"r"),
         *out = fdopen(contact,"w");
    if (readUTF(in, hostname, 256)<0) errormsg("readutf");
    // fprintf(stderr,"Received Hostname=%s\n", hostname);
    writeintUTF(out, contactPort);
    fflush(out);
// sleep(5);
// printmsg("Client accepted %s %d", hostname, outmgr);
    if (outmgr) {fprintf(outmgr, "%s\n", hostname); fflush(outmgr);} 
    close(contact);
    // printmsg("Open + closed contact: %s", hostname);
    }
    
int main(int argc, char *argv[]) {
     if (!strncmp(argv[1],"gate", 4)) {
      /* Server */
     char *mgrdHost = argv[2], *contactHost = argv[4];
     mgrdPort = atoi(argv[3]);
     contactPort = atoi(argv[5]);
     UTLinit(NULL, NULL, NULL, "mgrd");
     // if (argv[1][4]=='L') {setLocal();local=1;}
     // printmsg("mgrd: Port %d", mgrdPort);
     {
     int socket = serverSocket(mgrdPort,0);
     if (socket<0) errormsg("Illegal server socket");
     {
     FILE *outmgr = NULL, *inmgr; 
     int mgr, contact = -1, ins[2]; 
     struct timeval tv;
     tv.tv_sec = 5;tv.tv_usec = 0;
 // printmsg("Serversocket created socket = %d port = %d", socket, mgrdPort);
     Acknowledge();
     AcceptMgr(socket, &mgr,  &inmgr, &outmgr);
     ins[0] = socket; ins[1]=mgr;
     while (1) {
        fd_set rfds; int i;
        if (contact==-1) {
          int FIRSTCONTACT = firstContact(getenv("USER"));
          // fprintf(stderr,"Firstcontact %d\n",FIRSTCONTACT); 
          contact = contactSocket(contactHost, FIRSTCONTACT, 1);
          // fprintf(stderr,"Contacted: %d\n", FIRSTCONTACT);
          if (contact>=0) ExchangeContactMessage(contact, outmgr);
         }
        FD_ZERO(&rfds); 
        if (contact<0) FD_SET(socket, &rfds); 
        FD_SET(mgr, &rfds); 
	if (select(MAXFDS, &rfds, NULL, NULL, &tv)>0)
	  for (i=0;i<2;i++) if (FD_ISSET(ins[i], &rfds)) {  
          // printf(stderr,"Help i = %d\n", i);
	  if (ins[i]==socket) { 
            // printmsg("1 Accept");
            contact = accept(socket,NULL,NULL);
            // printmsg("2 Accept contact %d", contact);
            if (contact<0) errormsg("Illegal accept 2"); 
            ExchangeContactMessage(contact, outmgr);
	    }
	   else  if (ins[i]==mgr) {
            int tag = fgetc(inmgr);
            switch (tag) {
               case MGR_EXIT:  exit(0);
               case MGR_DISCONNECT: contact=-1; break;
               case MGR_REPORT: {
                    int nseg, i; readintUTF(inmgr, &nseg); 
                    for (i=0;i<nseg;i++, getlabelindex(cmd, 1)) {
                       readUTF(inmgr, clientname, 256);
                       // fprintf(stderr,"%s == %s\n", clientname, mgrdHost);
                       if (!strcmp(clientname,mgrdHost))
                       sprintf(cmd,"%s/mgrd tope%c %s %s %d &", 
                            LIBEXECDIR, local?'L':'N', clientname, hostname, contactPort);
                       else
                       sprintf(cmd,"ssh -T -x %s '%s/mgrd tope%c %s %s %d' &",
                       clientname, LIBEXECDIR, local?'L':'N', clientname, hostname, contactPort);
                       }
                    for (nseg = getlabelcount(), i=0;i<nseg;i++) {   
                       // printmsg("%s", getlabelstring(i));
                       system(getlabelstring(i));
                       }
                    break;
               default: errormsg("%c: Illegal tag read:", tag);
               }
	    }
	  }
       }
     sleep(1);
     }
     }
     }
     } else if (!strncmp(argv[1],"tope", 4)) {
           /* Client */
           char *localHost = argv[2], *contactHost = argv[3], buf[256], cmd[256], *t;
           int sd = -1;
           FILE *in = NULL, *out = NULL;
	       contactPort = atoi(argv[4]);
	       snprintf(cmd,256, "%s;echo %s;%s;echo %s",
"export TERM=xterm", localHost, "top -b  -n 1|grep dinstantiate",
	       "voorbij");
           UTLinit(NULL, NULL, NULL, "top");
           // if (argv[1][4]=='L') setLocal();       
           do {
             // FILE *from = popen("hostname;top -b  -n 1","r");
             FILE *from = popen(cmd,"r");
             if (sd>=0) while (close(sd)!=0) {
                        printmsg("Cannot close");
                        sleep(1);
                        }
             if (in) fclose(in); 
             if (out) fclose(out);
             if ((sd = contactSocket(contactHost, contactPort, 10))<0) errormsg("Illegal sd %s %d", contactHost, contactPort);
             out =fdopen(sd,"w"); in  = fdopen(sd,"r");
             // fprintf(stderr,"Connected %s\n", contactHost);
             while (!feof(from)) {
                 char *s = fgets(buf, 256, from);
                 // fprintf(stderr,"s = %d buf = %d\n", s, buf);
                 // perror(s?s:"Help");
                 if (s) fputs(s , out);
                 }
             pclose(from); fflush(out);  
           } while ((t=fgets(buf, 256,in)) && t[0]=='y'); 
        }
     exit(EXIT_SUCCESS);
     }
