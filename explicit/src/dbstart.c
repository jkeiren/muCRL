/* $Id: dbstart.c,v 1.27 2007/10/09 09:46:26 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#define DBSTART_C
#define E(X) {if ((err=X)<0) errormsg(""#X);}
#ifdef LINUX
#include <unistd.h>
#include <signal.h>
#include <sys/stat.h> 
#include <sys/types.h>
#include <sys/select.h>
#include <stdio.h>
#include <errno.h>
#include "param0.h"
#include <string.h>
#include <assert.h>
#include "utl.h"
#include "vector_db.h"
#include "term_db.h"
#include "stringindex.h"
#include "label.h"
#include "db.h"
#include "mgr.h"
#include "mgr_db.h"

#define MAXFDS 1024
#define INITSIZE 50
#define DBSIZE 256

#define MGR 1

typedef enum {MSGstart, MSGdisconnect,  MSGexit, MSGabort, 
    MSGinform, MSGaction, MSGterm} msg_t;

typedef struct { 
  char *name;
  int srt;
  } nameid_t;

static char dirname[DBSIZE], outputfile[DBSIZE];
static int npars = 0, nsorts = 0, dmp = 0, mgrd = 0, mgrdPort = 0;
static int sockets[MAXFDS], s = 0, ndbs = 0, syncdb = 0, contact = -1;
static nameid_t *nameid; 
static int *traverse, homePort;
static string_index_t sortnamedb = NULL;

typedef struct {
     FILE *r, *w;
     } rw_t;

static rw_t control, rw[MAXFDS];
     
typedef union  {
      db_e  db;
      vdb_t vdb;
      tdb_t tdb;
      } db_t;
      
db_t *fd2db;

typedef struct {
      int level, src, dest, ofs;
      } trace_t;
                       
static vdb_t *nodes; 
static tdb_t tdb, adb, *sortdb, *pardb;

static int adb2contact = 0;

static void Explore(int *queu, int *tree, int *left) {
    int i, right = queu[0];
    for (i=*left;i<right;i++) {
       int elm0 = DISmapNodeId(queu[i], 0, npars),
           elm1 = DISmapNodeId(queu[i], 1, npars);
       if (elm0>0) {
              tree[3*i-2]=3*queu[0];
              queu[queu[0]++]=elm0; 
              }
       if (elm1>0) {
              tree[3*i-1]=3*queu[0];
              queu[queu[0]++]=elm1;
              }
       tree[3*(i-1)]=queu[i];  
       }
    *left = right;
    }

static int *Traverse(void) {
    int *queu =calloc(2*npars, sizeof(int)),
        *tree =calloc(2*npars*3, sizeof(int));
    int left = 1, i;  
    queu[0]++; 
    queu[queu[0]++]=2;queu[queu[0]++]=3;
    while (left<queu[0]) Explore(queu, tree, &left);
    queu[0]--;
    return tree;
    }
    
static void ControlInit(void) {
   getlabelindex("start", 1);
   getlabelindex("disconnect", 1);
   getlabelindex("exit", 1);
   getlabelindex("abort", 1);
   getlabelindex("inform", 1);
   getlabelindex("action", 1);
   getlabelindex("term", 1);
   }

static char *finish = "#";

static void Start(void) {
    int i, err;
    if (control.w) {
       int n = 3*(2*npars-2);
       E(printUTF(control.w, getlabelstring(MSGstart)));
       writeintUTF(control.w, npars);
       writeintUTF(control.w, nsorts);
       for (i=0;i<npars;i++) printUTF(control.w, nameid[npars+i].name);
       for (i=0;i<nsorts;i++) printUTF(control.w, SIget(sortnamedb, i));
       for (i=0;i<n;i++) {
           if ((i%3)!=0) 
              {E(writeintUTF(control.w,traverse[i]));}
           else {
               if (traverse[i]<npars) /* Index for data */ {
                 {E(writeintUTF(control.w, traverse[i]));}
                 }
              else {
                 {E(printUTF(control.w, nameid[traverse[i]].name));}
              }
           }
          }
       E(printUTF(control.w, finish));
       fflush(control.w);
       }
    }


static void Action(void) { 
     if (control.w) { 
       int i, n = TDBgetCount(adb);
       printUTF(control.w, getlabelstring(MSGaction));
       for (i=adb2contact;i<n;i++) {
           // printmsg("%s", ATgetName(ATgetAFun(TDBget(adb, i))));
           printUTF(control.w, ATgetName(ATgetAFun(TDBget(adb, i)))); 
           }
       printUTF(control.w,finish); 
       fflush(control.w);
       adb2contact = n;
       }
     // printmsg("Informed");
     } 

static void Term(void) { 
     if (control.w) { 
       int i;
       printUTF(control.w, getlabelstring(MSGterm));
       for (i=0;i<npars;i++) {
           writeintUTF(control.w, TDBgetCount(pardb[i])); 
           }
       for (i=0;i<nsorts;i++) {
           writeintUTF(control.w, TDBgetCount(sortdb[i])); 
           }
       printUTF(control.w,finish); 
       fflush(control.w);
       }
     // printmsg("Informed");
     }
                  
static void Inform(void) {  
     if (control.w) { 
       int i, n = npars-2, err;  
       printUTF(control.w, getlabelstring(MSGinform));
       writeintUTF(control.w,TDBgetCount(tdb));
       writeintUTF(control.w,TDBgetCount(adb));
       for (i=2;i<npars;i++) {
           E(writeintUTF(control.w, VDBgetCount(nodes[i]))); 
           }
       printUTF(control.w,finish); 
       fflush(control.w);
       }
     // printmsg("Informed");
     }

static void Exitted() {
    int err;
    if (control.w) {
       Inform();
       E(printUTF(control.w, getlabelstring(MSGexit)));
       E(printUTF(control.w, finish));
       fflush(control.w);
       }
    } 
            
static int SelectAction(int idx) {
   int err;
   switch (idx) {
      case MSGstart: Start(); return 1;
      case MSGexit: return 1;
      case MSGabort: return 0;
      case MSGinform:  Inform(); return 1;
      case MSGaction:  Action(); return 1;
      case MSGterm:    Term(); return 1;
      case MSGdisconnect:  return 0;
      default: errormsg("Illegal tag: %d", idx);
      }
   return 0;
   }
   
static void HandleMessage(void) {
   char msg[256];
   int idx, go, err;
   if (!control.r) return;
   E(readUTF(control.r, msg, 256));
   // printmsg("HandleMessage %s", msg);
   idx = getlabelindex(msg, 0);
   go = SelectAction(idx);
   E(readUTF(control.r, msg, 256));
   if (!go) {
       fclose(control.r); fclose(control.w); 
       control.w = control.r = NULL; 
       sockets[contact] = -1; contact =  -1;
       }
   if (strcmp(msg,finish)) errormsg("Msg %s not equal to expected %s",
   msg, finish);
   // printmsg("HandleMessage %s finished", msg);
   }
    
static void handler(int signum) {
    exit(0);
    }
    
static void AtExit(void) {
/* Needed for flushing */
    TDBdestroy(tdb);
    TDBdestroy(adb);
    }
    
static void ShutStop(void) {
    int i;
    for (i=1;i<s;i++)
    if (sockets[i]>=0&& i!=contact) close(sockets[i]);
    // fcloseall();
    Exitted();
    errorreset();printmsg("exits");
    }
                   
static void WarningHandler(const char *format, va_list args) {
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }

static void ErrorHandler(const char *format, va_list args) {
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n"); 
     }
        
static int lcb(int id, VDBload_t kind, int count, elm_t *elm) {
     if (kind==VDBbarrier) {
        return 0;
        }
     if (elm[0]>=0) {
       int elm0 = DISmapNodeId(id, 0, npars);
       if (elm0<npars) 
          {
          if (VDBget(nodes[elm0], NULL, elm[0])<0) return -1;
          }
        else 
          {
          if (!TDBget(tdb, elm[0])) return -1;
          }
        }
     if (elm[1]>=0) {
       int elm1 = DISmapNodeId(id, 1, npars);
       if (elm1<npars) 
          {if (VDBget(nodes[elm1], NULL, elm[1])<0) return -1;}
        else 
          {if (!TDBget(tdb, elm[1])) return -1;}
        }
     return 0;
     } 
      
static char *DBSname(int i) {
     char buf[80];
     sprintf(buf,"vdb.%d", i);
     return strdup(buf);
     }
     
static void AppendProcessParameters() {
     char *par; int i; 
     char *pars, *srts, *srt;
     pars = strdup(getenv("MCRL_PARS"));
     pars[strlen(pars)-1]='\0';
     for (i=npars, (par=strtok(pars+1," "));par;par=strtok(NULL," "), i++) {
        nameid[i].name = par;
        }
     srts = strdup(getenv("MCRL_PARS"));
     srts[strlen(srts)-1]='\0';
     for (i=npars, (srt=strtok(srts+1," "));srt;srt=strtok(NULL," "), i++) {
        nameid[i].srt = SIlookup(sortnamedb, strrchr(srt,'#')+1); 
        }
     }

static void OpenConnection(int i) {     
      if (!rw[i].r) {
        if (!(rw[i].r = fdopen(sockets[i],"r")))
        errormsg("Illegal rd channel %d", sockets[i]);
        // sleep(1);
        }
      if (!rw[i].w) {
      if (!(rw[i].w = fdopen(sockets[i],"w")))
        errormsg("Illegal wr channel %d", sockets[i]);
       } 
      } 
 
static int getCount(int id) {     
     switch (fd2db[id].db->type) {
        case VDB: return VDBgetCount(fd2db[id].vdb);       
        case TDB: return TDBgetCount(fd2db[id].tdb); 
	}
    }
 
static int OpenMgrConnection(int socket) { 
   int left = getCount(2<npars?2:npars),
   right = getCount(3<npars?3:npars), tag; 
   sockets[MGR] = Accept(socket); // mgr
   // rw[MGR].r = fdopen(sockets[MGR],"r");rw[MGR].w = fdopen(sockets[MGR],"w");  
   OpenConnection(MGR); 
   C_mgr2db_tag(rw[MGR].r, &tag);
   if (tag != MGR_DBSTART) errormsg("OpenMgrConnection: tag = %d != %d", 
          tag, MGR_DBSTART);
   C_db2mgr_leftright(rw[MGR].w, &left, &right); 
   return MGR+1;
   } 
   
                     
int main(int argc, char *argv[]) {
     char **newargv = (char**) calloc(argc, sizeof(char*)), *ptr;
     int i = 0, j = 0, err = 0, restore = 0, ready = 0;
     char *text; 
     newargv[j++] = argv[i++];
     ATinit(argc, argv, (ATerm*) &argc);
     ATsetWarningHandler(WarningHandler);
     ATsetErrorHandler(ErrorHandler);
     signal(SIGINT, handler);
     signal(SIGTERM, handler);
     signal(SIGPIPE, handler);
     signal(SIGKILL, handler);
     signal(SIGALRM, handler);
     signal(SIGQUIT, handler);
     signal(SIGHUP, handler);
     for (;i<argc;i++) {
        if (!strcmp(argv[i],"-dmp")) {
            dmp = 1;
            continue;
            }
        if (!strcmp(argv[i],"-restore")) {
            restore = 1;
            continue;
            }
        if (!strcmp(argv[i],"-npars")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *endptr = NULL;
                npars = strtol(argv[i],&endptr,10);
                if (*endptr != '\0') ATerror("Number expected after \"-npars\"");
                }
            else
                ATerror("Integer (number of parameters) expected after %s\n",argv[i-1]);
            continue;
            }
	 if (!strcmp(argv[i],"-port")) {
            if ((++i)<argc && strncmp(argv[i],"-",1)) {
                char *endptr = NULL;
                homePort = strtol(argv[i],&endptr,10);
                if (*endptr != '\0') ATerror("Number expected after \"-npars\"");
                }
            else
                ATerror("Integer (number of parameters) expected after %s\n",argv[i-1]);
            continue;
            }      
        newargv[j++] = argv[i];
        }
     UTLinit(NULL, NULL, NULL, "dbstart");
     if (homePort == 0) 
         homePort = atoi(getenv("DBPORT")?getenv("DBPORT"):"1953");
     if (getenv("MCRL_LOCAL")) setLocal(); 
     ControlInit();
     nameid = calloc(2*npars, sizeof(nameid_t));
     nameid[0].name = "adb"; nameid[1].name = "tdb";
     for (i=2;i<npars;i++) nameid[i].name = DBSname(i);
     text = getenv("MCRL_TEXT");
     if (text && !strcmp(text,"-text")) setText();
     SIcreate(&sortnamedb);
     {int idx;
     char *srts = strdup(getenv("MCRL_PARS")), *srt;
     srts[strlen(srts)-1]='\0';
     for (srt=strtok(srts+1," ");srt;srt=strtok(NULL," ")) 
         SIput(sortnamedb, strrchr(srt,'#')+1, &idx); 
     }   
     nsorts = SIgetCount(sortnamedb);
     AppendProcessParameters();
     strncpy(outputfile, argv[argc-1], DBSIZE);
     if ((ptr=strrchr(outputfile,'.')) && !strcmp(ptr,".tbf"))
        *ptr = '\0'; 
     sprintf(dirname,"%s.dmp/NODES", outputfile);
     traverse=Traverse();
     nodes =  (vdb_t*) calloc(npars, sizeof(vdb_t));
     pardb = (tdb_t*)  calloc(npars, sizeof(tdb_t));
     sortdb = (tdb_t*)  calloc(nsorts, sizeof(tdb_t));
     for (i=0;i<npars;i++) pardb[i] = TDBcreate(i, NULL, NULL);
     for (i=0;i<nsorts;i++) sortdb[i] = TDBcreate(i, NULL, NULL);
     tdb = TDBcreate(0, dmp?path(dirname,"a+", "tdb"):NULL, NULL);
     adb = TDBcreate(0, dmp?path(dirname,"a+", "adb"):NULL, NULL);
     if (atexit(AtExit)<0) {fprintf(stderr,"atexit\n");exit(1);}
     for (i=npars-1;i>=2;i--) {
        // printmsg("VDBcreate %d %lx", i, nodes_d[i]->file);
        if (!(nodes[i] = VDBcreate(i, 2, 
	dmp?path(dirname,"a+", "vdb.%d",i):NULL, 
	NULL, NULL, NULL, NULL, NULL, lcb))) errormsg("VDBcreate"); 
        }
     errorreset();
      /* if (fork()==0) */ {
        int go_on = 1;   
        //  struct timeval tv;
        int socket = serverSocket(homePort,1000000);
        fd_set rfds; 
        // fprintf(stderr,"DBS: serversocket %d\n", homePort);
        // fprintf(stderr, "Forked npars = %d socket = %d\n", npars, socket);
        fd2db = (db_t*) calloc(npars+2, sizeof(db_t));
        E(socket); 
        printmsg("Database server uses port %d", homePort);
        if (atexit(ShutStop)<0) {fprintf(stderr,"atexit\n");exit(1);}
        // tv.tv_sec = 1; tv.tv_usec = 0;
        memset(sockets, -1, sizeof(int)*MAXFDS);
        memset(rw, 0, sizeof(rw_t)*MAXFDS);
        for (i=2;i<npars;i++) fd2db[i].vdb = nodes[i];
        fd2db[npars+1].tdb = adb; fd2db[npars].tdb = tdb;
        errorreset();
        sockets[s++] = socket;sockets[s++] = -1;
	fputc('y', stdout);fflush(stdout);
	s = OpenMgrConnection(socket); 
        while (1) {
           int r=0; 
           // fprintf(stderr, "Wait %d\n", s);
	   FD_ZERO(&rfds); 
           FD_SET(sockets[0], &rfds);
           if (go_on) {
             for (i=MGR;i<s;i++) {
	     // fprintf(stderr,"Set %d %d\n", i, sockets[i]);
             if (sockets[i]>=0) FD_SET(sockets[i], &rfds);
	     }
             }
           if ((r=select(MAXFDS, &rfds, NULL, NULL, NULL))>0) 
           for (i=0;r>0 && i<s;i++) {
             if (sockets[i]>=0 && FD_ISSET(sockets[i], &rfds)) {
                  // fprintf(stderr, "DBS:Select %d\n", i);
               switch (i) {
                 case 0: {
                   int client = Accept(socket);
                   sockets[s]=client;
                   OpenConnection(s);
                   ndbs++; s++; 
                   break;
                   }
		 case MGR: {
		  int tag; C_mgr2db_tag(rw[i].r, &tag);
		  switch(tag) {
		   case MGR_INSPECT: { int act; char *s;
		    C_mgr2db_act(rw[i].r, &act);
                    // fprintf(stderr,"Received %d\n", act);
                    {
                    term_t t =TDBget(adb, act);
                    if (!t) errormsg("Term belonging to %d not found", act);
		    s = ATgetName(ATgetAFun(t));
		    C_db2mgr_string(rw[i].w, &s);
                    }
		    break;
		    }
                    case MGR_CONTACT: {
                      char contactname[256]; int j, c;
                      fgets(contactname, 256, rw[i].r);
                      contactname[strlen(contactname)-1]='\0';
   // fprintf(stderr,"DBS:Received contactname %s\n", contactname);
                      mgrdPort = atoi(getenv("MCRL_MGRDPORT"));
                      {
                      int port = mgrdPort+10000,
                      cs = contactSocket(contactname, port, 1);
                      if (cs<0) {
                          printmsg("Cannot connect with (%s, %d)",
                          contactname, port);
                          break;
                          }
                      for (j=2;j<s;j++) if (sockets[j]<0) break;
                      sockets[j] = cs;
                      control.r = fdopen(cs,"r");
                      if (j==s && sockets[j]>=0) s++;
                      if (!(control.w = fdopen(cs, "w")))
                          errormsg("Illegal wr channel %d", cs);
		      contact = j; // contact is index
                      }
                    break;
                    }
                    case MGR_EXIT: 
                       break;   
		    default: errormsg("Illegal tag: %c", tag);
		   }; break;
		  }  
                 default: {
                 if (i==contact) {
                     HandleMessage();
                    } else {
                 int id, parpos = -1;
                 E(readintUTF(rw[i].r, &id));
                 // printmsg("i = %d id = %d", i, id);
                 if (id== -1) {
                     errorreset();
                     // printmsg("Channel %d is closed", sockets[i]);
                     sockets[i]=-1;
                     ndbs--;
                     if (ndbs==0) {
                         exit(0);
                         }
                     }
		 else
                 {
                 if (id<-2 || id>2*npars+1) 
                         errormsg("ID: 1<=%d<=%d", id, 2*npars+1);
		 if (id>npars+1) {
		     parpos = id-npars-2;
                     id = npars;
		     }
                 if (fd2db[id].db) {
                 switch (fd2db[id].db->type) {
                   case VDB: VDBreact(fd2db[id].vdb, (channel_t) (rw+i)); break;        
                   case TDB: { 
		      idx_t idx = TDBreact(fd2db[id].tdb, (channel_t) (rw+i));
		      if (parpos>=0) {
                         if (idx >=0) {
// ATwarning("QQQ parpos = %d idx = %d", parpos, idx);
		            term_t term = TDBget(tdb, idx);
			    TDBput(pardb[parpos], term, NULL);
			    TDBput(sortdb[nameid[npars+parpos].srt], term, NULL);
// fprintf(stderr,"%d\n", nameid[npars+parpos].srt);
/* fprintf(stderr,"Test %s %d  %d\n", nameid[parpos].name, nameid[parpos].srt, 
   TDBgetCount(sortdb[nameid[parpos].srt])); */
                            }
		         }
		      break;
		      }
                   }
                 } else errormsg("System error id = %d", id); 
                 }
                 }
                 }
                 } /* Switch */
              } /* for */ 
             } /* If for */  
             } /* While */
           printmsg("Illegal exit");
           } 
           }
#else
main(){}
#endif
