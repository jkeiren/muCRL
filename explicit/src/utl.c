/* $Id: utl.c,v 1.16 2007/10/09 09:46:26 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <string.h>
#include <libgen.h>
#include "param0.h"
#include "utl.h"
#define id_size 128
#define msg_size 1024
#define utf_size 1024
#define DSIZE 100
#define MAXDIGITS 10
#define MAXFDS 20
#ifdef LINUX
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <netdb.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/select.h>
#include <sys/un.h>
#include <netinet/in.h>
#include <netinet/tcp.h> 
#include <dirent.h>
#endif


static char id[id_size], msg[msg_size];
static int code = 0, msg_pt = 0;
static FILE *fp = NULL, *tty;
static char *msg_error, *msg_print;
static char *socketdir= NULL;

typedef int (*readPair_t)(FILE *f, int32_t *elm);
typedef int (*writePair_t)(FILE *f, int32_t *elm);

typedef struct {
    readPair_t readPair;
    writePair_t writePair;
    int record_size;
    } io_t;

void setLocal() {
    char *tmp = getenv("TMPDIR")?getenv("TMPDIR"):"/tmp";
    socketdir = calloc(256, sizeof(char));
    // sprintf(socketdir, "%s/sockets/", getenv("HOME")); 
    sprintf(socketdir, "%s/", tmp); 
    }

static char *socketFile(int port) {
    static int n = -1;
    if (n<0) n = strlen(socketdir);
    else socketdir[n]='\0';
    sprintf(socketdir+n,"%d", port);
    // printmsg("socketdir:%s", socketdir);
    return socketdir;
    }
    
static char *UTLformat1(void) {
     static char *format = NULL;
     if (!format) {
         format = (char*) malloc(10);
         sprintf(format,"%%%dd\n",MAXDIGITS);
         }
     return format;
     }
     
static char *UTLformat2(void) {
     static char *format = NULL;
     if (!format) {
         format = (char*) malloc(10);
         sprintf(format,"%%%dd%%%dd\n",MAXDIGITS, MAXDIGITS);
         }
     return format;
     }
     
static int readPairText(FILE *f, int32_t *elm) {
    char bf[MAXDIGITS*2+2];
    if (fgets(bf, MAXDIGITS*2+2, f)) {
      // fprintf(stderr, "Hallo %s", bf);
      return sscanf(bf, UTLformat2(), elm, elm+1)==2;
      }
    return 0;
    }
    
static int writePairText(FILE *f, int32_t *elm) {
   int  err;
   if ((err=fseek(f, 0, SEEK_END))<0) return err;
/*
#ifdef LINUX
   if (ftell(f) < info.st_size) return 2; 
#endif
*/
   err = fprintf(f, UTLformat2(), elm[0], elm[1]);
// printmsg("writepair %d err= %d %lx (%d,%d)", ftell(f), err, f, elm[0], elm[1]);
   return err;
   } 

static int readPairBinary(FILE *f, int32_t *elm) {
   static int first = 1;
   // fprintf(stderr,"readPair %d<%d\n", ftell(f), FileLen(f)); 
    if (ftell(f)>=0 && ftell(f)==FileLen(f)) return 0;
    if (fread(elm, sizeof(int32_t), 2, f)==1) fread(elm+1, sizeof(int32_t), 1, f);
    if (first==1) {
        /* Test if it is binary file */
        short v = elm[0];
        char *space = "  ";
        if (!memcmp(&v, space, sizeof(short))) {
             /* Tekst file */
             rewind(f);
             setText();
             // printmsg("Text file encountered");
             return readPairText(f, elm);
             }
        first  = 0;
        }
    return 1;
    }
    
static int writePairBinary(FILE *f, int32_t *elm) {
   return (fwrite(elm, sizeof(int32_t), 2, f)==2)?0:-1;
   } 
   
int writeBinary(FILE *f, int32_t *elm, int n) {
   return (fwrite(elm, sizeof(int32_t), n, f)==n)?0:-1;
   }

int readBinary(FILE *f, int32_t *elm,int n) {
   // fprintf(stderr,"readPair %d<%d\n", ftell(f), FileLen(f)); 
    if (ftell(f)>=0 && ftell(f)==FileLen(f)) return 0;
    return fread(elm, sizeof(int32_t), n, f);
    }  
            
static io_t io = 
{readPairBinary, writePairBinary, 2*sizeof(int32_t)};
// {readPairText, writePairText, 21}; 
   
int UTLinit(FILE *msg_fp, char *print_tag, char *error_tag, const char* format, ...) {
   static int new = 1;
       if (new) {
       int n;
       va_list ap;
       va_start(ap, format);
       // tty = fopen("/dev/tty", "w");
       errno = 0;
       n= vsnprintf(id, id_size, format, ap);
       va_end(ap);
       new = 0;
       fp = msg_fp?msg_fp:stderr;
       msg_print = print_tag; msg_error = error_tag;
       return (n<0 || n==id_size)?-1:0;
       }
   return 0;
   }
   
void setBinary(void) {
   io.readPair = readPairBinary;
   io.writePair = writePairBinary;
   io.record_size = 2*sizeof(int32_t);
   }
   
void setText(void) {
   io.readPair = readPairText;
   io.writePair = writePairText;
   io.record_size = 21;
   } 
                
char *errortxt(int errcode) {
   switch (errcode) {
      case ERR_FULL: return "Buffer is full";
      case ERR_EMPTY: return "Buffer is empty";
      case ERR_READ:return "Cannot read";
      case ERR_WRITE:return "Cannot write";
      case ERR_FILE_NULL:return "File is not defined";
      case ERR_DIR_NULL:return "Directory is not defined";
      case ERR_NULL:return "";
      case ERR_INCOMPAT:return "Version clash";
      case ERR_PARSE:return "Parse error";
      default: return "errorinfo:illegal errorcode";
      }
   return NULL;
   }

void errormsg(const char *format, ...) {
   va_list ap;
   if (msg_error!=NULL) fprintf(fp, "%s", msg_error);
   va_start(ap, format);
   fprintf(fp,"%s", id);
   if (strlen(format)>0 && strlen(id)>0) fprintf(fp,":");
   vfprintf(fp, format, ap);
   if (code<0) {
        fprintf(fp,"%s", msg);
        if (code!=ERR_NULL) fprintf(fp,":%s", errortxt(code)); code = 0;
        }
   if (errno!=0) {
        fprintf(fp,":"); 
        fprintf(fp,"%s", strerror(errno)); 
        errno = 0;
        }
   fprintf(fp,"\n");
   fflush(fp);
   msg_pt = 0;
   va_end(ap);
#ifdef NDEBUG
   exit(1);
#else
   exit(1);
#endif
   }

void errorreset(void) {
     msg[0]='\0'; 
     code = 0;
     errno = 0;
     }
       
void printmsgv(const char *format, va_list ap) {
   if (msg_print!=NULL) fprintf(fp, "%s", msg_print);
   fprintf(fp,"%s", id);
   if (strlen(format)>0 && strlen(id)>0) fprintf(fp,":");
   vfprintf(fp, format, ap);
   if (code<0) {
        fprintf(fp,"%s", msg);
        fprintf(fp,":%s", errortxt(code)); code = 0;
        }
   if (errno!=0) {
        fprintf(fp,":");
        fprintf(fp,"%s", strerror(errno));  
        errno = 0;
        }
   fprintf(fp,"\n");
   fflush(fp);
   msg_pt = 0;
   }
   
void printmsg(const char *format, ...) {
   va_list ap;
   va_start(ap, format);
   printmsgv(format, ap);
   va_end(ap);
   }

int mkerrorv(int errcode, const char *format, va_list ap) {
   code = errcode;
   strcpy(msg+msg_pt,":");msg_pt++; 
   msg_pt += vsnprintf(msg+msg_pt, (size_t) msg_size-msg_pt, format, ap);
   return errcode;
   }
   
int mkerror(int errcode, const char *format, ...) {
   int r;
   va_list ap;
   va_start(ap, format);
   r = mkerrorv(errcode, format, ap);
   va_end(ap);
   return r;
   }
   
int errorcode(void) {return code;}

file_t UTLopen(char *dir, char *mode, const char *format, ...) {
     char buf[256];
     FILE *f;
     va_list ap;
     va_start(ap, format);
     strcpy(buf, dir);
     vsprintf(buf+strlen(buf), format, ap);
     if (CreateEmptyDir(strdup(dirname(strdup(buf))), DELETE_NONE)<0) errormsg("%s", buf);
     f = fopen(buf, mode);
     if (!f) errormsg("%s", buf);
     return f;
     }

int readUTF(FILE *f, char *data, int size) {
    int err =fread(data, sizeof(char), sizeof(uint16_t), f), N;
    if (err!=sizeof(uint16_t)) 
       errormsg("readUTF16 %d!=%d", err, sizeof(uint16_t));
    N = NtoHS(*((uint16_t*) data));
    if (N>=size-1) errormsg("readUTF N=%d>=%d=size", N, size-1);
    err = fread(data, sizeof(char), (size_t) N, f);
    if (err!=N) errormsg("readUTF %d!=%d", err, N);
    data[err]='\0';
    // fprintf(stderr, "Okay fread was %s\n", data);
    return err;
    }     

int readUTF32(FILE *f, char *data, int size) {
    int err=fread(data, sizeof(char), sizeof(uint32_t), f), N;
    if (err!=sizeof(uint32_t)) 
       errormsg("readUTF32 %d!=%d", err, sizeof(uint32_t));
    N = NtoHL(*((uint32_t*) data));
    if (N>=size-1) errormsg("readUTF32 N=%d>=%d=size", N, size-1);
    err = fread(data, sizeof(char), (size_t) N, f);
    if (err!=N) errormsg("readUTF32 %d!=%d", err, N);
    data[err]='\0';
    // fprintf(stderr, "Okay fread was %s\n", data);
    return err;
    }     

    
int writeUTF32(FILE *f, char *data, int N) {
    size_t size = sizeof(uint32_t)+N*sizeof(char);
    DECLA(char, utf, size);
// fprintf(stderr,"writeUTF32 N=%d %s\n", N, data);
    N = (int) HtoNL((uint32_t) N);
    memcpy(utf, &N, sizeof(uint32_t));
    memcpy(utf+sizeof(uint32_t),data, size-sizeof(uint32_t));
    return fwrite(utf, sizeof(char), size, f);
    }

int writeUTF(FILE *f, char *data, int N) {
    size_t size = sizeof(uint16_t)+N*sizeof(char);
    uint16_t m = (uint16_t) N;
// fprintf(stderr,"writeUTF m=%d %s\n", m, data);
    DECLA(char, utf, size);
    m = HtoNS(m);
    memcpy(utf, &m, sizeof(uint16_t));
    memcpy(utf+sizeof(uint16_t),data, size-sizeof(uint16_t));
    return fwrite(utf, sizeof(char), size, f);
    }

char *readstringUTF32(FILE *f) {
    static char *utf = NULL;
    uint32_t  N = 0;
    static uint32_t size = 0;
    int err =fread(&N, sizeof(char), sizeof(uint32_t), f);
    if (err!=sizeof(uint32_t)) 
                 errormsg("readstring32 %d!=%d", err, sizeof(uint32_t));
    N = NtoHL(N);
    if (N>=size) {
        size = N+1<=utf_size?utf_size:N+1;
// printmsg("Readstring32 resize %d", size);
        utf=realloc(utf, size);
        if (!utf) 
             errormsg("readstring32 realloc size = %d", size);
        }
    err = fread(utf, sizeof(char), N, f);
    if (err!=N) errormsg("readstring32 %d!=%d", err, N);
    utf[err]='\0';
 // printmsg("readstring32= %s N=%d err = %d size=%d", utf, N, err,utf_size);
    return utf;
    } 
        
char *readstringUTF(FILE *f) {
    static char *utf = NULL;
    static uint32_t size = 0; 
    uint32_t  N = 0; 
    size_t err =fread(&N, sizeof(char), sizeof(uint16_t), f);
    if (err!=sizeof(uint16_t)) 
                 errormsg("readstring %d!=%d", err, sizeof(uint16_t));
    N = NtoHS((uint16_t) N);
    if (N>=size) {
        size = N+1<=utf_size?utf_size:N+1;
// printmsg("Readstring resize %d", size);
        utf=realloc(utf, size);
        if (!utf) 
             errormsg("readstring realloc size = %d", size);
        }
    err = fread(utf, sizeof(char), N, f);
    if (err!=N) errormsg("readstring %d!=%d", err, N);
    utf[err]='\0';
 // printmsg("readstring= %s N= %d err = %d size=%d", utf, N, err,size);
    return utf;
    }     

int printUTF(FILE *f, const char *format, ...) {
    va_list ap;
    char utf[utf_size];
    va_start(ap, format);
    {
    int N = vsnprintf(utf+sizeof(uint16_t), 
         utf_size-sizeof(uint16_t), format, ap);
    size_t size = sizeof(uint16_t)+N*sizeof(char);
    uint16_t m = HtoNS((uint16_t) N);
    memcpy(utf, &m, sizeof(uint16_t));
// fprintf(stderr,"printUTF d %d %s\n", N, size, utf+sizeof(uint16_t));
    return fwrite(utf, sizeof(char), size, f)==size?0:-1;
    }
    } 
       
int readintUTF(FILE *f, int *r) {
    char d[DSIZE]; int err;
    if ((err=readUTF(f, d, DSIZE))<0) return err;
    // fprintf(stderr, "QQ err = %d readint %s\n", err, d);
    if (sscanf(d,"%d", r)!=1) return -1;
    return err;
    }
    
int writeintUTF(FILE *f, int r) {
    char d[DSIZE];
    snprintf(d, DSIZE, "%d", r);
// fprintf(stderr,"writeintUTF %d\n", r);
    return printUTF(f, d, DSIZE);
    }

int readlongUTF(FILE *f, long *r) {
    char d[DSIZE]; int err;
    if ((err=readUTF(f, d, DSIZE))<0) return err;
// fprintf(stderr, "QQ err = %d readint %s\n", err, d);
    if (sscanf(d,"%ld", r)!=1) return -1;
    return err;
    }
    
int writelongUTF(FILE *f, long r) {
    char d[DSIZE];
    snprintf(d, DSIZE, "%ld", r);
// fprintf(stderr,"writeintUTF %d\n", r);
    return printUTF(f, d, DSIZE);
    }
    
    
int readPair(FILE *f, int32_t *elm) {
    return io.readPair(f, elm);
    }
    
int writePair(FILE *f, int32_t *elm) {
    return io.writePair(f, elm);
    }
    
int getRecordSize(void) {return io.record_size;}


file_t path(dir_t dir, char *mode, const char *format,...) {
      char name[1024];
      va_list ap;
      file_t file;
// printmsg("PATH");
      sprintf(name,"%s/", dir);
      if (format) {
         va_start(ap, format);
         vsprintf(name+strlen(name), format, ap);
         if (CreateEmptyDir(name, DELETE_NONE)<0) 
             errormsg("createmptydir none \"%s\"", name);
         strcat(name,"/file");
         if (!(file = fopen(name,mode))) {
                 errormsg("%s", name);
                 }
         rewind(file);
// fprintf(stderr,"Path %s %d\n", name, FileLen(file));
         return file;
         } 
      return NULL;
      }
#ifdef LINUX

static void ExtendBuffer(int sd, int val) {
        if (val<=0) return;
        if (setsockopt(sd, SOL_SOCKET, SO_SNDBUF, &val ,sizeof(int))<0)
                errormsg("Set Socket Option"); 
        if (setsockopt(sd, SOL_SOCKET, SO_RCVBUF, &val ,sizeof(int))<0)
                errormsg("Set Socket Option"); 
        }
        
static int unixConnect(int port, int contact) {
          struct sockaddr_un addr;
         int sd=socket(AF_UNIX,SOCK_STREAM,0), i, err;
         if(sd == -1) errormsg("No socket");
         // printmsg("UnixConnect %d %d", port, sd);
         memset(&addr, 0, sizeof(struct sockaddr_un));
         addr.sun_family = AF_UNIX;
         strncpy(addr.sun_path, socketFile(port), sizeof(addr.sun_path)-1);
         for (i=0;i<10;i++) {
         if ((err=connect(sd,(struct sockaddr*) &addr,sizeof(struct
         sockaddr_un)))>=0 || contact) break;
         sleep(1);
         }
         if (err<0) {
            close(sd);
            if (contact) return -1;
            errormsg("Connection failed on port %d", port);
            }
        // fprintf(stderr,"UnixConnected %d %d\n", port, sd);
        return sd;
        }
        
static int unixBind(int port) {
         struct sockaddr_un addr;
         int sd=socket(AF_UNIX,SOCK_STREAM,0);
         if(sd == -1) errormsg("No socket");
         // printmsg("UnixBind %d %d sizeof:%d\n", port, sd, sizeof(addr.sun_path));
         memset(&addr, 0, sizeof(struct sockaddr_un));
         addr.sun_family = AF_UNIX;
         strncpy(addr.sun_path, socketFile(port), sizeof(addr.sun_path)-1);
         unlink(addr.sun_path);
         if (bind(sd,(struct sockaddr*) &addr,sizeof(struct sockaddr_un))<0)
              errormsg("Binding failed on port %d", port);
         // fprintf(stderr,"UnixBinded %d %d\n", port, sd);
         if (listen(sd,4)==-1) {
                   errormsg("Bad Listen");
           }
        return sd;
        }
               
int clientSocket(char *hostname, int port, int bsize) {
        struct  hostent *hostinfo;
        int sd, err, cnt, val = 1, i;
        if (!socketdir) {
           struct sockaddr_in addr;
           hostinfo=gethostbyname(hostname);
           if(!hostinfo) hostinfo=gethostbyname("localhost");
           if(!hostinfo) errormsg(" error %s", hostname);
           memcpy(&addr.sin_addr,*(hostinfo->h_addr_list),
                (size_t) hostinfo->h_length);
           addr.sin_family = AF_INET;
           addr.sin_port = htons(port);
           sd=socket(AF_INET,SOCK_STREAM,0);
           if(sd == -1) errormsg("No socket");
           for (i=0;i<10;i++) {
           for (cnt=0;cnt<30 &&
                (err=connect(sd,(struct sockaddr*) &addr,sizeof(struct sockaddr))) 
                  == -1 && errno == ECONNREFUSED;cnt++) {
                sleep(1);
                }
           if (err>=0 || errno != ECONNREFUSED) break;
           sleep(30);
           if (i<9) printmsg("round %d host = %s port = %d", i+1, hostname, port);
           }
           if (err<0) errormsg("Connection failed (cnt=%d): host = %s port = %d", 
           cnt, hostname,  port);
           setsockopt(sd, PROTOCOL, TCP_NODELAY, &val ,sizeof(int));
           // ExtendBuffer(sd, bsize);
   //      printmsg("Client TCP_NODELAY %d", sd);
        } else return unixConnect(port, 0);
        return sd;
        }

int contactSocket(char *portname, int port, int cnt) {
        struct  hostent *hostinfo; 
            // if (!socketdir) {
            struct sockaddr_in addr;
            int sd = socket(AF_INET,SOCK_STREAM,0), err = -1, i;
            if (sd<0) errormsg("Cannot open socket to look for \"contact\"");
    // printmsg("ContactSocket: gethostbyname %s %d", portname, port);
            hostinfo=gethostbyname(portname);
            if(!hostinfo) hostinfo=gethostbyname("localhost");
            if(!hostinfo) errormsg("DNS error %s", portname);
            memcpy(&addr.sin_addr,*(hostinfo->h_addr_list),
            (size_t) hostinfo->h_length);
            addr.sin_family = AF_INET; addr.sin_port = htons((uint16_t) port);
            for (i=0;i<cnt && err== -1;i++) { 
            // printmsg("i=%d cnt=%d", i, cnt);
            if ((err=
                 connect(sd,(struct sockaddr*) &addr,sizeof(struct sockaddr)))==-1 
                 && errno != ECONNREFUSED) 
            errormsg("Connection failed host = %s port = %d", portname,  port);
            if (err<0) sleep(1);
            }
            if (err<0) {
                while (close(sd)!=0) {
                           printmsg("Cannot close");
                           sleep(1);
                           }
               // shutdown(sd, SHUT_RDWR);
               return -1;
               }
            return sd;
            // } else return unixConnect(port, 1); 
        }
        
 int serverSocket(int port, int bsize) {
        if (!socketdir) {
           struct sockaddr_in addr;
           int sd=socket(AF_INET,SOCK_STREAM,0), val=1;
   //      fprintf(stderr, "Open socked %d\n", port);
           if(sd == -1) errormsg("No socket");
           addr.sin_family = AF_INET;
           addr.sin_port = htons(port);
           addr.sin_addr.s_addr = INADDR_ANY;
           if (setsockopt(sd, PROTOCOL, TCP_NODELAY, &val ,sizeof(int))<0)
                   errormsg("Set Socket Option"); 
   //      printmsg("Server TCP_NODELAY %d", sd);
           setsockopt(sd, SOL_SOCKET, SO_REUSEADDR, &val ,sizeof(int));
           if (bind(sd,(struct sockaddr*) &addr,sizeof(struct sockaddr))==-1) {
              errormsg("Bad Bind: port = %d", port);       
              }
           if (listen(sd,4)==-1) {
                   errormsg("Bad Listen");
           }
           // ExtendBuffer(sd, bsize);
   //      errorreset();
           return sd;
        } else return unixBind(port);
        }
        
 int Accept(int sd) {
    // printmsg("Try to accept %d\n", sd);
    {
    int client = accept(sd,NULL,NULL), val = 1;
    if (client<0) errormsg("accept");
    // fprintf(stderr,"Accepted %d client = %d\n", sd, client);
    if (!socketdir) setsockopt(client, PROTOCOL, TCP_NODELAY, &val ,sizeof(int));
    return client;
    }
    }

int Fileno(FILE *f) {
    int r = fileno(f);
    if (r<0) errormsg("fileno error: %d", r);
    return r;
    }
     
#endif
