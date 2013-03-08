/* $Id: unix.c,v 1.25 2008/02/04 14:52:49 bertl Exp $ */
#ifdef __cplusplus
extern "C"
{
#endif/* __cplusplus */

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/times.h>
#include <netinet/in.h>
#include <errno.h>
#include <unistd.h>
#include <dirent.h>
#include <string.h>
#include <limits.h>
#include <regex.h>
#include <fcntl.h>
#undef FREAD
#undef FWRITE


#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#ifdef DEVELOPMENT
#include <sys/time.h>
#include <sys/resource.h>
#endif

/* printable comments
 *
 * defining CPRINTF(args...) printf(args)
 * will make them visible.
 */
/* #define CPRINTF(args...) printf(args)  */

#ifdef SGI
#define CPRINTF //
#else
#ifdef SUN
#define CPRINTF //
#else
#define CPRINTF(args...)
#endif
#endif

#ifdef USE_ZLIB
#include <zlib.h>
/* typedef gzFile GZfile; */ 
#else
/* typedef FILE*  GZfile; */
#endif
   
static int _CreateDir(const char *dir) {
    char *path = strdup(dir), *ptr , 
    *build = (char*) malloc(sizeof(char)*strlen(path)+1);
    int err;
    build[0]='\0';
    if (path[0]=='/') {
        strcat(build,"/");
        ptr = strtok(path+1, "/");
        }
    else
        ptr = strtok(path, "/");
    do {
      if (strlen(ptr)>0) {
        strcat(build,ptr);
        if ((err=mkdir(build, S_IRWXU|S_IRWXG|S_IRWXO))<0 && errno!=EEXIST)
            return err;          
/*
         mkdir(build, S_IRWXU|S_IRWXG|S_IRWXO);
*/	
        if (errno==EEXIST) errno = 0;
        }
      if ((ptr=strtok(NULL,"/"))) strcat(build,"/");
      } while (ptr);
    free(path); free(build);
    return 0;
    }
    
static int _RemoveDir(const char *name) {
    DIR *dir; struct dirent *file;
    char fname[NAME_MAX*2+2];
    int err;
    dir=opendir(name);
    if (dir==NULL) return -1;
    while((file=readdir(dir))){
       CPRINTF("entry %s\n",file->d_name);
       if(!strcmp(file->d_name,".")) continue;
       if(!strcmp(file->d_name,"..")) continue;
       sprintf(fname,"%s/%s",name,file->d_name);
       if (IsADir(fname)) {
           if ((err=_RemoveDir(fname))<0) return err;
           }
       else {
       if(unlink(fname)==-1) return -1;
       }
       }
    if ((err=rmdir(name))<0 && (err=unlink(name))<0) return err;
    return 0;
    } 
       
int CreateEmptyDir(const char *name,int _delete){
	struct stat info;
        errno = 0;
        if (!strcmp(name,".")||!strcmp(name, "..")) return -1;
        CPRINTF("CreateEmpty dir %s\n", name);
	if (stat(name,&info)==-1){
		switch(errno){
			default: 
				return -1;
			case ENOENT:
		         CPRINTF("%s does not exist creating now...\n",name);
			 return _CreateDir(name);
		}
	}
        if (!(_delete|DELETE_NONE)) return 0;
	if (S_ISREG(info.st_mode)){
	   CPRINTF("%s is a regular file\n",name);
           errno=EPERM;
	   return -1;        
	   }
	if (S_ISDIR(info.st_mode)){
	   DIR *dir;
	   struct dirent *file;
	   char fname[NAME_MAX*2+2];
	   CPRINTF("%s is a directory\n",name);
           CPRINTF("Help-1\n");
	   dir=opendir(name);
	   if (dir==NULL) return -1;
            CPRINTF("Help0\n");
	   while((file=readdir(dir))){
             CPRINTF("Help\n");
	     CPRINTF("entry %s\n",file->d_name);
	     if(!strcmp(file->d_name,".")) continue;
	     if(!strcmp(file->d_name,"..")) continue;
	     sprintf(fname,"%s/%s",name,file->d_name);
             if (IsADir(fname)) 
                {if ((_delete&DELETE_DIR) && 
                        _RemoveDir(fname)<0) return -1;}
             else 
		{if ((_delete&DELETE_FILE) && 
                        unlink(fname)==-1)  return -1;}
	   }
           closedir(dir);
	   return 0;
	}
	CPRINTF("%s is unknown type\n",name);
	errno=EINVAL;
	return -1;
        }

int IsADir(const char *name){
   struct stat info;
   return ((stat(name,&info)==0)&&(S_ISDIR(info.st_mode)))?1:0;
   }

int IsAReg(const char *name){
   struct stat info;
   return ((stat(name,&info)==0)&&(S_ISREG(info.st_mode)))?1:0;
   }
   
static int cmpstringp(const void *p1, const void *p2)
       {
           /* The actual arguments to this function are "pointers to
              pointers to char", but strcmp() arguments are "pointers
              to char", hence the following cast plus dereference */

           return strcmp(* (char * const *) p1, * (char * const *) p2);
       }

static int ForEachFile(const char *path, EachFile eachFile, int directory) {
   struct dirent *file;
   char fname[NAME_MAX*2+2];
   int cnt = 0, i =0;
   char **ptr;
   DIR *dir=opendir(path);
   if (dir==NULL) return -1;
   while((file=readdir(dir))){
      CPRINTF("entry %s\n",file->d_name);
      if(!strcmp(file->d_name,".")) continue;
      if(!strcmp(file->d_name,"..")) continue;
      sprintf(fname,"%s/%s",path ,file->d_name);
      if (directory?IsADir(fname):IsAReg(fname)) cnt++;
      }
   if (eachFile) {
      ptr = malloc(sizeof(char*)*cnt);
      rewinddir(dir);
      while (file=readdir(dir)) {
         CPRINTF("entry %s\n",file->d_name);
         if(!strcmp(file->d_name,".")) continue;
         if(!strcmp(file->d_name,"..")) continue;
         sprintf(fname,"%s/%s",path ,file->d_name);
         if (directory?IsADir(fname):IsAReg(fname)) {     
           ptr[i++]=strdup(fname);
           }
         }
      qsort(ptr, cnt, sizeof(char*), cmpstringp);
         for (i=0;i<cnt;i++) {
           int err= eachFile(ptr[i]);
           free(ptr[i]);
           if (err<0) return err;
           }
      free(ptr);
   }
   closedir(dir);
   return cnt;
   }
   
int ForEachFileInDir(const char *path, EachFile eachFile) {
  return ForEachFile(path, eachFile, 0);
  }
  
int ForEachDirInDir(const char *path, EachFile eachDir) {
  return ForEachFile(path, eachDir, 1);
  }
    
int ReadOnly(FILE *f) {
   return f==NULL || ((fcntl(fileno(f),F_GETFL)&O_ACCMODE)==O_RDONLY);
   }

int WriteOnly(FILE *f) {
   return f==NULL || (fcntl(fileno(f),F_GETFL)&O_WRONLY);
   }
      
FILE *Popen(const char *command, const char *type) {
   return popen(command, type);
   }
   
int Pclose(FILE *stream) {
   return pclose(stream);
   }

FILE *Redirect(const char *command, const char *type, FILE *stream) {
   FILE *client = Popen(command,  type);
   if (!client) return (FILE*) NULL;
   if (dup2(fileno(client),fileno(stream))<0) return (FILE*) NULL;
   return client;
   }

int Truncate(const char *file, long size) {
   return truncate(file, size); 
   }
   
int Ftruncate(FILE *file, long size) {
   return ftruncate(fileno(file), size); 
   }

/* Computing time evaluation */
struct timer {
	clock_t	real_time;
	struct tms times;
	int running;
};

mytimer_t createTimer(){
	mytimer_t timer;
	timer=(mytimer_t)malloc(sizeof(struct timer));
	if (timer){
		timer->real_time=0;
		timer->times.tms_utime=0;
		timer->times.tms_stime=0;
		timer->times.tms_cutime=0;
		timer->times.tms_cstime=0;
		timer->running=0;
	}
	return timer;
}

void deleteTimer(mytimer_t timer){
	free(timer);
}

void resetTimer(mytimer_t timer){
	if (timer->running) {
		timer->real_time=times(&(timer->times));
	} else {
		timer->real_time=0;
		timer->times.tms_utime=0;
		timer->times.tms_stime=0;
		timer->times.tms_cutime=0;
		timer->times.tms_cstime=0;
	}
}

void startTimer(mytimer_t timer){
	if (!(timer->running)) {
		struct tms tmp;
		clock_t real_time;
		real_time=times(&tmp);
		timer->real_time-=real_time;
		timer->times.tms_utime-=tmp.tms_utime;
		timer->times.tms_stime-=tmp.tms_stime;
		timer->times.tms_cutime-=tmp.tms_cutime;
		timer->times.tms_cstime-=tmp.tms_cstime;
		timer->running=1;
	}
}

void stopTimer(mytimer_t timer){
	if (timer->running) {
		struct tms tmp;
		clock_t real_time;
		real_time=times(&tmp);
		timer->real_time+=real_time;
		timer->times.tms_utime+=tmp.tms_utime;
		timer->times.tms_stime+=tmp.tms_stime;
		timer->times.tms_cutime+=tmp.tms_cutime;
		timer->times.tms_cstime+=tmp.tms_cstime;
		timer->running=0;
	}
}


void reportTimer(mytimer_t timer,char *msg){
	clock_t tick=sysconf(_SC_CLK_TCK);
	float tm_real=((float)(timer->real_time))/((float)tick);
	float tm_user=((float)(timer->times.tms_utime))/((float)tick);
	float tm_sys=((float)(timer->times.tms_stime))/((float)tick);
	fprintf(stderr,"%s %5.3f real %5.3f user %5.3f sys",msg,tm_real,
        tm_user,tm_sys);
}

float timerUser(mytimer_t timer) {
   clock_t tick=sysconf(_SC_CLK_TCK);
   float tm_user=((float)(timer->times.tms_utime))/((float)tick);
   /* fprintf(stderr,"%9.3f ", tm_user); */
   return tm_user;
   }
                                                                                
float timerReal(mytimer_t timer) {
   clock_t tick=sysconf(_SC_CLK_TCK);
   float tm_real=((float)(timer->real_time))/((float)tick);
   /* fprintf(stderr,"%9.3f ", tm_real); */
   return tm_real; 
   }

float timerSys(mytimer_t timer) {
   clock_t tick=sysconf(_SC_CLK_TCK);
   float tm_sys=((float)(timer->times.tms_stime))/((float)tick);
   /* fprintf(stderr,"%9.3f", tm_sys); */
   return tm_sys;
   }

#ifdef DEVELOPMENT  
int GetTimeOfDay(void) {
   struct timeval  tv[1];
   gettimeofday(tv, NULL);
   return (int) (tv->tv_sec);
   }
#endif
     
uint16_t HtoNS(uint16_t hostshort) {
       return htons(hostshort);
       }
       
uint16_t NtoHS(uint16_t netshort) {
       return ntohs(netshort);
       }

uint32_t HtoNL(uint32_t hostlong) {
       return htonl(hostlong);
       }
       
uint32_t NtoHL(uint32_t netlong) {
       return ntohl(netlong);
       }
       
int RemoveDir(const char *pathname) {
       return rmdir(pathname); 
       }

int RemoveFile(const char *pathname) {
       return unlink(pathname);
       }
             
int CreateDir(const char *pathname) {
       return mkdir(pathname, S_IRWXU|S_IRWXG|S_IRWXO);
       }

int FileLen(FILE *f) {
     struct stat info;
     fstat(fileno(f),&info);
     /* return info.st_size; */
     return S_ISREG(info.st_mode)?info.st_size:-1; 
     }

char *GetCwd(char *name, int n) {
     return getcwd(name, n);
     }

int ExecVp(const char *path, char *const argv[]) {
     return execvp(path, argv);
     }
     
FILE *TempFile(char *fname, int len) {
    char *tmpdir = getenv("TMPDIR");
    int d; FILE *r;
    if (!tmpdir) tmpdir ="/var/tmp";
    snprintf(fname, len, "%s/%s",tmpdir,"mcrlXXXXXX");
    if ((d = mkstemp(fname))<0) r = NULL;
    else r = fdopen(d, "w");
    if (r==NULL) fname[0]='\0';
    return r;
    }

int Pr(const char *format, ...) {
    int r;
    va_list ap;
    va_start(ap, format);
    r = vfprintf(stdout, format, ap);
    fprintf(stdout,"\n");
    va_end(ap);
    return r+1;
    }
            
#if defined HAVE_STRDUP && !HAVE_STRDUP
char *strdup(const char *s)
{
    size_t len;
    char *p;

    len = strlen(s);
    if((p = (char *)malloc(len + 1)) == NULL)
	return NULL;
    return strcpy(p, s);
}
#endif /* HAVE_STRDUP */

preg_t RegCompile(const char *regex) {
    int cflags = 0, err = 0;
    regex_t *preg = (regex_t*) malloc(sizeof(regex_t));
    cflags |= REG_NOSUB;
    cflags |= REG_EXTENDED;
    // fprintf(stderr,"RegCompile: %s %d\n", regex, cflags);
    if ((err=regcomp(preg, regex, cflags))!=0) {
        char buf[256];
        regerror(err, preg, buf, 256);
        fprintf(stderr, "%s\n", buf);
        return NULL;
        }
    return (preg_t) preg;
    }

int RegMatch(preg_t preg, const char *s) {
    return regexec((regex_t*) preg, s, 0, NULL, 0)==0?1:0;
    } 

typedef struct {
   int zopen;
   void *f;
   } zfile;
   
GZfile GZopen(const char *path, const char *mode) {
    zfile *r = (zfile*) malloc(sizeof(zfile));
#ifdef USE_ZLIB
    r->zopen = 1;
    if (strlen(mode)<=2 && (!strncmp(mode,"a", 1) || !strncmp(mode,"w", 1))) {
       r->f = (GZfile) gzopen(path, "wb9");
       }
    else
    if (strlen(mode)<=2 && !strncmp(mode,"r", 1)) 
                              r->f = (GZfile) gzopen(path, "rb");
    else
    if (strcmp(mode,"wb0")) r->f = (GZfile) gzopen(path, mode);
    else
#endif
    {r->zopen = 0;r->f = (FILE*) fopen(path, mode);}
// fprintf(stderr,"GZopen %d", r->zopen);
    return (GZfile) r;
    }

GZfile GZdopen(int fd, const char *mode) {
     zfile *r = (zfile*) malloc(sizeof(zfile));
#ifdef USE_ZLIB
    r->zopen = 1;
    if (strlen(mode)<=2 && (!strncmp(mode,"a", 1) || !strncmp(mode,"w", 1))) {
       r->f = (GZfile) gzdopen(fd, "wb9");
       }
    else
    if (strlen(mode)<=2 && !strncmp(mode,"r", 1)) 
                              r->f = (GZfile) gzdopen(fd, "rb");
    else
    if (strcmp(mode,"wb0")) r->f = (GZfile) gzdopen(fd, mode);
    else
#endif
    {r->zopen = 0;r->f = (FILE*) fdopen(fd, mode);}
// fprintf(stderr,"GZdopen %d\n", r->zopen);
    return (GZfile) r;
    }

int GZclose (GZfile file) { 
    zfile *r = (zfile*) file;
    int d;  
#ifdef USE_ZLIB
    if (r->zopen) d = gzclose((gzFile)(r->f));
    else
#endif
    d = fclose((FILE*)(r->f));
    free(r);
    return d;
    }

int GZflush (GZfile file) {
    zfile *r = (zfile*) file;  
#ifdef USE_ZLIB
    if (r->zopen)
    return gzflush((gzFile) (r->f), Z_FULL_FLUSH);
#endif
    return fflush((FILE*) (r->f));
}

int GZeof (GZfile file) {
    zfile *r = (zfile*) file;
#ifdef USE_ZLIB
    if (r->zopen)
    return gzeof ((gzFile) (r->f));
#endif
    return feof((FILE*) (r->f));
}
 
char *GZgets (GZfile file, char *buf, int len) {
    zfile *r = (zfile*) file;
#ifdef USE_ZLIB
    if (r->zopen)
    return gzgets((gzFile) (r->f), buf, len);
#endif
    return fgets( buf, len, (FILE*) (r->f));
}

int GZgetc (GZfile file) {
    zfile *r = (zfile*) file;
#ifdef USE_ZLIB
    if (r->zopen)
    return gzgetc((gzFile) (r->f));
#endif
    return fgetc((FILE*) (r->f));
}

int GZputs (GZfile file, const char *buf) {
    zfile *r = (zfile*) file;
#ifdef USE_ZLIB
    if (r->zopen)
    return gzputs((gzFile) (r->f), buf);
#endif
    return fputs(buf, (FILE*) (r->f));
} 

int GZputc (GZfile file, int c) {
    zfile *r = (zfile*) file;
#ifdef USE_ZLIB
    if (r->zopen)
    return gzputc((gzFile) (r->f), c);
#endif
    return fputc(c, (FILE*) (r->f));
}
 
int GZread (GZfile file, void *buf, unsigned len) {
zfile *r = (zfile*) file;
#ifdef USE_ZLIB
// fprintf(stderr,"GZread %d\n", r->zopen);
if (r->zopen)
   return gzread((gzFile) (r->f), buf, len);
#endif
   return (int) fread(buf, 1, (size_t) len, (FILE*) (r->f));
   }

int GZwrite (GZfile file, void *buf, unsigned len) {
    zfile *r = (zfile*) file;
#ifdef USE_ZLIB
if (r->zopen)
   return gzwrite((gzFile) (r->f), buf, len);
#endif
   return (int) fwrite(buf, 1, (size_t) len, (FILE*) (r->f));
   }

int GZprintf (GZfile file, const char *format, ...) {
   char buf[80092];
   va_list ap;
   va_start(ap, format);
   vsnprintf(buf, 80092, format, ap); 
   return GZputs(file, buf);
   }

#ifdef LINUX
int GZscanf (GZfile file, const char *format, ...) {
   int r;
   char buf[80092];
   va_list ap;
   va_start(ap, format);
   GZgets(file, buf, 80092);
   r=vsscanf(buf, format, ap);
   return r;
   }
#endif
       
int GZrewind (GZfile file) {
   zfile *r = (zfile*) file;
#ifdef USE_ZLIB
   if (r->zopen)
      gzrewind((gzFile) (r->f));
   else
#endif
    rewind((FILE*) (r->f));
    return 0;
} 


int  GZlen(GZfile file) {
zfile *r = (zfile*) file;
#ifdef USE_ZLIB
#define GZLEN 8096
if (r->zopen) {
    char buf[GZLEN];
    int len = 0, d;
    gzrewind((gzFile) (r->f));
    while ((d=gzread((gzFile) (r->f),  buf, GZLEN))>0) len += d;
    gzrewind((gzFile) (r->f));
    return len;
    }
#undef GZLEN
#endif
    return FileLen((FILE*) (r->f));
   } 

/* Buffer package */

#define BLOCKLEN 8096

bfile_t *bopen_memstream(size_t initLength, char **ptr, size_t *sizeloc) {
   bfile_t* b = calloc(1, sizeof(bfile_t));
   b->rptr = ptr; b->rsizeloc = sizeloc; 
   b->size = (initLength==0?BLOCKLEN:initLength);
   b->ptr = (char*) malloc(b->size);
   return b->ptr?b:NULL;  
   }

size_t blength(bfile_t *f) {return f->size;}

void bfputc(char c, bfile_t *f) {
   for (;f->sizeloc+1>=f->size;f->size*=2);
   if (!(f->ptr = (char*) realloc(f->ptr, f->size))) return;
   f->ptr[f->sizeloc++] = c;  
   } 
 
size_t bfwrite(void *ptr, size_t size, size_t nmemb, bfile_t *f) {
   size_t n = size*nmemb;
   for (;f->sizeloc+n>=f->size;f->size*=2);
      /* fprintf(stderr, "Realloc %d %d %d>=%d\n",
      size, nmemb, f->sizeloc+n, f->size); */
   if (!(f->ptr = (char*) realloc(f->ptr, f->size)))
         return 0;
   memcpy(f->ptr+f->sizeloc, ptr, n);
   f->sizeloc+=n;
   return nmemb;
   }

int bfflush(bfile_t *f) {
   *(f->rptr) = f->ptr;
   *(f->rsizeloc) = f->sizeloc; 
   return 0;
   }
   
int bfclose(bfile_t *f) {
   *(f->rptr) = f->ptr;
   *(f->rsizeloc) = f->sizeloc; 
   f->ptr = NULL;
   return 0;
   } 

void brewind(bfile_t *f) {
   f->sizeloc = 0;
   *(f->rsizeloc) = f->sizeloc; 
   }
                
#ifdef DEVELOPMENT  
MCRLUSAGE *Rusage(void) {
    struct rusage r;
    int err = getrusage(RUSAGE_SELF, &r);
    static MCRLUSAGE *MCRLusage = NULL;
    if (err<0) return NULL;
    if (!MCRLusage) MCRLusage = malloc(sizeof(MCRLUSAGE));
    MCRLusage->utime = r.ru_utime.tv_sec+(r.ru_utime.tv_usec)/1000;
    MCRLusage->stime = r.ru_stime.tv_sec+(r.ru_stime.tv_usec)/1000;
    MCRLusage->ixrss = r.ru_ixrss; /* integral shared memory size */
    MCRLusage->idrss = r.ru_idrss; /* integral unshared data size */
    MCRLusage->isrss = r.ru_isrss; /* integral unshared stack size */
    MCRLusage->nvcsw = r.ru_nvcsw; /* voluntary context switches */
    MCRLusage->nivcsw = r.ru_nivcsw; /* involuntary context switches */
    return MCRLusage;
    }    
#endif
#ifdef __cplusplus
}
#endif/* __cplusplus */
