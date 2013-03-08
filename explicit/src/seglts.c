/* $Id: seglts.c,v 1.8 2007/06/29 13:30:57 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "seglts.h"
#include "data_io.h"
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stdio.h>
#include "param0.h"
#include "utl.h"
#include "stringindex.h"

static char *sandpitdir = "/wslocal/<host>/<user>/<basename>/STEPPERS",
            *homedir = "/<dirname>/<basename>/STEPPERS";
static char **dest;
static char buf[FNAMESIZE], datadir[FNAMESIZE], *basename, *dirname;
	    
static char errormessage[1024]="Programming error in seglts: success or forgot to write error message";

char *SLTSerror(){
	return errormessage;
}

static pathar_t  *altar, *homear;

int SLTSCreateInfo(seginfo_t *info,int segment_count){
	int i,j;

	(*info)=(seginfo_t)malloc(sizeof(struct seginfo));
	if ((*info)==NULL) {
		sprintf(errormessage,"out of memory");
		return 1;
	}
	(*info)->info=NULL;
	(*info)->segment_count=segment_count;
	(*info)->initial_seg=0;
	(*info)->initial_ofs=0;
	(*info)->label_count=0;
	(*info)->label_tau=0;
	(*info)->top_count=0;
	(*info)->state_count=(int*)malloc(segment_count*sizeof(int));
	(*info)->transition_count=(int**)malloc(segment_count*sizeof(int*));
	for(i=0;i<segment_count;i++) {
		(*info)->state_count[i]=0;
		(*info)->transition_count[i]=(int*)malloc(segment_count*sizeof(int));
		for(j=0;j<segment_count;j++) {
			(*info)->transition_count[i][j]=0;
		}
	}
	return 0;
}


static int create_info_v31(seginfo_t *info,FILE *f) {
	char *info_string;
	int len;
	int segment_count;
	int i,j;

	fread16(f,&len);
	info_string=(char*)malloc(len+1);
	freadN(f,info_string,len);
	info_string[len]=0;
	fread32(f,&segment_count);
	SLTSCreateInfo(info,segment_count);
	(*info)->info=info_string;
	fread32(f,&((*info)->initial_seg));
	fread32(f,&((*info)->initial_ofs));
	fread32(f,&((*info)->label_count));
	fread32(f,&((*info)->label_tau));
	fread32(f,&((*info)->top_count));
	for(i=0;i<segment_count;i++){
		fread32(f,((*info)->state_count)+i);
	}
	for(i=0;i<segment_count;i++){
		for(j=0;j<segment_count;j++){
			fread32(f,&((*info)->transition_count[i][j]));
		}
	}
	return 0;
}


int SLTSReadInfo(seginfo_t *info,char *name){
	char filename[1024];
	FILE* f;
	int version;

	sprintf(filename,"%s/info",name);
	f=fopen(filename,"r");
	fread32(f,&version);
	switch(version){
		default:
			sprintf(errormessage,"unknown version %d",version);
			fclose(f);
			return 1;
		case 31:
			if(create_info_v31(info,f)) {
				fclose(f);
				return 1;
			}
			break;
	}
	return 0;
}

void SLTSPrintInfo(seginfo_t info, FILE *f) {
        int i, j;
        long sum; 
        fprintf(f,"VERSION 31\n");
        fprintf(f,"info->info: %s\n", info->info);
        fprintf(f,"info->segment_count: %d\n", info->segment_count);
	fprintf(f,"info->initial_seg: %d\n", info->initial_seg);
	fprintf(f,"info->initial_ofs: %d\n", info->initial_ofs);
	fprintf(f,"info->label_count: %d\n", info->label_count);
	fprintf(f,"info->label_tau: %d\n", info->label_tau);
	fprintf(f,"info->top_count: %d\n", info->top_count);
        fprintf(f,"Nr states:");
	for(sum=0, i=0;i<info->segment_count;sum+=info->state_count[i++]){
		fprintf(f,"%10d", info->state_count[i]);
	}; 
        fprintf(f,"\n");
        fprintf(f,"Total number of states: %ld\n", sum);
        fprintf(f,"Number of transitions:\n");
	for(sum=0, i=0;i<info->segment_count;i++){
           fprintf(f,"client%3d:", i);
           for(j=0;j<info->segment_count;sum+=info->transition_count[i][j++]){
             fprintf(f,"%10d", info->transition_count[i][j]);
           }
           fprintf(f,"\n");
        }
        fprintf(f,"Total number of transitions: %ld\n", sum);
    }
    
int SLTSWriteInfo(seginfo_t info,char *name){
	int i,j,len;
	char info_name[1024];
	FILE *f;
	sprintf(info_name,"%s/info",name);
	if (!(f=fopen(info_name,"w"))) {
           perror(info_name); return -1;
           };
	fwrite32(f,31);
	if (info->info==NULL){
		fwrite16(f,0);
	} else {
		len=strlen(info->info);
		fwrite16(f,len);
		fwriteN(f,info->info,len);
	}
	fwrite32(f,info->segment_count);
	fwrite32(f,info->initial_seg);
	fwrite32(f,info->initial_ofs);
	fwrite32(f,info->label_count);
	fwrite32(f,info->label_tau);
	fwrite32(f,info->top_count);
	for(i=0;i<info->segment_count;i++){
		fwrite32(f,info->state_count[i]);
	}
	for(i=0;i<info->segment_count;i++){
		for(j=0;j<info->segment_count;j++){
			fwrite32(f,info->transition_count[i][j]);
		}
	}
	fclose(f);
	return 0;
}

dir_client_t SLTSCreateClient(int n, char *name, int idx) {
       int i;
       char filename[1024];
       dir_client_t r = (dir_client_t) calloc(sizeof(struct dir_client), 1);
       r->n = n;
       r->src=(char**) malloc(n*sizeof(char*));
       r->lbl=(char**) malloc(n*sizeof(char*));
       r->dst=(char**) malloc(n*sizeof(char*));
       r->srcf=(FILE**) malloc(n*sizeof(char*));
       r->lblf=(FILE**) malloc(n*sizeof(char*));
       r->dstf=(FILE**) malloc(n*sizeof(char*));
       for (i=0;i<n;i++) {
          sprintf(filename,"%s/src-%d-%d",name, idx, i);
          r->src[i] = strdup(filename);
          if (!(r->srcf[i]=fopen(r->src[i], "a"))) {
              perror(r->src[i]); exit(1);
              }
          sprintf(filename,"%s/label-%d-%d",name,i, idx);
	  r->lbl[i] = strdup(filename);
          if (!(r->lblf[i]=fopen(r->lbl[i], "a"))) {
              perror(r->lbl[i]); exit(1);
              }
	  sprintf(filename,"%s/dest-%d-%d",name,  i, idx);
          r->dst[i] = strdup(filename);
          if (!(r->dstf[i]=fopen(r->dst[i], "a"))) {
              perror(r->dst[i]); exit(1);
              }
          }
       return r;
       }
       
FILE *SLTSopen(dir_client_t r, int pos, SLTSkind_t kind) {
       switch (kind) {
           case SLTSsrc: return fopen(r->src[pos], "a");
           case SLTSlbl: return fopen(r->lbl[pos], "a");
           case SLTSdst: return fopen(r->dst[pos], "a");
           }
       return NULL;
       }
                                 
dir_server_t SLTSCreateServer(seginfo_t info, char *name) {
       char filename[1024];
       dir_server_t r = (dir_server_t) calloc(sizeof(struct dir_server), 1);
       if (SLTSWriteInfo(info, name)<0) return NULL;
       r->n = info->segment_count;
       sprintf(filename,"%s/TermDB",name);
       if (!(r->TermDB=fopen(filename,"w"))) {
           perror(filename); return NULL;
           };
       return r;
       }      
  
static pathar_t  *MCRL_PRIVATE(char *path) {
   char *s = strdup(path+1), *t = s;
   int i;
   pathar_t *pathar = (pathar_t*) calloc(1, sizeof(pathar_t));
   for (pathar->n=0, s=strtok(s,"/");s;s=strtok(NULL,"/"),(pathar->n)++);
   pathar->p = (char**) malloc((pathar->n)*sizeof(char*));
   for (i=0;i<pathar->n;i++,t+=(strlen(t)+1)) (pathar->p)[i]=t;
   return pathar;
   }

static void EVAL_PRIVATE(pathar_t ar, char *host, char *user, 
   char *dirname, char *basename,  char *path) {
   int i;
   path[0]='\0';
   for (i=0;i<ar.n;i++) {
       strcat(path,"/");
       if (host && !strcmp(ar.p[i],"<host>")) {strcat(path, host);continue;}
       if (user && !strcmp(ar.p[i],"<user>")) {strcat(path, user);continue;}
       if (dirname && !strcmp(ar.p[i],"<dirname>")) {strcat(path, dirname+1);continue;}
       if (basename && !strcmp(ar.p[i],"<basename>")) {strcat(path, basename);continue;}
       strcat(path, ar.p[i]);
       }
   }  
     
void patharInit(char *absname) {
   basename = strdup(strrchr(absname,'/')+1);
   dirname = strdup(absname);
   *strrchr(dirname,'/')='\0';
   homear = MCRL_PRIVATE(homedir);
   altar = MCRL_PRIVATE(getenv("MCRL_PRIVATE")?getenv("MCRL_PRIVATE"):sandpitdir); 
   EVAL_PRIVATE(*homear, NULL, NULL, dirname, basename, datadir);
   }  
          
char *EnvironmentDest(int nhosts, int nsegments, int nskip) {
     int i, len = 0; char *r, *lhs = "MCRL_DEST=";
     for (i=nskip;i<nhosts;i++) len+=strlen(dest[i]);
     r =(char*) malloc((len+strlen(lhs)+nsegments+1)*sizeof(char));
     strcpy(r, lhs);
     for (i=nskip;i<nhosts;i++) {
        if (i>nskip) strcat(r," ");
	strcat(r, dest[i]);
        }
// fprintf(stderr,"Environmentdest %s\n", r);
     return r;
     }

int guess_nsegments() {
  return ForEachDirInDir(datadir, NULL);
  }

int guess_nhosts(int *local) {
   char *home = getenv("HOME"), *pbs = 
   getenv("PBS_NODEFILE"), fname[FNAMESIZE], host[FNAMESIZE], *pt;
   FILE *f;
   int cnt =0;
   if (pbs) strcpy(fname, pbs); else 
       sprintf(fname,"%s/%s", home, "hosts");
   if (!(f=fopen(fname,"r"))) {
         printmsg("File %s not found  (-local is added)", fname);
         *local=1;
         putenv("LOCAL=-local");
         return 0;
         }
   while ((pt=fgets(host, FNAMESIZE, f))) cnt++;
   fclose(f);
   return cnt;
   }
   
void CreateRestoreJob(char *outputfile, int nhosts, int argc, char **argv) {
    FILE *f;
    int i, idx, *frek, n;
    string_index_t si;
    SIcreate(&si);
    frek = (int*) calloc(nhosts, sizeof(int));
    for (i=0;i<nhosts;i++) {
    SIput(si,strrchr(dest[i],'/')?
             strrchr(dest[i],'/')+1:dest[i],&idx);
    frek[idx]++;
    }
    sprintf(buf,"%s.sh", strrchr(outputfile,'/')?
         (strrchr(outputfile,'/')+1):outputfile);
    if (!(f= fopen(buf, "w"))) errormsg("Cannot open %s", buf); 
    fprintf(f,"#PBS -l nodes="); 
    n = SIgetCount(si);
    for (i=0;i<n;i++) {
       char *host = SIget(si, i);
       if (i>0) fprintf(f,"+");
       fprintf(f, "%s:ppn=%d", host , frek[i]); 
       }
    fprintf(f, ",walltime=12:00:00,cput=12:00:00\n");
    fprintf(f,"#PBS -N instantiators\n");
    fprintf(f,"instantiators -restore ");
    for (i=1;i<argc-1;i++) fprintf(f, "%s ",argv[i]);
    fprintf(f, "%s 1>1 2>2\n",argv[i]);
    fclose(f);
    } 
        
int ForEachDirInHost(int nhosts, int nsegments, int local, int nskip, 
int private, int restore, int output, char *path, EachFile eachFile) {
   int cnt = 0, i = 0; 
   char *user = getenv("USER"),
   host[FNAMESIZE]; 
   dest = (char**) malloc((local?nsegments:nhosts)*sizeof(char*)); 
   if (!local) {
   char *home = getenv("HOME"), *pbs = 
   getenv("PBS_NODEFILE"), fname[FNAMESIZE], *pt;
   FILE *f;
   if (pbs) strcpy(fname, pbs); else 
       sprintf(fname,"%s/%s", home, "hosts");
   if (!(f=fopen(fname,"r"))) return 0;
   for (i=0;cnt<nsegments && (pt=fgets(host, FNAMESIZE, f));i++) {
       if (pt[strlen(pt)-1]=='\n') pt[strlen(pt)-1]='\0';
       if (i<nskip) {
       dest[i] = strdup(host);
          } else {
              EVAL_PRIVATE(private?*altar:*homear, host, user, dirname, basename,  path);
	      sprintf(path+strlen(path), "/stepper.%d",   cnt);
              // printmsg("ForEachHost %s", path);
              if (restore) {if (eachFile) eachFile(path);}
              else if (output) {
                 if (CreateEmptyDir(path, DELETE_ALL)!=0) 
                      errormsg("At Creating empty directory %s", path);
                 }
	      sprintf(path+strlen(path),"/%s", host);
	      dest[i]=strdup(path);
	      // printmsg("%s", dest[i]);
              if (private && !restore) {
                  char oldpath[FNAMESIZE];
                  strcpy(oldpath, dest[i]);
                  *strrchr(oldpath,'/')='\0';
                  EVAL_PRIVATE(*homear, host, user, dirname, basename,  path);
                  if (output) {
                  if (CreateEmptyDir(path, DELETE_NONE)!=0) 
                      errormsg("At Creating directory %s", path);
                    }
                  sprintf(path+strlen(path), "/stepper.%d",   cnt);
                  symlink(oldpath, path);
                  }
              cnt++;
              }
        }
      if (cnt<nsegments)  {
        printmsg(
      "Too few lines in host file: nhosts = %d<%d = nsegments  (skip = %d)",
      cnt, nsegments, nskip);
         return -2; 
         }
      }
      else {
      gethostname(host,FNAMESIZE);
      // strcpy(host,"localhost");
      for (cnt=0;cnt<nsegments;cnt++) {
          EVAL_PRIVATE(private?*altar:*homear, host, user, dirname, basename,  path);
	  sprintf(path+strlen(path), "/stepper.%d",   cnt);
          /* printmsg("ForEachHost %s", path); */
	  if (restore) eachFile(path);
	  else 
              {if (CreateEmptyDir(path, DELETE_ALL)!=0)
                 errormsg("At Creating empty directory %s", path);}
	  sprintf(path+strlen(path),"/%s", host);
	  dest[cnt]=strdup(path);
          if (private && !restore) {
              char oldpath[FNAMESIZE];
              strcpy(oldpath, dest[cnt]);
              *strrchr(oldpath,'/')='\0';
              EVAL_PRIVATE(*homear, host, user, dirname, basename,  path);
              if (CreateEmptyDir(path, DELETE_NONE)!=0)
                      errormsg("At Creating directory %s", path);
                  sprintf(path+strlen(path), "/stepper.%d",   cnt);
              symlink(oldpath, path);
              }
	  /* printmsg("%s", dest[cnt]); */
          }  
      }
    return cnt; 
   }

