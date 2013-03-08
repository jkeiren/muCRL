/* $Id: stringdbs.c,v 1.1 2004/01/29 13:17:32 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "stringdbs.h"
#include "generichash.h"

#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#define DATA_BLOCK_SIZE 512
#define TABLE_INITIAL 0xfff
#define FULL_MAX 7
#define FULL_OUTOF 8

struct stringdbs {
	FILE *f;
	int count;
	int size;
	char **data;
	int *table;
	int mask;
};

static char errormessage[1024]="Programming error in stringdbs: success or forgot to write error message";

static int create_record(stringdbs_t *dbs){
	int i;

	*dbs=(stringdbs_t)malloc(sizeof(struct stringdbs));
	if ((*dbs)==NULL) {
		sprintf(errormessage,"not enough memory for struct stringdbs");
		return 1;
	}
	(*dbs)->count=0;
	(*dbs)->size=DATA_BLOCK_SIZE;
	(*dbs)->data=(char**)malloc(DATA_BLOCK_SIZE*sizeof(char*));
	if ((*dbs)->data==NULL) {
		sprintf(errormessage,"not enough memory for data");
		free(*dbs);
		return 1;
	}
	(*dbs)->table=(int*)malloc((TABLE_INITIAL+1)*sizeof(int));
	if ((*dbs)->table==NULL) {
		sprintf(errormessage,"not enough memory for table");
		free((*dbs)->data);
		free(*dbs);
		return 1;
	}
	(*dbs)->mask=TABLE_INITIAL;
	for(i=0;i<=(*dbs)->mask;i++) (*dbs)->table[i]=SD_INDEX_FAILED;
	return 0;}

static void delete_record(stringdbs_t dbs){
	free(dbs->data);
	free(dbs->table);
	free(dbs);
}

int SDcreate(stringdbs_t *dbs,char *filename,int format){
	if (format==SD_AUTO) format=SD_PLAIN;
	if (format!=SD_PLAIN) {
		sprintf(errormessage,"unsupported file format");
		return 1;
	} 
	if (create_record(dbs)){
		return 1;
	}
	if (filename==NULL){
		(*dbs)->f=NULL;
	} else {
		(*dbs)->f=fopen(filename,"w");
		if (((*dbs)->f)==NULL) {
			sprintf(errormessage,"open failed: %s",strerror(errno));
			delete_record(*dbs);
			return 1;
		}
	}
	return 0;
}

extern int SDclone(stringdbs_t *newdbs,char *filename,int format,stringdbs_t olddbs){
	int i;

	if (SDcreate(newdbs,filename,format)) return 1;
	for(i=0;i<SDcount(olddbs);i++){
		if (SDindex(*newdbs,SDstring(olddbs,i))!=i){
			SDclose(*newdbs);
			sprintf(errormessage,"cloning failed");
			return 1;
		}
	}
	return 0;
}


int SDopen(stringdbs_t *dbs,char *filename,int format,int readonly){
	FILE *f;
	char buffer[4096];
	int len,count;

	if (SDcreate(dbs,NULL,format)) return 1;
	f=fopen(filename,"r");
	if (f==NULL){
		SDclose(*dbs);
		sprintf(errormessage,"open for read failed: %s",strerror(errno));
		return 1;
	}
	count=0;
	while(!feof(f)){
		if (fgets(buffer,4096,f)==NULL) {
			if (feof(f)) {
				// Why do we need this???
				break;
			}
			SDclose(*dbs);
			sprintf(errormessage,"read failed: %s",strerror(errno));
			return 1;
		}
		len=strlen(buffer);
		if (len==4095) {
			SDclose(*dbs);
			sprintf(errormessage,"buffer overrun");
			return 1;
		}
		if (buffer[len-1]=='\n') buffer[len-1]=0;
		if (SDindex(*dbs,buffer)!=count) {
			SDclose(*dbs);
			sprintf(errormessage,"open failed on SDindex");
			return 1;
		}
		count++;
	}
	fclose(f);
	if (!readonly){
		f=fopen(filename,"a");
		if (f==NULL){
			SDclose(*dbs);
			sprintf(errormessage,"open for append failed: %s",strerror(errno));
			return 1;
		}
		(*dbs)->f=f;
	} else {
		(*dbs)->f=NULL;
	}
	return 0;
}

extern int SDclose(stringdbs_t dbs){
	if (dbs->f!=NULL && fclose(dbs->f)==EOF){
		sprintf(errormessage,"close failed: %s",strerror(errno));
		delete_record(dbs);
		return 1;
	}
	delete_record(dbs);
	return 0;
}

char* SDerror(){
	return errormessage;
}

int SDcount(stringdbs_t dbs){
	return dbs->count;
}

int SDindex(stringdbs_t dbs,char* string){
	ub4 hash;
	ub4 len;
	char *dup;

	len=strlen(string);
	for(hash=hash_4_1((unsigned char*) string,len,0);
		dbs->table[hash&dbs->mask]!=SD_INDEX_FAILED;
		hash=hash_4_1((unsigned char*) string,len,hash))
		{
		if (!strcmp(string,dbs->data[dbs->table[hash&dbs->mask]])) return dbs->table[hash&dbs->mask];
	}
	dup=strdup(string);
	if (dup==NULL) {
		sprintf(errormessage,"not enough memory for strdup");
		return SD_INDEX_FAILED;
	}
	if (dbs->f!=NULL){
		fprintf(dbs->f,"%s\n",string);
	}
	if (dbs->count==dbs->size) {
		char **newdata;

		newdata=(char**) realloc(dbs->data,(dbs->size+DATA_BLOCK_SIZE)*sizeof(char*));
		if (newdata==NULL) {
			sprintf(errormessage,"not enough memory for data realloc");
			return SD_INDEX_FAILED;
		}
		dbs->data=newdata;
		dbs->size+=DATA_BLOCK_SIZE;
		dbs->data[dbs->count]=dup;
		dbs->table[hash&dbs->mask]=dbs->count;
		dbs->count++;
		if (dbs->size*FULL_OUTOF>dbs->mask*FULL_MAX) {
			int *newtable;
			int i;
			int collision_count;
			int collision_this;
			int collision_worst;

			newtable=(int*)realloc(dbs->table,(dbs->mask+1)*2*sizeof(int));
			if (newtable==NULL){
				sprintf(errormessage,"not enough memory for data realloc");
				return SD_INDEX_FAILED;
			}
			dbs->table=newtable;
			dbs->mask=2*dbs->mask+1;
			for(i=0;i<=dbs->mask;i++) dbs->table[i]=SD_INDEX_FAILED;
			collision_count=0;
			collision_worst=0;
			for(i=0;i<dbs->count;i++){
				collision_this=0;
				len=strlen(dbs->data[i]);
				hash=hash_4_1((unsigned char*) dbs->data[i],len,0);
				while(dbs->table[hash&dbs->mask]!=SD_INDEX_FAILED){
					hash=hash_4_1(
                                        (unsigned char*) dbs->data[i],len,hash);
					collision_count++;
					collision_this++;
				}
				if (collision_this>collision_worst) collision_worst=collision_this;
				dbs->table[hash&dbs->mask]=i;
			}
			fprintf(stderr,"resized hashtable with %d entries to %d with %d collisions %d worst\n",
					dbs->count,dbs->mask+1,collision_count,collision_worst);
		}
		return dbs->count-1;
	} else {
		dbs->data[dbs->count]=dup;
		dbs->table[hash&dbs->mask]=dbs->count;
		return dbs->count++;
	}
}

char* SDstring(stringdbs_t dbs,int index){
	if (0<=index && index < dbs->count) {
		return dbs->data[index];
	} else {
		sprintf(errormessage,"illegal index");
		return NULL;
	}
}

