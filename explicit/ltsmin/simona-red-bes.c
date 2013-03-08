/* $Id: simona-red.c,v 1.2 2004/11/23 12:36:17 uid523 Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdlib.h>
#include <unistd.h>
#include "xlts.h"
#include "messages.h"
#include "simona-red.h"

static lts_t sig;
static int *next_in_class;

#define LABELSIZE 500

typedef enum {UNDEF = 0, AND = 1, OR = 2} OPERAND;
typedef struct bes_label BES_LABEL;
struct bes_label {OPERAND op; int rank;} ;
extern BES_LABEL labelset[LABELSIZE]; // [LABELSIZE]; // GLOBALLY ACCESSIBLE LIST OF CONVERSIONS FOR THE LABELS <-> RANK/OP

typedef struct record {
	int repr;
	int last;
	int next;
} record_t;

#define TABLE_SIZE 65536
#define TABLE_MASK 65535

static record_t table_record[TABLE_SIZE];
static int table_count=0;
static int table_hash[TABLE_SIZE];

static void ClearTable(){
	int i;
	table_count=0;
	for(i=0;i<TABLE_SIZE;i++) table_hash[i]=-1;
}

static int SameSig(int s1,int s2){
	int i1,i2;
	int end1,end2;

	i1=sig->begin[s1];
	end1=sig->begin[s1+1];
	i2=sig->begin[s2];
	end2=sig->begin[s2+1];
	for(;;){
		if(i1==end1) return (i2==end2); // in this case, the blocks for s1 and s2 coincide
		if(i2==end2) return 0; // in this case, i1 != end1, but i2 == end2, so block s1 and s2 differ
		if(sig->label[i1]!=sig->label[i2]) return 0; // in this case, i1 != end1 && i2 != end2, but s1 and s2 do not share a transition
		if(sig->dest[i1]!=sig->dest[i2]) return 0; // in this case, s1 and s2 do not share a certain destination
		i1++;
		while((i1<end1) && (sig->label[i1]==sig->label[i1-1]) && (sig->dest[i1]==sig->dest[i1-1])) i1++;
		i2++;
		while((i2<end2) && (sig->label[i2]==sig->label[i2-1]) && (sig->dest[i2]==sig->dest[i2-1])) i2++;
	}
}

static int SameSig2(int s1,int s2){
	int i1,i2;
	int dest1, dest2, size1, size2;
	int end1,end2;

	i1=sig->begin[s1];
	Warning(1,"Considering states %d and %d",s1,s2);
	size1 = 1;
	dest1=sig->dest[i1];
	end1=sig->begin[s1+1];

	i2=sig->begin[s2];
	size2 = 1;
	dest2=sig->dest[i2];
	end2=sig->begin[s2+1];
	for(;;){
		if(i1==end1) return (i2==end2);
		if(i2==end2) return 0;
		if(labelset[sig->label[i1]].rank ==labelset[sig->label[i2]].rank) return (sig->dest[i1] == sig->dest[i2]);
		if(sig->dest[i1]!=sig->dest[i2]) return 0;
		if( (labelset[sig->label[i1]].op != labelset[sig->label[i2]].op) && (size1 > 1 || size2 > 1)) return 0; // check this one
		i1++; size1 += (dest1 != sig->dest[i1]);
		while((i1<end1) && 
                      (labelset[sig->label[i1]].rank == labelset[sig->label[i1-1]].rank) && 
                      (sig->dest[i1]==sig->dest[i1-1] &&
		      ((labelset[sig->label[i1]].op == labelset[sig->label[i1-1]].op) || size1 == 1))) {i1++; size1 += (dest1 != sig->dest[i1]);}
		i2++; size2 += (dest2 != sig->dest[i2]);
		while((i2<end2) && (sig->label[i2]==sig->label[i2-1]) && (sig->dest[i2]==sig->dest[i2-1])) {i2++; size2 += (dest2 != sig->dest[i2]);}
	}
}


static int ComputeHash(int state){
	int hash,i,end;

	//return 8634*sig->dest[sig->begin[state]]+64237*sig->label[sig->begin[state]];

	hash=641299;
	end=sig->begin[state+1];
	for(i=sig->begin[state];i<end;){
		hash=687637*(hash+(5419859*sig->label[i]))+(9238841*sig->dest[i]);
		i++;
		while((i<end) && (sig->label[i]==sig->label[i-1]) && (sig->dest[i]==sig->dest[i-1])) i++;
	}
	return hash;
}

static int EnterTable(int state){
	int hash_code,rec;
	//int depth;

	hash_code=ComputeHash(state)&TABLE_MASK;
	rec=table_hash[hash_code];
	//depth=1;
	if(rec==-1){
		Warning(1,"Hasing table");
		table_hash[hash_code]=table_count;
	} else {
		for(;;){
			//depth++;
			Warning (1,"Checking for same signature of state %d",state);
			if (SameSig2(state,table_record[rec].repr)){
				next_in_class[table_record[rec].last]=state;
				next_in_class[state]=-1;
				table_record[rec].last=state;
				return table_record[rec].repr;
			}
			if (table_record[rec].next==-1) break;
			rec=table_record[rec].next;
		}
		table_record[rec].next=table_count;
	}
	if (table_count>=TABLE_SIZE) Fatal(1,1,"please make table dynamic or increase TABLE_SIZE");
	//if (depth>2) Warning(1,"hash bucket %d has depth %d",hash_code,depth);
	table_record[table_count].repr=state;
	table_record[table_count].last=state;
	next_in_class[state]=-1;
	table_record[table_count].next=-1;
	table_count++;
	return state;
}

static void ModifySig(int state, int label,int oldclass,int newclass){
	int i,max;
	i=sig->begin[state+1]-1;
	while(sig->label[i]!=label) i--;
	max=i;
	while(sig->dest[i]!=oldclass)i--;
	while((i<max)&&(sig->dest[i+1]<newclass)){
		sig->dest[i]=sig->dest[i+1];
		i++;
	}
	sig->dest[i]=newclass;
}

static void ModifySig2(int state, int label,int oldclass,int newclass){
	int i,max;
	i=sig->begin[state+1]-1;
	Warning(1,"Modifying signature based on state=%d, rank=%d, op=%d, oldclass=%d and newclass=%d",state,labelset[label].rank,labelset[label].op,oldclass,newclass);
	while(labelset[sig->label[i]].rank !=labelset[label].rank) i--;
	max=i;
	while(sig->dest[i]!=oldclass)i--;
	while((i<max)&&(sig->dest[i+1]<newclass)){
		sig->dest[i]=sig->dest[i+1];
		i++;
	}
	sig->dest[i]=newclass;
}
void simona_strong_reduce(lts_t lts){
	int i,j,s,u,iter;
	int *class,*next_unstable,*changed,*oldclass;
	int first_unstable,last_unstable,changed_count,count;

	sig=lts_create();
	lts_set_size(sig,lts->states,lts->transitions);
	sig->root=lts->root;
	lts_set_type(lts,LTS_LIST);
	Warning (1, "Duplicating LTS");
	for(i=0;i<lts->transitions;i++){
		sig->src[i]=lts->src[i];
		sig->label[i]=lts->label[i];
		sig->dest[i]=0;
	}
	Warning (1, "Sorting LTS");
	lts_sort(sig);
        
	lts_set_type(lts,LTS_BLOCK_INV);

	class=(int*)malloc(lts->states*sizeof(int));
	next_unstable=(int*)malloc(lts->states*sizeof(int));
	changed=(int*)malloc(lts->states*sizeof(int));
	oldclass=(int*)malloc(lts->states*sizeof(int));
	next_in_class=(int*)malloc(lts->states*sizeof(int));
	if ((class==NULL)||(next_unstable==NULL)||(changed==NULL)||(oldclass==NULL)||(next_in_class==NULL)) {
		Fatal(1,1,"out of memory in simona_strong_reduce");
	}
	for(i=0;i<lts->states;i++){
		class[i]=0;
		next_in_class[i]=i+1;
		next_unstable[i]=i;
	}
	next_in_class[lts->states-1]=-1;
	next_unstable[0]=-1;
	first_unstable=0;
	iter=0;
	for(;;){
		/* split and build changed */
		Warning(2,"splitting");
		changed_count=0;
		for(u=first_unstable;u!=-1;) {
			ClearTable();
			for(s=u;s!=-1;){
				j=next_in_class[s];
				Warning (1,"s = %d, u = %d, i = %d, next_in_class[s] = %d",s,u,i,j);
				if ((i=EnterTable(s))!=u) {
					class[s]=i;
					oldclass[changed_count]=u;
					changed[changed_count++]=s;
				}
				s=j;
			}
			s=u;
			u=next_unstable[u];
			next_unstable[s]=s;
		}
		iter++;
		Warning(1,"iteration %d produced %d changes",iter,changed_count);
		if (changed_count==0) break;
		/* build unstable */
		first_unstable=-1;
		for(i=0;i<changed_count;i++){
			for(j=lts->begin[changed[i]];j<lts->begin[changed[i]+1];j++){
				ModifySig2(lts->src[j],lts->label[j],oldclass[i],class[changed[i]]);
				u=class[lts->src[j]];
				if (next_unstable[u]==u){
					if (first_unstable==-1){
						first_unstable=u;
						last_unstable=u;
						next_unstable[u]=-1;
					} else {
						next_unstable[last_unstable]=u;
						next_unstable[u]=-1;
						last_unstable=u;
					}
				}
			}
		}
	}
	/* build reduced lts. */
	count=0;
	for(i=0;i<lts->states;i++) {
		if(class[i]==i) {
			class[i]=count++;
		} else {
			class[i]=class[class[i]];
		}
	}
	lts_set_type(lts,LTS_LIST);
	lts->states=count;
	lts->root=class[lts->root];
	for(i=0;i<lts->transitions;i++){
		lts->src[i]=class[lts->src[i]];
		lts->dest[i]=class[lts->dest[i]];
	}
	lts_uniq(lts);
	free(class);
	free(next_unstable);
	free(changed);
	free(oldclass);
	free(next_in_class);
	lts_free(sig);
}

