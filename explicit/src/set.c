/* $Id: set.c,v 1.1 2004/01/29 13:17:32 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "set.h"
#include "messages.h"
#include <stdlib.h>

#define EMPTY_LIST -1


#define sethashcode(set,label,dest) (36425657*set+77673689*label+2341271*dest)

/*
static unsigned int sethashcode(int set,int label,int dest){
	unsigned register int a,b,c;
	a=set;
	b=label;
	c=dest;
  a -= b; a -= c; a ^= (c>>13);
  b -= c; b -= a; b ^= (a<<8); 
  c -= a; c -= b; c ^= (b>>13);
  a -= b; a -= c; a ^= (c>>12);
  b -= c; b -= a; b ^= (a<<16);
  c -= a; c -= b; c ^= (b>>5); 
  a -= b; a -= c; a ^= (c>>3);  
  b -= c; b -= a; b ^= (a<<10); 
  c -= a; c -= b; c ^= (b>>15); 
	return c;
}
*/

#define seteq(l1,d1,l2,d2) ((l1==l2)&&(d1==d2))
#define setleq(l1,d1,l2,d2) ((l1 < l2) || ((l1==l2)&&(d1<=d2)))
#define setless(l1,d1,l2,d2) ((l1 < l2) || ((l1==l2)&&(d1<d2)))


/** dynamic node array **/

struct setnode {
	int	label;
	int	dest;
	int	parent;
	int	tag;
} ;

static struct setnode *setnodes=NULL;
static int setnodesize=0;
static int setnodenext=1;
static int undefined_tag;

#define SET_NODE_BLOCK 15000


static void setchecknode(){
	if (setnodenext>=setnodesize) {
		Warning(2,"setnoderealloc");
		setnodesize+=SET_NODE_BLOCK;
		setnodes=(struct setnode*)realloc(setnodes,setnodesize*sizeof(struct setnode));
	}
}


/** dynamic hash table **/

struct setbucket {
	int	set;
	int	label;
	int	dest;
	int	bigset;
	int	next;
} ;

static struct setbucket *setbuckets=NULL;
static int setbucketsize=0;
static int setbucketnext=0;

#define SET_BUCKET_BLOCK 25000

static const int listhash[1]={EMPTY_LIST};
static int *sethash=(int*)listhash;
static int sethashmask=0;

#define SET_HASH_CLASS 18


static void setcheckbucket(){
	int i,hc;
	if (setbucketnext>=setbucketsize){
		Warning(2,"setbucketrealloc");
		setbucketsize+=SET_BUCKET_BLOCK;
		setbuckets=(struct setbucket*)realloc(setbuckets,setbucketsize*sizeof(struct setbucket));
		if ((sethashmask/4)<(setbucketsize/3)){
			Warning(2,"setrehash");
			if (sethash==listhash) {
				sethashmask=(1<<SET_HASH_CLASS)-1;
				sethash=NULL;
			} else {
				sethashmask=sethashmask+sethashmask+1;
			}
			sethash=(int*)realloc(sethash,(sethashmask+1)*sizeof(int));
			for(i=0;i<=sethashmask;i++){
				sethash[i]=EMPTY_LIST;
			}
			for(i=0;i<setbucketnext;i++){
				hc=sethashcode(setbuckets[i].set,setbuckets[i].label,setbuckets[i].dest) & sethashmask;
				setbuckets[i].next=sethash[hc];
				sethash[hc]=i;
			}
		}
	}
}

/** print **/

void SetPrint(FILE *f,int set){
	int i;
	if (set==EMPTY_SET) {
		fprintf(f,"{}");
	} else {
		fprintf(f,"{-%d->%d",setnodes[set].label,setnodes[set].dest);
		for(i=setnodes[set].parent;i!=EMPTY_SET;i=setnodes[i].parent){
			fprintf(f,",-%d->%d",setnodes[i].label,setnodes[i].dest);
		}
		fprintf(f,"}");
	}
}

void SetPrintIndex(FILE *f,int set,char **index){
	int i;
	if (set==EMPTY_SET) {
		fprintf(f,"{}");
	} else {
		fprintf(f,"{-%s->%d",index[setnodes[set].label],setnodes[set].dest);
		for(i=setnodes[set].parent;i!=EMPTY_SET;i=setnodes[i].parent){
			fprintf(f,",-%s->%d",index[setnodes[i].label],setnodes[i].dest);
		}
		fprintf(f,"}");
	}
}

/** reset **/

void SetFree(){
	Warning(2,"Freeing set structure with %d nodes and %d edges.",setnodenext,setbucketnext);
	free(setnodes);
	setnodes=NULL;
	setnodesize=0;
	setnodenext=1;
	free(setbuckets);
	setbuckets=NULL;
	setbucketsize=0;
	setbucketnext=0;
	free(sethash);
	sethash=(int*)listhash;
	sethashmask=0;
}

/** clear the structure **/

void SetClear(int tag){
	int i;

	setchecknode();
	setcheckbucket();
	undefined_tag=tag;
	setnodes[0].tag=tag;
	Warning(2,"Clearing set structure with %d nodes and %d edges.",setnodenext,setbucketnext);
	setnodenext=1;
	setbucketnext=0;
	for(i=0;i<=sethashmask;i++) sethash[i]=EMPTY_LIST;
}

/** insertion sub routines **/

static int SetBuild(int set,int label,int dest){
	int i,hc;
	//int depth;

	hc=sethashcode(set,label,dest) & sethashmask;
	//depth=1;
	for(i=sethash[hc];i!=EMPTY_LIST;i=setbuckets[i].next){
		if (setbuckets[i].set==set&&setbuckets[i].label==label&&setbuckets[i].dest==dest) return setbuckets[i].bigset;
		//depth++;
	}
	setchecknode();

	setnodes[setnodenext].label=label;
	setnodes[setnodenext].dest=dest;
	setnodes[setnodenext].parent=set;
	setnodes[setnodenext].tag=undefined_tag;

	setcheckbucket();
	hc=sethashcode(set,label,dest) & sethashmask;

	//if(depth==3) Warning(1,"bucket %d exceeding depth %d",hc,depth);

	setbuckets[setbucketnext].set=set;
	setbuckets[setbucketnext].label=label;
	setbuckets[setbucketnext].dest=dest;
	setbuckets[setbucketnext].bigset=setnodenext;
	setbuckets[setbucketnext].next=sethash[hc];
	sethash[hc]=setbucketnext;
	setbucketnext++;

	return setnodenext++;
}

static int SetFind(int set,int label,int dest){
	if (set!=EMPTY_SET) {
		if (setless(label,dest,setnodes[set].label,setnodes[set].dest)) {
			return SetBuild(SetFind(setnodes[set].parent,label,dest),setnodes[set].label,setnodes[set].dest);
		}
		if (seteq(label,dest,setnodes[set].label,setnodes[set].dest)) {
			return set;
		}
	}
	return SetBuild(set,label,dest);
}

/** insert **/

int SetInsert(int set,int label,int dest){
	int i,hc,s;

	hc=sethashcode(set,label,dest) & sethashmask;
	for(i=sethash[hc];i!=EMPTY_LIST;i=setbuckets[i].next){
		if (setbuckets[i].set==set&&setbuckets[i].label==label&&setbuckets[i].dest==dest) return setbuckets[i].bigset;
	}
	s=SetFind(set,label,dest);
	if (setnodes[s].parent!=set) {
		setcheckbucket();
		hc=sethashcode(set,label,dest) & sethashmask;
		setbuckets[setbucketnext].set=set;
		setbuckets[setbucketnext].label=label;
		setbuckets[setbucketnext].dest=dest;
		setbuckets[setbucketnext].bigset=s;
		setbuckets[setbucketnext].next=sethash[hc];
		sethash[hc]=setbucketnext;
		setbucketnext++;
	}
	return s;
}


/** union **/

int SetUnion(int set1,int set2){
	if (set2==EMPTY_SET) {
		return set1;
	} else {
		return SetInsert(SetUnion(set1,setnodes[set2].parent),setnodes[set2].label,setnodes[set2].dest);
	}
}


int SetGetTag(int set){
	return setnodes[set].tag;
}


void SetSetTag(int set,int tag){
	setnodes[set].tag=tag;
}

int SetGetSize(int set){
	int size=0;
	while(set!=EMPTY_SET){
		set=setnodes[set].parent;
		size++;
	}
	return size;
}

void SetGetSet(int set,int*data){
	int i;
	i=SetGetSize(set)-1;
	while(i>=0){
		data[2*i]=setnodes[set].label;
		data[2*i+1]=setnodes[set].dest;
		i--;
		set=setnodes[set].parent;
	}
}

int SetGetLabel(int set){
	return setnodes[set].label;
}

int SetGetDest(int set){
	return setnodes[set].dest;
}

int SetGetParent(int set){
	return setnodes[set].parent;
}

unsigned int SetGetHash(int set){
	unsigned int hash=0;
	while(set!=EMPTY_SET){
		hash=31*hash+sethashcode(0,setnodes[set].label,setnodes[set].dest);
		set=setnodes[set].parent;
	}
	return hash;
}



