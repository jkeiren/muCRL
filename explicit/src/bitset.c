/* $Id: bitset.c,v 1.2 2004/04/29 09:58:28 bertl Exp $ */
#include "bitset.h"
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include <stdlib.h>
#include <sys/types.h>

typedef unsigned int word_t;

#define WORD_CLASS ((sizeof(word_t)==4)?5:\
		    ((sizeof(word_t)==8)?6:\
		     ((sizeof(word_t)==16)?7:\
                      (fprintf(stderr,"strange size for type word_t\n"),exit(1),0)\
		   )))

#define WORD_MASK ((1<<WORD_CLASS)-1)

struct bitset {
	element_t max;
	void *set;
	void *default_value;
	int node_class;
	int base_class;
	int depth;
};


#define ALL_ZERO ((void*)1)
#define ALL_ONES ((void*)2)

bitset_t bitset_create(int node_class,int base_class){
	bitset_t set;
	if (base_class < WORD_CLASS) return NULL;
	set=(bitset_t)malloc(sizeof(struct bitset));
	if (set==NULL) return set;
	set->max=(((element_t)1)<<base_class)-1;
	set->set=ALL_ZERO;
	set->default_value=ALL_ZERO;
	set->node_class=node_class;
	set->base_class=base_class;
	set->depth=0;
	return set;
}

static void free_set(int depth,int size,void *set){
	if (set==ALL_ZERO) return;
	if (set==ALL_ONES) return;
	if (depth){
		int i;
		depth--;
		for(i=0;i<size;i++){
			free_set(depth,size,((void**)set)[i]);
		}
	}
	free(set);
}

void bitset_destroy(bitset_t set){
	free_set(set->depth,1<<(set->node_class),set->set);
	free(set);
}

int bitset_clear_all(bitset_t set){
	free_set(set->depth,1<<(set->node_class),set->set);
	set->max=(((element_t)1)<<set->base_class)-1;
	set->set=ALL_ZERO;
	set->default_value=ALL_ZERO;
	set->depth=0;
	return 1;
}

int bitset_set_all(bitset_t set){
	free_set(set->depth,1<<(set->node_class),set->set);
	set->max=(((element_t)1)<<set->base_class)-1;
	set->set=ALL_ONES;
	set->default_value=ALL_ONES;
	set->depth=0;
	return 1;
}

static int expand(bitset_t set){
	void **newset=(void**)malloc((1<<set->node_class)*sizeof(void*));
	int i;
	if(newset==NULL) return 0;
	newset[0]=set->set;
	for(i=1;i<(1<<set->node_class);i++){
		newset[i]=set->default_value;
	}
	set->set=(void*)newset;
	set->max++;
	set->max<<=set->node_class;
	set->max--;
	set->depth++;
	return 1;
}

static int modify(bitset_t set,void**ptr,int depth,void *v,element_t e){
	if ((*ptr)==v) return 1;
	if (depth) {
		int seg;
		int bits;
		if (((int)(*ptr))&3) {
			void **newset=(void**)malloc((1<<set->node_class)*sizeof(void*));
			int i;
			if(newset==NULL) return 0;
			for(i=0;i<(1<<set->node_class);i++){
				newset[i]=(*ptr);
			}
			(*ptr)=(void*)newset;
		}
		depth--;
		bits=depth*set->node_class+set->base_class;
		seg=e>>bits;
		e=e&((1<<bits)-1);
		if (modify(set,(void**)(((void**)(*ptr))+seg),depth,v,e)){
			for(seg=0;seg<(1<<set->node_class);seg++){
				if (((void**)(*ptr))[seg]!=v) return 1;
			}
			free(*ptr);
			*ptr=v;
			return 1;
		} else {
			return 0;
		}
	} else {
		int seg;
		word_t w;
		if (((int)(*ptr))&3) {
			word_t *newset=(word_t*)malloc((1<<set->base_class)>>3);
			int i;
			if(newset==NULL) return 0;
			w=(word_t)0;
			if ((*ptr)==ALL_ONES) w=~w;
			for(i=0;i<(1<<(set->base_class-WORD_CLASS));i++){
				newset[i]=w;
			}
			*ptr=(void*)newset;
		}
		seg=e>>WORD_CLASS;
		e=e&WORD_MASK;
		w=((word_t)1)<<e;
		if (v==ALL_ONES){
			((word_t*)(*ptr))[seg]|=w;
		} else {
			((word_t*)(*ptr))[seg]&=(~w);
		}
		if (v==ALL_ONES) {
			w=~0;
		} else {
			w=0;
		}
		for(seg=0;seg<(1<<(set->base_class-WORD_CLASS));seg++){
			if (((word_t*)(*ptr))[seg]!=w) return 1;
		}
		free(*ptr);
		*ptr=v;
		return 1;
	}
}

int bitset_clear(bitset_t set,element_t e){
	if(e>set->max){
		if (set->default_value==ALL_ZERO) return 1;
		while(e>set->max){
			if (!expand(set)) return 0;
		}
	}
	return modify(set,&(set->set),set->depth,ALL_ZERO,e);
}

int bitset_set(bitset_t set,element_t e){
	if(e>set->max){
		if (set->default_value==ALL_ONES) return 1;
		while(e>set->max){
			if (!expand(set)) return 0;
		}
	}
	return modify(set,&(set->set),set->depth,ALL_ONES,e);
}

static int testbit(bitset_t set,void *ptr,int depth,element_t e){
	int seg;
	int bits;
	if (ptr==ALL_ONES) return 1;
	if (ptr==ALL_ZERO) return 0;
	if (depth) {
		depth--;
		bits=depth*set->node_class+set->base_class;
		seg=e>>bits;
		e=e&((1<<bits)-1);
		return testbit(set,((void**)ptr)[seg],depth,e);
	} else {
		seg=e>>WORD_CLASS;
		e=e&WORD_MASK;
		return ((((word_t*)ptr)[seg]) & (((word_t)1)<<e))?1:0;	
	}
}

int bitset_test(bitset_t set,element_t e){
	if (e>set->max) return (set->default_value==ALL_ONES);
	return testbit(set,set->set,set->depth,e);
}

int bitset_next_clear(bitset_t set,element_t *e);
int bitset_prev_clear(bitset_t set,element_t *e);

static int scan_right_set(bitset_t set,void *ptr,int depth,element_t *e){
	int bits;
	element_t w;
	int seg;
	int found;
	int le;
	word_t word;

	if (ptr==ALL_ONES) return 1;
	if (ptr==ALL_ZERO) {
		bits=depth*set->node_class+set->base_class;
		w=~0;
		w<<=bits;
		*e&=w;
		*e+=1<<bits;
		return 0;
	}
	if (depth) {
		bits=depth*set->node_class+set->base_class;
		w=(1<<bits)-1;
		depth--;
		bits-=set->node_class;
		seg=(*e&w)>>bits;
		for (;seg<(1<<set->node_class);seg++){
			if (scan_right_set(set,((void**)ptr)[seg],depth,e)) return 1;
		}
		return 0;
	} else {
		bits=set->base_class;
		w=(1<<bits)-1;
		le=*e&w;
		*e&=~w;
		found=0;
		for(;le<(1<<set->base_class);le++){
			seg=le>>WORD_CLASS;
			word=1<<(le&WORD_MASK);
			if ((((word_t*)ptr)[seg])&word) {
				found=1;
				break;
			}
		}
		*e+=le;
		return found;
	}
}

int bitset_next_set(bitset_t set,element_t *e){
	element_t old;
	if (*e>set->max) return (set->default_value==ALL_ONES);
	old=*e;
	if (scan_right_set(set,set->set,set->depth,e)) return 1;
	*e=old;
	return (set->default_value==ALL_ONES);
}

static int scan_left_set(bitset_t set,void *ptr,int depth,element_t *e){
	int bits;
	element_t w;
	int seg;
	int found;
	int le;
	word_t word;

	if (ptr==ALL_ONES) return 1;
	if (ptr==ALL_ZERO) {
		bits=depth*set->node_class+set->base_class;
		w=(1<<bits)-1;
		(*e)|=w;
		(*e)-=1<<bits;
		return 0;
	}
	if (depth) {
		bits=depth*set->node_class+set->base_class;
		w=(1<<bits)-1;
		depth--;
		bits-=set->node_class;
		seg=(*e&w)>>bits;
		for (;seg>=0;seg--){
			if (scan_left_set(set,((void**)ptr)[seg],depth,e)) return 1;
		}
		return 0;
	} else {
		bits=set->base_class;
		w=(1<<bits)-1;
		le=*e&w;
		*e&=~w;
		found=0;
		for(;le>=0;le--){
			seg=le>>WORD_CLASS;
			word=1<<(le&WORD_MASK);
			if ((((word_t*)ptr)[seg])&word) {
				found=1;
				break;
			}
		}
		*e+=le;
		return found;
	}
}

int bitset_prev_set(bitset_t set,element_t *e){
	element_t old;
	if (*e>set->max) {
		if (set->default_value==ALL_ONES) return 1;
		old=*e;
		*e=set->max;
	} else {
		old=*e;
	}
	if (scan_left_set(set,set->set,set->depth,e)) return 1;
	*e=old;
	return 0;
}

static void print(FILE*f,bitset_t set,void* ptr,int depth){
	int i,seg;
	for(i=set->depth;i>depth;i--) fprintf(f,"|");
	if (ptr==ALL_ONES) {
		fprintf(f,"+ALL_ONES\n");
	} else if (ptr==ALL_ZERO) {
		fprintf(f,"+ALL_ZERO\n");
	} else if (depth) {
		fprintf(f,"++\n");
		depth--;
		for(seg=0;seg<(1<<set->node_class);seg++) print(f,set,((void**)ptr)[seg],depth);
	} else {
		fprintf(f,"+");
		for(seg=0;seg<(1<<(set->base_class-WORD_CLASS));seg++){
			for(i=0;i<1<<WORD_CLASS;i++){
				fprintf(f,"%s",(((word_t*)ptr)[seg]&(1<<i))?"1":"0");
			}
		}
		fprintf(f,"\n");
	}
}

void bitset_fprint(FILE*f,bitset_t set) {
	print(f,set,set->set,set->depth);
	fprintf(f,"+%s\n",(set->default_value==ALL_ONES)?"ALL_ONES":"ALL_ZERO");
}

