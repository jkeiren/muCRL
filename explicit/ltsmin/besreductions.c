/* $id$ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "besreductions.h"
#include "xlts.h"
#include "set.h"
#include "messages.h"
#include "bitset.h"
#include <stdlib.h>
#include "memstat.h"

#define LABELSIZE 500

typedef enum {UNDEF = 0, AND = 1, OR = 2} OPERAND;
typedef struct bes_label BES_LABEL;
struct bes_label {OPERAND op; int rank;} ;
extern BES_LABEL labelset[LABELSIZE]; // [LABELSIZE]; // GLOBALLY ACCESSIBLE LIST OF CONVERSIONS FOR THE LABELS <-> RANK/OP


void bes_reduce_strong(lts_t lts){
	int iter, set, *newmap, setcount, count, *tmp, *map, l1,l2;
        uint32_t i;
	char str[25];
	mytimer_t timer;
        cell_t j;
	l1 = lts->states;
	lts_uniq(lts); // remove redundant transitions (these actually occur in BESs)
	if (l1 > lts->states) Warning(1,"Identified some duplicates");
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK);
	map=(int*)malloc(sizeof(int)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	if (!map || !newmap ) Fatal(1,1,"out of memory");
	for(i=0;i<lts->states;i++){
		map[i]= 0; //labelset[lts->label[lts->begin[i]]].rank; // creating initial block: map(x) = rank(x) for all equations x.
	}
	timer=createTimer();
	startTimer(timer);
	count=1;
	iter=0;
	for(;;){
		MEMSTAT_CHECK;
		SetClear(-1);
		iter++;
		setcount=0;
		for(i=0;i<lts->states;i++){
			set=EMPTY_SET;
			for(j=lts->begin[i];j<lts->begin[i+1];j++) set=SetInsert(set,lts->label[j],map[lts->dest[j]]);
			newmap[i]=SetGetTag(set);
			if (newmap[i]<0) {
				SetSetTag(set,setcount);
				newmap[i]=setcount;
				setcount++;
			}
		}
		Warning(2,"count is %d",setcount);
		if(count==setcount) break;
		count=setcount;
		tmp=map;
		map=newmap;
		newmap=tmp;
	}
	SetFree();
	free(newmap);
	stopTimer(timer);
	/* reportTimer(timer,"computation of partition took"); */
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root];
	for(j=0;j<lts->transitions;j++){
		lts->src[j]=map[lts->src[j]];
		lts->dest[j]=map[lts->dest[j]];
	}
	lts->states=count;
	free(map);
	lts_uniq(lts);
	Warning(1,"reduction took %d iterations",iter);
}

void bes_reduce_oblivious(lts_t lts){
	int iter, set, set2, *newmap, setcount, count, *tmp, *map,  l1,l2,d1;
        char *size_sig;
	uint32_t i;
	char str[25];
	mytimer_t timer;
        cell_t j;
	lts_uniq(lts); // remove redundant transitions (these actually occur in BESs)
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK);
	map=(int*)malloc(sizeof(int)*lts->states);
	size_sig=(char*)malloc(sizeof(char)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	if (!map || !newmap || !size_sig ) Fatal(1,1,"out of memory");
	timer=createTimer();
	startTimer(timer);
	count=1;
	iter=1;
	MEMSTAT_CHECK;
	SetClear(-1);
	setcount=0;
	for(i=0;i<lts->states;i++){
		l2 = lts->begin[i];
		l1 = -2-labelset[lts->label[l2]].rank;
		set=SetInsert(EMPTY_SET,l1,0);
		size_sig[i]= 'O';
		newmap[i]=SetGetTag(set);
		if (newmap[i]<0) {
			SetSetTag(set,setcount);
			newmap[i]=setcount++;
		}
	}
	Warning(2,"count is %d",setcount);
	if(count!=setcount)
	{ 
		count=setcount;
		tmp=map;
		map=newmap;
		newmap=tmp;

		for(;;){
			MEMSTAT_CHECK;
			SetClear(-1);
			iter++;
			setcount=0;
			for(i=0;i<lts->states;i++){
				if (size_sig[i] == 'O'){// ignore the logical operand; only use the ranks
					l2 = lts->begin[i];
					d1 = map[lts->dest[l2]];
					l1 = -2-labelset[lts->label[l2]].rank;
					set2 = set = SetInsert(EMPTY_SET,l1,map[lts->dest[l2]]);
					for(j=l2+1;j<lts->begin[i+1];j++){
						set=SetInsert(set,l1,map[lts->dest[j]]);
						if (set2 != set) break;
					}
					if (j < lts->begin[i+1]){
						size_sig[i] = 'M';
						j++;
						for(;j<lts->begin[i+1];j++) set=SetInsert(set,l1,map[lts->dest[j]]);

					}
				}
				else{// take the logical operand into account; 
					set = EMPTY_SET;
					for(j=lts->begin[i];j<lts->begin[i+1];j++){
						set=SetInsert(set,lts->label[j],map[lts->dest[j]]);
					}
				}
				newmap[i]=SetGetTag(set);
				if (newmap[i]<0) {
					SetSetTag(set,setcount);
					newmap[i]=setcount++;
				}
			}
			Warning(2,"count is %d",setcount);
			if(count==setcount) break;
			count=setcount;
			tmp=map;
			map=newmap;
			newmap=tmp;
		}
	}
	SetFree();
	free(newmap);
	stopTimer(timer);
	/* reportTimer(timer,"computation of partition took"); */
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root];
        lts->root2=map[lts->root2];
	for(j=0;j<lts->transitions;j++){
		if (size_sig[lts->src[j]] == 'O') {
			l1 = sprintf(str, "\"code(%d,%d)\"\00", UNDEF,labelset[lts->label[j]].rank);
			lts->label[j]= getlabelindex(str,1);
		}
		lts->src[j]=map[lts->src[j]];
		lts->dest[j]=map[lts->dest[j]];
	}
	lts->states=count;
	free(map);
	free(size_sig);
	lts_uniq(lts);
	Warning(1,"reduction took %d iterations",iter);
}

void bes2_reduce_strong(lts_t lts){
	int *map,count,*newmap,i,*tmp,iter,setcount,j,set;
	bitset_t has_repr;

	has_repr=bitset_create(8,16);
	lts_uniq(lts);
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK);
	map=(int*)malloc(sizeof(int)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	if (!map || !newmap || !has_repr) Fatal(1,1,"out of memory");
	for(i=0;i<lts->states;i++){
		map[i]=0;
	}
	count=1;
	iter=0;
	for(;;){
		SetClear(-1);
		iter++;
		setcount=0;
		for(i=0;i<lts->states;i++){
			set=EMPTY_SET;
			for(j=lts->begin[i];j<lts->begin[i+1];j++){
				set=SetInsert(set,lts->label[j],map[lts->dest[j]]);
			}
			newmap[i]=set;
			if (!bitset_test(has_repr,set)){
				bitset_set(has_repr,set);
				setcount++;
			}
		}
		Warning(2,"count is %d",setcount);
		if(count==setcount) break;
		bitset_clear_all(has_repr);
		count=setcount;
		tmp=map;
		map=newmap;
		newmap=tmp;
	}
	setcount=0;
	for(i=0;i<lts->states;i++){
		newmap[i]=SetGetTag(map[i]);
		if (newmap[i]<0) {
			SetSetTag(map[i],setcount);
			newmap[i]=setcount;
			setcount++;
		}
	}
	free(map);
	map=newmap;
	Warning(2,"final count is %d",setcount);
	SetFree();
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root];
        lts->root2=map[lts->root2];
	for(i=0;i<lts->transitions;i++){
		lts->src[i]=map[lts->src[i]];
		lts->dest[i]=map[lts->dest[i]];
	}
	lts->states=count;
	lts_uniq(lts);
	free(map);
	bitset_destroy(has_repr);
	Warning(1,"reduction took %d iterations",iter);
}

void bes2_reduce_oblivious(lts_t lts){
	int *map,count,*newmap,i,*tmp,iter,setcount,j,set,*size_sig, l1, l2;
        char str[25];
	bitset_t has_repr;
	mytimer_t timer;

	has_repr=bitset_create(8,16);
	lts_uniq(lts);
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK);
	map=(int*)malloc(sizeof(int)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	size_sig=(int*)malloc(sizeof(int)*lts->states);
	if (!map || !newmap || !has_repr || !size_sig) Fatal(1,1,"out of memory");
	timer=createTimer();
	startTimer(timer);
	count=1;
	iter=0;
 	for(i=0;i<lts->states;i++){
		l2 = lts->begin[i];
		l1 = -2-labelset[lts->label[l2]].rank;
		set=SetInsert(EMPTY_SET,l1,0);
		size_sig[i]= 'O';
		newmap[i]=SetGetTag(set);
		if (newmap[i]<0) {
			SetSetTag(set,setcount);
			newmap[i]=setcount++;
		}
	}
	Warning(2,"count is %d",setcount);
	if(count!=setcount)
	{

	for(;;){
		SetClear(-1);
		iter++;
		setcount=0;
		for(i=0;i<lts->states;i++){
			set=EMPTY_SET;
			for(j=lts->begin[i];j<lts->begin[i+1];j++){
				set=SetInsert(set,lts->label[j],map[lts->dest[j]]);
			}
			newmap[i]=set;
			if (!bitset_test(has_repr,set)){
				bitset_set(has_repr,set);
				setcount++;
			}
		}
		Warning(2,"count is %d",setcount);
		if(count==setcount) break;
		bitset_clear_all(has_repr);
		count=setcount;
		tmp=map;
		map=newmap;
		newmap=tmp;
	}
	setcount=0;
	for(i=0;i<lts->states;i++){
		newmap[i]=SetGetTag(map[i]);
		if (newmap[i]<0) {
			SetSetTag(map[i],setcount);
			newmap[i]=setcount;
			setcount++;
		}
	}
        }
	free(map);
	map=newmap;
	Warning(2,"final count is %d",setcount);
	SetFree();
	stopTimer(timer);
	/* reportTimer(timer,"computation of partition took"); */
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root];
        lts->root2=map[lts->root2];
	for(j=0;j<lts->transitions;j++){
		if (size_sig[lts->src[j]] == 'O') {
			l1 = sprintf(str, "\"code(%d,%d)\"\00", UNDEF,labelset[lts->label[j]].rank);
			lts->label[j]= getlabelindex(str,1);
		}
		lts->src[j]=map[lts->src[j]];
		lts->dest[j]=map[lts->dest[j]];
	}
	lts->states=count;
	free(map);
	free(size_sig);
	lts_uniq(lts);
	bitset_destroy(has_repr);
	Warning(1,"reduction took %d iterations",iter);
}


