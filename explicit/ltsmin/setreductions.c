/* $id$ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "setreductions.h"
#include "xlts.h"
#include "set.h"
#include "messages.h"
#include "bitset.h"
#include <stdlib.h>
#include "memstat.h"

int tau_cycle_elim=0;

int tau_indir_elim=0;

static void dfs_weak_a(lts_t lts,int tau,int*map,int*newmap,int s,int a,int id){
	int i,sig,t;
	for(i=lts->begin[s];i<lts->begin[s+1];i++){
		if(lts->label[i]==tau) {
			t=lts->src[i];
			sig=SetInsert(newmap[t],a,id);
			if(sig!=newmap[t]){
				newmap[t]=sig;
				dfs_weak_a(lts,tau,map,newmap,t,a,id);
			}
		}
	}
}

static void dfs_weak_tau(lts_t lts,int tau,int*map,int*newmap,int s,int id){
	int i,sig,a,t;
	for(i=lts->begin[s];i<lts->begin[s+1];i++){
		a=lts->label[i];
		t=lts->src[i];
		if(a==tau){
			if (map[t]!=id) {
				sig=SetInsert(newmap[t],tau,id);
				if(sig!=newmap[t]){
					newmap[t]=sig;
					dfs_weak_tau(lts,tau,map,newmap,t,id);
				}
			}
		} else {
			sig=SetInsert(newmap[t],a,id);
			if(sig!=newmap[t]){
				newmap[t]=sig;
				dfs_weak_a(lts,tau,map,newmap,t,a,id);
			}
		}
	}
}

static int weak_essential(int*sig,int*repr,int src,int label,int dest,int tau){
	int set,set2;
	for(set=sig[repr[src]];set!=EMPTY_SET;set=SetGetParent(set)){
		if (SetGetLabel(set)==label){
			for(set2=sig[repr[SetGetDest(set)]];set2!=EMPTY_SET;set2=SetGetParent(set2)){
				if (SetGetLabel(set2)==tau && SetGetDest(set2)==dest) return 0;
			}
		}
	}
	if (label==tau) return 1;
	for(set=sig[repr[src]];set!=EMPTY_SET;set=SetGetParent(set)){
		if (SetGetLabel(set)==tau){
			for(set2=sig[repr[SetGetDest(set)]];set2!=EMPTY_SET;set2=SetGetParent(set2)){
				if (SetGetLabel(set2)==label && SetGetDest(set2)==dest) return 0;
			}
		}
	}
	return 1;
}

void set_reduce_weak(lts_t lts){
	int tau,count,i,*tmp,iter,s,l,d,setcount,j,set,*repr,t_count,tag,num_states,last_trans;
	int *map,*newmap;

	tau=lts->tau;
	if (tau_cycle_elim) {
		lts_tau_cycle_elim(lts);
		Warning(1,"size after tau cycle elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	if (tau_indir_elim) {
		lts_tau_indir_elim(lts);
		Warning(1,"size after trivial tau elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	num_states=lts->states;
	map=(int*)malloc(sizeof(int)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK_INV);
	for(i=0;i<num_states;i++){
		map[i]=0;
		newmap[i]=EMPTY_SET;
	}
	count=1;
	iter=0;
	for(;;){
		SetClear(-1);
		iter++;
		for(i=0;i<num_states;i++){
			dfs_weak_tau(lts,tau,map,newmap,i,map[i]);
		}
		SetSetTag(newmap[lts->root],0);
		setcount=1;
		for(i=0;i<num_states;i++){
			set=newmap[i];
			if (SetGetTag(set)<0) {
				//fprintf(stderr,"new set:");
				//PrintSet(stderr,set);
				//fprintf(stderr,"\n");
				SetSetTag(set,setcount);
				setcount++;
			}
		}
		Warning(2,"count is %d",setcount);
		//for(i=0;i<num_states;i++){
		//	fprintf(stderr,"%d: old %d new %d sig ",i,map[i],SetGetTag(newmap[i]));
		//	SetPrintIndex(stderr,newmap[i],lts->label_string);
		//	fprintf(stderr,"\n");
		//}
		if(count==setcount) break;
		count=setcount;
		for(i=0;i<num_states;i++){
			map[i]=SetGetTag(newmap[i]);
			newmap[i]=EMPTY_SET;
		}
	}
	repr=(int*)malloc(sizeof(int)*count);
	for(i=0;i<count;i++) {
		repr[i]=-1;
	}
	t_count=0;
	for(i=0;i<lts->states;i++){
		if(repr[map[i]]==-1){
			repr[map[i]]=i;
			t_count+=SetGetSize(newmap[i]);
		}
	}
	lts_set_type(lts,LTS_BLOCK);
	lts_set_size(lts,count,t_count);
	lts->root=0;
	lts->begin[0]=0;
	for(i=0;i<lts->states;i++){
		count=lts->begin[i];
		set=newmap[repr[i]];
		while(set!=EMPTY_SET){
			if(weak_essential(newmap,repr,i,SetGetLabel(set),SetGetDest(set),tau)){
				lts->label[count]=SetGetLabel(set);
				lts->dest[count]=SetGetDest(set);
				count++;
			}
			set=SetGetParent(set);
		}
		lts->begin[i+1]=count;
	}
	lts_set_size(lts,lts->states,count);
	SetFree();
	free(newmap);
	free(map);
	free(repr);
	Warning(1,"set2 reduction took %d iterations",iter);
}




void set_reduce_strong(lts_t lts){
	int iter, set, *newmap, setcount, count, *tmp, *map;
        uint32_t i;
	mytimer_t timer;
        cell_t j;
	timer=createTimer();
	startTimer(timer);
	lts_uniq(lts);
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK);
	map=(int*)malloc(sizeof(int)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	if (!map || !newmap ) Fatal(1,1,"out of memory");
	for(i=0;i<lts->states;i++){
		map[i]=0;
	}
	count=1;
	iter=0;
	for(;;){
		MEMSTAT_CHECK;
		SetClear(-1);
		iter++;
		setcount=0;
		for(i=0;i<lts->states;i++){
			set=EMPTY_SET;
			for(j=lts->begin[i];j<lts->begin[i+1];j++){
				set=SetInsert(set,lts->label[j],map[lts->dest[j]]);
			}
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
        lts->root2=map[lts->root2];
	for(j=0;j<lts->transitions;j++){
		lts->src[j]=map[lts->src[j]];
		lts->dest[j]=map[lts->dest[j]];
	}
	lts->states=count;
	free(map);
	lts_uniq(lts);
	Warning(1,"reduction took %d iterations",iter);
}


void set2_reduce_strong(lts_t lts){
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


#define PREV_UNION

void set_reduce_branching(lts_t lts){
	int tau,*map,count,*newmap,i,*tmp,iter,s,l,d,setcount,j,set;
	int this_union;
#ifdef PREV_UNION
	int prev_union;
#endif
	tau=lts->tau;
	tau_cycle_elim=1;
	if (tau_cycle_elim) {
		lts_tau_cycle_elim(lts);
		Warning(1,"size after tau cycle elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	if (tau_indir_elim) {
		lts_tau_indir_elim(lts);
		Warning(1,"size after trivial tau elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK);
	map=(int*)malloc(sizeof(int)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	for(i=0;i<lts->states;i++){
		map[i]=0;
	}
	count=1;
	iter=0;
	for(;;){
		SetClear(-1);
		iter++;
		for(i=lts->states-1;i>=0;i--){
			set=EMPTY_SET;
#ifdef PREV_UNION
			prev_union=EMPTY_SET;
#endif
			for(j=lts->begin[i];j<lts->begin[i+1];j++){
				if (lts->label[j]==tau && map[i]==map[lts->dest[j]]) {
					this_union=newmap[lts->dest[j]];
#ifdef PREV_UNION
					if(this_union!=prev_union){
						prev_union=this_union;
#endif
						set=SetUnion(set,this_union);
#ifdef PREV_UNION
					}
#endif
				} else {
					set=SetInsert(set,lts->label[j],map[lts->dest[j]]);
				}
			}
			newmap[i]=set;
		}
		SetSetTag(newmap[lts->root],0);
		setcount=1;
		for(i=0;i<lts->states;i++){
			set=newmap[i];
			newmap[i]=SetGetTag(set);
			if (newmap[i]<0) {
				//fprintf(stderr,"new set:");
				//PrintSet(stderr,set);
				//fprintf(stderr,"\n");
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
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root];
        lts->root2=map[lts->root2];
	lts->states=count;
	count=0;
	for(i=0;i<lts->transitions;i++){
		s=map[lts->src[i]];
		l=lts->label[i];
		d=map[lts->dest[i]];
		if ((l==tau)&&(s==d)) continue;
		lts->src[count]=s;
		lts->label[count]=l;
		lts->dest[count]=d;
		count++;
	}
	lts_set_size(lts,lts->states,count);
	lts_uniq(lts);
	free(map);
	Warning(1,"reduction took %d iterations",iter);
}

static lts_t inv;
static int *map;
static int *newmap;
static int label;
static int dest;

//static void dfs_insert(lts_t inv,int *map,int *newmap,int label,int dest,int state){
static void dfs_insert(int state){
	int set,j,last,mymap,pred;
	set=SetInsert(newmap[state],label,dest);
	if (set != newmap[state]) {
		newmap[state]=set;
		last=inv->begin[state+1];
		mymap=map[state];
		for(j=inv->begin[state];j<last;j++){
			pred=inv->dest[j];
			if (mymap==map[pred]){
				//dfs_insert(inv,map,newmap,label,dest,pred);
				dfs_insert(pred);
			}
		}
	}
}

void set_reduce_branching2(lts_t lts){
	int tau,count,i,*tmp,iter,s,l,d,setcount,j,set,*repr,t_count,tag,num_states,last_trans;
	//int *map,*newmap;
	//lts_t inv;

	tau=lts->tau;
        lts_divergence_marking(lts);
	if (tau_cycle_elim) {
		lts_tau_cycle_elim(lts);
		Warning(1,"size after tau cycle elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	if (tau_indir_elim) {
		lts_tau_indir_elim(lts);
		Warning(1,"size after trivial tau elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	num_states=lts->states;
	map=(int*)malloc(sizeof(int)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	lts_set_type(lts,LTS_LIST);
	inv=lts_create();
	lts_set_type(inv,LTS_LIST);
	lts_set_size(inv,lts->states,lts->transitions);
	inv->root=0;
	count=0;
	for(i=0;i<lts->transitions;i++) if (lts->label[i]==tau){
		inv->src[count]=lts->dest[i];
		inv->label[count]=lts->label[i];
		inv->dest[count]=lts->src[i];
		count++;
	}
	lts_set_size(inv,lts->states,count);
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK);
	lts_set_type(inv,LTS_BLOCK);
	for(i=0;i<num_states;i++){
		map[i]=0;
		newmap[i]=EMPTY_SET;
	}
	count=1;
	iter=0;
	for(;;){
		SetClear(-1);
		iter++;
		for(i=0;i<num_states;i++){
			last_trans=lts->begin[i+1];
			for(j=lts->begin[i];j<last_trans;j++){
				label=lts->label[j];
				dest=map[lts->dest[j]];
				if (label!=tau || map[i]!=dest) {
					//dfs_insert(inv,map,newmap,lts->label[j],map[lts->dest[j]],i);
					dfs_insert(i);
				}
			}
		}
		SetSetTag(newmap[lts->root],0);
		setcount=1;
		for(i=0;i<num_states;i++){
			set=newmap[i];
			if (SetGetTag(set)<0) {
				//fprintf(stderr,"new set:");
				//PrintSet(stderr,set);
				//fprintf(stderr,"\n");
				SetSetTag(set,setcount);
				setcount++;
			}
		}
		Warning(2,"count is %d",setcount);
		if(count==setcount) break;
		count=setcount;
		for(i=0;i<num_states;i++){
			map[i]=SetGetTag(newmap[i]);
			newmap[i]=EMPTY_SET;
		}
	}
	repr=(int*)malloc(sizeof(int)*count);
	for(i=0;i<count;i++) {
		repr[i]=-1;
	}
	t_count=0;
	for(i=0;i<lts->states;i++){
		if(repr[map[i]]==-1){
			repr[map[i]]=i;
			t_count+=SetGetSize(newmap[i]);
		}
	}
	lts_set_size(lts,count,t_count);
	lts->root=0;
        lts->root2=map[lts->root2];
	lts->begin[0]=0;
	for(i=0;i<lts->states;i++){
		count=lts->begin[i];
		set=newmap[repr[i]];
		while(set!=EMPTY_SET){
			lts->label[count]=SetGetLabel(set);
			lts->dest[count]=SetGetDest(set);
			set=SetGetParent(set);
			count++;
		}
		lts->begin[i+1]=count;
	}
	SetFree();
	free(newmap);
	free(map);
	free(repr);
	Warning(1,"set2 reduction took %d iterations",iter);
}


void set_reduce_branching3(lts_t lts){
	int tau,*map,count,*newmap,i,*tmp,iter,s,l,d,setcount,j,set;
	int itemcount,subitercount,*tmpmap;

	tau=lts->tau;
	if (tau_cycle_elim) {
		lts_tau_cycle_elim(lts);
		Warning(1,"size after tau cycle elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	if (tau_indir_elim) {
		lts_tau_indir_elim(lts);
		Warning(1,"size after trivial tau elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	map=(int*)malloc(sizeof(int)*lts->states);
	tmpmap=(int*)malloc(sizeof(int)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	lts_set_type(lts,LTS_LIST);
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK);
	for(i=0;i<lts->states;i++){
		map[i]=0;
	}
	count=1;
	iter=0;
	for(;;){
		SetClear(-1);
		iter++;
		for(i=0;i<lts->states;i++){
			newmap[i]=EMPTY_SET;
		}

		for(i=0;i<lts->states;i++){
			for(j=lts->begin[i];j<lts->begin[i+1];j++){
				if (lts->label[j]!=tau || map[i]!=map[lts->dest[j]]) {
					newmap[i]=SetInsert(newmap[i],lts->label[j],map[lts->dest[j]]);
				} 
			}
			tmpmap[i]=newmap[i];
		}
		subitercount=0;
		itemcount=1;
		while(itemcount>0){
			subitercount++;
			for(i=0;i<lts->states;i++){
				for(j=lts->begin[i];j<lts->begin[i+1];j++){
					if (lts->label[j]==tau && map[i]==map[lts->dest[j]] && tmpmap[i]!= newmap[lts->dest[j]]) {
						tmpmap[i]=SetUnion(tmpmap[i],newmap[lts->dest[j]]);
					}
				}
			}
			itemcount=0;
			for(i=0;i<lts->states;i++){
				if (tmpmap[i]!=newmap[i]) {
					newmap[i]=tmpmap[i];
					itemcount++;
				}
			}
			Warning(2,"sub iteration %d had %d changes",subitercount,itemcount);
		}
		Warning(1,"Needed %d sub iterations",subitercount);

		SetSetTag(newmap[lts->root],0);
		setcount=1;
		for(i=0;i<lts->states;i++){
			set=newmap[i];
			newmap[i]=SetGetTag(set);
			if (newmap[i]<0) {
				//fprintf(stderr,"new set:");
				//PrintSet(stderr,set);
				//fprintf(stderr,"\n");
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
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root];
        lts->root2=map[lts->root2];
	lts->states=count;
	count=0;
	for(i=0;i<lts->transitions;i++){
		s=map[lts->src[i]];
		l=lts->label[i];
		d=map[lts->dest[i]];
		if ((l==tau)&&(s==d)) continue;
		lts->src[count]=s;
		lts->label[count]=l;
		lts->dest[count]=d;
		count++;
	}
	lts_set_size(lts,lts->states,count);
	lts_uniq(lts);
	free(map);
	Warning(1,"reduction took %d iterations",iter);
}



static void dfs_insert_tau_star_a(lts_t inv,int *newmap,int label,int dest,int state){
	int set,j;
	set=SetInsert(newmap[state],label,dest);
	if (set != newmap[state]) {
		newmap[state]=set;
		for(j=inv->begin[state];j<inv->begin[state+1];j++){
			dfs_insert_tau_star_a(inv,newmap,label,dest,inv->dest[j]);
		}
	}
}

void set_reduce_tau_star_a(lts_t lts){
	int tau,*map,count,*newmap,i,*tmp,iter,s,l,d,setcount,j,set,tau_count,a_count;
	int reachable,r_count,t_count,*repr;
	lts_t inv;

	tau=lts->tau;
	if (tau_cycle_elim) {
		lts_tau_cycle_elim(lts);
		Warning(1,"size after tau cycle elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	if (tau_indir_elim) {
		lts_tau_indir_elim(lts);
		Warning(1,"size after trivial tau elimination is %d states and %d transitions",lts->states,lts->transitions);
	}
	map=(int*)malloc(sizeof(int)*lts->states);
	newmap=(int*)malloc(sizeof(int)*lts->states);
	lts_set_type(lts,LTS_LIST);
	inv=lts_create();
	lts_set_type(inv,LTS_LIST);
	lts_set_size(inv,lts->states,lts->transitions);
	inv->root=0;
	tau_count=0;
	a_count=0;
	for(i=0;i<lts->states;i++){
		map[i]=0;
	}
	map[lts->root]=1;
	for(i=0;i<lts->transitions;i++) {
		if (lts->label[i]!=tau) map[lts->dest[i]]++;
	}
	reachable=0;
	for(i=0;i<lts->states;i++){
		if(map[i]!=0){
			newmap[i]=reachable;
			reachable++;
		} else {
			newmap[i]=(lts->states)+reachable-i-1;
		}
	}
	Warning(1,"%d states are reachable",reachable); 
	for(i=0;i<lts->transitions;i++) {
		if (lts->label[i]==tau){
			inv->src[tau_count]=newmap[lts->dest[i]];
			inv->label[tau_count]=lts->label[i];
			inv->dest[tau_count]=newmap[lts->src[i]];
			tau_count++;
		} else {
			lts->src[a_count]=newmap[lts->src[i]];
			lts->label[a_count]=lts->label[i];
			lts->dest[a_count]=newmap[lts->dest[i]];
			a_count++;
		}
	}
	lts_set_size(inv,lts->states,tau_count);
	lts_set_size(lts,lts->states,a_count);
	lts_sort(lts);
	lts_set_type(lts,LTS_BLOCK);
	lts_set_type(inv,LTS_BLOCK);
	for(i=0;i<lts->states;i++){
		map[i]=0;
		newmap[i]=EMPTY_SET;
	}
	count=1;
	iter=0;
	for(;;){
		SetClear(-1);
		iter++;
		for(i=0;i<lts->states;i++){
			for(j=lts->begin[i];j<lts->begin[i+1];j++){
				dfs_insert_tau_star_a(inv,newmap,lts->label[j],map[lts->dest[j]],i);
			}
		}
		SetSetTag(newmap[lts->root],0);
		setcount=1;
		for(i=0;i<lts->states;i++){
			if (SetGetTag(newmap[i])<0) {
				//fprintf(stderr,"new set:");
				//PrintSet(stderr,set);
				//fprintf(stderr,"\n");
				SetSetTag(newmap[i],setcount);
				setcount++;
			}
			if (i==(reachable -1)) {
				Warning(2,"reachable count is %d",setcount);
				r_count=setcount;
			}
		}
		Warning(2,"count is %d",setcount);
		if(count==setcount) break;
		count=setcount;
		for(i=0;i<lts->states;i++){
			map[i]=SetGetTag(newmap[i]);
			newmap[i]=EMPTY_SET;
		}
	}
	repr=(int*)malloc(sizeof(int)*r_count);
	for(i=0;i<r_count;i++) {
		repr[i]=-1;
	}
	t_count=0;
	for(i=0;i<reachable;i++){
		if(repr[map[i]]==-1){
			repr[map[i]]=i;
			t_count+=SetGetSize(newmap[i]);
		}
	}
	lts_set_size(lts,r_count,t_count);
	lts->root=0;
	lts->begin[0]=0;
	for(i=0;i<r_count;i++){
		count=lts->begin[i];
		set=newmap[repr[i]];
		while(set!=EMPTY_SET){
			lts->label[count]=SetGetLabel(set);
			lts->dest[count]=SetGetDest(set);
			set=SetGetParent(set);
			count++;
		}
		lts->begin[i+1]=count;
	}
	SetFree();
	free(newmap);
	free(map);
	free(repr);
	Warning(1,"reduction took %d iterations",iter);
}

static int mkdet_next(lts_t orig,int l,int S){
	int T,s,i;
	if (S==EMPTY_SET) return EMPTY_SET;
	T=mkdet_next(orig,l,SetGetParent(S));
	s=SetGetDest(S);
	for(i=orig->begin[s];i<orig->begin[s+1];i++){
		if(orig->label[i]==l){
			T=SetInsert(T,0,orig->dest[i]);
		}
	}
	return T;
}

#define MKDET_BLOCK_SIZE 4096
#define MKDET_MONITOR_INTERVAL 10000

static int fully_expored;

static void mkdet_dfs(lts_t orig,int S,lts_t lts,int*scount,int*tcount,int*tmax){
	int l,T;

	if(SetGetTag(S)==-1){
		SetSetTag(S,*scount);
		(*scount)++;
		for(l=0;l<lts->label_count;l++){
			T=mkdet_next(orig,l,S);
			if (T!=EMPTY_SET) {
				mkdet_dfs(orig,T,lts,scount,tcount,tmax);
				if ((*tcount)==(*tmax)) {
					(*tmax)+=MKDET_BLOCK_SIZE;
					lts_set_size(lts,1,(*tmax));
				}
				lts->src[*tcount]=SetGetTag(S);
				lts->label[*tcount]=l;
				lts->dest[*tcount]=SetGetTag(T);
				(*tcount)++;
				if (((*tcount)%MKDET_MONITOR_INTERVAL)==0){
					Warning(1,"visited %d states and %d transitions, fully expored %d states",
						*scount,*tcount,fully_expored);
				}
			}
		}
		fully_expored++;
	}
}

void set_mkdet(lts_t lts){
	int i,j,tcount,tmax,scount;
	lts_t orig;

	orig=lts_create();
	Warning(2,"copying LTS");
	lts_set_type(orig,LTS_BLOCK);
	lts_set_type(lts,LTS_BLOCK);
	lts_set_size(orig,lts->states,lts->transitions);
	orig->root=lts->root;
	for(i=0;i<=lts->states;i++) {
		orig->begin[i]=lts->begin[i];
	}
	for(i=0;i<lts->transitions;i++){
		orig->label[i]=lts->label[i];
		orig->dest[i]=lts->dest[i];
	}
	SetClear(-1);
	tmax=MKDET_BLOCK_SIZE;
	tcount=0;
	scount=0;
	lts_set_type(lts,LTS_LIST);
	lts_set_size(lts,1,tmax);
	fully_expored=0;
	mkdet_dfs(orig,SetInsert(EMPTY_SET,0,orig->root),lts,&scount,&tcount,&tmax);
	//for(i=0;i<orig->states;i++){
	//	mkdet_dfs(orig,SetInsert(EMPTY_SET,0,i),lts,&scount,&tcount,&tmax);
	//}
	lts->root=SetGetTag(SetInsert(EMPTY_SET,0,orig->root));
	lts_set_size(lts,scount,tcount);
	lts_free(orig);
	SetFree();
}





