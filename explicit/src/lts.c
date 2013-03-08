/* $Id: lts.c,v 1.26 2007/10/16 11:57:34 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "messages.h"
#include "xlts.h"
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include "seglts.h"
#include "data_io.h"
#include "memstat.h"
#include "bitset.h"
#include "param0.h"
#include "vector_db.h"
#include "utl.h"

/* AUT IO */

#include "aut-io.h"
#include "label.h"

typedef int (*compar_f) (const void *,const void *);

int lts_write_segments=0;

lts_t lts_create(){
	lts_t lts=(lts_t)malloc(sizeof(struct lts));
	if (lts==NULL) {
		Fatal(1,1,"out of memory in new_lts");
	}
	lts->begin=NULL;
	lts->src=NULL;
	lts->label=NULL;
	lts->dest=NULL;
	lts->type=LTS_LIST;
	lts->transitions=0;
	lts->states=0;
	lts->tau=-1;
        lts->deadlock = DEADLOCK;
	lts->label_string=NULL;
        lts->s_ofs= lts->t_ofs = 0;
        lts->root = lts->root2 = 0;
	return lts;
}

void lts_free(lts_t lts){
	lts->begin=realloc(lts->begin,0);
	lts->src=realloc(lts->src,0);
	lts->label=realloc(lts->label,0);
	lts->dest=realloc(lts->dest,0);
	free(lts);
}

static void build_block(int states,cell_t transitions,cell_t *begin,
        cell_t *block,uint32_t *label,cell_t *other){
	cell_t i, loc1,loc2;
	uint32_t tmp_label1,tmp_label2;
	uint32_t tmp_other1,tmp_other2;
	for(i=0;i<states;i++) begin[i]=0;
	for(i=0;i<transitions;i++) {
            if (block[i]>=states) fprintf(stderr, "States %d Block % ld i=% ld\n", 
              states, block[i], i);
            assert(block[i]<states);
            begin[block[i]]++;
            }
	for(i=1;i<states;i++) begin[i]=begin[i]+begin[i-1];
        if (transitions>0)
	for(i=transitions-1;1;i--){
		block[i]=--begin[block[i]];
                if (i==0) break;
	}
	begin[states]=transitions;
	for(i=0;i<transitions;i++){
		if (block[i]==i) {
			continue;
		}
		loc1=block[i];
		tmp_label1=label[i];
		tmp_other1=other[i];
		for(;;){
			if (loc1==i) {
				block[i]=i;
				label[i]=tmp_label1;
				other[i]=tmp_other1;
				break;
			}
			loc2=block[loc1];
			tmp_label2=label[loc1];
			tmp_other2=other[loc1];
			block[loc1]=loc1;
			label[loc1]=tmp_label1;
			other[loc1]=tmp_other1;
			if (loc2==i) {
				block[i]=i;
				label[i]=tmp_label2;
				other[i]=tmp_other2;
				break;
			}
			loc1=block[loc2];
			tmp_label1=label[loc2];
			tmp_other1=other[loc2];
			block[loc2]=loc2;
			label[loc2]=tmp_label2;
			other[loc2]=tmp_other2;
		}
	}
}

void lts_set_type(lts_t lts,LTS_TYPE type){
	uint32_t i;
        cell_t j;
	if (lts->type==type) return; /* no type change */

	/* first change to LTS_LIST */
	switch(lts->type){
		case LTS_LIST:
			lts->begin=(cell_t*)malloc(sizeof(cell_t)*(lts->states+1));
			if (lts->begin==NULL) Fatal(1,1,"out of memory in lts_set_type");
			break;
		case LTS_BLOCK:
			lts->src=(cell_t*)malloc(sizeof(cell_t)*
                              (lts->transitions));
			if (lts->src==NULL) Fatal(1,1,"out of memory in lts_set_type");
			for(i=0;i<lts->states;i++){
				for(j=lts->begin[i];j<lts->begin[i+1];j++){
					lts->src[j]=i;
				}
			}
			break;
		case LTS_BLOCK_INV:
			lts->dest=(cell_t*)malloc(sizeof(cell_t)*(lts->transitions));
			if (lts->dest==NULL) Fatal(1,1,"out of memory in lts_set_type");
			for(i=0;i<lts->states;i++){
				for(j=lts->begin[i];j<lts->begin[i+1];j++){
					lts->dest[j]=i;
				}
			}
			break;
	}
	MEMSTAT_CHECK;
	/* then change to required type */
	lts->type=type;
	switch(type){
		case LTS_LIST:
			free(lts->begin);
			lts->begin=NULL;
			return;
		case LTS_BLOCK:
			build_block(lts->states,lts->transitions,lts->begin,lts->src,lts->label,lts->dest);
			free(lts->src);
			lts->src=NULL;
			return;
		case LTS_BLOCK_INV:
			build_block(lts->states,lts->transitions,lts->begin,lts->dest,lts->label,lts->src);
			free(lts->dest);
			lts->dest=NULL;
			return;
	}
}




void lts_set_size(lts_t lts,uint32_t states, cell_t transitions){
	lts->states=states;
	lts->transitions=transitions;
	switch(lts->type){
		case LTS_BLOCK:
		case LTS_BLOCK_INV:
			lts->begin=(cell_t*)realloc(lts->begin,sizeof(cell_t)*(states+1));
			if (lts->begin==NULL) Fatal(1,1,"out of memory in lts_set_size");
	}
	switch(lts->type){
		case LTS_LIST:
		case LTS_BLOCK_INV:
			lts->src=(cell_t*)realloc(lts->src,sizeof(cell_t)*transitions);
			if (lts->src==NULL && transitions!=0) Fatal(1,1,"out of memory in lts_set_size");
	}
	switch(lts->type){
		case LTS_LIST:
		case LTS_BLOCK:
		case LTS_BLOCK_INV:
			lts->label=(uint32_t*)realloc(lts->label,sizeof(uint32_t)*transitions);
			if (lts->label==NULL && transitions!=0) Fatal(1,1,"out of memory in lts_set_size");
	}
	switch(lts->type){
		case LTS_LIST:
		case LTS_BLOCK:
			lts->dest=(cell_t*)realloc(lts->dest,sizeof(cell_t)*transitions);
			if (lts->dest==NULL && transitions!=0) Fatal(1,1,"out of memory in lts_set_size");
	}
}

void lts_uniq(lts_t lts){
	int found;
        uint32_t  i;
        cell_t k, j, count, oldbegin;
	lts_set_type(lts,LTS_BLOCK);
	count=0;
	for(i=0;i<lts->states;i++){
		oldbegin=lts->begin[i];
		lts->begin[i]=count;
		for(j=oldbegin;j<lts->begin[i+1];j++){
			found=0;
			for(k=lts->begin[i];k<count;k++){
				if((lts->label[j]==lts->label[k])&&(lts->dest[j]==lts->dest[k])){
					found=1;
					break;
				}
			}
			if (!found){
				lts->label[count]=lts->label[j];
				lts->dest[count]=lts->dest[j];
				count++;
			}
		}
	}
	lts->begin[lts->states]=count;
	lts_set_size(lts,lts->states,count);
}

void lts_sort_alt(lts_t lts){
	int i,j,k,l,d;
	int *lbl_index;

	lbl_index=(int*)malloc(lts->label_count*sizeof(int));
	for(i=0;i<lts->label_count;i++){
		lbl_index[i]=-1;
	}
	lts_set_type(lts,LTS_BLOCK);
	k=0;
	for(i=0;i<lts->transitions;i++){
		if (lbl_index[lts->label[i]]==-1){
			lbl_index[lts->label[i]]=k;
			k++;
		}
	}
	for(i=0;i<lts->states;i++){
		for(j=lts->begin[i];j<lts->begin[i+1];j++){
			l=lts->label[j];
			d=lts->dest[j];
			for(k=j;k>lts->begin[i];k--){
				if (lbl_index[lts->label[k-1]]<lbl_index[l]) break;
				if ((lts->label[k-1]==l)&&(lts->dest[k-1]<=d)) break;
				lts->label[k]=lts->label[k-1];
				lts->dest[k]=lts->dest[k-1];
			}
			lts->label[k]=l;
			lts->dest[k]=d;
		}
	}
}

void lts_sort(lts_t lts){
	int i,j,k,l,d;
	lts_set_type(lts,LTS_BLOCK);
	for(i=0;i<lts->states;i++){
		for(j=lts->begin[i];j<lts->begin[i+1];j++){
			l=lts->label[j];
			d=lts->dest[j];
			for(k=j;k>lts->begin[i];k--){
				if (lts->label[k-1]<l) break;
				if ((lts->label[k-1]==l)&&(lts->dest[k-1]<=d)) break;
				lts->label[k]=lts->label[k-1];
				lts->dest[k]=lts->dest[k-1];
			}
			lts->label[k]=l;
			lts->dest[k]=d;
		}
	}
}


void lts_sort_dest(lts_t lts){
	int i,j,k,l,d;
	lts_set_type(lts,LTS_BLOCK);
	for(i=0;i<lts->states;i++){
		for(j=lts->begin[i];j<lts->begin[i+1];j++){
			l=lts->label[j];
			d=lts->dest[j];
			for(k=j;k>lts->begin[i];k--){
				if (lts->dest[k-1]<d) break;
				if ((lts->dest[k-1]==d)&&(lts->label[k-1]<=l)) break;
				lts->label[k]=lts->label[k-1];
				lts->dest[k]=lts->dest[k-1];
			}
			lts->label[k]=l;
			lts->dest[k]=d;
		}
	}
}


void lts_bfs_reorder(lts_t lts) {
	int i,j,k;
	int *map,*repr;

	Warning(1,"starting BFS reordering");
	lts_set_type(lts,LTS_BLOCK);
	Warning(2,"sorted lts into blocked format");
	map=(int*)malloc(lts->states*sizeof(int));
	repr=(int*)malloc(lts->states*sizeof(int));
	for(i=0;i<lts->states;i++){
		map[i]=-1;
	}
	repr[0]=lts->root;
	map[lts->root]=0;
	i=0;
	j=1;
	while(i<j){
		for(k=lts->begin[repr[i]];k<lts->begin[repr[i]+1];k++){
			if (map[lts->dest[k]]==-1) {
				map[lts->dest[k]]=j;
				repr[j]=lts->dest[k];
				j++;
			}
		}
		i++;
	}
	MEMSTAT_CHECK;
	if (i<lts->states) {
		Fatal(1,1,"only %d out of %d states reachable",i,lts->states);
	}
	free(repr);
	Warning(2,"created map");
	lts_set_type(lts,LTS_LIST);
	Warning(2,"transformed into list representation");
	for(i=0;i<lts->transitions;i++){
		lts->src[i]=map[lts->src[i]];
		lts->dest[i]=map[lts->dest[i]];
	}
	lts->root=0;
	free(map);
	Warning(2,"applied map");
	lts_set_type(lts,LTS_BLOCK);
	Warning(2,"sorted lts into blocked format");
}

static int *random_value;

static int randomize_compare(const int *a, const int *b){
	return (random_value[*a]-random_value[*b]);
}

#ifdef LINUX

void lts_randomize(lts_t lts) {
	int i,fd;
	int *map;
	map=(int*)malloc(lts->states*sizeof(int));
	for(i=0;i<lts->states;i++) map[i]=i;
        i=1953;
        /*
	random_value=(int*)malloc(lts->states*sizeof(int));
	if ((fd=open("/dev/random",O_RDONLY))<0) 
           Warning(1,"Cannot open /dev/random");
        else
	if (read(fd,&i,sizeof(int))!=sizeof(int)) 
           Warning(1,"Cannot read /dev/random");
        */
	srand(i);
	close(fd);
	for(i=0;i<lts->states;i++) random_value[i]=rand();
	qsort(map,lts->states,sizeof(int),(compar_f) randomize_compare);
	free(random_value);
	lts_set_type(lts,LTS_LIST);
	Warning(2,"transformed into list representation");
	for(i=0;i<lts->transitions;i++){
		lts->src[i]=map[lts->src[i]];
		lts->dest[i]=map[lts->dest[i]];
	}
	lts->root=map[lts->root];
	free(map);
	Warning(2,"applied map");
}
#endif

static int pass1_dfs_count;

static void pass1_dfs(lts_t lts,int tau,uint32_t *e_time,int *time,int state){
	int i;
	if (e_time[state]>0) return;
	pass1_dfs_count++;
	e_time[state]=1;
	for(i=lts->begin[state];i<lts->begin[state+1];i++){
		if (lts->label[i]==tau) pass1_dfs(lts,tau,e_time,time,lts->dest[i]);
	}
	(*time)++;
	e_time[state]=(*time);
}

static void pass2_dfs(lts_t lts,int tau,uint32_t *map,int component,int state){
	int i;
	if(map[state]>0) return;
	map[state]=component;
	for(i=lts->begin[state];i<lts->begin[state+1];i++){
		if (lts->label[i]==tau) pass2_dfs(lts,tau,map,component,lts->dest[i]);
	}
}

void lts_tau_cycle_elim(lts_t lts){
	int i,time,tmp,component,count,s,l,d,max,tau;
	uint32_t *map;

	tau=lts->tau;
	/* mark with exit times */
	lts_set_type(lts,LTS_BLOCK);
	map=(uint32_t*)malloc(sizeof(uint32_t)*lts->states);
	for(i=0;i<lts->states;i++) {
		map[i]=0;
	}
	time=1;
	max=0;
	for(i=0;i<lts->states;i++){
		pass1_dfs_count=0;
		pass1_dfs(lts,tau,map,&time,i);
		if (pass1_dfs_count) Warning(3,"(tau cycle elim) tau compenent has size %d",pass1_dfs_count);
		if (pass1_dfs_count>max) max=pass1_dfs_count;
	}
	Warning(2,"(tau cycle elim) worst tau component has size %d",max);
	/* renumber: highest exit time means lowest number */
	/* at the same time reverse direction of edges */
	lts_set_type(lts,LTS_LIST);
	lts->root=time-map[lts->root];
	for(i=0;i<lts->transitions;i++){
		tmp=lts->src[i];
		lts->src[i]=time-map[lts->dest[i]];
		lts->dest[i]=time-map[tmp];
	}
	/* mark components */
	lts_set_type(lts,LTS_BLOCK);
	for(i=0;i<lts->states;i++){
		map[i]=0;
	}
	component=0;
	for(i=0;i<lts->states;i++){
		if(map[i]==0){
			component++;
			pass2_dfs(lts,tau,map,component,i);
		}
	}
	/* divide out equivalence classes reverse direction of edges again */
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root]-1;
	count=0;
	for(i=0;i<lts->transitions;i++){
		d=map[lts->src[i]]-1;
		s=map[lts->dest[i]]-1;
		l=lts->label[i];
		if ((l==tau)&&(s==d)) {
			continue;
		}
		lts->src[count]=s;
		lts->label[count]=l;
		lts->dest[count]=d;
		count++;
		if ((l==tau)&&(s>d)){
			Fatal(1,0,"tau from high to low");
		}
	}
	Warning(2,"(tau cycle elim) all tau steps from low to high");
	lts_set_size(lts,component,count);
	free(map);
	lts_uniq(lts);
}

// lts_divergence_marking replaces divergent tau actions with a dedicated
// divergence action ("divergence").
// This variation does contract all nodes in a strongly connected tau component
// into a single node.
static void lts_divergence_marking_contract(lts_t lts){
	int i,time,tmp,component,count,s,l,d,max,tau,divergent;
	uint32_t *map;

        // Create new label, and store some index
        divergent = getlabelindex("divergent", 1);
        Warning(2,"label index for divergent: %d\n", divergent);
        // New count of labels (this includes divergent)
        count=getlabelcount();
        // Record label in label_string structure.
        // This requires additional space
        lts->label_string=(char**) realloc(lts->label_string, count*sizeof(char*));
        lts->label_string[count-1]=getlabelstring(divergent);

	tau=lts->tau;
	/* mark with exit times */
	lts_set_type(lts,LTS_BLOCK);
	map=(uint32_t*)malloc(sizeof(uint32_t)*lts->states);
	for(i=0;i<lts->states;i++) {
		map[i]=0;
	}
	time=1;
	max=0;
	for(i=0;i<lts->states;i++){
		pass1_dfs_count=0;
		pass1_dfs(lts,tau,map,&time,i);
		if (pass1_dfs_count) Warning(3,"(div marking) tau component has size %d",pass1_dfs_count);
		if (pass1_dfs_count>max) max=pass1_dfs_count;
	}
	Warning(2,"(div marking) worst tau component has size %d",max);
	/* renumber: highest exit time means lowest number */
	/* at the same time reverse direction of edges */
	lts_set_type(lts,LTS_LIST);
	lts->root=time-map[lts->root];
	for(i=0;i<lts->transitions;i++){
		tmp=lts->src[i];
		lts->src[i]=time-map[lts->dest[i]];
		lts->dest[i]=time-map[tmp];
	}
        // At this point, direction of edges has been reversed.

	/* mark components */
	lts_set_type(lts,LTS_BLOCK);
	for(i=0;i<lts->states;i++){
		map[i]=0;
	}
	component=0;
	for(i=0;i<lts->states;i++){
		if(map[i]==0){
			component++;
			pass2_dfs(lts,tau,map,component,i);
		}
	}
        // Components have been marked.

	/* divide out equivalence classes reverse direction of edges again */
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root]-1;
	count=0;
	for(i=0;i<lts->transitions;i++){
		d=map[lts->src[i]]-1; // SCC of src
		s=map[lts->dest[i]]-1; // SCC of dest
		l=lts->label[i]; // Original label

		if ((l==tau)&&(s==d)) {
                  // Class is divergent (has tau-loop).
                  // Change label into div and re-add the transition.
                  //l=divergent;
//                  continue;
                  l=divergent;
		}
                // Reverse transitions, keep original states.
		//lts->src[count]=lts->dest[i];
		//lts->label[count]=l;
		//lts->dest[count]=lts->src[i];
                lts->src[count]=s;
		lts->label[count]=l;
		lts->dest[count]=d;
		++count;
		if ((l==tau)&&(s>d)){
			Fatal(1,0,"tau from high to low");
		}
	}
	Warning(2,"(div marking) all tau steps from low to high");
	lts_set_size(lts,component,count);
	free(map);
	lts_uniq(lts);
}

void lts_divergence_marking(lts_t lts){
	int i,time,tmp,component,count,s,l,d,max,tau,divergent;
	uint32_t *map;

        // array recording divergence information per state
        int* divergence_marking;
        uint32_t divergence_count; // record number of divergences
        divergence_count = 0;
        divergence_marking=(uint32_t*)malloc(sizeof(uint32_t)*lts->states);
        for(i=0; i<lts->states;++i)
        {
          divergence_marking[i]=0;
        }
        // marking has position for each state;

        // Create new label, and store some index
        divergent = getlabelindex("divergent", 1);
        Warning(2,"label index for divergent: %d\n", divergent);
        // New count of labels (this includes divergent)
        count=getlabelcount();
        // Record label in label_string structure.
        // This requires additional space
        lts->label_string=(char**) realloc(lts->label_string, count*sizeof(char*));
        lts->label_string[count-1]=getlabelstring(divergent);

	tau=lts->tau;
	/* mark with exit times */
	lts_set_type(lts,LTS_BLOCK);
	map=(uint32_t*)malloc(sizeof(uint32_t)*lts->states);
	for(i=0;i<lts->states;++i) {
		map[i]=0;
	}
	time=1;
	max=0;
	for(i=0;i<lts->states;i++){
		pass1_dfs_count=0;
		pass1_dfs(lts,tau,map,&time,i);
		if (pass1_dfs_count) Warning(3,"(div marking) tau component has size %d",pass1_dfs_count);
		if (pass1_dfs_count>max) max=pass1_dfs_count;
	}
	Warning(2,"(div marking) worst tau component has size %d",max);
	/* renumber: highest exit time means lowest number */
	/* at the same time reverse direction of edges */
	lts_set_type(lts,LTS_LIST);
	lts->root=time-map[lts->root];
	for(i=0;i<lts->transitions;i++){
		tmp=lts->src[i];
		lts->src[i]=time-map[lts->dest[i]];
		lts->dest[i]=time-map[tmp];
	}
        // At this point, direction of edges has been reversed.

	/* mark components */
	lts_set_type(lts,LTS_BLOCK);
	for(i=0;i<lts->states;i++){
		map[i]=0;
	}
	component=0;
	for(i=0;i<lts->states;i++){
		if(map[i]==0){
			++component;
			pass2_dfs(lts,tau,map,component,i);
		}
	}
        // Components have been marked.

	/* divide out equivalence classes reverse direction of edges again */
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root]-1;
	for(i=0;i<lts->transitions;++i){
		d=map[lts->src[i]]-1; // SCC of src
		s=map[lts->dest[i]]-1; // SCC of dest
		l=lts->label[i]; // Original label

		if ((l==tau)&&(s==d)) {
                  // Class is divergent (has tau-loop).
                  // Change label into div and re-add the transition.
                  divergence_marking[lts->src[i]] = 1;
                  ++divergence_count;
		}
                // Reverse transitions, keep original states.
                tmp=lts->src[i];
		lts->src[i]=lts->dest[i];
		lts->label[i]=l;
		lts->dest[i]=tmp;
		if ((l==tau)&&(s>d)){
			Fatal(1,0,"tau from high to low");
		}
	}

        tmp = lts->transitions;
	//lts_set_size(lts,component,count);
        lts_set_size(lts, lts->states, (lts->transitions) + divergence_count);
        // start adding at position tmp;
        for(i = 0; i < lts->states; ++i)
        {
          if(divergence_marking[i]==1)
          {
            Warning(3,"  marking state i: %ld as divergent. Position: %ls", i, tmp);
            lts->src[tmp]=i;
            lts->label[tmp]=divergent;
            lts->dest[tmp]=i;
            ++tmp;
          }
        }
        lts->transitions=tmp;
	Warning(2,"(div marking) all tau steps from low to high");

	free(map);
        free(divergence_marking);
	lts_uniq(lts);
        Warning(2,"done marking divergent states");
}

void lts_remove_divergence_marking(lts_t lts){
  int i, tau, divergent;
  tau = lts->tau;

  divergent = getlabelindex("divergent", 0);
  
  Warning(2,"replacing divergent labels with tau");

  if(divergent >= 0)
  {
    for(i = 0; i < lts->transitions; ++i)
    {
      if(lts->label[i] == divergent)
      {
        lts->label[i] = tau;
      }
    }
  }

  Warning(2,"done replacing divergent labels with tau");
}


static int normalize(int *map,int i){
	int old;
	if (map[i]==i) return i;

	old=map[i];
	map[i]=i;
	map[i]=normalize(map,old);
	return map[i];
}

void lts_tau_indir_elim(lts_t lts){
	int i,*map,tau,scount,tcount;

	tau=lts->tau;
	lts_set_type(lts,LTS_BLOCK);
	map=(int*)malloc(lts->states*sizeof(int));
	for(i=0;i<lts->states;i++){
		if((lts->begin[i+1]-lts->begin[i])==1 && lts->label[lts->begin[i]]==tau){
			lts->label[lts->begin[i]]=-1;
			map[i]=lts->dest[lts->begin[i]];
		} else {
			map[i]=i;
		}
	}
	for(i=0;i<lts->states;i++){
		map[i]=normalize(map,i);
	}
	lts_set_type(lts,LTS_LIST);
	lts->root=map[lts->root];
	for(i=0;i<lts->transitions;i++){
		lts->dest[i]=map[lts->dest[i]];
		lts->src[i]=map[lts->src[i]];
		if ((lts->label[i]==tau) && (lts->src[i]==lts->dest[i])) lts->label[i]=-1;
	}
	for(i=0;i<lts->states;i++){
		map[i]=0;
	}
	map[lts->root]=1;
	for(i=0;i<lts->transitions;i++){
		if (lts->label[i]!=-1) {
			map[lts->dest[i]]=1;
		}
	}
	scount=0;
	for(i=0;i<lts->states;i++){
		if (map[i]==1){
			map[i]=scount;
			scount++;
		}
	}
	lts->root=map[lts->root];
	tcount=0;
	for(i=0;i<lts->transitions;i++){
		if (lts->label[i]!=-1){
			lts->dest[tcount]=map[lts->dest[i]];
			lts->label[tcount]=lts->label[i];
			lts->src[tcount]=map[lts->src[i]];
			tcount++;
		}
	}
	lts_set_size(lts,scount,tcount);
	free(map);
}


static void lts_read_aut(char *name,lts_t lts){
	GZfile file;
	int i,count;
	file=GZopen(name,"r");
	if (file == NULL) {
		FatalCall(1,0,"Failed to open %s for reading",name);
	}
	if (readaut(file,lts)<0)
           Fatal(1,0,"Illegal format encountered at reading %s",name);
	count=getlabelcount();
	lts->label_string=malloc(count*sizeof(char*));
	for(i=0;i<count;i++){
		lts->label_string[i]=getlabelstring(i);
	}
	if (lts->tau<0) lts->tau=getlabelindex("\"tau\"",0);
	if (lts->tau<0) lts->tau=getlabelindex("tau",0);
	if (lts->tau<0) lts->tau=getlabelindex("i",0);
	lts->label_count=count;
	GZclose(file);
}

static void lts_write_aut(char *name,lts_t lts, int compress){
	GZfile file=GZopen(name,compress?"wb9":"wb0");
	if (file == NULL) {
		FatalCall(1,0,"Could not open %s for output",name);
	}
	writeaut(file,lts);
	GZclose(file);
}

static int lts_guess_format(char *name){
	char *lastdot=strrchr(name,'.');
	if(!lastdot) Fatal(1,0,"filename %s has no extension",name);
	lastdot++;
#ifdef USE_ZLIB
        if (!strcmp(lastdot,"gz"))  return LTS_GZ;
#endif
	if (!strcmp(lastdot,"aut")) return LTS_AUT;
#ifdef USE_BCG
	if (!strcmp(lastdot,"bcg")) return LTS_BCG;
#endif
#ifdef USE_SVC
	if (!strcmp(lastdot,"svc")) return LTS_SVC;
#endif
	if (!strcmp(lastdot,"dir")) return LTS_DIR;
	if (!strcmp(lastdot,"fsm")) return LTS_FSM;
	if (!strcmp(lastdot,"fc2")) return LTS_FC2;
        if (!strcmp(lastdot,"dmp")) return LTS_DMP;
	Fatal(1,1,"unknown extension %s",lastdot);
	return 6987623; // This statement should not be reachable!
}


/* BCG IO */
#ifdef USE_BCG

#include "bcg_user.h"

static void lts_read_bcg(char *name,lts_t lts){
	BCG_TYPE_OBJECT_TRANSITION bcg_graph;
	bcg_type_state_number bcg_s1;
	BCG_TYPE_LABEL_NUMBER bcg_label_number;
	bcg_type_state_number bcg_s2;
	int i;

	BCG_OT_READ_BCG_BEGIN (name, &bcg_graph, 0);
	lts_set_type(lts,LTS_LIST);
	Warning(2," %d states %d transitions",BCG_OT_NB_STATES (bcg_graph),BCG_OT_NB_EDGES (bcg_graph));
	lts_set_size(lts,BCG_OT_NB_STATES (bcg_graph),BCG_OT_NB_EDGES (bcg_graph));
	lts->root=BCG_OT_INITIAL_STATE (bcg_graph);
	lts->label_count=BCG_OT_NB_LABELS (bcg_graph);
	lts->label_string=malloc(lts->label_count*sizeof(char*));
	for(i=0;i<lts->label_count;i++){
		lts->label_string[i]=strdup(BCG_OT_LABEL_STRING (bcg_graph,i));
		if (!BCG_OT_LABEL_VISIBLE (bcg_graph,i)){
			if (lts->tau==-1) {
				lts->tau=i;
			} else {
				Fatal(1,1,"more than one invisible label");
			}
		}
	}
	i=0;
	BCG_OT_ITERATE_PLN (bcg_graph,bcg_s1,bcg_label_number,bcg_s2){
		lts->src[i]=bcg_s1;
		lts->label[i]=bcg_label_number;
		lts->dest[i]=bcg_s2;
		i++;
	} BCG_OT_END_ITERATE;
	BCG_OT_READ_BCG_END (&bcg_graph);
}

static void lts_write_bcg(char *name,lts_t lts){
	int i,j;
	lts_set_type(lts,LTS_BLOCK);
	BCG_IO_WRITE_BCG_BEGIN (name,lts->root,2,"bsim2",0);
	for(i=0;i<lts->states;i++) for(j=lts->begin[i];j<lts->begin[i+1];j++){
                int l=lts->label[j];
                DECLA(char, a, strlen(lts->label_string[l])+3);
		/* a[0]='"'; */
                strcpy(a,lts->label_string[l]); 
                /* strcat(a,"\""); */
		BCG_IO_WRITE_BCG_EDGE (i,(l==lts->tau)?"i":(a),lts->dest[j]);
	}
	BCG_IO_WRITE_BCG_END ();
}

#endif
/* BCG IO END */

static void lts_write_dir(char *name,lts_t lts){
	seginfo_t info;
	char filename[1024];
	int i,j,k;
	FILE *output;
	FILE **src_out;
	FILE **lbl_out;
	FILE **dst_out;

	if (lts_write_segments==0) lts_write_segments=1;
	Warning(1,"writing %s with %d segment(s)",name,lts_write_segments);
	lts_set_type(lts,LTS_BLOCK);
	SLTSCreateInfo(&info,lts_write_segments);
	info->label_tau=lts->tau;
	info->label_count=lts->label_count;
	info->initial_seg=lts->root%lts_write_segments;
	info->initial_ofs=lts->root/lts_write_segments;
	CreateEmptyDir(name,DELETE_ALL);
	sprintf(filename,"%s/TermDB",name);
	output=fopen(filename,"w");
	for(i=0;i<lts->label_count;i++){
		fprintf(output,"%s\n",lts->label_string[i]);
	}
	fclose(output);
	src_out=(FILE**)malloc(lts_write_segments*sizeof(FILE*));
	lbl_out=(FILE**)malloc(lts_write_segments*sizeof(FILE*));
	dst_out=(FILE**)malloc(lts_write_segments*sizeof(FILE*));
	for(i=0;i<lts_write_segments;i++) {
		for(j=0;j<lts_write_segments;j++) {
			sprintf(filename,"%s/src-%d-%d",name,i,j);
			src_out[j]=fopen(filename,"w");
			sprintf(filename,"%s/label-%d-%d",name,i,j);
			lbl_out[j]=fopen(filename,"w");
			sprintf(filename,"%s/dest-%d-%d",name,i,j);
			dst_out[j]=fopen(filename,"w");
		}
		for(j=i;j<lts->states;j+=lts_write_segments){
			for(k=lts->begin[j];k<lts->begin[j+1];k++){
				int dseg=(lts->dest[k])%lts_write_segments;
				info->transition_count[i][dseg]++;
				fwrite32(src_out[dseg],info->state_count[i]);
				fwrite32(lbl_out[dseg],lts->label[k]);
				fwrite32(dst_out[dseg],(lts->dest[k])/lts_write_segments);
			}
			info->state_count[i]++;
		}
		for(j=0;j<lts_write_segments;j++) {
			fclose(src_out[j]);
			fclose(lbl_out[j]);
			fclose(dst_out[j]);
		}
	}
	info->info="bsim2 output";
	SLTSWriteInfo(info,name);
}

#include "dlts.h"
static void lts_read_dir(char *name,lts_t lts) {
	dlts_t dlts;
	int i,j,k;
        cell_t t_offset, t_count;
        uint32_t s_count, *offset;
	dlts=dlts_create();
	dlts->dirname=name;
	dlts_getinfo(dlts);
	if (lts_write_segments==0) {
		lts_write_segments=dlts->segment_count;
		Warning(1,"setting lts_write_segments to %d",dlts->segment_count);
	}
	s_count=0;
	t_count=0;
	offset=(uint32_t*)calloc(dlts->segment_count,sizeof(uint32_t));
	for(i=0;i<dlts->segment_count;i++){
		offset[i]=s_count;
		s_count+=dlts->state_count[i];
		for(j=0;j<dlts->segment_count;j++){
			t_count+=dlts->transition_count[i][j];
		}
	}
	lts_set_type(lts,LTS_LIST);
	lts_set_size(lts,s_count,t_count);
	lts->root=offset[dlts->root_seg]+dlts->root_ofs;
	lts->tau=dlts->tau;

	dlts_getTermDB(dlts);
	lts->label_count=dlts->label_count;
	lts->label_string=malloc(lts->label_count*sizeof(char*));
	for(i=0;i<lts->label_count;i++){
		lts->label_string[i]=strdup(dlts->label_string[i]);
	}

	t_offset=0;
	for(i=0;i<dlts->segment_count;i++){
		for(j=0;j<dlts->segment_count;j++){
			dlts_load_src(dlts,i,j);
			dlts_load_label(dlts,i,j);
			dlts_load_dest(dlts,i,j);
			for(k=0;k<dlts->transition_count[i][j];k++){
int d = offset[i]+dlts->src[i][j][k];
assert(0<=d&&d<s_count);
				lts->src[t_offset+k]= d;
				lts->label[t_offset+k]=dlts->label[i][j][k];
				lts->dest[t_offset+k]=offset[j]+dlts->dest[i][j][k];
			}
			t_offset+=dlts->transition_count[i][j];
			dlts_free_src(dlts,i,j);
			dlts_free_label(dlts,i,j);
			dlts_free_dest(dlts,i,j);
		}
	}

	dlts_free(dlts);
}

#ifdef USE_SVC
#include "svc.h"
#include "aterm2.h"

void* lts_stack_bottom=NULL;
int lts_aterm_init_done=0;

static void lts_read_svc(char *name,lts_t lts){
	SVCfile inFile;
	SVCbool indexed;
	SVCstateIndex fromState, toState;
	SVClabelIndex label;
	SVCparameterIndex parameter;
	int i, iact_ptr=0;
        char *iact[]={"i","tau","\"tau\""};

	if(lts_aterm_init_done==0) ATinit(0,NULL,lts_stack_bottom);

	lts_set_type(lts,LTS_LIST);
	SVCopen(&inFile, name, SVCread, &indexed);
	lts_set_size(lts,SVCnumStates(&inFile),SVCnumTransitions(&inFile));
	lts->root=SVCgetInitialState(&inFile);
	lts->label_count=SVCnumLabels(&inFile);
	lts->label_string=(char**)malloc(SVCnumLabels(&inFile)*sizeof(char*));
	i=0;
	while (SVCgetNextTransition(&inFile, &fromState, &label, &toState, &parameter)){
		lts->src[i]=fromState;
		lts->label[i]=label;
		lts->dest[i]=toState;
		i++;
	}
	for(i=0;i<SVCnumLabels(&inFile);i++){
                int k=0, iact_n= sizeof(iact)/sizeof(char*);
		lts->label_string[i]=strdup(ATwriteToString(SVClabel2ATerm(&inFile,i)));
                for (k=iact_ptr;k<iact_n;k++) 
		if(!strcmp(iact[k],lts->label_string[i])) break;
                if (k<iact_n) {
                    iact_ptr=k;
	            lts->tau=i;
		    }
        }
	if (SVCclose(&inFile)<0){
		Fatal(1,1, "SVC file trailer corrupt");
	}
}


static void lts_write_svc(char *name,lts_t lts){	
	SVCbool indexed=SVCtrue;
	SVCfile outFile;
	SVCparameterIndex parameter;
	SVClabelIndex label;
	SVCstateIndex fromState, toState;
	SVCbool       _new;
	int i,j,lbl_i;
	char *lbl_s;

	if(lts_aterm_init_done==0) ATinit(0,NULL,lts_stack_bottom);

	lts_set_type(lts,LTS_BLOCK);
	SVCopen(&outFile,name,SVCwrite,&indexed);
	parameter=SVCnewParameter(&outFile, (ATerm)ATmakeList0(), &_new);
	SVCsetCreator(&outFile, "lts");
	SVCsetInitialState(&outFile, SVCnewState(&outFile, (ATerm)ATmakeInt(lts->root), &_new));
	for(i=0;i<lts->states;i++){
                fromState=SVCnewState(&outFile, (ATerm)ATmakeInt(i), &_new);
		for(j=lts->begin[i];j<lts->begin[i+1];j++){
			lbl_i=lts->label[j];
			if(lbl_i==lts->tau){
				lbl_s="i";
			} else {
				lbl_s=lts->label_string[lbl_i];
			}
			toState=SVCnewState(&outFile, (ATerm)ATmakeInt(lts->dest[j]), &_new);
			label=SVCnewLabel(&outFile, (ATerm)ATmakeAppl(ATmakeAFun(lbl_s,0,ATfalse)), &_new);
			SVCputTransition(&outFile, fromState, label, toState, parameter);
		}
	}
	SVCclose(&outFile);
}


#endif

void lts_join(lts_t lts1, lts_t lts2, lts_t lts) {
   int i, n1 = lts1->states, n2 = lts2->states,
   m1 = lts1->transitions, m2 = lts2->transitions, count,
   tau1 = lts1->tau, tau2 = lts2->tau;
   if (tau1>=0 && tau2>=0 && 
         strcmp(lts1->label_string[tau1],lts2->label_string[tau2]))
   Fatal(1,1,"Different tau's defined %s != %s",
            lts1->label_string[tau1],lts2->label_string[tau2]);
   lts_set_type(lts1,LTS_LIST);lts_set_type(lts2,LTS_LIST);
   lts_set_type(lts,LTS_LIST);
   lts_set_size(lts,n1+n2,m1+m2);
   lts->s_ofs = n1; lts->t_ofs = m1;
   lts->root = lts1->root; lts->root2=lts2->root+lts->s_ofs;
   memcpy(lts->src, lts1->src, m1*sizeof(cell_t));
   memcpy(lts->dest, lts1->dest, m1*sizeof(cell_t));
   for (i=0;i<m2;i++) {
       lts->src[m1+i]=lts2->src[i]+n1;
       lts->dest[m1+i]=lts2->dest[i]+n1;
       }
   lts->label_string=
      (char**)malloc((lts1->label_count+lts2->label_count)*sizeof(char*));
   for (i=0;i<m1;i++)
     lts->label[i]=getlabelindex(lts1->label_string[lts1->label[i]], 1);
   for (i=0;i<m2;i++)
     lts->label[m1+i]=getlabelindex(lts2->label_string[lts2->label[i]], 1);
   count=getlabelcount();
	lts->label_string=malloc(count*sizeof(char*));
	for(i=0;i<count;i++){
		lts->label_string[i]=getlabelstring(i);
	}
   if (tau1>=0) lts->tau = lts1->tau;
	lts->label_count=count;
}

static vdb_t vdb = NULL;
static cell_t dmp_transitions = 0, dmp_deadlock = 0;
static uint32_t *dmp_sum_states = NULL;
static int *dmp_states;
static int nsegments  = 0, k1 = 0, k2;
static char **aname, **sname, **dname, *rootdir, *subdir;

static uint32_t* sum_states() {
   int i; 
   uint32_t s = 0,
   *r = calloc(nsegments+1, sizeof(uint32_t));
   for (i=0;i<nsegments;s+=dmp_states[i], i++) {
      // fprintf(stderr,"sum_states: %d\n", s);
      r[i] = s;
      }
   // fprintf(stderr,"sum_states: %d\n", s);
   r[nsegments]=s;
   return r;
   }
   
static int eachFile(char *name) {
    FILE *input = fopen(name,"r");
    elm_t elm[2];
    int constant = -1;
    if (!input) Fatal(1,1,"Load:Cannot read from %s", name);
    while (FREAD(elm, sizeof(elm_t), 2, input)==2) {
  // printmsg("eachFile (%d %d) %d %s", elm[0], elm[1], dmp_transitions, name);
        if (elm[0]>=0) {
            if (elm[1]>=0) {
                /* assert(vdb || elm[1]>0); */
                if (constant<0) constant = elm[0];
                   else if (constant!=elm[0]) 
                       Fatal(1,1,"Illegal (old) .dmp format. (%d!=%d)",
                       constant, elm[0]);
	        if (vdb) VDBput(vdb, elm, NULL);
                else if (dmp_states[elm[0]]<elm[1]) dmp_states[elm[0]] = elm[1];
                if (vdb)
                      {if (elm[1]==DEADLOCK) dmp_deadlock++;}
                else {if (elm[1]==0) dmp_deadlock++;}
		}
            dmp_transitions++;
            }
        }
    fclose(input);
    return 0;
    }

static int eachDir(char *name) {
    char dirname[256];
    sprintf(dirname, "%s/%s", name, "dest");
    ForEachFileInDir(dirname, eachFile);
    nsegments++;
    return 0;
    }
    
static int eachFile2(char *name) {
    char *tail;
    dname[k1*nsegments+k2] = strdup(name);
    aname[k1*nsegments+k2]= (char*) malloc(strlen(name)*sizeof(char)+1);
    sname[k1*nsegments+k2]= (char*) malloc(strlen(name)*sizeof(char)+1);
    tail = strrchr(name,'/')+1;
    sprintf(aname[k1*nsegments+k2],"%s/%s/act/%s", rootdir, subdir, tail);
    sprintf(sname[k1*nsegments+k2],"%s/%s/src/%s", rootdir, tail, subdir);
    // fprintf(stderr,"EachFile2: dest file %s\n", name);
    k2++;
    return 0;
    }

static int eachDir2(char *name) {
    char dirname[256];
    subdir = strrchr(name,'/')+1;
    sprintf(dirname, "%s/%s", name, "dest");
    k2 = 0;
    ForEachFileInDir(dirname, eachFile2);
    k1++;
    return 0;
    }
   
static void Fill(cell_t *data, char **name ,cell_t *root) {
    int n = nsegments*nsegments, i;
    cell_t k = 0, l = 0;
    for (i=0;i<n;i++) {
       elm_t elm[2];
       FILE *input = fopen(name[i],"r");
       if (!input) Fatal(1,1,"Fill %d: Cannot read from %s", i, name[i]);
       if (FREAD(elm, sizeof(elm_t), 2, input)!=2) 
            Fatal(1,1,"Fill %d: Empty file %s",  i, name[i]);
       if (root && elm[0]>=0 && elm[1]>=0) {
           assert(vdb || elm[1]>0);
           if (vdb) *root = VDBput(vdb, elm, NULL);
             else *root = elm[1]-1+dmp_sum_states[elm[0]];   
           }
        while (FREAD(elm, sizeof(elm_t), 2, input)==2) {
           if (elm[0]>=0) {
	       if (data[l]==0) {
                   assert(vdb || elm[1]>0);
                   if (vdb) data[k++]=VDBput(vdb, elm, NULL);
                       else data[k++]= elm[1]-1+ dmp_sum_states[elm[0]];
                   }
              l++;
	      }
           }
       fclose(input);
       }
    }
    
static int FillAct(uint32_t *data, char **name, lts_t lts) {
    int n = nsegments*nsegments, i, k = 0, cnt = 0, l=0;
    for (i=0;i<n;i++) {
       int elm[2];
       FILE *input = fopen(name[i],"r");
       if (!input) Fatal(1,1,"FillAct %d: Cannot read from %s", i, name[i]);
       if (FREAD(elm, sizeof(elm_t), 2, input)!=2) 
            Fatal(1,1,"Fill %d: Empty file %s",  i, name[i]);
       while (FREAD(elm, sizeof(elm_t), 2, input)==2) {
           if (elm[0]>=0 && elm[0]!=lts->deadlock) {
               data[k++] = elm[0];
               lts->src[l] = lts->dest[l] = 0;
               l++;
               }
          else  {
           if (elm[0]==lts->deadlock) {
                lts->src[l] = lts->dest[l] = 1;
                cnt++;
                l++;
                } 
               } 
           }
       fclose(input);
       }
    return cnt;
    }
               
void lts_read_dmp(char *dirname, lts_t lts) {
       char *ptr, *termdata, name[256], deadlock[20];  
       unsigned int len, cnt = 0, i;
       GZfile f;
       sprintf(deadlock,"\"%s\"", deadlockstring);
       UTLinit(NULL, NULL, NULL, "lts_read_dmp");
       dmp_states = (int*) calloc(256, sizeof(int));
       dmp_transitions = 0;
       // vdb = VDBcreate(0, 2, NULL, NULL, NULL, NULL, NULL, NULL, NULL);
       sprintf(name,"%s/NODES/adb/%s",dirname, "file");
       if (!(f=GZopen(name,"r"))) Fatal(1,1,"Cannot open %s", name);
       len = GZlen(f);
       termdata=(char*)malloc(len+1);termdata[len]='\0';
       GZread(f, termdata, len);
       // lts->root = UINT_MAX;
       for (cnt=0,ptr=termdata;*ptr && (ptr=strchr(ptr+1,'\n'));cnt++);
       lts->label_string=(char**) malloc(cnt*sizeof(char*));
       for (i=0,ptr=strtok(termdata,"\n");i<cnt;i++) {
         if (i>0) ptr=strtok(NULL,"\n");
         lts->label_string[i] = ptr;
         if (lts->tau== -1 && 
           (!strcmp(ptr, "tau") || !strcmp(ptr, "\"tau\""))) lts->tau = i;
	 if (lts->deadlock== DEADLOCK && !strcmp(ptr,deadlock)) {
	     lts->deadlock = i;
	     }
         }
       GZclose(f);
       lts->label_count = cnt;
       sprintf(name,"%s/STEPPERS",dirname);
       rootdir = strdup(name);
       ForEachDirInDir(name, eachDir);
       if (!vdb) dmp_sum_states = sum_states(); 
       lts_set_type(lts,LTS_LIST);
       Warning(1,"starting reading dmp file: states=%d transitions=% ld",
       vdb?VDBgetCount(vdb):dmp_sum_states[nsegments], 
       dmp_transitions-1-dmp_deadlock);
       lts_set_size(lts, (uint32_t) (vdb?VDBgetCount(vdb):dmp_sum_states[nsegments]),
                       dmp_transitions-1);
       aname = (char**) malloc(nsegments*nsegments*sizeof(char*));
       sname = (char**) malloc(nsegments*nsegments*sizeof(char*));
       dname = (char**) malloc(nsegments*nsegments*sizeof(char*));
       ForEachDirInDir(name, eachDir2); 
       lts->transitions -= FillAct(lts->label, aname, lts);
       Fill(lts->src, sname, NULL);
       Fill(lts->dest, dname, &(lts->root));
       if (vdb) VDBdestroy(vdb);
       free(aname); free(sname); free(dname);  nsegments=0;
       dmp_transitions = 0; k1 = 0;
       }

static void lts_write_fsm(char *name,lts_t lts){
	FILE *f;
	int *fanin;
	int i,j;
	char *pre,*base,*post;

	f=fopen(name,"w");
	fanin=(int*)malloc(lts->states*sizeof(int));
	lts_set_type(lts,LTS_BLOCK);
	for(i=0;i<lts->states;i++) fanin[i]=0;
	for(i=0;i<lts->transitions;i++) fanin[lts->dest[i]]++;
	fprintf(f,"fan_in(0)\r\n");
	fprintf(f,"fan_out(0)\r\n");
	fprintf(f,"node_nr(0)\r\n");
	fprintf(f,"---\r\n");
	for(i=0;i<lts->states;i++){
		fprintf(f,"%d %ld %d\r\n",fanin[i],lts->begin[i+1]-lts->begin[i],i+1);
	}
	fprintf(f,"---\r\n");
	for(i=0;i<lts->states;i++){
		for(j=lts->begin[i];j<lts->begin[i+1];j++){
			if (lts->label[j]==lts->tau) {
				pre="\"";
				base="tau";
				post="\"";
			} else {
				base=lts->label_string[lts->label[j]];
				if (base[0]=='\"') pre=""; else pre="\"";
				if (base[strlen(base)-1]=='\"') post=""; else post="\"";
			}
			fprintf(f,"%d % ld %s%s%s\r\n",i+1,lts->dest[j]+1,pre,base,post);
		}
	}
	fclose(f);
}

static void lts_write_fc2(char *name,lts_t lts){
	FILE *f;
	int i,j;

	lts_set_type(lts,LTS_BLOCK);
	f=fopen(name,"w");
	fprintf(f,"%% FC2 file (oc5 format)\n");
	fprintf(f,"\n");
	fprintf(f,"version \"1\"\n");
	fprintf(f,"\n");
	fprintf(f,"nets 1\n");
	fprintf(f,"\n");
	fprintf(f,"h\"main\">0\n");
	fprintf(f,"net 0\n");
	fprintf(f,"B %d\n",lts->label_count);
	for(i=0;i<lts->label_count;i++){
		char *base,*pre,*post;
		base=lts->label_string[i];
		if (base[0]=='\"') pre=""; else pre="\"";
		if (base[strlen(base)-1]=='\"') post=""; else post="\"";
		fprintf(f,":%d %s%s%s\n",i,pre,base,post);
	}
	fprintf(f,"\n");
	fprintf(f,"H 1\n");
	fprintf(f,":0 \"automaton\"\n");
	fprintf(f,"\n");
	fprintf(f,"L 1\n");
	fprintf(f,":% ld \"initial\"\n",lts->root);
	fprintf(f,"\n");
	fprintf(f,"s\"...bsim2...\" l0>0 h0\n");
	fprintf(f,"\n");
	fprintf(f,"vertice %d\n",lts->states);
	fprintf(f,"\n");
	for(i=0;i<lts->states;i++){
		fprintf(f,"v%d s\"ST%d\" E%ld\n",i,i,lts->begin[i+1]-lts->begin[i]);
		for(j=lts->begin[i];j<lts->begin[i+1];j++){
			fprintf(f,"   b #%d\n",lts->label[j]);
			fprintf(f,"   ->% ld\n",lts->dest[j]);
		}
	}
	fclose(f);
}

void lts_read(int format,char *name,lts_t lts){
	if (format==LTS_AUTO) format=lts_guess_format(name);

	switch(format){
	case LTS_AUT:
#ifdef USE_ZLIB
        case LTS_GZ:
#endif
		lts_read_aut(name,lts);
		break;
#ifdef USE_BCG
	case LTS_BCG:
		lts_read_bcg(name,lts);
		break;
#endif
	case LTS_DIR:
		lts_read_dir(name,lts);
		break;
#ifdef USE_SVC
	case LTS_SVC:
		lts_read_svc(name,lts);
		break;
	case LTS_FSM:
		Fatal(1,1,"cannot parse FSM format yet");
	case LTS_FC2:
		Fatal(1,1,"cannot parse FC2 format");
#endif
        case LTS_DMP:
        lts_read_dmp(name,lts);
        break;	
        default:
		Fatal(1,1,"read: illegal file name extension");
	}
}

void lts_write(int format,char *name,lts_t lts){
	if (format==LTS_AUTO) format=lts_guess_format(name);
	switch(format){
#ifdef USE_ZLIB
        case LTS_GZ:
		lts_write_aut(name,lts, 1);
		break;
#endif
	case LTS_AUT:
		lts_write_aut(name,lts, 0);
		break;
#ifdef USE_BCG
	case LTS_BCG:
		lts_write_bcg(name,lts);
		break;
#endif
	case LTS_DIR:
		lts_write_dir(name,lts);
		break;
#ifdef USE_SVC
	case LTS_SVC:
		lts_write_svc(name,lts);
		break;
#endif
	case LTS_FSM:
		lts_write_fsm(name,lts);
		break;
	case LTS_FC2:
		lts_write_fc2(name,lts);
		break;
	default:
		Fatal(1,1,"write: illegal fulename extension");
	}
}

int lts_diameter(lts_t lts){
	int i,diameter,todo,explored,depth,limit,j,s,t;
	int *state;
	bitset_t visited;

	lts_set_type(lts,LTS_BLOCK);
	visited=bitset_create(8,16);
	state=(int*)malloc(lts->states*sizeof(int));
	diameter=0;
	for(i=0;i<lts->states;i++){
		state[0]=i;
		todo=1;
		explored=0;
		depth=-1;
		bitset_clear_all(visited);
		while(explored<todo){
			depth++;
			limit=todo;
			while(explored<limit){
				s=state[explored];
				for(j=lts->begin[s];j<lts->begin[s+1];j++){
					t=lts->dest[j];
					if (!bitset_test(visited,t)) {
						bitset_set(visited,t);
						state[todo]=t;
						todo++;
					}
				}
				explored++;
			}
		}
		if (depth>diameter) diameter=depth;
	}
	free(state);
	bitset_destroy(visited);
	return diameter;
}

int lts_equivalent(lts_t lts) {return lts->root==lts->root2;}
