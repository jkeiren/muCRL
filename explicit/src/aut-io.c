/* $Id: aut-io.c,v 1.8 2007/06/29 13:30:57 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "aut-io.h"
#include "label.h"
#include "config.h"
#include "messages.h"
#include <ctype.h>
#include <stdlib.h>
#include <assert.h>

static char *cvs_id="$Id: aut-io.c,v 1.8 2007/06/29 13:30:57 bertl Exp $";
static char *cvs_id_h=AUT_IO_H;

#define BUFFER_SIZE 100000

int readaut(GZfile file,lts_t lts){
	int states,from_idx,from_end,label_idx,to_idx,i,from,label,to;
        uint32_t transitions, root;
	char buffer[BUFFER_SIZE];
        uint32_t t;
        if (GZgets(file, buffer,BUFFER_SIZE)==NULL){
	        Fatal(1,0,"fgets error (transition %d)",t+1);
		}
        // fprintf(stderr,"Help: %s\n", buffer);
	if (sscanf(buffer,"des (%d,%d,%d ) \n",&root,&transitions,&states)<3)
            return -1;
	lts_set_type(lts,LTS_LIST);
	lts->root=root;
	lts_set_size(lts,states,transitions);
	for(t=0;t<transitions;t++){
                int n; 
		if (GZgets(file, buffer,BUFFER_SIZE)==NULL){
			Fatal(1,0,"fgets error (transition %d)",t+1);
		}
                n = strlen(buffer);
                if (n>BUFFER_SIZE) n = BUFFER_SIZE;
		for(i=strlen(buffer);i>=0 && !isdigit(buffer[i]);i--);
		buffer[i+1]=0;
		for(;i>=0 && isdigit(buffer[i]);i--);
		to_idx=i+1;
		for(;i>=0&&buffer[i]!=',';i--);
		for(i--;i>=0 && isspace(buffer[i]);i--);
		buffer[i+1]=0;

		for(i=0;i<n&& !isdigit(buffer[i]);i++);
		from_idx=i;
		for(;i<n && isdigit(buffer[i]);i++);
		from_end=i;
		for(;i<n&&buffer[i]!=',';i++);
		for(i++;i<n&&isspace(buffer[i]);i++);
		buffer[from_end]='\00';
		label_idx=i;

		from=atoi(buffer+from_idx);
assert(from>=0 && from<states);
		label=getlabelindex(buffer+label_idx,1);
		to=atoi(buffer+to_idx);
if (to<0 || to>=states) fprintf(stderr,"%d:%d < %d < states=%d <= %d=to\n",
t, to, 0, states, to); 
assert(to>=0 && to<states);

		lts->src[t]=from;
		lts->label[t]=label;
		lts->dest[t]=to;
	}
        return 0;
}

/*
 * we map the states of the lts on-the-fly. currently two maps can be chosen:
 *
 * transparent map:
 * #define MAP(s) s
 *
 * forcing root to be state 0: 
 * #define MAP(s) ((s==lts->root)?0:((s==0)?lts->root:s))
 */

#define MAP(s) ((s==lts->root)?0:((s==0)?lts->root:s))

void writeaut(GZfile file,lts_t lts){
	cell_t i,j;
	GZprintf(file,"des(%d,%ld,%d)\n",MAP(lts->root),lts->transitions,lts->states);
	switch(lts->type){
	case LTS_LIST:
		for(i=0;i<lts->transitions;i++){
			GZprintf(file,"(%d,%s,%d)\n",MAP(lts->src[i]),lts->label_string[lts->label[i]],MAP(lts->dest[i]));
		}
		break;
	case LTS_BLOCK:
		for(i=0;i<lts->states;i++){
			for(j=lts->begin[i];j<lts->begin[i+1];j++){
				GZprintf(file,"(%d,%s,%d)\n",MAP(i),lts->label_string[lts->label[j]],MAP(lts->dest[j]));
			}
		}
		break;
	case LTS_BLOCK_INV:
		for(i=0;i<lts->states;i++){
			for(j=lts->begin[i];j<lts->begin[i+1];j++){
				GZprintf(file,"(%d,%s,%d)\n",MAP(lts->src[j]),lts->label_string[lts->label[j]],MAP(i));
			}
		}
		break;
	default:
		lts_set_type(lts,LTS_LIST);
		writeaut(file,lts);
		break;
	}
}


