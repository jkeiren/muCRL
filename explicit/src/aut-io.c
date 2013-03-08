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

// HACK TO REPRESENT THE OPERANDS AND DEPENDENCIES OF THE BES USING LABELS
#define LABELSIZE 500

typedef enum {UNDEF = 0, AND = 1, OR = 2} OPERAND;
typedef struct bes_label BES_LABEL;
struct bes_label {OPERAND op; int rank;} ;
BES_LABEL labelset[LABELSIZE]; // [LABELSIZE]; // GLOBALLY ACCESSIBLE LIST OF CONVERSIONS FOR THE LABELS <-> RANK/OP


#define BUFFER_SIZE 100000

int readbes(FILE *file, lts_t lts){
	int states,from_idx,i,from,label,to,rank,ah;
	int n,j,l;
	uint32_t transitions, root;
	char buffer[BUFFER_SIZE];
	uint32_t t = 0;
	char str[25];
	OPERAND op;
	
	//if (GZgets(file, buffer,BUFFER_SIZE)==NULL){
	if (fgets(buffer,BUFFER_SIZE,file)==NULL){
		Fatal(1,0,"fgets error (equation %d)", t+1);
		}
	if (sscanf(buffer,"des (%d,%d,%d ) \n",&root,&transitions,&states)<3)
            return -1;

        // allocate memory for the lts; set root
	lts_set_type(lts,LTS_LIST);
	lts->root=root;
	lts_set_size(lts,states,transitions); 

	Warning(1,"Reading %d equations",states);

	t=0; ah=0; rank = 0; // keep track of the ranks of the equations
	while(1){
		//if (GZgets(file, buffer,BUFFER_SIZE)==NULL){break;// reached the end of file
		if (fgets(buffer,BUFFER_SIZE,file)==NULL){break;// reached the end of file
			//Fatal(1,0,"fgets error (transition %d)",t+1);
		}

		n = strlen(buffer);
		if (n>BUFFER_SIZE){
			n = BUFFER_SIZE;
			Warning(1,"Line too long. Parsing may not succeed.");
		}

		for (i=0;i<n && buffer[i]==' ';i++);
		assert(strncmp(buffer+i,"min",3)==0 || strncmp(buffer+i,"max",3)==0); // bail out if not a fixed point sign

		//rank =  ((rank%2==0) == (strncmp(buffer+ i,"max",3) == 0))? rank : rank+1; // increase rank if alternation is seen
		rank+=((rank%2==0) != (strncmp(buffer+i,"max",3)==0)); // increase rank if alternation is seen
		ah+=(ah<rank); //update the alternation hierarchy; alternatively: if (ah<rank) ah=rank;

		for(;i<n&&!isdigit(buffer[i]);i++); // move on to the first digit encountered, i.e., the variable at the left side of the equation
		from_idx=i;//first digit encountered
		for(;i <=n && isdigit(buffer[i]);i++);
		buffer[i]='\00'; // first non-digit replaced by terminal symbol
		from=atoi(buffer+from_idx)-1; // offset by 1 due to input format, which does not start at 0 but 1

		i++; for(;i <= n && !isdigit(buffer[i]);i++); // search the first destination at the right-hand side of the equation
		op=UNDEF; // assume we have an equation of the form sigma X = Y, until disproven at some later stage
		j=n;      // process the equation from right-to-left
		while(j>=i){
			for (;j>=i&&!isdigit(buffer[j]);j--); // find first digit from right to left
			buffer[j+1]='\00';
			for (;j>=i&&isdigit(buffer[j]);j--);  // buffer[j:] contains a digit
			to = atoi(buffer+j+1)-1;               // store the destination
			if (j>i&&op==UNDEF){
				for(;j>=i && buffer[j] !='|' && buffer[j] !='&'; j--); // find logical operand
				if (j >=i) op=(buffer[j]=='|')?OR:AND; 
			}
			j--; // Move buffer to the left
			sprintf(str, "\"%d,%d\"\00", op,rank);
			l=getlabelindex(str,1);
			
			labelset[l].rank = rank; labelset[l].op = op; // map the internal representation onto ranks and operator

			lts->src[t]=from;  // set the from part of the transition
			lts->label[t]=l;  // set the label part
			lts->dest[t]=to;   // set the destination part of the transition
		
			t++;
		}
	};
	// create extra internal labels representing (UNDEF,rank) for each rank <= ah
	rank = 0;
	for (rank=0; rank <= ah; rank++){
		sprintf(str, "\"code(%d,%d)\"\00", UNDEF,rank);
		l=getlabelindex(str,1);
		labelset[l].rank = rank; labelset[l].op = op;
	}
	
	return 0;
}

int readaut(FILE* file,lts_t lts){
	int states,from_idx,from_end,label_idx,to_idx,i,from,label,to;
        uint32_t transitions, root;
	char buffer[BUFFER_SIZE];
        uint32_t t;
        if (fgets(buffer, BUFFER_SIZE, file)==NULL){
                perror("the following error occurred");
	        Fatal(1,0,"fgets error (transition %d)",t+1);
		}
        fprintf(stderr,"Help: `%s'\n", buffer);
	if (sscanf(buffer,"des (%d,%d,%d ) \n",&root,&transitions,&states)<3)
            return -1;
	lts_set_type(lts,LTS_LIST);
	lts->root=root;
	lts_set_size(lts,states,transitions);
	for(t=0;t<transitions;t++){
                int n; 
		if (fgets(buffer,BUFFER_SIZE, file)==NULL){
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
		fprintf(stderr,"Processed transition %d --%s--> %d; label %s is encoded as %d\n",from,buffer+label_idx,to,buffer+label_idx,label);

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

void writeaut(FILE* file,lts_t lts){
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

void writebes(FILE *file,lts_t lts, int oblivious){
	cell_t i,j;
	int r,t1,t2,l;
	char c;
	if (oblivious){
		fprintf(file,"des(%ld,%ld,%d)\n",MAP(lts->root),lts->transitions,lts->states);
		switch(lts->type){
		case LTS_LIST:
			for(i=0;i<lts->transitions;i++){
				fprintf(file,"(%d,%s,%d)\n",MAP(lts->src[i]),lts->label_string[lts->label[i]],MAP(lts->dest[i]));
			}
			break;
		case LTS_BLOCK:
			t2 = 0; r=0;
			for (r=0; t2<lts->states;r++){
				for(t1=0;t1<lts->states;t1++){
					l = lts->label[lts->begin[t1]];
					if (labelset[l].rank == r){
						if (r%2==0) {
							fprintf(file,"max X%d = ",MAP(t1)+1); 
						}
						else {
							fprintf(file,"min X%d = ",MAP(t1)+1);
						}
						if (labelset[l].op != UNDEF)
							c = (labelset[l].op == AND)? '&': '|'; else c = ' ';
						for(j=lts->begin[t1];j<lts->begin[t1+1];j++){
							fprintf(file,"X%d",MAP(lts->dest[j])+1);
							if (j < lts->begin[t1+1]-1) {
								fprintf(file,"%c",c);
							}
						}
						fprintf(file,"\n");
						t2++;
					}
				}
			}
			break;
		case LTS_BLOCK_INV:
			for(i=0;i<lts->states;i++){
				for(j=lts->begin[i];j<lts->begin[i+1];j++){
					fprintf(file,"(%d,%s,%d)\n",MAP(lts->src[j]),lts->label_string[lts->label[j]],MAP(i));
				}
			}
			break;
		default:
			lts_set_type(lts,LTS_LIST);
			writebes(file,lts,oblivious);
			break;
		}
	}
	else {
		switch(lts->type){
		case LTS_LIST:
			fprintf(file,"des(%ld,%ld,%d)\n",MAP(lts->root),lts->transitions,lts->states);
			for(i=0;i<lts->transitions;i++){
				fprintf(file,"(%d,%s,%d)\n",MAP(lts->src[i]),lts->label_string[lts->label[i]],MAP(lts->dest[i]));
			}
			break;
		case LTS_BLOCK:
			t2 = 0;
			for(t1=0;t1<lts->states;t1++){
				l = lts->label[lts->begin[t1]];
				if ((labelset[l].op != UNDEF) && (lts->begin[t1+1]-lts->begin[t1] <=1)) t2++;
			}
			fprintf(file,"des(%ld,%ld,%d)\n",MAP(lts->root),lts->transitions+t2,lts->states);
			t2 = 0; r=0;
			for (r=0; t2<lts->states;r++){
				for(t1=0;t1<lts->states;t1++){
					l = lts->label[lts->begin[t1]];
					if (labelset[l].rank == r){
						if (r%2==0) {
							fprintf(file,"max X%d = ",MAP(t1)+1); 
						}
						else {
							fprintf(file,"min X%d = ",MAP(t1)+1);
						}
						if (labelset[l].op != UNDEF)
							c = (labelset[l].op == AND)? '&': '|'; else c = ' ';
						for(j=lts->begin[t1];j<lts->begin[t1+1];j++){
							fprintf(file,"X%d",MAP(lts->dest[j])+1);
							if (j < lts->begin[t1+1]-1 || lts->begin[t1+1]-lts->begin[t1]<=1) {
								fprintf(file,"%c",c);
								if (labelset[l].op != UNDEF && lts->begin[t1+1]-lts->begin[t1] <=1) fprintf(file,"X%d",MAP(lts->dest[j])+1);
							}
						}
						fprintf(file,"\n");
						t2++;
					}
				}
			}break;
		case LTS_BLOCK_INV:
			fprintf(file,"des(%ld,%ld,%d)\n",MAP(lts->root),lts->transitions,lts->states);
			for(i=0;i<lts->states;i++){
				for(j=lts->begin[i];j<lts->begin[i+1];j++){
					fprintf(file,"(%d,%s,%d)\n",MAP(lts->src[j]),lts->label_string[lts->label[j]],MAP(i));
				}
			}
			break;
		default:
			lts_set_type(lts,LTS_LIST);
			writebes(file,lts,oblivious);
			break;
		}
	}
}


