
/* $Id: liblts.c,v 1.3 2004/12/16 15:28:24 uid523 Exp $ */

#include <string.h>
#include "step.h"
#include "lts.h"

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#define NREC 10000

#ifdef INSTRUMENTED
static hits = 0, countToTree = 0;
#endif
                    
static char *version = "#version_1.0";

static int nPars, nPars2;
static ATermIndexedSet db = NULL;
static LTScallback currentLTScallback;

static ATerm *src = NULL, *dest = NULL, *src_pt = NULL, *dest_pt =NULL, 
       label;
static int src_code, dest_code;

static ATbool use_hints=ATtrue;
static ST_ORDER order = enumOccurrenceOrdering;


#define INITSIZE 10000

static int *Enlarge(int *smd, int newsize) {
    static int size = 0;
    if (newsize == 0) size = newsize = INITSIZE;
    if (newsize < size) return smd;
    while (size<=newsize) size *= 2;
    return (int*) realloc(smd, size*sizeof(int));
    }
    
static void Fold() {
    int i;
    if(use_hints) {
#ifdef INSTRUMENTED
	countToTree+=nPars-1; 
#endif
	for (i=nPars-1;i>=1;i--) {
		if(src[i+i]== dest[i+i] && src[i+i+1]==dest[i+i+1]) {
#ifdef INSTRUMENTED
			hits++;
#endif
			dest[i]=src[i];
		} else {
	dest[i]=(ATerm) ATmakeAppl2(MCRLsym_pair, dest[i+i], dest[i+i+1]);
		}
	}

    } else {
	for (i=nPars-1;i>=1;i--) {
		dest[i]=(ATerm) ATmakeAppl2(MCRLsym_pair, dest[i+i], dest[i+i+1]);
	}
    } 
}


static void Unfold() {
	int i;
	for(i=1;i<nPars;i++){
		src[i+i]=ATgetArgument(src[i],0);
		src[i+i+1]=ATgetArgument(src[i],1);
	}
}
 
int LTSgetInitialState(void) {return 0;}

static void STcallBack(void) {
    ATbool new;
    static int size = 0;
    Fold();
    dest_code=ATindexedSetPut(db, dest[1], &new);
    currentLTScallback(src_code, label, dest_code);
    }


void LTShelp(void) {
    }




void LTSsetArguments(int *argc, char ***argv) {
     int i, j=0;
     ATerm confluent=NULL;
     char **newargv = (char**) calloc(*argc + 1, sizeof(char*));
     if (!newargv) ATerror("Cannot allocate array argv"); 
     newargv[j++] = (*argv)[0];
     for(i=1;i<*argc;i++){
	if (!strcmp((*argv)[i],"-lts-hints-enable")) {
		use_hints=ATtrue;
		continue;

	}
	if (!strcmp((*argv)[i],"-lts-hints-disable")) {
		use_hints=ATfalse;
		continue;
	}        
        newargv[j++] = (*argv)[i];
     }
     *argc = j;  *argv = newargv;
     STsetArguments(argc, argv);
}


void LTSinitialize(LTScallback callback) {
     ATbool new;
     nPars = MCRLgetNumberOfPars();  nPars2 = 2 * nPars;
     currentLTScallback = callback;
     if (src) {
          ATunprotect(src); ATunprotect(dest); ATunprotect(&label);
	  free(src); free(dest);
     }
     if (!(src = calloc(nPars2, sizeof(ATerm)))) 
         {ATerror("Cannot allocate src (%d bytes)",nPars2*sizeof(ATerm));
         exit(1);}
     if (!(dest = calloc(nPars2, sizeof(ATerm)))) 
         {ATerror("Cannot allocate dest (%d bytes)",nPars2*sizeof(ATerm));
         exit(1);}
     ATprotectArray(src, nPars2); ATprotectArray(dest, nPars2);
     label=(ATerm)0;
     ATprotect(&label);
     src_pt = src + nPars; dest_pt = dest + nPars;
     if (db) ATindexedSetReset(db); 
        else
     db = ATindexedSetCreate(NREC, 95); 
     STinitialize(order, &label, dest_pt, STcallBack);
     STsetInitialState();
     Fold();
     ATindexedSetPut(db, dest[1] , &new);
}
    
ATerm LTSgetState(int state) {
    ATermList r = ATmakeList0();
    int i;
    src[1] =  ATindexedSetGetElem(db, state);
    Unfold();
    for (i=nPars2-1;i>=nPars;i--) r = ATinsert(r, src[i]);
    return (ATerm) r;
    }

ATerm LTSgetPrintState(int state) {
       ATerm s = LTSgetState(state);
       if (ATgetType(s)==AT_LIST)
	   return (ATerm) MCRLprintList((ATermList) s);
       return MCRLterm_terminated;
} 
        
int LTSstep(int state) {
    src_code = state;
    src[1]=ATindexedSetGetElem(db, state);
    Unfold();
    return STstep(src_pt);
    }

void LTSfinish(int explored) {
    if (STgetNumberOfSummands()>0) /* optimize is on */
    ATwarning("Average number of summands: %.2f", 
         STgetNumberOfSummands()/explored);
    }
    
int LTSgetSmdIndex(void) {
    return STgetSmdIndex();
    }
    
int LTSnumberOfUsedSummands(void) {
    return STnumberOfUsedSummands();
}

ATermList  LTSgetUsedSummands(void) {
    return STgetUsedSummands();
    }

int LTSgetStateNo(ATermList statevector) {
    ATbool new;
    int i;
    for (i=nPars;i<nPars2;i++, statevector = ATgetNext(statevector)) 
         dest[i] = ATgetFirst(statevector);
    Fold();
    {
    int code = ATindexedSetPut(db, dest[1], &new);
    return code;
    }
    }
        
ATermList LTSgetTrace(char *filename, int *current) {
    FILE *f; 
    ATerm action;
    char version[50];
    int npars;
    ATermList statevector, transitions, r = ATempty;
    int stateno;
    if (!(f=fopen(filename,"r"))) {
         perror(filename); return NULL;
         }
    fscanf(f, "%d %s", &npars, version);
    
    /* ATfprintf(stdout, "QQ npars = %d version = %s %d\n", npars, version, 
        *current); */ 
    if (npars != nPars) {
    ATwarning(
    "Number of parameters read from %s: %d != %d: found number of parameters", 
         filename, npars, nPars);
         return NULL;
         }
    transitions = MCRLparseTrace(f, current);
    if (!transitions) return NULL;
    for (;!ATisEmpty(transitions);transitions = ATgetTail(transitions, nPars)) {
       ATerm action = ATgetFirst(transitions);
       transitions = ATgetNext(transitions);
       stateno = LTSgetStateNo(transitions);
       if (stateno<0) {
           ATwarning("Illegal statevector read from %s", filename);
           return NULL;
           }
       r = ATinsert(r, ATmake("t(<term>,<term>)", action, 
              ATmakeInt(stateno)));
       }
    fclose(f);
    return ATreverse(r);
    }

ATbool LTSsaveTrace(char *filename, ATermList transitions, int current) {
    ATermList r = ATempty;
    FILE *f;
    if (!(f=fopen(filename,"w"))) {
         perror(filename); return ATfalse;
         }
    fprintf(f,"%d %s\n", MCRLgetNumberOfPars(), version);
    for (;!ATisEmpty(transitions);transitions = ATgetNext(transitions)) {
       ATermAppl transition = (ATermAppl) ATgetFirst(transitions);
       ATerm action = ATgetArgument(transition, 0);
       ATermList statevector = MCRLprintList((ATermList) 
       LTSgetState(ATgetInt((ATermInt) ATgetArgument(transition, 1))));
       fprintf(f,"%s", ATgetName(ATgetAFun((ATermAppl) action))); 
       /* fprintf(stdout, "%s\n", ATgetName(ATgetAFun((ATermAppl) action))); */ 
       for (;!ATisEmpty(statevector);statevector=ATgetNext(statevector))
           ATfprintf(f," %t", ATgetFirst(statevector));
       ATfprintf(f,"\n");
       }
    fprintf(f, "%d\n", current);
    fclose(f);  
    return ATtrue;
    }
    
char *LTSgetVersion() {return version;} 
      
#ifdef INSTRUMENTED
void LTSreport(void) {
    ATwarning("#calls ToTree %d  #hits %d", countToTree, hits);
}
#endif
