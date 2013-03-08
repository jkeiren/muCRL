
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdio.h>
#include "rw.h"

#define P(msg)  fprintf(stderr,"%s\n",msg)

static char *who = "mCRL composer";

static void WarningHandler(const char *format, va_list args)
     {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }
     
static void ErrorHandler(const char *format, va_list args)
     {
     fprintf(stderr,"%s: ", who);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     exit(-1);
     }

static void helpmsg(void) 
    {
    P("Usage: composer <multi LPO> <LPO> <annotated LPO>");
    P("this tool takes a multi LPO and delivers both a single LPO");
    P("and an annotated LPO used for origin tracking");
    }

static void help(void)
    {
    P("");
    helpmsg();
    P("");
    }

#undef P

static ATerm adt=NULL;
static ATerm spec=NULL;
static ATerm lpo=NULL;
static ATerm ann_lpo=NULL;
static ATerm ann_extra=NULL;

int main(int argc, char *argv[]) {
    int i, j = 0;
    char **newargv = (char**) calloc(argc + 2, sizeof(char*));
    ATsetWarningHandler(WarningHandler);
    ATsetErrorHandler(ErrorHandler);
    if (!newargv) ATerror("Cannot allocate array argv");  
    newargv[j++] = argv[0]; //newargv[j++] = "-no-extra-rules";
    ATinit(argc, argv, (ATerm*) &argc);
    for (i=1;i<argc;i++) {
    if (!strcmp(argv[i],"-help")) {
	help();
	exit(0);
	}
    newargv[j++] = argv[i];
    }
	argc=j;
	RWsetArguments(&argc, &newargv);
	ATprotect(&adt);
	ATprotect(&spec);
	ATprotect(&lpo);
	ATprotect(&ann_lpo);
	ATprotect(&ann_extra);
	ATwarning("attempt to read from %s",newargv[1]);
	spec=ATreadFromNamedFile(newargv[1]);
	if(!ATmatch(spec,"spec2genM(<term>,<term>)",&adt,&lpo)){
		ATerror("bad input");
	}
	ATwarning("init MCRL");
	MCRLinitializeAdt(adt);
	ATwarning("init RW");
	RWinitialize(adt);
	ATwarning("converting to internal format (TODO)");
	ATwarning("lpo is %t",lpo);

	ATwarning("composing final process (TODO)");

	ATwarning("filtering 2gen LPO and annotated LPO (TODO)");

	lpo=ATmake("initprocspec([],[],[])");
	ann_lpo=lpo;
	ann_extra=ATmake("[]");

	ATwarning("attempt to write LPO to %s",newargv[2]);
	ATwriteToNamedBinaryFile(
		ATmake("spec2gen(<term>,<term>)",adt,lpo),
		newargv[2]);
	ATwarning("attempt to write annotated LPO to %s",newargv[3]);
	ATwriteToNamedBinaryFile(
		ATmake("spec2genA(<term>,<term>,<term>)",adt,ann_lpo,ann_extra),
		newargv[3]);

	return 0;
    }
