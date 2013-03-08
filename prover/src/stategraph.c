/* $Id: stategraph.c,v 1.3 2008/09/26 19:33:23 vdpol Exp $ */

#include <stdio.h>
#include "mcrl.h"
#define MY_NAME "Stategraph"
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

FILE *Stategraph(int argc, char* argv[]);

static void help() {
  ATfprintf(stderr,"%s\n",
	    "Usage: stategraph [Options] [file.tbf]\n"
	    "       Reads LPO from file or stdin, writes LPO or DOT graph to stdout\n"
	    "\nEffect:\n"
	    "- eliminates dummy summands and parameters from LPO,\n"
	    "- or (with -show) visualizes the control flow.\n"
	    "\nWorking:\n"
            "- computes the control flow from LPO\n"
            "- applies control flow analysis to remove unreachable summands\n"
            "- correlates data parameters to control flow graphs\n"
            "- applies data flow analysis to eliminate dummy parameters\n"
            "- tries to guess better initial values\n"
            "\nHints:\n"
	    "- only useful after mcrl -nocluster -regular[2]\n"
            "- effect takes often place after additional constelm\n");
  ATfprintf(stderr,"%s\n","OPTIONS:");
  ATfprintf(stderr,"%s\n",
	    "-help           : "
	    "prints this message");
  ATfprintf(stderr,"%s\n",
	    "-verbose        : "
	    "prints some diagnostic information");
  ATfprintf(stderr,"%s\n",
	    "-version        : "
	    "prints the version number");
  ATfprintf(stderr,"%s\n",
	    "-show           : "
	    "generates graphs in dot format on stdout instead of result LPO");
  ATfprintf(stderr,"%s\n",
	    "-show-summands  : "
	    "additionally shows summand numbers in generated dot graphs");
#ifdef GRAPPA
  ATfprintf(stderr,"%s\n",
	    "-stateview      : "
	    "displays graphs and their interaction");
#endif
  ATfprintf(stderr,"%s\n",
	    "-test           : "
	    "generates a lot of test-output on stderr");
  ATfprintf(stderr,"%s\n",
	    "-minchange      : "
	    "dummies are kept unchanged instead of set to a constant\n"
            "                  (this may result in larger state space, but it is\n"
            "                   handy for proving invariants or symmetry)");
  ATfprintf(stderr,"%s\n",
	    "-invariant      : "
	    "generates a (rudimentary) invariant and outputs it to stdout\n"
	    "                  the invariant is a conjunction of\n"
            "                  implications (x0=v1 => x1=v2), where\n"
	    "                  xi are parameters and vi closed values.");
  ATfprintf(stderr,"%s\n",
	    "-constant       : "
	    "propagates constant assignments by means of an invariant");
  ATfprintf(stderr,"%s\n",
	    "Type stategraph -help-mcrl for general mcrl options");
}

static void version(void) {
  fprintf(stderr,"%s (version %s)\n",MY_NAME, VERSION);
}

static void WarningHandler(const char *format, va_list args) {
     fprintf(stderr,"%s: ", MY_NAME);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }

static void ErrorHandler(const char *format, va_list args) {
     fprintf(stderr,"%s: ", MY_NAME);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     exit(-1);
     }
     
int main(int argc, char *argv[]) {
     FILE *in;
     ATinit(argc,argv,(ATerm*) &argc);
     ATsetWarningHandler(WarningHandler);
     ATsetErrorHandler(ErrorHandler);
     if (argc>1) {
        if (!strcmp(argv[1],"-help")) {
          help(); exit(0);
          }
        if (!strcmp(argv[1],"-help-mcrl")) {
          help(); MCRLhelp(); exit(0);
          }
        if (!strcmp(argv[1],"-version")) {
          version(); exit(0);
          }
        }
     in = Stategraph(argc, argv);
     exit(0);
     }
