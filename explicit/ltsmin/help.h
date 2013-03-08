/* $Id$ */
	{"",OPT_NORMAL,NULL,NULL,NULL,	"The file format of input and output is determined from the extension:"},
   {"",OPT_NORMAL,NULL,NULL,NULL,	"       format    extension"},
#ifdef USE_SVC
	{"",OPT_NORMAL,NULL,NULL,NULL,	"       SVC I     .svc   state information is discarded"},
#else
	{"",OPT_NORMAL,NULL,NULL,NULL,	"       SVC I     .svc   not available in this installation"},
#endif
#ifdef USE_BCG
	{"",OPT_NORMAL,NULL,NULL,NULL,	"       BCG       .BCG"},
#else
	{"",OPT_NORMAL,NULL,NULL,NULL,	"       BCG       .BCG   not available in this installation"},
#endif
	{"",OPT_NORMAL,NULL,NULL,NULL,	"       Aldebaran .aut"},
	{"",OPT_NORMAL,NULL,NULL,NULL,	"       dir       .dir   prototype for SVC II, focussing on distributed tools"},
	{"",OPT_NORMAL,NULL,NULL,NULL,	"       FSM       .fsm   write support only; no state information"},
	{"",OPT_NORMAL,NULL,NULL,NULL,	"       FC2       .fc2   write support only"},
   {"",OPT_NORMAL,NULL,NULL,NULL,"common options:"},
	{"-v",OPT_NORMAL,inc_int,&verbosity,NULL,"increase the level of verbosity"},
	{"-q",OPT_NORMAL,reset_int,&verbosity,NULL,"be silent"},
	{"-help",OPT_NORMAL,usage,NULL,NULL,"print this help message"},
	{"-o",OPT_REQ_ARG,assign_string,&outputname,"-o <file>","redirect output to <file>"},	
