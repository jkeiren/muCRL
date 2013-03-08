/* $Id: main.c,v 1.3 2005/04/13 15:48:57 amathijs Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#define MAIN
#include "tmcrl.h"

int to_file=0;
int to_toolbusfile=0;
int to_stdout=0;
int new_generation=1;
int newtbf = 1;
int regular=0;
int regular2=0;
int cluster=0;
int nocluster=0;
int binary=0;
int oldstate=1;
int statenames=0;
int writemulti=0;

/* The writemulti variable can be set to 1 to indicate that
 * the init expression should not be evualated, but should be written
 * to file unevaluated. The result is multi LPO format.
 * The format is the similar to 2gen, but its process is a composition
 * of linear processes rather than a single linear process.
 *
 * Stefan Blom 6-2003
 */

int cid=0;

FILE *outfile;
FILE *toolbusfile;
FILE *infile;

#define P(msg)  fprintf(stderr,"%s\n",msg)

void usage(void)
{
 rg_error("Use mcrl -help for options",NULL);
}

void version(void)
{
  fprintf(stderr,"mcrl: Timed mCRL parser and LPO generator. Version %s\n", VERSION);
}

void help(void)
{
P("");
P("Timed mCRL parser and (untimed) LPO generator");
P("=============================================");
P("");
P("Usage: mcrl [options] [file]");
P("");
P("The following options can be used:");
P("-linear:   a human readable LPO of the input file is written to file.lin");
P("-tbfile:   an LPO of the input file in toolbus term format file is ");
P("           written to file.tbf");
P("-tbf:      has the same effect as -tbfile");
P("-stdout:   an LPO in toolbus term format is generated, and written");
P("           to stdout");
P("-regular:  it is assumed that the input file is regular, and the");
P("           output LPO will be generated in regular form");
P("-regular2: a variant of regular where much more datavariables are");
P("           being used. Regular2 is sometimes successful where");
P("           the use of -regular leads to non termination of this tool");
P("-cluster:  all actions in the output are clustered ");
P("-nocluster:no actions are clustered, not even in intermediate LPOs");
P("-binary:   use binary, instead of n-ary, case functions when clustering.");
P("           In the presence of -newstate, state variables use binary encoding.");
P("-1gen:     with -stdout or -tbfile. This generates a .tbf file in the format");
P("           which can be read by the mcrl toolset release 1. This flag is only");
P("           available for backwards compatibility and its use is discouraged.");
P("-2gen:     with -stdout or -tbfile. This generates a .tbf file where");
P("           all objectnames are unique, by extending names with \"..#tag\", ");
P("           and terms and lists are in aterm format. -2gen is used by default.");
P("-multi     Write the term before the final composition of LPOs");
P("-newstate: mcrl will encode state variables using enumerated types.");
P("           -newstate is only allowed in the presence of -regular or -regular2.");
P("           Using the flag -binary in addition will lead mcrl to encode");
P("           the state by a vector of boolean variables.");
P("           By default (i.e. without -newstate), the functions");
P("           one, x2p1 and x2p0 will be used.");
P("-statenames: mcrl will use meaningful names for the state variables,");
P("           derived from the specification.");
P("-help:     yields this message");
P("-version:  get a version of the lineariser");
P("");
P("Except with the options help and version, a filename containing");
P("a timed mCRL description must be given. This program checks the syntax");
P("and the static semantics of a timed mCRL specification, and with ");
P("proper flags can transform a subclass of untimed mCRL specifications");
P("to linear process operators (LPOs)");
}

static ATbool ExtensionAdded(char *filename, char *suffix) {
     char *lastdot = strrchr(filename,'.');
     if (!lastdot || strcmp(lastdot, suffix)) {
          strcat(filename, suffix);
          return ATtrue;
          }
     return ATfalse;
     }

/*--- main program -----------------------------*/

static int main2(int argc, char *argv[],ATerm *stack_bottom)
{ 
  int i = 1;
  char *sname = NULL, *oname = NULL;
  specificationbasictype *spec;
  char messagebuffer[1024]="Internal error. Too bad <-:";
  int initial_process=0;
  ATerm result=NULL;
  char fname[1024], iname[1024];
  /* char *tool_name = "tmcrl";
  int ToolBus = 1; */
  
  fname[0]='\0';
  to_file=0;
  to_toolbusfile=0;
  to_stdout=0;
  for(i = 1; i < argc; i++){
    if(streq(argv[i], "-version")){
      version(); exit(0);
    } else if(streq(argv[i], "-help")){
      help(); exit(0);
    } else if(streq(argv[i], "-linear")){
      if (to_toolbusfile==1)
         rg_error("Options -tbfile and -linear cannot be used together",NULL);
      if (to_stdout==1)
         rg_error("Options -stdout and -linear cannot be used together",NULL);
      to_file=1;
    } else if (streq(argv[i], "-tbfile") || streq(argv[i], "-tbf")){
      if (to_file==1)
         rg_error("Options -tbfile and -linear cannot be used together",NULL);
      if (to_stdout==1)
         rg_error("Options -tbfile and -stdout cannot be used together",NULL);
      to_toolbusfile=1;
    } else if(streq(argv[i], "-stdout")){
      if (to_file==1)
         rg_error("Options -stdout and -linear cannot be used together",NULL);
      /* if (to_stdout==1)
         rg_error("Options -stdout and -tbfile cannot be used together",NULL);
      */
      to_toolbusfile=0;
      to_stdout=1;
    } else if(streq(argv[i], "-regular")){
      regular=1;
    } else if(streq(argv[i], "-regular2")){
      regular2=1;
      regular=1;
    } else if(streq(argv[i], "-cluster")){
      cluster=1;
      binary=1;
      fprintf(stderr,"mcrl: -cluster also sets -binary\n");
    } else if(streq(argv[i], "-1gen")){
      new_generation=0;
    } else if(streq(argv[i], "-2gen")){
      new_generation=1; newtbf = 0;
    } else if(streq(argv[i], "-nocluster")){
      nocluster=1;
     } else if(streq(argv[i], "-binary")){
      binary=1;
     } else if(streq(argv[i], "-newstate")){
      oldstate=0;
     } else if(streq(argv[i], "-statenames")){
      statenames=1;
     } else if(streq(argv[i], "-multi")){
      writemulti=1;
    } else if(streq(argv[i], "-at-termtable")){
      i++;
    } else if(streq(argv[i], "-at-symboltable")){
      i++;
    } else if((argv[i][0]=='-') && (argv[i][1]=='a') && (argv[i][2]=='t')){ 

    } else if(argv[i][0]=='-'){
      fprintf(stderr,"Unknown option %s ignored\n",argv[i]);
    } else {
      char *lastdot = NULL;
      sname = argv[i];
      strcpy(fname, sname);
      oname = fname;
      if ((strlen(fname)>3) && (strrchr(fname,'/')!=NULL))
         oname = strrchr(oname,'/')+1;
      lastdot = strrchr(oname,'.');
      if (lastdot && !strcmp(lastdot,".mcrl")) *lastdot = '\0';   
      break; 
    } 
  }
  if (to_stdout==0 && to_file==0 &&
     (regular || nocluster || cluster || binary || !oldstate)) 
      to_toolbusfile=1; 
  if (!oldstate && !regular && !regular2)
    rg_error("Option -newstate can only be used with -regular or -regular2",NULL);

  ATinit(argc,argv,stack_bottom);
  ATprotect(&result);
  if (((argc < 2)||(sname==NULL)))
      usage();
  initialize_data();
  /* fprintf(stderr,"NAME TO LINEARISE: %s\n",sname); */
  /* probe whether input file exists */
  strcpy(iname, sname);
  infile=fopen(iname,"r");
  if (infile==NULL) { 
     if (ExtensionAdded(iname, ".mcrl")) {
           infile=fopen(iname,"r");
          /* fprintf(stderr,"%s: ", iname);*/
          }
     }
  if (infile==NULL)
	rg_error ("Cannot open file for input", NULL);
  fclose(infile);
  if (to_file)
   { sprintf(messagebuffer,"%s.lin",oname);
     outfile=fopen(messagebuffer,"w");
     if (outfile==NULL)
        rg_error("Cannot open file for output",NULL); }
  if (to_toolbusfile)
   { sprintf(messagebuffer,"%s.tbf",oname);
     toolbusfile=fopen(messagebuffer,"w");
     if (toolbusfile==NULL)
        rg_error("Cannot open file for output",NULL); }
    spec=parse_script(iname,messagebuffer); /* if this terminates ok,  */
    if (spec==NULL)
     { rg_error(messagebuffer,NULL);
     }
    else if (!ssc(spec,messagebuffer))
       { rg_error(messagebuffer,NULL); }
    else 
     { initial_process=sscproc(spec,messagebuffer);
       if ((initial_process<=0)&&((to_file)||(to_toolbusfile)||(to_stdout)))
        { if (initial_process==-1)
             sprintf(messagebuffer,"There is no initial process");
          rg_error(messagebuffer,NULL);
        }
       else
       if ((initial_process==0)&&(!to_file)&&(!to_toolbusfile)&&(!to_stdout))
        { rg_error(messagebuffer,NULL);
        }
       else 
        { if ((to_file)||(to_toolbusfile)||(to_stdout))
           { result=transform(initial_process,spec,messagebuffer,(writemulti?1:0));
             if (result==NULL)
             {  rg_error(messagebuffer,NULL); }
             else if (to_file)
                   { printLPO(outfile,result); }
             else if (to_toolbusfile)
                  { if (new_generation||writemulti)
                     { ATwriteToSAFFile(ATmake(
			writemulti?"spec2genM(d(s(<term>,<term>,<term>),<term>),<term>)":
                        "spec2gen(d(s(<term>,<term>,<term>),<term>),<term>)",
                         translate_sorts_2gen(spec->sorts),
                         translate_funcs_2gen(spec->funcs),
                         translate_funcs_2gen(spec->maps),
                         translate_eqns_2gen(spec->eqns),
                         translate_lpo_2gen(result)),
                         toolbusfile);
                     }
                    else
                     { ATwriteToSAFFile(ATmake(
                        "spec(d(s(<term>,<term>,<term>),<term>),<term>)",
                         spec->sorts,spec->funcs,spec->maps,spec->eqns,result),
                         toolbusfile);
                     }
                  }
             else if (to_stdout)
                  { if (new_generation||writemulti)
                     { 
                       ATwriteToSAFFile(ATmake( 
			writemulti?"spec2genM(d(s(<term>,<term>,<term>),<term>),<term>)":
                        "spec2gen(d(s(<term>,<term>,<term>),<term>),<term>)",
                         translate_sorts_2gen(spec->sorts),
                         translate_funcs_2gen(spec->funcs),
                         translate_funcs_2gen(spec->maps),
                         translate_eqns_2gen(spec->eqns),
                         translate_lpo_2gen(result)),
                         stdout);
                     }
                    else
                     { ATwriteToSAFFile(ATmake(
                      "spec(d(s(<term>,<term>,<term>),<term>),<term>)",
                       spec->sorts,spec->funcs,spec->maps,spec->eqns,result),
                       stdout);
                     }
                  }
           }
          else 
           { fprintf(stdout,"The file %s contains correct (timed) mCRL\n",sname);
           }
        }
       
   }  
  return 0;
}

int main(int argc, char *argv[])
{
  ATerm stack_bottom;
  return main2(argc,argv,&stack_bottom);
}

