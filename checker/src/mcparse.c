#define  NAME      "mcparse"
#define  LVERSION  "1.0.9"
#define  AUTHOR    "Aad Mathijssen"

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <limits.h>
#include <getopt.h>
#include <stdbool.h>

#ifdef __cplusplus
}
#endif

#include "aterm2.h"
#include "mcrl.h"
#include "config.h"
#include "mcparse.h"
#include "mcfunc.h"
#include "libmcparse.h"

//local declarations

int main(int argc, char *argv[]);
//main function where:
//  argc represents the number of arguments
//  argv represents the arguments

void printUsage(FILE* stream);
//print usage information to stream

void printVersion(FILE* stream);
//print version information to stream

bool parseModalFormulaFileName(
  char *formFileName,
  char *outFileName,
  char *translateFilename,
  bool reduce,
  int acLevel,
  int vbLevel,
  bool noSave);
/*Pre: formFileName is the name of a valid formula file from which can be read
       outFileName is the name of a valid file to which can be written, or NULL
       translateFileName is the name of a valid ATerm file from which can be
       read, or NULL
       0 <= acLevel <= 2, 0 <= vbLevel <= 3
  Post:the modal formula in formFileName is parsed and saved to outFileName
       If outFileName is NULL, stdout is used.
       If reduce, all regular operations are replaced by equivalent non-regular
       operations.
       Alpha conversion is applied based on the value of acLevel.
       The display of messages is controlled by the value of vbLevel.
       If noSave, the parsed formula is not saved.
       If translateFileName is not NULL, the types of expressions occurring in
       the modal formula are checked and the formula is translated to the
       internal mCRL format, using the data specification in translateFileName
  Ret: true, if everything went ok.
       false, otherwise; appropriate error messages have been shown.
*/ 

bool parseModalFormulaStream(
  FILE *formStream,
  FILE *outStream,
  bool reduce,
  int acLevel,
  int vbLevel,
  bool saveToMCRLFormat,
  bool noSave);
/*Pre: formStream is a valid formula stream from which can be read
       outStream is the name of a valid stream to which can be written
       0 <= acLevel <= 2, 0 <= vbLevel <= 3
       if saveToMCRLFormat, an mCRL data specification is present in the mCRL
       library
  Post:the modal formula in formStream is parsed and saved to outStream
       If reduce, all regular operations are replaced by equivalent non-regular
       operations.
       Alpha conversion is applied based on the value of acLevel.
       The display of messages is controlled by the value of vbLevel.
       If saveToMCRLFormat, the types of expressions occurring in the modal
       formula are checked and the formula is translated to the internal mCRL
       format, using the data specification that is present in the mCRL library.
       If noSave, the parsed formula is not saved.
  Ret: true, if everything went ok.
       false, otherwise; appropriate error messages have been shown.
*/ 

//implementation

int main(int argc, char* argv[]) {
  int   result                 = 0;
  //declarations for parsing the modal formula
  char  *formFileName      = NULL;
  char  *outputFileName    = NULL;
  char  *translateFileName = NULL;
  bool  reduce            = false;
  int acLevel              = 0;
  int vbLevel              = 1;
  bool  noSave            = false;
  bool  moreInfo          = false;
  //declarations for getopt  
  #define shortOptions      "rsfqvdnt:"
  #define helpOption        CHAR_MAX + 1
  #define versionOption     helpOption + 1
  #define testOption        versionOption + 1
  struct option longOptions[] = { 
    {"help"      , no_argument,       NULL, helpOption},
    {"version"   , no_argument,       NULL, versionOption},
    {"test"      , no_argument,       NULL, testOption},
    {"reduce"    , no_argument,       NULL, 'r'},
    {"scope-ac"  , no_argument,       NULL, 's'},
    {"full-ac"   , no_argument,       NULL, 'f'},    
    {"quiet"     , no_argument,       NULL, 'q'},
    {"verbose"   , no_argument,       NULL, 'v'},
    {"debug"     , no_argument,       NULL, 'd'},
    {"no-save"   , no_argument,       NULL, 'n'},
    {"translate" , required_argument, NULL, 't'},
    {0, 0, 0, 0}
  };
  int option;
  //parse options
  option = getopt_long(argc, argv, shortOptions, longOptions, NULL);
  while (option != -1) {
    switch (option) {
      case helpOption: 
        printUsage(stdout);
        throwV(0); 
        break;
      case versionOption: 
        printVersion(stdout); 
        throwV(0);
        break;
      case testOption: 
        MCtest();
        throwV(0);
        break;
      case 'r': 
        reduce = true;
        break;
      case 's': 
        acLevel = 1;
        break;
      case 'f': 
        acLevel = 2;
        break;
      case 'q': 
        vbLevel = 0;
        break;
      case 'v': 
        vbLevel = 2;
        break;
      case 'd': 
        vbLevel = 3;
        break;
      case 'n': 
        noSave = true;
        break;
      case 't': 
        translateFileName = strdup(optarg);
        break;
      default:
      	moreInfo = true;
      	throwV(1);
        break;
    }
    option = getopt_long(argc, argv, shortOptions, longOptions, NULL);
  }
  int noargc; //non-option argument count
  noargc = argc - optind;
  if (noargc <= 0) {
    moreInfo = true;
    throwVM1(1,"%s: too few arguments\n", NAME);
  } else if (noargc > 2) {
    moreInfo = true;
    throwVM1(1,"%s: too many arguments\n", NAME);
  } else {
    //noargc > 0 && noargc <= 2
    formFileName = strdup(argv[optind]);
    if (noargc == 2) {
      outputFileName = strdup(argv[optind + 1]);
    }
  }
  //initialise ATerm library
  ATerm stackBottom;
  ATinit(0, NULL, &stackBottom);
  //parse modal formula  
  if (!parseModalFormulaFileName(formFileName, outputFileName,
    translateFileName, reduce, acLevel, vbLevel, noSave))
  {
    throwV(1);  
  }       
finally:
  if (moreInfo) {
    fprintf(stderr, "Try \'%s --help\' for more information.\n", NAME);
  }
  free(translateFileName);
  free(formFileName);
  free(outputFileName);
  if (vbLevel == 3) {
    printf("(main): all objects are freed; return %d.\n", result);
  }
  return result;
}

bool parseModalFormulaFileName(char *formFileName, char *outputFileName,
  char *translateFileName, bool reduce, int acLevel, int vbLevel, bool noSave)
{
  bool result          = true;
  FILE *formStream      = NULL;
  FILE *outputStream    = NULL;
  if (formFileName == NULL) {
    throwVM0(false, "error: formula file may not be NULL\n");
  }
  //open formula file for reading
  formStream = fopen(formFileName, "r");
  if (formStream == NULL) {
    throwVM2(false, "error: could not open formula file '%s' for reading (error %d)\n", 
      formFileName, errno);
  }
  if (vbLevel == 3) {  
    printf("formula file %s is opened for reading.\n", formFileName);
  }
  //initialize the mCRL library with the specification in typeCheckFileName
  bool saveToMCRLFormat = (translateFileName != NULL);
  if (saveToMCRLFormat) {
    if (MCRLinitNamedFile(translateFileName) == ATfalse) {
      throwVM0(false, "\nerror: could not initialise the mCRL library\n");
    }
  }
  //open output file for writing or set to stdout
  if (outputFileName == NULL) {
    outputStream = stdout;
    if (vbLevel == 3) {
      printf("output to stdout.\n");
    }
  } else {  
    outputStream = fopen(outputFileName, "w");
    if (!outputStream) {
      throwVM2(false, "error: could not open output file '%s' for writing (error %d)\n", 
        outputFileName, errno);
    }
    if (vbLevel == 3) {
      printf("output file %s is opened for writing.\n", outputFileName);
    }
  }
  if (!parseModalFormulaStream(formStream, outputStream, reduce, acLevel,
    vbLevel, saveToMCRLFormat, noSave))
  {
    throwV(false);
  }
finally:
  if (formStream != NULL) {
    fclose(formStream);
  }
  if (outputStream != NULL && outputStream != stdout) {
    fclose(outputStream);
  }
  if (vbLevel == 3) {
    printf("(parseModalFormulaFileName): all files are closed; return %s\n",
      result?"true":"false");
  }
  return result;
}

bool parseModalFormulaStream(FILE *formStream, FILE *outputStream, 
  bool reduce, int acLevel, int vbLevel, bool saveToMCRLFormat, bool noSave)
{
  bool result;
  ATermAppl form = NULL;
  //check preconditions
  if (formStream == NULL) {
    throwVM0(false, "error: formula stream may not be empty\n");
  }
  if (outputStream == NULL) {
    throwVM0(false, "error: output stream may not be empty\n");
  }
  //parse modal formula and save it to form
  form = MCparseModalFormula(
    formStream, reduce, acLevel, vbLevel, saveToMCRLFormat);
  if (form != NULL) {
    if (noSave) {
      if (vbLevel > 1) {
        printf("do not save formula\n");
      }
    } else {
      if (vbLevel > 1 && outputStream != stdout) {
        printf("saving formula to file\n");
      }
      ATwriteToTextFile((ATerm) form, outputStream);
      fprintf(outputStream, "\n");
    }
    result = true;
  } else {
    result = false;
  }
finally:
  if (vbLevel == 3) {
    printf("(parseModalFormulaStream): all files are closed; return %s\n",
      result?"true":"false");
  }
  return result;
}

void printUsage(FILE *stream) {
  fprintf(stream, 
    "Usage: %s OPTIONS FORMFILE [OUTFILE]\n"
    "Translate the extended modal formula in FORMFILE to the ATerm format and\n"
    "save it to OUTFILE. If OUTFILE is not present, stdout is used.\n"
    "\n"
    "The OPTIONS that can be used are:\n"
    "    --help               display this help\n"
    "    --version            display version information\n"
    "    --test               execute test function (will be removed)\n"
    "-r, --reduce             replace all regular operations by equivalent non-\n"
    "                         regular operations\n"
    "-s, --scope-ac           rename bound variables such that all names are unique\n"
    "                         wrt each other, if they are in each other's scope\n"
    "-f, --full-ac            rename bound variables such that all names are unique\n"
    "                         wrt each other\n"
    "-q, --quiet              do not display warning messages\n"
    "-v, --verbose            turn on the display of short intermediate messages\n"
    "-d, --debug              turn on the display of detailed intermediate messages\n"
    "-n, --no-save            do not save the parsed formula\n"
    "-t, --translate ADTFILE  the formula is translated to the mCRL format using the\n"
    "                         data specification in ADTFILE\n",
    NAME
  );
}

void printVersion(FILE *stream) {
  #ifdef VERSION
  fprintf(stream, "%s %s (mCRL distribution %s)\nWritten by %s.\n", 
    NAME, LVERSION, VERSION, AUTHOR);
  #else
  fprintf(stream, "%s %s\nWritten by %s.\n", 
    NAME, LVERSION, AUTHOR);  
  #endif
}
