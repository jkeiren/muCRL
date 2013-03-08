/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton implementation for Bison's Yacc-like parsers in C

   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor,
   Boston, MA 02110-1301, USA.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.3"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Using locations.  */
#define YYLSP_NEEDED 0



/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     NAME = 258,
     SORT = 259,
     FUNC = 260,
     MAP = 261,
     VAR = 262,
     REW = 263,
     PROC = 264,
     ACT = 265,
     COMM = 266,
     INIT = 267,
     ARROW = 268,
     MERGE = 269,
     LEFTMERGE = 270,
     LEFTTRIANGLE = 271,
     RIGHTTRIANGLE = 272,
     BOUNDINIT = 273,
     DELTA = 274,
     TAU = 275,
     ENCAP = 276,
     HIDE = 277,
     RENAME = 278,
     SUM = 279
   };
#endif
/* Tokens.  */
#define NAME 258
#define SORT 259
#define FUNC 260
#define MAP 261
#define VAR 262
#define REW 263
#define PROC 264
#define ACT 265
#define COMM 266
#define INIT 267
#define ARROW 268
#define MERGE 269
#define LEFTMERGE 270
#define LEFTTRIANGLE 271
#define RIGHTTRIANGLE 272
#define BOUNDINIT 273
#define DELTA 274
#define TAU 275
#define ENCAP 276
#define HIDE 277
#define RENAME 278
#define SUM 279




/* Copy the first part of user declarations.  */
#line 2 "tmcrl.y"

#include "tmcrl.h"
/* #include "TB.h" we now use Pieter Olivier's ATerm library */

#define YYDEBUG 1
/* #define YYINITDEPTH 200000 */
#define YYMAXDEPTH 10000000


void yyerror(char *);
extern FILE *yyin;
int aux=0;                 /* auxiliary variable used for parsing */

int lino = 1;              /* line number in source file */
int pos = 0;               /* position in line */

/* sorts, funcs, maps and eqns have the structure outlined in
   Dams & Groote. The structure of the rest needs to be defined */

static specificationbasictype spec;
extern int to_toolbus;
extern int to_file;
extern FILE *outfile;
extern int time_operators_used;
char *error_message=NULL;
int error=0;

ATermIndexedSet PROTECT;
ATbool* b; 

/* below we declare some temporary stores to be used when parsing */
ATerm auxterm=NULL, auxterm1=NULL, auxterm2=NULL ;
char *auxstring=NULL, *auxstring1=NULL;
char messagebuffer[256];

static ATerm eme = NULL, ems = NULL;

void init_structures(void)
{ ATprotect(&(spec.sorts));
  ATprotect(&(spec.funcs));
  ATprotect(&(spec.maps));
  ATprotect(&(spec.acts));
  ATprotect(&(spec.comms));
  ATprotect(&(spec.procs));
  ATprotect(&(spec.init));
  ATprotect(&(spec.eqns));
  ATprotect(&auxterm);
  ATprotect(&auxterm1);
  ATprotect(&auxterm2);
  ATprotect(&eme);
  ATprotect(&ems);

  ems=spec.sorts=ATmake("ems");
  spec.funcs=ATmake("emf");
  spec.maps=ATmake("emf");
  eme = spec.eqns=ATmake("eme");
  spec.acts=ATmake("ema");; /* actions ins(<string>,sortlist,tail) */
  spec.comms=ATmake("emc");
  spec.procs=ATmake("emp");
  spec.init=NULL;
  
  PROTECT=ATindexedSetCreate(1024,75);
}

specificationbasictype *parse_script(char *name,char *err_mes)
{ int pres;

  lino = 1;
  pos = 0;
  error_message=err_mes;
  error=0;
  if((yyin = fopen(name, "r")) == NULL)\
    { sprintf(err_mes,"Cannot open file `%s'", name);
      return NULL; }
yyrestart (yyin);
init_structures ();
pres = yyparse ();		/* at last, the actual parse */
fclose (yyin);
if (error)
  return NULL;
return &spec;
}

static ATerm Traverse(ATerm t, ATerm *a) {
   *a = ATgetArgument((ATermAppl) t, 0);
   return ATgetArgument((ATermAppl) t, 1);
   } 

static ATerm Reverse(ATerm t, ATerm em) {
   ATermList as = ATempty; 
   ATerm a, r = em;
   while (!ATisEqual(t, em)) {
       t =  Traverse(t, &a);
       as = ATinsert(as, a);
       }
   for (as=ATreverse(as);!ATisEmpty(as);as=ATgetNext(as)) {
       r = ATmake("ins(<term>,<term>)", ATgetFirst(as), r);
       }
   return r;
   }

/*--- Yacc stack type --------------------------*/

typedef struct {
  char      *string;   /* appear on parse stack */
  ATerm      t;        /* place to store intermediate terms */

  int lino;            /* I do not see the use of these fields (JFG) */
  int pos;
  int elino;
  int epos;

  /* TBbool    bool;      
  tkind     tk;
  ATerm      ATerm;
  char      *id;
  term_list *term_list; */
} yystype;

/* every non-terminal yields its begin and end coordinates
 * as four tuple (lino, pos, elino, epos). The following macro's
 * expect:
 * - res  (in all cases $$ of the current rule)
 * - b, e (the rule element, e.g. $i, defining the desired values)
 */

#define range(res,b,e)  res.lino = b.lino; res.pos = b.pos;\
                      res.elino = e.elino; res.epos = e.epos;
#define empty_range(res) res.lino = res.elino = lino; res.pos = res.epos = pos;

#define YYSTYPE yystype   /* Yacc stack entries */



/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif

#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef int YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif



/* Copy the second part of user declarations.  */


/* Line 216 of yacc.c.  */
#line 288 "y.tab.c"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int i)
#else
static int
YYID (i)
    int i;
#endif
{
  return i;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef _STDLIB_H
#      define _STDLIB_H 1
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined _STDLIB_H \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef _STDLIB_H
#    define _STDLIB_H 1
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss;
  YYSTYPE yyvs;
  };

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack)					\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack, Stack, yysize);				\
	Stack = &yyptr->Stack;						\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  54
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   167

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  37
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  58
/* YYNRULES -- Number of rules.  */
#define YYNRULES  106
/* YYNRULES -- Number of states.  */
#define YYNSTATES  208

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   279

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    26,     2,     2,     2,     2,
      28,    29,     2,    31,    25,     2,    33,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    27,     2,
       2,    30,     2,     2,    36,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    34,    32,    35,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,     9,    11,    15,    17,    18,    23,
      25,    28,    29,    33,    34,    38,    39,    43,    45,    46,
      50,    52,    53,    57,    62,    63,    70,    75,    76,    83,
      86,    87,    88,    92,    94,    95,    99,   103,   105,   109,
     111,   116,   118,   122,   124,   129,   130,   134,   136,   137,
     141,   145,   147,   151,   153,   155,   157,   161,   165,   169,
     173,   177,   179,   185,   187,   191,   193,   197,   199,   201,
     210,   219,   228,   237,   239,   244,   248,   252,   256,   262,
     266,   272,   274,   277,   280,   284,   291,   293,   294,   298,
     299,   303,   305,   306,   311,   313,   316,   319,   325,   328,
     329,   332,   335,   338,   341,   344,   347
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      94,     0,    -1,     3,    -1,    38,    25,     3,    -1,     3,
      -1,    39,    25,     3,    -1,     3,    -1,    -1,     3,    26,
      41,    40,    -1,     3,    -1,    42,     3,    -1,    -1,     4,
      44,    42,    -1,    -1,     5,    46,    48,    -1,    -1,     6,
      47,    50,    -1,    52,    -1,    -1,    48,    49,    52,    -1,
      54,    -1,    -1,    50,    51,    54,    -1,    39,    27,    13,
       3,    -1,    -1,    39,    27,    53,    40,    13,     3,    -1,
      39,    27,    13,     3,    -1,    -1,    39,    27,    55,    40,
      13,     3,    -1,    57,    66,    -1,    -1,    -1,     7,    58,
      59,    -1,    61,    -1,    -1,    59,    60,    61,    -1,    39,
      27,     3,    -1,    63,    -1,    63,    25,    62,    -1,     3,
      -1,     3,    28,    62,    29,    -1,    65,    -1,    65,    25,
      64,    -1,     3,    -1,     3,    28,    64,    29,    -1,    -1,
       8,    67,    68,    -1,    70,    -1,    -1,    68,    69,    70,
      -1,    63,    30,    63,    -1,    72,    -1,    72,    31,    71,
      -1,    73,    -1,    74,    -1,    75,    -1,    75,    15,    75,
      -1,    75,    14,    73,    -1,    75,    14,    75,    -1,    75,
      32,    74,    -1,    75,    32,    75,    -1,    76,    -1,    76,
      16,    65,    17,    76,    -1,    77,    -1,    77,    18,    76,
      -1,    78,    -1,    78,    33,    77,    -1,    19,    -1,    20,
      -1,    21,    28,    34,    38,    35,    25,    71,    29,    -1,
      22,    28,    34,    38,    35,    25,    71,    29,    -1,    23,
      28,    34,    79,    35,    25,    71,    29,    -1,    24,    28,
       3,    27,     3,    25,    71,    29,    -1,     3,    -1,     3,
      28,    64,    29,    -1,    28,    71,    29,    -1,    78,    36,
      65,    -1,     3,    13,     3,    -1,    79,    25,     3,    13,
       3,    -1,     3,    27,     3,    -1,     3,    27,     3,    25,
      80,    -1,    83,    -1,    81,    83,    -1,     9,    81,    -1,
       3,    30,    71,    -1,     3,    28,    80,    29,    30,    71,
      -1,    88,    -1,    -1,    84,    85,    88,    -1,    -1,    10,
      87,    84,    -1,     3,    -1,    -1,    39,    27,    89,    40,
      -1,    92,    -1,    90,    92,    -1,    11,    90,    -1,     3,
      32,     3,    30,     3,    -1,    12,    71,    -1,    -1,    43,
      94,    -1,    45,    94,    -1,    56,    94,    -1,    86,    94,
      -1,    91,    94,    -1,    82,    94,    -1,    93,    94,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   165,   165,   168,   175,   179,   186,   191,   190,   199,
     202,   208,   207,   214,   213,   218,   217,   223,   225,   224,
     229,   231,   230,   235,   242,   241,   252,   259,   258,   269,
     276,   280,   279,   285,   288,   287,   300,   313,   318,   326,
     330,   337,   342,   350,   354,   362,   361,   368,   374,   373,
     383,   398,   400,   408,   410,   412,   414,   422,   428,   436,
     442,   450,   452,   462,   464,   473,   475,   483,   487,   491,
     497,   503,   509,   515,   519,   524,   526,   535,   539,   546,
     551,   559,   561,   565,   568,   573,   582,   584,   583,   589,
     588,   594,   598,   597,   607,   608,   611,   614,   619,   624,
     625,   626,   627,   628,   629,   630,   631
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "NAME", "SORT", "FUNC", "MAP", "VAR",
  "REW", "PROC", "ACT", "COMM", "INIT", "ARROW", "MERGE", "LEFTMERGE",
  "LEFTTRIANGLE", "RIGHTTRIANGLE", "BOUNDINIT", "DELTA", "TAU", "ENCAP",
  "HIDE", "RENAME", "SUM", "','", "'#'", "':'", "'('", "')'", "'='", "'+'",
  "'|'", "'.'", "'{'", "'}'", "'@'", "$accept", "no_print_name_list",
  "name_list", "x_name_list", "@1", "space_name_list",
  "sort_specification", "@2", "function_specification", "@3", "@4",
  "space_function_declaration_list", "@5", "space_map_declaration_list",
  "@6", "function_declaration", "@7", "map_declaration", "@8",
  "equation_specification", "variable_declaration", "@9",
  "space_variables_list", "@10", "variables", "data_term_list",
  "data_term", "data_term_list_proc", "data_term_proc", "equation_section",
  "@11", "space_single_equation_list", "@12", "single_equation",
  "process_expression", "parallel_expression", "merge_parallel_expression",
  "comm_parallel_expression", "cond_expression", "bounded_expression",
  "dot_expression", "basic_expression", "renaming_declaration_list",
  "single_variable_declaration_list", "space_process_declaration_list",
  "process_specification", "process_declaration",
  "space_action_declaration_list", "@13", "action_specification", "@14",
  "action_declaration", "@15", "space_communication_declaration_list",
  "communication_specification", "communication_declaration",
  "initial_declaration", "specification", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,    44,    35,    58,    40,    41,
      61,    43,   124,    46,   123,   125,    64
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    37,    38,    38,    39,    39,    40,    41,    40,    42,
      42,    44,    43,    46,    45,    47,    45,    48,    49,    48,
      50,    51,    50,    52,    53,    52,    54,    55,    54,    56,
      57,    58,    57,    59,    60,    59,    61,    62,    62,    63,
      63,    64,    64,    65,    65,    67,    66,    68,    69,    68,
      70,    71,    71,    72,    72,    72,    72,    73,    73,    74,
      74,    75,    75,    76,    76,    77,    77,    78,    78,    78,
      78,    78,    78,    78,    78,    78,    78,    79,    79,    80,
      80,    81,    81,    82,    83,    83,    84,    85,    84,    87,
      86,    88,    89,    88,    90,    90,    91,    92,    93,    94,
      94,    94,    94,    94,    94,    94,    94
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     3,     1,     3,     1,     0,     4,     1,
       2,     0,     3,     0,     3,     0,     3,     1,     0,     3,
       1,     0,     3,     4,     0,     6,     4,     0,     6,     2,
       0,     0,     3,     1,     0,     3,     3,     1,     3,     1,
       4,     1,     3,     1,     4,     0,     3,     1,     0,     3,
       3,     1,     3,     1,     1,     1,     3,     3,     3,     3,
       3,     1,     5,     1,     3,     1,     3,     1,     1,     8,
       8,     8,     8,     1,     4,     3,     3,     3,     5,     3,
       5,     1,     2,     2,     3,     6,     1,     0,     3,     0,
       3,     1,     0,     4,     1,     2,     2,     5,     2,     0,
       2,     2,     2,     2,     2,     2,     2
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
      30,    11,    13,    15,    31,     0,    89,     0,     0,    30,
      30,    30,     0,    30,    30,    30,    30,     0,     0,     0,
       0,     0,     0,    83,    81,     0,     0,    96,    94,    73,
      67,    68,     0,     0,     0,     0,     0,    98,    51,    53,
      54,    55,    61,    63,    65,   100,   101,   102,    45,    29,
     105,   103,   104,   106,     1,     9,    12,     4,     0,    14,
      17,     0,    16,    20,     0,    32,    33,     0,     0,    82,
      91,     0,    90,    86,     0,    95,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    10,     0,    24,     0,    27,     0,     0,     0,     0,
       0,    84,    92,     0,     0,    43,     0,    41,     0,     0,
       0,     0,    75,    52,    57,    58,    56,    59,    60,     0,
      64,    66,    76,    39,     0,    46,    47,     5,     0,     0,
      19,     0,     0,    22,    36,    35,     0,     0,     0,    88,
       0,     0,    74,     0,     2,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    23,     6,     0,    26,     0,    79,
       0,    93,    97,     0,    42,     0,     0,     0,     0,     0,
       0,     0,    62,     0,    37,    50,    49,     7,     0,     0,
       0,    85,    44,     3,     0,     0,    77,     0,     0,     0,
      40,     0,     0,    25,    28,    80,     0,     0,     0,     0,
       0,    38,     8,    69,    70,    78,    71,    72
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,   145,    58,   156,   192,    56,     9,    18,    10,    19,
      20,    59,    94,    62,    96,    60,   129,    63,   132,    11,
      12,    21,    65,    98,    66,   173,   124,   106,   107,    49,
      90,   125,   153,   126,    37,    38,    39,    40,    41,    42,
      43,    44,   148,   100,    23,    13,    24,    72,   103,    14,
      25,    73,   138,    27,    15,    28,    16,    17
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -145
static const yytype_int16 yypact[] =
{
      31,  -145,  -145,  -145,  -145,    11,  -145,    12,     2,    31,
      31,    31,    25,    31,    31,    31,    31,    20,    36,    41,
      41,    41,    35,    11,  -145,    48,    13,    12,  -145,     6,
    -145,  -145,    29,    30,    53,    55,     2,  -145,    44,  -145,
    -145,    -3,    69,    68,   -20,  -145,  -145,  -145,  -145,  -145,
    -145,  -145,  -145,  -145,  -145,  -145,    84,  -145,    42,    85,
    -145,    43,    86,  -145,    46,    87,  -145,    88,     2,  -145,
      47,    51,    89,  -145,    90,  -145,    91,    61,    62,    63,
      95,    70,     2,     2,     2,     2,    91,     2,     2,    91,
      97,  -145,    98,    92,    41,    93,    41,    99,    41,    76,
      75,  -145,  -145,    48,    77,    80,    81,    94,   106,   106,
     108,    96,  -145,  -145,  -145,   100,  -145,  -145,    83,   101,
    -145,  -145,  -145,   102,    82,   110,  -145,  -145,   113,   114,
    -145,   117,   114,  -145,  -145,  -145,   118,   103,   114,  -145,
     119,    91,  -145,    91,  -145,   -16,    -8,   112,    -7,   123,
       2,    97,    97,    97,  -145,   105,   115,  -145,   116,   107,
       2,  -145,  -145,   109,  -145,   124,   111,   120,   131,   132,
     121,   122,  -145,   125,   126,  -145,  -145,  -145,   134,   136,
      88,  -145,  -145,  -145,     2,     2,  -145,   127,     2,     2,
    -145,    97,   114,  -145,  -145,  -145,   128,   129,   138,   130,
     133,  -145,  -145,  -145,  -145,  -145,  -145,  -145
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -145,    33,   -19,  -128,  -145,  -145,  -145,  -145,  -145,  -145,
    -145,  -145,  -145,  -145,  -145,    49,  -145,    54,  -145,  -145,
    -145,  -145,  -145,  -145,    57,   -47,  -144,   -61,   -30,  -145,
    -145,  -145,  -145,     3,   -36,  -145,    78,    79,   -23,   -84,
      72,  -145,  -145,   -17,  -145,  -145,   142,  -145,  -145,  -145,
    -145,    64,  -145,  -145,  -145,   139,  -145,    39
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -100
static const yytype_int16 yytable[] =
{
      81,    61,    64,   120,   158,    29,    71,   174,   175,   165,
     161,    83,    84,    88,    22,    26,    89,   165,   169,   166,
      54,    30,    31,    32,    33,    34,    35,   167,   170,    85,
      36,   -99,   101,    48,    76,     1,     2,     3,     4,    55,
       5,     6,     7,     8,    57,    74,   113,   174,    45,    46,
      47,    70,    50,    51,    52,    53,   119,    77,    78,   122,
     115,   116,   118,    67,   202,    68,   172,    92,    92,    93,
      95,    92,    -4,    97,    -4,    82,    92,    61,   102,    64,
     163,    79,   164,    80,    71,    86,    87,    91,   -18,   -21,
     -34,    99,   -87,   104,   105,   108,   109,   110,   111,   112,
     123,   127,   134,   136,   137,   128,   131,   140,   141,   144,
     142,   147,   152,   -48,    83,    85,   154,   155,   150,   143,
     157,   159,   162,   149,   181,   168,   171,   183,   178,   179,
     151,   177,   180,   160,   186,   187,   184,   193,   182,   194,
     198,   205,   146,   130,   201,   185,   188,   189,   196,   197,
     133,   191,   199,   200,   190,   135,   176,   203,   204,   206,
     121,   114,   207,   195,   117,    69,    75,   139
};

static const yytype_uint8 yycheck[] =
{
      36,    20,    21,    87,   132,     3,    25,   151,   152,    25,
     138,    14,    15,    33,     3,     3,    36,    25,    25,    35,
       0,    19,    20,    21,    22,    23,    24,    35,    35,    32,
      28,     0,    68,     8,    28,     4,     5,     6,     7,     3,
       9,    10,    11,    12,     3,    32,    82,   191,     9,    10,
      11,     3,    13,    14,    15,    16,    86,    28,    28,    89,
      83,    84,    85,    28,   192,    30,   150,    25,    25,    27,
      27,    25,    25,    27,    27,    31,    25,    96,    27,    98,
     141,    28,   143,    28,   103,    16,    18,     3,     3,     3,
       3,     3,     3,     3,     3,    34,    34,    34,     3,    29,
       3,     3,     3,    27,    29,    13,    13,    30,    28,     3,
      29,     3,    30,     3,    14,    32,     3,     3,    17,    25,
       3,     3,     3,    27,   160,    13,     3,     3,    13,    13,
      28,    26,    25,    30,     3,     3,    25,     3,    29,     3,
      13,     3,   109,    94,   191,    25,    25,    25,   184,   185,
      96,    25,   188,   189,    29,    98,   153,    29,    29,    29,
      88,    83,    29,   180,    85,    23,    27,   103
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     4,     5,     6,     7,     9,    10,    11,    12,    43,
      45,    56,    57,    82,    86,    91,    93,    94,    44,    46,
      47,    58,     3,    81,    83,    87,     3,    90,    92,     3,
      19,    20,    21,    22,    23,    24,    28,    71,    72,    73,
      74,    75,    76,    77,    78,    94,    94,    94,     8,    66,
      94,    94,    94,    94,     0,     3,    42,     3,    39,    48,
      52,    39,    50,    54,    39,    59,    61,    28,    30,    83,
       3,    39,    84,    88,    32,    92,    28,    28,    28,    28,
      28,    71,    31,    14,    15,    32,    16,    18,    33,    36,
      67,     3,    25,    27,    49,    27,    51,    27,    60,     3,
      80,    71,    27,    85,     3,     3,    64,    65,    34,    34,
      34,     3,    29,    71,    73,    75,    75,    74,    75,    65,
      76,    77,    65,     3,    63,    68,    70,     3,    13,    53,
      52,    13,    55,    54,     3,    61,    27,    29,    89,    88,
      30,    28,    29,    25,     3,    38,    38,     3,    79,    27,
      17,    28,    30,    69,     3,     3,    40,     3,    40,     3,
      30,    40,     3,    64,    64,    25,    35,    35,    13,    25,
      35,     3,    76,    62,    63,    63,    70,    26,    13,    13,
      25,    71,    29,     3,    25,    25,     3,     3,    25,    25,
      29,    25,    41,     3,     3,    80,    71,    71,    13,    71,
      71,    62,    40,    29,    29,     3,    29,    29
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto yyerrlab

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yytoken = YYTRANSLATE (yychar);				\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (YYLEX_PARAM)
#else
# define YYLEX yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *bottom, yytype_int16 *top)
#else
static void
yy_stack_print (bottom, top)
    yytype_int16 *bottom;
    yytype_int16 *top;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; bottom <= top; ++bottom)
    YYFPRINTF (stderr, " %d", *bottom);
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule)
#else
static void
yy_reduce_print (yyvsp, yyrule)
    YYSTYPE *yyvsp;
    int yyrule;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      fprintf (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       );
      fprintf (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into YYRESULT an error message about the unexpected token
   YYCHAR while in state YYSTATE.  Return the number of bytes copied,
   including the terminating null byte.  If YYRESULT is null, do not
   copy anything; just return the number of bytes that would be
   copied.  As a special case, return 0 if an ordinary "syntax error"
   message will do.  Return YYSIZE_MAXIMUM if overflow occurs during
   size calculation.  */
static YYSIZE_T
yysyntax_error (char *yyresult, int yystate, int yychar)
{
  int yyn = yypact[yystate];

  if (! (YYPACT_NINF < yyn && yyn <= YYLAST))
    return 0;
  else
    {
      int yytype = YYTRANSLATE (yychar);
      YYSIZE_T yysize0 = yytnamerr (0, yytname[yytype]);
      YYSIZE_T yysize = yysize0;
      YYSIZE_T yysize1;
      int yysize_overflow = 0;
      enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
      char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
      int yyx;

# if 0
      /* This is so xgettext sees the translatable formats that are
	 constructed on the fly.  */
      YY_("syntax error, unexpected %s");
      YY_("syntax error, unexpected %s, expecting %s");
      YY_("syntax error, unexpected %s, expecting %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s");
# endif
      char *yyfmt;
      char const *yyf;
      static char const yyunexpected[] = "syntax error, unexpected %s";
      static char const yyexpecting[] = ", expecting %s";
      static char const yyor[] = " or %s";
      char yyformat[sizeof yyunexpected
		    + sizeof yyexpecting - 1
		    + ((YYERROR_VERBOSE_ARGS_MAXIMUM - 2)
		       * (sizeof yyor - 1))];
      char const *yyprefix = yyexpecting;

      /* Start YYX at -YYN if negative to avoid negative indexes in
	 YYCHECK.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;

      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yycount = 1;

      yyarg[0] = yytname[yytype];
      yyfmt = yystpcpy (yyformat, yyunexpected);

      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
	if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	  {
	    if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
	      {
		yycount = 1;
		yysize = yysize0;
		yyformat[sizeof yyunexpected - 1] = '\0';
		break;
	      }
	    yyarg[yycount++] = yytname[yyx];
	    yysize1 = yysize + yytnamerr (0, yytname[yyx]);
	    yysize_overflow |= (yysize1 < yysize);
	    yysize = yysize1;
	    yyfmt = yystpcpy (yyfmt, yyprefix);
	    yyprefix = yyor;
	  }

      yyf = YY_(yyformat);
      yysize1 = yysize + yystrlen (yyf);
      yysize_overflow |= (yysize1 < yysize);
      yysize = yysize1;

      if (yysize_overflow)
	return YYSIZE_MAXIMUM;

      if (yyresult)
	{
	  /* Avoid sprintf, as that infringes on the user's name space.
	     Don't have undefined behavior even if the translation
	     produced a string with the wrong number of "%s"s.  */
	  char *yyp = yyresult;
	  int yyi = 0;
	  while ((*yyp = *yyf) != '\0')
	    {
	      if (*yyp == '%' && yyf[1] == 's' && yyi < yycount)
		{
		  yyp += yytnamerr (yyp, yyarg[yyi++]);
		  yyf += 2;
		}
	      else
		{
		  yyp++;
		  yyf++;
		}
	    }
	}
      return yysize;
    }
}
#endif /* YYERROR_VERBOSE */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
#else
static void
yydestruct (yymsg, yytype, yyvaluep)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
#endif
{
  YYUSE (yyvaluep);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {

      default:
	break;
    }
}


/* Prevent warnings from -Wmissing-prototypes.  */

#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */



/* The look-ahead symbol.  */
int yychar;

/* The semantic value of the look-ahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;



/*----------.
| yyparse.  |
`----------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void)
#else
int
yyparse ()

#endif
#endif
{
  
  int yystate;
  int yyn;
  int yyresult;
  /* Number of tokens to shift before error messages enabled.  */
  int yyerrstatus;
  /* Look-ahead token as an internal (translated) token number.  */
  int yytoken = 0;
#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

  /* Three stacks and their tools:
     `yyss': related to states,
     `yyvs': related to semantic values,
     `yyls': related to locations.

     Refer to the stacks thru separate pointers, to allow yyoverflow
     to reallocate them elsewhere.  */

  /* The state stack.  */
  yytype_int16 yyssa[YYINITDEPTH];
  yytype_int16 *yyss = yyssa;
  yytype_int16 *yyssp;

  /* The semantic value stack.  */
  YYSTYPE yyvsa[YYINITDEPTH];
  YYSTYPE *yyvs = yyvsa;
  YYSTYPE *yyvsp;



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  YYSIZE_T yystacksize = YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;


  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY;		/* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */

  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;


	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),

		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss);
	YYSTACK_RELOCATE (yyvs);

#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;


      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     look-ahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to look-ahead token.  */
  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a look-ahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid look-ahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the look-ahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token unless it is eof.  */
  if (yychar != YYEOF)
    yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 166 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,ems)",(yyvsp[(1) - (1)]).string);
       ATindexedSetPut(PROTECT,(yyval).t,b); }
    break;

  case 3:
#line 169 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,<term>)",(yyvsp[(3) - (3)]).string,(yyvsp[(1) - (3)]).t);
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);}
    break;

  case 4:
#line 176 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,ems)",(yyvsp[(1) - (1)]).string); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       if (to_file) { fprintf(outfile,"%s",(yyvsp[(1) - (1)]).string); fflush(outfile); } }
    break;

  case 5:
#line 180 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,<term>)",(yyvsp[(3) - (3)]).string,(yyvsp[(1) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       if (to_file) { fprintf(outfile,",%s",(yyvsp[(3) - (3)]).string); fflush(outfile);}}
    break;

  case 6:
#line 187 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,ems)",(yyvsp[(1) - (1)]).string); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       if (to_file) { fprintf(outfile,"%s",(yyvsp[(1) - (1)]).string);fflush(outfile);} }
    break;

  case 7:
#line 191 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"%s#",(yyvsp[(1) - (2)]).string); fflush(outfile); } }
    break;

  case 8:
#line 193 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,<term>)",(yyvsp[(1) - (4)]).string,(yyvsp[(4) - (4)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(4) - (4)]).t);
	}
    break;

  case 9:
#line 200 "tmcrl.y"
    { spec.sorts=ATmake("ins(<str>,<term>)",(yyvsp[(1) - (1)]).string,spec.sorts); 
       if (to_file) { fprintf(outfile,"%s ",(yyvsp[(1) - (1)]).string);fflush(outfile);} }
    break;

  case 10:
#line 203 "tmcrl.y"
    { spec.sorts=ATmake("ins(<str>,<term>)",(yyvsp[(2) - (2)]).string,spec.sorts); 
       if (to_file) { fprintf(outfile,"%s ",(yyvsp[(2) - (2)]).string);fflush(outfile);} }
    break;

  case 11:
#line 208 "tmcrl.y"
    { if (to_file)  { fprintf(outfile,"sort ");fflush(outfile);} }
    break;

  case 12:
#line 210 "tmcrl.y"
    { if (to_file)  { fprintf(outfile,"\n\n");fflush(outfile);} }
    break;

  case 13:
#line 214 "tmcrl.y"
    { if (to_file)  { fprintf(outfile,"func ");fflush(outfile);} }
    break;

  case 14:
#line 216 "tmcrl.y"
    { if (to_file)  { fprintf(outfile,"\n");fflush(outfile);} }
    break;

  case 15:
#line 218 "tmcrl.y"
    { if (to_file)  { fprintf(outfile,"map  ");fflush(outfile);} }
    break;

  case 16:
#line 220 "tmcrl.y"
    { if (to_file)  { fprintf(outfile,"\n");fflush(outfile);} }
    break;

  case 18:
#line 225 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
    break;

  case 21:
#line 231 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
    break;

  case 23:
#line 236 "tmcrl.y"
    { for(auxterm=Reverse((yyvsp[(1) - (4)]).t, ems); 
           (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm)) ;
           spec.funcs=ATmake("ins(f(<str>,ems,<str>),<term>)",auxstring,(yyvsp[(4) - (4)]).string,spec.funcs)){} ;
       if (to_file) { fprintf(outfile,":->%s\n",(yyvsp[(4) - (4)]).string);fflush(outfile);}
     }
    break;

  case 24:
#line 242 "tmcrl.y"
    { if (to_file) { fprintf(outfile,":");fflush(outfile);} }
    break;

  case 25:
#line 244 "tmcrl.y"
    { for(auxterm=Reverse((yyvsp[(1) - (6)]).t, ems) ; 
         (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm));
         spec.funcs=ATmake("ins(f(<str>,<term>,<str>),<term>)",auxstring,
                      (yyvsp[(4) - (6)]).t,(yyvsp[(6) - (6)]).string,spec.funcs)){};
       if (to_file) { fprintf(outfile,"->%s\n",(yyvsp[(6) - (6)]).string);fflush(outfile);}
     }
    break;

  case 26:
#line 253 "tmcrl.y"
    { for(auxterm=(yyvsp[(1) - (4)]).t ; 
         (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm));
         spec.maps=ATmake("ins(f(<str>,ems,<str>),<term>)",auxstring,(yyvsp[(4) - (4)]).string,spec.maps)){}; 
       if (to_file) { fprintf(outfile,":->%s\n",(yyvsp[(4) - (4)]).string);fflush(outfile);}
     }
    break;

  case 27:
#line 259 "tmcrl.y"
    { if (to_file) { fprintf(outfile,":");fflush(outfile);} }
    break;

  case 28:
#line 261 "tmcrl.y"
    { for(auxterm=(yyvsp[(1) - (6)]).t ; 
         ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm);
         spec.maps=ATmake("ins(f(<str>,<term>,<str>),<term>)",auxstring,
                   (yyvsp[(4) - (6)]).t,(yyvsp[(6) - (6)]).string,spec.maps)){}; 
       if (to_file) { fprintf(outfile,"->%s\n",(yyvsp[(6) - (6)]).string);fflush(outfile);}
     }
    break;

  case 29:
#line 270 "tmcrl.y"
    { for( auxterm=(yyvsp[(2) - (2)]).t;
       (ATmatch(auxterm,"ins(pair(<term>,<term>),<term>)",
               &auxterm1,&auxterm2,&auxterm));
       spec.eqns=ATmake("ins(e(<term>,<term>,<term>),<term>)",(yyvsp[(1) - (2)]).t,auxterm1,auxterm2,spec.eqns)){} ; }
    break;

  case 30:
#line 276 "tmcrl.y"
    { (yyval).t=ATmake("emv"); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
     }
    break;

  case 31:
#line 280 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"var  ");fflush(outfile);} }
    break;

  case 32:
#line 282 "tmcrl.y"
    { (yyval).t=(yyvsp[(3) - (3)]).t; }
    break;

  case 33:
#line 286 "tmcrl.y"
    { (yyval).t=(yyvsp[(1) - (1)]).t; }
    break;

  case 34:
#line 288 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
    break;

  case 35:
#line 290 "tmcrl.y"
    { (yyval).t=auxterm1=(yyvsp[(1) - (3)]).t; /* assignment to auxterm1 is for protection of this
                             term against garbage collection */
      ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
      for(auxterm=(yyvsp[(3) - (3)]).t ;
        (ATmatch(auxterm,"ins(<str>,<str>,<term>)",&auxstring,&auxstring1,&auxterm));
        (yyval).t=auxterm1=ATmake("ins(<str>,<str>,<term>)",auxstring,auxstring1,(yyval).t)){}; 
      ATindexedSetPut(PROTECT,(yyval).t,b);
    }
    break;

  case 36:
#line 301 "tmcrl.y"
    { auxterm1=ATmake("emv");
       for( auxterm=(yyvsp[(1) - (3)]).t ; 
            (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm)) ;)
            { auxterm1=ATmake("ins(<str>,<str>,<term>)",auxstring,(yyvsp[(3) - (3)]).string,auxterm1) ;
              /* insertvariablename(auxstring); */ }  
       if (to_file) { fprintf(outfile,":%s\n",(yyvsp[(3) - (3)]).string);fflush(outfile);}
       (yyval).t=auxterm1;
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
     }
    break;

  case 37:
#line 314 "tmcrl.y"
    { (yyval).t=ATmake("ins(<term>,emt)",(yyvsp[(1) - (1)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (1)]).t);
     }
    break;

  case 38:
#line 319 "tmcrl.y"
    { (yyval).t=ATmake("ins(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 39:
#line 327 "tmcrl.y"
    { (yyval).t=ATmake("t(<str>,emt)",(yyvsp[(1) - (1)]).string); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
     }
    break;

  case 40:
#line 331 "tmcrl.y"
    { (yyval).t=ATmake("t(<str>,<term>)",(yyvsp[(1) - (4)]).string,(yyvsp[(3) - (4)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (4)]).t);
     }
    break;

  case 41:
#line 338 "tmcrl.y"
    { (yyval).t=ATmake("ins(<term>,emt)",(yyvsp[(1) - (1)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (1)]).t);
     }
    break;

  case 42:
#line 343 "tmcrl.y"
    { (yyval).t=ATmake("ins(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 43:
#line 351 "tmcrl.y"
    { (yyval).t=ATmake("t(<str>,emt)",(yyvsp[(1) - (1)]).string); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
     }
    break;

  case 44:
#line 355 "tmcrl.y"
    { (yyval).t=ATmake("t(<str>,<term>)",(yyvsp[(1) - (4)]).string,(yyvsp[(3) - (4)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (4)]).t);
     }
    break;

  case 45:
#line 362 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"rew  ");fflush(outfile);} }
    break;

  case 46:
#line 364 "tmcrl.y"
    { (yyval).t=Reverse((yyvsp[(3) - (3)]).t, eme); 
       if (to_file) { fprintf(outfile,"\n");fflush(outfile);}}
    break;

  case 47:
#line 369 "tmcrl.y"
    { (yyval).t=ATmake("ins(<term>,eme)",(yyvsp[(1) - (1)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (1)]).t);
     }
    break;

  case 48:
#line 374 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
    break;

  case 49:
#line 376 "tmcrl.y"
    { (yyval).t=ATmake("ins(<term>,<term>)",(yyvsp[(3) - (3)]).t,(yyvsp[(1) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 50:
#line 384 "tmcrl.y"
    { (yyval).t=ATmake("pair(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
       if (to_file) 
        { long pos=0;
          print_term(outfile,(yyvsp[(1) - (3)]).t,&pos);
          fprintf(outfile,"=");
          pos++;
          print_term(outfile,(yyvsp[(3) - (3)]).t,&pos); 
          { fprintf(outfile,"\n");fflush(outfile);} }
     }
    break;

  case 51:
#line 399 "tmcrl.y"
    { (yyval).t=(yyvsp[(1) - (1)]).t; }
    break;

  case 52:
#line 401 "tmcrl.y"
    { (yyval).t=ATmake("alt(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 53:
#line 409 "tmcrl.y"
    { (yyval).t=(yyvsp[(1) - (1)]).t; }
    break;

  case 54:
#line 411 "tmcrl.y"
    { (yyval).t=(yyvsp[(1) - (1)]).t; }
    break;

  case 55:
#line 413 "tmcrl.y"
    { (yyval).t=(yyvsp[(1) - (1)]).t; }
    break;

  case 56:
#line 415 "tmcrl.y"
    { (yyval).t=ATmake("lmer(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 57:
#line 423 "tmcrl.y"
    { (yyval).t=ATmake("par(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 58:
#line 429 "tmcrl.y"
    { (yyval).t=ATmake("par(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 59:
#line 437 "tmcrl.y"
    { (yyval).t=ATmake("com(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 60:
#line 443 "tmcrl.y"
    { (yyval).t=ATmake("com(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 61:
#line 451 "tmcrl.y"
    { (yyval).t=(yyvsp[(1) - (1)]).t; }
    break;

  case 62:
#line 454 "tmcrl.y"
    { (yyval).t=ATmake("cond(<term>,<term>,<term>)",(yyvsp[(1) - (5)]).t,(yyvsp[(3) - (5)]).t,(yyvsp[(5) - (5)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (5)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (5)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(5) - (5)]).t);
     }
    break;

  case 63:
#line 463 "tmcrl.y"
    { (yyval).t=(yyvsp[(1) - (1)]).t; }
    break;

  case 64:
#line 465 "tmcrl.y"
    { (yyval).t=ATmake("bound(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       time_operators_used=1; 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 65:
#line 474 "tmcrl.y"
    { (yyval).t=(yyvsp[(1) - (1)]).t; }
    break;

  case 66:
#line 476 "tmcrl.y"
    { (yyval).t=ATmake("seq(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 67:
#line 484 "tmcrl.y"
    { (yyval).t=ATmake("delta"); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
     }
    break;

  case 68:
#line 488 "tmcrl.y"
    { (yyval).t=ATmake("tau"); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
     }
    break;

  case 69:
#line 492 "tmcrl.y"
    { (yyval).t=ATmake("encap(<term>,<term>)",(yyvsp[(4) - (8)]).t,(yyvsp[(7) - (8)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(4) - (8)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(7) - (8)]).t);
     }
    break;

  case 70:
#line 498 "tmcrl.y"
    { (yyval).t=ATmake("hide(<term>,<term>)",(yyvsp[(4) - (8)]).t,(yyvsp[(7) - (8)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(4) - (8)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(7) - (8)]).t);
     }
    break;

  case 71:
#line 504 "tmcrl.y"
    { (yyval).t=ATmake("rename(<term>,<term>)",(yyvsp[(4) - (8)]).t,(yyvsp[(7) - (8)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(4) - (8)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(7) - (8)]).t);
     }
    break;

  case 72:
#line 510 "tmcrl.y"
    { (yyval).t=ATmake("sum(<str>,<str>,<term>)",(yyvsp[(3) - (8)]).string,(yyvsp[(5) - (8)]).string,(yyvsp[(7) - (8)]).t); 
       insertvariablename((yyvsp[(3) - (8)]).string); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(7) - (8)]).t);
     }
    break;

  case 73:
#line 516 "tmcrl.y"
    { (yyval).t=ATmake("name(<str>,emt)",(yyvsp[(1) - (1)]).string); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
     }
    break;

  case 74:
#line 520 "tmcrl.y"
    { (yyval).t=ATmake("name(<str>,<term>)",(yyvsp[(1) - (4)]).string,(yyvsp[(3) - (4)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (4)]).t);
     }
    break;

  case 75:
#line 525 "tmcrl.y"
    { (yyval).t=(yyvsp[(2) - (3)]).t; }
    break;

  case 76:
#line 527 "tmcrl.y"
    { (yyval).t=ATmake("at(<term>,<term>)",(yyvsp[(1) - (3)]).t,(yyvsp[(3) - (3)]).t); 
       time_operators_used=1; 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (3)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 77:
#line 536 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,<str>,emr)",(yyvsp[(1) - (3)]).string,(yyvsp[(3) - (3)]).string); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
     }
    break;

  case 78:
#line 540 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,<str>,<term>)",(yyvsp[(3) - (5)]).string,(yyvsp[(5) - (5)]).string,(yyvsp[(1) - (5)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(1) - (5)]).t);
     }
    break;

  case 79:
#line 547 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,<str>,emv)",(yyvsp[(1) - (3)]).string,(yyvsp[(3) - (3)]).string); 
       insertvariablename((yyvsp[(1) - (3)]).string); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
     }
    break;

  case 80:
#line 552 "tmcrl.y"
    { (yyval).t=ATmake("ins(<str>,<str>,<term>)",(yyvsp[(1) - (5)]).string,(yyvsp[(3) - (5)]).string,(yyvsp[(5) - (5)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(5) - (5)]).t);
       insertvariablename((yyvsp[(1) - (5)]).string); 
     }
    break;

  case 81:
#line 560 "tmcrl.y"
    { spec.procs=ATmake("ins(<term>,<term>)",(yyvsp[(1) - (1)]).t,spec.procs); }
    break;

  case 82:
#line 562 "tmcrl.y"
    { spec.procs=ATmake("ins(<term>,<term>)",(yyvsp[(2) - (2)]).t,spec.procs); }
    break;

  case 84:
#line 569 "tmcrl.y"
    { (yyval).t=ATmake("proc(<str>,emv,<term>)",(yyvsp[(1) - (3)]).string,(yyvsp[(3) - (3)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (3)]).t);
     }
    break;

  case 85:
#line 574 "tmcrl.y"
    { (yyval).t=ATmake("proc(<str>,<term>,<term>)",
                            (yyvsp[(1) - (6)]).string,(yyvsp[(3) - (6)]).t,(yyvsp[(6) - (6)]).t); 
       ATindexedSetPut(PROTECT,(yyval).t,b);
       ATindexedSetRemove(PROTECT,(yyvsp[(3) - (6)]).t);
       ATindexedSetRemove(PROTECT,(yyvsp[(6) - (6)]).t);
     }
    break;

  case 87:
#line 584 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"     ");fflush(outfile);} }
    break;

  case 89:
#line 589 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"act  ");fflush(outfile);} }
    break;

  case 90:
#line 591 "tmcrl.y"
    { if (to_file) { fprintf(outfile,"\n");fflush(outfile);} }
    break;

  case 91:
#line 595 "tmcrl.y"
    { spec.acts=ATmake("ins(<str>,ems,<term>)",(yyvsp[(1) - (1)]).string,spec.acts); 
       if (to_file) { fprintf(outfile,"%s\n",(yyvsp[(1) - (1)]).string);fflush(outfile);} }
    break;

  case 92:
#line 598 "tmcrl.y"
    { if (to_file) { fprintf(outfile,":");fflush(outfile);} }
    break;

  case 93:
#line 600 "tmcrl.y"
    { for(auxterm=(yyvsp[(1) - (4)]).t;
         (ATmatch(auxterm,"ins(<str>,<term>)",&auxstring,&auxterm));
         spec.acts=ATmake("ins(<str>,<term>,<term>)",auxstring,(yyvsp[(4) - (4)]).t,spec.acts)){} ; 
       if (to_file) { fprintf(outfile,"\n");fflush(outfile);}
     }
    break;

  case 97:
#line 615 "tmcrl.y"
    { spec.comms=ATmake("ins(<str>,<str>,<str>,<term>)",
                   (yyvsp[(1) - (5)]).string,(yyvsp[(3) - (5)]).string,(yyvsp[(5) - (5)]).string,spec.comms); }
    break;

  case 98:
#line 620 "tmcrl.y"
    { if (spec.init==NULL)
            spec.init=(yyvsp[(2) - (2)]).t; 
          else yyerror("Only one init declaration is allowed"); }
    break;


/* Line 1267 of yacc.c.  */
#line 2296 "y.tab.c"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;


  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
      {
	YYSIZE_T yysize = yysyntax_error (0, yystate, yychar);
	if (yymsg_alloc < yysize && yymsg_alloc < YYSTACK_ALLOC_MAXIMUM)
	  {
	    YYSIZE_T yyalloc = 2 * yysize;
	    if (! (yysize <= yyalloc && yyalloc <= YYSTACK_ALLOC_MAXIMUM))
	      yyalloc = YYSTACK_ALLOC_MAXIMUM;
	    if (yymsg != yymsgbuf)
	      YYSTACK_FREE (yymsg);
	    yymsg = (char *) YYSTACK_ALLOC (yyalloc);
	    if (yymsg)
	      yymsg_alloc = yyalloc;
	    else
	      {
		yymsg = yymsgbuf;
		yymsg_alloc = sizeof yymsgbuf;
	      }
	  }

	if (0 < yysize && yysize <= yymsg_alloc)
	  {
	    (void) yysyntax_error (yymsg, yystate, yychar);
	    yyerror (yymsg);
	  }
	else
	  {
	    yyerror (YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse look-ahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse look-ahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  *++yyvsp = yylval;


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#ifndef yyoverflow
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEOF && yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}


#line 634 "tmcrl.y"


#include "lex.yy.c"

void yyerror(char *s)
{ sprintf(error_message,"line %d: %s, near %s\n", lino, s,
        get_token(yychar));
  /* fprintf(stderr,error_message); fflush(stderr); */
  error=1;
  /* err_fatal("line %d: %s, near %s", lino, s,
        get_token(yychar)); */
  return;
}

#ifndef HAVE_YYWRAP
int yywrap()
{
  return 1;
}
#endif


