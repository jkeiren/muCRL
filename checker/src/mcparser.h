/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton interface for Bison's Yacc-like parsers in C

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

/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     PAR_OPEN = 258,
     PAR_CLOSE = 259,
     BR_OPEN = 260,
     BR_CLOSE = 261,
     ANG_OPEN = 262,
     ANG_CLOSE = 263,
     COMMA = 264,
     SEMICOLON = 265,
     IS = 266,
     AT = 267,
     KWTRUE = 268,
     KWFALSE = 269,
     KWNIL = 270,
     KWFORALL = 271,
     KWEXISTS = 272,
     KWMU = 273,
     KWNU = 274,
     RNAME = 275,
     EQ = 276,
     IMP = 277,
     OR = 278,
     AND = 279,
     MUST = 280,
     MAY = 281,
     QUANTIFIER = 282,
     NOT = 283,
     PIPE = 284,
     DOT = 285,
     PLUS = 286,
     STAR = 287
   };
#endif
/* Tokens.  */
#define PAR_OPEN 258
#define PAR_CLOSE 259
#define BR_OPEN 260
#define BR_CLOSE 261
#define ANG_OPEN 262
#define ANG_CLOSE 263
#define COMMA 264
#define SEMICOLON 265
#define IS 266
#define AT 267
#define KWTRUE 268
#define KWFALSE 269
#define KWNIL 270
#define KWFORALL 271
#define KWEXISTS 272
#define KWMU 273
#define KWNU 274
#define RNAME 275
#define EQ 276
#define IMP 277
#define OR 278
#define AND 279
#define MUST 280
#define MAY 281
#define QUANTIFIER 282
#define NOT 283
#define PIPE 284
#define DOT 285
#define PLUS 286
#define STAR 287




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 50 "mcparser.y"
{
  ATermAppl appl;
  ATermList list;
}
/* Line 1489 of yacc.c.  */
#line 118 "mcparser.h"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE MCyylval;

