%{                              /* -*-C-*- mode */
char *last_lex;      /* last lexical token read */
void ll_inc_pos(int);
void ll_coords(int,int);
extern void yyerror(char *);
%}
%option never-interactive

layout        [ \t]
comment       "%".*
ws            {layout}|{comment}
name           [A-Za-z0-9\^\_\'\\\-]*[a-zA-Z0-9\^\_\'\\]

%%
\r?\n         { lino++; pos = 0;}
{ws}          { ll_inc_pos(strlen(yytext)); }

sort          { ll_inc_pos(4); return(SORT); }
func          { ll_inc_pos(4); return(FUNC); }
map           { ll_inc_pos(3); return(MAP); }
var           { ll_inc_pos(3); return(VAR); }
rew           { ll_inc_pos(3); return(REW); }
proc          { ll_inc_pos(4); return(PROC); }
act           { ll_inc_pos(3); return(ACT); }
comm          { ll_inc_pos(4); return(COMM); }
init          { ll_inc_pos(4); return(INIT); }

"->"          { ll_inc_pos(2); return(ARROW); }
"\|\|"        { ll_inc_pos(2); return(MERGE); }
"\|\|\_"      { ll_inc_pos(3); return(LEFTMERGE); }
"<\|"         { ll_inc_pos(2); return(LEFTTRIANGLE); }
"\|>"         { ll_inc_pos(2); return(RIGHTTRIANGLE); }
"<<"          { ll_inc_pos(2); return(BOUNDINIT); }
delta         { ll_inc_pos(5); return(DELTA); }
tau           { ll_inc_pos(3); return(TAU); }
encap         { ll_inc_pos(5); return(ENCAP); }
hide          { ll_inc_pos(4); return(HIDE); }
rename        { ll_inc_pos(6); return(RENAME); }
sum           { ll_inc_pos(3); return(SUM); }


{name}        { 
               ll_inc_pos(strlen(yytext));
               yylval.string = strdup(yytext);
               return(NAME);
              }
.             { ll_inc_pos(1); return(yytext[0]);}

%%
char msg[100];

void ll_inc_pos(int n)
{
  last_lex = yytext;
  /*  fprintf(stderr, "ll_inc_pos: %s\n", yytext); */
  yylval.lino = yylval.elino = lino;
  yylval.pos = pos;
  pos += n;
  yylval.epos = pos;
}

void ll_coords(int blino, int bpos)
{
  yylval.lino = blino; yylval.pos = bpos;
  yylval.elino = lino; yylval.epos = pos;
}

char *get_token(int tk)
{
  switch(tk){
  case NAME:
    sprintf(msg, "string \"%s\"", last_lex);
    return msg;
  case SORT:
  case FUNC:
  case MAP:
  case VAR:
  case REW:
  case PROC:
  case ACT:
  case COMM:
  case INIT:
    sprintf(msg, "keyword \"%s\"", last_lex);
    return msg;
  case ARROW:
  case MERGE:
  case LEFTMERGE:
  case LEFTTRIANGLE:
  case RIGHTTRIANGLE:
  case BOUNDINIT:
  case DELTA:
  case TAU:
  case ENCAP:
  case HIDE:
  case RENAME:
  case SUM:
    sprintf(msg, "operator \"%s\"", last_lex);
    return msg;
  default: 
    sprintf(msg, "character: \"%c\"",
            last_lex[0]);
    return msg;
  } 
} 
