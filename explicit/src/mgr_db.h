/* $Id:$ */
#define str(s) #s
/* #define DEBUG */
#ifdef DBSTART_C
#define SRC str(dbstart)
#define FFLUSH  fflush(stdout);
#define STD  stdout
#endif
#ifdef MGRSTART_C
#define SRC str(mgrstart)
#define STD stderr
#define FFLUSH 
#endif
static void C_mgr2db_tag(file_t f, int *tag) {
#ifdef MGRSTART_C
     fputc(*tag, f); // fflush(f);
#endif
#ifdef DBSTART_C
    *tag = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2db_tag:"SRC":tag = %c\n", *tag);
    FFLUSH;
#endif
}

static void C_db2mgr_leftright(file_t f, int *nLeft, int *nRight) {
#ifdef DBSTART_C 
    writeintUTF(f, *nLeft);writeintUTF(f, *nRight); 
    fflush(f);
#endif
#ifdef MGRSTART_C
    readintUTF(f, nLeft);readintUTF(f, nRight);
#endif
#ifdef DEBUG
    fprintf(STD,"C_db2mgr_leftright:"SRC":leftright = (%d %d)\n", 
    *nLeft, *nRight); FFLUSH
#endif
}

static void C_mgr2db_act(file_t f, int *act) {
#ifdef MGRSTART_C
     writeintUTF(f, *act); fflush(f);
#endif
#ifdef DBSTART_C
    readintUTF(f, act);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2db_act:"str(SRC)":act = %c\n", *act);
    FFLUSH
#endif
}

static void C_db2mgr_string(file_t f, char **s) {
#ifdef DBSTART_C
    printUTF(f, *s); fflush(f);
#endif
#ifdef MGRSTART_C
    *s = readstringUTF(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_db2mgr_string:"str(SRC)":string = %s\n", *s); 
    FFLUSH
#endif
}
#undef str
#undef SRC
#undef STD
#undef FFLUSH

