/* $Id:$ */
#define str(s) #s
/* #define DEBUG */
#ifdef DINSTANTIATE_C
#define SRC str(dinstantiate)
#define FFLUSH  fflush(stdout);
#define STD  stdout
#endif
#ifdef MGRSTART_C
#define SRC str(mgrstart)
#define STD stderr
#define FFLUSH
#endif

static void C_inst2mgr_tag(file_t f, int *tag) {
#ifdef DINSTANTIATE_C
     fputc(*tag, f); fflush(f);
#endif
#ifdef MGRSTART_C
    *tag = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_inst2mgr_tag:"SRC":tag = %c\n", *tag);
    FFLUSH
#endif
}

static void C_mgr2inst_tag(file_t f, int *tag) {
#ifdef MGRSTART_C
     fputc(*tag, f); fflush(f);
#endif
#ifdef DINSTANTIATE_C
    *tag = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2inst_tag:"SRC":tag = %c\n", *tag);
    FFLUSH
#endif
}

static void C_inst2mgr_seg(file_t f, int *seg) {
#ifdef DINSTANTIATE_C
     fputc(*seg, f); fflush(f);
#endif
#ifdef MGRSTART_C
    *seg = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_inst2mgr_seg:"SRC":seg = %d\n", *seg);
    FFLUSH
#endif
}

static void C_mgr2inst_idx(file_t f, int *idx) {
#ifdef MGRSTART_C
     writeintUTF(f, *idx); fflush(f);
#endif
#ifdef DINSTANTIATE_C
     readintUTF(f, idx);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2inst_idx:"SRC":idx = %d\n", *idx);
    FFLUSH
#endif
}

static void C_mgr2inst_seg(file_t f, int *seg) {
#ifdef MGRSTART_C
     writeintUTF(f, *seg); fflush(f);
#endif
#ifdef DINSTANTIATE_C
     readintUTF(f, seg);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2inst_seg:"SRC":seg= %d\n", *seg);
    FFLUSH
#endif
}

static void C_mgr2inst_env(file_t f, env_t *env) {
#ifdef MGRSTART_C
   fwrite(env,sizeof(env_t), 1, f); fflush(f); 
#endif
#ifdef DINSTANTIATE_C
   fread(env,sizeof(env_t), 1, f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2inst_env:"SRC":env = (%d %d %d %d %d %s)\n", 
    env->nseg, env->restore, env->port, env->nLeft, env->nRight, env->dir);
    FFLUSH
#endif
}

static void C_inst2mgr_ad(file_t f, ad_t ad) {
#ifdef DINSTANTIATE_C
   fwrite(ad,sizeof(ad_r), 1, f); fflush(f); 
#endif
#ifdef MGRSTART_C
   fread(ad,sizeof(ad_r), 1, f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_inst2mgr_ad:"SRC":ad = (%d %d %d %d %d %d)\n", 
    ad->visited, ad->explored, ad->level, ad->transitions, ad->deadlocks, 
    ad->ticks);
    FFLUSH
#endif
}

static void C_mgr2inst_dest(file_t f, char **dest, int n) {
   int i;
#ifdef MGRSTART_C
   for (i=0;i<n;i++)  printUTF(f, dest[i]); fflush(f); 
#endif
#ifdef DINSTANTIATE_C
   for (i=0;i<n;i++) dest[i]= strdup(readstringUTF(f));
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2inst_dest:"SRC":"); 
    for (i=0;i<n;i++) fprintf(STD," %s", dest[i]);
    fprintf(STD,"\n"); FFLUSH
#endif
}

static void C_inst2mgr_val(file_t f, vdbval_t *val) {
#ifdef DINSTANTIATE_C
   fwrite(val,sizeof(vdbval_t), 1, f); fflush(f); 
#endif
#ifdef MGRSTART_C
   fread(val,sizeof(vdbval_t), 1, f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_inst2mgr_val:"SRC":val = (%d %d %d)\n", 
    val->seg, val->idx, val->act); 
    FFLUSH
#endif
}

static void C_inst2mgr_int(file_t f, int *n) {
#ifdef DINSTANTIATE_C
     writeintUTF(f, *n); fflush(f);
#endif
#ifdef MGRSTART_C
     readintUTF(f, n);
#endif
#ifdef DEBUG
    fprintf(STD,"C_inst2mgr_int:"SRC":n = %d\n", *n);
    FFLUSH
#endif
}

static void C_mgr2inst_mcrlargs(file_t f, char **s) { 
#ifdef MGRSTART_C
   printUTF(f, *s); fflush(f); 
#endif
#ifdef DINSTANTIATE_C
   *s = strdup(readstringUTF(f));
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2inst_mcrlargs:"SRC":"); 
    fprintf(STD," %s\n", *s); FFLUSH
#endif
}
#undef str
#undef SRC
#undef STD
#undef FFLUSH
