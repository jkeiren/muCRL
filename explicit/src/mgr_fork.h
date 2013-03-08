/* $Id: mgr_fork.h,v 1.4 2006/11/16 14:55:04 bertl Exp $ */
#define str(s) #s
/* #define DEBUG */
#ifdef FORK_C
#define SRC str(fork)
#define FFLUSH  fflush(stdout);
#define STD  stdout
#endif
#ifdef MGRSTART_C
#define SRC str(mgrstart)
#define STD stderr
#define FFLUSH
#endif

static void C_fork2mgr_tag(file_t f, int *tag) {
#ifdef FORK_C
     if (fputc(*tag, f)<0) 
        errormsg("fork2mgr_tag:fputc"); 
     if (fflush(f)<0) 
        errormsg("fork2mgr_tag:fflush"); 
#endif
#ifdef MGRSTART_C
    *tag = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_fork2mgr_tag:"SRC":tag = %c\n", *tag);
    FFLUSH
#endif
}

static void C_mgr2fork_tag(file_t f, int *tag) {
#ifdef MGRSTART_C
     if (fputc(*tag, f)<0) 
        errormsg("mgr2fork_tag:fputc"); 
     if (fflush(f)<0)
        errormsg("mgr2fork_tag:fflush"); 
#endif
#ifdef FORK_C
    *tag = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2fork_tag:"SRC":tag = %c\n", *tag);
    FFLUSH
#endif
}

static void C_mgr2fork_tagseg(file_t f, int *tag, int *seg) {
#ifdef MGRSTART_C
     if (fputc(*tag, f)<0)
        errormsg("mgr2fork_tagseg:fputc(tag)"); 
     if (fputc(*seg, f)<0) 
        errormsg("mgr2fork_tagseg:fputc(seg)"); 
     if (fflush(f)<0)
        errormsg("mgr2fork_tagseg:fflush"); 
#endif
#ifdef FORK_C
    *tag = fgetc(f); *seg = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2fork_tagseg:"SRC":tag = %c seg = %d\n", *tag, *seg);
    FFLUSH
#endif
}

static void C_fork2mgr_seg(file_t f, int *seg) {
#ifdef FORK_C
     if (fputc(*seg, f)<0) 
        errormsg("fork2mgr_seg:fputc"); 
     if (fflush(f)<0)
        errormsg("fork2mgr_seg:fflush"); 
#endif
#ifdef MGRSTART_C
    *seg = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_fork2mgr_seg:"SRC":seg = %d\n", *seg);
    FFLUSH
#endif
}

static void C_mgr2fork_idx(file_t f, int *idx) {
#ifdef MGRSTART_C
     if (writeintUTF(f, *idx)<0)
            errormsg("mgr2fork_idx:writeintUTF");
     if (fflush(f)<0)
            errormsg("mgr2fork_idx:fflush");
#endif
#ifdef FORK_C
     readintUTF(f, idx);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2fork_idx:"SRC":idx = %d\n", *idx);
    FFLUSH
#endif
}

static void C_mgr2fork_seg(file_t f, int *seg) {
#ifdef MGRSTART_C
     if (fputc(*seg, f)<0)
        errormsg("mgr2fork_seg:fputc"); 
     if (fflush(f)<0)
        errormsg("mgr2fork_seg:fflush"); 
#endif
#ifdef FORK_C
     *seg = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2fork_seg:"SRC":seg= %d\n", *seg);
    FFLUSH
#endif
}
static void C_mgr2fork_env(file_t f, env_t *env) {
#ifdef MGRSTART_C
   DYNwrite(f, (DYNptr) env); fflush(f); 
#endif
#ifdef FORK_C
   DYNread(f, (DYNptr) env);
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2fork_env:"SRC":env = (%d %d %d %d %d %s)\n", 
    env->nseg, env->restore, env->port, env->nLeft, env->nRight, env->dir);
    FFLUSH
#endif
}

static void C_mgr2fork_dest(file_t f, char **dest, unsigned int n) {
   int i;
#ifdef MGRSTART_C
   for (i=0;i<n;i++)  printUTF(f, dest[i]); fflush(f); 
#endif
#ifdef FORK_C
   for (i=0;i<n;i++) dest[i]= strdup(readstringUTF(f));
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2fork_dest:"SRC":"); 
    for (i=0;i<n;i++) fprintf(STD," %s", dest[i]);
    fprintf(STD,"\n");
    FFLUSH
#endif
}

static void C_fork2mgr_val(file_t f, vdbval_t *val) {
#ifdef FORK_C
   fwrite(val,sizeof(vdbval_t), 1, f); fflush(f); 
#endif
#ifdef MGRSTART_C
   fread(val,sizeof(vdbval_t), 1, f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_fork2mgr_val:"SRC":val = (%d %d %d)\n", 
    val->seg, val->idx, val->act); 
    FFLUSH
#endif
}

static void C_fork2mgr_report(file_t f, report_t *report) {
#ifdef FORK_C
   fwrite(report,sizeof(report_t), 1, f); fflush(f); 
#endif
#ifdef MGRSTART_C
   fread(report,sizeof(report_t), 1, f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_fork2mgr_report:"SRC":report = (%s %d)\n", 
    report->hostname, report->pid); 
    FFLUSH
#endif
}

static void C_fork2mgr_int(file_t f, int *n) {
#ifdef FORK_C
   if (writeintUTF(f, *n)<0) 
            errormsg("fork2mgr_int:writeintUTF");
   // if (fflush(f)<0) errormsg("fork2mgr_int:fflush");
#endif
#ifdef MGRSTART_C
     readintUTF(f,n);
#endif
#ifdef DEBUG
    fprintf(STD,"C_fork2mgr_int:"SRC":n = %d\n", *n);
    FFLUSH

#endif
}

static void C_fork2mgr_long(file_t f, long *n) {
#ifdef FORK_C
   if (writelongUTF(f, *n)<0) 
            errormsg("fork2mgr_int:writeintUTF");
   if (fflush(f)<0) errormsg("fork2mgr_long:fflush");
#endif
#ifdef MGRSTART_C
     readlongUTF(f,n);
#endif
#ifdef DEBUG
    fprintf(STD,"C_fork2mgr_long:"SRC":n = %d\n", *n);
    FFLUSH
#endif
}

static void C_mgr2fork_taglong(file_t f, int *tag,  long *n) {
#ifdef FORK_C
   *tag = fgetc(f);
   if (readlongUTF(f, n)<0) 
            errormsg("mgr2fork_taglong:readlongUTF");
#endif
#ifdef MGRSTART_C
     if (fputc(*tag, f)<0)
        errormsg("mgr2fork_taglong:fputc(tag)"); 
     writelongUTF(f,*n);
     if (fflush(f)<0) errormsg("mgr2fork_taglong:fflush");
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2fork_taglong:"SRC":n = %d\n", *n);
    FFLUSH
#endif
}

static void C_mgr2fork_long(file_t f, int  long *n) {
#ifdef FORK_C
   if (readlongUTF(f, n)<0) 
            errormsg("mgr2fork_long:readlongUTF");
#endif
#ifdef MGRSTART_C 
     writelongUTF(f,*n);
     if (fflush(f)<0) errormsg("mgr2fork_long:fflush");
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2fork_long:"SRC":n = %d\n", *n);
    FFLUSH
#endif
}

static void C_fork2mgr_segtag(file_t f, int *seg, int *tag) {
#ifdef FORK_C
     if (fputc(*seg, f)<0) errormsg("fork2mgr_segtag:fputc(seg)"); 
     if (fputc(*tag, f)<0) errormsg("fork2mgr_segtag:fputc(seg)"); 
     if (fflush(f)<0) errormsg("fork2mgr_segtag:fflush");
#endif
#ifdef MGRSTART_C
    *seg = fgetc(f); *tag = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(STD,"C_fork2mgr_segtag:"SRC":seg = %d tag = %c\n", 
         *seg, *tag);
    FFLUSH
#endif
}


static void C_fork2mgr_ad(file_t f, ad_t *ad) {
#ifdef FORK_C
   DYNwrite(f, (DYNptr) ad); fflush(f); 
#endif
#ifdef MGRSTART_C
   DYNread(f, (DYNptr) ad);
#endif
#ifdef DEBUG
    fprintf(STD,"C_fork2mgr_ad:"SRC":ad = (%d %d %d %d %d %d)\n", 
    ad->visited, ad->explored, ad->level, ad->transitions, ad->deadlocks, 
    ad->ticks);
    FFLUSH
#endif
}

static void C_mgr2fork_string(file_t f, char **s) {
#ifdef MGRSTART_C
   printUTF(f, *s); fflush(f); 
#endif
#ifdef FORK_C
   *s = strdup(readstringUTF(f));
#endif
#ifdef DEBUG
    fprintf(STD,"C_mgr2fork_string:"SRC":"); 
    fprintf(STD," %s\n", *s); FFLUSH
#endif
}

static void C_fork2mgr_act(file_t f,  act_t *act) {
#ifdef FORK_C
     fwrite(act,  sizeof(act_t), 1, f);  fflush(f);
#endif
#ifdef MGRSTART_C
     fread(act,sizeof(act_t), 1, f); 
#endif
#ifdef DEBUG
    fprintf(stdout,"C_fork2mgr_act:"SRC":lab = %d\n", act->lab);
    fflush(stdout);
#endif
}
#undef str
#undef SRC
#undef STD
#ifdef DEBUG
#undef DEBUG
#endif
#undef FFLUSH

