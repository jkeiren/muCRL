/* $Id: inst_fork.h,v 1.4 2006/11/16 14:55:04 bertl Exp $ */
#define str(s) #s
/* #define DEBUG */
#ifdef FORK_C
#define SRC str(fork)
#endif
#ifdef DINSTANTIATE_C
#define SRC str(dinstantiate)
#endif

static void C_inst2fork_tag(file_t f, int *tag) {
#ifdef DINSTANTIATE_C
     if (fputc(*tag, f)<0) errormsg("inst2fork:fputc(tag)"); // fflush(f);
#endif
#ifdef FORK_C
    *tag = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(stdout,"C_inst2fork_tag:"SRC":tag = %c\n", *tag);
    fflush(stdout);
#endif
}

static void C_inst2fork_seg(file_t f, int *segment) {
#ifdef DINSTANTIATE_C
     if (fputc(*segment, f)<0) errormsg("inst2fork:fputc(segment)"); 
     if (fflush(f)<0) errormsg("inst_fork:fflush");
#endif
#ifdef FORK_C
    *segment = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(stdout,"C_inst2fork_seg:"SRC":segment = %d\n", *segment);
    fflush(stdout);
#endif
}

static void C_fork2inst_seg(file_t f, int *segment) {
#ifdef FORK_C
     if (fputc(*segment, f)<0) errormsg("fork2inst_seg:fputc(segment)"); 
     if (fflush(f)<0) errormsg("fork2inst_seg:fflush"); 
#endif
#ifdef DINSTANTIATE_C
    *segment = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(stdout,"C_fork2inst_seg:"SRC":segment = %d\n", *segment);
    fflush(stdout);
#endif
}

static void C_fork2inst_tag(file_t f, int *tag) {
#ifdef FORK_C
     if (fputc(*tag, f)<0) errormsg("fork2inst_tag:fputc(segment)");  
     if (fflush(f)<0) errormsg("fork2inst_tag:fflush"); 
#endif
#ifdef DINSTANTIATE_C
    *tag = fgetc(f);
#endif
#ifdef DEBUG
    fprintf(stdout,"C_fork2inst_tag:"SRC":segment = %d\n", *tag);
    fflush(stdout);
#endif
}

static void C_inst2fork_act(file_t f,  act_t *act) {
#ifdef DINSTANTIATE_C
     fwrite(act,  sizeof(act_t), 1, f);  fflush(f);
#endif
#ifdef FORK_C
     fread(act,sizeof(act_t), 1, f); 
#endif
#ifdef DEBUG
    fprintf(stdout,"C_inst2fork_act:"SRC":lab = %d\n", act->lab);
    fflush(stdout);
#endif
}

static size_t C_inst2fork_visited(file_t f, visited_t *visited) {
#ifdef DEBUG
    fprintf(stdout,"C_inst2fork_visited:"SRC"%d %d %d %d\n",
    visited->dest[0], visited->dest[1], visited->c.act, visited->c.idx);
    fflush(stdout);
#endif
#ifdef DINSTANTIATE_C
   return DYNwrite(f, (DYNptr) visited);/*fflush(f);*/ 
#endif
#ifdef FORK_C
   return DYNread(f, (DYNptr) visited);
#endif
}

static void C_fork2inst_unexplored(file_t f, unexplored_t *unexplored) {
#ifdef FORK_C
   // fprintf(stderr,"DYNwrite\n");
   DYNwrite(f, (DYNptr) unexplored);/*fflush(f);*/ 
#endif
#ifdef DINSTANTIATE_C
   // fprintf(stderr,"DYNread\n");
   DYNread(f, (DYNptr) unexplored);
#endif
#ifdef DEBUG
    fprintf(stdout,"C_inst2fork_unexplored:"SRC"%d %d %d %d\n",
    visited->dest[0], visited->dest[1], visited->c.act, visited->c.idx);
    fflush(stdout);
#endif
}

static void C_inst2fork_int(file_t f, int *idx) {
#ifdef DINSTANTIATE_C
     if (writeintUTF(f, *idx)<0) errormsg("inst2fork_int:writeintUTF(idx)");  
     if (fflush(f)<0) errormsg("inst2fork_int:fflush");  
#endif
#ifdef FORK_C
     readintUTF(f, idx);
#endif
#ifdef DEBUG
    fprintf(stdout,"C_inst2fork_int:"SRC":idx = %d\n", *idx);
    fflush(stdout);
#endif
}

static void C_fork2inst_long(file_t f, long *n) {
#ifdef FORK_C
     if (writelongUTF(f, *n)<0) errormsg("fork2inst_long:writeintUTF(n)");   
#endif
#ifdef DINSTANTIATE_C
     readlongUTF(f, n);
#endif
#ifdef DEBUG
    fprintf(stdout,"C_fork2inst_long:"SRC":idx = %d\n", *n);
    fflush(stdout);
#endif
}

static void C_inst2fork_ad(file_t f, ad_t *ad) {
#ifdef DINSTANTIATE_C
   DYNwrite(f, (DYNptr) ad); fflush(f);  
#endif
#ifdef FORK_C
   DYNread(f, (DYNptr) ad);
#endif
#ifdef DEBUG
    fprintf(stdout,"C_inst2mgr_ad:"SRC":ad = (%d %d %d %d %d %d)\n", 
    ad->visited, ad->explored, ad->level, ad->transitions, ad->deadlocks, 
    ad->ticks);
    fflush(stdout);
#endif
}

static void C_fork2inst_env(file_t f, env_t *env) {
#ifdef FORK_C
   DYNwrite(f, (DYNptr) env);fflush(f); 
#endif
#ifdef DINSTANTIATE_C
   DYNread(f, (DYNptr) env);
#endif
#ifdef DEBUG
    fprintf(stdout,"C_fork2inst_env:"SRC":env = (%d %d %d %d %d %s)\n", 
    env->nseg, env->restore, env->port, env->nLeft, env->nRight, env->dir);
    fflush(stdout);
#endif
}

static void C_fork2inst_dest(file_t f, char **dest, unsigned int n) {
   int i;
#ifdef FORK_C
   for (i=0;i<n;i++)  printUTF(f, dest[i]); fflush(f); 
#endif
#ifdef DINSTANTIATE_C
   for (i=0;i<n;i++) dest[i]= strdup(readstringUTF(f));
#endif
#ifdef DEBUG
    fprintf(stdout,"C_fork2inst_dest:"SRC":"); 
    for (i=0;i<n;i++) fprintf(stdout," %s", dest[i]);
    fprintf(stdout,"\n"); fflush(stdout);
#endif
}

static void C_fork2inst_string(file_t f, char **s) {
#ifdef FORK_C
   printUTF(f, *s); fflush(f); 
#endif
#ifdef DINSTANTIATE_C
   *s = strdup(readstringUTF(f));
#endif
#ifdef DEBUG
    fprintf(stdout,"C_fork2inst_mcrlargs:"SRC":"); 
    fprintf(stdout," %s\n", *s); fflush(stdout);
#endif
}
#undef str
#undef SRC
#undef DEBUG

