/* this file is temporary, and will be subsumed by 
   libmcrl */

void Init_signature(ATerm signature, int argc,char *argv[]);

#ifdef MCRLLIB
void SignatureSetArguments(int *argc,char ***argv);
void SignatureInitialize(void);
#endif

void Declare_vars(ATermList vars);

ATerm Sort_of(ATerm t);
ATerm Is_var(ATerm t);
ATerm Is_func(ATerm t);
ATerm Is_map(ATerm t);

char Is_eq(ATerm t);
char Is_ite(ATerm t);

ATerm prettyprint(ATerm t);
ATerm parse(ATerm t);
ATermList prettyprint_decls(ATermList t);
ATermList parse_decls(ATermList t);

ATermList generate_reflexivities();

extern ATerm prTRUE;
extern ATerm prFALSE;
extern ATerm prBOOL;

ATerm prEQ(ATerm t, ATerm s);
ATerm prAND(ATerm t, ATerm s);
ATerm prOR(ATerm t, ATerm s);
ATerm prIMPLIES(ATerm t, ATerm s);
ATerm prNOT(ATerm t);
ATerm prITE(ATerm e, ATerm high, ATerm low);

ATerm read_formula(FILE* fp);
void SignatureAddMap(char *name,ATermList args,ATerm sort);
/* The use of this function will be disabled in the future */
