dnl Process this file with autoconf to produce a configure script.
AC_REVISION($Id: configure.ac,v 1.37 2008/04/28 14:14:10 bertl Exp $)
AC_PREREQ(2.57)
AC_INIT(src/librww.c)
AC_PREFIX_DEFAULT(`if test $USER = root; then echo /usr/local; \
else echo $HOME; fi`)
RM="${RMPROG-/bin/rm -f}"
AC_SUBST(RM)
if test "${prefix}" = "NONE"
then
    echo "The top directory of this installation will be `pwd`"
else
    echo "The top directory of this installation will be ${prefix}"
fi

dnl Determine machine architecture
AC_CANONICAL_HOST
machine=${host_cpu}

VERSION="2.18.5"
AC_SUBST(VERSION)
AC_MSG_RESULT([Starting to configure version $VERSION])
distdir="${TMPDIR:-/tmp}/mcrl-${VERSION}"
AC_SUBST(distdir)
tmpdir="${TMPDIR:-/tmp}"
AC_SUBST(tmpdir)

AC_PROG_INSTALL
if test "`basename $INSTALL`" = "install-sh"
then
   echo INSTALL=$INSTALL
else
   INSTALL_DATA="$INSTALL_DATA -p"
fi
if test -z "$MAKE" 
then
AC_CHECK_PROG(MAKE,gmake,gmake,make)
fi
if $MAKE -v --no-print-directory>/dev/null 
then
    noprintdirectory="--no-print-directory"
else
    noprintdirectory=""
fi
AC_SUBST(noprintdirectory)
AC_PROG_MAKE_SET

LDFLAGS=${FROM_CONFIG_SITE}

dnl Which compiler will be used
if test -z "${CC}"; then
AC_ARG_ENABLE(cc,
    [  --enable-cc             use cc instead of gcc],
    [
    if test $enableval  = "yes"; then
	    CC=cc
    else
	CC=gcc
    fi
    ])
fi

if test -z "${CFLAGS}"; then
        AC_PROG_CC
        if test "${GCC}" = "yes"; then
	   CFLAGS="-Wno-unused"
        else
           CFLAGS="-g"
        fi
else
        AC_PROG_CC
fi
AC_MSG_RESULT([cc flags: ${CFLAGS}])
AC_FUNC_ALLOCA
AC_MSG_CHECKING([variable array])
AC_COMPILE_IFELSE(
     [[main(){int n= getchar();{int a[n];}}
     ]],[AC_DEFINE(VARARRAY)
         AC_MSG_RESULT([yes])
        ],[AC_MSG_RESULT([no])])
dnl testing for C99 standard
AC_PREPROC_IFELSE(
LCPPFLAGS=${CPPFLAGS}
AC_LANG_SOURCE([
#if defined __STDC_VERSION__ && __STDC_VERSION__ >= 199901L
#else
#include wrong
#endif
]), [
C99=yes],[
	CPPFLAGS="-std=c99"
	AC_PREPROC_IFELSE(
	AC_LANG_SOURCE([
	#if defined __STDC_VERSION__ && __STDC_VERSION__ >= 199901L
	#else
        #include wrong
	#endif
	]), [C99=yes; STDC="${CPPFLAGS}"],
	[C99=no;enable_checker="no";CPPFLAGS=${LCPPFLAGS}])
])
if test $C99 = "yes"; then
   AC_CHECK_DECLS(strdup) 
   AC_CHECK_DECLS(getenv) 
   AC_CHECK_DECLS(putenv)
   CC99="$CC $STDC -DC99=yes"
fi
AC_CHECK_FUNCS(strdup) 
AC_CHECK_FUNCS(getenv) 
AC_CHECK_FUNCS(putenv) 
AC_CHECK_FUNCS(fread_unlocked) 
CPPFLAGS=""
AC_MSG_RESULT([C99 standard: ${C99}])
AC_SUBST(C99)
AC_SUBST(CC99)
AC_SUBST(STDC)
AC_PATH_PROG(CCPATH, ${CC},"")
if test -n "${CCPATH}"; then
    SYSDIR=`dirname ${CCPATH}`
    SYSDIR=`dirname ${SYSDIR}`
    if test "`basename ${SYSDIR}`" = lib ;then
       AC_MSG_RESULT([System library: ${SYSDIR}])
    elif test "`basename ${SYSDIR}`" = lib64 ;then
       AC_MSG_RESULT([System library: ${SYSDIR}])
    else
      SYSDIR=${SYSDIR}/lib
       AC_MSG_RESULT([System library: ${SYSDIR}])
    fi
fi

AC_ISC_POSIX
AC_HEADER_STDC
AC_CHECK_HEADERS(stdint.h)


AC_ARG_WITH(64bit,
   [  --with-64bit            create 64 bit version],,
    )

AC_ARG_WITH(32bit,
   [  --with-32bit            create 32 bit version],,
    )


ARCH='unknown'
case ${machine} in
    mips) ARCH='sgi';AC_DEFINE(SGI) ;;
    sparc) ARCH='sun4';AC_DEFINE(SUN) ;;
    i686* | i586* | i386* | x86_64) ARCH='i686' ;;
    powerpc*) ARCH='powerpc';AC_DEFINE(POWERPC) ;;
    *) AC_MSG_ERROR([This machine is unknown ${machine}]) ;;
esac
if test "${with_32bit+set}" != set
then
   if test ${machine} = "x86_64" -o "${with_64bit+set}" = set
   then
    CC="${CC} -m64"
    CFLAGS="${CFLAGS} -DAT_64BIT"
    AC_MSG_RESULT([64 bits code will be produced])
    ARCH='x86_64'
    LIBNAME=lib64
   fi
else
  if test ${machine} = "x86_64"
  then
     AC_MSG_RESULT([Flag -m32 is added to ${CC} ])
     AC_MSG_RESULT([32 bits code will be produced])
     CC="${CC} -m32"
  fi
  LIBNAME=lib
fi

AC_DEFINE_UNQUOTED(LDFLAGS,"${DYNFLAGS}")
AC_SUBST(ARCH)
AC_SUBST(DYNFLAGS)
dyndir="${TMPDIR:-/tmp}"
AC_SUBST(dyndir)

datadir="${datadir}/mCRL"
exampledir="${datadir}/examples"
docdir="${datadir}/doc"
htmldir="${datadir}/doc/html"
javadir="${datadir}/java"
AC_SUBST(exampledir)
AC_SUBST(docdir)
AC_SUBST(htmldir)
AC_SUBST(javadir)
if test "${TERM}" = "cygwin";
then
    enable_dynlink="no"
    cygwin="yes"
else
    cygwin="no"
AC_ARG_ENABLE(dynlink, [  --disable-dynlink	  no dynamic linking will be used ],, \
    enable_dynlink="yes"
    ) 
fi    
AC_SUBST(cygwin)
test -z "${enable_dynlink}" && enable_dynlink="yes"

if test -z "${DYNFLAGS}" ; then
case ${ARCH} in
    sgi) DYNFLAGS="-shared" ;;
    sun4) DYNFLAGS="-Wl,-dy -Wl,-G" ;;
    i686) DYNFLAGS="-shared"
            if test ${enable_dynlink} = "yes"; then
	    LDFLAGS="$LDFLAGS -rdynamic" 
            fi ;;
    x86_64) DYNFLAGS="-shared -fPIC"
            if test ${enable_dynlink} = "yes"; then
	    LDFLAGS="$LDFLAGS -rdynamic" 
            fi ;;
esac
fi
case "${host_vendor}" in
   apple) DYNFLAGS="-bundle -bundle_loader \$(PROG)"
   ;;
esac 
dnl Dynamic library
if test "${enable_dynlink}" = "yes"; then
case ${machine} in
    hp*) AC_CHECK_HEADER(dl.h,AC_MSG_RESULT([Dynamic linking is supported]), \
	AC_MSG_ERROR([Dynamic linking is not supported]));;
    *) AC_CHECK_HEADER(dlfcn.h,AC_MSG_RESULT([Dynamic linking is supported]),\
		enable_dynlink="no");;
esac
AC_CHECK_LIB(m,dlopen,
    [
    AC_MSG_CHECKING("if -ldl is needed")
    ],
    [
    AC_CHECK_LIB(dl,dlopen,,enable_dynlink="no")
    ]
    )
fi
AC_MSG_RESULT([Dynamic linking used? ${enable_dynlink}])

 
AC_ARG_ENABLE(zlib, [  --disable-zlib	  no zlib will be used ],, \
    enable_zlib="yes")

if test "${enable_zlib}" = "yes"; then    
AC_CHECK_HEADERS(zlib.h,[
   AC_CHECK_LIB(z,gzopen,,AC_MSG_RESULT([Library libz.a is not available])) 
], AC_MSG_RESULT([Include file zlib.h is not available]))
else
   AC_MSG_RESULT([No zlib will be used])
fi

FROM_CONFIG_SITE=${LDFLAGS}

# end test with aterm
# debug: AC_MSG_RESULT([CPPFLAGS=$CPPFLAGS])
# debug: AC_MSG_RESULT([LDFLAGS=$LDFLAGS])

if test "${GCC}" = "yes"; then
    AC_PATH_PROG(LEXDIR, flex)
    LEXDIR=`dirname ${LEXDIR}`
    LEXDIR=`dirname ${LEXDIR}`/$LIBNAME
    LDFLAGS="-L${LEXDIR} ${LDFLAGS}"
fi
AC_PROG_LEX
AC_PROG_YACC
AC_ARG_ENABLE(debug, [  --enable-debug	  sets debugging mode ],, \
    test -z "${enable_debug}" && enable_debug="yes")

AC_ARG_ENABLE(profile, [  --enable-profile	  sets profiling mode ],, \
    test -z "${enable_profile}" && enable_profile="no")

AC_ARG_ENABLE(development, [  --enable-development	  development version ],, \
    test -z "${enable_development}" && enable_development="no")

AC_ARG_ENABLE(instrumented, [  --enable-instrumented	  instrumented version ],, \
    test -z "${enable_instrumented}" && enable_instrumented="no")

dnl Define defs
if test "${enable_dynlink}" = "yes"; then
    AC_DEFINE(DYNLINK)
fi
DEVELOPMENT=${enable_development}
AC_SUBST(DEVELOPMENT)
if test "${enable_development}" = "yes"; then
    AC_DEFINE(DEVELOPMENT,1,[aap])
    AC_DEFINE(LINUX)
fi
if test "${enable_instrumented}" = "yes"; then
    AC_DEFINE(INSTRUMENTED)
fi
AC_DEFINE_UNQUOTED(CC,"${CC}")
AC_DEFINE_UNQUOTED(CFLAGS,"${CFLAGS}")
AC_DEFINE_UNQUOTED(VERSION,"${VERSION}")
AC_DEFINE_UNQUOTED(DATADIR,"${datadir}")

dnl Go on with flags
AC_ARG_ENABLE(simulator, [  --disable-simulator	  no simulator will be installed ],, \
    enable_simulator="yes")
    
AC_ARG_ENABLE(jsim, [  --disable-jsim	  no java simulator will be installed ],, \
    enable_jsim="yes")
    
AC_ARG_ENABLE(svc, [  --disable-svc		  no interface to svc library will be installed ],, \
${MAKE} -v -f/dev/null >/dev/null  &&  enable_svc="yes")

if test "${enable_svc}" = "yes"; then
    AC_DEFINE(SVC)
    AC_ARG_ENABLE(svctools, [  --disable-svctools	  no svc tools will be installed ],, \
    test -z "${enable_svctools}" && ${MAKE} -v -f/dev/null >/dev/null  && \
    enable_svctools="yes")
fi

test -z "${enable_svctools}" && enable_svctools="no"

AC_ARG_ENABLE(prover, [  --disable-prover	  no prover will be installed ],, \
    test -z "${enable_prover}"  && enable_prover="yes")
test -z "${enable_prover}" && enable_prover="no"

if test -d java; then 
AC_ARG_ENABLE(grappa, [  --disable-grappa	  no stateviewer will be installed ],, \
    test -z "${enable_grappa}" && \
    enable_grappa="yes")
fi
test -z "${enable_grappa}" && enable_grappa="no"

if test -d checker; then 
AC_ARG_ENABLE(checker, [  --disable-checker	  no mu-calculus checker will be installed ],, \
    test -z "${enable_checker}" && \
    enable_checker="yes")
fi
test -z "${enable_checker}" && enable_checker="no"

if test ${enable_checker} = "yes"; then
      AC_CHECK_HEADERS([getopt.h],,enable_checker="no")
fi

if test -d absint; then 
AC_ARG_ENABLE(absint, [  --disable-absint	  no abstract interpretation ],, \
    test -z "${enable_absint}" && \
    enable_absint="yes")
fi
test -z "${enable_absint}" && enable_absint="no"

AC_ARG_ENABLE(cadp,   [  --disable-cadp	  no cadp libraries will be linked ],, \
    test -z "${enable_cadp}" -a -d mcrlopen && \
    enable_cadp="yes")
test -z "${enable_cadp}" && enable_cadp="no"

if test -z "${CADP}"; then
    enable_cadp="no"
fi
if test ! -x ${CADP}/com/arch; then
    enable_cadp="no"
fi

AC_ARG_ENABLE(aterm,   [  --enable-aterm2	  a newer aterm library linked ],, \
    test -z "${enable_aterm2}" -a -d aterm && \
    enable_aterm2="yes")
test -z "${enable_aterm2}" && enable_aterm2="yes"
AC_MSG_RESULT([${enable_aterm2}])
if test "${enable_aterm2}" = "yes"; then
    ATERM="aterm2"
else
    ATERM="aterm"
fi

hek='\#'
AC_PATH_PROG(JW, jw, $hek )

if test "${enable_grappa}" = "yes"; then
    AC_PATH_PROG(DOT, dot,"")
    if test -n "${DOT}" && java -cp .:./java/grappa.jar ClassPresent att.grappa.Graph; then
	   AC_DEFINE(GRAPPA)
           GRAPPAMAKEFILES="java/Makefile"
    else
       enable_grappa="no"
    fi
fi
AC_MSG_CHECKING([Java, Dot, and Grappa available])
AC_MSG_RESULT([${enable_grappa}])

AC_ARG_ENABLE(developer, [  --disable-developer	  no developers directory will be installed ],, \
    test -z "${enable_developer}" && \
    enable_developer="yes")

if test ! -d stst; then
    enable_developer="no"
fi
if test -z "${enable_developer}" &&  -d stst && -d explicit ; then
    enable_developer="yes"
fi
if test "${enable_cadp}" = "yes"
then
    CPPFLAGS="${CPPFLAGS} -I${CADP}/incl" 
    AC_DEFINE(USE_BCG)
fi
if test "${enable_debug}" = "no"; then
        AC_MSG_RESULT("Variable NDEBUG is defined")
	CFLAGS="-DNDEBUG ${CFLAGS}"
else
        AC_MSG_RESULT("Variable NDEBUG is undefined")
fi
if test "${enable_profile}" = "no"; then
        AC_MSG_RESULT("No profile option is set")
else
        AC_MSG_RESULT("Profile option -pg is set")
	CFLAGS="-pg ${CFLAGS}"
	LDFLAGS="-pg ${LDFLAGS}"
        FROM_CONFIG_SITE="-pg ${FROM_CONFIG_SITE}"
fi

if test "${enable_simulator}" = "yes"; then
    AC_PATH_XTRA
    LDFLAGS="${LDFLAGS} ${X_LIBS} ${X_EXTRA_LIBS} -lX11 ${X_PRE_LIBS} -lm" 
    if test "${no_x}" = "yes"
    then
       enable_simulator=no
    fi
fi

if test ${enable_simulator} = "yes"; then
   enable_simulator=test
fi
LIBSOLD=$LIBS
LIBS=""

while test "${enable_simulator}" = "test"; do
# Check for TCL library and header files

AC_ARG_WITH(
  [tcl],
  AC_HELP_STRING(
    [[[[--with-tcl=dir@<:@,suf@:>@]]]],
    [use tcl headers from dir/include@<:@/suf@:>@ and the tcl library from
     dir/lib@<:@/suf@:>@
    ]
  )
)
if test $with_tcl; then
  TCL_ROOT=$(echo $with_tcl, | cut -d, -f1)
  TCL_SUFFIX=$(echo $with_tcl, | cut -d, -f2)
  if test $TCL_ROOT; then
    if test $TCL_SUFFIX; then
      tclinclude="$TCL_ROOT/include/$TCL_SUFFIX"
      tcllib="$TCL_ROOT/$LIBNAME/$TCL_SUFFIX"
    else
      tclinclude="$TCL_ROOT/include"
      tcllib="$TCL_ROOT/$LIBNAME"
    fi
  fi
fi
# end test with tcl

if test "${TCL_ROOT}"; then
# Checks for header files.
    CPPFLAGS="-I$tclinclude $CPPFLAGS"
    AC_CHECK_HEADERS([tcl.h], , [enable_simulator=no])
    if test $enable_simulator = "no"; then
         break
    fi
    AC_MSG_CHECKING("Find library belonging to tcl.h")
     if test -z "${TCL}";
     then
        TCL=tcl
     fi
     AC_MSG_RESULT("Found:$TCL")
# Checks for libraries
   LDFLAGS="$LDFLAGS -L$tcllib"
   AC_CHECK_LIB([$TCL], [Tcl_AppendResult], 
        [ LDFLAGS="$LDFLAGS -l${TCL}"],
        [enable_simulator=no]) 
    if test ${enable_simulator} = "no"; then
         break
    fi
else
    AC_CHECK_HEADERS([tcl.h], , [enable_simulator=no])
    if test ${enable_simulator} = "no"; then
    AC_PATH_PROG(WISH, wish,"")
	    if test "${WISH}"; then
	      TCLDIR=`dirname ${WISH}`
	      TCLDIR=`dirname  ${TCLDIR}`
	    else
		TCLDIR=/usr/local
	    fi
    else
      TCLDIR=/usr
    fi
    CPPFLAGS="-I${TCLDIR}/include $CPPFLAGS" 
    if test ${enable_simulator} = "no"; then
        break
    fi
    tcllib=$TCLDIR/$LIBNAME
    if test -z "${TCL}"; then
        TCL=tcl
    fi
    LDFLAGS="$LDFLAGS -L$tcllib"
    AC_CHECK_LIB([$TCL], [Tcl_AppendResult],
       [ LDFLAGS="$LDFLAGS -l${TCL}"],
       [AC_CHECK_LIB([tcl], [Tcl_AppendResult],
       [LDFLAGS="$LDFLAGS -ltcl"],enable_simulator=no)
       ])
    if test ${enable_simulator} = "no"; then
         break
    fi
fi
if test "${tcllib}" != "${SYSDIR}"; then
    if test "${GCC}" = "yes"; then
	LDFLAGS="-Xlinker -L$tcllib $LDFLAGS"
    else
	LDFLAGS="-R$tcllib $LDFLAGS"
    fi
fi

# Check for TK library and header files
AC_ARG_WITH(
  [tk],
  AC_HELP_STRING(
    [[[[--with-tk=dir@<:@,suf@:>@]]]],
    [use tk headers from dir/include@<:@/suf@:>@ and the tk library from
     dir/lib@<:@/suf@:>@
    ]
  )
)
if test $with_tk; then
  TK_ROOT=$(echo $with_tk, | cut -d, -f1)
  TK_SUFFIX=$(echo $with_tk, | cut -d, -f2)
  if test $TK_ROOT; then
    if test $TK_SUFFIX; then
      tkinclude="$TK_ROOT/include/$TK_SUFFIX"
      tklib="$TK_ROOT/$LIBNAME/$TK_SUFFIX"
    else
      tkinclude="$TK_ROOT/include"
      tklib="$TK_ROOT/$LIBNAME"
    fi
  fi
fi
# end test with tk
# debug: AC_MSG_RESULT([CPPFLAGS=$CPPFLAGS])
# debug: AC_MSG_RESULT([LDFLAGS=$LDFLAGS])

if test "${TK_ROOT}"; then
# Checks for header files.
    CPPFLAGS="-I$tkinclude $CPPFLAGS"
    AC_CHECK_HEADERS([tk.h], , [enable_simulator=no]) 
    AC_MSG_CHECKING("Find library belonging to tk.h")
    TK=tk
    AC_MSG_RESULT($TK)
# Checks for libraries
   LDFLAGS="$LDFLAGS -L$tklib"
   AC_CHECK_LIB([$TK], [Tk_MainLoop],
       [LDFLAGS="$LDFLAGS -l${TK}"],
       [enable_simulator=no])
    if test ${enable_simulator} = "no"; then
         break
    fi
else
    TKDIR=$TCLDIR
    CPPFLAGS="-I${TKDIR}/include $CPPFLAGS" 
    AC_CHECK_HEADERS([tk.h], , [enable_simulator=no])
    if test ${enable_simulator} = "no"; then
       break
    fi
    tklib=$TKDIR/$LIBNAME
    TK=tk
    LDFLAGS="$LDFLAGS -L$tklib"
   AC_CHECK_LIB([$TK], [Tk_MainLoop], 
       [LDFLAGS="$LDFLAGS -l${TK}"],[
       AC_CHECK_LIB([tk], [Tk_MainLoop], 
       [LDFLAGS="$LDFLAGS -ltk"],[enable_simulator=no])
       ]) 
    if test ${enable_simulator} = "no"; then
         break
    fi
fi
if test "${tklib}" != "${SYSDIR}"; then
    if test "${GCC}" = "yes"; then
	LDFLAGS="-Xlinker -L$tklib $LDFLAGS"
    else
	LDFLAGS="-R$tklib $LDFLAGS"
    fi
fi
TCLLIBS=$LDFLAGS
AC_MSG_RESULT([Output variable TCLLIBS: ${TCLLIBS}])
AC_SUBST(TCLLIBS)
enable_simulator=yes
AC_MSG_RESULT([Installation of toolset with simulator])
done
if test ${enable_simulator} = "no"; then
AC_MSG_RESULT([Installation of toolset without simulator])
fi
#end simulator
LIBS=$LIBSOLD

# Check for ATerm library and header files
AC_ARG_WITH(
  [aterm],
  AC_HELP_STRING(
    [[[[--with-aterm=dir@<:@,suf@:>@]]]],
    [use ATerm headers from dir/include@<:@/suf@:>@ and the ATerm library from
     dir/lib@<:@/suf@:>@
    ]
  )
)
if test ${with_aterm}; then
  ATERM_ROOT=$(echo $with_aterm, | cut -d, -f1)
  ATERM_SUFFIX=$(echo $with_aterm, | cut -d, -f2)
  if test "${ATERM_ROOT}"; then
    if test "${ATERM_SUFFIX}"; then
      aterminclude="${ATERM_ROOT}/include/${ATERM_SUFFIX}"
      atermlib="${ATERM_ROOT}/lib/${ATERM_SUFFIX}"
    else
      aterminclude="${ATERM_ROOT}/include"
      atermlib="${ATERM_ROOT}/lib"
    fi
    LDFLAGS="$LDFLAGS -L$atermlib"
    CPPFLAGS="-I$aterminclude $CPPFLAGS"
  fi
fi 
if test "${ATERM_ROOT}"; then
# Checks for libraries
   AC_CHECK_LIB([ATerm], [ATinit], , [AC_MSG_ERROR([cannot find ATerm library])])
LIBS="-L$atermlib $LIBS"
# Checks for header files.
   AC_CHECK_HEADERS([aterm2.h], , [AC_MSG_ERROR([cannot find ATerm headers])])
else
    CPPFLAGS="-I\${top_srcdir}/${ATERM} $CPPFLAGS"
fi
CPPFLAGS="$CPPFLAGS -I\${top_srcdir}" 


if test -z "$atermlib"; then
   LIBS="-L\${top_srcdir}/${ATERM} -lATerm $LIBS"
   atermlib='${exec_prefix}/mCRL/lib'
   aterminclude='${prefix}/mCRL/include'
   atermlocallib='${top_srcdir}'/${ATERM}/libATerm.a
fi
AC_SUBST(atermlocallib)
AC_SUBST(atermlib)
AC_SUBST(aterminclude)
AC_SUBST(ATERM)

#end aterm library
LIBS="-L\${top_srcdir} -lmcrlunix $LIBS"

#AC_SUBST(CCFLAGS)

#NO CHECKS ARE ALLOWED ANYMORE
LDFLAGS=${FROM_CONFIG_SITE}
SIMULATOR=${enable_simulator}
AC_SUBST(SIMULATOR)
SVC=${enable_svc}
AC_SUBST(SVC)
SVCTOOLS=${enable_svctools}
AC_SUBST(SVCTOOLS)
PROVER=${enable_prover}
AC_SUBST(PROVER)
CAESAR=${enable_cadp}
AC_SUBST(CAESAR)

dnl Update LIBS variable
if test "${enable_svc}" = "yes"; then
    LIBS="${LIBS}  -L\${top_srcdir}/svc/src -lsvc"
fi
if test "${enable_cadp}" = "yes"
then
    LIBS="${LIBS} -L"${CADP}/bin.`${CADP}/com/arch`" -lBCG_IO -lBCG -lm"
fi
dnl Update CPPFLAGS 

dnl Create makefiles
MCRLMAKEFILES="Makefile ${ATERM}/Makefile lin/Makefile src/Makefile src/Rww data/Makefile doc/Makefile"
if test -d doc/src
then
     MCRLMAKEFILES="$MCRLMAKEFILES doc/src/Makefile"
fi
if test "${enable_svc}" = "yes"
then
    AC_MSG_RESULT([SVC library available? ${enable_svc}])
    SVCMAKEFILES="svc/Makefile svc/src/Makefile svc/man/Makefile"
else
    AC_MSG_RESULT([SVC library available? ${enable_svc}])
fi
if test "${enable_svctools}" = "yes"
then
    AC_MSG_RESULT([SVC tools available? ${enable_svctools}])
    SVCTOOLSMAKEFILES="svctools/Makefile svctools/src/Makefile svctools/man/Makefile"
else
    AC_MSG_RESULT([SVC tools available? ${enable_svctools}])
fi
if test "${enable_prover}" = "yes"
then
    AC_MSG_RESULT([Prover available? ${enable_prover}])
    PROVERMAKEFILES="prover/Makefile prover/src/Makefile prover/man/Makefile prover/doc/Makefile"
else
    AC_MSG_RESULT([Prover available? ${enable_prover}])
fi

if test "${enable_cadp}" = "yes"
then
    AC_MSG_RESULT([Caesar link (mcrl_open) available? ${CAESAR}])
    AC_CONFIG_FILES([mcrlopen/mcrl_open], 
           [chmod a+x mcrlopen/mcrl_open])
    MCRLOPENFILES="mcrlopen/mcrl_open mcrlopen/Makefile"
else
    AC_MSG_RESULT([Caesar link (mcrl_open) available? ${CAESAR}])
fi
if test "${enable_jsim}" = "yes" -a -d explicit
then
        AC_PATH_PROG(JAVA, "java", "")
        if test -n "${JAVA}" && ${JAVA} TestJava
        then
	    JSIM1="explicit/jsim/Makefile"
        AC_CONFIG_FILES([explicit/jsim/jsim], 
           [chmod a+x explicit/jsim/jsim])
        AC_CONFIG_FILES([explicit/jsim/contact], 
           [chmod a+x explicit/jsim/contact])
          AC_PATH_PROG(JAVAC, "javac", "")
         else
	    enable_jsim="no"
	    AC_MSG_RESULT([Installation without jsim])
         fi
fi
AC_MSG_RESULT([Jsim available? ${enable_jsim}])
JSIM=${enable_jsim}
AC_SUBST(JSIM)
IMPLICIT="no"
if test -d implicit
then
	IMPLICIT0="implicit/Makefile"
	IMPLICIT1="implicit/src/Makefile"
	IMPLICIT="yes"
fi
AC_SUBST(IMPLICIT)
EXPLICIT="no"
if test -d explicit
then
	EXPLICIT0="explicit/Makefile"
	EXPLICIT1="explicit/src/Makefile"
	EXPLICIT2="explicit/ltsmin/Makefile"
	EXPLICIT="yes"
        AC_MSG_RESULT([Development? ${enable_development}])
	if test "${enable_development}" = "yes"
        then
           AC_DEFINE(LINUX)
        fi
fi
AC_SUBST(EXPLICIT)
if test "${enable_grappa}" = "yes" -a -d java
then
    AC_MSG_RESULT([Grappa available? ${enable_grappa}])
else
    AC_MSG_RESULT([Grappa avaliable? ${enable_grappa}])
fi
GRAPPA=${enable_grappa}
AC_SUBST(GRAPPA)
if test "${enable_checker}" = "yes" -a -d checker
then
    AC_MSG_RESULT([Checker available? ${enable_checker}])
    CHECKERMAKEFILES="checker/Makefile checker/src/Makefile checker/doc/Makefile"
else
    AC_MSG_RESULT([Checker available? ${enable_checker}])
fi
CHECKER=${enable_checker}
AC_SUBST(CHECKER)
if test "${enable_absint}" = "yes" -a -d absint
then
    AC_MSG_RESULT([Absint available? ${enable_absint}])
    ABSINTMAKEFILES="absint/Makefile absint/src/Makefile absint/doc/Makefile"
else
    AC_MSG_RESULT([Absint available? ${enable_absint}])
fi
ABSINT=${enable_absint}
AC_SUBST(ABSINT)
AC_PATH_PROG(TEST, test,"")
AC_PATH_PROG(XMLTO, "xmlto", "")
MAKEFILES="$MCRLMAKEFILES $SVCMAKEFILES $SVCTOOLSMAKEFILES $PROVERMAKEFILES \
$MCRLOPENFILES $EXPLICIT0 $EXPLICIT1 $EXPLICIT2 $JSIM1 \
$IMPLICIT0 $IMPLICIT1 \
$GRAPPAMAKEFILES $CHECKERMAKEFILES $ABSINTMAKEFILES" 
AC_CONFIG_HEADERS([config.sh:config.in])
CONFIG1="config.in:config.hin"
CONFIG2="config.in:config.hin"
includedir='${prefix}/mCRL/include'
libdir='${exec_prefix}/mCRL/lib'
libexecdir='${exec_prefix}/mCRL/libexec'
if test $cache_file != /dev/null -a $TEST -a -f Makefile -a Makefile -nt configure
then
if $TEST ! -f config.in -o config.hin -nt config.in
then
    AC_CONFIG_FILES([$CONFIG1])
fi
for F in $MAKEFILES
do
if $TEST ! -f $F -o "$F.in" -nt $F
then
     AC_CONFIG_FILES([$F])
fi
done
AC_OUTPUT
else
AC_CONFIG_FILES([$CONFIG2])
AC_CONFIG_FILES([$MAKEFILES])
AC_OUTPUT
fi
if test $cache_file != /dev/null -a $TEST -a -f config.h -a config.h -nt configure
then
if $TEST ! -f config.h -o config.hin -nt config.h
then
    sed -e 1d  config.sh|/bin/sh
    AC_MSG_RESULT([Creating config.h])
else
    AC_MSG_RESULT([config.h is unchanged])
fi
else
    sed -e 1d  config.sh|/bin/sh
    AC_MSG_RESULT([Creating config.h])
fi
AC_MSG_RESULT([Configure successfully finished])
AC_MSG_RESULT(
[For compiling, linking, and installing the toolset, enter ${MAKE} install]
)
