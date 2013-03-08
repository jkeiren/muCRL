/*
 * $Log: aut-io.h,v $
 * Revision 1.2  2004/11/23 12:36:17  uid523
 *
 *
 * New release of MCRL toolset.  Version 2.16.0
 *
 * 1 New standard aterm library 2.3
 * 2 mcrl.h sysdep.h aterm2.h can be used in a C++ environment
 * 3 Install will be done in 3 phases
 *    1 configure: (nothing will be build)
 *    2 make all: building de binaries (nothing will be installed)
 *    3 make install: installing the binaries and include files
 * 4  libraries and auxilary binaries will be installed in respectively
 *     the subdirectories lib and libexec of $(exec_prefix)/mCRL
 *    binaries will be installed in $(exec_prefix)/bin
 *    include files will be installed in $(prefix)/mCRL/include
 *    data files will be installed $(prefix)/share/mCRL
 *    No hard search pathes anymore in source code like
 *    #include "mcrl/config.h"
 *
 * Default: $(prefix) is equal to the directory $HOME if $USER is unequal root,
 *  $(prefix) is equal to /usr/local otherwise
 * So the installation tree will be located outside the source tree (MCRLTOOLSET).
 * Installation is not needed if one of the src directories of the
 * source tree (MCRLTOOLSET) is current.
 *
 * Revision 1.1.1.1  2004/09/07 15:06:33  uid523
 * version 2.15.0
 *
 * Revision 1.2  2004/04/29 09:58:28  bertl
 *
 *
 * #include unistd.h is removed (without causing harm)
 *
 * Renaming of "lts.h" to "xlts.h"
 *
 * Revision 1.1  2004/03/23 13:42:28  bertl
 *
 *
 *  	Makefile.in explore.c explore.h instantiator.c instantiator.h
 *  	term_db.h term_db0.c utl.c vector_db.h vector_db0.c:
 * Development and documentation of libraries needed for distributed instantiator
 *
 * lts2dot: Request of Aad: The lts (.aut, .svc) to .dot convertor
 *          with the requested flags and behaviour.
 *          An exception is the -spec flag, this flag must be added in the
 *          future.  For documentation: see lts2dot -help.
 *          This tool replaces svc2dot.
 *
 * aut_io.c aut_io.h lts.c lts.h: These are added to libexplicit.a (comes from ltsmin)
 *
 * Revision 1.1  2004/01/29 13:30:55  bertl
 *
 *
 * Added the tools developed by stefan which are not dependent of mpi
 * The main tool: ltsmin
 *
 * Revision 1.1  2002/02/08 12:14:40  sccblom
 * Just saving.
 *
 */

#ifndef AUT_IO_H
#define AUT_IO_H "$Id: aut-io.h,v 1.2 2004/11/23 12:36:17 uid523 Exp $"

#include <stdio.h>
#include "xlts.h"

extern int readaut(GZfile file,lts_t lts);

extern void writeaut(GZfile file,lts_t lts);

#endif
