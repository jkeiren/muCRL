/* $Id: generichash.h,v 1.1 2004/01/29 13:17:30 bertl Exp $ */
#ifndef GENERIC_HASH_H
#define GENERIC_HASH_H

typedef  unsigned long  long ub8;   /* unsigned 8-byte quantities */
typedef  unsigned long  int  ub4;   /* unsigned 4-byte quantities */
typedef  unsigned       char ub1;   /* unsigned 1-byte quantities */

extern ub4 hash_4_1( register ub1 *k, register ub4 length, register ub4 initval);
extern ub4 hash_4_4( register ub4 *k, register ub4 length, register ub4 initval);
extern ub8 hash_8_1( register ub1 *k, register ub8 length, register ub8 initval);
extern ub8 hash_8_8( register ub8 *k, register ub8 length, register ub8 initval);

#endif

