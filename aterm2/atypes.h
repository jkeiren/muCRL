#ifndef ATYPES_H
#define ATYPES_H

#include "abool.h"

#ifdef __cplusplus
extern "C"
{
#endif/* __cplusplus */

typedef unsigned int ShortHashNumber;

typedef long MachineWord;
typedef unsigned long HashNumber;

#ifdef AT_64BIT
#define SIZEOF_LONG     8 
#define SIZEOF_VOID_P     8 
#define ALIGNOF_VOID_P 8
#define ADDR_TO_SHORT_HNR(a) ((ShortHashNumber)(((((unsigned long)(char*)(a)) >> 2)&0xffffffff) ^ (((unsigned long)(char*)(a)) >> 34)))
#else
#define SIZEOF_LONG     4
#define SIZEOF_VOID_P     4 
#define ALIGNOF_VOID_P 4
#define ADDR_TO_SHORT_HNR(a) (((ShortHashNumber)(char*)(a)) >> 2)
#endif /* AT_64BIT */

#define ADDR_TO_HNR(a) (((HashNumber)(a)) >> 2)

#ifdef __cplusplus
}
#endif/* __cplusplus */ 

#endif /* ATYPES_H */
