/* $Id: memstat.h,v 1.1 2004/01/29 13:17:31 bertl Exp $ */
#ifndef MEMSTAT_H
#define MEMSTAT_H

#include <stdio.h>

struct memstat {
	int size;
	int resident;
	int shared;
	int trs;
	int drs;
	int lrs;
	int dt;
};

extern struct memstat currentmem;
extern struct memstat maxmem;
extern int memstat_enable;

extern void memstat_check();

extern void memstat_warn(int v,struct memstat stats,const char *fmt,...);

#ifdef LINUX
#define MEMSTAT_CHECK memstat_check()
#else
#define MEMSTAT_CHECK {}
#endif

#endif

