/* $Id: memstat.c,v 1.2 2004/04/29 09:58:29 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "memstat.h"
#ifdef LINUX
#include <unistd.h>
#include <sys/types.h>
#endif

#include <stdlib.h>
#include <stdarg.h>
#include "messages.h"

/*
 File     Content                         
 size     total program size              
 resident size of memory portions         
 shared   number of pages that are shared 
 trs      number of pages that are 'code' 
 drs      number of pages of data/stack   
 lrs      number of pages of library      
 dt       number of dirty pages         
*/


struct memstat currentmem;
struct memstat maxmem={0};
int memstat_enable=0;

void memstat_check(){
#ifdef LINUX
	FILE* statm;
	if(!memstat_enable) return;
	statm=fopen("/proc/self/statm","r");
	fscanf(statm,"%d%d%d%d%d%d%d",&currentmem.size,&currentmem.resident,
		&currentmem.shared,&currentmem.trs,&currentmem.drs,&currentmem.lrs,&currentmem.dt);
	fclose(statm);
	if (currentmem.size > maxmem.size ) maxmem.size = currentmem.size ;
	if (currentmem.resident > maxmem.resident ) maxmem.resident = currentmem.resident ;
	if (currentmem.shared > maxmem.shared ) maxmem.shared = currentmem.shared ;
	if (currentmem.trs > maxmem.trs ) maxmem.trs = currentmem.trs ;
	if (currentmem.drs > maxmem.drs ) maxmem.drs = currentmem.drs ;
	if (currentmem.lrs > maxmem.lrs ) maxmem.lrs = currentmem.lrs ;
	if (currentmem.dt > maxmem.dt ) maxmem.dt = currentmem.dt ;
#else
	Fatal(1,1,"memstat check on unsupported machine");
#endif
}

void memstat_warn(int v,struct memstat stats,const char *fmt,...){
#ifdef LINUX
	// common to all memstat implementations.
	va_list args;
	char prefix[1024];
	int pagesz=sysconf(_SC_PAGE_SIZE);

	va_start(args,fmt);
	vsprintf(prefix,fmt,args);
	va_end(args);
#endif

#ifdef LINUX
	// Linux specific part.
	if (memstat_enable){
		Warning(v,"%s: %8u total program size",prefix,stats.size*pagesz);
		Warning(v,"%s: %8u resident",prefix,stats.resident*pagesz);
		Warning(v,"%s: %8u shared",prefix,stats.shared*pagesz);
		Warning(v,"%s: %8u code",prefix,stats.trs*pagesz);
		Warning(v,"%s: %8u data/stack",prefix,stats.drs*pagesz);
		Warning(v,"%s: %8u library",prefix,stats.lrs*pagesz);
		Warning(v,"%s: %8u dirty pages",prefix,stats.dt);
		Warning(v,"%s: %8u page size",prefix,pagesz);
	} else {
		Warning(v,"%s: memstat disabled",prefix);
	}
#endif
}


