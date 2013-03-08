/* $Id: messages.h,v 1.1 2004/01/29 13:17:31 bertl Exp $ */
#ifndef MESSAGES_H
#define MESSAGES_H

extern int verbosity;

extern void Warning(int v,const char *fmt,...);
extern void WarningCall(int v,const char *fmt,...);
extern void Fatal(int code,int v,const char *fmt,...);
extern void FatalCall(int code,int v,const char *fmt,...);


#endif
