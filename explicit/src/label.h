/* $Id: label.h,v 1.1 2004/01/29 13:17:30 bertl Exp $ */

#ifndef LABEL_H
#define LABEL_H


extern int getlabelindex(char *label, int create);

extern char *getlabelstring(int label);

extern int getlabelcount();

#endif
