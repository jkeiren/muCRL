/* $Id: tree_db.h,v 1.9 2006/05/17 08:08:42 bertl Exp $ */
#ifndef TREE_DB_H
#define TREE_DB_H

typedef void *trdb_t;
trdb_t TRDBcreate(int id, int width);
elm_t *TRDBput(trdb_t trdb, elm_t *dest);
elm_t *TRDBget(trdb_t trdb, elm_t *src);
unsigned long  TRDBgetByteSize(trdb_t trdb);
unsigned long  TRDBgetEntrieCount(trdb_t trdb);
#endif
