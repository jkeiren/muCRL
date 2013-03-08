#ifndef USECHANGE_H
#define USECHANGE_H

#include "lpo1.h"
#include "finset.h"

void UCinitialize(LPO_t lpo);
void UCdestroy();

FINSET_t Used_in_act_set(LPO_t lpo, int i);
FINSET_t Used_in_next_set(LPO_t lpo, int i);
FINSET_t Used_in_guard_set(LPO_t lpo, int i);
FINSET_t Used_set(LPO_t lpo, int i);
FINSET_t Changed_set(LPO_t lpo, int i);

char Used_in_act(LPO_t lpo, int i, int j);
char Used_in_next(LPO_t lpo, int i, int j);
char Used_in_guard(LPO_t lpo, int i, int j);
char Used_in_act_or_guard(LPO_t lpo, int i, int j);
char Used(LPO_t lpo, int i, int j);
char Changed(LPO_t lpo, int i, int j);

#endif
