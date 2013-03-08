/* SVC tools -- the SVC (Systems Validation Centre) tool set

   Copyright (C) 2000  Stichting Mathematisch Centrum, Amsterdam,
                       The  Netherlands

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

 $Id: svcconf.h,v 1.1.1.1 2004/09/07 15:06:33 uid523 Exp $ */

#include <stdio.h> 
#include <stdlib.h>
#include <string.h>
#include "svc.h"

#include <assert.h>

/* #define PARAMETER */

typedef struct statetype
{ SVCint list1;
  SVCint list2;
  SVCstateIndex old_index;
} statetype;

typedef struct transitiontype
{ SVCstateIndex source;
  SVCstateIndex target;
  SVClabelIndex label;
#ifdef PARAMETER
  SVCparameterIndex parameter;
#endif
  SVCint list1_next;
  SVCint list2_next;
  SVCint hashtable_next;
  SVCint stack_next;
  short candidate;
  short on_stack;
} transitiontype;


