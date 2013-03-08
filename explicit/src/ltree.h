/* $Id: ltree.h,v 1.3 2004/03/11 14:46:53 bertl Exp $ */
#ifndef LEVELED_TREE_H
#define LEVELED_TREE_H

/** @name Leveled Tree
    @doc The leveled tree is parametrized with the type {\tt *FILE}, 
    type {\tt dir_t} and the type {\tt idx_t}. 
    The tree is build in a breadth first way. Each object has a parent. 
    The only objects which have itself as parents are the roots. 
    The tree objects are levelwise stored in a stack. A level determined
    by the length of the object to a root. A root has level $0$.
    There are also crossedges, which are called here joins. They are not
    part of the tree but are seperately stored also levelwise in a stack. 
    Levels can be popped and pushed on the stacks. 
    Each object contains extra information  for example the outgoing label 
    and the destination index. The following pointers play a role: {\it current object pointer},
    {\it current join pointer}, {\it current level pointer}.
    The endpoints of the leveled tree are marked as leaves.
*/

//@{
typedef void *ltr_t;

typedef int (*object_cb)(int idx, void *rec);
typedef int (*parent_cb) (void *rec, int current, int leaf, int marked);
typedef int (*join_cb) (void *trans, int join, idx_t current, int length,
int leaf, int marked);
typedef int (*trace_cb)(void *rec, idx_t current);
typedef int (*mark_cb) (int idx, int join, idx_t endpoint);

/** 
@memo Creates a new leveled_tree
@doc The current object pointer, the current join pointer, 
the current level pointer are undefined (equal to $-1$).
A first new level will be created indexed by level number $0$.
However the pointer to the current level has still the value $-1$.
@param width fixed width of the elements which will be stored in the
leveled tree (number of bytes)
@param file refers to the file in which the buffer will be dumped
@param dir refers to the directory in which checkpoint information will be 
dumped
@return ltr handler 
*/
ltr_t LTRcreateMemo(int width, FILE *file, dir_t dir);


/**
    @param ltr handler
    @return 0 success
    @return <0 failure
*/
int LTRdestroy(ltr_t ltr);

/**
    @param ltr handler
    @return 0 success
    @return <0 failure
*/
int LTRreset(ltr_t ltr);

/** 
@memo Allocates a new level if needed
@doc At succes the level pointer will be increased by one.
@param ltr handler
@return 0 success, a new level is allocated
@return <0 failure, no new level is allocated
*/
int LTRnewLevel(ltr_t ltr);

/** 
@memo Removes the levels two or more higher than the current level.
@doc All objects in level above the current level becomes leaves.
@param ltr handler
@return 0 success
@return <0 failure
*/
int LTRtruncate(ltr_t ltr);

/**
@memo Tests if an object is a leaf object
@param ltr handler
@param idx to object
@return 0 current object is not a leaf object
@return 1 current object is a leaf object
*/
int LTRisLeaf(ltr_t ltr, idx_t idx);

/**
@memo Adds an object to the tree
with {\tt parent} as parent 
@doc If {\tt parent} is equal to the index of this object 
then {\it obj} will be assumed as a root. The {\tt current object pointer}
doesn't change. The object will be added to the highest level, 
whose index must be one higher than the current level.
@param ltr handler
@param parent of {\tt obj}
@param obj input parameter: reference to the memory in which 
the object is placed
@param idx output parameter: reference to the memory in which 
the index will be written ({\tt null} permitted)
@return 0 success
@return <0 failure
*/
int LTRput(ltr_t ltr,  idx_t parent,  void* obj, idx_t *idx);

/**
@memo Gets the current object
@param ltr handler
@param obj output parameter: reference to the memory in which 
the content of the current object will be written
@return 0 success
@return <0 failure
*/
int LTRget(ltr_t ltr,   void *obj);
int LTRgetElm(ltr_t ltr,  idx_t idx, void *obj);
/**
@memo Gets current object pointer
@param ltr handler
@return pointer to current object
*/
idx_t LTRgetCurrent(ltr_t ltr);

/**
@memo Assigns a value to the current object pointer 
@param ltr handler
@param current pointer to object
@return 0 success, the current object is not a root after this operation
@return 1 success, the current object is a root after this operation
@return <0 failure
*/
int LTRsetCurrent(ltr_t ltr, idx_t current);

/**
@memo Gets the lower and upper bound of the current level
@param ltr handler
@param start the lowest index of the objects in the level
@param end the highest index plus one of the objects in the level 
@param startjoin the lowest index of the joins in the level
@param endjoin the highest index plus one of the joins in the level
@param startmark he lowest index of the marks in the level
@param endmark the highest index plus one of the marks in the level  
*/
int LTRgetBounds(ltr_t ltr, idx_t *start, idx_t *end, int *startjoin,
int *endjoin, int *startmark, int *endmark); 

/** 
@memo Gets the parent of an object
@param ltr handler
@param idx index of the object 
@return parent of object
*/
idx_t LTRgetParent(ltr_t ltr, idx_t idx);


/**
@param ltr handler
@return number of objects in {\it ltr}
*/
int LTRgetNumberOfObjects(ltr_t ltr);

/**
@param ltr handler
@return number of levels
*/
int LTRgetNumberOfLevels(ltr_t ltr);

/**
@param ltr handler
@return number of all levels included the levels which are popped from the
stack
*/
int LTRgetNumberOfAllLevels(ltr_t ltr);

/** 
@memo Dumps checkpoint
@param ltr handler
@param cid checkpoint identifier
@return >=0 success
@return <0 failure
*/
int LTRdumpCheckpoint(ltr_t ltr, int cid);

/** 
@memo Restores checkpoint
@param ltr handler
@param cid checkpoint identifier
@return >=0 success
@return <0 failure
*/
int LTRrestoreCheckpoint(ltr_t ltr, int cid);

/**
@memo Creates an extra object belonging to a cross edge
@doc The size of the extra object must be equal to the size of a tree object.
@param ltr handler
@param dest destination node
@param src source node
@param join input parameter: reference to the memory in which 
which must contain extra information about the join
@param idx output parameter: index to the memory in which 
the join  will be written ({\tt NULL} permitted)
@return >=0 success
@return <0 failure
*/
int LTRmakeJoin(ltr_t ltr, idx_t dest, idx_t src, void *join, idx_t *idx);

/**
@param ltr handler 
@return number of joins
*/
int LTRgetNumberOfJoins(ltr_t ltr);

/** 
@memo Makes the indicated join transition (cross edge) current
@doc  The destination node coincides with a node in the tree. 
@param ltr handler
@param index of {\tt join}
*/
int LTRsetJoinCurrent(ltr_t ltr, int index);

/**
@memo Gets the current coin 
@param ltr handler
@param join output parameter: reference to the memory in which 
the content of the current join will be written
@return 0 success
@return <0 failure
*/
int LTRgetJoin(ltr_t ltr,   void *join);

/**
@memo Gets the join indexed by {\tt idx} 
@param ltr handler
@param join output parameter: reference to the memory in which 
the content of the join indexed by {\tt idx} will be written
@return 0 success
@return <0 failure
*/
int LTRgetJoinElm(ltr_t ltr,   int idx, void *join);

/**
@memo Gets the length of the path leading to join index by {\tt idx}
@param ltr handler
@param idx index of join
@return length of the path
*/
int LTRgetJoinLength(ltr_t ltr, int idx) ;

/**
@memo Marks that the current state is explored
@param ltr handler
@return 0 success
@return <0 failure
*/
int LTRfinishState(ltr_t ltr, idx_t current);

/** 
@memo Returns information about the current level
@param ltr handler
@param index of level
@param nstates number of explored states
@param visited number of visited states
@param ntransitions number of outgoing transitions from {\tt level}
*/ 
int LTRgetLevelInfo(ltr_t ltr, int level, int *nstates, 
int *visited, int *ntransitions);

/** 
@memo Returns information about all levels
@param ltr handler
@param nstates number of explored states
@param visited number of visited states
@param ntransitions number of outgoing transitions from {\tt level}
*/ 
int LTRgetTotalLevelInfo(ltr_t ltr,  int *nstates, int *visited,
int *ntransitions);

/** 
@memo Returns information about all levels until {\tt level}
@param ltr handler
@param index of level
@param nstates number of explored states
@param visited number of visited states
@param ntransitions number of outgoing transitions from {\tt level}
*/ 
int LTRgetCumLevelInfo(ltr_t ltr, int level_pt, int *nstates, int *visited,
int *ntransitions);

/**
@memo Gets the source node belonging to {\tt join}
@param ltr handler
@return index of source
@return <0 failure
*/
idx_t LTRgetJoinSource(ltr_t ltr, int join);

/**
@memo Gets the destination node belonging to {\tt join} 
@param ltr handler
@return index of destination
*/
idx_t LTRgetJoinDestination(ltr_t ltr, int join);

/**
@memo Gets current join index
@param ltr handler
@return index to current join
*/
idx_t LTRgetJoinCurrent(ltr_t ltr);

/**
@memo Gets current level
@param ltr handler
@return index to current level
*/
int  LTRgetCurrentLevel(ltr_t ltr);

void *LTRgetArray(ltr_t ltr);
int LTRrunFromParent(ltr_t ltr, idx_t parent, parent_cb f);
int LTRrunJoinsFromParent(ltr_t ltr, idx_t parent, join_cb f);
int LTRrunThroughTrace(ltr_t ltr, trace_cb f);
int LTRrunThroughObjects(ltr_t ltr, object_cb cb);
int LTRrunThroughMarks(ltr_t ltr, mark_cb cb);
int LTRmakeMark(ltr_t ltr, idx_t join, idx_t *idx);
int LTRgetMarkElm(ltr_t ltr, int idx, void *obj);
int LTRgetNumberOfMarks(ltr_t ltr);
int LTRgetLengthOfMark(ltr_t ltr, int idx);
int LTRgetDepthOfMark(ltr_t ltr, int idx);
idx_t LTRgetStartOfMark(ltr_t ltr, int idx);
idx_t LTRgetEndOfMark(ltr_t ltr, int idx);
int LTRgetJoinOfMark(ltr_t ltr, int idx);
void LTRsetCurrentLevel(ltr_t ltr, int level);
int LTRgetLevel(ltr_t ltr, idx_t idx);
int LTRresetMarks(ltr_t ltr);
//@}
#endif
