#include <stdio.h>
#include <string.h>
#include "stdlib.h"
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "table.h"
/*
Defining necessary data structures.
*/

//doubly linked list for nodes
typedef struct COL_nodeList_ *COL_nodeList;
struct COL_nodeList_{
    G_node node;
    COL_nodeList prev, next;
};

//doubly linked list for moves
typedef struct COL_moveList_ *COL_moveList;
struct COL_moveList_{
	Live_moveList move;
	//enum {COL_activeMove, COL_frozenMove, COL_workListMove, COL_coalescedMove, COL_constrainedMove} kind;
	COL_moveList prev, next;
};

COL_moveList COL_MoveList(Live_moveList, COL_moveList, COL_moveList);

//The extra information class. Including degree, kind, COL_nodeList corresp. to G_node and move related nodes.
typedef struct COL_inf_ *COL_inf;
struct COL_inf_{
    int degree;
    enum {COL_simplify, COL_freeze, COL_spill, COL_spilled, COL_coalesced, COL_colored, COL_precolored} kind;
    COL_nodeList list;
    Live_moveList move_f, move_l;
    G_node alias;
    int color;
};

typedef struct COL_moveInf_ *COL_moveInf;
struct COL_moveInf_{
    COL_moveList move;
    enum {COL_activeMove, COL_frozenMove, COL_workListMove, COL_coalescedMove, COL_constrainedMove} kind;
};

//A node-extraInf mapping
typedef TAB_table COL_InfTable;
COL_InfTable COL_InfEmpty(void) {
  return TAB_empty();
}

COL_InfTable COL_enter(COL_InfTable t, G_node n, void *value)
{
  TAB_enter(t, n, value);
}

string COL_strLook(COL_InfTable t, G_node n){
    return (string)TAB_look(t,n);
}

COL_InfTable COL_moveEnter(COL_InfTable t, Live_moveList m, void *value)
{
  TAB_enter(t, m, value);
}

string COL_moveStrLook(COL_InfTable t, Live_moveList m){
	return (string)TAB_look(t,m);
}

COL_moveInf COL_moveInfLook(COL_InfTable t, Live_moveList m){
    return (COL_moveInf)TAB_look(t,m);
}

COL_inf COL_infLook(COL_InfTable t, G_node n){
    return (COL_inf)TAB_look(t, n);
}


COL_inf COL_Inf(int degree){
    COL_inf inf = (COL_inf)checked_malloc(sizeof(*inf));
    inf->degree = degree;
    inf->move_f = inf->move_l = COL_MoveList(NULL,NULL,NULL);
    inf->list = NULL;
    inf->alias = NULL;
    inf->color = -1;
    return inf;
}

COL_moveInf COL_MoveInf(COL_moveList m){
    COL_moveInf inf = (COL_moveInf)checked_malloc(sizeof(*inf));
    inf->move = m;
    return inf;
}

COL_nodeList COL_NodeList(G_node node, COL_nodeList prev, COL_nodeList next){
    COL_nodeList ret = (COL_nodeList)checked_malloc(sizeof(*ret));
    ret->node = node;
    ret->prev = prev;
    ret->next = next;
    return ret;
}

COL_moveList COL_MoveList(Live_moveList m, COL_moveList prev, COL_moveList next){
    COL_moveList ret = (COL_moveList)checked_malloc(sizeof(*ret));
    ret->move = m;
    ret->prev = prev;
    ret->next = next;
    //ret->kind = COL_workListMove;//by default
    return ret;
}

void COL_enterNodeList(COL_nodeList *first, COL_nodeList *last, G_node n){
    if(*first==NULL || (*first)->node==NULL) *first = *last = COL_NodeList(n,NULL,NULL);
    //else if(*last == NULL || (*last)->node==NULL){
    //    (*first)->next = *last = COL_NodeList(n,*first,NULL);
    //}
    else{
        (*last)->next = COL_NodeList(n,*last,NULL);
        *last = (*last)->next;
    }
}

void COL_removeFromList(COL_nodeList *first, COL_nodeList *last, COL_nodeList n){
    if(!n) return;
    if((*first)==n){
        COL_nodeList p = *first;
    	if((*first)->next) (*first)->next->prev = NULL;
        *first = (*first)->next;
        free(p);
    }
    else if(n==*last){
        (*last)->prev->next = (*last)->next;
        *last=(*last)->prev;
    }
    else{
        if(n->next) n->next->prev = n->prev;
        
        n->prev->next = n->next;
        free(n);
    }
}

//difference of two node lists
static G_nodeList diff_nodeList(G_nodeList t1, G_nodeList t2){
    G_nodeList p1, p2;
    G_nodeList first = NULL, last = NULL;
    //use hash map to accelerate
    COL_InfTable m = COL_InfEmpty();
    for(p2 = t2; p2; p2 = p2->tail){
        COL_enter(m, p2->head, String(""));
    }
    for(p1 = t1; p1; p1 = p1->tail){
        G_node cur1 = p1->head;
        if(!COL_strLook(m, cur1)){
            if(!first) first = G_NodeList(cur1, NULL);
            else if(!last){
                first->tail = last = G_NodeList(cur1, NULL);
            }
            else last = last->tail = G_NodeList(cur1, NULL);
        }
    }
    return first;
}

//intersect of two node lists
static G_nodeList intersect_nodeList(G_nodeList t1, G_nodeList t2){
    G_nodeList p1, p2;
    G_nodeList first = NULL, last = NULL;
    //use hash map to accelerate
    COL_InfTable m = COL_InfEmpty();
    for(p2 = t2; p2; p2 = p2->tail){
        COL_enter(m, p2->head, String(""));
    }
    for(p1 = t1; p1; p1 = p1->tail){
        G_node cur1 = p1->head;
        if(COL_strLook(m, cur1)){
            if(!first) first = G_NodeList(cur1, NULL);
            else if(!last){
                first->tail = last = G_NodeList(cur1, NULL);
            }
            else last = last->tail = G_NodeList(cur1, NULL);
        }
    }
    return first;
}

//union of two node lists
static G_nodeList union_nodeList(G_nodeList t1, G_nodeList t2){
    G_nodeList p1, p2;
    G_nodeList first = NULL, last = NULL;
    //use hash map to accelerate
    COL_InfTable m = COL_InfEmpty();
    for(p1 = t1; p1; p1 = p1->tail){
       G_node cur1 = p1->head;
       COL_enter(m, cur1, String("")); 
       if(!first) first = G_NodeList(cur1, NULL);
       else if(!last){
            first->tail = last = G_NodeList(cur1, NULL);
       }
       else last = last->tail = G_NodeList(cur1, NULL);
    }
    for(p2 = t2; p2; p2 = p2->tail){
       G_node cur2 = p2->head;
       if(COL_strLook(m, cur2)) continue;
       COL_enter(m, cur2, String("")); 
       if(!first) first = G_NodeList(cur2, NULL);
       else if(!last){
            first->tail = last = G_NodeList(cur2, NULL);
       }
       else last = last->tail = G_NodeList(cur2, NULL);
    }
    return first;
}


void COL_enterMoveList(COL_moveList *first, COL_moveList *last, Live_moveList n){
    if(*first == NULL || (*first)->move==NULL){
        *first = *last = COL_MoveList(n,NULL,NULL);
    }
    //else if(*last==NULL || (*last)->move==NULL){
    //    (*first)->next = *last = COL_MoveList(n,*first,NULL);
    //}
    else{
        (*last) = (*last)->next = COL_MoveList(n,*last,NULL);
    }

}

void COL_removeFromMoveList(COL_moveList *first, COL_moveList *last, COL_moveList n){
    if(!n) return;
    if((*first)==n){
        COL_moveList p = *first;
        (*first)->next->prev = NULL;
        *first = (*first)->next;
        free(p);
    }
    else if(n==*last){
        (*last)->prev->next = (*last)->next;
        *last = (*last)->prev;
    }
    else{
        if(n->next) n->next->prev = n->prev;
        n->prev->next = n->next;
        free(n);
    }
}

//difference of two node lists
static COL_moveList diff_moveList(COL_moveList t1, COL_moveList t2){
    COL_moveList p1, p2;
    COL_moveList first = NULL, last = NULL;
    //use hash map to accelerate
    COL_InfTable m = COL_InfEmpty();
    for(p2 = t2; p2; p2 = p2->next){
        if(!(p2->move)) continue;
        COL_moveEnter(m, p2->move, String(""));
    }
    for(p1 = t1; p1; p1 = p1->next){
        Live_moveList cur1 = p1->move;
        if(!cur1) continue;
        if(!COL_moveStrLook(m, p1->move)){
            if(!first){
                first = COL_MoveList(p1->move, NULL, NULL);
            }
            else if(!last){
                first->next = last = COL_MoveList(p1->move, first, NULL);
            }
            else{
                last = last->next = COL_MoveList(p1->move, last, NULL);
            }
        }
    }
    return first;
}

void COL_printMoveList(COL_moveList m){
    for(COL_moveList p = m; p; p = p->next){
        Live_moveList pm = p ? p->move : NULL;
        if(!pm) continue;
        printf("(r%d r%d) ", Temp_int(G_nodeInfo(pm->dst)), Temp_int(G_nodeInfo(pm->src))); 
    }
    printf("\n");
}

void COL_printNodeList(COL_nodeList m){
    for(COL_nodeList p = m; p; p = p->next){
        G_node n = p ? p->node : NULL;
        if(!n){continue;}
        printf("r%d ", Temp_int(G_nodeInfo(n))); 
    }
    printf("\n");
}

void COL_printNodeList1(COL_nodeList m, COL_nodeList m1){
    for(COL_nodeList p = m; p!=m1->next; p = p->next){
        G_node n = p ? p->node : NULL;
        if(n==NULL) break;
        printf("r%d ", Temp_int(G_nodeInfo(n))); 
    }
    printf("R%d ", Temp_int(G_nodeInfo(m1->node)));
    printf("\n");
}

//intersect of two node lists
static COL_moveList intersect_moveList(COL_moveList t1, COL_moveList t2){
    COL_moveList p1, p2;
    COL_moveList first = NULL, last = NULL;
    //use hash map to accelerate
    COL_InfTable m = COL_InfEmpty();
    for(p2 = t2; p2; p2 = p2->next){
        if(!(p2->move)) continue;
        COL_moveEnter(m, p2->move, String(""));
    }
    for(p1 = t1; p1; p1 = p1->next){
        Live_moveList cur1 = p1->move;
        if(!cur1) continue;
        //fix kind inconsistency here!!! 20181223
        if(COL_moveStrLook(m, p1->move)){
            if(!first){
                first = p1;
                first->next = COL_MoveList(p1->move, NULL, NULL);
            }
            else if(!last){
                first->next = last = COL_MoveList(p1->move, first, NULL);
            }
            else{
                last = last->next = COL_MoveList(p1->move, last, NULL);
            }
        }
    }
    //printf("t1:");COL_printMoveList(t1);
    //printf("t2:");COL_printMoveList(t2);
    return first;
}

//union of two node lists
static COL_moveList union_moveList(COL_moveList t1, COL_moveList t2){
    COL_moveList p1, p2;
    COL_moveList first = NULL, last = NULL;
    //use hash map to accelerate
    COL_InfTable m = COL_InfEmpty();
    for(p1 = t1; p1; p1 = p1->next){
       Live_moveList cur1 = p1->move;
       if(!cur1) continue;
       COL_moveEnter(m, p1->move, String("")); 
       if(!first){
           first = COL_MoveList(p1->move, NULL, NULL);
       }
       else if(!last){
           first->next = last = COL_MoveList(p1->move, first, NULL);
       }
       else{
           last = last->next = COL_MoveList(p1->move, last, NULL);
       }
    }
    
    for(p2 = t2; p2; p2 = p2->next){
       Live_moveList cur2 = p2->move;
       if(!cur2) continue;
       if(COL_moveStrLook(m, p2->move)) continue;
       COL_moveEnter(m, p2, String("")); 
       if(!first){
           first = COL_MoveList(p2->move, NULL, NULL);
       }
       else if(!last){
           first->next = last = COL_MoveList(p2->move, first, NULL);
       }
       else{
           last = last->next = COL_MoveList(p2->move, last, NULL);
       }
    }
    //printf("%d %d %d", t1, t2, first);
    //printf("t1:");if(t1){COL_printMoveList(t1);}
    //printf("t2:");if(t2){COL_printMoveList(t2);}
    //printf("union:");if(first){COL_printMoveList(first);}
    return first;
}

/*
End Defining necessary data structures.
*/

/*
Defining necessary instances.
*/

//G_nodeList represents nodes in the original graph, while COL_nodeList adds some new information
//and is designed as doubly-linked lists to accelerate deletion.
COL_nodeList simplifyWorkList_f, freezeWorkList_f, spillWorkList_f;
COL_nodeList simplifyWorkList_l, freezeWorkList_l, spillWorkList_l;


COL_moveList coalescedMoves_f, coalescedMoves_l;
COL_moveList constrainedMoves_f, constrainedMoves_l, frozenMoves_f, frozenMoves_l;
COL_moveList workListMoves_f, workListMoves_l, activeMoves_f, activeMoves_l;
COL_moveList allMoves, allMoves_l;

G_nodeList selectStack, coalescedNodes, precolored, spilledNodes, coloredNodes;
string *COL_colors;

COL_InfTable COL_information, COL_moveInformation;

/*
End Defining necessary instances.
*/

/*
Implementing Graph Coloring.
*/

void COL_init(){
    COL_colors = (string*)checked_malloc(F_numRegisters()*sizeof(string));
    precolored = NULL;
    simplifyWorkList_f = simplifyWorkList_l = COL_NodeList(NULL, NULL, NULL);  //low-degree non-move-related nodes
    freezeWorkList_f = freezeWorkList_l = COL_NodeList(NULL, NULL, NULL); //low-degree move-related nodes
    spillWorkList_f = spillWorkList_l = COL_NodeList(NULL, NULL, NULL); //candidate spilling nodes
    spilledNodes = NULL; //spilled nodes
    coalescedNodes = NULL; //coalesced nodes
    coloredNodes = NULL; //colored nodes
    selectStack = NULL; //temps removed from graph
    coalescedMoves_f = coalescedMoves_l = COL_MoveList(NULL, NULL, NULL); //moves that have been coalesced
    constrainedMoves_f = constrainedMoves_l = COL_MoveList(NULL, NULL, NULL); //moves where src, dst conflicts
    frozenMoves_f = frozenMoves_l = COL_MoveList(NULL, NULL, NULL); //moves that will not be coalesced
    workListMoves_f = workListMoves_l = COL_MoveList(NULL, NULL, NULL); //moves enabled for coalescing
    activeMoves_f = activeMoves_l = COL_MoveList(NULL, NULL, NULL); //not yet ready for coalescing
    allMoves = allMoves_l = COL_MoveList(NULL, NULL, NULL);//all the moves
    COL_information = COL_InfEmpty();
    COL_moveInformation = COL_InfEmpty();
}

void decrementDegree(G_node);
void enableMoves(G_nodeList);

G_nodeList adjacent(G_node n){
    return diff_nodeList(G_succ(n), union_nodeList(selectStack, coalescedNodes));
}

COL_moveList nodeMoves(G_node n){
    COL_inf inf = COL_infLook(COL_information, n);
    //printf("%d %d %d\n", inf->move_f, activeMoves_f, workListMoves_f);
    return intersect_moveList(inf->move_f, union_moveList(activeMoves_f, workListMoves_f));
}

bool moveRelated(G_node n){
    return (nodeMoves(n)!=NULL && nodeMoves(n)->move!=NULL);
}

G_node getAlias(G_node n){
    G_node p = n;
    while(G_inNodeList(p, coalescedNodes)){
        COL_inf inf = COL_infLook(COL_information, p);
        p = inf->alias;
    }
    return p;
}

//This is the Live Graph.
void makeWorkList(G_graph g, Live_moveList moves){
    G_nodeList nodes = G_nodes(g);
    
    for(G_nodeList p=nodes; p; p = p->tail){
        G_node n = p->head;
        int degree = G_degree(n);
        //printTemp(G_nodeInfo(n));
        //printf("%d\n", degree);
        COL_inf info = COL_infLook(COL_information, n);
        if(info) continue;
        COL_inf inf = COL_Inf(degree);
        COL_enter(COL_information, n, inf);
    }
    
    //printf("\n\n\n");
    for(Live_moveList p = moves; p; p = p->tail){
        //printf("%d %d\n", Temp_int(G_nodeInfo(p->dst)), Temp_int(G_nodeInfo(p->src)));
    	COL_inf dst_inf = COL_infLook(COL_information, p->dst);
    	COL_inf src_inf = COL_infLook(COL_information, p->src);
        COL_enterMoveList(&allMoves, &allMoves_l, p);
        COL_enterMoveList(&workListMoves_f, &workListMoves_l, p);
        if(workListMoves_l){
            COL_moveInf minf = COL_MoveInf(workListMoves_l);
            minf->kind = COL_workListMove;
            COL_moveEnter(COL_moveInformation, p, minf);
        }
        else{
            COL_moveInf minf = COL_MoveInf(workListMoves_f);
            minf->kind = COL_workListMove;
            COL_moveEnter(COL_moveInformation, p, COL_MoveInf(workListMoves_f));
        }
        //wrong!!
        COL_enterMoveList(&(src_inf->move_f), &(src_inf->move_l), p);        
        COL_enterMoveList(&(dst_inf->move_f), &(dst_inf->move_l), p);
    }
    
    
    for(G_nodeList p=nodes; p; p = p->tail){
        G_node n = p->head;
        COL_nodeList list;
        COL_inf inf = COL_infLook(COL_information, n);
        int degree = inf->degree;
        if(inf->kind == COL_precolored) continue;
        //printf("%d\n", COL_infLook(COL_information, n)->degree);
        if(degree >= F_numRegisters()){
            printTemp(G_nodeInfo(n));
            printf("%d\n", degree);
            COL_enterNodeList(&spillWorkList_f, &spillWorkList_l, n);
            list = spillWorkList_l->node?spillWorkList_l:spillWorkList_f;
            inf->kind = COL_spill;
        }
        else if(moveRelated(n)){
            COL_enterNodeList(&freezeWorkList_f, &freezeWorkList_l, n);
            list = freezeWorkList_l->node?freezeWorkList_l:freezeWorkList_f;
            inf->kind = COL_freeze;
        }
        else{
            COL_enterNodeList(&simplifyWorkList_f, &simplifyWorkList_l, n);
            list = simplifyWorkList_l->node?simplifyWorkList_l:simplifyWorkList_f;
            inf->kind = COL_simplify;
        }
        inf->list = list;
    }
    
}


//simplifyStep
void simplify(){
    printf("========Start Simplifying========\n");
    //These nodes are to be removed from simplify work list
    for(COL_nodeList p=simplifyWorkList_f; p; p = p->next){
        G_node cur = p->node;
        printf("Register r%d is simplified!\n", Temp_int(G_nodeInfo(cur)));
        simplifyWorkList_f = simplifyWorkList_f->next;
        if(simplifyWorkList_f!=NULL) simplifyWorkList_f->prev = NULL;
        
        G_nodeList succ = adjacent(cur);
        for(G_nodeList q = succ; q; q = q->tail){
            decrementDegree(q->head);
        }
        selectStack = G_NodeList(p->node, selectStack);
        
    }
    printf("========End Simplifying========\n");
    COL_printNodeList(freezeWorkList_f);
    printf("========End Printing Freeze WorkList========\n");
}
//decrement degree of a node. Potential influence: spillWorkList, simplifyWorkList, freezeWorkList can be changed.
void decrementDegree(G_node n){
    //printf("Processing register %d (decrement degree)\n", Temp_int(G_nodeInfo(n)));
    COL_inf inf = COL_infLook(COL_information, n);
    int degree = inf->degree;
    COL_nodeList nl = inf->list;
    //printf("%d %d\n", nl->prev, nl->next);
    inf->degree--;
    assert(inf->degree>=0);
    //degree changes from K to K-1. Can do coalescing or simplifying
    if(degree == F_numRegisters()){
        G_nodeList neighborhood = G_NodeList(n,adjacent(n));
        enableMoves(neighborhood);
        if(inf->kind == COL_spill){
            COL_removeFromList(&spillWorkList_f, &spillWorkList_l, nl);
        }
        else return;
        if(moveRelated(n)){
            //move related. So -> coalescing candidate.
            COL_enterNodeList(&freezeWorkList_f, &freezeWorkList_l, n);
            inf->kind = COL_freeze;
            inf->list = freezeWorkList_l?freezeWorkList_l:freezeWorkList_f;
        }
        else if(inf->kind!=COL_precolored){
            //not move related. So -> simplify candidate. ADD precolor constraint.
            COL_enterNodeList(&simplifyWorkList_f, &simplifyWorkList_l, n);
            inf->kind = COL_simplify;
            inf->list = simplifyWorkList_l?simplifyWorkList_l:simplifyWorkList_f;
        }
    }
}

//all moves related to nodes in "neighbor" will be removed from activeMoves and they will enter workListMoves
void enableMoves(G_nodeList neighbor){
    for(G_nodeList p = neighbor; p; p = p->tail){
        COL_moveList cur_nodeMoves = nodeMoves(p->head);
        for(COL_moveList q = cur_nodeMoves; q; q = q->next){
            COL_moveInf minf = COL_moveInfLook(COL_moveInformation, q->move);
            if(minf->kind == COL_activeMove){
                COL_moveInf minf = COL_moveInfLook(COL_moveInformation, minf->move);
                COL_removeFromMoveList(&activeMoves_f, &activeMoves_l, minf->move);
                minf->kind = COL_workListMove;
                COL_enterMoveList(&workListMoves_f, &workListMoves_l, minf->move);
                minf->move = workListMoves_l?workListMoves_l:workListMoves_f;
            }
        }
    }
}

void addWorkList(G_node);
void combine(G_node, G_node);

bool Briggs(G_node u, G_node v){
    G_nodeList adj_u = adjacent(u), adj_v = adjacent(v);
    G_nodeList combined = union_nodeList(adj_u, adj_v);
    int cnt = 0;
    for(G_nodeList p = combined; p; p = p->tail){
        COL_inf inf = COL_infLook(COL_information, p->head);
        if(inf->degree >= F_numRegisters()) cnt++;
    }
    return (cnt<F_numRegisters());
}

//for lake of adjSet, this implementation is currently slow.
bool George_OK(G_node t, G_node u){
    COL_inf inf = COL_infLook(COL_information, t);
    return inf->degree < F_numRegisters() || G_inNodeList(t, precolored) || G_goesTo(t, u);
}
    
bool George(G_node u, G_node v){
    G_nodeList adj_v = adjacent(v);
    for(G_nodeList p = adj_v; p; p = p->tail){
        if(!George_OK(p->head, u)) return 0;
    }
    return 1;
}

//coalescing
void coalesce(){
    printf("========Start Coalescing========\n");
    for(COL_moveList p = workListMoves_f; p; p = p->next){
        //printf("%d\n", p);//dead loop?
        Live_moveList l = p->move;
        if(!l) continue;
        G_node dst = l->dst, src = l->src;
        G_node x = getAlias(dst);
        G_node y = getAlias(src);
        G_node u, v;
        if(G_inNodeList(y, precolored)){
            u = y;
            v = x;
        }
        else{
            u = x;
            v = y;
        }
        COL_moveInf minf = COL_moveInfLook(COL_moveInformation, p->move);
        if(u==v){
            minf->kind = COL_coalescedMove;
            COL_enterMoveList(&coalescedMoves_f, &coalescedMoves_l, minf->move);
            minf->move = coalescedMoves_l?coalescedMoves_l:coalescedMoves_f;
            addWorkList(u);
        }
        else if(G_inNodeList(v, precolored) || G_goesTo(u,v)){
            //Remark: adjSet is not implemented. Currently the condition judgement is slow.
            minf->kind = COL_constrainedMove;
            COL_enterMoveList(&constrainedMoves_f, &constrainedMoves_l, minf->move);
            minf->move = constrainedMoves_l?constrainedMoves_l:constrainedMoves_f;
            addWorkList(u);
            addWorkList(v);
        }
        else if( (G_inNodeList(u, precolored)&&George(u,v)) || (!G_inNodeList(u, precolored) && Briggs(u,v)) ){
            minf->kind = COL_coalescedMove;
            COL_enterMoveList(&coalescedMoves_f, &coalescedMoves_l, minf->move);
            minf->move = coalescedMoves_l?coalescedMoves_l:coalescedMoves_f;
            combine(u, v);
            addWorkList(u);
        }
        else{
            minf->kind = COL_activeMove;
            COL_enterMoveList(&activeMoves_f, &activeMoves_l, minf->move);
            minf->move = activeMoves_l?activeMoves_l:activeMoves_f;
        }
        workListMoves_f = workListMoves_f->next; //remove the current move from workListMoves
    }
    printf("========End coalescing========\n");
}

void addWorkList(G_node u){
    COL_inf inf = COL_infLook(COL_information, u);
    if(inf->kind !=COL_precolored && !moveRelated(u) && inf->degree < F_numRegisters()){
        COL_removeFromList(&freezeWorkList_f, &freezeWorkList_l, inf->list);
        COL_enterNodeList(&simplifyWorkList_f, &simplifyWorkList_l, u);
        inf->kind = COL_simplify;
        inf->list = simplifyWorkList_l?simplifyWorkList_l:simplifyWorkList_f;
    }
    //else{
    //    printf("(r%d: %d %d %d)", Temp_int(G_nodeInfo(u)), inf->kind, moveRelated(u), inf->degree);
    //}
}

void combine(G_node u, G_node v){
    printf("Coalesced r%d and r%d!\n", Temp_int(G_nodeInfo(u)), Temp_int(G_nodeInfo(v)));
    COL_inf inf = COL_infLook(COL_information, v);
    if(inf->kind == COL_freeze){
        COL_removeFromList(&freezeWorkList_f, &freezeWorkList_l, inf->list);
    }
    else if(inf->kind == COL_spill){
        //It seems that the book doesn't consider simplify?
        COL_removeFromList(&spillWorkList_f, &spillWorkList_l, inf->list);
    }

    coalescedNodes = G_NodeList(v, coalescedNodes);
    inf->kind = COL_coalesced;
    inf->alias = u;
    
    COL_inf infu = COL_infLook(COL_information, u);
    infu->move_f = union_moveList(infu->move_f, inf->move_f);
    enableMoves(G_NodeList(v,NULL));
    for(G_nodeList p = adjacent(v); p; p = p->tail){
        G_addEdge(u, p->head);
        G_addEdge(p->head, u);
        COL_inf infp = COL_infLook(COL_information, p->head);
        infp->degree++;
        infu->degree++;
        decrementDegree(p->head);
    }
    if(infu->degree >= F_numRegisters() && infu->kind==COL_freeze){
        COL_removeFromList(&freezeWorkList_f, &freezeWorkList_l, infu->list);
        COL_enterNodeList(&spillWorkList_f, &spillWorkList_l, u);
        infu->kind = COL_spill;
        infu->list = spillWorkList_l?spillWorkList_l:spillWorkList_f;
    }
    
}

void freezeMoves(G_node u){
    COL_moveList moves = nodeMoves(u);
    for(COL_moveList p = moves; p; p = p->next){
        Live_moveList l = p->move;
        G_node x = l->dst, y = l->src;
        G_node aliasU = getAlias(u);
        G_node aliasY = getAlias(y);
        G_node v;
        if(aliasU == aliasY){
            v = getAlias(x);
        }
        else v = aliasY;
        COL_moveInf minf = COL_moveInfLook(COL_moveInformation, p->move);
        COL_removeFromMoveList(&activeMoves_f, &activeMoves_l, minf->move);
        minf->kind = COL_frozenMove;
        COL_enterMoveList(&frozenMoves_f, &frozenMoves_l, p->move);
        minf->move = frozenMoves_l?frozenMoves_l:frozenMoves_f;
        COL_inf infv = COL_infLook(COL_information, v);
        if(nodeMoves(v) == NULL && infv->degree < F_numRegisters()){
            COL_removeFromList(&freezeWorkList_f, &freezeWorkList_l, infv->list);
            COL_enterNodeList(&simplifyWorkList_f, &simplifyWorkList_l, u);
            infv->kind = COL_simplify;
            infv->list = simplifyWorkList_l?simplifyWorkList_l:simplifyWorkList_f;
        }
        
    }
}

void freeze(){
    printf("========Start freezing========\n");
    G_node u = freezeWorkList_f->node;
    printf("Node r%d is frozen!\n", Temp_int(G_nodeInfo(u)));
    COL_inf inf = COL_infLook(COL_information, u);
    COL_removeFromList(&freezeWorkList_f, &freezeWorkList_l, inf->list);
    COL_enterNodeList(&simplifyWorkList_f, &simplifyWorkList_l, u);
    //update inf->list!!!
    inf->list = simplifyWorkList_l?simplifyWorkList_l:simplifyWorkList_f;
    inf->kind = COL_simplify;
    freezeMoves(u);
    printf("========End freezing========\n");
}

void printTemp(Temp_temp t){
    printf("t%d ", Temp_int(t));
}

void selectSpill(){
    printf("========Start select spill========\n");
    COL_printNodeList(spillWorkList_f);
    //the heuristic is to select the node with largest degree.
    int largest_degree = -1;
    G_node u = NULL; //the node to be spilled
    COL_nodeList u_l = NULL;
    COL_inf saved_inf = NULL;
    for(COL_nodeList p = spillWorkList_f; p; p = p->next){
        G_node cur = p->node;
        COL_inf inf = COL_infLook(COL_information, cur);
        if(inf->degree > largest_degree){
            largest_degree = inf->degree;
            u = cur;
            u_l = inf->list;
            saved_inf = inf;
        }
    }
    //if(!u) return;
    printTemp(G_nodeInfo(u));
    printf("%d\n", largest_degree);
    COL_removeFromList(&spillWorkList_f, &spillWorkList_l, u_l);
    COL_enterNodeList(&simplifyWorkList_f, &simplifyWorkList_l, u);
    saved_inf->kind = COL_simplify;
    saved_inf->list = simplifyWorkList_l?simplifyWorkList_l:simplifyWorkList_f;
    freezeMoves(u);
    printf("========End select spill========\n");
}

int getColor(G_node n){
    COL_inf inf = COL_infLook(COL_information, n);
    return inf->color;
}

void setColor(G_node n, int color){
    COL_inf inf = COL_infLook(COL_information, n);
    inf->color = color;
}

void assignColors(){
    for(G_nodeList p = selectStack; p; p = p->tail){
        G_node n = p->head;
        COL_inf inf = COL_infLook(COL_information, n);
        int reg_num = F_numRegisters();
        bool *OK_colors = (bool*)checked_malloc(sizeof(bool)*reg_num);
        for(int i = 0; i < reg_num; i++) OK_colors[i] = (i!=0 && i!=6)?1:0;
        G_nodeList adjList = G_succ(n);
        for(G_nodeList q = adjList; q; q = q->tail){
            G_node w = q->head;
            G_node aliasW = getAlias(w);
            if(G_inNodeList(aliasW, union_nodeList(precolored, coloredNodes))){
                OK_colors[getColor(aliasW)] = 0;
            }
        }
        
        bool exist_color = 0;
        int first_available_color = -1;
        for(int i = 0; i < reg_num; i++){
            if(OK_colors[i]) exist_color = 1;
            if(OK_colors[i] && first_available_color < 0) first_available_color = i;
        }
        if(!exist_color){
            inf->kind = COL_spilled;
            spilledNodes = G_NodeList(n, spilledNodes);
        }
        else{
            inf->kind = COL_colored;
            coloredNodes = G_NodeList(n, coloredNodes);
            setColor(n, first_available_color);
        }
    }
    
    for(G_nodeList p = coalescedNodes; p; p = p->tail){
        printf("Coalesced register r%d is colored as %d.\n", Temp_int(G_nodeInfo(p->head)), getColor(getAlias(p->head)));
        setColor(p->head, getColor(getAlias(p->head)));
        //color them...
        coloredNodes = G_NodeList(p->head, coloredNodes);
    }
}

//Note: precolored nodes don't have corresponding COL_nodeList because they cannot be simplified.
void COL_buildPrecolor(G_graph ig, Temp_tempList regs, Temp_map initial){
    int cnt = 0;
    if(precolored != NULL) return;
    TAB_table tab = Live_getTable();
    for(Temp_tempList p = regs; p; p = p->tail, cnt++){
        string name = Temp_look(initial, p->head);
        COL_colors[cnt] = name;
        G_node n = Live_lookupTempMap(tab, p->head);
        if(!n){
            Temp_dumpMap(stdout, F_tempMap);
            n = G_Node(ig, p->head);
            Live_enter(tab, p->head, n);
        }
        precolored = G_NodeList(n, precolored);
        int degree = G_degree(n);
        COL_inf inf = COL_Inf(degree);
        inf->color = cnt;
        inf->kind = COL_precolored;
        COL_enter(COL_information, n, inf);
    }
}

/*
End Implementing Graph Coloring.
*/

//This function will be called in regalloc.c. It's actually the "Main" function.
struct COL_result COL_color(G_graph ig, Temp_map initial, Temp_tempList regs, Live_moveList moves) {
	//your code here.
	struct COL_result ret;
    COL_init();
    COL_buildPrecolor(ig, regs, initial);
    makeWorkList(ig, moves);
    
    while((simplifyWorkList_f && simplifyWorkList_f->node!=NULL) || (workListMoves_f && workListMoves_f->move!=NULL) || (freezeWorkList_f && freezeWorkList_f->node !=NULL) || (spillWorkList_f && spillWorkList_f->node !=NULL)){
        if(simplifyWorkList_f && simplifyWorkList_f->node!=NULL) simplify();
        else if(workListMoves_f && workListMoves_f->move!=NULL) coalesce();
        else if(freezeWorkList_f && freezeWorkList_f->node!=NULL) freeze();
        else if(spillWorkList_f && spillWorkList_f->node!=NULL) selectSpill();
    }
    
    assignColors();
    
    Temp_tempList spilledTemps = NULL;
    for(G_nodeList p = spilledNodes; p; p = p->tail){
        spilledTemps = Temp_TempList(G_nodeInfo(p->head), spilledTemps);
    }
    ret.spills = spilledTemps;
    for(G_nodeList p = coloredNodes; p; p = p->tail){
        COL_inf inf = COL_infLook(COL_information, p->head);
        int color = inf->color;
        string name = COL_colors[color];
        //printf("Register %d is colored as %s.\n", Temp_int(G_nodeInfo(p->head)), (char*)name);
        Temp_temp node_temp = G_nodeInfo(p->head);
        Temp_enter(initial, node_temp, name);
    }
    
    for(G_nodeList p = G_nodes(ig); p; p = p->tail){
        G_node cur = p->head;
        COL_inf inf = COL_infLook(COL_information, cur);
        //printf("Reg %d: %d %s\n", Temp_int(G_nodeInfo(cur)), inf->kind, COL_colors[inf->color]);
        printf("Reg %d: %d %d\n", Temp_int(G_nodeInfo(cur)), inf->kind, inf->color);
    }
    ret.coloring = initial;
    
	return ret;
}

