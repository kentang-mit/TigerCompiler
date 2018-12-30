#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"

G_table def_table, use_table;

void FG_init(){
    def_table = G_empty();
    use_table = G_empty();
}

G_table FG_getDefTable(){
    return def_table;
}

G_table FG_getUseTable(){
    return use_table;
}

Temp_tempList FG_def(G_node n) {
    AS_instr cur_inst = G_nodeInfo(n);
    switch(cur_inst->kind){
        case I_OPER: {
            return cur_inst->u.OPER.dst;
        }
        case I_MOVE: {
            return cur_inst->u.MOVE.dst;
        }
    }
	return NULL;
}

Temp_tempList FG_use(G_node n) {
    AS_instr cur_inst = G_nodeInfo(n);
    switch(cur_inst->kind){
        case I_OPER: {
            return cur_inst->u.OPER.src;
        }
        case I_MOVE: {
            return cur_inst->u.MOVE.src;
        }
    }
    return NULL;
}

bool FG_isMove(G_node n) {
	AS_instr cur_inst = G_nodeInfo(n);
	return cur_inst->kind == I_MOVE;
}

//removed the frame param.
G_graph FG_AssemFlowGraph(AS_instrList il) {
    //G_table mapping = G_empty();
    FG_init();
	G_graph G = G_Graph();
    G_nodeList first_l=NULL, last_l=NULL;
    for(AS_instrList ilptr = il; ilptr; ilptr = ilptr->tail){
        AS_instr iptr = ilptr->head;
        G_node g = G_Node(G,iptr);
        Temp_tempList g_def = FG_def(g);
        Temp_tempList g_use = FG_use(g);
        G_enter(def_table, g, g_def);
        G_enter(use_table, g, g_use);
        if(!first_l) first_l = G_NodeList(g, NULL);
        else if(!last_l){
            last_l = G_NodeList(g, NULL);
            first_l = G_NodeList(first_l->head, last_l);
        }
        else{
            last_l->tail = G_NodeList(g, NULL);
            last_l = last_l->tail;
        }
    }
    
    for(G_nodeList nptr = first_l; nptr->tail; nptr = nptr->tail){
        
        G_node cur_node = nptr->head;
        AS_instr cur_instr = G_nodeInfo(cur_node);
        if(cur_instr->kind == I_OPER && cur_instr->u.OPER.jumps!=NULL){
            for(Temp_labelList labels = cur_instr->u.OPER.jumps->labels; labels; labels = labels->tail){
                Temp_label target = labels->head;
                //finding the target
                G_nodeList nptr2 = first_l;
                for(AS_instrList ilptr = il; ilptr && nptr2; ilptr = ilptr->tail, nptr2= nptr2->tail){
                    AS_instr iptr = ilptr->head;
                    if(iptr->kind != I_LABEL){
                        continue;
                    }
                    if(iptr->u.LABEL.label == target){
                        G_addEdge(cur_node, nptr2->head);
                        break;
                    }
                }
            }
            //A hack. If the instruction is jmp, then don't add the next instruction to conflict list; else add it.
            if((cur_instr->u.OPER.assem)[1]!='m') G_addEdge(cur_node, nptr->tail->head);
        }
        else{
            G_addEdge(cur_node, nptr->tail->head);
        }
    }
    
    //printf("Showing the control flow graph...\n");
    //G_show(stdout, first_l, NULL);
    //printf("End showing the control flow graph...\n");
    
	return G;
}
