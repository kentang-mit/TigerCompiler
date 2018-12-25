#include <stdio.h>
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
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"

typedef TAB_table Temp_regRegMap;
void Temp_regEnter(Temp_regRegMap m, Temp_temp t, Temp_temp t1){
    TAB_enter(m, t, t1);
}

Temp_temp Temp_regLook(Temp_regRegMap m, Temp_temp t){
    return (Temp_temp)TAB_look(m, t);
}

Temp_map initial;
Temp_tempList spilled, regs;
G_graph fg, lg;
Temp_map mem_access;
Temp_regRegMap reg_map;
Temp_tempList new_temps;

void append_instrList(AS_instrList *first, AS_instrList *last, AS_instr inst){
    if(!(*first)) *first = AS_InstrList(inst, NULL);
    else if(!(*last)) (*first)->tail = *last = AS_InstrList(inst, NULL);
    else (*last)->tail = *last = AS_InstrList(inst, NULL);
}

//wrapper
static Temp_tempList L(Temp_temp head, Temp_tempList tail){
	return Temp_TempList(head, tail);
}

static bool Temp_inTempList(Temp_temp t, Temp_tempList l){
    for(Temp_tempList p = l; p; p = p->tail){
        if(p->head == t) return 1;
    }
    return 0;
}

static void Temp_changeTempList(Temp_tempList l, Temp_temp to_replace, Temp_temp replacement){
    for(Temp_tempList p = l; p; p = p->tail){
        if(p->head == to_replace){
            p->head = replacement;
            return;
        }       
    }
}

AS_instrList rewriteProgram(F_frame f, Temp_tempList spilled, AS_instrList il){
    printf("========Rewriting the program========\n");
    new_temps = NULL;
    mem_access = Temp_empty();
    for(Temp_tempList p = spilled; p; p = p->tail){
        Temp_temp t = p->head;
        Temp_temp t1 = Temp_newtemp();
        new_temps = Temp_TempList(t1, new_temps);
        F_access acc = F_allocLocal(f, 1);
        int offset = acc->u.offset;
        char buffer[50];
        //`r0 is %rbp.
        sprintf(buffer, "$%d(`s0)", offset);
        string mem_dst = String(buffer);
        Temp_enter(mem_access, t, mem_dst);
        Temp_regEnter(reg_map, t, t1);
    }
    
    AS_instrList new_il = NULL, new_il_l = NULL;
    for(AS_instrList ilp = il; ilp; ilp = ilp->tail){
        AS_instr inst = ilp->head;
        switch(inst->kind){
            case I_LABEL: {
                append_instrList(&new_il, &new_il_l, inst);
            }
            case I_MOVE: {
                //Not bothering to write code for coalesced nodes now.
                append_instrList(&new_il, &new_il_l, inst);
            }
            case I_OPER: {
                Temp_tempList dst = inst->u.OPER.dst;
                Temp_tempList src = inst->u.OPER.src;
                for(Temp_tempList p = spilled; p; p = p->tail){
                    Temp_temp cur_spill = p->head;
                    string acc = Temp_look(mem_access, cur_spill);
                    Temp_temp replacement = Temp_regLook(reg_map, cur_spill);
                    if(Temp_inTempList(cur_spill, dst)){    
                        char buffer[50];
                        sprintf(buffer, "movq `s1 %s", (char*)acc);
                        //printf("%s\n", buffer);
                        Temp_tempList d = NULL;
                        Temp_tempList s = L(F_FP(), L(replacement, NULL));
                        AS_instr save_inst = AS_Oper(String(buffer), d, s, NULL);
                        Temp_changeTempList(inst->u.OPER.dst, cur_spill, replacement);
                        append_instrList(&new_il, &new_il_l, inst);
                        append_instrList(&new_il, &new_il_l, save_inst);
                    }
                    else if(Temp_inTempList(p->head, src)){
                        char buffer[50];
                        sprintf(buffer, "movq %s `d0", (char*)acc);
                        Temp_tempList d = L(replacement, NULL);
                        Temp_tempList s = L(F_FP(), NULL);
                        AS_instr fetch_inst = AS_Oper(String(buffer), d, s, NULL);
                        Temp_changeTempList(inst->u.OPER.dst, cur_spill, replacement);
                        append_instrList(&new_il, &new_il_l, fetch_inst);
                        append_instrList(&new_il, &new_il_l, inst);
                    }
                    else{
                        append_instrList(&new_il, &new_il_l, inst);
                    }
                }
            }
        }
    }
    
    spilled = NULL;
    printf("========End rewriting the program========\n");
    return new_il;
}


static Temp_map RA_initMap(){
    Temp_map F_tempMap = Temp_empty();
    Temp_enter(F_tempMap, F_FP(), String("%rbp"));
    Temp_enter(F_tempMap, F_RV(), String("%rax"));
    Temp_enter(F_tempMap, F_RDX(), String("%rdx"));
    Temp_enter(F_tempMap, F_RDI(), String("%rdi"));
    Temp_enter(F_tempMap, F_RSI(), String("%rsi"));
    Temp_enter(F_tempMap, F_RCX(), String("%rcx"));
    Temp_enter(F_tempMap, F_SP(), String("%rsp"));
    Temp_enter(F_tempMap, F_RBX(), String("%rbx"));
    Temp_enter(F_tempMap, F_R8(), String("%r8"));
    Temp_enter(F_tempMap, F_R9(), String("%r9"));
    Temp_enter(F_tempMap, F_R10(), String("%r10"));
    Temp_enter(F_tempMap, F_R11(), String("%r11"));
    Temp_enter(F_tempMap, F_R12(), String("%r12"));
    Temp_enter(F_tempMap, F_R13(), String("%r13"));
    Temp_enter(F_tempMap, F_R14(), String("%r14"));
    Temp_enter(F_tempMap, F_R15(), String("%r15"));
    return F_tempMap;
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	//your code here
	struct RA_result ret;
    bool stop = 0;
    initial = RA_initMap();
    struct Live_graph liveg;
    struct COL_result col_res;
    while(!stop){
        fg = FG_AssemFlowGraph(il);
        liveg = Live_liveness(fg);
        lg = liveg.graph;
        Live_print(liveg);
        Live_moveList moves = liveg.moves;
        Temp_tempList regs = F_MachineRegisters();
        //I don't know calling the F_getTempMap fails.
        
        //Temp_dumpMap(stdout, initial);
        col_res = COL_color(lg, initial, regs, moves);
        initial = col_res.coloring;
        spilled = col_res.spills;
        if(!spilled) stop = 1;
        else il = rewriteProgram(f, spilled, il);
    }
    ret.coloring = initial;
    ret.il = il;
    //AS_printInstrList(stdout, il, Temp_layerMap(initial, Temp_name()));
    return ret;
}
