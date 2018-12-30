#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"
#include "printtree.h"

static Temp_temp munchExp(T_exp);
static void munchStm(T_stm);
static void emit(AS_instr);

AS_instrList globalInstrList = NULL, last = NULL;

//wrapper
static Temp_tempList L(Temp_temp head, Temp_tempList tail){
	return Temp_TempList(head, tail);
}
//caller convention. Move parameters to corresponding positions.
static Temp_tempList munchArgs(int i, T_expList args){
	if(!args) return NULL;
	Temp_temp arg_reg = munchExp(args->head);
	Temp_temp dest_reg;
	switch(i){
		case 0: {dest_reg = F_RDI(); break;}
		case 1: {dest_reg = F_RSI(); break;}
		case 2: {dest_reg = F_RDX(); break;}
		case 3: {dest_reg = F_RCX(); break;}
		case 4: {dest_reg = F_R8(); break;}
		case 5: {dest_reg = F_R9(); break;}
	}
	emit(AS_Move(String("movq `s0, `d0"), L(dest_reg, NULL), L(arg_reg,NULL)));
	if(i < 5) return L(dest_reg, munchArgs(i+1, args->tail));
	else{
		T_expList reversedArgs = NULL, p;
		for(p = args; p; p = p->tail) reversedArgs = T_ExpList(p->head, reversedArgs);
		for(p = reversedArgs; p; p = p->tail){
			//enter stack
			emit(AS_Oper(String("pushq `s0"), NULL, L(arg_reg,NULL), NULL));
		}
		return L(dest_reg, NULL);
	}
}

static void emit(AS_instr inst){
	if(last != NULL){
		last = last->tail = AS_InstrList(inst, NULL);
	}
	else{
		globalInstrList = last = AS_InstrList(inst, NULL);
	}
}

char buffer[256];

static Temp_temp munchExp(T_exp e){
	switch(e->kind){
		case T_MEM:{
			if(e->u.MEM->kind == T_BINOP && e->u.MEM->u.BINOP.op == T_plus && 
					e->u.MEM->u.BINOP.left->kind == T_CONST){
				Temp_temp result = Temp_newtemp();
				T_exp e1 = e->u.MEM->u.BINOP.left, e2 = e->u.MEM->u.BINOP.right;
				Temp_temp offset = munchExp(e2);
				sprintf(buffer, "movq %d(`s0), `d0", e1->u.CONST);
				emit(AS_Oper(String(buffer), L(result, NULL), L(offset, NULL), NULL));
                return result;
			}
			else if(e->u.MEM->kind == T_BINOP && e->u.MEM->u.BINOP.op == T_plus && 
					e->u.MEM->u.BINOP.right->kind == T_CONST){
				Temp_temp result = Temp_newtemp();
				T_exp e1 = e->u.MEM->u.BINOP.left, e2 = e->u.MEM->u.BINOP.right;
                Temp_temp offset = munchExp(e1);
				sprintf(buffer, "movq %d(`s0), `d0", e2->u.CONST);
				emit(AS_Oper(String(buffer), L(result, NULL), L(offset, NULL), NULL));
                return result;
			}
			else if(e->u.MEM->kind == T_CONST){
				Temp_temp result = Temp_newtemp();
				Temp_temp const_reg = Temp_newtemp();
				sprintf(buffer, "movq %d, `d0", e->u.MEM->u.CONST);
				emit(AS_Oper(String(buffer), L(const_reg, NULL), NULL, NULL));
				sprintf(buffer, "movq (`s0), `d0");
				emit(AS_Oper(String(buffer), L(result, NULL), L(const_reg, NULL), NULL));
				return result;
			}
			else if(e->u.MEM->kind == T_TEMP){
				Temp_temp result = Temp_newtemp();
				sprintf(buffer, "movq (`s0), `d0");
				emit(AS_Oper(String(buffer), L(result, NULL), L(e->u.TEMP, NULL), NULL));
				return result;
			}
			else{
				Temp_temp result = Temp_newtemp();
				Temp_temp add = munchExp(e->u.MEM);
				emit(AS_Oper(String("movq (`s0), `d0"), L(result, NULL), L(add, NULL), NULL));
                return result;
			}
		}
		case T_BINOP:{
			//NOT supporting CISC addressing mode now.
			string oper;
			switch(e->u.BINOP.op){
				case T_plus:{oper=String("addq"); break;}
				case T_minus:{oper=String("subq"); break;}
				case T_mul:{oper=String("imulq"); break;} 
				default: oper = String("");
			}
			Temp_temp result = Temp_newtemp();
			T_exp e1 = e->u.BINOP.left, e2 = e->u.BINOP.right;
			//make sure e1 is not const
			if(e1->kind == T_CONST){
				T_exp tmp = e1;
				e1 = e2;
				e2 = tmp;
			}
			Temp_temp left_op = munchExp(e1);
			if(result != left_op){
                if(e->u.BINOP.op!=T_div){
                    if(e1->kind != T_CONST) emit(AS_Move("movq `s0, `d0", L(result, NULL), L(left_op, NULL)));
                    else{
                        sprintf(buffer, "movq $%d, `d0", e1->u.CONST);
                        emit(AS_Oper(String(buffer), L(result, NULL), NULL, NULL));
                    }
                }
			}
			if(e2->kind == T_CONST){
                if(e->u.BINOP.op!=T_div){
                    sprintf(buffer, "%s $%d, `d0", oper, e2->u.CONST);
                    if(e->u.BINOP.op!=T_div) emit(AS_Oper(String(buffer), L(result, NULL), L(result, NULL), NULL));
                    return result;
                }
			}
			Temp_temp right_op = munchExp(e2);
			sprintf(buffer, "%s `s0, `d0", oper);
            
			if(e->u.BINOP.op != T_div){
				emit(AS_Oper(String(buffer), L(result, NULL), L(right_op, L(result, NULL)), NULL));
			}
			else{
				//special division for x86-64
				Temp_temp rax = F_RV();
				Temp_temp rdx = F_RDX();
				emit(AS_Move(String("movq `s0, `d0"), L(rax, NULL), L(left_op, NULL)));
				emit(AS_Oper(String("xorq `s0, `d0"), L(rdx, NULL), L(rdx, NULL), NULL));
				emit(AS_Oper(String("idivq `s0"), L(rdx, L(rax, NULL)), L(right_op, L(rax, NULL)), NULL));
				emit(AS_Move(String("movq `s0, `d0"), L(result, NULL), L(rax, NULL)));
			}
			return result;
		}
		case T_TEMP: return e->u.TEMP;
		case T_CONST: {
            //pr_tree_exp(stdout, e, 0);
			Temp_temp result = Temp_newtemp();
			sprintf(buffer, "movq $%d, `d0", e->u.CONST);
			emit(AS_Oper(String(buffer), L(result, NULL), NULL, NULL));
			return result;
		}
		case T_CALL:{
			//It is responsible for moving all params. to %rdi, %rci, ... and push some params on stack.
			//Don't care view shift. These are done by F_procEntryExitx()
			Temp_tempList calldefs = F_callerSavedRegisters();
			//first do munch args
            Temp_tempList l = munchArgs(0, e->u.CALL.args);
            //Temp_temp r = munchExp(e->u.CALL.fun);
            //emit(AS_Oper(String("call `s0"), calldefs, L(r,l), NULL));
			sprintf(buffer, "call %s", Temp_labelstring(e->u.CALL.fun->u.NAME));
            emit(AS_Oper(String(buffer), calldefs, l, NULL));
            return F_RV();
		}
        case T_NAME:{
			//label usage(only appear in j/cond-j). Normal case: should be dealt with in munchStm.
            //20181226 It is also possible that this is from a string!
            Temp_temp r = Temp_newtemp();
            sprintf(buffer, "leaq .%s(\%rip), `d0", Temp_labelstring(e->u.NAME));
            //sprintf(buffer, "movq .%s, `d0", Temp_labelstring(e->u.NAME));
			string as = String(buffer);
			emit(AS_Oper(as, L(r, NULL), NULL, NULL));
            return r;
		}
		default: assert(0);
	}
}

static void munchStm(T_stm s){
	switch(s->kind){
		case T_MOVE: {
			T_exp dst = s->u.MOVE.dst, src = s->u.MOVE.src;
			if(dst->kind == T_MEM){
				if(dst->u.MEM->kind == T_BINOP && dst->u.MEM->u.BINOP.op == T_plus && 
					dst->u.MEM->u.BINOP.left->kind == T_CONST){//5
					Temp_temp r_src = munchExp(src);
					Temp_temp dst_r = munchExp(dst->u.MEM->u.BINOP.right);
                    //fix a bug. The dst is also a used node!
					sprintf(buffer, "movq `s0, `$%d(`s1)", dst->u.MEM->u.BINOP.left->u.CONST);
					emit(AS_Oper(String(buffer), NULL, L(r_src, L(dst_r, NULL)), NULL));
					return;
				}
				else if(dst->u.MEM->kind == T_BINOP && dst->u.MEM->u.BINOP.op == T_plus && 
					dst->u.MEM->u.BINOP.right->kind == T_CONST){//5
					Temp_temp r_src = munchExp(src);
					Temp_temp dst_l = munchExp(dst->u.MEM->u.BINOP.left);
                    //fix a bug. The dst is also a used node!
					sprintf(buffer, "movq `s0, %d(`s1)", dst->u.MEM->u.BINOP.right->u.CONST);
					emit(AS_Oper(String(buffer), NULL, L(r_src, L(dst_l, NULL)), NULL));
					return;
				}
				else if(src->kind == T_MEM){//3
					Temp_temp r_dst = munchExp(dst->u.MEM), r_src = munchExp(src->u.MEM);
					Temp_temp r = Temp_newtemp();
					emit(AS_Oper(String("movq (`s0), `d0"), L(r,NULL), L(r_src, NULL), NULL));
                    //fix a bug here. 1225
					emit(AS_Oper(String("movq `s0, (`s1)"), NULL, L(r,L(r_dst, NULL)), NULL));
					return;
				}
				else{//2
					Temp_temp r_dst = munchExp(dst->u.MEM), r_src = munchExp(src);
					emit(AS_Oper(String("movq `s0, (`s1)"), NULL, L(r_src, L(r_dst, NULL)), NULL));
					return;
				}
			}
			else if(dst->kind == T_TEMP){
				Temp_temp r_src = munchExp(src);
				//AS_Move for movement between Temp_temps
				emit(AS_Move(String("movq `s0, `d0"), L(dst->u.TEMP,NULL), L(r_src, NULL)));
				return;
			}
			else assert(0);
		}
		case T_JUMP: {
			//only consider the first label
			Temp_labelList l = s->u.JUMP.jumps;
			//T_exp e = s->u.JUMP.exp;
			emit(AS_Oper(String("jmp `j0"), NULL, NULL, AS_Targets(l)));
			return;
		}
		case T_CJUMP: {
			string oper;
			switch(s->u.CJUMP.op){
				case T_eq: {oper = String("je"); break;}
				case T_ne: {oper = String("jne"); break;}
				case T_lt: {oper = String("jl"); break;}
				case T_le: {oper = String("jle"); break;}
				case T_gt: {oper = String("jg"); break;}
				case T_ge: {oper = String("jge"); break;}
				default: assert(0);
			}
            Temp_temp r_l = munchExp(s->u.CJUMP.left);
            Temp_temp r_r = munchExp(s->u.CJUMP.right);
            //X86 assembly is operand2 > operand1 corresponding to jg!!!
            sprintf(buffer, "cmpq `s1, `s0");
            emit(AS_Oper(String(buffer), NULL, L(r_l, L(r_r, NULL)), NULL));
			sprintf(buffer, "%s `j0", oper);
            emit(AS_Oper(String(buffer), NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true,NULL))));
			return;
		}
		case T_LABEL: {
			Temp_label l = s->u.LABEL;
			emit(AS_Label(Temp_labelstring(l), l));
			return;
		}
        case T_EXP:{
            munchExp(s->u.EXP);
            return;
        }
		default: {printf("%d\n", s->kind);assert(0);}
	}
}
//Lab 6: put your code here
AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    
    Temp_tempList l = L(F_RDI(), L(F_RSI(), L(F_RDX(), L(F_RCX(), L(F_R8(), L(F_R9(), NULL))))));
    F_accessList p = f->accessList;
    for(int i = 0; i < 6 && p; i++, p = p->tail){
        if(p->head->kind == inReg) emit(AS_Oper(String(""), NULL, L(p->head->u.reg, l->tail), NULL));
        l = l->tail;
    }
    
	T_stmList sl;
	AS_instrList il;
	for(sl = stmList; sl; sl = sl->tail) munchStm(sl->head);
	il = globalInstrList; globalInstrList=last=NULL;
	return il;
}
