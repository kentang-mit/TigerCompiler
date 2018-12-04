#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/

//frame pointer(%rbp), return value(%rax)
void F_initMap(){
    if(F_tempMap != NULL) return;
    F_tempMap = Temp_empty();
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
}
Temp_temp F_FP(void){
	//rbp
	if(FP==NULL) FP = Temp_newtemp();
	return FP;
}

Temp_temp F_RV(void){
	//rax
	if(RV==NULL) RV = Temp_newtemp();
	return RV;
}

Temp_temp F_RDX(void){
	if(RDX==NULL) RDX = Temp_newtemp();
	return RDX;
}

Temp_temp F_RDI(void){
	if(RDI==NULL) RDI = Temp_newtemp();
	return RDI;
}

Temp_temp F_RSI(void){
	if(RSI==NULL) RSI = Temp_newtemp();
	return RSI;
}

Temp_temp F_RCX(void){
	if(RCX==NULL) RCX = Temp_newtemp();
	return RCX;
}

Temp_temp F_R8(void){
	if(R8==NULL) R8 = Temp_newtemp();
	return R8;
}

Temp_temp F_R9(void){
	if(R9==NULL) R9 = Temp_newtemp();
	return R9;
}

Temp_temp F_R10(void){
	if(R10==NULL) R10 = Temp_newtemp();
	return R10;
}

Temp_temp F_R11(void){
	if(R11==NULL) R11 = Temp_newtemp();
	return R11;
}

Temp_temp F_R12(void){
	if(R12==NULL) R12 = Temp_newtemp();
	return R12;
}

Temp_temp F_R13(void){
	if(R13==NULL) R13 = Temp_newtemp();
	return R13;
}

Temp_temp F_R14(void){
	if(R14==NULL) R14 = Temp_newtemp();
	return R14;
}

Temp_temp F_R15(void){
	if(R15==NULL) R15 = Temp_newtemp();
	return R15;
}

Temp_temp F_SP(void){
	if(SP==NULL) SP = Temp_newtemp();
	return SP;
}

Temp_temp F_RBX(void){
	if(RBX==NULL) RBX = Temp_newtemp();
	return RBX;
}

//varibales

F_access InFrame(int offset){
	F_access f_acc = (F_access)checked_malloc(sizeof(*f_acc));
	f_acc->kind = inFrame;
	f_acc->u.offset = offset;
	return f_acc;
}

F_access InReg(Temp_temp reg){
	F_access f_acc = (F_access)checked_malloc(sizeof(*f_acc));
	f_acc->kind = inReg;
	f_acc->u.reg = reg;
	return f_acc;
}

F_frag F_StringFrag(Temp_label label, string str) {   
	F_frag f_frag = (F_frag)checked_malloc(sizeof(*f_frag));
	f_frag->kind = F_stringFrag;
	f_frag->u.stringg.label = label;
	f_frag->u.stringg.str = str;
	return f_frag;                                      
}                                                     
                                                      
F_frag F_ProcFrag(T_stm body, F_frame frame) {        
	F_frag f_frag = (F_frag)checked_malloc(sizeof(*f_frag));
	f_frag->kind = F_procFrag;
	f_frag->u.proc.body = body;
	f_frag->u.proc.frame = frame;
	return f_frag;                                 
}                                                     
                                                      
F_fragList F_FragList(F_frag head, F_fragList tail) { 
	F_fragList frl = (F_fragList)checked_malloc(sizeof(*frl));
	frl->head = head;
	frl->tail = tail;
	return frl;                                 
}                

F_accessList F_AccessList(F_access head, F_accessList tail){
	F_accessList al = (F_accessList)checked_malloc(sizeof(*al));
	al->head = head;
	al->tail = tail;
	return al;
}


F_frame F_newFrame(Temp_label label, U_boolList escapes){
	F_frame fm = (F_frame)checked_malloc(sizeof(*fm));
	fm->size = 0;
	fm->label = label;
	fm->escapes = escapes;
    fm->accessList = NULL;
	//64 bit
	int cnt = 0;

	//allocate space for formals
	F_accessList tmp_list = NULL;
	for(U_boolList p = escapes; p; p = p -> tail, cnt++){
		F_access cur_acc = F_allocLocal(fm, p->head);
		tmp_list = F_AccessList(cur_acc, tmp_list);
	}
	//reverse storage
    
	F_accessList ans = NULL;
	for(F_accessList p = tmp_list; p; p = p->tail){
		ans = F_AccessList(p->head, ans);
	}
	fm->accessList = ans;
    
	return fm;
}             

string F_name(F_frame f){
    return Temp_labelstring(f->label);
}
//allocate a local param on stack. may need to change according to x86.
F_access F_allocLocal(F_frame f, bool escape){
	if(!escape){
        F_access ret = InReg(Temp_newtemp());
        return ret;
    }
	else{
		int offset = f->size + F_wordSize;
		f->size += F_wordSize;
		F_access ret = InFrame(offset);
        return ret;
	}
}

//access a variable if its relative pos to fp and its fp are given.
T_exp F_exp(F_access acc, T_exp fp){
	switch(acc->kind){
		case inFrame:{
			return T_Mem(T_Binop(T_plus, fp, T_Const(acc->u.offset)));
		}
		case inReg:{
			return T_Temp(acc->u.reg);
		}
	}
}

//call an external function
T_exp F_externalCall(string s, T_expList args){
	return T_Call(T_Name(Temp_namedlabel(s)), args);
}

//dummy implementation. Will be replaced at page 267(ENG book).
T_stm F_procEntryExit1(F_frame frame, T_stm stm) { 
	return stm;
}
