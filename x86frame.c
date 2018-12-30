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

int F_numRegisters(){
    return 14; //not allowed to use RBP, RSP
}

extern Temp_map F_tempMap;

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

Temp_map F_getTempMap(){
    if(F_tempMap == NULL) F_initMap();
    return F_tempMap;
}

Temp_tempList F_MachineRegisters(){
    if(!F_machineRegisters) F_machineRegisters = Temp_TempList(F_FP(), Temp_TempList(F_RV(), Temp_TempList(F_RDX(), Temp_TempList(F_RDI(), 
              Temp_TempList(F_RSI(), Temp_TempList(F_RCX(), Temp_TempList(F_SP(), Temp_TempList(F_RBX(),
              Temp_TempList(F_R8(), Temp_TempList(F_R9(), Temp_TempList(F_R10(), Temp_TempList(F_R11(),
              Temp_TempList(F_R12(), Temp_TempList(F_R13(), Temp_TempList(F_R14(), Temp_TempList(F_R15(), NULL))))))))))))))));
    return F_machineRegisters;
}


Temp_tempList F_calleeSavedRegisters(){
    //FP, SP never used in RA
    if(!F_calleeSaved) F_calleeSaved = Temp_TempList(F_RBX(), Temp_TempList(F_R12(), Temp_TempList(F_R13(), 
                             Temp_TempList(F_R14(), Temp_TempList(F_R15(), NULL))))); 
    //if(!F_calleeSaved) F_calleeSaved = Temp_TempList(F_FP(), Temp_TempList(F_RBX(), Temp_TempList(F_R12(), Temp_TempList(F_R13(), 
    //                          Temp_TempList(F_R14(), Temp_TempList(F_R15(), NULL)))))); 
    return F_calleeSaved;
}

Temp_tempList F_callerSavedRegisters(){
    if(!F_callerSaved)  F_callerSaved = Temp_TempList(F_RV(), Temp_TempList(F_RCX(), Temp_TempList(F_RDX(), Temp_TempList(F_R8(), 
                              Temp_TempList(F_R9(), Temp_TempList(F_R10(), Temp_TempList(F_R11(), Temp_TempList(F_RDI(), Temp_TempList(F_RSI(), NULL)))))))));
    return F_callerSaved;
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
    //should be minus. 20181226
	f_acc->u.offset = -offset;
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
    fm->accessList = fm->accessList_l = NULL;
	//64 bit
	int cnt = 0;
    
	//allocate space for formals
	//F_accessList tmp_list = NULL;
	for(U_boolList p = escapes; p; p = p -> tail, cnt++){
		F_allocLocal(fm, p->head);
        //F_access cur_acc = F_allocLocal(fm, p->head);
		//tmp_list = F_AccessList(cur_acc, tmp_list);
	}
	//reverse storage
    
    /*
	F_accessList ans = NULL;
	for(F_accessList p = tmp_list; p; p = p->tail){
		ans = F_AccessList(p->head, ans);
	}
	fm->accessList = ans;
    */
	return fm;
}             

string F_name(F_frame f){
    return Temp_labelstring(f->label);
}

//allocate a local param on stack. may need to change according to x86.
F_access F_allocLocal(F_frame f, bool escape){
	if(!escape){
        F_access ret = InReg(Temp_newtemp());
        if(!(f->accessList)) f->accessList = f->accessList_l = F_AccessList(ret, NULL);
        else f->accessList_l = f->accessList_l->tail = F_AccessList(ret, NULL);
        return ret;
    }
	else{
		int offset = f->size;
		f->size += F_wordSize;
		F_access ret = InFrame(offset+F_wordSize);
        if(!(f->accessList)) f->accessList = f->accessList_l = F_AccessList(ret, NULL);
        else f->accessList_l = f->accessList_l->tail = F_AccessList(ret, NULL);
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

static Temp_tempList L(Temp_temp t, Temp_tempList l){
    return Temp_TempList(t, l);
}

//dummy implementation. Will be replaced at page 267(ENG book).
T_stm F_procEntryExit1(F_frame frame, T_stm stm) {
    Temp_tempList calleeSaved = F_calleeSavedRegisters();
    T_stm ret = NULL;
    Temp_tempList save_pos=NULL, save_pos_l=NULL;
    for(Temp_tempList p = calleeSaved; p; p = p->tail){
        Temp_temp save = Temp_newtemp();
        if(!save_pos) save_pos = save_pos_l = L(save, NULL);
        else save_pos_l = save_pos_l->tail = L(save, NULL);
        T_stm cur = T_Move(T_Temp(save), T_Temp(p->head));
        if(!ret) ret = cur;
        else ret = T_Seq(ret, cur);
    }
    ret = T_Seq(ret, stm);
    for(Temp_tempList p = calleeSaved, q = save_pos; p && q; p = p->tail, q = q->tail){
        ret = T_Seq(ret, T_Move(T_Temp(p->head), T_Temp(q->head)));
    }
    
	return ret;
}

//produce the live variables after procedure
AS_instrList F_procEntryExit2(AS_instrList body) {
    Temp_tempList returnSink = L(F_RV(), L(F_SP(), L(F_FP(), F_calleeSavedRegisters())));
	return AS_splice(body, AS_InstrList(AS_Oper("", NULL, returnSink, NULL), NULL));
}

//prologue and epilogue.
//prologue: adjust rbp rsp allocate space for the new frame(pushq %rbp; movq %rsp, %rbp;)
//epilogue: adjust rbp rsp (leave ret) where leave=movq %rbp, %rsp; popq %rbp;(clean the new frame)
AS_proc F_procEntryExit3(F_frame frame, AS_instrList body){
    int fsize = frame->size;
    char buffer[100], prolog[100], epilog[100];
    AS_instr pro1 = AS_Oper(String("pushq `s0"), NULL, L(F_FP(), NULL), NULL);
    AS_instr pro2 = AS_Oper(String("movq `s0, `d0"), L(F_FP(), NULL), L(F_SP(), NULL), NULL);
    sprintf(buffer, "subq $%d, `s0", fsize);
    AS_instr pro3 = AS_Oper(String(buffer), L(F_SP(), NULL), L(F_SP(), NULL), NULL);
    
    AS_instr epi1 = AS_Oper(String("leaveq"), L(F_SP(), NULL), L(F_FP(), NULL), NULL);
    AS_instr epi2 = AS_Oper(String("ret"), NULL, NULL, NULL);
    
    AS_instrList prologue =  AS_InstrList(pro1, AS_InstrList(pro2, AS_InstrList(pro3, NULL)));
    AS_instrList epilogue = AS_InstrList(epi1, AS_InstrList(epi2, NULL));
    AS_instrList final = F_procEntryExit2(AS_splice(prologue, body));
    
    string procName = F_name(frame);
    sprintf(prolog, ".text\n.globl %s\n.type %s, @function\n%s:\n", procName, procName, procName);
    sprintf(epilog, "leaveq\nret\n");
    
    
    AS_proc proc = AS_Proc(String(prolog), final, String(epilog));
    return proc;
}