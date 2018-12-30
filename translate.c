#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"
#include "string.h"

//LAB5: you can modify anything you want.
Tr_level OUTERMOST = NULL;

struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};


//The global fragment list
F_fragList glbl = NULL;


Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail){
	Tr_expList ret = (Tr_expList)checked_malloc(sizeof(*ret));
	ret->head = head;
	ret->tail = tail;
	return ret;
}

static patchList PatchList(Temp_label *head, patchList tail)
{
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

void doPatch(patchList tList, Temp_label label)
{
	for(; tList; tList = tList->tail)
		*(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second)
{
	if(!first) return second;
	for(; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

Tr_access Tr_Access(Tr_level level, F_access access){
	Tr_access ac = (Tr_access)checked_malloc(sizeof(*ac));
	ac->level = level;
	ac->access = access;
	return ac;
}


Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail){
	Tr_accessList acl = (Tr_accessList)checked_malloc(sizeof(*acl));
	acl->head = head;
	acl->tail = tail;
	return acl;
}

Tr_level Tr_outermost(void){
    //very important to have this U_boolList here! otherwise nothing can be added to the outmost frame.
    U_boolList formals =  U_BoolList(1, NULL);
	if(!OUTERMOST) OUTERMOST = Tr_newLevel(NULL, Temp_namedlabel("tigermain"), formals);
    return OUTERMOST;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals){
	Tr_level lv = (Tr_level)checked_malloc(sizeof(*lv));
	lv->frame = F_newFrame(name, formals);
	lv->parent = parent;
	return lv;
}

Tr_accessList Tr_formals(Tr_level level){
	F_frame frame = level->frame;
	Tr_accessList tmp_list = NULL;
	for(F_accessList p = frame->accessList; p; p = p -> tail){
		F_access f_acc = p->head;
		Tr_access cur_acc = Tr_Access(level, p->head);
		tmp_list = Tr_AccessList(cur_acc, tmp_list);
	}
	//reverse storage
	Tr_accessList ans = NULL;
	for(Tr_accessList p = tmp_list; p; p = p->tail){
		ans = Tr_AccessList(p->head, ans);
	}
    //printf("%d %d\n", frame, frame->accessList);
	return ans;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape){
	F_access f_acc = F_allocLocal(level->frame, escape);
	Tr_access acc = (Tr_access)checked_malloc(sizeof(*acc));
	acc->level = level;
	acc->access = f_acc;
	return acc;
}

Tr_exp Tr_Ex(T_exp ex){
	Tr_exp ret = (Tr_exp)checked_malloc(sizeof(*ret));
	ret->kind = Tr_ex;
	ret->u.ex = ex;
	return ret;
}

static Tr_exp Tr_Nx(T_stm nx){
	Tr_exp ret = (Tr_exp)checked_malloc(sizeof(*ret));
	ret->kind = Tr_nx;
	ret->u.nx = nx;
	return ret;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm){
	struct Cx *cx = (struct Cx*)checked_malloc(sizeof(*cx));
	cx->trues = trues;
	cx->falses = falses;
	cx->stm = stm;
	Tr_exp exp = (Tr_exp)checked_malloc(sizeof(*exp));
	exp->kind = Tr_cx;
	exp->u.cx = *cx;
	return exp;
}

//forced type conversion to T_exp
static T_exp unEx(Tr_exp e){
	switch(e->kind){
		case Tr_ex: return e->u.ex;
        case Tr_nx: return T_Eseq(e->u.nx, T_Const(0));
		case Tr_cx: {
			Temp_temp r = Temp_newtemp();
			Temp_label t = Temp_newlabel(); Temp_label f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
				 	T_Eseq(e->u.cx.stm,
				 	T_Eseq(T_Label(f),
			    	T_Eseq(T_Move(T_Temp(r), T_Const(0)),
			  		T_Eseq(T_Label(t), T_Temp(r))
			    	))));
			}
	}
}

//forced type conversion to T_stm
static T_stm unNx(Tr_exp e){
	switch(e->kind){
		case Tr_nx: return e->u.nx;
		case Tr_ex: {
            //pr_tree_exp(stdout,e->u.ex,0);
            //printf("\n\n");
			return T_Exp(e->u.ex);
		}
		case Tr_cx:{
			Temp_temp r = Temp_newtemp();
			Temp_label t = Temp_newlabel(); Temp_label f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			T_stm stm = T_Seq(T_Move(T_Temp(r), T_Const(1)),
						T_Seq(e->u.cx.stm,
						T_Seq(T_Label(f),
						T_Seq(T_Move(T_Temp(r), T_Const(0)),
						T_Label(t)))));
			return stm;
		} 

	}
	
}

//forced type conversion to Cx
static struct Cx unCx(Tr_exp e){
	switch(e->kind){
		case Tr_cx: return e->u.cx;
		case Tr_ex: {
            struct Cx cx;
			T_stm s = T_Cjump(T_ne, e->u.ex, T_Const(0), NULL, NULL);
			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			cx.trues = trues;
			cx.falses = falses;
			cx.stm = s;
			return cx;
			
		}
		default:break;
	}
	printf("Tr_nx cannot appear in function unCx!\n");
	assert(0);
}

Tr_exp Tr_staticLink(Tr_level used, Tr_level declared){
	//F_exp implemented in x86frame.h, it returns a T_exp
	T_exp fp = T_Temp(F_FP());
	for(Tr_level cur = used; cur&&cur!=declared; cur = cur->parent){
		//get access list
		Tr_accessList acl = Tr_formals(cur);
		//fp must be the first param.
		Tr_access fpa = acl->head;
		//go through static link
		fp = F_exp(fpa->access, fp);
	}
	//return the frame pointer of the level one variable/func is in.
    //pr_tree_exp(stdout, fp, 0); printf("\n\n\n");
	return Tr_Ex(fp);
}

//access: declared level, level: current level
Tr_exp Tr_simpleVar(Tr_access access, Tr_level level){
    //printf("%d %d\n", level, access->level);
	Tr_exp tr_fp = Tr_staticLink(level, access->level);
	T_exp fp = tr_fp->u.ex;
	F_access acc = access->access;
	//F_exp(acc,fp) finds this variable on stack.
	return Tr_Ex(F_exp(acc, fp));
}


//Access a field variable. Don't forget to time F_wordSize
Tr_exp Tr_fieldVar(Tr_exp base, int offset){
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base), T_Const(offset*F_wordSize))));
}

//Access a subscript variable.
Tr_exp Tr_subscriptVar(Tr_exp base, Tr_exp idx){
	//Memory access: Add(base) + idx * 8
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base), T_Binop(T_mul, unEx(idx), T_Const(F_wordSize)))));
}

//nop
Tr_exp Tr_nop(){
	return Tr_Ex(T_Const(0));
}

//intExp, an integer
Tr_exp Tr_intExp(int i){
	return Tr_Ex(T_Const(i));
}

//nilExp
Tr_exp Tr_nilExp(){
	return Tr_nop();
}

//opExp, just translate directly
Tr_exp Tr_opExp(A_oper op, Tr_exp left, Tr_exp right){
	switch(op){
		case A_plusOp: return Tr_Ex(T_Binop(T_plus, unEx(left), unEx(right)));
		case A_minusOp: return Tr_Ex(T_Binop(T_minus, unEx(left), unEx(right)));
		case A_timesOp: return Tr_Ex(T_Binop(T_mul, unEx(left), unEx(right)));
		case A_divideOp: return Tr_Ex(T_Binop(T_div, unEx(left), unEx(right)));
	}
	printf("Not valid operand!\n");
	assert(0);
}

//cmpExp, translate to conditional jump
Tr_exp Tr_cmpExp(A_oper op, Tr_exp left, Tr_exp right){
	T_relOp oper;
	switch(op){
		case A_eqOp: {oper = T_eq; break;}
		case A_neqOp: {oper = T_ne; break;}
		case A_gtOp: {oper = T_gt; break;}
		case A_geOp: {oper = T_ge; break;}
		case A_ltOp: {oper = T_lt; break;}
		case A_leOp: {oper = T_le; break;}
	}
	T_stm cmp = T_Cjump(oper, unEx(left), unEx(right), NULL, NULL);
	patchList trues = PatchList(&(cmp->u.CJUMP.true), NULL);
	patchList falses = PatchList(&(cmp->u.CJUMP.false), NULL);
	return Tr_Cx(trues, falses, cmp);
}

//string exp. The tiger string is composed of two parts. The first 4 bytes is string length, the next strlen bytes
//are the content.
Tr_exp Tr_stringExp(string s){
    int length = strlen(s);
    //Here should not be sizeof(*s) + sizeof(int) + 1. Should be length!
    string new_s = (string)checked_malloc(length+sizeof(int)+1);
    *new_s = length;
    for(int i = 0; i < strlen(s); i++) new_s[i+4] = s[i];
    //fix a bug, should consider int. It takes up 4 bytes.
    new_s[strlen(s)+4] = '\0';
	Temp_label lab = Temp_newlabel(); //use newlabel is better. The string can be empty!
	glbl = F_FragList(F_StringFrag(lab, new_s), glbl);
	return Tr_Ex(T_Name(lab));
}

Tr_exp Tr_stringEq(Tr_exp s1, Tr_exp s2){
    return Tr_Ex(F_externalCall(String("stringEqual"), T_ExpList(unEx(s1), T_ExpList(unEx(s2), NULL))));
}

//creation of a record TBD: initialization? return a ptr?
Tr_exp Tr_recordExp(int cnt, Tr_expList expList, Tr_level l){
    //non-escape. Tr_level l is passed to make sure this address can be accessed.
    Tr_access ra = Tr_allocLocal(l, 0);
    Temp_temp r = ra->access->u.reg;
	T_stm move_inst = T_Move(T_Temp(r), F_externalCall(String("allocRecord"), T_ExpList(T_Const(cnt * F_wordSize), NULL)));
    T_stm ret = move_inst;
    int i = 0;
    for(Tr_expList p = expList; p; p = p->tail, i++){
        ret = T_Seq(ret, T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(i*F_wordSize))), unEx(p->head)));
    }
    return Tr_Ex(T_Eseq(ret, T_Temp(r)));
	//return Tr_Ex(T_Call(T_Name(Temp_namedlabel("initRecord")), T_ExpList(T_Const(cnt), NULL)));
}

//creation of an array
Tr_exp Tr_arrayExp(Tr_exp cnt, Tr_exp value){
	return Tr_Ex(F_externalCall(String("initArray"), T_ExpList(unEx(cnt), T_ExpList(unEx(value), NULL))));
	//return Tr_Ex(T_Call(T_Name(Temp_namedlabel("initArray")), T_ExpList(T_Const(cnt)), T_ExpList(T_Const(value), NULL)));
}

//while loop
Tr_exp Tr_whileExp(Tr_exp cond_exp, Tr_exp body_exp, Temp_label bTarget){
	//convert to Cx, the labels are to fill in
	struct Cx cond_cx = unCx(cond_exp);
	//T_stm cjmp = cond_cx.stm;
	Temp_label test = Temp_newlabel();
	Temp_label body = Temp_newlabel();
	doPatch(cond_cx.trues, body);
	doPatch(cond_cx.falses, bTarget);
	return Tr_Nx(
			T_Seq(T_Label(test),
			T_Seq(cond_cx.stm,
			T_Seq(T_Label(body),
			T_Seq(unNx(body_exp),
			T_Seq(T_Jump(T_Name(test), Temp_LabelList(test, NULL)),
			T_Label(bTarget)
			))))));
}

//for loop. Change to while loop first.
Tr_exp Tr_forExp(Tr_exp id_exp, Tr_exp lo, Tr_exp hi, Tr_exp body_exp, Temp_label bTarget){
	//struct Cx cond_cx = unCx(cond_exp);
	Temp_temp r_i = id_exp->u.ex->u.TEMP;
	Temp_temp r_lim = Temp_newtemp();

	Temp_label test = Temp_newlabel();
	Temp_label body = Temp_newlabel();

	//doPatch(cond_cx.trues, body);
	//doPatch(cond_cx.falses, bTarget);
	return Tr_Nx(
			T_Seq(T_Move(T_Temp(r_i), unEx(lo)),
            T_Seq(T_Label(test),	
			T_Seq(T_Move(T_Temp(r_lim), unEx(hi)),		
			T_Seq(T_Cjump(T_gt, T_Temp(r_i), T_Temp(r_lim), bTarget, body),
			T_Seq(T_Label(body),
			T_Seq(unNx(body_exp),
			T_Seq(T_Move(T_Temp(r_i), T_Binop(T_plus, T_Temp(r_i), T_Const(1))),
			T_Seq(T_Jump(T_Name(test), Temp_LabelList(test, NULL)),
			T_Label(bTarget)
			)))))))));
}

Tr_exp Tr_breakExp(Temp_label bTarget){
	return Tr_Nx(T_Jump(T_Name(bTarget), Temp_LabelList(bTarget, NULL)));
}

//call a function. fun_level: declared level, cur_level: call level. static link as first param.
//update on 20181221: Previous implementation is wrong. The lis should contain all actual positions, consisting of 
//T_exp terms of translated arguments.
//update on 20181226: runtime functions do not use static link.
//update on 20181228: If call level < declared level, static link = rbp. Else, static link = (%rbp)(should access one layer upper).
Tr_exp Tr_callExp(Temp_label fun_label, Tr_level fun_level, Tr_level cur_level, Tr_expList args){
	T_expList rev_lis = NULL;
	//T_exp sl = Tr_staticLink(cur_level, fun_level)->u.ex;    
    Temp_temp fp = F_FP();
    int flag = 0;
    Tr_level p;
    for(p = fun_level; p&&p != cur_level; p = p->parent);
    if(p==cur_level && fun_level->parent != cur_level->parent) flag = 1;
    
    
    //failed parameter passing
    /*
	Tr_accessList accs = Tr_formals(cur_level);
	for(Tr_accessList acc = accs; acc; acc = acc->tail){
		F_access facc = acc->head->access;
		rev_lis = T_ExpList(F_exp(facc, T_Temp(fp)), rev_lis);
	}
    */
    for(Tr_expList p = args; p; p = p->tail){
        rev_lis = T_ExpList(unEx(p->head), rev_lis);
    }
	T_expList lis = NULL;
	for(T_expList expl = rev_lis; expl; expl = expl->tail){
		lis = T_ExpList(expl->head, lis);
	}
    
    if(strcmp((char*)Temp_labelstring(fun_label), "printi")!=0 && strcmp((char*)Temp_labelstring(fun_label), "print")!=0
      && strcmp((char*)Temp_labelstring(fun_label), "flush")!=0 && strcmp((char*)Temp_labelstring(fun_label), "ord")!=0
      && strcmp((char*)Temp_labelstring(fun_label), "chr")!=0 && strcmp((char*)Temp_labelstring(fun_label), "size")!=0 
      && strcmp((char*)Temp_labelstring(fun_label), "substring")!=0 && strcmp((char*)Temp_labelstring(fun_label), "concat")!=0
      && strcmp((char*)Temp_labelstring(fun_label), "getchar")!=0){
        //failed static link
        if(flag) lis = T_ExpList(T_Temp(fp), lis);
        else lis = T_ExpList(T_Mem(T_Binop(T_plus, T_Temp(fp), T_Const(-8))), lis);
    }
    return Tr_Ex(T_Call(T_Name(fun_label),lis));
    //T_exp callex = T_Call(T_Name(fun_label),lis);
    //return Tr_Ex(T_Move(T_Temp(F_RV()), unEx(callex)));
}

//assign exp
Tr_exp Tr_assignExp(Tr_exp var, Tr_exp e){
	return Tr_Nx(T_Move(var->u.ex, e->u.ex));
}

//if exp. Not done, complicated
Tr_exp Tr_ifExp(Tr_exp if_exp, Tr_exp then_exp, Tr_exp else_exp){
	struct Cx if_cx = unCx(if_exp);
	Temp_label t = Temp_newlabel(); Temp_label f = Temp_newlabel(); Temp_label done = Temp_newlabel();
	Temp_temp r = Temp_newtemp();
	doPatch(if_cx.trues, t);
	doPatch(if_cx.falses, f);
	//Should consider all the following cases!
	if(then_exp->kind == Tr_cx || else_exp->kind == Tr_cx){
		//set the value of r to be one.
		Temp_label setone = Temp_newlabel();
		if(then_exp->kind == Tr_cx){
            doPatch(then_exp->u.cx.trues, setone);
            doPatch(then_exp->u.cx.falses, done);
        }
		if(else_exp->kind == Tr_cx){
			doPatch(else_exp->u.cx.trues, setone);
			doPatch(else_exp->u.cx.falses, done);
		}
		T_exp ret = T_Eseq(T_Move(T_Temp(r), T_Const(0)),
					T_Eseq(if_cx.stm,
					T_Eseq(T_Label(t),
					T_Eseq(then_exp->kind==Tr_cx?then_exp->u.cx.stm:unNx(then_exp),
					T_Eseq(T_Label(setone),
					T_Eseq(T_Move(T_Temp(r), T_Const(1)),
					T_Eseq(T_Jump(T_Name(done), Temp_LabelList(done, NULL)),
					T_Eseq(T_Label(f),
					T_Eseq(else_exp->kind==Tr_cx?else_exp->u.cx.stm:unNx(else_exp),
					T_Eseq(T_Label(done), T_Temp(r))
					)))))))));
        //printf("%d\n", else_exp->kind);
        //pr_tree_exp(stdout,ret,0);
		return Tr_Ex(ret);
	}

	else if(then_exp->kind == Tr_nx && else_exp->kind == Tr_nx){
		T_stm then_nx = then_exp->u.nx;
		T_stm else_nx = else_exp->u.nx;
		T_stm ret = T_Seq(if_cx.stm,
					T_Seq(T_Label(t),
					T_Seq(then_nx,
					T_Seq(T_Jump(T_Name(done), Temp_LabelList(done, NULL)),
					T_Seq(T_Label(f),
					T_Seq(else_nx,
					T_Label(done)
					))))));
		return Tr_Nx(ret);
	}
    
    else if(then_exp->kind == Tr_ex || else_exp->kind == Tr_ex){
		T_exp then_ex = unEx(then_exp);
		T_exp else_ex = unEx(else_exp);
		//put the return value of else exp in a register.
		T_exp ret = T_Eseq(T_Move(T_Temp(r),T_Const(0)), 
					T_Eseq(if_cx.stm,
					T_Eseq(T_Label(t),
					T_Eseq(T_Move(T_Temp(r),then_ex),
					T_Eseq(T_Jump(T_Name(done), Temp_LabelList(done, NULL)),
					T_Eseq(T_Label(f),
					T_Eseq(T_Move(T_Temp(r),else_ex),
					T_Eseq(T_Label(done), T_Temp(r))
					)))))));
        //pr_stm(stdout, if_cx.stm, 0);
        //assert(0);
		return Tr_Ex(ret);
	}
    
	else{
        printf("%d %d\n", then_exp->kind, else_exp->kind);
		printf("unexpected case in translating if!\n");
		assert(0);
	}
}

Tr_exp Tr_seqExp(Tr_expList expList){
	T_exp eseq = NULL;
	for(Tr_expList expl = expList; expl; expl = expl->tail){
		if(!eseq){
            eseq = unEx(expl->head);
        }
		else eseq = T_Eseq(unNx(expl->head), eseq);
	}
	return Tr_Ex(eseq);
}

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals){
	//the second param of procEntryExit is uncertain.
    //1227 move the return value to %rax
    T_stm move_stm=NULL;
    int cnt = 0;
    //move all the formals to correct positions
    
    for(Tr_accessList p = formals; p; p = p->tail, cnt++){
        //printf("%d\n", cnt);
        Temp_temp reg;
         if(cnt<=5){
             if(cnt == 0) reg = F_RDI();
             else if(cnt==1) reg = F_RSI();
             else if(cnt==2) reg = F_RDX();
             else if(cnt==3) reg = F_RCX();
             else if(cnt==4) reg = F_R8();
             else if(cnt==5) reg = F_R9();
         }
         else{
             reg = Temp_newtemp();
             move_stm = (move_stm!=NULL)? T_Seq(move_stm, T_Move(T_Mem(T_Binop(T_plus, T_Temp(F_FP()), T_Const((cnt-4)*8))), T_Temp(reg))) : T_Move( T_Mem(T_Binop(T_plus, T_Temp(F_FP()), T_Const((cnt-4)*8))), T_Temp(reg));
             continue;
         }
         if(cnt==0&&level==Tr_outermost()) continue;
         if(p->head->access->kind == inReg){
             move_stm = (move_stm!=NULL)?T_Seq(move_stm, T_Move(T_Temp(p->head->access->u.reg), T_Temp(reg))): T_Move(T_Temp(p->head->access->u.reg), T_Temp(reg)); 
         }
         else{
             move_stm = (move_stm!=NULL)? T_Seq(move_stm, T_Move(T_Mem(T_Binop(T_plus, T_Temp(F_FP()), T_Const(p->head->access->u.offset))), T_Temp(reg))) : T_Move(T_Mem(T_Binop(T_plus, T_Temp(F_FP()), T_Const(p->head->access->u.offset))),T_Temp(reg));
         }
         
    }
    
	T_stm body_stm = F_procEntryExit1(level->frame, T_Move(T_Temp(F_RV()), unEx(body)));
	if(move_stm) glbl = F_FragList(F_ProcFrag(T_Seq(move_stm, body_stm), level->frame), glbl);
    else glbl = F_FragList(F_ProcFrag(body_stm, level->frame), glbl);
}

F_fragList Tr_getResult(){
	return glbl;
}

void Tr_init(){
    glbl = NULL;
}