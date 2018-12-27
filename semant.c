#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "helper.h"
#include "env.h"
#include "semant.h"
#include "translate.h"
#include "prabsyn.h"

/*Lab4: Your implementation of lab4*/
//A_callExp, all params are escape
//Problem: currently cannot determine the postion of fieldVars on heap.
static int streq(string a, string b)
{
 if((int)a==0 || (int)b==0) return 1;
 return !strcmp(a,b);
}

struct expty 
{
	Tr_exp exp; 
	Ty_ty ty;
};

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

Ty_ty actual_ty(Ty_ty pseudo){
	Ty_ty p = pseudo;
	while(p->kind == Ty_name){
		p = p->u.name.ty;
        //if(!p) return Ty_Nil();
	}
	return p;
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params){
	Ty_tyList ans = NULL;
	for(; params; params = params->tail){
		S_symbol param_typ = params->head->typ;
		E_enventry ent = S_look(tenv, param_typ);
		if(ent){
			Ty_ty param_ty = ent->u.var.ty;
			//printf("%s %s\n", S_name(params->head->name), S_name(param_typ));
			ans = Ty_TyList(param_ty, ans);
		}
		else ans = Ty_TyList(Ty_Void(), ans);
	}
	return ans;
}

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level l, Temp_label label){
	switch(v->kind){
		case A_simpleVar:{
			E_enventry x = S_look(venv, get_simplevar_sym(v));
			if(x && x->kind == E_varEntry){
				return expTy(Tr_simpleVar(x->u.var.access, l), actual_ty(x->u.var.ty));
			}
			else{
				EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
				return expTy(Tr_nop(), Ty_Int());
			}
		}
		case A_fieldVar:{
			S_symbol id = get_fieldvar_sym(v);
			A_var var = get_fieldvar_var(v);
			E_enventry x = S_look(venv, id);
			
			if(x==NULL || x->kind != E_varEntry){
				EM_error(v->pos, "undefined variable %s", S_name(id));
				return expTy(Tr_nop(), Ty_Int());
			}
			
			struct expty var_trans = transVar(venv, tenv, var, l, label);
			//printf("%d\n", var_trans.ty->kind);
			
			Ty_ty var_ty = var_trans.ty;
			if(var_ty->kind == Ty_record){
				Ty_fieldList fl = var_ty->u.record;
				for(int cnt = 0; fl; fl = fl->tail, ++cnt){
					S_symbol cur_field_id = fl->head->name;
					if(cur_field_id == id){
						Ty_ty cur_field_ty = fl->head->ty;
						//exp: need base, offset. offset related to position on stack
                        return expTy(Tr_fieldVar(var_trans.exp, cnt), cur_field_ty);
					}
				}
				EM_error(var->pos, "field %s doesn't exist", S_name(id));
				return expTy(Tr_nop(), Ty_Int());
			}	
			else{
				EM_error(var->pos, "not a record type");
				return expTy(Tr_nop(), Ty_Int());
			}
			
		}
		case A_subscriptVar:{
			A_exp id = get_subvar_exp(v);
			A_var var = get_subvar_var(v);
			struct expty var_trans = transVar(venv, tenv, var, l, label);
			struct expty id_trans = transExp(venv, tenv, id, l, label);
			if(var_trans.ty->kind != Ty_array){
				EM_error(v->pos, "array type required");
                return expTy(Tr_nop(), Ty_Int());
			}
			if(id_trans.ty->kind != Ty_int){
				EM_error(v->pos, "subscript must be integer");
				return expTy(Tr_nop(), Ty_Int());
			}
			//return type of element, not ty_array
			return expTy(Tr_subscriptVar(var_trans.exp, id_trans.exp), var_trans.ty->u.array);
		}
	}

}

struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level l, Temp_label label){
	switch(a->kind){
		case A_opExp:{
			//A op B
			A_oper oper = get_opexp_oper(a);
			struct expty left = transExp(venv, tenv, get_opexp_left(a), l, label);
			struct expty right = transExp(venv, tenv, get_opexp_right(a), l, label);
			if(oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp){
				if(left.ty->kind != Ty_int){
					EM_error(get_opexp_left(a)->pos, "integer required");
				}
				if(right.ty->kind != Ty_int){
					EM_error(get_opexp_right(a)->pos, "integer required");
				}
				return expTy(Tr_opExp(oper, left.exp, right.exp), Ty_Int());
			}
			if(oper == A_eqOp || oper == A_gtOp || oper == A_ltOp || oper == A_geOp || oper == A_leOp || oper == A_neqOp){
				if((left.ty->kind == Ty_nil && right.ty->kind == Ty_record) || 
					(right.ty->kind == Ty_nil && left.ty->kind == Ty_record)){
					return expTy(Tr_nop(), Ty_Int());
				}
				if(left.ty->kind != right.ty->kind){
					EM_error(get_opexp_left(a)->pos, "same type required");
					return expTy(Tr_nop(), Ty_Int());
				}
				return expTy(Tr_cmpExp(oper, left.exp, right.exp), Ty_Int());
			}
		}
		
		case A_varExp:{
			//return error if undeclared
			return transVar(venv, tenv, a->u.var, l, label);
		}
		case A_nilExp:{
			return expTy(Tr_nop(), Ty_Nil());
		}
		case A_intExp:{
			return expTy(Tr_intExp(a->u.intt), Ty_Int());
		}
		case A_stringExp:{
			return expTy(Tr_stringExp(a->u.stringg), Ty_String());
		}
		case A_callExp:{
			S_symbol func = get_callexp_func(a);
			A_expList args = get_callexp_args(a);
			E_enventry ent = S_look(venv, func);
            //printf("\n\n%s\n", S_name(func));
			//check whether function is defined
			if(!ent){
				EM_error(a->pos, "undefined function %s", S_name(func));
				return expTy(Tr_nop(), Ty_Nil());
			}

			Ty_tyList formals_ = ent->u.fun.formals;
			Ty_tyList formals = NULL;
			for(Ty_tyList formal_ = formals_; formal_; formal_ = formal_->tail) formals = Ty_TyList(formal_->head, formals);
			Ty_ty result = ent->u.fun.result;
			//check the types
			A_expList arg;
			Ty_tyList formal;
			
			//for(arg = args, formal = formals; arg && formal; arg = arg->tail, formal = formal->tail);
            //The arguments will be found in venv. (Update: 20181221)
            Tr_expList call_args = NULL;
			for(arg = args, formal = formals; arg && formal; arg = arg->tail, formal = formal->tail){
				struct expty cur_arg = transExp(venv, tenv, arg->head, l, label);
                call_args = Tr_ExpList(cur_arg.exp, call_args);
                //temporarily, set all parameters to be escape
                //Tr_access acc = Tr_allocLocal(l, 1);
				if(cur_arg.ty->kind != formal->head->kind){
					//printf("%d %d\n", cur_arg.ty->u.name.ty, formal->head->kind);
					//EM_error(arg->head->pos, "argument type mismatch");
					if(cur_arg.ty->kind == Ty_name){
                        if(cur_arg.ty->u.name.ty == formal->head->kind) continue;
                    }
                    EM_error(arg->head->pos, "para type mismatch");
					return expTy(Tr_nop(), result);
				}
			}
			
			if(arg){
				//EM_error(arg->head->pos, "more arguments than expectd");
				EM_error(arg->head->pos, "too many params in function %s", S_name(func));
				return expTy(Tr_nop(), result);
			}
			else if(formal && formal->head->kind != Ty_void){
				//EM_error(a->pos, "fewer arguments than expected");
				EM_error(a->pos, "para type mismatch");
				return expTy(Tr_nop(), result);
			}
            //reverse the reversed call_args back
            Tr_expList real_args = NULL;
            for(Tr_expList p = call_args; p; p = p->tail){
                real_args = Tr_ExpList(p->head, real_args);
            }
			//ent->u.fun.level: declared level; l: used level
			return expTy(Tr_callExp(ent->u.fun.label, ent->u.fun.level, l, real_args), result);
		}
		case A_recordExp:{
			//S_symbol typ = get_recordexp_typ(a);
			A_efieldList fields = get_recordexp_fields(a);
			Ty_fieldList fl = NULL;
            int cnt = 0;
            Tr_expList fieldExps = NULL;
			while(fields){
				S_symbol field_symbol = fields->head->name;
				//S_look should return E_enventry
				A_exp field_exp = fields->head->exp;
				struct expty field_expty = transExp(venv, tenv, field_exp, l, label);
                fieldExps = Tr_ExpList(field_expty.exp, fieldExps);
				Ty_ty field_ty = field_expty.ty;
				Ty_field field = Ty_Field(field_symbol, field_ty);
				if(!fl){	
					fl = Ty_FieldList(field, NULL);
				}
				else{
					Ty_fieldList new_fl = Ty_FieldList(field, fl);
					fl = new_fl;
				}
				fields = fields->tail;
                ++cnt;
			}
			//This Tr_exp term is problematic
			return expTy(Tr_recordExp(cnt, fieldExps, l), Ty_Record(fl));
		}
		case A_seqExp:{
			A_expList cur_exp = get_seqexp_seq(a);
			Tr_expList reversed=NULL;
			//fix here for test43
			if(cur_exp==NULL) return expTy(Tr_nop(), Ty_Nil());
			while(cur_exp->tail){
                struct expty cur_expty = transExp(venv, tenv, cur_exp->head, l, label);
				reversed = Tr_ExpList(cur_expty.exp, reversed);
				cur_exp = cur_exp->tail;
			}
			struct expty cur_expty = transExp(venv, tenv, cur_exp->head, l, label);
			reversed = Tr_ExpList(cur_expty.exp, reversed);
			return expTy(Tr_seqExp(reversed), cur_expty.ty);
		}
		case A_assignExp:{
			//printf("%d\n", get_assexp_var(a)->kind);
            struct expty var = transVar(venv, tenv, get_assexp_var(a), l, label);
			struct expty e = transExp(venv, tenv, get_assexp_exp(a), l, label);
			if(var.ty->kind == Ty_record && e.ty->kind == Ty_nil){
				return expTy(Tr_nop(), Ty_Nil());
			}
			else if(var.ty->kind != Ty_nil && e.ty->kind == Ty_nil){
				EM_error(a->pos, "init should not be nil without type specified");
			}
			else if(var.ty->kind != e.ty->kind){
				if(var.ty->kind != Ty_array && var.ty->kind != Ty_record){
					EM_error(a->pos, "unmatched assign exp");
					return expTy(Tr_nop(), Ty_Nil());
				}
				else if(var.ty->kind == Ty_array){
					if(var.ty->u.array->kind != e.ty->kind){
						EM_error(a->pos, "unmatched assign exp");
						return expTy(Tr_nop(), Ty_Nil());
					}
				}
				else if(var.ty->kind == Ty_record){
					//if(var.ty->u.record->kind != e.ty->kind) EM_error(a->pos, "unmatched assign exp");
				}
			}
			return expTy(Tr_assignExp(var.exp, e.exp), Ty_Nil());
		}
		
		case A_ifExp:{
			struct expty test = transExp(venv, tenv, get_ifexp_test(a), l, label);
			struct expty then = transExp(venv, tenv, get_ifexp_then(a), l, label);
			if(get_ifexp_else(a)){
				struct expty else_ = transExp(venv, tenv, get_ifexp_else(a), l, label);
				if(then.ty->kind != else_.ty->kind && else_.ty->kind != Ty_nil){
					EM_error(get_ifexp_else(a)->pos, "then exp and else exp type mismatch");
					return expTy(Tr_nop(), then.ty);
				}
				return expTy(Tr_ifExp(test.exp, then.exp, else_.exp), then.ty);
			}
			else if(then.ty->kind != Ty_nil){
				EM_error(get_ifexp_then(a)->pos, "if-then exp's body must produce no value");
				return expTy(Tr_nop(), Ty_Nil());
			}
			return expTy(Tr_ifExp(test.exp, then.exp, Tr_nop()), then.ty);
		}
		
		case A_whileExp:{
			//while E do E
			Temp_label done_label = Temp_newlabel();
			struct expty test = transExp(venv, tenv, get_whileexp_test(a), l, done_label);
			
			struct expty body = transExp(venv, tenv, get_whileexp_body(a), l, done_label);
			if(test.ty->kind != Ty_int){
				EM_error(get_whileexp_test(a)->pos, "integer required");
				return expTy(Tr_nop(), Ty_Nil());
			}
			if(body.ty->kind != Ty_nil){
				EM_error(get_whileexp_body(a)->pos, "while body must produce no value");
				return expTy(Tr_nop(), Ty_Nil());
			}
			return expTy(Tr_whileExp(test.exp, body.exp, done_label), Ty_Nil());
		}

		
		case A_forExp:{
			//for id = exp1 to exp2 do exp3
			//TBD: loop variable can't be assigned
			//here var is S_Symbol
			//struct expty var = transVar(venv, tenv, get_forexp_var(a));
			S_beginScope(venv);
			S_symbol id = get_forexp_var(a);
			string id_name = S_name(id);
			Temp_temp id_reg = Temp_newtemp();
			S_enter(venv, id, E_VarEntry(Tr_Access(l,InReg(id_reg)), Ty_Int()));
			struct expty lo = transExp(venv, tenv, get_forexp_lo(a), l, label);
			struct expty hi = transExp(venv, tenv, get_forexp_hi(a), l, label);
			Temp_label done_label = Temp_newlabel();
			struct expty body = transExp(venv, tenv, get_forexp_body(a), l, done_label);
			if(lo.ty->kind != Ty_int){
				EM_error(get_forexp_lo(a)->pos, "for exp's range type is not integer");
				return expTy(Tr_nop(), Ty_Nil());
			}
			if(hi.ty->kind != Ty_int){
				EM_error(get_forexp_hi(a)->pos, "for exp's range type is not integer");
				return expTy(Tr_nop(), Ty_Nil());
			}
			if(body.ty->kind != Ty_nil){
				EM_error(get_forexp_body(a)->pos, "for body must produce no value");
				return expTy(Tr_nop(), Ty_Nil());
			}

			A_exp cur_exp_ = get_forexp_body(a);
			if(cur_exp_->kind == A_seqExp){	
				A_expList cur_exp = cur_exp_->u.seq;		
				while(cur_exp){
					//loop variable must be simple variable
					//this field is strange

					if(cur_exp->head->kind == A_assignExp){
						A_var cur_var = cur_exp->head->u.assign.var;
						if(cur_var->kind == A_simpleVar){
							S_symbol new_id = cur_var->u.simple;
							string new_id_name = S_name(new_id);

							if(streq(id_name, new_id_name)){
								EM_error(cur_var->pos, "loop variable can't be assigned");
								return expTy(Tr_nop(), Ty_Nil());
							}
						}
					}
					cur_exp = cur_exp->tail;
				}
			}
			else{
				if(cur_exp_->kind == A_assignExp){
					A_var cur_var = cur_exp_->u.assign.var;
					if(cur_var->kind == A_simpleVar){
						S_symbol new_id = cur_var->u.simple;
						string new_id_name = S_name(new_id);
						if(streq(id_name, new_id_name)){
							EM_error(cur_var->pos, "loop variable can't be assigned");
							return expTy(Tr_nop(), Ty_Nil());
						}
					}
				}
			}
			S_endScope(venv);
			return expTy(Tr_forExp(Tr_Ex(T_Temp(id_reg)), lo.exp, hi.exp, body.exp, done_label), Ty_Nil());
		}

		case A_breakExp:{
			return expTy(Tr_breakExp(label), Ty_Nil());
		}
		
		case A_letExp:{
			//book
			//let D in E end
			struct expty exp;
            Tr_expList el = NULL;
			A_decList d;
			S_beginScope(venv);
			S_beginScope(tenv);
			for(d = get_letexp_decs(a); d; d = d->tail){
				Tr_exp e = transDec(venv, tenv, d->head, l, label);
                el = Tr_ExpList(e, el);
			}
			exp = transExp(venv, tenv, get_letexp_body(a), l, label);
            el = Tr_ExpList(exp.exp, el);
			S_endScope(venv);
			S_endScope(tenv);
			exp.exp = Tr_seqExp(el);
			return exp;
		}
		
		case A_arrayExp:{
			//here typ is S_Symbol
			//S_symbol id = get_arrayexp_typ(a);
			struct expty arr_size = transExp(venv, tenv, get_arrayexp_size(a), l, label);
			struct expty arr_init = transExp(venv, tenv, get_arrayexp_init(a), l, label);
			if(arr_size.ty->kind != Ty_int){
				EM_error(get_arrayexp_size(a)->pos, "array's size type is not integer");
				return expTy(Tr_nop(), Ty_Array(arr_init.ty));
			}
			return expTy(Tr_arrayExp(arr_size.exp, arr_init.exp), Ty_Array(arr_init.ty));
		}
		
	}
	//return expTy(NULL, NULL);
	assert(0);
}

Tr_exp transDec(S_table venv, S_table tenv, A_dec d, Tr_level l, Temp_label label){
	switch(d->kind){
		case A_varDec:{
			A_exp init = get_vardec_init(d);
			S_symbol var = get_vardec_var(d);
			S_symbol typ = get_vardec_typ(d);
			bool escape = d->u.var.escape;
			//E_enventry x1 = S_look(tenv, typ);
			//Ty_print(x1->u.var.ty);
			struct expty e = transExp(venv, tenv, init, l, label);
            
			if(typ == NULL && init->kind != A_recordExp && init->kind != A_arrayExp 
				&& init->kind != A_nilExp){
                Tr_access cur_acc = Tr_allocLocal(l, escape);
				S_enter(venv, var, E_VarEntry(cur_acc, e.ty));
				//return e.exp;
                return Tr_assignExp(Tr_simpleVar(cur_acc, l), e.exp);
			}
			else{
				if(e.ty->kind != Ty_nil){
					Ty_ty req_typ;
					if(typ){
						E_enventry x = S_look(tenv, typ);
						req_typ = x->u.var.ty;
						//printf("%d %d\n", req_typ, e.ty);
					}
					else{
						req_typ = e.ty;
					}
					
					if(req_typ->kind != e.ty->kind){
						//EM_error(init->pos, "wrong type for variable %s", S_name(var));
						EM_error(init->pos, "type mismatch");
						//don't allocate
						S_enter(venv, var, E_VarEntry(Tr_Access(l,NULL), e.ty));
						return Tr_nop();
					}

					else{
						switch(req_typ->kind){
							case Ty_record:{
								//restore the original type of init_type
								S_symbol init_typ = init->u.record.typ;
								E_enventry init_org_ent = S_look(tenv, init_typ);
								if(init_org_ent==NULL || init_org_ent->kind != E_varEntry){
									EM_error(d->pos, "undefined type %s", S_name(init_typ));
									return Tr_nop();
								}
								Ty_ty init_org_ty = init_org_ent->u.var.ty;

								if(init_org_ty->kind != Ty_name){
									if (typ && init_typ && !streq(S_name(typ), S_name(init_typ))) EM_error(d->pos, "type mismatch");
								}
								else{
									S_symbol init_org_typ = init_org_ty->u.name.sym;
									if(!streq(S_name(typ), S_name(init_org_typ))){
										EM_error(d->pos, "type mismatch");
										return Tr_nop();
									}
								}
								break;
							}
							case Ty_array:{
								//intuition: if originally the init exp is led by a namety,
								//We must restore the true type of this namety.
								S_symbol init_typ = init->u.array.typ;
                                //printf("%s %d\n",S_name(init_typ), init_typ);
								E_enventry init_org_ent = S_look(tenv, init_typ);
								//printf("Found: %d\n", init_org_ent!=NULL);
								//get the initial ty of init, instead of the translated one
								//Ty_ty init_org_ty = init_org_ent->u.var.ty is OK only when it is namety
								Ty_ty init_org_ty = init_org_ent->u.var.ty;
                                //Ty_print(init_org_ty);printf("%s\n",S_name(typ));

								//The specific initial value
								A_exp init_init = init->u.array.init;
								//struct expty parsed_init_expty = transExp(venv, tenv, init_init, l, label);
								Ty_ty parsed_init_ty = e.ty->u.array;
								//Ty_print(parsed_init_ty);
								
								if(init_org_ty->kind != Ty_name){
									//EM_error(d->pos, "different array types");
									if(typ && !streq(S_name(typ), S_name(init_typ))){
                                        //fix a bug in lab5.
                                        if(parsed_init_ty->kind == init_org_ty->u.array->kind) break;
                                        EM_error(d->pos, "type mismatch");
                                        return Tr_nop();
                                    }
									else if(parsed_init_ty->kind != init_org_ty->u.array->kind){EM_error(d->pos, "type mismatch");return Tr_nop();}
								}
								else{
									S_symbol init_org_typ = init_org_ty->u.name.sym;
									if(!streq(S_name(typ), S_name(init_org_typ))){
										//EM_error(d->pos, "different array types");
										EM_error(d->pos, "type mismatch");
										return Tr_nop();
									}
								}
								
								break;
							}
							default: break;
						}

					}
                    Tr_access cur_acc = Tr_allocLocal(l, escape);
					S_enter(venv, var, E_VarEntry(cur_acc, e.ty));
					return Tr_assignExp(Tr_simpleVar(cur_acc, l), e.exp);
				}
				else{
					if(typ){
						E_enventry x = S_look(tenv, typ);
						Ty_ty req_typ = x->u.var.ty;
						if(req_typ->kind != Ty_record){
							EM_error(init->pos, "init should not be nil without type specified");
							return Tr_nop();
						}
					}
					else{
						EM_error(init->pos, "init should not be nil without type specified");
						return Tr_nop();
					}
					S_enter(venv, var, E_VarEntry(Tr_allocLocal(l, escape), e.ty));
					return e.exp;
				}
			}

		}
		case A_typeDec:{
			//TBD: recursive(2 passes)
			A_nametyList typ = get_typedec_list(d);
			S_table tmp_env = tenv, temp_env = E_base_tenv();
			//pass 1
			for(A_nametyList typ_ = typ; typ_; typ_ = typ_->tail){
				//printf("type_: %s %d\n",S_name(typ_->head->name), typ_->head->name);
				E_enventry ent = S_look(temp_env, typ_->head->name);
				if(ent){
                    EM_error(d->pos, "two types have the same name");
				}
				S_enter(tmp_env, typ_->head->name, E_VarEntry(Tr_Access(l,NULL),Ty_Name(typ_->head->name, NULL)));
                S_enter(temp_env, typ_->head->name, E_VarEntry(Tr_Access(l,NULL),Ty_Name(typ_->head->name, NULL)));
			}
			//pass 2
			for(; typ; typ = typ->tail){
				//printf("type: %s %d\n",S_name(typ->head->name), typ->head->name);
				//printf("%d\n", typ->head->ty->kind);
                E_enventry ent = S_look(tmp_env, typ->head->name);
				if(!ent){
					EM_error(d->pos, "undefined type");
				}
				Ty_ty cur_ty = transTy(tmp_env, typ->head->ty);
				Ty_ty actual_cur_ty = actual_ty(cur_ty);
                if(actual_cur_ty->kind==Ty_record){
                    Ty_fieldList fl = actual_cur_ty->u.record;
                    for(;fl && fl->head;fl=fl->tail){
                        //S_enter(venv, fl->head->name, E_VarEntry(Tr_Access(l,NULL), fl->head->ty));
                        S_enter(venv, fl->head->name, E_VarEntry(Tr_allocLocal(l, 1), fl->head->ty));
                    }
                }
                //printf("ACTUAL TY: %d\n", actual_cur_ty->kind);
				//update environment, important!
				ent->u.var.ty = actual_cur_ty;
				//ugly, to be modified. contain unresolved name type
				if(!(actual_cur_ty->kind>=0 && actual_cur_ty->kind<=6)){
					EM_error(d->pos, "illegal type cycle");
				}
				//The Tr_access term is not important here!
				S_enter(tenv, typ->head->name, E_VarEntry(Tr_allocLocal(l, 1), actual_cur_ty));
			}
			//printf("end\n");
			return Tr_nop();
		}
		case A_functionDec:{
			//TBD: recursive modification(this implementation is ugly!) TBD: lifecycle problem(introduced in lab5)
			A_fundecList fl = get_funcdec_list(d);
			S_table tmp_venv = venv, temp_venv = E_base_venv();
			S_table tmp_tenv = tenv;//E_base_tenv();
            
            Temp_label newLabel;
            Tr_level newLevel;
            
			for(; fl; fl = fl->tail){
				A_fundec f = fl->head;
				Ty_ty resultTy;
				E_enventry ent;
                newLabel = Temp_namedlabel(S_name(f->name));
				if(f->result){
					ent = S_look(tmp_tenv, f->result);
					if(ent) resultTy = ent->u.var.ty;
					else resultTy = Ty_Nil();
				}
				else resultTy = Ty_Nil();
                
				Ty_tyList formalTys = makeFormalTyList(tmp_tenv, f->params);
                //staticLink
                U_boolList boolList= NULL;
				A_fieldList l_, ls=NULL, ls_backup; Ty_tyList t; //reversed....
				for(l_ = f->params; l_; l_ = l_->tail) ls = A_FieldList(l_->head, ls);
                ls_backup = ls;
				for(t = formalTys; ls; ls = ls->tail, t = t->tail){
					boolList = U_BoolList(ls->head->escape, boolList);
				}
                boolList = U_BoolList(1, boolList);
				newLevel =  Tr_newLevel(l, newLabel, boolList);
                //Here, the positions should be RDI, RSI,... (updated 20181221) 
                //Original implementation is wrong. No need to allocLocal!
                int cnt = 0;
                for(t = formalTys, ls = ls_backup; ls; ls = ls->tail, t = t->tail, cnt++){
                    //printf("%s: %s\n", S_name(f->name), S_name(ls->head->name));
                    Temp_temp reg;
                    if(cnt<5){
                        if(cnt==0) reg = F_RSI();
                        else if(cnt==1) reg = F_RDX();
                        else if(cnt==2) reg = F_RCX();
                        else if(cnt==3) reg = F_R8();
                        else if(cnt==4) reg = F_R9();
                        S_enter(venv, ls->head->name, E_VarEntry(Tr_Access(newLevel, InReg(reg)), t->head));
                    }
                    else{
                        //because offset 0 is actually the static link. 8 = F_wordSize
                        S_enter(venv, ls->head->name, E_VarEntry(Tr_Access(newLevel, InFrame(8 * (cnt-4))), t->head));
                    }
				}
				ent = S_look(temp_venv, f->name);
				if(!ent){
					S_enter(venv, f->name, E_FunEntry(newLevel, newLabel, formalTys, resultTy));
                    S_enter(temp_venv, f->name, E_FunEntry(newLevel, newLabel, formalTys, resultTy));
				}
				else{
					EM_error(d->pos, "two functions have the same name");
				}
			}

			fl = get_funcdec_list(d);
			for(; fl; fl = fl->tail){
				A_fundec f = fl->head;
				E_enventry ent = S_look(venv, f->name), ent1;
				if(!ent){
					EM_error(d->pos, "undefined function %s", S_name(f->name));
					//S_enter(venv, f->name, ent);
					continue;
				}
				Ty_ty resultTy;
				if(f->result){
					ent1 = S_look(tmp_tenv, f->result);
					if(ent1) resultTy = ent1->u.var.ty;
					else resultTy = Ty_Nil();
				}
				else resultTy = Ty_Nil();

				Ty_tyList formalTys = ent->u.fun.formals;
				
				//S_beginScope(tmp_venv);
				struct expty ret_val = transExp(tmp_venv, tenv, f->body, ent->u.fun.level, ent->u.fun.label);
                Tr_procEntryExit(ent->u.fun.level, ret_val.exp, Tr_formals(ent->u.fun.level)); //fix a bug. originally using newLevel, but its (relatively) global.
                
				if(ret_val.ty->kind != resultTy->kind){
					if(ret_val.ty->kind != Ty_nil && resultTy->kind == Ty_nil) EM_error(f->pos, "procedure returns value");
					//TBD: return type mismatch is a problem!
					//else EM_error(f->pos, "return type mismatch");
				}
				//S_endScope(tmp_venv);
			}
			
			return Tr_nop();
		}
	}
}

Ty_ty transTy(S_table tenv, A_ty a){
	//TBD: mutually recursive, recordTy
	switch(a->kind){
		case A_nameTy:{
			S_symbol name = get_ty_name(a);
			E_enventry ent = S_look(tenv, name);
			Ty_ty namety;
			if(ent == NULL){
				namety = NULL;
			}
			else{
				namety = ent->u.var.ty;
			}
			return Ty_Name(name,namety);
		}
		case A_recordTy:{
			A_fieldList fl = get_ty_record(a);
			Ty_fieldList tl = NULL;
			for(; fl; fl = fl->tail){
				S_symbol cur_name = fl->head->name;
				S_symbol cur_typ = fl->head->typ;
				E_enventry ent = S_look(tenv, cur_typ);
				Ty_field tf;
				if(ent == NULL){
					EM_error(a->pos, "undefined type %s", S_name(cur_typ));
					tf = Ty_Field(cur_name, NULL);
				}
				else{
					//ugly the following if means this is recursive type
					if(!(ent->u.var.ty->kind >= 0 && ent->u.var.ty->kind <=6)){
						ent->u.var.ty->kind = Ty_record;
					}
					tf = Ty_Field(cur_name, ent->u.var.ty);
				}
				if(tl == NULL){
					tl = Ty_FieldList(tf, NULL);
				}
				else{
					tl = Ty_FieldList(tf, tl);
				}
			}
			return Ty_Record(tl);
		}
		case A_arrayTy:{
			S_symbol array = get_ty_array(a); //type of array
			E_enventry ent = S_look(tenv, array);
			Ty_ty arrayty;
			if(ent == NULL){
				arrayty = Ty_Array(NULL);
			}
			else{
				//printf("%d\n", ent->u.var.ty);
				arrayty = Ty_Array(ent->u.var.ty);
			}
			return arrayty;
		}
	}
    printf("Invalid Type!\n");
    assert(0);
}


F_fragList SEM_transProg(A_exp exp){
    Tr_init();
	Temp_label label = Temp_newlabel();
	Tr_level OUTMOST = Tr_outermost();
	S_table venv = E_base_venv();
	S_table tenv = E_base_tenv();
	struct expty final = transExp(venv, tenv, exp, OUTMOST, label);
    Tr_procEntryExit(OUTMOST, final.exp, Tr_formals(OUTMOST));
	return Tr_getResult();
}

