#include <stdio.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "escape.h"
#include "table.h"
#include "env.h"

static void traverseExp(S_table env, int depth, A_exp e);
static void traverseDec(S_table env, int depth, A_dec d);
static void traverseVar(S_table env, int depth, A_var v);

static void traverseExp(S_table env, int depth, A_exp e){
    switch(e->kind){
        case A_varExp:{
            traverseVar(env, depth, e->u.var);
            break;
        }
        case A_nilExp:{
            break;
        }
        case A_intExp:{
            break;
        }
        case A_stringExp: {
            break;
        }
        case A_callExp:{
            for(A_expList p = e->u.call.args; p; p = p->tail){
                traverseExp(env, depth, p->head);
            }
            break;
        }
        case A_opExp:{
            traverseExp(env, depth, e->u.op.left);
            traverseExp(env, depth, e->u.op.right);
            break;
        }
        case A_recordExp:{
            for(A_efieldList p = e->u.record.fields; p; p = p->tail){
                traverseExp(env, depth, p->head->exp);
            }
            break;
        }
        case A_seqExp:{
            for(A_expList p = e->u.seq; p; p = p->tail){
                traverseExp(env, depth, p->head);
            }
            break;
        }
        case A_assignExp:{
            traverseVar(env, depth, e->u.assign.var);
            traverseExp(env, depth, e->u.assign.exp);
            break;
        }
        case A_ifExp:{
            traverseExp(env, depth, e->u.iff.test);
            traverseExp(env, depth, e->u.iff.then);
            if(e->u.iff.elsee!=NULL) traverseExp(env, depth, e->u.iff.elsee);
            break;
        }
        case A_whileExp:{
            traverseExp(env, depth, e->u.whilee.test);
            traverseExp(env, depth, e->u.whilee.body);
            break;
        }
        case A_forExp:{
            //1. the loop variable need to be treated as varDec.
            //2. the lifecycle problem
            traverseExp(env, depth, e->u.forr.lo);
            traverseExp(env, depth, e->u.forr.hi);
            S_beginScope(env);
            e->u.forr.escape = 0;
            S_enter(env, e->u.forr.var, E_EscapeEntry(depth, &(e->u.forr.escape)));
            traverseExp(env, depth, e->u.forr.body);
            S_endScope(env);
            break;
        }
        case A_breakExp:{
            break;
        }
        case A_letExp:{
            S_beginScope(env);
            for(A_decList p = e->u.let.decs; p; p = p->tail){
                traverseDec(env, depth, p->head);
            }
            traverseExp(env, depth, e->u.let.body);
            S_endScope(env);
            break;
        }
        case A_arrayExp:{
            traverseExp(env, depth, e->u.array.size);
            traverseExp(env, depth, e->u.array.init);
            break;
        }
    }
}

static void traverseVar(S_table env, int depth, A_var v){
	switch(v->kind){
		case A_simpleVar:{
			E_escapeEntry ent = (E_escapeEntry)S_look(env, v->u.simple);
            if(!ent){
               printf("%s\n", S_name(v->u.simple));
               assert(0);
               break;
            }
            if(depth > ent->depth){
                *(ent->escape) = 1;
            }    
            break;
		}
		case A_fieldVar:{
            //id
            traverseVar(env, depth, v->u.field.var);
            //field must be escape.
            break;
		}
		case A_subscriptVar:{
			traverseVar(env, depth, v->u.subscript.var);
            traverseExp(env, depth, v->u.subscript.exp);
		}
	}
}

static void traverseDec(S_table env, int depth, A_dec d){
    switch(d->kind){
        case A_functionDec:{
            A_fundecList funcs = d->u.function;
            for(A_fundecList func = funcs; func; func = func->tail){
                A_fundec fun = func->head;
                A_fieldList params = fun->params;
                S_beginScope(env);
                for(A_fieldList p = params; p; p = p->tail){
                    A_field f = p->head;
                    S_symbol fn = f->name;
                    f->escape = 0;
                    S_enter(env, fn, E_EscapeEntry(depth+1, &(f->escape)));
                }
                traverseExp(env, depth+1, fun->body);
                S_endScope(env);
            }
            
            break;
        }
        case A_varDec:{
            S_symbol var = d->u.var.var;
            d->u.var.escape = 0;
            S_enter(env, var, E_EscapeEntry(depth, &(d->u.var.escape)));
            traverseExp(env, depth, d->u.var.init);
            break;
        }
        case A_typeDec:{
           //Notice that even for recordTy, all its fields must be escape, because they're pointers.
           //for record fields, they are A_efield(no escape=0) not A_field(can escape=0)
            break;
        }
    }
}

void Esc_findEscape(A_exp exp) {
    //your code here
    S_table env = S_empty();
    traverseExp(env, 0, exp);
}
