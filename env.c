#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "env.h" 

/*Lab4: Your implementation of lab4*/
//The provided file is problematic.
//1. The binder of each table should be a E_envEntry type
//2. return NULL is invalid. Should return Ty_nil.

E_escapeEntry E_EscapeEntry(int d, bool *escape){
    E_escapeEntry entry = checked_malloc(sizeof(*entry));
    entry->depth = d;
    entry->escape = escape;
    return entry;
}

E_enventry E_VarEntry(Tr_access access, Ty_ty ty)
{
	E_enventry entry = checked_malloc(sizeof(*entry));

	entry->u.var.access = access;
	entry->u.var.ty = ty;
    //printf("%d %d\n", access, ty->kind);
	return entry;
}

E_enventry E_ROVarEntry(Tr_access access, Ty_ty ty)
{
	E_enventry entry = checked_malloc(sizeof(*entry));
    entry->kind = E_varEntry;
	entry->u.var.access = access;
	entry->u.var.ty = ty;
	entry->readonly = 1;
	return entry;
}

E_enventry E_FunEntry(Tr_level level, Temp_label label, Ty_tyList formals, Ty_ty result)
{
	E_enventry entry = checked_malloc(sizeof(*entry));
    entry->kind = E_funEntry;
	entry->u.fun.level = level;
	entry->u.fun.label = label;
	entry->u.fun.formals = formals;
	entry->u.fun.result = result;
	return entry;
}

//sym->value
//type_id(name, S_symbol) -> type (Ty_ty)
S_table E_base_tenv(void)
{
	S_table table = S_empty();
	S_enter(table, S_Symbol("int"), E_VarEntry(NULL,Ty_Int()));
	S_enter(table, S_Symbol("string"), E_VarEntry(NULL,Ty_String()));
	return table;

	return table;
}

S_table E_base_venv(void)
{
	S_table venv;

	Ty_ty result;
	Ty_tyList formals;
	
	Temp_label label = NULL;
	Tr_level level;
	
	level = Tr_outermost();
	venv = S_empty();

	S_enter(venv,S_Symbol("flush"),E_FunEntry(level,Temp_namedlabel(String("flush")),NULL,Ty_Nil()));
	
	result = Ty_Int();

	formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_Int();
	formals->tail = NULL;
	S_enter(venv,S_Symbol("exit"),E_FunEntry(level,Temp_namedlabel(String("exit")),formals,Ty_Nil()));

	S_enter(venv,S_Symbol("not"),E_FunEntry(level,Temp_namedlabel(String("not")),formals,result));

	result = Ty_String();
	
	S_enter(venv,S_Symbol("chr"),E_FunEntry(level,Temp_namedlabel(String("chr")),formals,result));

	S_enter(venv,S_Symbol("getchar"),E_FunEntry(level,Temp_namedlabel(String("getchar")),NULL,result));

	formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_String();
	formals->tail = NULL;

	S_enter(venv,S_Symbol("print"),E_FunEntry(level,Temp_namedlabel(String("print")),formals,Ty_Nil()));
    
    formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_Int();
	formals->tail = NULL;

	S_enter(venv,S_Symbol("printi"),E_FunEntry(level,Temp_namedlabel(String("printi")),formals,Ty_Nil()));
    
	result = Ty_Int();
    formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_String();
	formals->tail = NULL;
	S_enter(venv,S_Symbol("ord"),E_FunEntry(level,Temp_namedlabel(String("ord")),formals,result));

	S_enter(venv,S_Symbol("size"),E_FunEntry(level,Temp_namedlabel(String("size")),formals,result));

	result = Ty_String();
	formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_String();
	formals->tail = checked_malloc(sizeof(*formals));
	formals->tail->head = Ty_String();
	S_enter(venv,S_Symbol("concat"),E_FunEntry(level,Temp_namedlabel(String("concat")),formals,result));

	formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_String();
	formals->tail = checked_malloc(sizeof(*formals));
	formals->tail->head = Ty_Int();
	formals->tail->tail = checked_malloc(sizeof(*formals));
	formals->tail->tail->head = Ty_Int();
	S_enter(venv,S_Symbol("substring"),E_FunEntry(level,Temp_namedlabel(String("substring")),formals,result));


	return venv;
}
