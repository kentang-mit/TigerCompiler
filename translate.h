#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "util.h"
#include "absyn.h"
#include "temp.h"
#include "frame.h"
#include "tree.h"

/* Lab5: your code below */
typedef struct Tr_level_ *Tr_level;

typedef struct Tr_exp_ *Tr_exp;

struct Tr_access_{
	Tr_level level;
	F_access access;
};
typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ *Tr_accessList;


typedef struct Tr_expList_ *Tr_expList;
struct Tr_expList_{
	Tr_exp head;
	Tr_expList tail;
};

typedef struct patchList_ *patchList;
struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};

struct Cx 
{
	patchList trues; 
	patchList falses; 
	T_stm stm;
};


Tr_exp Tr_Ex(T_exp ex);

Tr_access Tr_Access(Tr_level level, F_access access);
Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

Tr_level Tr_outermost(void);

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);

Tr_accessList Tr_formals(Tr_level level);

Tr_access Tr_allocLocal(Tr_level level, bool escape);

//problem regarding to inconsistent pointer type: function not defined in header!
Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail);
Tr_exp Tr_nop();
Tr_exp Tr_intExp(int i);
Tr_exp Tr_staticLink(Tr_level used, Tr_level declared);
Tr_exp Tr_simpleVar(Tr_access access, Tr_level level);
Tr_exp Tr_fieldVar(Tr_exp base, int offset);
Tr_exp Tr_subscriptVar(Tr_exp base, Tr_exp idx);
Tr_exp Tr_nilExp();
Tr_exp Tr_opExp(A_oper op, Tr_exp left, Tr_exp right);
Tr_exp Tr_cmpExp(A_oper op, Tr_exp left, Tr_exp right);
Tr_exp Tr_stringExp(string s);
Tr_exp Tr_recordExp(int cnt);
Tr_exp Tr_arrayExp(Tr_exp cnt, Tr_exp value);
Tr_exp Tr_whileExp(Tr_exp cond_exp, Tr_exp body_exp, Temp_label bTarget);
Tr_exp Tr_forExp(Tr_exp id_exp, Tr_exp lo, Tr_exp hi, Tr_exp body_exp, Temp_label bTarget);
Tr_exp Tr_breakExp(Temp_label bTarget);
Tr_exp Tr_callExp(Temp_label fun_label, Tr_level fun_level, Tr_level cur_level, Tr_expList args);
Tr_exp Tr_assignExp(Tr_exp var, Tr_exp e);
Tr_exp Tr_ifExp(Tr_exp if_exp, Tr_exp then_exp, Tr_exp else_exp);
Tr_exp Tr_seqExp(Tr_expList expList);
F_fragList Tr_getResult(void);

//static T_stm F_procEntryExit1(F_frame frame, T_stm stm);
void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals);
void Tr_init();
F_fragList Tr_getResult(void);

#endif
