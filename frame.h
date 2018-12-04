
/*Lab5: This header file is not complete. Please finish it with more definition.*/

#ifndef FRAME_H
#define FRAME_H

#include "tree.h"
#include "util.h"
#include "assem.h"
//#include "temp.h"
static const int F_wordSize = 8;
static Temp_temp FP = NULL, RV = NULL, RDX = NULL, RDI = NULL, RSI = NULL, RCX = NULL, R8 = NULL,
	R9 = NULL, R10 = NULL, R11 = NULL, R12 = NULL, R13 = NULL, R14 = NULL, R15 = NULL, SP = NULL,
	RBX = NULL;
Temp_temp F_FP(void);
Temp_temp F_RV(void);
Temp_temp F_RDX(void);
Temp_temp F_RDI(void);
Temp_temp F_RSI(void);
Temp_temp F_RCX(void);
Temp_temp F_R8(void);
Temp_temp F_R9(void);
Temp_temp F_R10(void);
Temp_temp F_R11(void);
Temp_temp F_R12(void);
Temp_temp F_R13(void);
Temp_temp F_R14(void);
Temp_temp F_R15(void);
Temp_temp F_SP(void);
Temp_temp F_RBX(void);

Temp_map F_tempMap;
void F_initMap();

struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

typedef struct F_access_ *F_access;
typedef struct F_accessList_ *F_accessList;

struct F_frame_{
	Temp_label label;
	U_boolList escapes;
	int size;
	//how to access all params.
	F_accessList accessList;
};


typedef struct F_frame_ *F_frame;


F_frame F_newFrame(Temp_label label, U_boolList escapes);
string F_name(F_frame f);

struct F_accessList_ {F_access head; F_accessList tail;};

F_accessList F_AccessList(F_access head, F_accessList tail);

/* declaration for fragments */
typedef struct F_frag_ *F_frag;
struct F_frag_ {enum {F_stringFrag, F_procFrag} kind;
			union {
				struct {Temp_label label; string str;} stringg;
				struct {T_stm body; F_frame frame;} proc;
			} u;
};

F_frag F_StringFrag(Temp_label label, string str);
F_frag F_ProcFrag(T_stm body, F_frame frame);

typedef struct F_fragList_ *F_fragList;
struct F_fragList_ 
{
	F_frag head; 
	F_fragList tail;
};

F_fragList F_FragList(F_frag head, F_fragList tail);
F_access F_allocLocal(F_frame f, bool escape);
T_exp F_externalCall(string s, T_expList args);

F_access InFrame(int offset);
F_access InReg(Temp_temp reg);
T_exp F_exp(F_access acc, T_exp fp);

T_stm F_procEntryExit1(F_frame frame, T_stm stm);
//produce the live variables after procedure
AS_instrList F_procEntryExit2(AS_instrList body);
//prologue and epilogue
AS_instrList F_procEntryExit3(F_frame frame, AS_instrList body);
#endif
