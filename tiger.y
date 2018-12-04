//WARNING: DELETE orOp, andOp before submission!!!
%{
#include <stdio.h>
#include "stdlib.h"
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#define YYERROR_VERBOSE 1
int yylex(void); /* function prototype */

A_exp absyn_root;

void yyerror(char *s)
{
 EM_error(EM_tokPos, "%s", s);
 exit(1);
}
%}


%union {
	int pos;
	int ival;
	string sval;
	A_exp exp;
	A_expList explist;
	A_var var;
	A_decList declist;
	A_dec  dec;
	A_efieldList efieldlist;
	A_efield  efield;
	A_namety namety;
	A_nametyList nametylist;
	A_fieldList fieldlist;
	A_field field;
	A_fundecList fundeclist;
	A_fundec fundec;
	A_ty ty;
	}

%token <sval> ID STRING
%token <ival> INT

%token 
  COMMA COLON SEMICOLON LPAREN RPAREN LBRACK RBRACK 
  LBRACE RBRACE DOT 
  PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE
  AND OR ASSIGN
  ARRAY IF THEN ELSE WHILE FOR TO DO LET IN END OF 
  BREAK NIL
  FUNCTION VAR TYPE 

%type <exp> exp expseq ifexp whileexp forexp opexp
%type <explist> actuals  nonemptyactuals sequencing  sequencing_exps
%type <var>  lvalue
%type <declist> decs decs_nonempty
%type <dec>  decs_nonempty_s vardec
%type <efieldlist> rec rec_nonempty 
%type <efield> rec_one
%type <nametylist> tydec
%type <namety>  tydec_one
%type <fieldlist> tyfields tyfields_nonempty
%type <ty> ty
%type <fundeclist> fundec
%type <fundec> fundec_one

%start program

//to fix the tydec, fundec problem. Input terminal is TYPE, FUNCTION. prec of rule is LOW.
%nonassoc LOW
%nonassoc TYPE FUNCTION

//to fix 3 shift/reduce conflicts LBRACK has higher priority
%nonassoc ID
%nonassoc LBRACK
//the following are for the dangling else
%nonassoc THEN
%nonassoc ELSE

%nonassoc ASSIGN
%left AND OR
%nonassoc EQ NEQ LT LE GT GE//higher precendence than AND/OR
%left PLUS MINUS
%left TIMES DIVIDE
%left UMINUS

%%

program: exp {absyn_root = $1;};//Program is an expression.
//paranthesis grouping, record creation, no value, let nil exp, sequencing
		

exp: opexp {$$ = $1;} 
	| ifexp {$$ = $1;};
	| whileexp {$$ = $1;};
	| forexp {$$ = $1;};
	| lvalue ASSIGN exp {$$=A_AssignExp(EM_tokPos, $1, $3);}//assign lvalue := exp
	| BREAK {$$ = A_BreakExp(EM_tokPos);}
	| LET decs IN expseq END {$$ = A_LetExp(EM_tokPos,$2,$4);}
	//solving 12 shift/reduce conflicts
	| ID LBRACK exp RBRACK OF exp {$$ = A_ArrayExp(EM_tokPos,S_Symbol($1),$3,$6);};//array creation.$3:size $5:value
	| ID ASSIGN exp {$$=A_AssignExp(EM_tokPos, A_SimpleVar(EM_tokPos,S_Symbol($1)), $3);}//assign lvalue := exp

opexp: NIL {$$ = A_NilExp(EM_tokPos);}
	| 	LPAREN expseq RPAREN {$$ = $2;}
	//queens line 21 through 31
	//|	LPAREN exp RPAREN {$$ = $2;}
	| ID LPAREN RPAREN {$$ = A_CallExp(EM_tokPos, S_Symbol($1), NULL);} //func call
	| ID LPAREN actuals RPAREN {$$ = A_CallExp(EM_tokPos, S_Symbol($1), $3);} //func call
	| ID LBRACE rec RBRACE {$$ = A_RecordExp(EM_tokPos, S_Symbol($1), $3);}//Problematic, record creation
	|	lvalue {$$ = A_VarExp(EM_tokPos,$1);}//var exp
	|	INT	{$$ = A_IntExp(EM_tokPos, $1);}//int exp
	|	STRING {$$ = A_StringExp(EM_tokPos, $1);}//string exp
	|	MINUS opexp %prec UMINUS{$$ = A_OpExp(EM_tokPos, A_minusOp, A_IntExp(EM_tokPos,0), $2);}//negation
	|	opexp PLUS opexp {$$ = A_OpExp(EM_tokPos, A_plusOp, $1, $3);}
	|	opexp MINUS opexp {$$ = A_OpExp(EM_tokPos, A_minusOp, $1, $3);}
	|	opexp TIMES opexp {$$ = A_OpExp(EM_tokPos, A_timesOp, $1, $3);}
	|	opexp DIVIDE opexp {$$ = A_OpExp(EM_tokPos, A_divideOp, $1, $3);}
	|	opexp EQ opexp {$$ = A_OpExp(EM_tokPos, A_eqOp, $1, $3);}
	| 	opexp NEQ opexp {$$ = A_OpExp(EM_tokPos, A_neqOp, $1, $3);}
	|	opexp LT opexp {$$ = A_OpExp(EM_tokPos, A_ltOp, $1, $3);}
	|	opexp LE opexp {$$ = A_OpExp(EM_tokPos, A_leOp, $1, $3);}
	|	opexp GT opexp {$$ = A_OpExp(EM_tokPos, A_gtOp, $1, $3);}
	|	opexp GE opexp {$$ = A_OpExp(EM_tokPos, A_geOp, $1, $3);}
	|	opexp AND opexp {$$ = A_IfExp(EM_tokPos, $1, $3, A_IntExp(EM_tokPos, 0));}//change to cond. jump
	|	opexp OR opexp {$$ = A_IfExp(EM_tokPos, $1, A_IntExp(EM_tokPos,1), $3);}//change to cond. jump	;
	

ifexp: 	IF exp THEN exp {$$=A_IfExp(EM_tokPos, $2, $4, A_NilExp(EM_tokPos));}//if exp then exp
		|IF exp THEN exp ELSE exp {$$ = A_IfExp(EM_tokPos, $2, $4, $6);}
		;//if exp then exp else exp

whileexp: WHILE exp DO exp {$$ = A_WhileExp(EM_tokPos, $2, $4);}//while exp do exp
		;

forexp: FOR ID ASSIGN exp TO exp DO exp {$$ = A_ForExp(EM_tokPos, S_Symbol($2), $4,$6,$8);};//for id:=exp to exp do exp


expseq	:  sequencing {$$ = A_SeqExp(EM_tokPos,$1);}
		;

actuals	:  nonemptyactuals {$$ = $1;} //non empty, return explis
		;

nonemptyactuals: exp {$$ = A_ExpList($1, NULL);}
			|	exp COMMA nonemptyactuals {$$ = A_ExpList($1, $3);}
		;
sequencing 	:	exp {$$ = A_ExpList($1, NULL);}
			|	sequencing_exps {$$ = $1;}
		;
sequencing_exps: 	exp SEMICOLON exp {$$ = A_ExpList($1,A_ExpList($3,NULL));}
				|	exp SEMICOLON sequencing_exps {$$ = A_ExpList($1,$3);}
				|	exp SEMICOLON LPAREN RPAREN {$$ = A_ExpList($1, A_ExpList(A_SeqExp(EM_tokPos, NULL), NULL));}
				;
lvalue     :   ID  {$$ = A_SimpleVar(EM_tokPos, S_Symbol($1));}
              |lvalue DOT ID  {$$ = A_FieldVar(EM_tokPos, $1, S_Symbol($3));}
              |lvalue LBRACK exp RBRACK  {$$ = A_SubscriptVar(EM_tokPos, $1, $3);}
              //fix queens bug
              |ID LBRACK exp RBRACK  {$$ = A_SubscriptVar(EM_tokPos, A_SimpleVar(EM_tokPos, S_Symbol($1)), $3);}
              ;
decs:	{$$=NULL;}//empty definition
		|	decs_nonempty {$$=$1;}//non empty definition(sequence)
decs_nonempty: 		decs_nonempty_s {$$ = A_DecList($1,NULL);}//a single definition
				|	decs_nonempty_s decs_nonempty {$$ = A_DecList($1,$2);}//a list of definitions
decs_nonempty_s: vardec {$$=$1;}//variable declaration
				|tydec {$$=A_TypeDec(EM_tokPos,$1);}//type declaration
				|fundec {$$=A_FunctionDec(EM_tokPos,$1);}//function declaration

vardec     :   VAR ID ASSIGN exp  {$$ = A_VarDec(EM_tokPos,S_Symbol($2),NULL,$4);}//var id:=exp
              |VAR ID COLON ID ASSIGN exp  {$$ = A_VarDec(EM_tokPos,S_Symbol($2),S_Symbol($4),$6);}//var id:type-id:=exp
              |VAR ID ASSIGN LPAREN RPAREN {$$ = A_VarDec(EM_tokPos,S_Symbol($2),NULL,A_SeqExp(EM_tokPos, NULL));}
              ;
rec 		: 	{$$=NULL;}
			|	rec_nonempty {$$=$1;} //A record creation: list{first=i,rest=readlist()}
			;
rec_nonempty: 	rec_one {$$=A_EfieldList($1,NULL);}
			|	rec_one COMMA rec_nonempty {$$=A_EfieldList($1,$3);}//e.g. first=i,rest=readlist()
			;
rec_one:	ID EQ exp{$$=A_Efield(S_Symbol($1),$3);}//e.g. first=i

tydec		:	tydec_one tydec {$$=A_NametyList($1,$2);}
			|	tydec_one %prec LOW {$$=A_NametyList($1,NULL);}
			;
tydec_one	:	TYPE ID EQ ty {$$ = A_Namety(S_Symbol($2),$4);};//type type-id = ty
tyfields 	:	{$$=NULL;}
			|	tyfields_nonempty {$$=$1;}
			; 	
tyfields_nonempty: ID COLON ID
					{$$ = A_FieldList(A_Field(EM_tokPos,S_Symbol($1),S_Symbol($3)), NULL);}//id: typeid
				|	ID COLON ID COMMA tyfields_nonempty
					{$$ = A_FieldList(A_Field(EM_tokPos,S_Symbol($1),S_Symbol($3)), $5);}//id:typeid{,id:typeid}
				;
ty 		:	ID {$$=A_NameTy(EM_tokPos,S_Symbol($1));}//type-id
		|	LBRACE tyfields RBRACE {$$=A_RecordTy(EM_tokPos,$2);}//{tyfields}
		|	ARRAY OF ID {$$=A_ArrayTy(EM_tokPos,S_Symbol($3));}//array of type-id
		;
fundec: 	fundec_one fundec{$$=A_FundecList($1,$2);}//a list of functions
		|	fundec_one %prec LOW {$$=A_FundecList($1,NULL);}//a single function
		;
fundec_one: FUNCTION ID LPAREN tyfields RPAREN EQ exp
			{$$ = A_Fundec(EM_tokPos, S_Symbol($2), $4, NULL, $7);}//Don't know return type
		|	FUNCTION ID LPAREN tyfields RPAREN COLON ID EQ exp
			{$$ = A_Fundec(EM_tokPos, S_Symbol($2), $4, S_Symbol($7), $9);}//know return type
		;