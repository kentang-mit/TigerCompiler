#ifndef PRINT_TREE_H
#define PRINT_TREE_H

/* function prototype from printtree.c */
void printStmList (FILE *out, T_stmList stmList) ;
void pr_stm(FILE *out, T_stm stm, int d);
void pr_tree_exp(FILE *out, T_exp exp, int d);
#endif

