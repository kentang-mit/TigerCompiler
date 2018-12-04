%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "ctype.h"
#include "stdbool.h"
#include "symbol.h"
#include "absyn.h"
#include "y.tab.h"

int charPos=1;
int comments = 0;
int yyless_param = 0;
int error_type = 0;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences 
 * translated into their meaning.
 */
bool iswhitespace(char s){
	return s==' '||s=='\t'||s=='\n'||s=='\v'||s=='\f'||s=='\r';
}


char *getstr(const char *str)
{
	//optional: implement this function if you need it
	//printf("The string: %s", str);
	char *out = (char*)malloc(yyleng+1);
	char ch;
	int curlen = 0;
	for(int i = 1; i < yyleng; i++){
		ch = str[i];
		if(ch=='\\'){
			char ch_ = str[++i];
			if(ch_ == 'n'){
				out[curlen++] = '\n';
				continue;
			}
			else if(ch_ == 't'){
				out[curlen++] = '\t';
				continue;
			}
			else if(ch_ == '\\'){
				out[curlen++] = '\\';
				continue;
			}
			else if(ch_ == '\"'){
				out[curlen++] = '\"';
				continue;
			}
			else if(ch_ == '\''){
				out[curlen++] = '\'';
				continue;
			}
			//control sequence
			else if(ch_ == '^'){
				ch_ = str[++i];
				if(ch_>='A'&&ch_<='Z'){
					out[curlen++] = ch_-'A'+1;
				}
				else{
					error_type = 2;
					break;
				}
			}
			else if(ch_ == '?'){
				out[curlen++] = '\?';
				continue;
			}
			//three digit ascii code
			else if(isdigit(ch_)){

				char ch1 = str[++i];
				char ch2 = str[++i];
				if(isdigit(ch1) && isdigit(ch2)){
					int ascii = (ch_-'0')*100+(ch1-'0')*10+(ch2-'0');
					out[curlen++] = ascii;
					continue;
				}
				else if(ch_ == '0') break;
				else {
					//error
					EM_tokPos = charPos + i;
					error_type = 1;
					break;
				}
			}
			//follow by whitespace(' ', \t, \n, \v, \f, \r), read until we get another '\'
			else if(iswhitespace(ch_)){
				while(ch_ != '\n' && iswhitespace(ch_)){
					ch_ = str[++i];
				}
				if(!iswhitespace(ch_)){
					//error
					EM_tokPos = charPos + i;
					error_type = 2;
					break;
				}
				else{
					while(iswhitespace(ch_)){
						ch_ = str[++i];
					}
					//next line case
					if(ch_ != '\\'){
						EM_tokPos = charPos + i;
						error_type = 2;
						break;
					}
					else continue;
				}
			}
			else{
				//error
				EM_tokPos = charPos + i;
				error_type = 2;
				break;
			}
		}
		else if(ch=='\"') {
			yyless_param = i+1;
			yyleng = i+1;
			//printf("yyless_param: %d\n", yyless_param);
			break;
		}
		else out[curlen++] = ch;
	}
	//modified for lab3
	if(curlen == 0){
		out = "\0";
	}
	else out[curlen] = '\0';
	return out;
}

%}
  /* You can add lex definitions here. */
digits	[0-9]+
whitespace [ \t]+
%Start COMMENT
%%
  /* 
  * Below is an example, which you can wipe out
  * and write reguler expressions and actions of your own.
  */
<INITIAL>"\n" {adjust(); EM_newline(); continue;}
<INITIAL>{whitespace} {adjust();}
<INITIAL>"," {adjust(); return COMMA;}
<INITIAL>":" {adjust(); return COLON;}
<INITIAL>";" {adjust(); return SEMICOLON;}
<INITIAL>"(" {adjust(); return LPAREN;}
<INITIAL>")" {adjust(); return RPAREN;}
<INITIAL>"[" {adjust(); return LBRACK;}
<INITIAL>"]" {adjust(); return RBRACK;}
<INITIAL>"{" {adjust(); return LBRACE;}
<INITIAL>"}" {adjust(); return RBRACE;}
<INITIAL>"." {adjust(); return DOT;}
<INITIAL>"+" {adjust(); return PLUS;}
<INITIAL>"-" {adjust(); return MINUS;}
<INITIAL>"*" {adjust(); return TIMES;}
<INITIAL>"/" {adjust(); return DIVIDE;}
<INITIAL>"=" {adjust(); return EQ;}
<INITIAL>"<>" {adjust(); return NEQ;}
<INITIAL>"<" {adjust(); return LT;}
<INITIAL>"<=" {adjust(); return LE;}
<INITIAL>">" {adjust(); return GT;}
<INITIAL>">=" {adjust(); return GE;}
<INITIAL>"&" {adjust(); return AND;}
<INITIAL>"|" {adjust(); return OR;}
<INITIAL>":=" {adjust(); return ASSIGN;}
<INITIAL>"array" {adjust(); return ARRAY;}
<INITIAL>"if" {adjust(); return IF;}
<INITIAL>"then" {adjust(); return THEN;}
<INITIAL>"else" {adjust(); return ELSE;}
<INITIAL>"while" {adjust(); return WHILE;}
<INITIAL>"for" {adjust(); return FOR;}
<INITIAL>"to" {adjust(); return TO;}
<INITIAL>"do" {adjust(); return DO;}
<INITIAL>"let" {adjust(); return LET;}
<INITIAL>"in" {adjust(); return IN;}
<INITIAL>"end" {adjust(); return END;}
<INITIAL>"of" {adjust(); return OF;}
<INITIAL>"break" {adjust(); return BREAK;}
<INITIAL>"nil" {adjust(); return NIL;}
<INITIAL>"function" {adjust(); return FUNCTION;}
<INITIAL>"var" {adjust(); return VAR;}
<INITIAL>"type" {adjust(); return TYPE;}
<INITIAL>[a-zA-Z][a-zA-Z0-9_]* {adjust(); yylval.sval=String(yytext); return ID;}
<INITIAL>{digits} {adjust(); yylval.ival=atoi(yytext); return INT;}
<INITIAL>\".*(\n)?.*\" {
	yylval.sval = getstr(yytext); 
	if(yyless_param!=0){
		yyless(yyless_param); 
		yyless_param=0;
	} 
	if(error_type ==0 ) adjust();
	else{
		if(error_type==1){
			EM_error(EM_tokPos, "Invalid ASCII!");
		}
		else if(error_type==2){
			EM_error(EM_tokPos, "Invalid escape sequence!");
		}
		error_type = 0;
	}
	return STRING;
}
<INITIAL>\" {adjust(); EM_error(EM_tokPos, "Unclosed string!");}
<INITIAL>"\/\*" {adjust(); ++comments; BEGIN COMMENT;} 
<COMMENT>"\/\*" {adjust(); ++comments;} 
<COMMENT>"\*\/" {adjust(); --comments; if(comments>0){continue;} else{BEGIN INITIAL;}}
<COMMENT>"\n"|{whitespace} {adjust();}
<COMMENT>. {adjust();}
<INITIAL>. {adjust(); EM_error(EM_tokPos,"Illegal character!");}
<<EOF>> {
	if(comments>0){
		EM_error(EM_tokPos, "Unclosed comment!");
	}
	yyterminate();
}

