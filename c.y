%{

#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include "error.h"
#include "op.h"
#include "stmt.h"
#include "sym.h"
#include "node.h"
#include "globals.h"
#include "typedefs.h"

extern void yyerror(char* s);
extern int yylex();

%}

%union {
	node_t*		node;
	int		num;
	char*		string;
	list_t*		node_list;
};

%token			INVALID
%token			ELSE
%token			IF
%token			INT
%token			RETURN
%token			WHILE
%token			EQ
%token			NE
%token			LE
%token			GE
%token			PUT_TOKEN
%token			GET_TOKEN
%token			GOTO

%token	<string>	ID
%token	<num>		NUM

%type	<string>	int_id
%type	<num>		opt_array
%type	<node>		opt_ref
%type	<node>		sym
%type	<node>		expr
%type	<node>		add_expr
%type	<node>		mul_expr
%type	<node>		unary_expr
%type	<node>		primary_expr
%type	<node>		literal
%type	<node>		integer_literal
%type	<node>		stmt
%type	<node>		asgn_stmt
%type	<node>		comp_stmt
%type	<node>		cond_stmt
%type	<node>		jump_stmt
%type	<node>		label_stmt
%type	<node>		loop_stmt
%type	<node>		put_stmt
%type	<node_list>	stmt_list

%%

translation_unit:
	INT ID '(' ')' '{' declaration_list comp_stmt '}'
	{
		if (strcmp($2, "main") != 0)
			yyerror("we can only compile a function called \"main\"");

		emit(LABEL, new_label(), no_op, no_op, 1);
		gencode($7);
		free_node($7);
		free($2); // we don't need the "main" string...
	}
	;

expr:
	add_expr

	| expr EQ add_expr
	{
		$$ = new_node(EQ_NODE, $1, $3);
	}

	| expr NE add_expr
	{
		$$ = new_node(NE_NODE, $1, $3);
	}

	| expr '<' add_expr
	{
		$$ = new_node(LT_NODE, $1, $3);
	}

	| expr '>' add_expr
	{
		$$ = new_node(GT_NODE, $1, $3);
	}

	| expr LE add_expr
	{
		$$ = new_node(LE_NODE, $1, $3);
	}

	| expr GE add_expr
	{
		$$ = new_node(GE_NODE, $1, $3);
	}
	;

add_expr:
	mul_expr

	| add_expr '+' mul_expr
	{
		$$ = new_node(ADD_NODE, $1, $3);
	}

	| add_expr '-' mul_expr
	{
		$$ = new_node(SUB_NODE, $1, $3);
	}
	;

mul_expr:
	unary_expr

	| mul_expr '*' unary_expr
	{
		$$ = new_node(MUL_NODE, $1, $3);
	}

	| mul_expr '/' unary_expr
	{
		$$ = new_node(DIV_NODE, $1, $3);
	}
	;

unary_expr:
	primary_expr

	| '+' unary_expr
	{
		$$ = $2;
	}

	| '-' unary_expr
	{
		$$ = new_node(NEG_NODE, $2);
	}
	;

opt_ref:
	{
		$$ = NULL;
	}

	| '[' expr ']'
	{
		$$ = $2;
	}
	;

primary_expr:
	literal

	| '(' expr ')'
	{
		$$ = $2;
	}

	| sym opt_ref
	{
		if ($2 == NULL)
			$$ = $1;
		else
			$$ = new_node(REF_NODE, $1, $2);
	}

	| GET_TOKEN '(' ')'
	{
		$$ = new_node(GET_NODE);
	}
	;

literal:
	integer_literal
	;

integer_literal:
	NUM
	{
		$$ = new_node(NUM_NODE, $1);
	}
	;

int_id:
	INT ID
	{
		$$ = $2;
	}
	;

opt_array:
	{ 
		$$ = 0;
	}

	| '[' NUM ']'
	{
		$$ = $2;
	}
	;

declaration:
	int_id opt_array
	{
		install($1, $2);
	}
	;

declaration_list:
	| declaration_list declaration ';'
	;

stmt:
	asgn_stmt

	| '{' comp_stmt '}'
	{
		$$ = $2;
	}

	| label_stmt

	| cond_stmt

	| loop_stmt

	| jump_stmt

	| put_stmt

	;

put_stmt:
	PUT_TOKEN '(' expr ')' ';'
	{
		$$ = new_node(PUT_NODE, $3);
	}
	;

comp_stmt:
	stmt_list 
	{
		$$ = new_node(STMT_LIST_NODE, $1);
	}
	;

stmt_list:
	{
		$$ = NULL;
	}

	| stmt_list stmt
	{
		insert_last(&$1, $2);
		$$ = $1;
	}
	;

asgn_stmt:
	sym opt_ref '=' expr ';'
	{
		$$ = new_node(ASSIGN_NODE, $1, $2, $4);
	}
	;

sym: ID
	{
		$$ = new_node(ID_NODE, $1);
	}
	;

cond_stmt:
	IF '(' expr ')' stmt
	{
		$$ = new_node(IF_NODE, $3, $5);
	}

	| IF '(' expr ')' stmt ELSE stmt
	{
		$$ = new_node(IF_ELSE_NODE, $3, $5, $7);
	}
	;

loop_stmt:
	WHILE '(' expr ')' stmt
	{
		$$ = new_node(WHILE_NODE, $3, $5);
	}
	;

label_stmt:
	ID ':' stmt
	{
		install($1, -1);

		$$ = new_node(LABEL_NODE, $1, $3);
	}
	;

jump_stmt:
	GOTO ID ';'
	{
		$$ = new_node(GOTO_NODE, $2);
	}

	| RETURN expr ';'
	{
		$$ = new_node(RETURN_NODE, $2);
	}
	;
%%

void yyerror(char* s)
{
	error(SYNTAX, "");
	exit(1);
}
