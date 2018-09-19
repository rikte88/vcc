#ifndef func_h
#define func_h

#include "typedefs.h"
#include "instr.h"
#include "stmt.h"
#include "set.h"

#define MAX_SUCC	2

struct vertex_t {
	int		index;		/* Unique number for each vertex. */
	int		work;		/* See book on SSA. */
	int		already;	/* See book on SSA. */
	op_t		label;		/* Label with symbol for the vertex. */
	int		dfnum;		/* Depth-first search number. */
	vertex_t*	idom;		/* Immediate dominator. */
	vertex_t*	sdom;		/* Semidominator. */
	vertex_t*	domchild;	/* First child in dominator tree. */
	vertex_t*	domsibling;	/* Sibling in dominator tree. */
	vertex_t*	ancestor;	/* For Lengauer-Tarjan algorithm. */
	vertex_t*	parent;		/* Parent in depth first search. */
	list_t*		phi_func_list;	/* All phi funcs in the basic block. */
	set_t*		df;		/* Dominance frontier. See SSA. */
	list_t*		bucket;		/* For Lengauer-Tarjan algorithm. */
	vertex_t*	succ[2];	/* Successors. succ[1] always for BA. */
	list_t*		pred;		/* Predecessors. */
	list_t*		stmts;		/* Statements. */
};

struct func_t {
	char*		id;		/* Name. */
	int		vcg;		/* Counter for printing graphs. */
	list_t*		stmts;		/* Statements. */
	vertex_t**	vertex;		/* Basic blocks. */
	size_t		nvertex;	/* Number of basic blocks. */
	vertex_t*	start; 		/* Start verex. */
	vertex_t*	exit; 		/* Exit verex. */
	list_t*		var;		/* Variables. */
};

void init_func(void);
void free_func(void);
void opt(void);
void to_cfg(func_t*);
void from_cfg(func_t*);
void to_ssa(func_t*);
void from_ssa(func_t*);
void dominance(func_t*);
void alloc_regs(func_t*);
instr_t* stmt2instr(int* size);
void add_stmt(stmt_t*);
void add_sym(sym_t* sym);
void print_cfg(func_t*);
void print_dt(func_t*);
void print_func(char* comment);
void fix_const_operand(func_t* func);
void clean_nop(func_t* func);
phi_t* new_phi(vertex_t*);
void free_phi(phi_t*);

#endif
