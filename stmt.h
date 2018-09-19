#ifndef stmt_h
#define stmt_h

#include "list.h"
#include "op.h"

typedef enum {	
	NOP,		/* No operation. */
	ADD,		/* Add. */
	BT,		/* Branch to op[2] if op[0] is true. */
	BF,		/* Branch to op[2] if op[0] is false. */
	BA,		/* Branch always. */
	DIV,		/* Divide. */
	GET,		/* Get integer from stdin. */
	LABEL,		/* A label. */
	LD,		/* Load from memory. */
	MOV,		/* Copy. */
	MUL,		/* Multiply. */
	NEG,		/* Negate. */
	PHI,		/* Phi-function. */
	PUT,		/* Print integer to stdout. */
	RET,		/* Return. */
	SEQ,		/* Set to true if ==. */
	SGE,		/* Set to true if >=. */
	SGT,		/* Set to true if >. */
	SLE,		/* Set to true if <=. */
	SLL,		/* Shift left logical. */
	SLT,		/* Set to true if <. */
	SRA,		/* Shift right arithmetic. */
	SRL,		/* Shift right logical. */
	SNE,		/* Set to true if !=. */
	ST,		/* Store to memory. */
	SUB,		/* Subtract. */
	NSTMT
} stmt_type_t;

typedef struct {
	int		n;	/* Number of operands, ie size of rhs array. */
	op_t*		rhs;	/* Right-hand side, i.e. operands. */
	stmt_t*		stmt;	/* The statement which owns this phi func. */
} phi_t;

struct stmt_t {
	unsigned	index;	/* Serial number for debugging. */
	stmt_type_t	type;	/* What the statement does (ADD, SUB, etc). */
	op_t		op[3];	/* Three operands. */
	int		addr;	/* The instruction address of this statement. */
	unsigned	line;	/* Source code line number. */
	phi_t*		phi;	/* Used only by phi-functions. */
};

stmt_t* new_stmt(stmt_type_t type, op_t a, op_t b, op_t dest, unsigned line);
void free_stmt(stmt_t* stmt);
void emit(stmt_type_t type, op_t a, op_t b, op_t dest, unsigned line);
bool is_branch(stmt_t* stmt);
bool is_real(stmt_t* stmt);
instr_t make_instr(stmt_t*);
sym_t* defined_sym(stmt_t*);
void init_stmt(void);
void print_stmt(stmt_t* stmt, FILE* fp);
void set_stmt_addr(stmt_t* stmt, int addr);
void relocate(stmt_t* stmt);
op_t branch_dest(stmt_t* stmt);

#endif
