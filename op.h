#ifndef ac_op_h
#define ac_op_h

#include <stdio.h>
#include "typedefs.h"

#define OP_WIDTH	(10)		/* Width when printing using printf. */

typedef enum {
	NO_OP,				/* No operand. */
	NUM_OP,				/* Number operand. */
	SYM_OP,				/* Symbol operand. */
	REG_OP				/* Register operand. */
} op_type_t;

struct op_t {
	op_type_t	type;		/* The type of op, NUM_OP, etc. */
	union {
		int	num;		/* Value if op is a NUM_OP. */
		sym_t*	sym;		/* Symbol if op is a SYM_OP. */
		int	reg;		/* Register number is op is a REG_OP. */
	}		u;
};

extern op_t  zero;
extern op_t  no_op;

op_t new_op(op_type_t type, ...);
void free_op(op_t*);
op_t temp();
op_t new_label();
op_t new_reg_op(int);
op_t new_num_op(int);
op_t new_sym_op(sym_t*);
bool is_num(op_t);
bool is_sym(op_t);
bool is_reg(op_t);
bool is_label(op_t);

stmt_t* op_def(op_t);
void set_op_def(op_t op, stmt_t* stmt);
void print_op(op_t, FILE*, int);
int op_repr(op_t);
int op_index(op_t);

#endif
