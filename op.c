#include <assert.h>
#include <stdarg.h>

#include "util.h"
#include "error.h"
#include "sym.h"
#include "op.h"
#include "stmt.h"
#include "globals.h"

op_t	zero	= { .type = NUM_OP };
op_t	no_op	= { .type = NO_OP };


void print_op(op_t op, FILE* fp, int xwidth)
{
	switch (op.type) {
	case NO_OP:
		break;

	case REG_OP:
		fprintf(fp, "r%-*d", xwidth-1, op.u.reg); 
		break;

	case NUM_OP:
		fprintf(fp, "%-*d", xwidth, op.u.num);
		break;

	case SYM_OP:
		fprintf(fp, "%-*s", xwidth, op.u.sym->id);
		break;
	}
}

int op_repr(op_t op)
{
	switch (op.type) {
	case REG_OP:
		return op.u.reg;

	case NUM_OP:
		return op.u.num;

	case SYM_OP:
		return op.u.sym->index;

	default:
		fatal(op.type);
	}
}
	
void set_op_def(op_t op, stmt_t* stmt)
{
	if (op.type == SYM_OP)
		op.u.sym->def = stmt;
}

stmt_t* op_def(op_t op)
{
	assert(op.type == SYM_OP);
	return op.u.sym->def;
}
	
int op_addr(op_t op)
{
	if (op.type == SYM_OP)
		return op.u.sym->index;
	else
		fatal(op.type);
}

op_t new_op(op_type_t type, ...)
{
	op_t		op;
	va_list		ap;

	va_start(ap, type);

	op.type = type;

	switch (type) {
	case NO_OP:
		break;

	case NUM_OP:
		op.u.num = va_arg(ap, int);
		break;
		
	case REG_OP:
		op.u.reg = va_arg(ap, int);
		break;
		
	case SYM_OP:
		op.u.sym = va_arg(ap, sym_t*);
		break;
	}
		
	va_end(ap);

	return op;
}

bool is_reg(op_t op)
{
	return op.type == REG_OP;
}

bool is_num(op_t op)
{
	return op.type == NUM_OP;
}

bool is_sym(op_t op)
{
	return op.type == SYM_OP;
}

bool is_label(op_t op)
{
	return op.type == SYM_OP && op.u.sym->islabel;
}

op_t new_sym_op(sym_t* sym)
{	
	return new_op(SYM_OP, sym);
}

op_t new_num_op(int num)
{	
	return new_op(NUM_OP, num);
}

op_t new_reg_op(int reg)
{	
	return new_op(REG_OP, reg);
}

int op_index(op_t op)
{
	assert(op.type == SYM_OP);
	return op.u.sym->index;
}
