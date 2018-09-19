#include <assert.h>
#include <stdio.h>

#include "util.h"
#include "error.h"
#include "instr.h"
#include "op.h"
#include "sym.h"
#include "stmt.h"
#include "globals.h"

char* stmt_string[NSTMT];

void init_stmt(void)
{
	int	i;

	for (i = 0; i < NSTMT; i += 1)
		stmt_string[i] = "???";

	stmt_string[NOP]	= "nop";
	stmt_string[ADD]	= "add";
	stmt_string[BT] 	= "bt";
	stmt_string[BF] 	= "bf";
	stmt_string[BA] 	= "ba";
	stmt_string[DIV]	= "div";
	stmt_string[LABEL]	= "label";
	stmt_string[LD] 	= "ld";
	stmt_string[MOV]	= "mov";
	stmt_string[MUL]	= "mul";
	stmt_string[NEG]	= "neg";
	stmt_string[PHI]	= "phi";
	stmt_string[PUT]	= "put";
	stmt_string[GET]	= "get";
	stmt_string[RET]	= "ret";
	stmt_string[SEQ]	= "seq";
	stmt_string[SGT]	= "sgt";
	stmt_string[SGE]	= "sge";
	stmt_string[SLE]	= "sle";
	stmt_string[SLL]	= "sll";
	stmt_string[SLT]	= "slt";
	stmt_string[SRA]	= "sra";
	stmt_string[SRL]	= "srl";
	stmt_string[SNE]	= "sne";
	stmt_string[ST] 	= "st";
	stmt_string[SUB]	= "sub";
} 

void emit(stmt_type_t type, op_t a, op_t b, op_t dest, unsigned line)
{
	static stmt_t*	last;
	stmt_t*		stmt;
	op_t		c;

	if (type == LABEL && last != NULL && last->type != BA) {
		stmt = new_stmt(BA, no_op, no_op, a, line);
		add_stmt(stmt);
	} else if (type == BA && last != NULL && last->type == BA)
		return;

	if (a.type != NO_OP && is_num(a)) {

		/* We cannot have code such as:
		 *     dest = 12+b;
		 * because the first operand may not be a number
		 * (as in most real computers as well), so we change 
		 * it to:
		 *     c = 12;
		 *     dest = c+12;
		 *
		 * We could have changed it to 
		 *     dest = b+12;
		 *
		 * but then we would have to be careful about
		 * non-commutative operations such as minus.
		 *
		 */
	
		c = temp();
		stmt = new_stmt(MOV, a, (op_t){.type = NO_OP }, c, line);
		add_stmt(stmt);

		stmt = new_stmt(type, c, b, dest, line);
	} else
		stmt = new_stmt(type, a, b, dest, line);

	add_stmt(stmt);	

	last = stmt;
}

stmt_t* new_stmt(stmt_type_t type, op_t a, op_t b, op_t dest, unsigned line)
{
	stmt_t*		stmt;
	static unsigned	index;

	stmt = calloc(1, sizeof(stmt_t));
	stmt->index	= index++;
	stmt->type	= type;
	stmt->line	= line;
	stmt->op[0]	= a;
	stmt->op[1]	= b;
	stmt->op[2]	= dest;

	if (!is_branch(stmt) && dest.type != NO_OP)
		set_op_def(stmt->op[2], stmt);
	else if (stmt->type == LABEL)	
		set_op_def(stmt->op[0], stmt);
	
	return stmt;
}

void free_stmt(stmt_t* stmt)
{
	if (stmt->phi != NULL)
		free_phi(stmt->phi);
	free(stmt);
}

bool is_real(stmt_t* stmt)
{
	if (stmt->type == LABEL || stmt->type == NOP || stmt->type == PHI)
		return false;
	else
		return true;
}

bool is_branch(stmt_t* stmt)
{
	switch (stmt->type) {
	case BT:
	case BF:
	case BA:
		return true;
	default:
		return false;
	}
}

void set_stmt_addr(stmt_t* stmt, int addr)
{
	stmt->addr = addr;
}

void relocate(stmt_t* stmt)
{
	stmt_t*		target;

	/* Only one relocation type: for PC-relative branches. */
	
	
	switch (stmt->type) {
	case BA:
	case BT:	
	case BF:
		target = op_def(stmt->op[2]);
		stmt->op[2] = new_num_op(target->addr - stmt->addr);
		break;

	default:
		fatal(stmt->type);
	}
}

op_t branch_dest(stmt_t* stmt)
{
	/* The target label of a branch stmt is always as op[2]. */

	return stmt->op[2];
}

void print_phi(stmt_t* stmt, FILE* fp)
{ 
	int		k;

	print_op(stmt->op[2], fp, 1);
	fprintf(fp, " := (");

	for (k = 0; k < stmt->phi->n; k += 1) {
		print_op(stmt->phi->rhs[k], fp, 1);	

		if (k < stmt->phi->n-1)
			fprintf(fp, ", ");
		
	} 
	fprintf(fp, ")");
}

void print_stmt(stmt_t* stmt, FILE* fp)
{
	int	k;

	if (stmt->type != LABEL)
		fputc('\t', fp);

	fprintf(fp, "%4u %5u    ", stmt->line, stmt->index);
	fprintf(fp, "%-8s", stmt_string[stmt->type]);

	if (stmt->phi != NULL)
		print_phi(stmt, fp);
	else 
		for (k = 0; k < 3; k += 1)
			print_op(stmt->op[k], fp, OP_WIDTH);

	fputc('\n', fp);
}

instr_t make_instr(stmt_t* stmt)
{
	instr_t	instr = { 0 };

	instr.type = stmt->type;

	switch (stmt->type) {
	case PHI:
		error(FATAL, "remaining phi function");

	case ADD: 
	case SUB:
	case MUL:
	case DIV:	
	case SEQ:
	case SGE:
	case SGT:
	case SLE:
	case SLT:
	case SNE:
	case SRA:
	case SRL:
	case SLL:
		if (is_num(stmt->op[0]) && is_num(stmt->op[1])) {
			int	a = op_repr(stmt->op[0]);
			int	b = op_repr(stmt->op[1]);
			int	c;

			switch (stmt->type) {
			case ADD: c = a + b; break;
			case SUB: c = a - b; break;
			case MUL: c = a * b; break;
			case DIV: c = a / b; break;
			case SEQ: c = a == b; break;
			case SGE: c = a >= b; break;
			case SGT: c = a > b; break;
			case SLE: c = a <= b; break;
			case SLT: c = a < b; break;
			case SNE: c = a != b; break;
			case SRA: c = a >> b; break; /* Not portable, though. */
			case SRL: c = (unsigned)a >> (unsigned)b; break;
			case SLL: c = a << b; break;
			default:
				fatal(stmt->type);
			}

			instr.type = MOV;
			instr.op[0] = c;
			instr.imm = true;
			instr.op[2] = op_repr(stmt->op[2]);
		} else { 
			instr.op[0] = op_repr(stmt->op[0]);
			instr.op[1] = op_repr(stmt->op[1]);
			instr.op[2] = op_repr(stmt->op[2]);
			instr.imm = is_num(stmt->op[1]);
		}
		break;

	case ST:
	case LD:
		instr.op[0] = op_repr(stmt->op[0]);
		instr.op[1] = op_repr(stmt->op[1]);
		instr.op[2] = op_repr(stmt->op[2]);
		instr.imm = is_num(stmt->op[1]);
		break;

	case BT:
	case BF:
	case MOV:
	case NEG:
		instr.op[0] = op_repr(stmt->op[0]);
		instr.op[2] = op_repr(stmt->op[2]);
		instr.imm = is_num(stmt->op[0]);
		break;

	case BA:
		instr.op[2] = op_repr(stmt->op[2]);
		break;

	case PUT:
	case RET:
		instr.op[0] = op_repr(stmt->op[0]);
		instr.imm = is_num(stmt->op[0]);
		break;

	case GET:
		instr.op[2] = op_repr(stmt->op[2]);
		break;

	case NOP:
	case LABEL:
	default:
		fatal(stmt->type);
	}

	return instr;
}

sym_t* defined_sym(stmt_t* stmt)
{
	if (stmt->type == ST
		|| !is_sym(stmt->op[2])
		|| is_label(stmt->op[2]))
		return NULL;

	return stmt->op[2].u.sym;
}
