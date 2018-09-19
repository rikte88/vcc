#include "error.h"
#include "globals.h"
#include "instr.h"
#include "util.h"

int cost_vec[NSTMT];

instr_t* new_instr()
{
	instr_t*	instr;

	instr = calloc(1, sizeof(instr_t));

	instr->type	= NOP;
	instr->op[0]	= -1;
	instr->op[1]	= -1;
	instr->op[2]	= -1;
	instr->imm	= false;
	instr->count	= 0;

	return instr;
}

void init_instr(void)
{
	int	i;

	for (i = 0; i < NSTMT; i += 1)
		cost_vec[i] = 1;

	cost_vec[LD] = 2;
	cost_vec[MUL] = 4;
	cost_vec[DIV] = 20;
}

unsigned cost(stmt_type_t type)
{	
	return cost_vec[type];
}

void print_instr(instr_t* instr, FILE* fp)
{
	fprintf(fp, "%-8s", stmt_string[instr->type]);
	
	switch (instr->type) {
	case ADD:
	case DIV:
	case MUL:
	case SEQ:
	case SGE:
	case SGT:
	case SLE:
	case SLT:
	case SNE:
	case SUB:
	case LD:
	case ST:
		fprintf(fp, "r%u,", instr->op[0]);
		if (instr->imm)
			fprintf(fp, "%d,", instr->op[1]);
		else
			fprintf(fp, "r%u,", instr->op[1]);
		fprintf(fp, "r%u", instr->op[2]);
		break;

	case BT:
	case BF:
		fprintf(fp, "r%u", instr->op[0]);
		fprintf(fp, "  %d", instr->op[2]);
		break;

	case BA:
		break;

	case RET:
		if (instr->imm)
			fprintf(fp, "%d ", instr->op[0]);
		else
			fprintf(fp, "r%u", instr->op[0]);
		break;

	case MOV:
		if (instr->imm)
			fprintf(fp, "%d,", instr->op[0]);
		else
			fprintf(fp, "r%u,", instr->op[0]);
		fprintf(fp, "r%u", instr->op[2]);
		break;

	case NEG:
		fprintf(fp, "r%u", instr->op[0]);
		fprintf(fp, "r%u", instr->op[2]);
		break;

	case PUT:
		if (instr->imm)
			fprintf(fp, "%d", instr->op[0]);
		else
			fprintf(fp, "r%u", instr->op[0]);
		break;

	case GET:
		fprintf(fp, "r%u", instr->op[2]);
		break;

	default:
		fatal(instr->type);
	}
}
