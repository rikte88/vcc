#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <limits.h>

#include "error.h"
#include "util.h"
#include "globals.h"
#include "instr.h"


static bool		trace;		/* Trace execution. */
static uint32_t		pc;		/* Program counter. */
static int		nreg;		/* Number of registers.*/
static int*		reg;		/* Register file.*/
static uint64_t*	ready_cycle;	/* When a register's data is available. */
static instr_t*		imem;		/* Instruction memory.*/
static uint32_t		imem_size;	/* Number of instructions.*/
static uint32_t*	dmem;		/* Data memory.*/
static uint32_t		dmem_size;	/* Data memory size in words.*/
static uint64_t		max_cycles;	/* Max cycles to simulate. */
static uint64_t		cycles;		/* Cycles simulated. */
static uint64_t		nexec[NSTMT];	/* #times an instr type was executed. */
static uint64_t		ncycle[NSTMT];	/* #cycles an instr type needed. */
static uint64_t		total_stalls;	/* Total pipeline stalls. */

void init_sim()
{
	max_cycles = ULLONG_MAX;
}

void set_trace(bool t)
{
	trace = t;
}

void increment_cycles(unsigned n)
{
	ncycle[imem[pc].type] += n;
	imem[pc].cycles += n;
	cycles += n;
}

void set_regs(unsigned n)
{
	nreg = n;
	reg = calloc(nreg, sizeof(int));
	ready_cycle = calloc(nreg, sizeof(uint64_t));
}

int read_mem(int addr)
{
	return dmem[addr];
}

void set_dmem_size(int n)
{
	dmem_size = n;
	dmem = calloc(dmem_size, sizeof *dmem);
	
	if (dmem == NULL)
		error(FATAL, "simulator could not malloc data memory: %d\n", n);
}

void set_imem(instr_t* v, int n)
{
	int	i;

	imem = v;
	imem_size = n;

	/* We sort the imem after execution so we want to 
	 * remember the original address of an instruction.
	 */

	for (i = 0; i < n; i += 1)
		imem[i].cycles = 0;
}

void set_max_cycles(unsigned n)
{
	max_cycles = n;
}

void print_stats()
{
	int		i;
	FILE*		fp;

	fp = fopen("stats", "w");
	assert(fp != NULL);

	fprintf(fp, "--- simulation statistics ------------------------------------------------------\n");

	fputc('\n', fp);
	fprintf(fp, "%-40s %8" PRIu64 "\n", "total number of clock cycles: ", cycles);
	fprintf(fp, "%-40s %8" PRIu64 "\n", "pipeline stalls: ", total_stalls);
	fputc('\n', fp);
	fputc('\n', fp);

	fprintf(fp, "--- execution by individual instructions ---------------------------------------\n");

	fputc('\n', fp);

	fprintf(fp, "%8s %8s %8s    %8s\n", "address", "count",
		"stalls", "instruction");

	for (i = 0; i < imem_size; i += 1) {
		fprintf(fp, "%8u ", i);
		fprintf(fp, "%8u ", imem[i].count);
		fprintf(fp, "%8u    ", imem[i].stalls);
		print_instr(&imem[i], fp);
		fputc('\n', fp);
	}

	fputc('\n', fp);
	fprintf(fp, "--------------------------------------------------------------------------------\n");

	fclose(fp);
}

void read_op(instr_t* instr, int k, int* data, bool imm, bool memaccess)
{
	int		wait_cycles;

	if (imm)
		*data = instr->op[k];

	else if (memaccess && instr->op[k] == 0)
		*data = 0;

	else {
		*data = reg[instr->op[k]];

		wait_cycles = ready_cycle[instr->op[k]] - cycles;
		if (wait_cycles > 0) {
			assert(wait_cycles < 40);
			increment_cycles(wait_cycles);
			instr->stalls += wait_cycles;
			total_stalls += wait_cycles;
		}
	}

	if (trace) {
		if (imm)
			fprintf(tracefp, " %-11d", *data);
		else
			fprintf(tracefp, " r%02d=%-7d", instr->op[k], *data);

		fflush(tracefp);
	}
}

static void skip_op()
{
	fprintf(tracefp, "            ");
}
	
static void print_result(int value, int addr)
{
	fprintf(tracefp, "%14c | r%02u := %13d\n", ' ', addr, value);
}


void run(void)
{
	int		a;
	int		b;
	int		c;
	int		dest;

	cycles	= 0;
	pc	= 0;

	while (cycles < max_cycles) {

		a = b = dest = -1;

		if (trace) {
			fprintf(tracefp, "%8d: %-8s ", pc, stmt_string[imem[pc].type]);
			fflush(stdout);
		}

		nexec[imem[pc].type] += 1;

		increment_cycles(1);

		imem[pc].count += 1;


		switch (imem[pc].type) {
		case NOP:
			error(FATAL, "sim found NOP\n");
			break;

		case LABEL:
			error(FATAL, "sim found LABEL\n");
			break;

		case SLL:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);

			dest = imem[pc].op[2];
			reg[dest] = a << b;

			if (trace)
				print_result(dmem[dest], dest);
			pc += 1;
			break;

		case SRA:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);

			dest = imem[pc].op[2];
			reg[dest] = (signed)a >> b;

			if (trace)
				print_result(dmem[dest], dest);
			pc += 1;
			break;

		case SRL:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);

			dest = imem[pc].op[2];
			reg[dest] = (unsigned)a >> b;

			if (trace)
				print_result(dmem[dest], dest);
			pc += 1;
			break;

		case ADD:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);

			dest = imem[pc].op[2];
			reg[dest] = a + b;

			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		case BT:
			read_op(&imem[pc], 0, &a, false, false);
			dest = imem[pc].op[2];

			if (a != 0)
				pc += dest;
			else
				pc += 1;
			if (trace)
				fputc('\n', tracefp);
			break;

		case BF:
			read_op(&imem[pc], 0, &a, false, false);
			dest = imem[pc].op[2];
				
			if (a == 0)
				pc += dest;
			else
				pc += 1;
			if (trace)
				fputc('\n', tracefp);
			break;

		case BA:
			dest = imem[pc].op[2];
			pc += dest;
			if (trace)
				fputc('\n', tracefp);
			break;

		case DIV:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);

			dest = imem[pc].op[2];

			if (b == 0)	
				error(FATAL, "sim found divide by zero");

			reg[dest] = a / b;
			ready_cycle[dest] = cycles + cost(DIV);

			if (trace)
				print_result(reg[dest], dest);

			pc += 1;
			break;

		case LD:

			read_op(&imem[pc], 0, &a, false, true);
			read_op(&imem[pc], 1, &b, imem[pc].imm, true);

			dest = imem[pc].op[2];
			ready_cycle[dest] = cycles + cost(LD);

			reg[dest] = dmem[a+b];

			if (trace)
				print_result(reg[dest], dest);

			pc += 1;
			break;

		case MOV:
			read_op(&imem[pc], 0, &a, imem[pc].imm, false);
			dest = imem[pc].op[2];

			reg[dest] = a;

			if (trace) {
				skip_op();
				print_result(reg[dest], dest);
			}

			pc += 1;
			break;

		case MUL:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);
			
			dest = imem[pc].op[2];
			reg[dest] = a * b;
			ready_cycle[dest] = cycles + cost(MUL);

			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		case NEG:
			read_op(&imem[pc], 0, &a, false, false);
			dest = imem[pc].op[2];
			reg[dest] = -a;

			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		case PUT:
			read_op(&imem[pc], 0, &a, imem[pc].imm, false);
			if (trace) {
				skip_op();
				fputc('\n', tracefp);
			}
			fprintf(output, "%d\n", a);
			pc += 1;
			break;

		case GET:
		{
			int	value;

			if (trace) {
				skip_op();
				skip_op();
			}

			dest = imem[pc].op[2];
			scanf("%d", &value);
			reg[dest] = value;
			
			if (trace)
				print_result(reg[dest], dest);

			pc += 1;
			break;
		}

		case RET:
			if (trace)
				fputc('\n', tracefp);
			goto end;

		case SEQ:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);
			dest = imem[pc].op[2];

			reg[dest] = a == b;
			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		case SGE:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);
			dest = imem[pc].op[2];
			reg[dest] = a >= b;
			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		case SGT:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);
			dest = imem[pc].op[2];
			reg[dest] = a > b;
			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		case SLE:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);
			dest = imem[pc].op[2];
			reg[dest] = a <= b;
			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		case SLT:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);
			dest = imem[pc].op[2];
			reg[dest] = a < b;
			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		case SNE:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);
			dest = imem[pc].op[2];
			reg[dest] = a != b;
			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		case ST:
			read_op(&imem[pc], 0, &a, false, true);
			read_op(&imem[pc], 1, &b, imem[pc].imm, true);
			read_op(&imem[pc], 2, &c, false, true);

			if (trace) {
				fprintf(tracefp, "   | m[%04u] := %9d\n", a+b, c);
			}
			dmem[a+b] = c;
			pc += 1;
			break;

		case SUB:
			read_op(&imem[pc], 0, &a, false, false);
			read_op(&imem[pc], 1, &b, imem[pc].imm, false);
			dest = imem[pc].op[2];
			reg[dest] = a - b;
			if (trace)
				print_result(reg[dest], dest);
			pc += 1;
			break;

		default:
			fatal(imem[pc].type);
		}
	}
	
end:
	fprintf(stderr, "C = %" PRIu64 "\n", cycles);
	;
}

void free_sim()
{
	free(reg);
	free(ready_cycle);
	free(imem);
	free(dmem);
}
