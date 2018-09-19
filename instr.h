#ifndef instr_h
#define instr_h

#include "typedefs.h"
#include "stmt.h"

struct instr_t {
	stmt_type_t	type;	/* MUL, ADD etc, this is the opcode. */
	bool		imm;	/* True if instr has an immediate ie constant */
				/* operand. For MOV op[0] can be constant and */
				/* for others: op[1] can be constant. */

	int		op[3];	/* Operands in the instruction. */

	/* The following are used for producing statistics,
	 * and are not implemented in hardware. 
	 *
	 */

	unsigned	count;	/* Number of times the instruction executed. */
	unsigned	cycles;	/* Clock cycles. */
	unsigned	addr;	/* Address of instr. */
	unsigned	stalls;	/* Stalled clock cycles. */
	
};

void print_instr(instr_t* instr, FILE* fp);
unsigned cost(stmt_type_t);
void init_instr(void);

#endif
