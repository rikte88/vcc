#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"
#include "func.h"
#include "globals.h"
#include "error.h"
#include "list.h"
#include "set.h"
#include "typedefs.h"

#include "sym.h"
#include "op.h"
#include "stmt.h"

/* The first operand must not be a constant in certain statements.
 * This function inserts a MOV to a new temporary and uses that
 * temporary instead of the constant as the first operand.
 * 
 * Call this function before doing register allocation.
 *
 */

void fix_const_operand(func_t* func)
{
	int		k;
	int		i;
	list_t*		p;
	list_t*		h;
	stmt_t*		stmt;
	stmt_t*		mov;

	for (i = 0; i < func->nvertex; i += 1) {
		p = h = func->vertex[i]->stmts;
		if (p == NULL)
			continue;
		do {
			stmt = p->data;

			switch (stmt->type) {
			case ADD:
			case DIV:
			case MUL:
			case SEQ:
			case SGE:
			case SGT:
			case SLE:
			case SLL:
			case SLT:
			case SRA:
			case SRL:
			case SNE:
			case SUB:
			case ST:
			case LD:
				for (k = 0; k <= 2; k += 2) {
					if (stmt->op[k].type != NUM_OP)
						continue;

					/* Only ST can have a numeric op[2]. */
					assert(k == 0 || stmt->type == ST);

					mov = new_stmt(MOV, stmt->op[k], no_op, 
						temp(), stmt->line);

					stmt->op[k] = mov->op[2];

					insert_before(&p, mov);
				}

			default:
				/* do nothing. */

				;
			}
			
			p = p->succ;

		} while (p != h);
	}
}
