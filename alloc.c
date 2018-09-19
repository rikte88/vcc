#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"
#include "func.h"
#include "globals.h"
#include "error.h"
#include "sym.h"

/* Do a simplest possible register allocation: one stmt is treated
 * at a time. Operand number K is loaded into register K+1 before
 * being used. Register 0 will always give the value 0 when it is read
 * in a memory access.
 *
 */

void alloc_regs(func_t* func)
{
	unsigned	line;
	int		k;
	stmt_t*		stmt;
	stmt_t*		load;
	stmt_t*		store;
	vertex_t*	v;
	op_t		reg;
	op_t		imm;
	int		i;
	int		addr;
	list_t*		p;
	list_t*		h;
	sym_t*		sym;

	zero = new_reg_op(0);
	for (i = 0; i < func->nvertex; i += 1) {
		v = func->vertex[i];

		if (v->stmts == NULL)
			continue;

		p = h = v->stmts;

		do {
			stmt = p->data;

			line = stmt->line;
			store = NULL;

			if (stmt->type == NOP) {
				p = p->succ;
				continue;
			}

			for (k = 0; k < 3; k += 1) {
				if (stmt->op[k].type == NO_OP
					|| !is_sym(stmt->op[k])
					|| is_label(stmt->op[k]))
					continue;
				
				sym = stmt->op[k].u.sym;

				addr = sym_addr(sym);
				imm = new_num_op(addr);

				if (sym->isarray) {
					stmt->op[k] = imm;
					continue;
				}

				reg = new_reg_op(k+1);

				if (k < 2 || stmt->type == ST) {
					load = new_stmt(LD, zero, imm,reg,line);
					insert_before(&p, load);

				} else {
					store = new_stmt(ST, zero,imm,reg,line);
					insert_after(&p, store);
					p = p->succ;
				}

				stmt->op[k] = reg;
			}

			p = p->succ;

		} while (p != h);
	}
}
