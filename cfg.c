#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"
#include "func.h"
#include "sym.h"
#include "globals.h"
#include "error.h"

/* Control flow graph construction.
 *
 */

void add_stmt_to_vertex(vertex_t* vertex, stmt_t* stmt)
{
	insert_last(&vertex->stmts, stmt);
}

bool connected(vertex_t* tail, vertex_t* head)
{
	int		k;

	/* Check if there already is an arc from tail to head. */

	for (k = 0; k < MAX_SUCC; k += 1)
		if (tail->succ[k] == head)
			return true;
	return false;
}

void connect(vertex_t* tail, vertex_t* head, bool unconditional_branch)
{
	vertex_t*	tmp;

	/* Add an arc from tail to head. */

	if (connected(tail, head))
		return;

	/* The target of an unconditional branch always is put at succ[1]
	 * and that of a conditional at succ[0].
	 *
	 */

	insert_last(&head->pred, tail);

	if (cfg_fp != NULL) {

		/* If we want to test a graph using the command % vcc -g file
		 *
		 */

		if (tail->succ[1] == NULL)
			tail->succ[1] = head;
		else 
			tail->succ[0] = head;

		if (tail->succ[0] != NULL
			&& tail->succ[0]->index > tail->succ[1]->index) {
			tmp = tail->succ[0];
			tail->succ[0] = tail->succ[1];
			tail->succ[1] = tmp;
		}

	} else if (unconditional_branch) {
		assert(tail->succ[1] == NULL);
		tail->succ[1] = head;
	} else {
		assert(tail->succ[0] == NULL);
		tail->succ[0] = head;
	}
}

vertex_t* new_vertex(op_t op)
{
	vertex_t*	vertex;

	vertex = calloc(1, sizeof(vertex_t));

	vertex->label		= op;
	vertex->dfnum		= -1;
	vertex->ancestor	= NULL;
	vertex->parent		= NULL;
	vertex->idom		= NULL;
	vertex->sdom		= NULL;

	if (op.type != NO_OP)
		vertex->index	= op_repr(op);

	return vertex;
}

void free_vertex(vertex_t* vertex)
{
	free_list(&vertex->pred);
	free_list(&vertex->stmts);
	free_list(&vertex->phi_func_list);
	free_set(&vertex->df);
	free(vertex);
}

vertex_t* new_ivertex(int index)
{
	vertex_t*	vertex;

	/* Used with vcc -g file */

	vertex = new_vertex(no_op);
	vertex->index = index;

	return vertex;
}

static int compare_index(void* ap, void* bp)
{
	vertex_t*	a = ap;
	vertex_t*	b = bp;

	return a->index - b->index;
}

vertex_t* open_vertex(op_t op, set_t** set)
{
	vertex_t*	vertex;
	vertex_t	b;

	/* op is a label and if we have not yet heard about this
	 * label then we create a basic block for it, otherwise
	 * we return the existing one.
	 *
	 */

	b.index = op_index(op);
	vertex = find(*set, &b, compare_index);

	if (vertex != NULL)
		return vertex;

	vertex = new_vertex(op);

	add(set, vertex, compare_index);

	return vertex;
}

vertex_t* open_ivertex(int index, set_t** set)
{
	vertex_t*	vertex;
	vertex_t	b;

	/* Used with vcc -g file */

	b.index = index;
	vertex = find(*set, &b, compare_index);

	if (vertex != NULL)
		return vertex;

	vertex = new_ivertex(index);
	add(set, vertex, compare_index);

	return vertex;
}

void to_cfg(func_t* func)
{
	int		tail_index;
	int		head_index;
	vertex_t*	vertex;
	vertex_t*	tail;
	vertex_t*	head;
	stmt_t*		stmt;
	vertex_t*	current;
	list_t*		p;
	list_t*		h;
	set_t*		vertex_set;
	op_t		label;

	/* Now we construct the control flow graph. Input is a 
	 * sequence of stmts and the output is the array func->vertex,
	 * with size func->nvertex.
	 *
	 */
	 
	vertex_set = NULL;

	if (cfg_fp != NULL) {
		func->start = NULL;
		func->exit = NULL;

		while (fscanf(cfg_fp, "%d %d", &tail_index, &head_index) == 2) {

			tail = open_ivertex(tail_index, &vertex_set);
			head = open_ivertex(head_index, &vertex_set);

			if (func->start == NULL)
				func->start = tail;

			connect(tail, head, true);
		}

	} else {

		/* Create special start and exit basic blocks. */
		func->start = open_vertex(new_label(), &vertex_set);
		func->exit = open_vertex(new_label(), &vertex_set);
		current = func->start;

		connect(func->start, func->exit, false);

		p = h = func->stmts;
		do {
			stmt = p->data;
			p = p->succ;

			switch (stmt->type) {
			case LABEL:
				vertex = open_vertex(stmt->op[0], &vertex_set);

				if (current != NULL)
					connect(current, vertex, true); 

				current = vertex,

				add_stmt_to_vertex(current, stmt);
				break;

			case BT:
			case BF:
				assert(current != NULL);

				label = branch_dest(stmt);

				vertex = open_vertex(label, &vertex_set);

				connect(current, vertex, false);

				add_stmt_to_vertex(current, stmt);
				break;
				
			case BA:
				if (current == NULL) {
					free_stmt(stmt);
					break;
				}

				label = branch_dest(stmt);

				vertex = open_vertex(label, &vertex_set);

				connect(current, vertex, true);

				add_stmt_to_vertex(current, stmt);
				current = NULL;
				break;

			case RET:
				if (current == NULL) {
					free_stmt(stmt);
					break;
				}

				add_stmt_to_vertex(current, stmt);
				connect(current, func->exit, true);
				current = NULL;
				break;

			default:
				if (current != NULL)
					add_stmt_to_vertex(current, stmt);
				else
					free_stmt(stmt);
			}

		} while (p != h);
	}

	/* Now we move all basic blocks from the set to the vertex array. */

	func->vertex = set_to_array(vertex_set, &func->nvertex);

	free_set(&vertex_set);
	free_list(&func->stmts);

	print_cfg(func);

}

void from_cfg(func_t* func)
{
	/* Move all stmts from the basic blocks to func->stmts. */

	vertex_t*	v;
	vertex_t*	w;
	int		i;
	list_t*		p;
	list_t*		h;
	stmt_t*		stmt;
	stmt_t*		last_stmt;	/* last stmt in v. */

	for (i = 0; i < func->nvertex; i += 1) {

		v = func->vertex[i];

		if (v == func->exit)
			continue;

		if (v->stmts == NULL)
			continue;

		p = h = v->stmts;

		do {
			stmt = p->data;
			add_stmt(stmt);

			p = p->succ;
		} while (p != h);

		if (i == func->nvertex - 1)
			w = NULL;
		else
			w = func->vertex[i+1];

		assert(v->succ[1] != NULL);

		/* Consider the following original code:
		 *	lab x
		 *	  mul
		 *	lab y
		 *
		 * There is no need for a branch after the mul to y. However,
		 * optimization may change the order of the basic blocks
		 * so thay y does not follow x. Without an explicit branch
		 * to y we would follow-through to some unknown place.
		 * The following code adds such explicit branches when needed.
		 *
		 */

		if (w == NULL || w->index != v->succ[1]->index) {
			/* w == null means V is the last block. */

			last_stmt = v->stmts->pred->data;

			switch (last_stmt->type) {
			case BA:
			case RET:
				break;

			default:
				stmt = new_stmt(BA, no_op, no_op,
					v->succ[1]->label, last_stmt->line);
				add_stmt(stmt);
			}
		}
	}
}
