#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"
#include "func.h"
#include "sym.h"
#include "globals.h"
#include "stmt.h"
#include "error.h"

phi_t* new_phi(vertex_t* x)
{
	phi_t*		phi;

	phi		= calloc(1, sizeof(phi_t));
	phi->n		= length(x->pred);
	phi->rhs	= calloc(phi->n, sizeof(op_t));

	return phi;
}

void free_phi(phi_t* phi)
{
	free(phi->rhs);
	free(phi);
}

static void print_index(void* vp, FILE* fp)
{
	vertex_t*	v = vp;

	fprintf(fp, "%d", v->index);
}

static void df(vertex_t* u)
{
	/* MAKE COMPLETE DURING LAB 2. */
	/* postorder traversal*/
	if (u->domchild) {
		df(u->domchild);
	}
	if (u->domsibling) {
		df(u->domsibling);
	}

	u->df = NULL;

	for (int i = 0; i < 2; i++) {
		vertex_t *v = u->succ[i];
		if (v != NULL && v->idom != u) {
			join_set(&u->df, v);
		}
	}

	vertex_t *w = u->domchild;
	while (w != NULL) {
		size_t	n;
		vertex_t **a = set_to_array(w->df, &n);
		for (int i = 0; i < n; i++) {
			vertex_t *v = a[i]; //use a[i] here
			if (v->idom != u) {
				join_set(&u->df, v);
			}
		}
		free(a);
		w = w->domsibling;
	}
}

void modsets(func_t* func)
{
	int		i;
	stmt_t*		stmt;
	vertex_t*	v;
	sym_t*		sym;
	list_t*		p;
	list_t*		h;

	for (i = 0; i < func->nvertex; i += 1) {
		v = func->vertex[i];
		if (v->stmts == NULL)
			continue;
		p = h = v->stmts;
		do {
			stmt = p->data;
			p = p->succ;
			sym = defined_sym(stmt);
			if (sym != NULL)
				join_set(&sym->modset, v);
		} while (p != h);
	}
}

void insert_phi_stmt(func_t* func, vertex_t* vertex, sym_t* sym)
{
	int		i;
	unsigned	line;
	phi_t*		phi;
	stmt_t*		stmt;
	list_t*		p;

	if (vertex == func->exit)
		return;

	p = vertex->stmts;

	stmt = p->data;
	assert(stmt->type == LABEL);
	line = stmt->line;

	stmt = new_stmt(PHI, no_op, no_op, new_sym_op(sym), line);
	insert_after(&p, stmt);

	phi = new_phi(vertex);
	stmt->phi = phi;
	phi->stmt = stmt;
	insert_last(&vertex->phi_func_list, phi);

	for (i = 0; i < phi->n; i += 1)
		phi->rhs[i] = new_sym_op(sym);
}

unsigned which_pred(vertex_t* pred, vertex_t* vertex)
{
	int		i;
	list_t*		h;
	list_t*		p;

	i = 0;

	h = p = vertex->pred;

	assert(p != NULL);

	do {
		if (p->data == pred)
			return i;

		i += 1;

		p = p->succ;

	} while (p != h);

	error(FATAL, "pred not found in which_pred");

	/* We will never get here. */

	return 0;
}

void rename_symbols(vertex_t* u)
{
	/* MAKE COMPLETE DURING LAB 2. */
	stmt_t *t;
	list_t *vars_to_pop_last = NULL;

	list_t*		p = u->stmts;
	if (p != NULL)
	do {
		t = p->data;
		p = p->succ;


		// "foreach vairable V in RHS"
		// this is the calculation side
		for (int i = 0; i < 2; i++) {
			if (is_var(t->op[i])) {
				sym_t *V = t->op[i].u.sym;
				// efter här: foreach V
				assert(V);
				sym_t *Vi = top(V->rename_stack);
				t->op[i].u.sym = Vi;
			}
		}

		// "foreach vairable V in LHS"
		// this is the assignment side.
		sym_t *V = defined_sym(t);
		if (V != NULL) {
			unsigned *i = &V->ssa_version;
			op_t Vi = temp();
			Vi.u.sym->ssa_version = *i;
			insert_last(&vars_to_pop_last, V);
			t->op[2] = Vi;
			push(V->rename_stack, Vi.u.sym);
			(*i)++;
		}
	} while (p != u->stmts);

	for (int i = 0; i < 2; i++) {
		vertex_t *v = u->succ[i];
		if (!v) continue;
		unsigned j = which_pred(u, v); // correct order verified
		p = v->phi_func_list;
		if (p)
		do {
			phi_t *phi = p->data; //verified type
			p = p->succ;
			assert(is_var(phi->rhs[j]));
			sym_t *V = phi->rhs[j].u.sym;
			phi->rhs[j].u.sym = top(V->rename_stack);

		} while(p!=v->phi_func_list);
	}

	vertex_t *v = u->domchild;
	while (v != NULL) {
		rename_symbols(v);
		v = v->domsibling;
	}

	p = vars_to_pop_last;
	if (p != NULL)
	do {
		sym_t *x = p->data;
		p = p->succ;
		pop(x->rename_stack);
	} while (p != vars_to_pop_last);
	free_list(&vars_to_pop_last);
}

void insert_phi(func_t* func)
{
	/* Insert phi functions. Figure 11. */

	int		iter;		/* Itereration count of Figure 11. */
	sym_t*		sym;		/* Variable V of Figure 11. */
	vertex_t*	x;		/* Node X of Figure 11. */
	vertex_t*	y;		/* Node Y of Figure 11. */
	vertex_t**	a;		/* Node Y of Figure 11. */
	int		i;
	size_t		n;
	list_t*		p;
	list_t*		h;
	list_t*		worklist;

	iter = 0;

	if (func->var == NULL)
		return;

	for (i = 0; i < func->nvertex; i += 1)
		func->vertex[i]->work = func->vertex[i]->already = 0;

	p = h = func->var;

	worklist = NULL;

	do {

		sym = p->data;
		p = p->succ;
		iter += 1;

		/* Add all basic blocks where sym which have an assignment
		 * to sym to the basic block worklist.
		 *
		 */

		/* Create a temporary array for simplicity. */

		if (use_pr) {
			pr("modset(%s) = ", sym->id);
			print_set(sym->modset, print_index, stdout);
		}

		a = set_to_array(sym->modset, &n);
		for (i = 0; i < n; i += 1) {
			x = a[i];
			x->work = iter;
			insert_last(&worklist, x);
		}
		free(a);

		/* Now worklist contains all assignment nodes of sym. */

		while (worklist != NULL) {
			x = remove_first(&worklist);

			/* Create a temporary array for simplicity. */
			a = set_to_array(x->df, &n);
			for (i = 0; i < n; i += 1) {
				y = a[i];

				if (y->already >= iter)
					continue;

				assert(y != func->vertex[0]);
				insert_phi_stmt(func, y, sym);
				y->already = iter;
				if (y->work >= iter)
					continue;
				y->work = iter;
				insert_last(&worklist, y);
			}
			free(a);
		}

	} while (p != h);
}

void to_ssa(func_t* func)
{
	sym_t*		sym;
	list_t*		p;
	list_t*		h;

	/*printf("LAB 2: Remove RETURN in \"%s\", line %d\n",
		__FILE__, 1+(int)__LINE__);
	return;*/

	if (func->var == NULL)
		return;

	df(func->vertex[0]);
	printf("done with df\n");

	p = h = func->var;
	do {
		sym = p->data;
		p = p->succ;
		join_set(&sym->modset, func->vertex[0]);
		sym->rename_stack = new_stack();
		push(sym->rename_stack, sym);
	} while (p != h);

	modsets(func);
	insert_phi(func);
	rename_symbols(func->vertex[0]);

	p = h = func->var;
	do {
		sym = p->data;
		p = p->succ;
		free_stack(&sym->rename_stack);
	} while (p != h);

	free_list(&func->var);
}

static void fix_move(phi_t* phi, list_t** moves)
{
	stmt_t*		move;
	sym_t*		phi_dest;
	op_t		t;

	t = temp();

	phi_dest = phi->stmt->op[2].u.sym;
	phi->stmt->op[2].u.sym = t.u.sym;

	/* Save the real destination operand of the PHI function in
	 * move->op[1] and also tell the move which PHI this was.
	 */

	move = new_stmt(MOV, t, no_op, new_sym_op(phi_dest), line);
	move->op[1] = new_sym_op(phi_dest);
	move->phi = phi;

	/* This move will be put after all the normal moves inserted by
	 * from_ssa.
	 */
	insert_last(moves, move);
}

static void check_later_use(phi_t* phi, list_t* link, list_t** moves, int k)
{
	stmt_t*		stmt;

	link = link->succ;
	stmt = link->data;

	/* If there is a later use as a PHI-operand of the destination,
	 * then we must save the value so that use can consume it.
	 */

	while (stmt->type == PHI || stmt->type == NOP) {

		if (stmt->type == PHI
			&& is_sym(stmt->phi->rhs[k])
			&& stmt->phi->rhs[k].u.sym == phi->stmt->op[2].u.sym)
			fix_move(phi, moves);

		link = link->succ;
		stmt = link->data;
	}

}

static void insert_move(
	vertex_t*		pred,
	phi_t*		phi,
	int		k,
	list_t*		link,
	list_t**	moves)
{
	list_t*		p;
	stmt_t*		last_stmt;
	stmt_t*		stmt;
	stmt_t*		move;
	unsigned	line;
	op_t		op;

	/* We take as line number of our new move statement, the line
	 * number of the last statement in the basic block.
	 *
	 */

	last_stmt = pred->stmts->pred->data;
	assert(last_stmt->type == BA);

	line = last_stmt->line;

	check_later_use(phi, link, moves, k);

	op = new_sym_op(phi->stmt->op[2].u.sym);
	move = new_stmt(MOV, phi->rhs[k], no_op, op, line);

	p = pred->stmts->pred->pred;
	stmt = p->data;

	if (is_branch(stmt))
		insert_before(&p, move);
	else
		insert_after(&p, move);

}

static void insert_move_before_branch(vertex_t* w, stmt_t* move)
{
	list_t*		p;
	stmt_t*		stmt;

	if (w->stmts == NULL)
		return;

	assert(move->op[1].type != NO_OP);

	/* Now restore the PHI function so that it has the correct
	 * destination operand.
	 */

	move->phi->stmt->op[2] = move->op[1];
	move->op[1] = no_op;
	move->phi = NULL;

	p = w->stmts->pred->pred;
	stmt = p->data;

	if (is_branch(stmt))
		insert_before(&p, move);
	else
		insert_after(&p, move);
}

static void insert_move_list(vertex_t* w, list_t* moves)
{
	list_t*		p;

	p = moves;

	do {
		insert_move_before_branch(w, p->data);
		p = p->succ;
	} while (p != moves);
}

void from_ssa(func_t* func)
{
	vertex_t*	x;
	vertex_t*	pred;
	int		i;
	int		k;
	phi_t*		phi;
	stmt_t*		stmt;
	list_t*		q;
	list_t*		p;
	list_t*		more_moves;


	/*printf("LAB 2: Remove RETURN in \"%s\", line %d\n",
		__FILE__, 1+(int)__LINE__);
	return;*/

	for (i = 1; i < func->nvertex; i += 1) {
		x = func->vertex[i];

		if (x == func->exit)
			continue;

		assert(x->stmts != NULL);

		p = x->pred;

		do {
			// Next predecessor vertex.
			pred = p->data;
			p = p->succ;
			k = which_pred(pred, x);

			// Find link of first PHI.
			q = x->stmts;
			q = q->succ;

			// Reset stmt to first PHI (which might be a NOP now).
			stmt = q->data;

			more_moves = NULL;

			while (stmt->type == PHI || stmt->type == NOP) {

				if (stmt->type == PHI) {
					phi = stmt->phi;
					insert_move(pred, phi, k, q,
						&more_moves);
				}

				q = q->succ;
				stmt = q->data;

			}

			if (more_moves != NULL) {
				insert_move_list(pred, more_moves);
				free_list(&more_moves);
			}

			q = q->succ;
			stmt = q->data;
		} while (p != x->pred);

		// Finally change each PHI into a NOP.
		q = x->stmts;
		q = q->succ;
		stmt = q->data;

		while (stmt->type == PHI || stmt->type == NOP) {
			stmt->type = NOP;
			q = q->succ;
			stmt = q->data;
		}
	}
}
