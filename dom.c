#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include "util.h"
#include "cfg.h"
#include "func.h"
#include "sym.h"
#include "globals.h"
#include "error.h"

static bool visited(vertex_t* v)
{
	return v->dfnum != -1;
}

static void dfs(vertex_t* v, int* dfnum, vertex_t** vertex)
{
	/* succ[0] corresponds to the target of a conditional branch.
	 * succ[0] is NULL for an unconditional branch (BA).
	 * succ[1] corresponds to the target of an unconditional branch.
	 *
	 */

	/* 1. assign number to self
	 * 2. recurse left
	 * 3. recurse right
	 */

	v->dfnum = *dfnum;  // replace -1
	vertex[*dfnum] = v; // reorder elements.
	// sdom is already self.
	// ancestor is already null
	(*dfnum)++;

	for (int i=0; i<2; i++) {
		vertex_t *w = v->succ[i];
		if (w) {
			int todo = !visited(w);
			// we cannot check todo by checking sdom because they are never null.
			if (todo) {
				dfs(w, dfnum, vertex);
			}
		}
	}
}

static void link(vertex_t* parent, vertex_t* child)
{
	child->ancestor = parent;
	pr("ancestor(%d) = %d\n", child->index, parent->index);
}

static vertex_t* eval(vertex_t* v)
{
	vertex_t*		u;

	u = v;

	/* Find the ancestor of V with least semi-dominator. */

	while (v->ancestor != NULL) {

		if (v->sdom->dfnum < u->sdom->dfnum)
			u = v;

		v = v->ancestor;
	}

	return u;
}

static void remove_from_preds(vertex_t* w)
{
	int		i;

	for (i = 0; i < MAX_SUCC; ++i)
		if (w->succ[i] != NULL)
			remove_from_list(&w->succ[i]->pred, w);
}

static void free_stmts(vertex_t* w)
{
	list_t*		p;
	list_t*		h;

	p = h = w->stmts;

	do {
		free_stmt(p->data);
		p = p->succ;
	} while (p != h);
}

void dominance(func_t* func)
{
	int		i;
	int		dfnum;
	vertex_t*	u;
	vertex_t*	v;
	vertex_t*	w;
	list_t*		p;
	list_t*		h;
	vertex_t*	original[func->nvertex];

	/*printf("LAB 1: Remove RETURN in \"%s\", line %d\n",
		__FILE__, 1+(int)__LINE__);
	return;*/

	if (0) visited(NULL);	/* For silencing GCC. */

	/* Construct the immediate-dominator tree. */

	memcpy(original, func->vertex, sizeof original);

	use_pr = false;

	/* Step 1. */

	/* Initialise sdom of each vertex to itself. */
	for (i = 0; i < func->nvertex; i++)	{
		func->vertex[i]->dfnum		= -1;
		func->vertex[i]->sdom		= func->vertex[i];
		func->vertex[i]->idom		= NULL;
		func->vertex[i]->ancestor	= NULL;
		func->vertex[i]->parent		= NULL;
		func->vertex[i]->domchild	= NULL;
		func->vertex[i]->domsibling	= NULL;

		if (func->vertex[i] == func->start) {
			u = func->vertex[0];
			func->vertex[0] = func->start;
			func->vertex[i] = u;
		}
	}

	dfnum = 0;

	assert(func->vertex[0] == func->start);

	dfs(func->vertex[0], &dfnum, func->vertex);

	for (i = 0; i < func->nvertex; ++i) {
		if (original[i]->dfnum == -1) {
			remove_from_preds(original[i]);
			free_stmts(original[i]);
			free_vertex(original[i]);
		}
	}

	pr("dfnum = %d\n", dfnum);
	pr("n     = %d\n", func->nvertex);
	func->nvertex = dfnum;

	print_cfg(func);

	for (i = func->nvertex - 1; i > 0; i--) {
		w = func->vertex[i];

		/* Step 2. */
		pr("\nstep 2 for %d:%d\n", w->index, w->dfnum);

		/* All vertices except the start node must have a predecessor.
		 *
		 */

		assert(w->pred != NULL);

		p = h = w->pred;
		do {
			v = p->data;
			p = p->succ;

			u = eval(v);

			pr("pred %d\n", v->index);
			pr("eval(%d) = %d\n", v->index, u->index);
			pr("sdom(%d) = %d\n", u->index, u->sdom->index);

			/* MAKE COMPLETE DURING LAB 1 */

		} while (p != h);

		pr("sdom(%d) = %d\n", w->index, w->sdom->index);

		link(w->parent, w);

		/* Step 3. */
		insert_first(&w->sdom->bucket, w);

		pr("emptying bucket of %d\n", w->parent->index);

		p = h = w->parent->bucket;

		if (p == NULL)
			continue;

		do {

			v = p->data;
			p = p->succ;
			u = eval(v);

			/* MAKE COMPLETE DURING LAB 1 */

		} while (p != h);

		free_list(&w->parent->bucket);
	}

	/* Step 4. */
	pr("\nstep 4\n", "");
	for (i = 1; i < func->nvertex; i++) {
		w = func->vertex[i];

		/* MAKE COMPLETE DURING LAB 1 */

		pr("final idom(%d) = %d\n", w->index, w->idom->index);
	}

	print_dt(func);
}
