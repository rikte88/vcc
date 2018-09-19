#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <assert.h>
#include "func.h"
#include "error.h"

#define EDGE_THICKNESS	(3)

void print_cfg(func_t* func)
{
	char		buf[BUFSIZ];
	FILE*		fp;
	int		i;
	int		j;
	vertex_t*	v;

	sprintf(buf, "cfg.%d.dot", func->vcg++);
	fp = fopen(buf, "w");
	if (fp == NULL) {
		warning("cannot open file %s for writing", buf);
		return;
	}
		
	fprintf(fp, "digraph cfg {\n");

	for (i = 0; i < func->nvertex; i += 1) {
		v = func->vertex[i];

		fprintf(fp, "%d -> { ", v->dfnum);

		for (j = 0; j < MAX_SUCC; j += 1) {
			if (v->succ[j] == NULL)
				continue;

			fprintf(fp, "%d ", v->succ[j]->dfnum);
		}

		fprintf(fp, "}\n");
	}
	fprintf(fp, "}\n");

	fclose(fp);
}

static void walk_dt(vertex_t* v, FILE* fp)
{
	vertex_t*	w;

	w = v->domchild;

	while (w != NULL) {

		fprintf(fp, "%d -> { %d }\n", v->dfnum, w->dfnum);
		walk_dt(w, fp);

		w = w->domsibling;
	}
}

void print_dt(func_t* func)
{
	char		buf[BUFSIZ];
	FILE*		fp;

	sprintf(buf, "dt.%d.dot", func->vcg++);
	fp = fopen(buf, "w");
	if (fp == NULL) {
		warning("cannot open file %s for writing", buf);
		return;
	}
		
	fprintf(fp, "digraph dt {\n");

	walk_dt(func->vertex[0], fp);

	fprintf(fp, "}\n");

	fclose(fp);
}
