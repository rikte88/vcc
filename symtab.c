#include <string.h>
#include "error.h"
#include "globals.h"
#include "symtab.h"
#include "op.h"
#include "sym.h"
#include "util.h"

static set_t*	var_table;
static set_t*	label_table;

static int compare_sym(void* ap, void* bp)
{
	sym_t*		a = ap;
	sym_t*		b = bp;

	return strcmp(a->id, b->id);
}

op_t lookup(char* id)
{
	sym_t*		sym;
	sym_t		s;

	s.id = id;

	sym = find(var_table, &s, compare_sym);

	if (sym == NULL) {
		error(FATAL, "\"%s\" line %u: undefined variable: %s\n", 
			source, line, id);
	} else if (sym->isarray)
		return new_op(NUM_OP, sym->index);
	else
		return new_sym_op(sym);

	return no_op;
}

op_t lookup_label(char* id)
{
	sym_t*		sym;
	sym_t		s;

	s.id = id;

	sym = find(label_table, &s, compare_sym);

	if (sym == NULL) {
		error(FATAL, "\"%s\" line %u: undefined label: %s\n", 
			source, line, id);
	} else 
		return new_sym_op(sym);

	return no_op;
}

static void check_label_redecl(sym_t* sym)
{
	if (find(label_table, sym, compare_sym) != NULL)
		error(FATAL, "\"%s\" line %u: redeclared label: %s\n", 
			source, line-1, sym->id);
}

int install(char* id, int array_size)
{
	sym_t*		sym;

	sym = new_sym(id, array_size);

	if (!is_label_sym(sym)) {
		add(&var_table, sym, compare_sym);
		add_sym(sym);
	} else {
		check_label_redecl(sym);
		add(&label_table, sym, compare_sym);
	}

	return sym->index;
}

static void free_symtab(set_t* table)
{
	void**		a;
	size_t		n;
	size_t		i;

	a = set_to_array(table, &n);
	for (i = 0; i < n; ++i)
		free_sym(a[i]);
	free(a);
	free_set(&table);
}

void deinit_symtab(void)
{
	free_symtab(var_table);
	free_symtab(label_table);
}

void init_symtab(void)
{
	/* Nothing to do. */
}
