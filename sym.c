#include <inttypes.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "list.h"
#include "globals.h"
#include "stmt.h"
#include "sym.h"
#include "op.h"

/* The index will also be used as the symbol's address in the data memory. */
static uint64_t	next_index;
static list_t*	templist;

sym_t* new_sym(char* id, int array_size)
{
	sym_t*		sym;

	sym = calloc(1, sizeof(sym_t));

	sym->id 		= id;
	sym->index		= next_index;
	sym->def		= NULL;
	sym->ssa_version	= 0;

	if (array_size > 0) {
		next_index += array_size;
		sym->isarray = true;
	} else {
		next_index += 1;
		if (array_size < 0)
			sym->islabel = true;
	}

	return sym;
}

void free_sym(sym_t* sym)
{
	free_set(&sym->modset);
	free_stack(&sym->rename_stack);
	free_list(&sym->uses);
	free(sym->id);
	free(sym);
}

op_t make_temp(bool label)
{
	char		id[40];
	char*		s;
	op_t		op;
	sym_t*		sym;

	if (label)
		sprintf(id, "$L%" PRIu64, next_index);
	else
		sprintf(id, "$%" PRIu64, next_index);
	s = strdup2(id);
	sym = new_sym(s, 0);

	if (!label)
		add_sym(sym);

	insert_last(&templist, sym);
	sym->islabel = label;
	op = new_sym_op(sym);
	
	return op;
}

op_t temp()
{
	return make_temp(false);
}

op_t new_label()
{
	return make_temp(true);
}

unsigned sym_addr(sym_t* sym)
{
	return sym->index;
}

void add_use(sym_t* sym, stmt_t* stmt)
{
	insert_last(&sym->uses, stmt);
}

void set_sym_def(sym_t* sym, stmt_t* stmt)
{
	sym->def = stmt;
}

bool is_label_sym(sym_t* sym)
{
	return sym->islabel;
}

static void void_ptr_param_free_sym(void* p)
{
	free_sym(p);
}

void deinit_sym(void)
{
	apply(templist, void_ptr_param_free_sym);
	free_list(&templist);
}
