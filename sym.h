#ifndef ac_sym_h
#define ac_sym_h

#include <stdint.h>

#include "list.h"
#include "set.h"
#include "stack.h"
#include "op.h"
#include "stack.h"

struct sym_t {
	char*		id;		/* Name of variable or temp. */
	uint64_t	index;		/* Unique number for this sym. */
	stmt_t*		def;		/* Statement which defines sym. */
	set_t*		modset;		/* Basic blocks where sym is defined. */
	list_t*		uses;		/* Statements which use sym. */
	stack_t*	rename_stack;	/* SSA rename stack. */
	unsigned	ssa_version;	/* SSA version. */
	bool		islabel;	/* True if sym is a branch target. */
	bool		isarray;	/* True if sym is an array. */
};

sym_t* new_sym(char*, int array_size);
void free_sym(sym_t*);
bool is_label_sym(sym_t*);
void add_use(sym_t*, stmt_t*);
void set_sym_def(sym_t*, stmt_t*);
unsigned sym_addr(sym_t*);
void deinit_sym(void);

#endif
