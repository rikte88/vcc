#ifndef ssa_typedefs_h
#define ssa_typedefs_h

#include <stdbool.h>

typedef struct sim_t	sim_t;
typedef struct op_t	op_t;
typedef struct func_t	func_t;
typedef struct stmt_t	stmt_t;
typedef struct instr_t	instr_t;
typedef struct sym_t	sym_t;
typedef struct vertex_t	vertex_t;
typedef struct node_t	node_t;

typedef int (*compare_func)(void*, void*);

#endif
