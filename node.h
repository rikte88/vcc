#ifndef node_h
#define node_h

#include "typedefs.h"
#include "op.h"

typedef enum {
	NO_NODE,
	ADD_NODE,
	ASSIGN_NODE,
	DIV_NODE,
	EQ_NODE,
	GE_NODE,
	GT_NODE,
	ID_NODE,
	IF_NODE,
	IF_ELSE_NODE,
	LE_NODE,
	LT_NODE,
	NE_NODE,
	NEG_NODE,
	MUL_NODE,
	NUM_NODE,
	PUT_NODE,
	GET_NODE,
	RETURN_NODE,
	STRING_NODE,
	STMT_LIST_NODE,
	SUB_NODE,
	WHILE_NODE,
	GOTO_NODE,
	LABEL_NODE,
	REF_NODE
} node_type_t;

struct node_t {
	node_type_t	type;		/* IF_NODE, etc */
	node_t*		a;		/* First child. */
	node_t*		b;		/* Second child. */
	node_t*		c;		/* Third child. */
	int		num;		/* A number if the node needs one. */
	char*		id;		/* Identifier if the node needs one. */
	list_t*		node_list;	/* A list of other nodes. */
	unsigned	line;		/* Source code line number. */
};

node_t* new_node(node_type_t, ...);
void free_node(node_t*);
op_t gencode(node_t*);

#endif
