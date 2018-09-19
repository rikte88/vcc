#include <assert.h>
#include <stdio.h>
#include <stdarg.h>

#include "util.h"
#include "error.h"
#include "globals.h"
#include "node.h"
#include "sym.h"
#include "stmt.h"
#include "y.tab.h"

node_t* new_node(node_type_t type, ...)
{
	va_list		ap;
	node_t*		node;

	va_start(ap, type);

	node = calloc(1, sizeof(node_t));
	
	node->type = type;
	node->line = line;

	switch (type) {
	case ADD_NODE:
	case DIV_NODE:
	case LE_NODE:
	case LT_NODE:
	case NE_NODE:
	case MUL_NODE:
	case WHILE_NODE:
	case SUB_NODE:
	case EQ_NODE:
	case GE_NODE:
	case GT_NODE:
	case IF_NODE:
	case REF_NODE:
		node->a = va_arg(ap, node_t*);		
		node->b = va_arg(ap, node_t*);		
		break;

	case NUM_NODE:
		node->num = va_arg(ap, int);
		break;

	case GOTO_NODE:
	case ID_NODE:
		node->id = va_arg(ap, char*);
		break;

	case LABEL_NODE:
		node->id = va_arg(ap, char*);
		node->a = va_arg(ap, node_t*);
		break;

	case NEG_NODE:
	case PUT_NODE:
	case RETURN_NODE:
		node->a = va_arg(ap, node_t*);		
		break;

	case GET_NODE:
		break;

	case IF_ELSE_NODE:
	case ASSIGN_NODE:
		node->a = va_arg(ap, node_t*);		
		node->b = va_arg(ap, node_t*);		
		node->c = va_arg(ap, node_t*);		
		break;


	case STMT_LIST_NODE:
		node->node_list = va_arg(ap, list_t*);		
		break;

	default:
		fatal(type);
	}

	va_end(ap);

	return node;
}

void free_node(node_t* node)
{
	list_t*		p;
	list_t*		h;

	if (node == NULL)
		return;

	if (node->a != NULL) free_node(node->a);
	if (node->b != NULL) free_node(node->b);
	if (node->c != NULL) free_node(node->c);

	if (node->type == STMT_LIST_NODE && node->node_list != NULL) {
		p = h = node->node_list;
		do {
			free_node(p->data);
			p = p->succ;	
		} while (p != h);
		free_list(&node->node_list);
	}

	switch (node->type) {
	case GOTO_NODE:
		free(node->id);	
		break;
	
	default:
		;
	}

	free(node);
}

op_t gencode(node_t* node)
{
	op_t		result;
	op_t		addr;
	node_t*		a;
	node_t*		b;
	node_t*		c;
	int		line;

	a = node->a;
	b = node->b;
	c = node->c;
	line = node->line;

	result = no_op;

	switch (node->type) {
	case ADD_NODE:
	{
		result = temp();
		emit(ADD, gencode(a), gencode(b), result, line);
		break;
	}

	case REF_NODE:
	{
		result = temp();
		addr = temp();
		emit(ADD, gencode(a), gencode(b), addr, line);
		emit(LD, addr, zero, result, line);
		break;
	}

	case ASSIGN_NODE:
	{
		if (node->b == NULL) {
			result = gencode(a);
			emit(MOV, gencode(c), no_op, result, line);
		} else {
			addr = temp();
			emit(ADD, gencode(a), gencode(b), addr, line);
			emit(ST, addr, zero, gencode(c), line);
		}
		break;
	}

	case DIV_NODE:
	{
		result = temp();
		emit(DIV, gencode(a), gencode(b), result, line);
		break;
	}

	case EQ_NODE:
	{
		result = temp();
		emit(SEQ, gencode(a), gencode(b), result, line);
		break;
	}

	case GE_NODE:
	{
		result = temp();
		emit(SGE, gencode(a), gencode(b), result, line);
		break;
	}

	case GT_NODE:
	{
		result = temp();
		emit(SGT, gencode(a), gencode(b), result, line);
		break;
	}

	case ID_NODE:
	{
		result = lookup(node->id);
		free(node->id);
		break;
	}

	case IF_NODE:
	{
		op_t		cond;
		op_t		then_label;
		op_t		end_label;

		then_label = new_label();
		end_label = new_label();

		cond = gencode(a);
		emit(BF, cond, no_op, end_label, line);
		emit(BA, no_op, no_op, then_label, line);

		emit(LABEL, then_label, no_op, no_op, line);
		gencode(b);
		emit(BA, no_op, no_op, end_label, line);

		emit(LABEL, end_label, no_op, no_op, line);
		break;
	}

	case IF_ELSE_NODE:
	{
		op_t		cond;
		op_t		then_label;
		op_t		else_label;
		op_t		end_label;

		then_label = new_label();
		else_label = new_label();
		end_label = new_label();

		cond = gencode(a);

		emit(BF, cond, no_op, else_label, line);
		emit(BA, no_op, no_op, then_label, line);

		emit(LABEL, then_label, no_op, no_op, line);
		gencode(b);
		emit(BA, no_op, no_op, end_label, line);

		emit(LABEL, else_label, no_op, no_op, line);
		gencode(c);
		emit(BA, no_op, no_op, end_label, line);

		emit(LABEL, end_label, no_op, no_op, line);
		break;
	}

	case LE_NODE:
	{
		result = temp();
		emit(SLE, gencode(a), gencode(b), result, line);
		break;
	}

	case LT_NODE:
	{
		result = temp();
		emit(SLT, gencode(a), gencode(b), result, line);
		break;
	}

	case NE_NODE:
	{
		result = temp();
		emit(SNE, gencode(a), gencode(b), result, line);
		break;
	}

	case NEG_NODE:
	{
		result = temp();
		emit(NEG, gencode(a), no_op, result, line);
		break;
	}

	case MUL_NODE:
	{
		result = temp();
		emit(MUL, gencode(a), gencode(b), result, line);
		break;
	}

	case NUM_NODE:
	{
		result = new_num_op(node->num);
		break;
	}

	case PUT_NODE:
	{
		emit(PUT, gencode(a), no_op, no_op, line);		
		break;
	}

	case GET_NODE:
	{
		result = temp();
		emit(GET, no_op, no_op, result, line);
		break;
	}

	case RETURN_NODE:
	{
		emit(RET, gencode(a), no_op, no_op, line);
		break;
	}

	case STMT_LIST_NODE:
	{
		node_t*		n;
		list_t*		p;
		list_t*		h;

		if (node->node_list == NULL)
			break;

		p = h = node->node_list;
		do {
			n = p->data;
			gencode(n);
			p = p->succ;
		} while (p != h);
		
		break;
	}

	case SUB_NODE:
	{
		result = temp();
		emit(SUB, gencode(a), gencode(b), result, line);
		break;
	}

	case WHILE_NODE:
	{
		op_t	start;
		op_t	continue_label;	/* target of continue statement. */
		op_t	break_label;	/* target of break statement. */
		op_t	cond;

		start = new_label();
		continue_label = new_label();
		break_label = new_label();

		emit(BA, no_op, no_op, continue_label, line);

		emit(LABEL, start, no_op, no_op, line);
		gencode(b);
		emit(BA, no_op, no_op, continue_label, line);

		emit(LABEL, continue_label, no_op, no_op, line);
		cond = gencode(a);
		emit(BT, cond, no_op, start, line);
		emit(BA, no_op, no_op, break_label, line);
		emit(LABEL, break_label, no_op, no_op, line);

		break;
	}

	case LABEL_NODE:
	{
		emit(LABEL, lookup_label(node->id), no_op, no_op, line);
		gencode(a);
		break;
	}

	case GOTO_NODE:
	{
		emit(BA, no_op, no_op, lookup_label(node->id), line);
		break;	
	}

	default:
		fatal(node->type);
	}

	return result;
}
