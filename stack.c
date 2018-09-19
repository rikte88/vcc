#include <stdbool.h>
#include <stdlib.h>

#include "stack.h"

stack_t* new_stack(void)
{
	return calloc(1, sizeof(stack_t));
}

void free_stack(stack_t** stack)
{
	stack_t*	s;
	stack_t*	t;

	s = *stack;
	*stack = NULL;
	while (s != NULL) {
		t = s->next;
		free(s);
		s = t;
	}
}

void push(stack_t* stack, void* d)
{
	stack_t		*s;

	s = new_stack();
	s->data = d;
	s->next = stack->next;
	stack->next = s;
}

void* pop(stack_t* stack)
{
	stack_t*	s;
	void*		d;

	s = stack->next;
	d = s->data;

	stack->next = stack->next->next;
	free(s);
	return d;
}

void* top(stack_t* stack)
{	
	return stack->next->data;
}

bool empty(stack_t* stack)
{
	return stack->next == NULL;
}
