#ifndef ssa_stack_h
#define ssa_stack_h

typedef struct stack_t stack_t;

struct stack_t {
	stack_t*	next;
	void*		data;
};

stack_t*		new_stack(void);
void			free_stack(stack_t**);

void			clear_stack(stack_t*);
void			put(stack_t*, void*);
void			push(stack_t*, void*);
void*			pop(stack_t*);
void*			top(stack_t*);
void			set_top(stack_t*, void*);
void*			bottom(stack_t*);
unsigned		height(stack_t*);

#endif
