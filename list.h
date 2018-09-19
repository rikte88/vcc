#ifndef ssa_list 
#define ssa_list

typedef struct list_t	list_t;

struct list_t {
	list_t*		succ;
	list_t*		pred;
	void*		data;
};

list_t*	new_list(void*);
void	free_list(list_t**);
void	apply(list_t*, void (*)(void*));
void	delete_list(list_t*);
void*	remove_first(list_t**);
void*	remove_last(list_t**);
void	insert_before(list_t**, void*);
void	insert_after(list_t**, void*);
void 	insert_first(list_t**, void*);
void 	insert_last(list_t**, void*);
size_t	length(list_t*);
void	print_list(list_t*);
void	remove_from_list(list_t** list, void* data);

#endif
