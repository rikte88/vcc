#ifndef ssa_set_h
#define ssa_set_h

#include <stddef.h>

typedef struct set_t set_t;

/* An empty set is represented by NULL. */

void free_set(set_t**);

void* set_to_array(set_t *, size_t* n);

void* find(set_t*, void*, int (*)(void*, void*));
void add(set_t**, void*, int (*)(void*, void*));
void join_set(set_t**, void*);
void* leave_set(set_t**);

void print_set(set_t*, void (*)(void*, FILE*), FILE*);

#endif
