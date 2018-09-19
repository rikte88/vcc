#ifndef symtab_h
#define symtab_h

#include "op.h"

void init_symtab(void);
void deinit_symtab(void);
op_t lookup(char*);
op_t lookup_label(char*);
int install(char*, int);

#endif
