#ifndef ac_error_h
#define ac_error_h

#include <stdio.h>
#include <stdlib.h>
#include "globals.h"

#define fatal(expr)                                                          \
        fprintf(stderr, "%s: compiler error in file %s line %d: %s = %d\n",  \
		progname, __FILE__, __LINE__, #expr, expr), abort()

typedef enum { 
	SYSERR,			/* System error which sets errno. */
	PROCEED,		/* Recoverable error. */
	FATAL,			/* Irrecoverable error. */
	SYNTAX			/* Syntax error. */
} error_type_t;

void error(error_type_t, char*, ...);
void warning(char*, ...);

#endif
