#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <stdlib.h>

#include "error.h"
#include "globals.h"

void bp()
{
	/* set a breakpoint in this function. */
}

int yywrap()
{
	return 1;
}

#ifdef PRDEBUG
void pr(char *fmt, ...)
{
	va_list         ap;

	if (use_pr) {
		va_start(ap, fmt);
		vfprintf(stdout, fmt, ap);
		va_end(ap);
		fflush(stdout);
	}
}
#endif

char* strdup2(char* s)
{
	char*	t;
	int	n;

	n = strlen(s) + 1;
	t = malloc(n);
	if (t == NULL)
		error(FATAL, "out of memory");
	memcpy(t, s, n);
	
	return t;
}
