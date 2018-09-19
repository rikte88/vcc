#include <errno.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>

#include "error.h"
#include "globals.h"
#include "util.h"

void error(error_type_t num, char* fmt, ...)
{
	va_list		ap;
	bool		proceed;
	bool		syserr;

	proceed = true;
	syserr = false;

	fprintf(stderr, "%s: ", progname);

	switch(num) {
	case SYNTAX:
		fprintf(stderr, "syntax error: %s line %u\n", source, line);
		proceed = false;
		break;

	case PROCEED:
		fprintf(stderr, "error: ");
		break;

	case SYSERR:
		fprintf(stderr, "error: ");
		syserr = true;
		proceed = false;
		break;

	case FATAL:
		fprintf(stderr, "fatal error: ");
		proceed = false;
		break;

	default:
		fprintf(stderr, "unknown error code: %d\n", num);
		proceed = false;
	}

	va_start(ap, fmt);
	vfprintf(stderr, fmt, ap);
	fprintf(stderr, "\n");

	if (syserr)
		perror(NULL);
	
	if (!proceed)
		exit(1);
}

void warning(char* fmt, ...)
{
	va_list		ap;

	fprintf(stderr, "%s: warning: ", progname);
	va_start(ap, fmt);
	vfprintf(stderr, fmt, ap);
	fprintf(stderr, "\n");
}
