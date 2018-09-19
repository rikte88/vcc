#ifndef globals_h
#define globals_h

#include <stdio.h>

#include "op.h"
#include "func.h"
#include "sim.h"
#include "symtab.h"

extern bool		use_pr;
extern unsigned		line;
extern FILE*		yyin;
extern FILE*		output;		
extern FILE*		tracefp;	
extern FILE*		cfg_fp;
extern char*		source;
extern char*		stmt_string[];
extern int		yydebug;
extern char*		progname;

#endif
