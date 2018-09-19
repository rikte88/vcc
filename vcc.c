#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "util.h"
#include "op.h"
#include "globals.h"
#include "error.h"
#include "func.h"
#include "util.h"
#include "sym.h"

char*		progname;
FILE*		cfg_fp;

static void usage()
{
	fprintf(stderr, "-g <file>       read control flow graph from file\n");

	fprintf(stderr, "-q              quite; print application output to "
		"the file \"out\"\n");

	fprintf(stderr, "-t              dump execution of application to the "
		"file \"trace\"\n");

	fprintf(stderr, "-y              dump parser actions\n");

	exit(1);
}

static void params(int ac, char** av)
{
	char*		s;

	while (++av, --ac > 0) {

		if (av[0][0] == '-' && isalpha((int)av[0][1]) && !av[0][2]) {

			switch (av[0][1]) {
			case 'g':
				cfg_fp = fopen(av[1], "r");
				if (cfg_fp == NULL)
					error(SYSERR, "can't find cfg file");

			case 'q':
				output = fopen("out", "w");
				assert(output != NULL);
				break;

			case 't':
				set_trace(true);
				tracefp = fopen("trace", "w");
				assert(tracefp != NULL);
				break;

			case 'y':
				yydebug = true;
				break;

			default: 
				goto fail;
			}

		} else if (av[0][0] == '-' && isalpha((int)av[0][1])) {

			switch (av[0][1]) {
			/* for parameters such as -O2 which we don't use for now
			 *
			 */

			default:
			fail:
				warning("unrecognised option: %s", av[0]);
				usage();
			}

		} else {
			s = av[0];

			if ((yyin = fopen(s, "r")) == NULL)
				error(SYSERR, "cannot open %s for reading", s);

			source	= s;
			line	= 1;
		}
	}
}

int main(int ac, char** av)
{
	instr_t*	imem;
	int		imem_size;
	int		yyparse();
	int		yylex_destroy();

	progname = av[0];
	output = stdout;

	init_func();
	init_instr();
	init_stmt();
	init_sim();

	params(ac, av);

	if (yyin == NULL) {
		warning("no input file");
		exit(0);	
	}
		
	if (cfg_fp == NULL)
		yyparse();
	
	fclose(yyin);
	yylex_destroy();

	opt();

	if (cfg_fp != NULL)
		exit(0);

	imem = stmt2instr(&imem_size);

	free_func();
	deinit_symtab();
	deinit_sym();

	set_dmem_size(100000);
	set_imem(imem, imem_size);
	set_regs(32);

	run(); 

	print_stats();
		
	free_sim();

	if (output != NULL)
		fclose(output);

	if (yyin != NULL)
		fclose(yyin);

	return 0;
}
