#ifndef ssa_util_h
#define ssa_util_h

void bp();			/* for setting a breakpoint. */
#ifdef PRDEBUG
void pr(char*, ...);		/* like printf when use_pr is true. */
#else
#define pr(a, ...)		
#endif
char* chext(char*, char*);	/* change extension chext("a.c", "x") = "a.x" */
char* strdup2(char*);		/* like strdup (nonportable): copy a string. */

#endif
