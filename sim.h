#ifndef sim_h
#define sim_h

#include "instr.h"

struct sim_t {
	bool		trace;		/* Trace execution. */
	int		pc;		/* Program counter. */
	int*		reg;		/* Register file.*/
	int		nreg;		/* Number of registers.*/
	instr_t*	imem;		/* Instruction memory.*/
	int		imem_size;	/* Number of instructions.*/
	int*		dmem;		/* Data memory.*/
	int		dmem_size;	/* Data memory size in words.*/
	unsigned	max_cycles;	/* Max cycles to simulate. */
	unsigned	cycles;		/* Cycles simulated. */
	unsigned	load_stalls;	/* Stall cycles due to load. */
	int		loaded_reg;	/* Read from cache last cycle,*/
					/* if any, otherwise -1. */
	unsigned	nexec[NSTMT];	/* #times an instr type was executed. */
	unsigned	ncycle[NSTMT];	/* #cycles an instr type needed. */
};
	
void set_trace(bool t);
void init_sim(void);
void free_sim(void);
void set_dmem_size(int n);
void set_imem(instr_t* v, int n);
void set_max_cycles(unsigned n);
void set_regs(unsigned n);
void run(void);
void print_stats();

#endif
