OPT		= -O3
OPT		= -g

BENCH		= a
CC		= gcc
YACC		= bison
LEX		= flex
YFLAGS		= -d -y
OUT		= vcc
CFLAGS		= $(OPT) -Wall -pedantic -DYYSTACK_USE_ALLOC -D_ANSI_SOURCE \
			-DYYDEBUG -std=c99 -DPRDEBUG

OBJS		= globals.o c.o lex.o vcc.o symtab.o stmt.o error.o util.o\
		func.o sym.o op.o node.o sim.o instr.o cfg.o dom.o ssa.o vcg.o\
		alloc.o list.o set.o stack.o const_op.o

main: $(OUT)
	make test

$(OUT): $(OBJS)
	$(CC) -o $(OUT) $(OBJS) $(CFLAGS) $(LDFLAGS)

clean:
	rm -f gmon.out *.ps *.pdf *.o *.c:* *.dot lex.c c.c vcc a.out trace \
		out correct stats

c.o: c.c
	$(CC) -DYYDEBUG $(CFLAGS) -c c.c

$(BENCH).o: $(BENCH).c
	gcc -c $(BENCH).c

get.o: get.c
	gcc -c get.c

put.o: put.c
	gcc -c put.c

test: $(OUT)
	rm -f out correct $(BENCH).c:*
	gcc -O3 -g $(BENCH).c put.c get.c 
	./a.out < in > correct
	time ./vcc -q $(BENCH).c < in
	diff out correct | head

lex.c: lex.l

vg: $(OUT)
	valgrind --leak-check=full --track-origins=yes vcc -q $(BENCH).c < in
