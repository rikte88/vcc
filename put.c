#include <stdio.h>

void put(int a)
{
#ifndef NO_OUTPUT
	printf("%d\n", a);
#endif
}
