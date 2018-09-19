%{ 

#include "assert.h"
#include "op.h"
#include "globals.h"
#include "list.h"
#include "node.h"
#include "y.tab.h"
#include "util.h"

#define YY_NO_INPUT

extern int fileno(FILE*);

static void yyunput (int c,char *buf_ptr  );

void dummy_to_silence_gcc_warning()
{
	yyunput(0, NULL);
}

%}

ws		(\t|" ")+
digit		[0-9]
num		{digit}+
letter		[_a-zA-Z]
special		$
comment		"//"
id		({letter}({special}|{letter}|{digit})*)

%%

\n		{
			line += 1;
		}
{ws}		;
{comment}.*\n	line += 1;

else		return ELSE;
if		return IF;
int		return INT;
get		return GET_TOKEN;
put		return PUT_TOKEN;
return		return RETURN;
while		return WHILE;
goto		return GOTO;

"<="		return LE;
">="		return GE;
"=="		return EQ;
"!="		return NE;

__LINE__	{
			/* Provide the ANSI C __LINE__ macro which is
			 * replaced by the current source code line number.
			 *
			 * this is not how macro-expansion should be done,
			 * but we keep this as simple as possible...
			 *
			 */

			yylval.num = line;
			return NUM;
		}

{id}		{
			yylval.string = strdup2(yytext);
			return ID;
		}

{num}		{
			sscanf(yytext, "%d", &yylval.num);
			return NUM;
		}

.		{
			return *yytext; 
		}

%%
