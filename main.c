
#include "main.h"


extern int yyparse();

extern FILE *yyin;

extern char * term_symb[];

extern void init_parser(int, int);
extern void   printast		();
extern int   init_out_file (char* fn);
extern void  term_out_file (char * );


void  main (int na, char *arg[])
{
	char *filename = "test.c";
	char * outfilename = "out.txt";

	//ָ���ļ�
	if(!(yyin = fopen(filename,"r"))) {
		printf("the file not exist\n");
		exit(0);
	}
	//��ʼ��
	init_parser(100, 1000);
	printf("\n");
	if(yyparse())exit(1);
    tac();
	start_optimize();
	init_out_file(outfilename);

	print_symtab (term_symb);  // Print the symbol table contents.

	printast();	   // Print the AST, if ast option indicates.
	term_out_file(outfilename);
	//print the asm code to the files.Without this sentence,then it will print to dos.
	freopen ("E:\\MASM\\out.txt", "w", stdout);
	start_asm();

	return ;

}


void  quit ()
{
		#ifdef WAIT_ON_KEY
   // Wait until key is pressed ...
	  	printf( "Press any key to continue ...\n");
	  	while( !_kbhit() );
		#endif
		exit (0);
}

















