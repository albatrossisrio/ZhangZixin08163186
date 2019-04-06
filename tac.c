#include "parser.h"
#include <string.h>
#include<stdio.h>


typedef struct addr  //数值 或 局部变量 或 中间变量 或 类型 或 空         
{
	char kind[20];
	char name[20];
}addr;

typedef struct fourvarcode  //(op ,addr1 ,addr2 ,addr3 ,)           
{
	int op;
	struct addr addr1;
	struct addr addr2;
	struct addr addr3;
	struct fourvarcode *next;
}fourvarcode;
typedef struct symboltable
{
	char type[100];
	char name[100];
	int location;
	struct symboltable* next;
}symboltable;
extern int root;  //前面分析获得的根节点的结点位置
extern Node*  node; //parser.c的生成的结点数组
extern char * node_name[140];//结点名
extern struct Symbol*  symbol;//符号表
char assign_table[20][20];
void flocal_table(char type[],char name[],char num[],int n);
char *op_string(int op);
static void start_tac(int n);
static char *deal_expk(int n);  
static void MAIN_K(int n);      
static void DEFINEPARA_K(int n); 
static void ASSIGN_K(int n);
static void get_tac(int op,char a[],char b[],char c[]); 
static char * newtemp();   
fourvarcode *tac_temp;    
fourvarcode *tac_head;   
static int newtemp_no=0;    
static char adr[10]= {'\0'};
static char empty[10]= "\0";
void print_tac();
symboltable *lsptempg,*lsptempl;///用于构造符号表的临时变量
int AX_FLAG=0,BX_FLAG=0,CX_FLAG=0,DX_FLAG=0,SI_FLAG=0;///通用寄存器
char AX[5],BX[5],CX[5],DX[5],SI[5];
int num=0;
char Empty[]="\0";
int stackn=0;
symboltable *local_table;
static void build_asm(fourvarcode* t);
static void build_assign(fourvarcode* t);
static void build_define(fourvarcode* t);
static void build_muls(fourvarcode* t); ///乘
static void build_divs(fourvarcode* t);  ///除
static void build_adds(fourvarcode* t);
static void build_minu(fourvarcode* t);
static void registerfree(char b[10]);
static char* registerspare(int n);
static void print_optimize_tac();
static void optimer_tac();
static  
void build_mainfuns(fourvarcode* t);
static void build_mainfuns_end(fourvarcode* t);
int T[1005];//T[n]保存t#n所用的寄存器
char Tvalue[1005][5];
int assign_pos_T[1005];
fourvarcode* Pointer[1005];
int cnt_pointer=0;
FILE *freopen( const char *filename, const char *mode, FILE *stream );
// bool last_div=0;
// bool last_mul=0;
void  tac()
{
	for(int i=0;i<1000;i++)
	T[i]=0;
    tac_head=(fourvarcode*)malloc(sizeof(fourvarcode));
    tac_temp=tac_head;
    start_tac(root);
	print_tac();
}
 
void start_tac(int n)
{

    while(n!=0)
    {	
		char *start=node_name[node[n].id]; //结点名
        if(strcmp(start,"funcdecl_")==0) //函数结点
        {
            MAIN_K(n);
			break;
        }
        if(strcmp(start,"declarations_")==0) //声明
        {
            DEFINEPARA_K(n);
			n = node[n].next;
			continue;
        }
        if(strcmp(start,"statements_")==0)//表达式
        {
            ASSIGN_K(n);
			n = node[n].next;
			continue;
        }    
		n = node[n].child; //下一个结点
    }
}

void MAIN_K(int n)
{
    char a[10];
    a[0]='0';
    a[1]='\0';
    get_tac(6,adr,adr,adr); 
    start_tac(node[n].next);  
    get_tac(7,adr,adr,adr);
}
 
void DEFINEPARA_K(int n)
{
	char a[10];
	char b[10];
	n = node[n].child;//decl_init_
	while(n!=0)
	{
		int i=node[n].child;//decl_spec_
		char *d1=node_name[node[node[i].child].id];//type
		strcpy(a,d1); 
		i=node[i].next; //init_declarators_
		i=node[i].child; //declarator_		
		while(i!=0)
		{
			int j=node[i].child;//direct_decl_
			j=node[j].child; //ident
			j=node[j].child; //name		
			int sti = node[j].sti;
			char* d2= symbol[sti].name;
			strcpy(b,d2);
			get_tac(8,a,b,adr);		
			i=node[i].next;//next declarator_
		}
		n=node[n].next;//next decl_init_
	}	
}

void ASSIGN_K(int n)
{	
	char t1[10],t2[10];
	n = node[n].child;//exp_
	while(n!=0)
	{
		strcpy(t1,newtemp());
		int i=node[n].child;//assignment_
		i=node[i].child;//equals_
		i=node[i].child;//IDENT_
		strcpy(t2,deal_expk(node[i].next)); 
        get_tac(1,t2,t1,adr);		
		int sti = node[i].sti;
		char* q= symbol[sti].name;
		get_tac(1,t1,q,adr);		
		n=node[n].next;
	}
}
 
void get_tac(int op,char a[],char b[],char c[])
{
    fourvarcode* t=NULL;
    t=(fourvarcode*)malloc(sizeof(fourvarcode));
    t->op=op;
 
    if(a[0]=='\0')
    {
		strcpy(t->addr1.kind,"emptys");
        strcpy(t->addr1.name,"\0");
    }
    else if((a[0]>='a'&&a[0]<='z')||(a[0]>='A'&&a[0]<='Z'))
    {
        strcpy(t->addr2.kind,"strings");
        strcpy(t->addr1.name,a);
    }
    else
    {
        strcpy(t->addr2.kind,"consts");
        strcpy(t->addr1.name,a);
    }
 
 
    if(b[0]=='\0')
    {
		strcpy(t->addr2.kind,"emptys");
        strcpy(t->addr2.name,"\0");
    }
    else if((b[0]>='a'&&b[0]<='z')||(b[0]>='A'&&b[0]<='Z'))
    {
        strcpy(t->addr2.kind,"strings");
        strcpy(t->addr2.name,b);
    }
    else
    {
		strcpy(t->addr2.kind,"consts");
        strcpy(t->addr2.name,b);
    }
 
 
    if(c[0]=='\0')
    {
        strcpy(t->addr3.kind,"emptys");
        strcpy(t->addr3.name,"\0");
    }
    else if((c[0]>='a'&&c[0]<='z')||(c[0]>='A'&&c[0]<='Z'))
    {
        strcpy(t->addr3.kind,"strings");
        strcpy(t->addr3.name,c);
    }
    else
    {
        strcpy(t->addr3.kind,"consts");
        strcpy(t->addr3.name,c);
    }
 
    t->next=NULL;
    tac_temp->next=t;
    tac_temp=t;
}

char *newtemp()
{
    char s[10];
    sprintf(s,"t#%d",newtemp_no);
    newtemp_no++;
    return s;
}
 
char* deal_expk(int n)
{
	char empty[10];
    empty[0]='\0';	
	char *e=node_name[node[n].id];
	char t1[10],t2[10],t3[10];
    if(strcmp(e,"IDENT_")==0)
	{				
		int sti = node[n].sti;
		char* e1= symbol[sti].name;
		strcpy(t1,newtemp());
		get_tac(1,e1,t1,adr);
		return t1;
	}
	if(strcmp(e,"CONST_")==0)
	{
		int sti = node[n].sti;
		char* e1= symbol[sti].name;
		return e1;
	}
	if(strcmp(e,"add_")==0)
	{        	
		int i=node[n].child;
		int j=node[i].next;			
		strcpy(t1,deal_expk(i));		
		strcpy(t2,deal_expk(j));
		strcpy(t3,newtemp());	
        get_tac(3,t1,t2,t3);
        return t3;
	}
	if(strcmp(e,"sub_")==0)
	{
		int i=node[n].child;
		int j=node[i].next;			
		strcpy(t1,deal_expk(i));		
		strcpy(t2,deal_expk(j));
		strcpy(t3,newtemp());	
        get_tac(4,t1,t2,t3);
        return t3;
	}
	if(strcmp(e,"mul_")==0)
	{
		int i=node[n].child;
		int j=node[i].next;			
		strcpy(t1,deal_expk(i));		
		strcpy(t2,deal_expk(j));
		strcpy(t3,newtemp());	
        get_tac(2,t1,t2,t3);
        return t3;
	}
	if(strcmp(e,"div_")==0)
	{
		int i=node[n].child;
		int j=node[i].next;			
		strcpy(t1,deal_expk(i));		
		strcpy(t2,deal_expk(j));
		strcpy(t3,newtemp());	
        get_tac(5,t1,t2,t3);
        return t3;
	}
	if(strcmp(e,"exp_")==0)
	{
		n=node[n].child;//assignment_
		n=node[n].child;
		deal_expk(n);
	}
}
 
void print_tac()
{
	fourvarcode* t=tac_head->next;
	while(t!=NULL)
	{
	    printf("(");
		printf("%s ,",op_string(t->op));
		if(t->addr1.kind=="emptys")
			printf("_ ,");
		else
			printf("%s ,",t->addr1.name);
 
		if(t->addr2.kind=="emptys")
			printf("_ ,");
		else
			printf("%s ,",t->addr2.name);
 
		if(t->addr3.kind=="emptys")
			printf("_ ,");
		else
			printf("%s ,",t->addr3.name);
 
		t=t->next;
		printf(")");
		printf("\n");
	}
}

// void print_asm()
// {
// 	fourvarcode* t=tac_head->next;
// 		printf(".MODEL SMALL\n");
// 		printf(".386\n");
//   		printf(".STACK 100H\n");
//     	printf(".DATA\n");
//     	printf(".CODE\n");
//     	printf(".STARTUP\n");
// 		printf("push bp\n");
//     	printf("mov bp,sp\n");
//     	printf("jmp alloc\n");
//     	printf("main:\n");
// 		local_table=(symboltable *)malloc(sizeof(symboltable));
//    		lsptempl=local_table;
//     	local_table->next=NULL;
// 		fourvarcode* q=t->next;
// 		while(q->op!=7){
// 			if(q->op==8)
// 			build_asm(q);
// 			q=q->next;
// 		}
// 		t=t->next;
// 		while(t->op!=7){
// 			if(t->op!=8)
// 			{
// 				build_asm(t);
// 			}
// 			t=t->next;
// 		}
// 		build_asm(t);
// 		printf("jmp over\n");
// 		int i;
// 		printf("alloc:\n");
// 		for(i=num;i>=1;i--)
// 		{
// 			if(strcmp(Tvalue[assign_table[i][2]-'0'],Empty)==0)
// 			{
// 				printf("MOV AX,0\n");
// 				printf("PUSH AX\n");
// 			}
// 			else
// 			{
// 				printf("MOV AX,%s\n",Tvalue[assign_table[i][2]-'0']);
// 				printf("PUSH AX\n");
// 			}

			
// 		}
// 		printf("jmp main\n");
// 		printf("over:\n");
// 		printf(".exit\n");
// 		printf("end\n");
// 		/* code */
	
// }
// void build_asm(fourvarcode* t)
// {
// 	if(t->op==8)
// 	{
// 		build_define(t);
// 		return;
// 	}
// 	if(t->op==7)
// 	{
// 		return;
// 	}
// 	if(t->op==1)
// 	{
// 		build_assign(t);
// 	}
// 	if(t->op==3)
// 	{
// 		build_adds(t);
// 		return;
// 	}
// 	if(t->op==4)
// 	{
// 		build_minu(t);
// 		return;
// 	}
// 	if(t->op==5)
// 	{
// 		build_divs(t);
        
// 		return;
// 	}
// 	if(t->op==2)
// 	{
// 		build_muls(t);
// 		return;
// 	}
// }


// void build_define(fourvarcode* t) 
// {
//     flocal_table(t->addr1.name,t->addr2.name,t->addr3.name,num+1);
//     if(strcmp(t->addr3.name,Empty)==0)
//     {
//         num++;
//     }
// }

// void build_muls(fourvarcode* t) ///乘  x86中乘法的被乘数在AX里  结果在AX中
// {
//     char a3[10],axorbx[5];
//     strcpy(a3,t->addr3.name);
//     char tmp[5];
//     strcpy(tmp,registerspare(-1));
//     if(T[t->addr3.name[2]-'0']!=1)
//     printf("MOV AX,%s\n",t->addr3.name[2]-'0');
//     printf("MOV %s,%s\n",tmp,t->addr2.name);
//     if(CX_FLAG==1)//用到cx寄存器了
//     {
//         printf("MUL BX,CX\n");
//         strcpy(axorbx,"BX");
//     }
//     else
//     {
//         printf("MUL BX\n");
//         strcpy(axorbx,"AX");
//     }
//     if(a3[1]!='#')
//     {
//         int d=searchlocal(t->addr3.name);
//         if(d==-1)
//         {
//             printf("MOV [BP+%d],%s\n",d,axorbx);
//             printf("MOV BP,SP\n");
//         }
//         //当数在局部变量符号表里
//         else
//         {
//             printf("MOV [BP+%d],%s\n",d*2,axorbx);
//         }
 
//         if(strcmp(axorbx,"AX")==0)
//         {
//             registerfree("AX");
//             registerfree("BX");
//         }
//         else
//         {
//             registerfree("BX");
//             registerfree("CX");
//         }
//     }
//     //结果仍然留在AX 中
//     else
//     {
//         if(strcmp(axorbx,"AX")==0)
//         {
//             printf("MOV %s,AX\n",registerspare(a3[2]-'0'));
//             registerfree("AX");
//             registerfree("BX");
//         }
//         else 
//         {
//             registerfree("CX");
//         }
//     }
    
// }

// void registerfree(char b[10])
// {
//     if(strcmp(b,"AX")==0||strcmp(b,"EAX")==0)
//     {
//         AX_FLAG=0;
//     }
//     if(strcmp(b,"BX")==0||strcmp(b,"EBX")==0)
//     {
//         BX_FLAG=0;
//     }
//     if(strcmp(b,"CX")==0||strcmp(b,"ECX")==0)
//     {
//         CX_FLAG=0;
//     }
 
// }
 
//  int searchlocal(char a[20])
// {
//     symboltable *t=local_table->next;
 
//     while(t!=NULL)
//     {
//         if(strcmp(t->name,a)==0)
//         {
//             return t->location;
//             break;
//         }
//         t=t->next;
//     }
//     return -1;
// }
void build_divs(fourvarcode* t)
{
    char a1[10],a2[10],a3[10];
    strcpy(a1,t->addr1.name);
    strcpy(a2,t->addr2.name);
    strcpy(a3,t->addr3.name);
    if(a1[1]=='#')
    {
        char *tt = &a1[2];
        if(T[(int)atof(tt)]!=1)
        printf("MOV AX,%s\n",registerspare(atof(tt)));
        AX_FLAG=1;
    }
    else if(a1[0]>='a'&&a1[0]<='z'||a1[0]>='A'&&a1[0]<='Z')
    {
        int d=searchlocal(a1);
         if(d==-1)
        {
            printf("MOV AX,[BP+%d]\n",d);
            printf("MOV BP,SP\n");
        }
        //当数在局部变量符号表里
        else
        {
            printf("MOV AX,[BP+%d]\n",d*2);
        }
        AX_FLAG=1;
    }
    else
    {
        printf("MOV AX,%s\n",a1);
        AX_FLAG=1;
    }
    if(a2[1]=='#')
    {
        
         char *tt = &a2[2];
         char *tmp="";
         strcpy(tmp,registerspare((int)atof(tt)));
        printf("DIV %s\n",tmp);
        registerfree(tmp);
    }
    else
    {
        char tmp[10]="";
        strcpy(tmp,registerspare(-1));
        printf("MOV %s,%s\n",tmp,a2);
        registerfree(tmp);
        printf("DIV %s\n",tmp);
    }
    if(a3[0]>='a'&&a3[0]<='z'&&a3[1]!='#'||a3[0]>='A'&&a3[0]<='Z'&&a3[1]!='#')
    {
        int d=searchlocal(a3);
         if(d==-1)
        {
            printf("MOV [BP+%d],AX\n",d);
            printf("MOV BP,SP\n");
        }
        //当数在局部变量符号表里
        else
        {
            printf("MOV [BP+%d],AX\n",d*2);
        }
        registerfree("AX");
    }
    else
    {
        char *tt = &a3[2];
        T[(int)atof(tt)]=1;
    }
}


// void build_divs(fourvarcode* t)  ///除
// {
//     char a3[10],axorbx[5];
//     strcpy(a3,t->addr3.name);
//     char tmp[5];
//     strcpy(tmp,registerspare(-1));
//     if(T[t->addr3.name[2]-'0']!=1)
//     printf("MOV AX,%s\n",t->addr3.name[2]-'0');
//     printf("MOV %s,%s\n",tmp,t->addr2.name);
//     if(CX_FLAG==1)//用到cx寄存器了
//     {
//         printf("DIV BX,CX\n");
//         strcpy(axorbx,"BX");
//     }
//     else
//     {
//         printf("DIV BX\n");
//         strcpy(axorbx,"AX");
//     }
//     if(a3[1]!='#')
//     {
//         int d=searchlocal(t->addr3.name);
//         if(d==-1)
//         {
//             printf("MOV [BP+%d],%s\n",d,axorbx);
//             printf("MOV BP,SP\n");
//         }
//         //当数在局部变量符号表里
//         else
//         {
 
//             printf("MOV [BP+%d],%s\n",d*2,axorbx);
//         }
 
//         if(strcmp(axorbx,"AX")==0)
//         {
//             registerfree("AX");
//             registerfree("BX");
//         }
//         else
//         {
//             registerfree("BX");
//             registerfree("CX");
//         }
//     }
//     //结果仍然留在AX 中
//     else
//     {
//         if(strcmp(axorbx,"AX")==0)
//         {
//             printf("MOV %s,AX\n",registerspare(a3[2]-'0'));
//             registerfree("AX");
//             registerfree("BX");
//         }
//         else 
//         {
//             registerfree("CX");
//         }
//     }
    
// }
 
 
 
// void build_adds(fourvarcode* t)
// {
//     char a2[10],a3[10],axorbx[5];
//     strcpy(a2,t->addr2.name);
//     strcpy(a3,t->addr3.name);
//     if(strcmp(a2,"1")!=0)//不是自增运算
//     {
//         if(CX_FLAG==1)//用到cx寄存器了
//         {
//             printf("ADD BX,CX\n");
//             strcpy(axorbx,"BX");
//         }
//         else
//         {
//             printf("ADD AX,BX\n");
//             strcpy(axorbx,"AX");
//         }
//         if(a3[1]!='#')///结果赋值给局部变量
//         {
//             int d=searchlocal(t->addr3.name);
//             if(d==-1)
//             {;
//                 printf("MOV [BP+%d],%s\n",d,axorbx);
//                 printf("MOV BP,SP\n");
//             }
//             ///当数在局部变量符号表里
//             else
//             {
 
//                 printf("MOV [BP+%d],%s\n",d*2,axorbx);
//             }
//             if(strcmp(axorbx,"AX")==0)
//             {
//                 registerfree("AX");
//                 registerfree("BX");
//             }
//             else
//             {
//                 registerfree("BX");
//                 registerfree("CX");
//             }
//         }
//         ///结果仍然留在AX 中
//         else
//         {
//             if(strcmp(axorbx,"AX")==0)
//             {
//                 registerfree("BX");
//             }
//             else
//             {
//                 registerfree("CX");
//             }
//         }
//     }
// }
 
 
 
// void build_minu(fourvarcode* t)
// {
//     char a2[10],a3[10],axorbx[5];
//     strcpy(a2,t->addr2.name);
//     strcpy(a3,t->addr3.name);
//     if(strcmp(a2,"1")!=0)
//     {
//         if(CX_FLAG==1)///用到cx寄存器了
//         {
//             printf("SUB BX,CX\n");
//             strcpy(axorbx,"BX");
//         }
//         else
//         {
//             printf("SUB AX,BX\n");
//             strcpy(axorbx,"AX");
//         }
//         if(a3[1]!='#')
//         {
//             int d;
//             //d=searchstack(t->addr3.name);
//             if(d>-1&&d<0)
//             {
//                 d=-(d+2);
//                 printf("MOV [BP+%d],%s\n",d,axorbx);
//                 printf("MOV BP,SP\n");
//             }
//             else
//             {
//                 printf("MOV [BP+%d],%s\n",d,axorbx);
//             }
//             if(strcmp(axorbx,"AX")==0)
//             {
//                 registerfree("AX");
//                 registerfree("BX");
//             }
//             else
//             {
//                 registerfree("BX");
//                 registerfree("CX");
//             }
//         }
//         else
//         {
//             if(strcmp(axorbx,"AX")==0)registerfree("BX");
//             else registerfree("CX");
//         }
//     }
 
// }


char *registerspare(int n)
{
    if(n==-1)
    {
        if(AX_FLAG==0)
    {
        AX_FLAG=1;
		T[n]=1;
        return "AX";
    }
    if(BX_FLAG==0)
    {
        BX_FLAG=1;
		T[n]=2;
        return "BX";
    }
 
    if(CX_FLAG==0)
    {
        CX_FLAG=1;
		T[n]=3;
        return "CX";
    }
    return "-1";
    }
	char tmp[5]="AX";
	if(T[n])
	{
		tmp[0]=tmp[0]+T[n]-1;
		return tmp;
	}
	
    if(AX_FLAG==0)
    {
        AX_FLAG=1;
		T[n]=1;
        return "AX";
    }
    if(BX_FLAG==0)
    {
        BX_FLAG=1;
		T[n]=2;
        return "BX";
    }
 
    if(CX_FLAG==0)
    {
        CX_FLAG=1;
		T[n]=3;
        return "CX";
    }
    return "-1";
}

// void flocal_table(char type[],char name[],char num[],int n)
// {
//     symboltable *t;
//     t = (symboltable *)malloc(sizeof(symboltable));
//     t->next = NULL;
//     strcpy(t->type, type);
//     strcpy(t->name, name);
//     t->location=n;
//     lsptempl->next=t;
//     lsptempl=t;
 
// }
// void build_assign(fourvarcode* t)
// {
//     char b[20],a1[20],a2[20];  ///a1 a2分别用来存储 赋值四元式的 值和变量名
//     strcpy(a1,t->addr1.name);
//     strcpy(a2,t->addr2.name);
//     if(a1[0]>='0'&&a1[0]<='9')///数字赋给局部变量或者中间变量
//     {
//         if(((a2[0]>='a'&&a2[0]<='z')||(a2[0]>='A'&&a2[0]<='Z'))&&a2[1]!='#')///局部变量 形如这样的四元式= ,1,a,___
//         {
//             ///找一下当前变量是否在局部变量表
//             if(searchlocal(t->addr2.name)!=(-1))
//             {
 
//                 int n=searchlocal(t->addr2.name);
//                 if(strcmp(assign_table[n],empty)==0)
//                 {
//                     strcpy(assign_table[n],t->addr1.name);
//                     printf("MOV AX,%s\n",assign_table[n]);
//                     printf("MOV [BP+%d],AX\n",n*2);
 
//                 }
//                 else  ///如果不是则为全局变量
//                 {
//                     printf("MOV AX,%s\n",t->addr1.name);
//                     printf("MOV [BP+%d],AX\n",n*2);
//                 }
//             }
//         }
//         else  ///if(a2[1]=='#'形如 =，1，t#1
//         {
// 			strcpy(Tvalue[a2[2]-'0'],t->addr1.name);
//             strcpy(b,registerspare(a2[2]-'0'));
//             printf("MOV %s,%s\n",b,a1);
//         }
//     }

//     else if(((a1[0]>='a'&&a1[0]<='z')||(a1[0]>='A'&&a1[0]<='Z'))&&a1[1]!='#')  ///形如这样的四元式 =,a,t#1,___ 主要翻译if while for (a<b)
//     {
//         ///中间变量寄存器的赋值
 
//         int c1=searchlocal(a1);
//         //if (a<b)中的a和b中间变量
 
//         strcpy(b, registerspare(a2[2]-'0'));
//         if (c1!=-1 )
//         {
//             printf("MOV %s,[BP+%d]\n", b, c1*2);
//         }
//         else
//         {
 
//         }
//     }
// 	else if(a1[0]=='t'&&a1[1]=='#'&&a2[1]!='#') //=,t#0,a
// 	{
// 		///找一下当前变量是否在局部变量表
// 		char tmp[5];
// 		strcpy(tmp,registerspare(a1[2]-'0'));
//             if(searchlocal(t->addr2.name)!=(-1))
//             {
 
//                 int n=searchlocal(t->addr2.name);
//                 if(strcmp(assign_table[n],empty)==0)
//                 {
//                     strcpy(assign_table[n],t->addr1.name);
//                     printf("MOV [BP+%d],%s\n",n*2,tmp);
 
//                 }
//                 else  ///如果不是则为全局变量
//                 {
//                     printf("MOV [BP+%d],%s\n",n*2,tmp);
//                 }
//             }
// 			registerfree(tmp);
// 	} 
//     else if(a1[0]=='t'&&a1[1]=='#'&&a2[1]=='#')
//     {
//         char tmp1[5];
//         char tmp2[5];
//         strcpy(tmp1,registerspare(a1[2]-'0'));
//         T[a2[2]-'0']=1;
//         printf("MOV %s,AX\n",tmp1);
//     }
// }

char *op_string(int op)
{
    switch (op)
    {
    case (1):
        return "=";  
    case (2):
        return "*";
    case (3):
        return "+";
    case (4):
        return "-";
	case (5):
        return "/";
    case (6):
        return "mainfun";
    case(7):
        return "mainfun_end";
    case(8):
        return "definepara";
    default:
        printf("匹配有误");
		return 0;
    }
}
void flocal_table(char type[],char name[],char num[],int n)
{
    symboltable *t;
    t = (symboltable *)malloc(sizeof(symboltable));
    t->next = NULL;
    strcpy(t->type, type);
    strcpy(t->name, name);
    t->location=n;
    lsptempl->next=t;
    lsptempl=t;
 
}
 
int searchlocal(char a[20])
{
    symboltable *t=local_table->next;
 
    while(t!=NULL)
    {
 
 
        if(strcmp(t->name,a)==0)
        {
            return t->location;
            break;
        }
        t=t->next;
    }
    return -1;
}
void registerfree(char b[10])
{
    if(strcmp(b,"AX")==0||strcmp(b,"EAX")==0)
    {
        AX_FLAG=0;
    }
    if(strcmp(b,"BX")==0||strcmp(b,"EBX")==0)
    {
        BX_FLAG=0;
    }
    if(strcmp(b,"CX")==0||strcmp(b,"ECX")==0)
    {
        CX_FLAG=0;
    }
 
}
void start_asm()
{
    printf(".MODEL SMALL\n");
    printf(".386\n");
    printf(".STACK 100H\n");
    printf(".DATA\n");
    printf(".CODE\n");
    printf("START:MOV AX,@data\n");
    printf("MOV DS,AX\n");
    local_table=(symboltable *)malloc(sizeof(symboltable));
    lsptempl=local_table;
    local_table->next=NULL;
 
    fourvarcode* t=tac_head->next;
 
    fourvarcode* q=t->next;
    while(q->op!=7)
    {
        if(q->op==8)
        {
            build_asm(q);
        }
        q=q->next;
    }

    build_asm(t); ///此时t是mainstart
    printf("push bp\n");
    printf("mov bp,sp\n");
    printf("jmp alloc\n");
    printf("main:\n");
    
    t=t->next; ///没有结束  建立其他的汇编
 
 
    while(t->op!=7)
    {
        if(t->op!=8)
        {
            build_asm(t);
        }
        t=t->next;
    }
    build_asm(t);
    printf("jmp over\n");
    int i;
    printf("alloc:\n");
    for(i=num; i>=1; i--)
    {
        if(strcmp(assign_table[i],empty)==0)
        {
            printf("MOV AX,0\n");
            printf("PUSH AX\n");
        }
        else ///有赋值
        {
            printf("MOV AX,%s\n",assign_table[i]);
            printf("PUSH AX\n");
        }
    }
    printf("jmp main\n");
    printf("over:\n");
    printf("MOV AX,4C00H\n");
    printf("INT 21H\n");
    printf("end\n");
 
}
 


/***********************************************************
* 功能:开始根据op来生成汇编代码
**********************************************************/
void build_asm(fourvarcode* t)
{
    if(t->op==1)
    {
        build_assign(t);
        return;
    }
    if(t->op==8)
    {
        build_define(t);
        return;
    }
    
    if(t->op==4)//-
    {
        build_minu(t);
        return ;
    }
    if(t->op==5)//÷
    {
        build_divs(t);
        return ;
    }
    if(t->op==3)//+
    {
        build_adds(t);
        return ;
    }
    if(t->op==2)//*
    {
        build_muls(t);
        return ;
    }
    if(t->op==6)
    {
        build_mainfuns(t);
        return ;
    }
    if(t->op==7)
    {
        build_mainfuns_end(t);
        return ;
    }
}
 
 
 
 
/***********************************************************
* 功能:用于申请寄存器 为0则可以用
**********************************************************/
// char *registerspare()
// {
//     if(AX_FLAG==0)
//     {
//         AX_FLAG=1;
//         return "AX";
//     }
//     if(BX_FLAG==0)
//     {
//         BX_FLAG=1;
//         return "BX";
//     }
 
//     if(CX_FLAG==0)
//     {
//         CX_FLAG=1;
//         return "CX";
//     }
//     return "-1";
// }
 
 
 
/***********************************************************
* 功能:
        具体建立汇编代码
**********************************************************/
 
void build_define(fourvarcode* t)  ///跟符号表有关了！！
{
    flocal_table(t->addr1.name,t->addr2.name,t->addr3.name,num+1);
    if(strcmp(t->addr3.name,empty)==0)////这一定不是数组定义了
    {
        num++;
    }
}
 
 
void build_assign(fourvarcode* t)
{
    char b[20],a1[20],a2[20];  ///a1 a2分别用来存储 赋值四元式的 值和变量名
    strcpy(a1,t->addr1.name);
    strcpy(a2,t->addr2.name);
    if(a1[0]>='0'&&a1[0]<='9')///数字赋给局部变量或者中间变量
    {
        if(((a2[0]>='a'&&a2[0]<='z')||(a2[0]>='A'&&a2[0]<='Z'))&&a2[1]!='#')///局部变量 形如这样的四元式= ,1,a,___
        {
            ///找一下当前变量是否在局部变量表
            if(searchlocal(t->addr2.name)!=(-1))
            {
                int n=searchlocal(t->addr2.name);
                char *tmpp="";
                strcpy(tmpp,registerspare(-1));
                strcpy(assign_table[n],t->addr1.name);
                printf("MOV %s,%s\n",tmpp,assign_table[n]);
                printf("MOV [BP+%d],%s\n",n*2,tmpp);
                registerfree(tmpp);

            }
        }
        else  ///if(a2[1]=='#'形如 =，1，t#1
        {
            char *tt = &a2[2];
            strcpy(b,registerspare((int)atof(tt)));
            printf("MOV %s,%s\n",b,a1);
        }
    }
 
    else if(((a1[0]>='a'&&a1[0]<='z')||(a1[0]>='A'&&a1[0]<='Z'))&&a1[1]!='#')  ///形如这样的四元式 =,a,t#1,___ 主要翻译if while for (a<b)
    {
        ///中间变量寄存器的赋值
 
        int c1=searchlocal(a1);
        //if (a<b)中的a和b中间变量
        char *tt = &a2[2];
        strcpy(b, registerspare((int)atof(tt)));
        if (c1!=-1 )
        {
            printf("MOV %s,[BP+%d]\n", b, c1*2);
        }
        else
        {
 
            //printf("MOV %s,[BP+%d]\n", b, c1*2);
        }
    }
}


 
void build_muls(fourvarcode* t) ///乘  x86中乘法的被乘数在AX里  结果在AX中
{
 char a1[10],a2[10],a3[10];
    strcpy(a1,t->addr1.name);
    strcpy(a2,t->addr2.name);
    strcpy(a3,t->addr3.name);
    if(a1[1]=='#')
    {
        char *tt = &a1[2];
        if(T[(int)atof(tt)]!=1)
        printf("MOV AX,%s\n",registerspare((int)atof(tt)));
        AX_FLAG=1;
    }
    else if(a1[0]>='a'&&a1[0]<='z'||a1[0]>='A'&&a1[0]<='Z')
    {
        int d=searchlocal(a1);
         if(d==-1)
        {
            printf("MOV AX,[BP+%d]\n",d);
            printf("MOV BP,SP\n");
        }
        //当数在局部变量符号表里
        else
        {
            printf("MOV AX,[BP+%d]\n",d*2);
        }
        AX_FLAG=1;
    }
    else
    {
        printf("MOV AX,%s\n",a1);
        AX_FLAG=1;
    }
    if(a2[1]=='#')
    {
         char *tt = &a2[2];
         char *tmp="";
         strcpy(tmp,registerspare((int)atof(tt)));
        printf("MUL %s\n",tmp);
        registerfree(tmp);
    }
    else
    {
        char tmp[10]="";
        strcpy(tmp,registerspare(-1));
        printf("MOV %s,%s\n",tmp,a2);
        registerfree(tmp);
        printf("MUL %s\n",tmp);
    }
    if(a3[0]>='a'&&a3[0]<='z'&&a3[1]!='#'||a3[0]>='A'&&a3[0]<='Z'&&a3[1]!='#')
    {
        int d=searchlocal(a3);
         if(d==-1)
        {
            printf("MOV [BP+%d],AX\n",d);
            printf("MOV BP,SP\n");
        }
        //当数在局部变量符号表里
        else
        {
            printf("MOV [BP+%d],AX\n",d*2);
        }
        registerfree("AX");
    }
    else
    {
         char *tt = &a3[2];
        T[(int)atof(tt)]=1;
    }
    
}
 
// void build_divs(fourvarcode* t)  ///除
// {
//     char a3[10],axorbx[5];
//     strcpy(a3,t->addr3.name);
//     if(CX_FLAG==1)//用到cx寄存器了
//     {
//         printf("DIV BX,CX\n");
//         strcpy(axorbx,"BX");
//     }
//     else
//     {
//         printf("DIV BX\n");
//         strcpy(axorbx,"AX");
//     }
//     if(a3[1]!='#')
//     {
//         int d=searchlocal(t->addr3.name);
//         if(d==-1)
//         {
//             printf("MOV [BP+%d],%s\n",d,axorbx);
//             printf("MOV BP,SP\n");
//         }
//         //当数在局部变量符号表里
//         else
//         {
 
//             printf("MOV [BP+%d],%s\n",d*2,axorbx);
//         }
 
//         if(strcmp(axorbx,"AX")==0)
//         {
//             registerfree("AX");
//             registerfree("BX");
//         }
//         else
//         {
//             registerfree("BX");
//             registerfree("CX");
//         }
//     }
//     //结果仍然留在AX 中
//     else
//     {
//         if(strcmp(axorbx,"AX")==0)registerfree("BX");
//         else registerfree("CX");
//     }
// }
 
 
 
void build_adds(fourvarcode* t)
{
    char a1[10],a2[10],a3[10],first[5],second[5];
    strcpy(a2,t->addr2.name);
    strcpy(a3,t->addr3.name);
    strcpy(a1,t->addr1.name);
    if(strcmp(a2,"1")!=0)//不是自增运算
    {
        if(a1[1]=='#')
        {
             char *tt = &a1[2];
            strcpy(first,registerspare(atof(tt)));
        }
        else if(a1[0]>='a'&&a1[0]<='z'||a1[0]>='A'&&a1[0]<='Z')
        {
            strcpy(first,registerspare(-1));
            int d=searchlocal(a1);
            printf("MOV %s,[BP+%d]",first,d);
        }
        else if(a1[0]>='0'&&a1[0]<='9')
        {
            strcpy(first,registerspare(-1));
            printf("MOV %s,%s",first,a1);
        }
        if(a2[1]=='#')
        {
             char *tt = &a2[2];
            strcpy(second,registerspare(atof(tt)));
        }
        else if(a2[0]>='a'&&a2[0]<='z'||a2[0]>='A'&&a2[0]<='Z')
        {
            strcpy(second,registerspare(-1));
            int d=searchlocal(a2);
            printf("MOV %s,[BP+%d]",second,d);
        }
        else if(a2[0]>='0'&&a2[0]<='9')
        {
            strcpy(second,a2);
        }
        printf("ADD %s,%s\n",first,second);
        if(a3[1]!='#')///结果赋值给局部变量
        {
            int d=searchlocal(t->addr3.name);
            if(d==-1)
            {;
                printf("MOV [BP+%d],%s\n",d,first);
                printf("MOV BP,SP\n");
            }
            ///当数在局部变量符号表里
            else
            {
                printf("MOV [BP+%d],%s\n",d*2,first);
            }
            registerfree(first);
            if(!(second[0]>='0'&&second[0]<='9'))
            {
                registerfree(second);
            }
        }
        ///结果仍然留在AX 中
        else
        {
            if(!(second[0]>='0'&&second[0]<='9'))
            {
                registerfree(second);
            }
            if(strcmp(first,"AX")==0)
            {
                 char *tt = &a3[2];
                 T[(int)atof(tt)]=1;
            }
            
            else if(strcmp(first,"BX")==0)
            {
                 char *tt = &a3[2];
                  T[(int)atof(tt)]=2;
            }
           
            else
            { char *tt = &a3[2];
                 T[(int)atof(tt)]=3;
            }
            
        }
    }
}
 
 
 
void build_minu(fourvarcode* t)
{
    
    char a1[10],a2[10],a3[10],first[5],second[5];
    strcpy(a2,t->addr2.name);
    strcpy(a3,t->addr3.name);
    strcpy(a1,t->addr1.name);
    if(strcmp(a2,"1")!=0)//不是自增运算
    {
        if(a1[1]=='#')
        {
             char *tt = &a1[2];
            strcpy(first,registerspare(atof(tt)));
        }
        else if(a1[0]>='a'&&a1[0]<='z'||a1[0]>='A'&&a1[0]<='Z')
        {
            strcpy(first,registerspare(-1));
            int d=searchlocal(a1);
            printf("MOV %s,[BP+%d]",first,d);
        }
        else if(a1[0]>='0'&&a1[0]<='9')
        {
            strcpy(first,registerspare(-1));
            printf("MOV %s,%s",first,a1);
        }
        if(a2[1]=='#')
        {
             char *tt = &a2[2];
            strcpy(second,registerspare(atof(tt)));
        }
        else if(a2[0]>='a'&&a2[0]<='z'||a2[0]>='A'&&a2[0]<='Z')
        {
            strcpy(second,registerspare(-1));
            int d=searchlocal(a2);
            printf("MOV %s,[BP+%d]",second,d);
        }
        else if(a2[0]>='0'&&a2[0]<='9')
        {
            strcpy(second,a2);
        }
        printf("SUB %s,%s\n",first,second);
        if(a3[1]!='#')///结果赋值给局部变量
        {
            int d=searchlocal(t->addr3.name);
            if(d==-1)
            {;
                printf("MOV [BP+%d],%s\n",d,first);
                printf("MOV BP,SP\n");
            }
            ///当数在局部变量符号表里
            else
            {
                printf("MOV [BP+%d],%s\n",d*2,first);
            }
            registerfree(first);
            if(!(second[0]>='0'&&second[0]<='9'))
            {
                registerfree(second);
            }
        }
        ///结果仍然留在AX 中
        else
        {
            if(!(second[0]>='0'&&second[0]<='9'))
            {
                registerfree(second);
            }
            if(strcmp(first,"AX")==0)
            {
                 char *tt = &a3[2];
                 T[(int)atof(tt)]=1;
            }
            
            else if(strcmp(first,"BX")==0)
            {
                 char *tt = &a3[2];
                 T[(int)atof(tt)]=2;
            }
            
            else
            {
                 char *tt = &a3[2];
                 T[(int)atof(tt)]=3;
            }
            
        }
    }
}
 
void build_mainfuns(fourvarcode* t)
{
    return;
}
 
void build_mainfuns_end(fourvarcode* t)
{
    return;
}


void start_optimize()
{
    optimer_tac();
    print_optimize_tac();
}
void optimer_tac()
{
    fourvarcode* t=tac_head->next;
    fourvarcode* p;
    fourvarcode* q;
    p=t->next;
    q=p->next;
    while(q!=NULL)
    {
        if(p->op==1)
        {
            if(q->op==1)
            {
                char a[20];
                strcpy(a,p->addr2.name);
                if(strcmp(p->addr2.name,q->addr1.name)==0&&a[0]=='t'&&a[1]=='#')
                {
                    strcpy(p->addr2.name,q->addr2.name);
                    p->next=q->next;
                    free(q);
                    q=p->next;
                }
                else
                {
                    t=t->next;
                    p=p->next;
                    q=q->next;
                }
            }
 
            else if(q->op!=1) ///p可能需要删掉  比如return 0 的多于
            {
                char a[10],b[20],c[20];
                strcpy(a,p->addr1.name);
                strcpy(b,p->addr2.name);
                strcpy(c,q->addr3.name);
                if(strcmp(p->addr2.name,q->addr1.name)==0&&b[0]=='t'&&b[1]=='#'&&(c[0]=='\0'||a[1]=='#'))
                {
                    strcpy(q->addr1.name,p->addr1.name);///将asn的值给下一句
                    t->next=p->next;
                    free(p);
                    p=t->next;
                    q=q->next;
                }
                else
                {
                    t=t->next;
                    p=p->next;
                    q=q->next;
                }
            }
        }
        else if(p->op!=1)  ///如果不是赋值语句，那么它的下一句是赋值语句的话，且有运算
        {
            if(q->op==1)
			{
				if(strcmp(p->addr3.kind,"emptys"))
				{
					char a[20];
				    strcpy(a,p->addr3.name);
					if(strcmp(p->addr3.name,q->addr1.name)==0&&a[0]=='t'&&a[1]=='#')
					{
						strcpy(p->addr3.name,q->addr2.name);///将赋值提前
						p->next=q->next;
						free(q);
						q=p->next;
					}
					else ///如果不是运算 --继续执行
					{
						t=t->next;
						p=p->next;
						q=q->next;
					}
				}
				else///如果不是运算 --继续遍历
				{
					t=t->next;
				    p=p->next;
					q=q->next;
				}
			}
			else  ///下一句也不是赋值语句，那么肯定继续搜索，没法简化
			{
				t=t->next;
				p=p->next;
				q=q->next;
			}
		}
 
    }
    t=tac_head->next;
    fourvarcode* last=tac_head;
    for(int i=0;i<1000;i++)
    Pointer[i]=NULL;
    while(t->op!=7){

        if(t->op==1)
        {
            if(t->addr1.name[1]!='#'&&t->addr2.name[1]=='#')
            {
                char *tmp=&t->addr2.name[2];
                Pointer[(int)atof(tmp)]=t;
                last->next=t->next;
                t=t->next;
            }
            else
            {
                last=t;
                t=t->next;
            }
            
        }
        else if(t->op!=6&&t->op!=7&&t->op!=8)
        {
            if(t->addr1.name[1]=='#')
            {
                 char *tmp=&t->addr1.name[2];
                 if(Pointer[(int)atof(tmp)]!=NULL)
                 {
                     last->next=Pointer[(int)atof(tmp)];
                     Pointer[(int)atof(tmp)]->next=t;
                     last=Pointer[(int)atof(tmp)];
                 }
            }
            if(t->addr2.name[1]=='#')
            {
                 char *tmp=&t->addr2.name[2];
                 if(Pointer[(int)atof(tmp)]!=NULL)
                 {
                     last->next=Pointer[(int)atof(tmp)];
                     Pointer[(int)atof(tmp)]->next=t;
                     last=Pointer[(int)atof(tmp)];
                 }
            }
            if(t->addr3.name[1]=='#')
            {
                 char *tmp=&t->addr3.name[2];
                 if(Pointer[(int)atof(tmp)]!=NULL)
                 {
                     last->next=Pointer[(int)atof(tmp)];
                     Pointer[(int)atof(tmp)]->next=t;
                     last=Pointer[(int)atof(tmp)];
                 }
            }
                last=t;
                t=t->next;
        }
        else
        {
            last=t;
            t=t->next;
        }
 
    }
    
}
///输出简化后的四元式
void print_optimize_tac()
{
	fourvarcode* t=tac_head->next;
	while(t!=NULL)
	{
	    if(t->op==7||t->op==6||t->op==8)
        {
            t=t->next;
        }
        else
        {
	    printf("(");
		printf("%s ,",op_string(t->op));
		if(!strcmp(t->addr1.kind,"emptys"))
			printf("_ ,");
		else
			printf("%s ,",t->addr1.name);
 
		if(!strcmp(t->addr2.kind,"emptys"))
			printf("_ ,");
		else
			printf("%s ,",t->addr2.name);
 
		if(!strcmp(t->addr3.kind,"emptys"))
			printf("_ ,");
		else
			printf("%s ,",t->addr3.name);
 
		t=t->next;
		printf(")");
		printf("\n");
        }
	}
}

