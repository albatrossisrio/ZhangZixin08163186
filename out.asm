.MODEL SMALL
.386
.STACK 100H
.DATA
.CODE
START:MOV AX,@data
MOV DS,AX
push bp
mov bp,sp
jmp alloc
main:
MOV AX,12
MOV [BP+2],AX
MOV AX,13
MOV [BP+4],AX
MOV AX,[BP+2]
MOV BX,[BP+4]
ADD AX,BX
MOV BX,2
MUL BX
MOV BX,3
DIV BX
MOV [BP+6],AX
jmp over
alloc:
MOV AX,0
PUSH AX
MOV AX,13
PUSH AX
MOV AX,12
PUSH AX
jmp main
over:
MOV AX,4C00H
INT 21H
end
