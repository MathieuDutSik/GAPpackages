# x>= 0
# y>= 0
# x+y <= -1
# minimize x+y

ListIneq:=[
[0,1,0],
[0,0,1],
[-1,-1,-1]];

ToBeMinimized:=[0,1,1];
StrType:="rational";
TheReply:=GLPK_LinearProgramming_General(ListIneq, ToBeMinimized, StrType);
