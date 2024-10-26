# 2y >= x-1
# y <= 2 + 2x
# minimize x+y

ListIneq:=[
[2,2,-1],
[1,-1,2]];

ToBeMinimized:=[0,1,1];
StrType:="rational";
TheReply:=GLPK_LinearProgramming_General(ListIneq, ToBeMinimized, StrType);
