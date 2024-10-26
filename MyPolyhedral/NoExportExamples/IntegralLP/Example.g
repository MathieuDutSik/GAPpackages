ListIneq:=[
   [-5/4,1,0],
   [-1,0,1]];

ToBeMinimized:=[0,1,1];
ListIneqInt:=List(ListIneq, RemoveFraction);
eSol:=GLPK_IntegerLinearProgramming(ListIneqInt, ToBeMinimized);
