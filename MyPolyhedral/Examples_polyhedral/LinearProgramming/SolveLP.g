eRec:=ReadAsFunction("DATA_LP")();

ListIneq:=eRec.ListIneq;
ToBeMinimized:=eRec.ToBeMinimized;




TheSol:=LPSOLVE_LinearProgramming(ListIneq, ToBeMinimized);


