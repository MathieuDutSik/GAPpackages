Read("FctPaper.g");
case1:=rec(DoSL:=false, n:=2, d:=-3);
case2:=rec(DoSL:=false, n:=3, d:=-4);
case3:=rec(DoSL:=false, n:=3, d:=-7);
case4:=rec(DoSL:=false, n:=3, d:=-15);
ListCases:=[case4];

for eCase in ListCases
do
  TreatSingleCase(eCase);
od;
