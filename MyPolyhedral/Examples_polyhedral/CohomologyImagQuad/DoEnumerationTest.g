Read("FctPaper.g");
case1:=rec(DoSL:=false, n:=2, d:=-4);
case2:=rec(DoSL:=false, n:=3, d:=-4);
ListCases:=[case1];

for eCase in ListCases
do
  TreatSingleCase(eCase);
od;
