Read("FctPaper.g");
case1:=rec(DoSL:=false, n:=2, d:=-3);
case2:=rec(DoSL:=false, n:=3, d:=-3);
ListCases:=[case1];

for eCase in ListCases
do
  TreatSingleCase(eCase);
od;
