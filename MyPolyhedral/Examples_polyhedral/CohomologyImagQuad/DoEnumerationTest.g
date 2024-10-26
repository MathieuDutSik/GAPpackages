Read("FctPaper.g");
ListCases:=[rec(DoSL:=false, n:=3, d:=-3)];

for eCase in ListCases
do
  TreatSingleCase(eCase);
od;
