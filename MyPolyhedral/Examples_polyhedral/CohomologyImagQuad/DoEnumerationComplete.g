Read("FctPaper.g");
#Resulting files are in subdirectory Result
ListCases:=[];
#
for d in [-3, -4, -7, -8, -11, -15, -19, -20, -23, -24]
do
  Add(ListCases, rec(DoSL:=false, n:=3, d:=d));
od;
#
for d in [-3, -4]
do
  Add(ListCases, rec(DoSL:=false, n:=4, d:=d));
od;

for eCase in ListCases
do
  TreatSingleCase(eCase);
od;
