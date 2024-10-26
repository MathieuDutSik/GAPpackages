GramMat:=ClassicalSporadicLattices("E6");

LFC:=DelaunayComputationStandardFunctions(GramMat);

n:=Length(GramMat);
eDen:=3;

for i in [1..10]
do
  eVert:=[];
  for i in [1..n]
  do
    eVal:=Random([0..eDen])/eDen;
    Add(eVert, eVal);
  od;
  #
  Print("i=", i, " eVert=", eVert, "\n");
  ListRec:=LFC.GetAllContainingCells(eVert);
  Print("   |ListRec|=", Length(ListRec), "\n");
od;
