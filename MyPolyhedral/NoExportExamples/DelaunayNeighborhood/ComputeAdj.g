TheGramMat:=IdentityMat(3);




ListFunc:=DelaunayComputationStandardFunctions(TheGramMat);

DelCO:=ListFunc.GetDelaunayDescription();

EXT:=DelCO[1].EXT;
LFC:=ListFunc.GetNeighborhood(EXT);
for i in [1..3]
do
  LFC.DoIncrement();
  LFC.PrintStatistics();
od;
