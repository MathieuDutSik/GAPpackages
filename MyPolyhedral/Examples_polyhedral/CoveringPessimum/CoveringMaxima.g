#TheGramMat:=ClassicalSporadicLattices("ER7");
#TheGramMat:=ClassicalSporadicLattices("E8");
#TheGramMat:=ClassicalSporadicLattices("Lambda9");
#TheGramMat:=RemoveFractionMatrix(Inverse(ClassicalSporadicLattices("Lambda9")));
#TheGramMat:=LatticeDnPlus(10);
#TheGramMat:=FuncFormAnr(11,4);
TheGramMat:=ClassicalSporadicLattices("K12");

DualPair:=function(eName)
  local TheList, TheGramMat, test, DualGramMat, DualName;
  Print("Inserting lattice ", eName, "\n");
  TheList:=[];
  TheGramMat:=ClassicalSporadicLattices(eName);
  Add(TheList, rec(eName:=eName, GramMat:=TheGramMat));
  test:=IsSelfDualLattice(TheGramMat);
  if test=false then
    DualGramMat:=RemoveFractionMatrix(Inverse(TheGramMat));
    DualName:=Concatenation("Dual_", eName);
    Add(TheList, rec(eName:=DualName, GramMat:=DualGramMat));
  fi;
  return TheList;
end;

ListCases:=[];
Append(ListCases, DualPair("E6"));
Append(ListCases, DualPair("E7"));
Append(ListCases, DualPair("ER7"));
Append(ListCases, DualPair("E8"));
Append(ListCases, DualPair("Lambda9"));
Append(ListCases, DualPair("Lambda10"));
Append(ListCases, DualPair("O10"));
Append(ListCases, DualPair("K12"));
Append(ListCases, DualPair("BW16"));
Append(ListCases, DualPair("Kappa7"));
Append(ListCases, DualPair("Kappa8"));
Append(ListCases, DualPair("Kappa9"));
Append(ListCases, DualPair("Kappa10"));
Append(ListCases, DualPair("Kappa11"));
Append(ListCases, DualPair("Lambda11max"));
Append(ListCases, DualPair("Lambda11min"));
Append(ListCases, DualPair("Lambda12max"));
Append(ListCases, DualPair("Lambda12mid"));
Append(ListCases, DualPair("Lambda12min"));
Append(ListCases, DualPair("Lambda13max"));
Append(ListCases, DualPair("Lambda13mid"));
Append(ListCases, DualPair("Lambda13min"));


TheFile:="CoveringStatus";
output:=OutputTextFile(TheFile, true);
for eCase in ListCases
do
  AppendTo(output, "Lattice name=", eCase.eName, "\n");
  n:=Length(eCase.GramMat);
  LFC:=DelaunayComputationStandardFunctions(eCase.GramMat);
  TestPessimum:=LFC.TestCoveringPessimum();
  TestMaxima:=LFC.TestCoveringMaximality();
  AppendTo(output, "TestPessimum=", TestPessimum, "  TestMaxima=", TestMaxima, "\n");
  AppendTo(output, "\n");
od;
CloseStream(output);
