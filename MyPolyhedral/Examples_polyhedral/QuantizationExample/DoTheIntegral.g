ListNames:=[];
Add(ListNames, "E6");
Add(ListNames, "E7");
Add(ListNames, "ER7");
Add(ListNames, "E8");
Add(ListNames, "Lambda9");

TheFile:="RESULT_QuantizationConstant";
RemoveFileIfExist(TheFile);
output:=OutputTextFile(TheFile, true);
for eName in ListNames
do
  eGram:=ClassicalSporadicLattices(eName);
  AppendTo(output, "name=", eName, "\n");
  AppendTo(output, "GramMat = \n");
  for eLine in eGram
  do
    AppendTo(output, POL_VectorString(eLine), "\n");
  od;
  ListFunc:=DelaunayComputationStandardFunctions(eGram);
  TheIntegral:=ListFunc.GetQuantization();
  AppendTo(output, "TheIntegral=", TheIntegral, "\n");
od;
