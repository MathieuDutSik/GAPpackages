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
Append(ListCases, DualPair("Kappa7"));
Append(ListCases, DualPair("Kappa8"));
#Append(ListCases, DualPair("Kappa8.2"));
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
Append(ListCases, DualPair("Lambda16"));

ListSymbol:=[];
for eCase in ListCases
do
  FileSave:=Concatenation("DATA/LattInfo_", eCase.eName);
  SHV:=ShortestVectorDutourVersion(eCase.GramMat);
  if RankMat(SHV)=Length(eCase.GramMat) then
    if IsExistingFilePlusTouch(FileSave)=false then
      LFC:=DelaunayComputationStandardFunctions(eCase.GramMat);
      ListRadiuses:=LFC.GetListRadiuses();
      MaxRad:=Maximum(ListRadiuses);
      eMin:=SHV[1]*eCase.GramMat*SHV[1];
      TheSymbol:=rec(name:=eCase.eName, n:=Length(eCase.GramMat), MaxRad:=MaxRad, det:=DeterminantMat(eCase.GramMat), min:=eMin);
      SaveDataToFilePlusTouch(FileSave, TheSymbol);
    else
      TheSymbol:=ReadAsFunction(FileSave)();
    fi;
    Add(ListSymbol, TheSymbol);
  fi;
od;
