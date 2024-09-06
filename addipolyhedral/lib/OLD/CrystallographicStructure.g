__FuncSpecialCharacteristicSet:=function(ListVertices)
  local eRet, i, eW, j;
  nM1:=Length(ListVertices[1]);
  eRet:=[];
  for i in [1..Length(ListVertices)]
  do
    eW:=[];
    for j in [1..Length(ListVertices)]
    do
      if i<>j then
        eS:=ListVertices[i]-ListVertices[j];
        Add(eW, eS{[2..nM1]});
      fi;
    od;
    Add(eRet, Set(eW);
  od;
  return Set(eRet);
end;

__CharacteristicDistMat:=function(ListVertices, GramMat)
  local nbVect, DistMat, iVert, jVert, TheVect, eDiff, result;
  nbVect:=Length(ListVertices);
  DistMat:=NullMat(nbVect, nbVect);
  for iVert in [1..nbVect-1]
  do
    for jVert in [iVert+1..nbVect]
    do
      TheVect:=ListVertices[iVert]-ListVertices[jVert];
      eDiff:=TheVect{[2..n+1]};
      result:=CVPVallentinProgram(GramMat, eDiff);
      DistMat[iVect][jVect]:=result.TheNorm;
    od;
  od;
  return DistMat;
end;



#
# the structure should be irreducible
AutomorphismGroupLatticeCrystallographicStructure:=function(ListVertices, GramMat)
  local GRPinf;
  n:=Length(GramMat);
  GRPinf:=MatrixAutomorphismGroupGramMatrix(GramMat);
  LattGRP:=Group(GRPinf.ListMat);
  DistMat:=__CharacteristicDistMat(ListVertices, GramMat);
  GRP:=AutomorphismGroupEdgeColoredGraph(DistMat);
  CharSetSet:=__FuncSpecialCharacteristicSet(ListVertices);
  TheStab:=Stabilizer(LattGRP, CharSetSet, OnSetsSets);
  # NEED TO WRITE CODE FOR THE RECOVERING OF DATA
end;


IsLattice:=function(ListVertices)
  local i, ListVect, i, j, eDiff, eSum;
  n:=Length(ListVertices[1])-1;
  ListVect:=[];
  for i in [2..Length(ListVertices)]
  do
    eDiff:=ListVertices[i]-ListVertices[1];
    Add(ListVect, FractionMod1(eDiff{[2..n+1]}));
  od;
  for i in [1..Length(ListVect)]
  do
    for j in [1..Length(ListVect)]
    do
      eSum:=FractionMod1(ListVect[i]+ListVect[j]);
      if Position(ListVect, eSum)=fail then
        return false;
      fi;
    od;
  od;
  return true;
end;

# an irreducible structure is one for which the group of translation
# preserving it is exactly Zn
IsIrreducibleCrystallographicStructure:=function(ListVert)
  local LVred, ListVect, i, j;
  LVred:=List(ListVert, x->FractionMod1(x));
  ListVect:=[];
  for i in [1..Length(ListVert)-1]
  do
    for j in [1..Length(ListVert)]
    do
      eDiff:=ListVert[j]-ListVert[i];
      Add(ListVect, 
    od;
  od;

end;
