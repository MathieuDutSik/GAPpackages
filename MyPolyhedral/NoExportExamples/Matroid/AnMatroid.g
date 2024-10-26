SettingFixedDim:=function(n)
  local GRPinp, ListSets, ListPermGens, eGen, eList, eSet, fSet, GRP, EXT, V;
  GRPinp:=SymmetricGroup(n);
  ListSets:=Combinations([1..n],2);
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRPinp)
  do
    eList:=[];
    for eSet in ListSets
    do
      fSet:=OnSets(eSet, eGen);
      Add(eList, Position(ListSets, fSet));
    od;
    Add(ListPermGens, PermList(eList));
  od;
  GRP:=Group(ListPermGens);
  EXT:=[];
  for eSet in ListSets
  do
    V:=ListWithIdenticalEntries(n, 0);
    V[eSet[1]]:=1;
    V[eSet[2]]:=-1;
    Add(EXT, ShallowCopy(V));
  od;
  return rec(EXT:=EXT, GRP:=GRP);
end;

ListFullRes:=[];
for n in [3..8]
do
  TheSetti:=SettingFixedDim(n);
  FullRes:=Matroid_EnumerateCircuitIndependentSets(TheSetti.EXT, TheSetti.GRP);
  Add(ListFullRes, FullRes);
od;
