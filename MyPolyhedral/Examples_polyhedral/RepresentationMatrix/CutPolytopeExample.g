GetCutPolytope:=function(n)
  local LSET, EXT, eSet, H, V, eGen, i, j, LVECT, eVect, eList, GetPosition, ListPermGens, eVect2, PermGRP;
  LSET:=Combinations([1..n-1]);
  #
  EXT:=[];
  for eSet in LSET
  do
    V:=[1];
    for i in [1..n-1]
    do
      for j in [i+1..n]
      do
        H:=Intersection(eSet, [i,j]);
        if Length(H)=1 then
          Add(V, 1);
        else
          Add(V, 0);
        fi;
      od;
    od;
    Add(EXT, V);
  od;
  #
  LVECT:=[];
  for eSet in LSET
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect{eSet}:=ListWithIdenticalEntries(Length(eSet), 1);
    Add(LVECT, eVect);
  od;
  GetPosition:=function(eVect)
    local pos, eVect2;
    pos:=Position(LVECT, eVect);
    if pos<>fail then
      return pos;
    fi;
    eVect2:=ListWithIdenticalEntries(n, 1)-eVect;
    pos:=Position(LVECT, eVect2);
    if pos=fail then
      Print("Something is wrong somewhere\n");
      Print(NullMat(5));
    fi;
    return pos;
  end;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(SymmetricGroup([1..n]))
  do
    eList:=[];
    for eVect in LVECT
    do
      Add(eList, GetPosition(Permuted(eVect, eGen)));
    od;
    Add(ListPermGens, PermList(eList));
  od;
  eList:=[];
  for eVect in LVECT
  do
    eVect2:=ShallowCopy(eVect);
    eVect2[1]:=1-eVect2[1];
    Add(eList, GetPosition(eVect2));
  od;
  Add(ListPermGens, PermList(eList));
  PermGRP:=Group(ListPermGens);
  return rec(EXT:=EXT, PermGRP:=PermGRP);
end;


n:=7;

TheInfo:=GetCutPolytope(n);
PolyInfo:=RepresentationMatrixAndFacetStandard(TheInfo.EXT, TheInfo.PermGRP);
