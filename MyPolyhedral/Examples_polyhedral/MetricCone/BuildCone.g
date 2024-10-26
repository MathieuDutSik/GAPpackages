GetCone:=function(n)
  local GRP, ListChar, eSet, i, GetElementImage, ListNewPermGens, eGen, eList, H, GetVector, FAC, fSet, GRPret;
  GRP:=SymmetricGroup(n);
  ListChar:=[];
  for eSet in Combinations([1..n],3)
  do
    for i in eSet
    do
      fSet:=Difference(eSet, [i]);
      Add(ListChar, [i, fSet]);
    od;
  od;
  GetElementImage:=function(eChar, g)
    return [OnPoints(eChar[1], g), OnSets(eChar[2], g)];
  end;
  ListNewPermGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=List(ListChar, x->Position(ListChar, GetElementImage(x, eGen)));
    Add(ListNewPermGens, PermList(eList));
  od;
  H:=Combinations([1..n], 2);
  GetVector:=function(eChar)
    local eVect, u, eSet, pos;
    eVect:=ListWithIdenticalEntries(Length(H)+1, 0);
    for u in eChar[2]
    do
      eSet:=Set([u, eChar[1]]);
      pos:=Position(H, eSet);
      eVect[pos+1]:=-1;
    od;
    pos:=Position(H, eChar[2]);
    eVect[pos+1]:=1;
    return eVect;
  end;
  FAC:=List(ListChar, GetVector);
  GRPret:=Group(ListNewPermGens);
  return rec(FAC:=FAC, GRP:=GRPret);
end;

n:=7;

eRec:=GetCone(n);

ePre:=Concatenation("Metric", String(n));
eFileEXT:=Concatenation(ePre, ".ext");
eFileGRP:=Concatenation(ePre, ".grp");
SYMPOL_PrintMatrix(eFileEXT, eRec.FAC);
SYMPOL_PrintGroup(eFileGRP, Length(eRec.FAC), eRec.GRP);
