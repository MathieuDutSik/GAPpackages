GramMat:=ClassicalSporadicLattices("E6");
LFC:=DelaunayComputationStandardFunctions(GramMat);
SHV:=ShortVectorDutourVersion(GramMat, 4);
ListNorm:=List(SHV, x->x*GramMat*x);
Lset:=[];
for eNorm in Set(ListNorm)
do
  ListRel:=Filtered([1..Length(ListNorm)], x->ListNorm[x]=eNorm);
  Add(Lset, SHV{ListRel});
  Print("eNorm=", eNorm, " siz=", Length(ListRel), "\n");
od;
LRec:=LFC.GetDelaunayDescription();
EXT:=LRec[1].EXT;

eIso:=Isobarycenter(EXT);
Mset:=List(EXT, x->x{[2..7]} - eIso{[2..7]});

#TotalSet:=Concatenation(Mset, Lset[1]);
TotalSet:=Concatenation(Lset[1], Lset[2]);
GRP:=LinPolytope_Automorphism(TotalSet);

ListOrb:=__RepresentativeOrbitTwoSet(GRP, [1..Length(TotalSet)]);
ListFinal:=[];
FuncInsert:=function(eSet)
  local fSet, test;
  for fSet in ListFinal
  do
    test:=RepresentativeAction(GRP, eSet, fSet, OnSets);
    if test<>fail then
      return;
    fi;
  od;
  Add(ListFinal, eSet);
end;
for eOrb in ListOrb
do
  NSP:=NullspaceMat(TransposedMat(TotalSet{eOrb}));
  Print("|NSP|=", Length(NSP), "\n");
  if Length(NSP)=4 then
    eSet:=[];
    for i in [1..Length(TotalSet)]
    do
      test:=First(NSP, x->x*TotalSet[i]<>0);
      if test=fail then
        Add(eSet, i);
      fi;
    od;
    FuncInsert(eSet);
  fi;
od;
