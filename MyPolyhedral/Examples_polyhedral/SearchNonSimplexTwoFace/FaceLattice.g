#EXT:=ClassicalExtremeDelaunayPolytopes("G6");
#EXT:=ClassicalExtremeDelaunayPolytopes("G7");
#EXT:=ClassicalExtremeDelaunayPolytopes([7,1]);

ListTwoFaces:=[];
for i in [1..27]
do
  EXT:=ClassicalExtremeDelaunayPolytopes([8,i]);
  GRP:=LinPolytope_Automorphism(EXT);
  LevSearch:=3;
  TheIncomp:=IncompleteSkeletonSearch(GRP, EXT, [], LevSearch);
  ListRep:=TheIncomp[3].ListRepresentent;
  ListSizes:=List(ListRep, Length);
  if Position(ListSizes, 4)<>fail then
    Print("We find one\n");
    Print(NullMat(5));
  fi;
od;
