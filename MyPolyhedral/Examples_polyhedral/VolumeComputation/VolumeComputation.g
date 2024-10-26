ListNames:=["G6", "G7", "ER7"];


ListResult:=[];
for eName in ListNames
do
  EXT:=ClassicalExtremeDelaunayPolytopes(eName);
  GRP:=LinPolytope_Automorphism(EXT);
  TheVol:=PolytopeVolumeRecursive(EXT, GRP);
  Add(ListResult, [eName, TheVol]);
od;
Print("ListResult=", ListResult, "\n");
