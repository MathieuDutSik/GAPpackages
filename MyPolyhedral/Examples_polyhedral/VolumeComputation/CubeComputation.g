for n in [3..9]
do
  EXT:=List(BuildSet(n,[0,1]), x->Concatenation([1],x));
  GRP:=LinPolytope_Automorphism(EXT);
  TheVol:=PolytopeVolumeRecursive(EXT, GRP);
  Print("n=", n, "  TheVol=", TheVol, "\n");
od;
