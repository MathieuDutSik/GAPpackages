EXT:=ClassicalExtremeDelaunayPolytopes("G6");

nbVert:=Length(EXT);
GRP:=SymmetricGroup([1..nbVert]);

ListCan:=[];
nbIter:=100;
for iter in [1..nbIter]
do
  Print("iter=", iter, " / ", nbIter, " |ListCan|=", Length(Set(ListCan)), "\n");
  g:=Random(GRP);
  EXTperm:=Permuted(EXT, g);
  eRec:=LinPolytopeIntegral_CanonicalForm(EXTperm);
#  eRand:=RandomIntegralGLnZmatrix(4);
  Add(ListCan, eRec.EXT);

od;