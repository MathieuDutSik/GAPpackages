#EXT:=ClassicalExtremeDelaunayPolytopes("G6");
EXT:=ClassicalExtremeDelaunayPolytopes("G7");
#EXT:=ClassicalExtremeDelaunayPolytopes([7,1]);

GRP:=__TheCore_Automorphism(EXT);


LevSearch:=RankMat(EXT);
TheIncomp:=IncompleteSkeletonSearch(GRP, EXT, [], LevSearch);
#TheBound:=BoundaryOperatorsCellularDecompositionPolytope(GRP, EXT, LevSearch-2);
