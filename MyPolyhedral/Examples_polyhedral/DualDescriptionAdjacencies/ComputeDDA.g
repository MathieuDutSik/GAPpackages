#EXT:=ClassicalExtremeDelaunayPolytopes("G6");
#EXT:=ClassicalExtremeDelaunayPolytopes("G7");
EXT:=ClassicalExtremeDelaunayPolytopes([7,1]);

GRP:=__TheCore_Automorphism(EXT);


DDA:=DualDescriptionAdjacencies(EXT);
Print("|FAC|=", Length(DDA.FAC), "\n");
nbVert:=DDA.SkeletonGraph.order;
Print("nbVert=", nbVert, "\n");
ListDeg:=Collected(List([1..nbVert], x->Length(Adjacency(DDA.SkeletonGraph, x))));
Print("ListDeg=", ListDeg, "\n");
TheDegDual:=DDA.RidgeGraph.order;
ListDegDual:=Collected(List([1..TheDegDual], x->Length(Adjacency(DDA.RidgeGraph, x))));
Print("ListDegDual=", ListDegDual, "\n");

