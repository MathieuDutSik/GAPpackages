GramMat:=ClassicalSporadicLattices("E6");
PointGRP:=ArithmeticAutomorphismGroup([GramMat]);


DelCO:=DelaunayDescriptionStandard(
    rec(GramMat:=GramMat,
        PointGRP:=PointGRP)
       );

CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, DelCO[1].EXT);
eVect1:=CP.Center;
eVect2:=-CP.Center;
eVect2[1]:=1;
ListCosets:=List([eVect1, eVect2], PeriodicVectorMod1);

U:=rec(GramMat:=GramMat, ListCosets:=ListCosets);

ListFunc:=Periodic_DelaunayComputationStandardFunctions(U);
TheDesc:=ListFunc.GetDelaunayDescription();
ListVoronoiVertices:=ListFunc.GetVoronoiVertices();
