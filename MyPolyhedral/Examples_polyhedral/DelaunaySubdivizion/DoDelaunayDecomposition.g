GramMat:=ClassicalSporadicLattices("ER7");
#GramMat:=ClassicalSporadicLattices("BW16");
#GramMat:=ClassicalSporadicLattices("E7");
#GramMat:=ClassicalSporadicLattices("E6");
#GramMat:=ClassicalSporadicLattices("O10");
#GramMat:=ClassicalSporadicLattices("O12");
#GramMat:=LatticeDn(4);

ListFunc:=DelaunayComputationStandardFunctions(GramMat);
DelCO:=ListFunc.GetDelaunayDescription();
