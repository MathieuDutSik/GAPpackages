#eG:=ClassicalSporadicLattices("E8");
eG:=ClassicalSporadicLattices("E6");
LFC:=DelaunayComputationStandardFunctions(eG);
ListOrbitByDim:=LFC.GetOrbitCells();
