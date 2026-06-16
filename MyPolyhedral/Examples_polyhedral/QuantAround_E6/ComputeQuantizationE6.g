eGram:=ClassicalSporadicLattices("E6");

ListFunc:=DelaunayComputationStandardFunctions(eGram);

SecMoment:=ListFunc.GetQuantization();
ConwaySloane:=ListFunc.GetQuantization_ConwaySloane();

Print("E6 lattice quantization constant\n");
Print("SecMoment = ", SecMoment, "\n");
Print("ConwaySloane = ", ConwaySloane, "\n");
