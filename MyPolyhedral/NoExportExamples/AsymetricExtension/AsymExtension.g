EXT6:=ClassicalExtremeDelaunayPolytopes("G6"); #The Schlafli polytope
EXT7:=ClassicalExtremeDelaunayPolytopes("G7"); #The Gosset polytope


GramMat6:=FuncExtreme(EXT6).GramMatrix;
TheGen:=AntisymmetryConstruction(EXT6, GramMat6);


testequiv:=__VectorConfiguration_Isomorphism(TheGen.EXT, EXT7);
