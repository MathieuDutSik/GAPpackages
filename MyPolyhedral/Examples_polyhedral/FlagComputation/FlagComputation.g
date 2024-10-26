#EXT:=ClassicalExtremeDelaunayPolytopes("G6"); #The Schlafli polytope
EXT:=ClassicalExtremeDelaunayPolytopes("G7"); #The Gosset polytope

GRP:=__VectorConfiguration_Automorphism(EXT);
FAC:=DualDescription(EXT);


Print("|EXT|=", Length(EXT), "  |FAC|=", Length(FAC), "  |GRP|=", Order(GRP), "\n");

LorbFlag:=ListFlagOrbit(GRP, EXT, FAC);

