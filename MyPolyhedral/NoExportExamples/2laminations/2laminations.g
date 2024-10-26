#EXT:=ClassicalExtremeDelaunayPolytopes("G6"); #The Schlafli polytope
EXT:=ClassicalExtremeDelaunayPolytopes("G7"); #The Gosset polytope

PermGRP:=__VectorConfiguration_Automorphism(EXT);



ListOrbit:=Enumerate2laminations(EXT, PermGRP);
