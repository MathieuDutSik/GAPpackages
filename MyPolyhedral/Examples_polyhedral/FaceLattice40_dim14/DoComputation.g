preEXT:=ReadVectorFile("FileCoord");

EXT:=ColumnReduction(preEXT).EXT;
GRP:=LinPolytope_Automorphism(EXT);
FAC:=DualDescription(EXT);

TheResult:=CreateK_skeletton(GRP, EXT, FAC);
