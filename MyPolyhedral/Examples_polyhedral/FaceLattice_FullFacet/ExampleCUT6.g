eRec:=CutPolytope(6);
EXT:=eRec.EXT;
GRP:=LinPolytope_Automorphism(EXT);
FAC:=DualDescription(EXT);

TheResult:=CreateK_skeletton(GRP, EXT, FAC);
