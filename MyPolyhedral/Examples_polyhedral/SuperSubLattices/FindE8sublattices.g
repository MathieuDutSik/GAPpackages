GramMat:=ClassicalSporadicLattices("E8");

GRP:=ArithmeticAutomorphismGroup([GramMat]);
TheMod:=2;
ListOrb:=GetSublattices(GramMat, GRP, TheMod);
GramMat1:=ListOrb[1].GramMat;
GramMat2:=ListOrb[2].GramMat;
test:=ArithmeticIsomorphism([GramMat1], [GramMat2]);


GRP1:=ArithmeticAutomorphismGroup([GramMat1]);
GRP2:=ArithmeticAutomorphismGroup([GramMat2]);


