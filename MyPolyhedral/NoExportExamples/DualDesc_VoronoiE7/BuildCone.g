#eName:="E6";
eName:="E7";
GramMat:=ClassicalSporadicLattices(eName);

eRec:=VOR_GetPerfectConeFromGramMat(GramMat);

ePre:=Concatenation("Cone_", eName);
eFileEXT:=Concatenation(ePre, ".ext");
eFileGRP:=Concatenation(ePre, ".grp");
SYMPOL_PrintMatrix(eFileEXT, eRec.EXT);
SYMPOL_PrintGroup(eFileGRP, Length(eRec.EXT), eRec.GRP);
