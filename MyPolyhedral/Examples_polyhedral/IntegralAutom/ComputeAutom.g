ListEXT:=ReadAsFunction("List24_EXT")();
#ListEXT:=ReadAsFunction("List8_EXT")();


ListGRP:=[];
for EXT in ListEXT
do
  eRecGRP:=LinPolytopeIntegral_Automorphism(EXT);
  Add(ListGRP, eRecGRP);
od;

