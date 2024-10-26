ListEXT:=ReadAsFunction("List24_EXT")();
#ListEXT:=ReadAsFunction("List8_EXT")();


ListEquiv:=[];
for EXT in ListEXT
do
  len:=Length(EXT[1]);
  eMat:=RandomIntegralGLnZmatrix(len);
  EXT1:=Set(EXT);
  EXT2:=Set(EXT*eMat);
  eEquiv:=LinPolytopeIntegral_Isomorphism(EXT1, EXT2);
  Add(ListEquiv, eEquiv);
od;

