eRecInfo:=Q5_GetPolyhedraH3();

TheGRP:=eRecInfo.WeylGroupH3;
ListVect:=eRecInfo.ListVert12Cell_Q5;
EXT:=List(ListVect, x->Concatenation([1], x));
ListPermGens:=[];
for eGen in GeneratorsOfGroup(TheGRP)
do
  eList:=List(ListVect, x->Position(ListVect, x*eGen));
  Add(ListPermGens, PermList(eList));
od;
GroupEXT:=Group(ListPermGens);

ListOrbInc:=__DualDescriptionCDD_Q5(EXT, GroupEXT);

#FileExt:="IcosaEXT_Q5";
#WriteMatrixQ5(FileExt, EXT);
