ProductOfPoset:=function(Poset1, Poset2)
  local ListVert1, ListVert2, ListNewVert, u1, u2, NewPoset, v1, v2, pos1, pos2;
  ListVert1:=ListOfVertices(Poset1);
  ListVert2:=ListOfVertices(Poset2);
  ListNewVert:=[];
  for u1 in ListVert1
  do
    for u2 in ListVert2
    do
      Add(ListNewVert, [u1,u2]);
    od;
  od;
  NewPoset:=[];
  for v1 in ListNewVert
  do
    for v2 in ListNewVert
    do
      pos1:=Position(ListNewVert, v1);
      pos2:=Position(ListNewVert, v2);
      if v1[1]=v2[1] and [v1[2],v2[2]] in Poset2 then
        Add(NewPoset, [pos1,pos2]);
      elif [v1[1],v2[1]] in Poset1 and v1[2]=v2[2] then
        Add(NewPoset, [pos1,pos2]);
      elif [v1[1],v2[1]] in Poset1 and [v1[2],v2[2]] in Poset2 then
        Add(NewPoset, [pos1,pos2]);
      fi;
    od;
  od;
  return rec(ListVert:=ListNewVert, Poset:=NewPoset);
end;


ProductOfPolytope:=function(Poset1, Poset2)
  return AddLowest(ProductOfPoset(RemoveLowest(Poset1), RemoveLowest(Poset2)).Poset);
end;

PrismConstruction:=function(Poset)
  return ProductOfPolytope(Poset, Diamond());
end;



BiPyramidConstruction:=function(Poset)
  return DualPoset(PrismConstruction(Poset));
end;






PyramidConstruction:=function(Poset)
  local NewList, eVert, fVert, iVert, jVert, NewPoset;
  NewList:=[];
  for eVert in ListOfVertices(Poset)
  do
    Add(NewList, [eVert, 0]);
    Add(NewList, [eVert, 1]);
  od;
  Print("NewList=", NewList, "\n");
  NewPoset:=[];
  for iVert in [1..Length(NewList)]
  do
    for jVert in [1..Length(NewList)]
    do
      eVert:=NewList[iVert];
      fVert:=NewList[jVert];
      if eVert[1]=fVert[1] and eVert[2]<fVert[2] then
        Add(NewPoset, [iVert, jVert]);
      elif [eVert[1], fVert[1]] in Poset and eVert[2]<=fVert[2] then
        Add(NewPoset, [iVert, jVert]);
      fi;
    od;
  od;
  return NewPoset;
end;


ExoticSuspensionFromBelow:=function(Poset)
  local lowest, ListVert, New1, New2, NewPoset, eVert;
  lowest:=FindLowest(Poset);
  ListVert:=ListOfVertices(Poset);
  New1:=1;
  New2:=2;
  while (New1 in ListVert) or (New2 in ListVert)
  do
    New1:=New1+1;
    New2:=New2+1;
  od;
  NewPoset:=StructuralCopy(Poset);
  for eVert in ListVert
  do
    if eVert<>lowest then
      Add(NewPoset, [New1, eVert]);
    fi;
    Add(NewPoset, [New2, eVert]);
  od;
  Add(NewPoset, [New2, New1]);
  return NewPoset;
end;

