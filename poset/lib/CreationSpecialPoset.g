
Diamond:=function()
  return [[0,1],[0,2],[0,3],[1,3],[2,3]];
end;

#
#
# The special posets and some operations on them.
BooleanAlgebra:=function(n)
  local ListOfSets, nbS, iSet, jSet, Poset;
  ListOfSets:=Combinations([1..n]);
#  Print("ListOfSets=", ListOfSets, "\n");
  nbS:=Length(ListOfSets);
  Poset:=[];
  for iSet in [1..nbS]
  do
    for jSet in [1..nbS]
    do
      if iSet<>jSet then
        if IsSubset(ListOfSets[jSet], ListOfSets[iSet])=true then
          Add(Poset, [iSet, jSet]);
        fi;
      fi;
    od;
  od;
  return Poset;
end;


#LatticeOfNCube:=function(n)
#  local LS, HasseList;
#  LS:=Cube(n);
#  HasseList:=CreateHasseList(Group(()), LS.FAC, LS.EXT);
#  return DualPoset(HasseListToPoset(HasseList));
#end;



LatticeOfPolygon:=function(n)
  local HasseList, i;
  HasseList:=[];
  for i in [1..n]
  do
    Add(HasseList, [1, i+1]);
    Add(HasseList, [n+1+i, 2*n+2]);
    Add(HasseList, [1+i, n+1+i]);
    if i<n then
      Add(HasseList, [2+i, n+1+i]);
    else
      Add(HasseList, [2, 2*n+1]);
    fi;
  od;
  return HasseListToPoset(HasseList);
end;

