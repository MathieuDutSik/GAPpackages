DoJohnsonEnum:=function(n,k)
  local eRec, ListOrbit, nbOrbit, iOrbit, eOrbit;
  eRec:=JohnsonPolytope(n, k);
  Print("n=", n, " k=", k, "\n");
  Print("|EXT|=", Length(eRec.EXT), " |GRP|=", Order(eRec.GRP), "\n");
  ListOrbit:=__DualDescriptionPD_Reduction_Equivariant(eRec.EXT, eRec.GRP);
  nbOrbit:=Length(ListOrbit);
  for iOrbit in [1..nbOrbit]
  do
    eOrbit:=ListOrbit[iOrbit];
    Print("iOrbit=", iOrbit, "/", nbOrbit, " |inc|=", Length(eOrbit), "\n");
  od;
  return ListOrbit;
end;


#ListOrbit:=DoJohnsonEnum(10, 3);
EXT:=JohnsonPolytope(6, 3).EXT;
ListSets:=__DualDescriptionPD_Reduction_Equivariant(EXT, Group(()));

