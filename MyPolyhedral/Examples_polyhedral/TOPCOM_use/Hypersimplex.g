DoTest:=function(n,k)
  local EXT1, EXT2, GRP1, GRP2, ListTrig;
  EXT1:=Filtered(BuildSet(n, [0,1]), x->Sum(x)=k);
  EXT2:=List(EXT1, x->Concatenation([1], x{[1..n-1]}));
  GRP1:=LinPolytope_Automorphism(EXT1);
  GRP2:=LinPolytope_Automorphism(EXT2);
  ListTrig:=GetAllTriangulations(EXT2, GRP2);
  return rec(ListTrig:=ListTrig,
             EXT:=EXT2, GRP:=GRP2);
end;

eRec:=DoTest(5,2);
