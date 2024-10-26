n:=3;
EXT1:=BuildSet(n, [0,1]);

EXT:=List(EXT1, x->Concatenation([1],x));

GRP:=LinPolytope_Automorphism(EXT);

ListTrig:=GetAllTriangulations(EXT, GRP);

