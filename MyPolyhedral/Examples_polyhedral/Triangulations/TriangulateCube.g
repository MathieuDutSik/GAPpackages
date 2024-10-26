n:=6;
EXT:=[];
for eEXT in BuildSet(n, [0,1])
do
  Add(EXT, Concatenation([1], eEXT));
od;
ListTrigs:=TriangulationRecursiveDelaunay(EXT);
