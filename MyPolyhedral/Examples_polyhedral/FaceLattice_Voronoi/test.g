ManyMatrices:=[
[[8,2,-1,-3,-3],[2,9,-2,-3,-3],[-1,-2,6,-1,-1],[-3,-3,-1,9,-1],[-3,-3,-1,-1,9]]
];
Dim:=5;
total:=0;
Fvector:=[];
for GramMat in ManyMatrices
do
  total:=total+1;
  Print("Working with decomposition" ,total);
  LFC:=DelaunayComputationStandardFunctions(GramMat);
  Print("LFC finished\n");
  RecVor:=LFC.GetVoronoiVertices();
  TheCanon:=RecVor.GetCanonicalGraph();
od;
