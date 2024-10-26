GetHalfCube:=function(n)
  local EXT;
  EXT:=Filtered(BuildSet(n, [0,1]), x->Sum(x) mod 2=0);
  return List(EXT, x->Concatenation([1], x));
end;



HalfH4:=GetHalfCube(4);
AffBas:=CreateAffineBasis(HalfH4);

DistMat:=NullMat(5,5);
for i in [1..5]
do
  for j in [1..5]
  do
    eDiff:=AffBas[i]-AffBas[j];
    dist:=eDiff*eDiff;
    DistMat[i][j]:=dist;
  od;
od;
GramMat:=DistanceMatrixToGramMatrix(DistMat);

GRP:=ArithmeticAutomorphismGroup([GramMat]);
SHV:=ShortestVectorDutourVersion(GramMat);

VoronoiPolytopeFacet:=[];
for eVect in SHV
do
  eFac:=[eVect*GramMat*eVect/2];
  Append(eFac, eVect*GramMat);
  Add(VoronoiPolytopeFacet, eFac);
od;
EXTprev:=DualDescription(VoronoiPolytopeFacet);
EXT:=List(EXTprev, x->x/x[1]);
FAC:=DualDescription(EXT);

nbV:=24;
DM:=NullMat(nbV, nbV);
for i in [1..nbV-1]
do
  for j in [i+1..nbV]
  do
    eDiff:=EXT[i]{[2..5]}-EXT[j]{[2..5]};
    DM[i][j]:=eDiff*GramMat*eDiff;
    DM[j][i]:=eDiff*GramMat*eDiff;
  od;
od;
iVert1:=1;
iVert2:=First([1..nbV], x->DM[iVert1][x]=1);

GRP24cell:=AutomorphismGroupEdgeColoredGraph(DM);
LorbFlag:=ListFlagOrbit(GRP24cell, EXT, FAC);


#TheMiddle:=(EXT[iVert1]+EXT[iVert2])/2;  # middle of edges
#TheMiddle:=(EXT[iVert1]+EXT[iVert2]+EXT[3])/3; # center of triangle
TheMiddle:=Concatenation([1], SHV[1]/2);

TheMiddleRed:=VectorMod1(TheMiddle{[2..5]});

FuncActionMod1:=function(eClass, eElt)
  return VectorMod1(eClass*eElt);
end;


ListCoset:=Orbit(GRP, TheMiddleRed, FuncActionMod1);
ListCosetForProg:=List(ListCoset, x->Concatenation([1], x));

eRecU:=rec(GramMat:=GramMat, ListCosets:=ListCosetForProg);

ListFunc:=Periodic_DelaunayComputationStandardFunctions(eRecU);
TheDesc:=ListFunc.GetDelaunayDescription();
ListVoronoiVertices:=ListFunc.GetVoronoiVertices();

