SelectSets:=function(SetSet, parity)
  local iCol, EvenOdd, iSet, h;
  EvenOdd:=[];
  for iSet in SetSet
  do
    h:=0;
    for iCol in [1..Length(iSet)]
    do
      h:=h+iSet[iCol];
    od;
    if (h mod 2)=0 and parity="even" then
      AddSet(EvenOdd, iSet);
    fi;
    if (h mod 2)=1 and parity="odd" then
      AddSet(EvenOdd, iSet);
    fi;
  od;
  return EvenOdd;
end;





#
#
# We take two polytopes given by coordinates
# (hypermetric or not) and returns the product polytope
ProductPolytope:=function(Polytope1, Polytope2)
  local nbVert1, nbVert2, dimension1, dimension2, iVert1, iVert2, iCol, VZ, LVert;
  nbVert1:=Length(Polytope1);
  nbVert2:=Length(Polytope2);
  dimension1:=Length(Polytope1[1]);
  dimension2:=Length(Polytope2[1]);
  LVert:=[];
  for iVert1 in [1..nbVert1]
  do
    for iVert2 in [1..nbVert2]
    do
      VZ:=Polytope1[iVert1];
      for iCol in [2..dimension2]
      do
	VZ[dimension1+iCol-1]:=Polytope2[iCol];
      od;
      Add(LVert, VZ);
    od;
  od;
  return LVert;
end;



Cube:=function(n)
  local EXT, U, V, C, i, iCol, FAC, LIST;
  EXT:=[[1]];
  for iCol in [1..n]
  do
    C:=ShallowCopy(EXT);
    EXT:=ShallowCopy([]);
    for i in [1..Length(C)]
    do
      U:=ShallowCopy(C[i]);
      V:=ShallowCopy(C[i]);
      Add(U, 1);
      Add(V, 0);
      Add(EXT, U);
      Add(EXT, V);
    od;
  od;
  FAC:=[];
  LIST:=[];
  for i in [1..n+1]
  do
    Add(LIST, 0);
  od;
  for i in [1..n]
  do
    LIST[i+1]:=1;
    Add(FAC, ShallowCopy(LIST));
    LIST[i+1]:=-1;
    LIST[1]:=1;
    Add(FAC, ShallowCopy(LIST));
    LIST[1]:=0;
    LIST[i+1]:=0;
  od;
  return rec(EXT:=EXT, FAC:=FAC);
end;




#
#
#  Construction of particular Polytopes
#  type should be "even or odd"
HalfCube:=function(n, type)
  local iCol, ListAsked, eDO, h;
  ListAsked:=[];
  for eDO in Cube(n).EXT
  do
    h:=0;
    for iCol in [2..n+1]
    do
      h:=h+eDO[iCol];
    od;
    if (h mod 2)=0 and type="even" then
      AddSet(ListAsked, eDO);
    fi;
    if (h mod 2)=1 and type="odd" then
      AddSet(ListAsked, eDO);
    fi;
  od;
  return ListAsked;
end;





InfiniteSequence:=function(n)
  local BZ, U, iCol;
  BZ:=ProductList(HalfCube(n-1, "even"), [[0]]);
  U:=[1];
  for iCol in [1..n-1]
  do
    Add(U, 1/2);
  od;
  Add(U, -1);
  Add(BZ, ShallowCopy(U));
  U[n+1]:=1;
  for iCol in [1..n-1]
  do
    U[iCol+1]:=-1/2;
    Add(BZ, ShallowCopy(U));
    U[iCol+1]:=3/2;
    Add(BZ, ShallowCopy(U));
    U[iCol+1]:=1/2;
  od;
  return BZ;
end;


InfiniteSequenceDistValues:=function(n)
  local BZ, AffBas, Hcoord, Mat, HypDim, DimHyp, V, VZ, DistM, DistValues, iCol;
  BZ:=InfiniteSequence(n);
  AffBas:=CreateAffineBasis(BZ);
  Hcoord:=HypermetricCoordinates(AffBas, BZ);
  Mat:=MatrixHypermetricInequalities(Hcoord);
  HypDim:=n+1;
  DimHyp:=1+HypDim*(HypDim-1)/2;
  V:=ListWithIdenticalEntries(DimHyp, 0);
  V[1]:=1;
  Add(Mat, V);
  VZ:=NullspaceMat(TransposedMat(Mat))[1];
  DistM:=DistanceConstructionDelaunay(VZ, Hcoord);
  DistValues:=[];
  for iCol in [1..Length(Hcoord)]
  do
    DistValues:=Union(DistValues, Set(DistM[iCol]));
  od;
  DistValues:=Difference(DistValues, [0]);
  DistValues:=RemoveFraction(DistValues);
  return DistValues;
end;

DelaunayOfDnDual:=function(n)
  local t, Vertex, ListSet, iSet, iCol, i, Zeros, Zeros4, U, SSet;
  t:=n/2;
  Vertex:=[];
  if IsInt(t)=true then
    ListSet:=BuildSet(t,[0,1]);
    Zeros:=[];
    for i in [1..t]
    do
      Zeros[i]:=0;
    od;
    for iSet in [1..Length(ListSet)]
    do
      SSet:=ListSet[iSet];
      U:=ShallowCopy([]);
      for iCol in [1..t]
      do
	if SSet[iCol]=1 then
	  U[iCol]:=1;
	else
	  U[iCol]:=-1;
	fi;
      od;
      Vertex:=Union(Vertex, ProductList([U], [Zeros]), ProductList([Zeros], [U]));
    od;
  else
    t:=t-1/2;
    ListSet:=BuildSet(t,[0,1]);
    Zeros:=[];
    for i in [1..t+1]
    do
      Zeros[i]:=0;
    od;
    Zeros4:=ShallowCopy(Zeros);
    Zeros4[t+1]:=1;
    for iSet in [1..Length(ListSet)]
    do
      SSet:=ListSet[iSet];
      U:=ShallowCopy([]);
      for iCol in [1..t]
      do
	if SSet[iCol]=1 then
	  U[iCol]:=2;
	else
	  U[iCol]:=-2;
	fi;
      od;
      Vertex:=Union(Vertex, ProductList([U], [Zeros]), ProductList([Zeros4], [U]));
    od;
  fi;
  return ProductList([[1]],Vertex);
end;
