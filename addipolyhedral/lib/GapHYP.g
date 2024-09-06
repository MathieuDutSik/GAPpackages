CanonicalizeHypermetricInequality:=function(eHyp)
  local EV, i;
  EV:=[];
  for i in [1..Length(eHyp)]
  do
    EV[i]:=eHyp[i];
  od;
  Sort(EV);
  return ShallowCopy(EV);
end;

CanonicalizeHypermetricInequalitySwitching:=function(eHYP)
  local eV, i;
  eV:=[];
  for i in [1..Length(eHYP)]
  do
    Add(eV, AbsInt(eHYP[i]));
  od;
  Sort(eV);
  return ShallowCopy(eV);
end;

TestNonDegeneracy:=function(d, HypDim)
  local DistMatrix, GramMatrix;
  DistMatrix:=DistanceVectorToDistanceMatrix(d, HypDim);
  GramMatrix:=DistanceMatrixToGramMatrix(DistMatrix);
  if (Determinant(GramMatrix)<>0) then
    return true;
  else
    return false;
  fi;
end;



VectorsToDistanceVector:=function(ListVector)
  local d, nV, VE, i, j;
  d:=[0];
  nV:=Length(ListVector);
  for i in [1..nV-1]
  do
    for j in [i+1..nV]
    do
      VE:=ListVector[j]-ListVector[i];
      Add(d, VE*VE);
    od;
  od;
  return d;
end;




#
#
# This function takes as argument a list of vertices in hypermetric coordinates
# and a distance vector and returns the hypermetric coordinates of the center of the
# corresponding Delaunay polytope
CenterRadiusPolytope:=function(DistVector, HypDim)
  local GramMatrix, DistMatrix, n, B, iCol, jLin, HI, Cent, SquareRadius;
  DistMatrix:=DistanceVectorToDistanceMatrix(DistVector, HypDim);
  GramMatrix:=DistanceMatrixToGramMatrix(DistMatrix);
  n:=HypDim-1;
  B:=List([1..n], x->GramMatrix[x][x]/2);
  HI:=SolutionMat(GramMatrix,B);
  Cent:=Concatenation([1-Sum(HI)], HI);
  SquareRadius:=HI*GramMatrix*HI;
  return rec(Center:=Cent, SquareRadius:=SquareRadius);
end;






FindHypDim:=function(MetDim)
  local HypDim, TryDim;
  HypDim:=1;
  while(true)
  do
    TryDim:=1+HypDim*(HypDim-1)/2;
    if TryDim=MetDim then
      return HypDim;
    fi;
    if HypDim>MetDim then
      return false;
    fi;
    HypDim:=HypDim+1;
  od;
end;


RankHypermetricCoordinates:=function(HypCoord)
  local HypDim, MetDim, Mat, eHyp;
  HypDim:=Length(HypCoord[1]);
  Mat:=MatrixHypermetricInequalities(HypCoord);
  MetDim:=HypDim*(HypDim-1)/2;
  return MetDim-RankMat(Mat);
end;

Decalc:=function(eV)
  return eV{[2..Length(eV)]};
end;






#
#
#
#
CombinatorialObjectOfExtremeDelaunayPolytope:=function(DistVector, Hcoord)
  local DistMatrix, VertexSet, NbV, iVertex, jVertex, pos1, pos2, pos3, Gra, CommonDenominator, iCol, PossibleDistances, iDist, jDist, d;
  DistMatrix:=DistanceConstructionDelaunay(DistVector, Hcoord);
  DistVector:=DistanceMatrixToDistanceVector(DistMatrix);
  CommonDenominator:=1;
  for iCol in [2..Length(DistVector)]
  do
    CommonDenominator:=Lcm(CommonDenominator, DenominatorRat(DistVector[iCol]));
  od;
  DistVector:=CommonDenominator*DistVector;
  DistMatrix:=CommonDenominator*DistMatrix;
  PossibleDistances:=[];
  for iCol in [2..Length(DistVector)]
  do
    AddSet(PossibleDistances, DistVector[iCol]);
  od;
#  Print("DistanceSet=", PossibleDistances, "\n");
  VertexSet:=[];
  NbV:=Length(Hcoord);
  for iVertex in [1..NbV]
  do
    AddSet(VertexSet, [1, iVertex]);
  od;
  for iVertex in [1..NbV-1]
  do
    for jVertex in [iVertex+1..NbV]
    do
      AddSet(VertexSet, [2, iVertex, jVertex]);
    od;
  od;
  for iDist in [1..Length(PossibleDistances)]
  do
    for jDist in [1..PossibleDistances[iDist]]
    do
      AddSet(VertexSet, [3, iDist, jDist]);
    od;
  od;
  # creation of the graph
  Gra:=NullGraph(Group(()), Length(VertexSet));
  for iVertex in [1..NbV-1]
  do
    for jVertex in [iVertex+1..NbV]
    do
      pos1:=Position(VertexSet, [2, iVertex, jVertex]);
      pos2:=Position(VertexSet, [1, iVertex]);
      pos3:=Position(VertexSet, [1, jVertex]);
      AddEdgeOrbit(Gra, [pos2, pos1]);
      AddEdgeOrbit(Gra, [pos3, pos1]);
    od;
  od;
  for iDist in [1..Length(PossibleDistances)]
  do
    for jDist in [1..PossibleDistances[iDist]-1]
    do
      pos1:=Position(VertexSet, [3, iDist, jDist]);
      pos2:=Position(VertexSet, [3, iDist, jDist+1]);
      AddEdgeOrbit(Gra, [pos1, pos2]);
    od;
  od;
  for iVertex in [1..NbV-1]
  do
    for jVertex in [iVertex+1..NbV]
    do
      d:=DistMatrix[iVertex][jVertex];
      pos1:=Position(PossibleDistances, d);
      pos2:=Position(VertexSet, [2, iVertex, jVertex]);
      pos3:=Position(VertexSet, [3, pos1, 1]);
      AddEdgeOrbit(Gra, [pos2, pos3]);
    od;
  od;
  return Gra;
end;





CreateNewExtremeDelaunay:=function(GramMat, Delaunay1, Cent1, Delaunay2, Cent2)
  local n, TheMat2, TheMat1, i, j, h, W, TheMat, EXTnew, eV, U, CP, rsquare, HLR, VectSet, HypDim, MetDim, V, EXT2, Aff, Hcoord, Mat, DistV, DistMatrix, GramMatrix, EXTreturn;
  n:=Length(GramMat);
  TheMat2:=NullMat(n+1, n+1);
  TheMat2[n+1][n+1]:=1;

  TheMat1:=NullMat(n+1, n+1);
  for i in [1..n]
  do
    for j in [1..n]
    do
      TheMat1[i][j]:=GramMat[i][j];
    od;
  od;
  h:=Cent2-Cent1;
  W:=-h*GramMat;
  for i in [1..n]
  do
    TheMat1[i][n+1]:=W[i];
    TheMat1[n+1][i]:=W[i];
  od;
  TheMat:=ShallowCopy(TheMat1);
  while(true)
  do
    if IsPositiveDefiniteSymmetricMatrix(TheMat)=true then
      break;
    fi;
    TheMat:=TheMat+TheMat2;
  od;


  EXTnew:=[];
  for eV in Delaunay1
  do
    U:=ShallowCopy(eV);
    Add(U, 0);
    Add(EXTnew, ShallowCopy(U));
  od;
  for eV in Delaunay2
  do
    U:=ShallowCopy(eV);
    Add(U, 1);
    Add(EXTnew, ShallowCopy(U));
  od;
#  Print(NullMat(5));
  while(true)
  do
    CP:=CenterRadiusDelaunayPolytopeGeneral(TheMat, EXTnew);
    rsquare:=CP.SquareRadius;
    HLR:=CVPVallentinProgram(TheMat, CP.Center{[2..n+2]} );
    if HLR.TheNorm=rsquare and Length(HLR.ListVect)>Length(EXTnew) then
      EXTreturn:=[];
      for eV in HLR.ListVect
      do
        U:=[1];
        Append(U, eV);
        Add(EXTreturn, U);
      od;
      return EXTreturn;
    fi;
    if HLR.TheNorm<rsquare then
      break;
    fi;
  od;
  VectSet:=ShallowCopy(HLR.ListVect);
  HypDim:=Length(VectSet[1])+1;
  MetDim:=1+HypDim*(HypDim-1)/2;
  V:=ListWithIdenticalEntries(MetDim, 0);
  V[1]:=1;
  while(true)
  do
    EXT2:=[];
    Append(EXT2, ShallowCopy(EXTnew));
    for eV in VectSet
    do
      U:=[1];
      Append(U, eV);
      Add(EXT2, U);
    od;
    Aff:=CreateAffineBasis(EXT2);
    Hcoord:=HypermetricCoordinates(Aff, EXT2);
    Mat:=MatrixHypermetricInequalities(Hcoord);
    Add(Mat, V);
    DistV:=NullspaceMat(TransposedMat(Mat))[1];
    DistMatrix:=DistanceVectorToDistanceMatrix(DistV, HypDim);
    GramMatrix:=DistanceMatrixToGramMatrix(DistMatrix);
    Print(NullMat(5));
  od;
end;









# OrthogonalProjection returns the orthogonal projection of Point
# on the affine span of ListPoint and its square distance
OrthogonalProjection:=function(DistMat, Point, ListPoint)
  local SquareDistance, Projection, GramMatrix, RK, HypDim, ListSig, iPoint, rnk, NewListSig, ListSigTotal, FuncScalProd, v1, v2, SP, i, j, iCol, iLin, ReducedGram, VEC, Alpha;
  GramMatrix:=DistanceMatrixToGramMatrix(DistMat);
  RK:=RankMat(ListPoint);
  HypDim:=Length(Point);
  ListSig:=[];
  iPoint:=1;
  rnk:=0;
  while(rnk<RK)
  do
    NewListSig:=ShallowCopy(ListSig);
    Add(NewListSig, ListPoint[iPoint]);
    if RankMat(NewListSig)> rnk then
      rnk:=rnk+1;
      ListSig:=ShallowCopy(NewListSig);
    fi;
    iPoint:=iPoint+1;
  od;
  ListSigTotal:=ShallowCopy(ListSig);
  Add(ListSigTotal, Point);
  FuncScalProd:=function(HypIdx1, HypIdx2)
    v1:=ListSigTotal[HypIdx1]-ListSigTotal[1];
    v2:=ListSigTotal[HypIdx2]-ListSigTotal[1];
    SP:=0;
    for i in [1..HypDim-1]
    do
      for j in [1..HypDim-1]
      do
        SP:=SP+v1[i+1]*v2[j+1]*GramMatrix[i][j];
      od;
    od;
    return SP;
  end;
  ReducedGram:=NullMat(RK-1);
  for iCol in [1..RK-1]
  do
    for iLin in [1..RK-1]
    do
      ReducedGram[iCol][iLin]:=FuncScalProd(iCol+1, iLin+1);
    od;
  od;
  VEC:=[];
  for iCol in [1..RK-1]
  do
    VEC[iCol]:=FuncScalProd(RK+1, iCol+1);
  od;
  Alpha:=SolutionMat(ReducedGram, VEC);
  Projection:=ListSigTotal[1];
  for iCol in [1..RK-1]
  do
    Projection:=Projection+Alpha[iCol]*(ListSigTotal[iCol+1]-ListSigTotal[1]);
  od;
  SquareDistance:=FuncScalProd(RK+1, RK+1);
  for iCol in [1..RK-1]
  do
    for iLin in [1..RK-1]
    do
      SquareDistance:=SquareDistance-Alpha[iCol]*Alpha[iLin]*ReducedGram[iCol][iLin];
    od;
  od;
  return rec(SquareDistance:=SquareDistance, Projection:=Projection);
end;



#
# this procedure tries to find an isomorphism
# between two polytopes by using graph isomorphism of the vertices
BackbonePolytopeIsomorphism:=function(EXT1, EXT2, Isom)
  local n, iCol, B, A, iVert, DepartureExt, ArrivalExt, Line, jCol, S1, VC, VAdd, MatrixTransformation;
  n:=Length(EXT1[1])-1;
  VAdd:=[];
  MatrixTransformation:=[];
  for iCol in [1..n]
  do
    B:=[];
    A:=[];
    for iVert in [1..Length(EXT1)]
    do
      DepartureExt:=EXT1[iVert];
      ArrivalExt:=EXT2[Isom[iVert]];
      Add(B, ArrivalExt[iCol+1]);
      Line:=Concatenation([1], DepartureExt{[2..n+1]});
      Add(A, Line);
    od;
#this code is broken and by now obsolete.
#    S1:=OverDeterminateLinearSystem(A, B);
    if S1=false then
      return fail;
    fi;
    if IsInt(S1[1])=false then
      return fail;
    fi;
    Add(VAdd, S1[1]);
    VC:=[];
    for jCol in [2..Length(S1)]
    do
      if IsInt(S1[jCol])=false then
        return fail;
      fi;
      Add(VC, S1[jCol]);
    od;
    Add(MatrixTransformation, VC);
  od;
  return rec(VectorAdd:=VAdd, MatrixTransformation:=MatrixTransformation);
end;


VertexIsomorphismToMatrixIsomorphism:=function(EXT, GroupExt)
  local eGen, MatrixGenerators, IsomExt, iExt;
  MatrixGenerators:=[];
  for eGen in GeneratorsOfGroup(GroupExt)
  do
    IsomExt:=OnTuples([1..Length(EXT)], eGen);
    Add(MatrixGenerators, BackbonePolytopeIsomorphism(EXT, EXT, IsomExt));
  od;
  return MatrixGenerators;
end;



PrintDataExtremeDelaunay:=function(output, ExtremeRecord, PrintType)
  local EXT, FAC, Oext, Ofac, DistMatrix, SymGrpExt, SymGrpFac, HK, FV, iF, iExt, jExt, eExt, iCol, iLin, DistSet, iDist, n, iGen, AllGen, VAdd, GramMatrix, MatrixTransformation, DistM, eMat, CommonDenominator, ListMatSymmetryDelaunay, eGen, ListInvForm, MGR;
  EXT:=ExtremeRecord.EXT;
  FAC:=ExtremeRecord.FAC;
  DistMatrix:=DistanceConstructionDelaunay(ExtremeRecord.distvector, EXT);
  SymGrpExt:=AutomorphismGroupEdgeColoredGraph(EXT, FAC, ExtremeRecord.GraphExt, ExtremeRecord.GraphFac, ExtremeRecord.distvector);
  SymGrpFac:=TranslateGroupExtToFac(SymGrpExt, EXT, FAC);
  n:=ExtremeRecord.Linv[1];


  AppendTo(output, "\\noindent Dimension=\$", n, "\$\\\\\n");
  AppendTo(output, Length(EXT), " vertices ");
  AppendTo(output, Length(FAC), " facets");
  AppendTo(output, ", symmetry group of order ", Order(SymGrpExt), "\\\\\n");
  #
  Oext:=Orbits(SymGrpExt, [1..Length(EXT)], OnPoints);
  Ofac:=Orbits(SymGrpFac, [1..Length(FAC)], OnPoints);
  AppendTo(output, Length(Oext), " orbits of vertices ", Length(Ofac), " orbits of facets\\\\\n");
  #
  HK:=CreateK_skeletton(SymGrpExt, EXT, FAC);
  FV:=Fvector(HK);
  AppendTo(output, "\$f=(");
  for iF in [1..Length(FV)]
  do
    AppendTo(output, FV[iF]);
    if iF<Length(FV) then
      AppendTo(output, ",");
    fi;
  od;
  AppendTo(output, ")\$\\\\\n");
  #
  AppendTo(output, "List Of Vertices\n");
  AppendTo(output, "\\begin{multicols}{3}\n");
  for iExt in [1..Length(EXT)]
  do
    eExt:=EXT[iExt];
    if iExt=1 then
      AppendTo(output, "\\noindent ");
    fi;
    AppendTo(output, "\$(");
    for iCol in [1..Length(eExt)]
    do
      AppendTo(output, eExt[iCol]);
      if iCol < Length(eExt) then
        AppendTo(output, ", ");
      fi;
    od;
    AppendTo(output, ")\$\\\\\n");
  od;
  AppendTo(output, "\\end{multicols}\n");
  #
  AppendTo(output, "\\noindent Distance Vector=");
  for iCol in [2..Length(ExtremeRecord.distvector)]
  do
    AppendTo(output, ExtremeRecord.distvector[iCol]);
    if iCol < Length(ExtremeRecord.distvector) then
      AppendTo(output, ", ");
    fi;
  od;
  AppendTo(output, "\\\\\n");
  #
  AppendTo(output, "Possible distances=");
  DistSet:=[];
  for iExt in [1..Length(EXT)-1]
  do
    for jExt in [iExt+1..Length(EXT)]
    do
      AddSet(DistSet, DistMatrix[iExt][jExt]);
    od;
  od;
  for iDist in [1..Length(DistSet)]
  do
    AppendTo(output, DistSet[iDist]);
    if iDist<Length(DistSet) then
      AppendTo(output, ", ");
    fi;
  od;
  AppendTo(output, "\\\\\n");
  #
  AppendTo(output, "Centrally Symmetric Delaunay=", IsCentrallySymmetric(EXT), "\\\\\n");
  #
  AppendTo(output, "Slice Number=", SliceNumber(EXT, FAC), "\\\\\n");
  #
  DistM:=DistanceVectorToDistanceMatrix(ExtremeRecord.distvector, n+1);
  GramMatrix:=DistanceMatrixToGramMatrix(DistM);
  CommonDenominator:=1;
  for iLin in [1..n]
  do
    for iCol in [1..n]
    do
      CommonDenominator:=Lcm(CommonDenominator, DenominatorRat(GramMatrix[iLin][iCol]));
    od;
  od;
  GramMatrix:=CommonDenominator*GramMatrix;
  #
  AllGen:=VertexIsomorphismToMatrixIsomorphism(EXT, SymGrpExt);
  ListMatSymmetryDelaunay:=[];
  for eGen in AllGen
  do
    Add(ListMatSymmetryDelaunay, eGen.MatrixTransformation);
  od;
  if PrintType="complete" then
    AppendTo(output, "Matrix Group by its generators: x\-\> b+Ax with \\\\\n");
    AppendTo(output, "\\begin{multicols}{2}\n");
    for iGen in [1..Length(AllGen)]
    do
      VAdd:=AllGen[iGen].VectorAdd;
      MatrixTransformation:=AllGen[iGen].MatrixTransformation;
      AppendTo(output, "\\noindent ", iGen, ":  b=(");
      for iCol in [1..n]
      do
        AppendTo(output, VAdd[iCol]);
        if iCol < n then
          AppendTo(output, ", ");
        fi;
      od;
      AppendTo(output, ") and A=\\\\\n");
      LatexPrintMatrix(output, MatrixTransformation);
    od;
    AppendTo(output, "\\end{multicols}\n");
  fi;
  #
  AppendTo(output, "\\begin{center}\n");
  AppendTo(output, "{\\bf Lattice Informations}\n");
  AppendTo(output, "\\end{center}\n");
  AppendTo(output, "Gram matrix of the lattice\\\\\n");
  LatexPrintMatrix(output, GramMatrix);
  #
  ListInvForm:=InvariantFormDutourVersion(ListMatSymmetryDelaunay);
  if PrintType="complete" then
    AppendTo(output, "\\noindent Invariant quadratic forms by the symmetry group\\\\\n");
    AppendTo(output, "\\begin{multicols}{2}\n");
    for eMat in ListInvForm
    do
      LatexPrintMatrix(output, eMat);
    od;
    AppendTo(output, "\\end{multicols}\n");
  else
    AppendTo(output, "Dimension of space of invariant forms is ", Length(ListInvForm), "\\\\\n");
  fi;
  MGR:=MatrixAutomorphismGroupGramMatrix(GramMatrix);
  AppendTo(output, "Order of symmetry group is ", MGR.order,"\\\\\n");
  AppendTo(output, "Number of shortest vector=", Length(ShortestVectorDutourVersion(GramMatrix)), "\\\\\n");
  AppendTo(output, "Determinant of the lattice=", DeterminantMat(GramMatrix), "\n");
  if PrintType="complete" then
    AppendTo(output, "Generators of the symmetry group are :\\\\n");
    AppendTo(output, "\\begin{multicols}{2}\n");
    for eMat in MGR.ListMat
    do
      LatexPrintMatrix(output, eMat);
    od;
    AppendTo(output, "\\end{multicols}\n");
  fi;
#  AppendTo(output, "Distance Matrix is\n");
#  LatexPrintMatrix(output, DistMatrix);
end;







PermutationMatrix:=function(ePerm, n)
  local NewMatrix, iLin, Line, iCol;
  NewMatrix:=NullMat(n,n);
  for iLin in [1..n]
  do
    NewMatrix[iLin][OnPoints(iLin,ePerm)]:=1;
  od;
  return NewMatrix;
end;

ExchangeColumnRow:=function(MatrixT, idx1, idx2)
  local PermMat;
  PermMat:=PermutationMatrix((idx1, idx2), Length(MatrixT));
  return PermMat*MatrixT*PermMat;
end;

IsGramAffineBasis:=function(GramMat, eSet, rnk)
  local n, CeSet, MatSys, Annulator, iCol, jCol, LineEq, iEq, B, SolM, H;
  n:=Length(GramMat);
  Annulator:=NullspaceMat(GramMat);
  Print("Annulator=", Annulator, "\n");
  CeSet:=Difference([1..n], eSet);
  MatSys:=ExtractSubMatrix(GramMat, eSet);
  if DeterminantMat(MatSys)=0 then
    return false;
  fi;
  MatSys:=[];
  for iCol in [1..Length(CeSet)]
  do
    LineEq:=[];
    for iEq in [1..Length(Annulator)]
    do
      Add(LineEq, Annulator[iEq][CeSet[iCol]]);
    od;
    Add(MatSys, LineEq);
  od;
  for iCol in [1..Length(CeSet)]
  do
    B:=ListWithIdenticalEntries(Length(CeSet), 0);
    B[iCol]:=1;
    SolM:=SolutionMat(TransposedMat(MatSys), B);
    H:=ListWithIdenticalEntries(n, 0);
    for iEq in [1..Length(Annulator)]
    do
      H:=H+SolM[iEq]*Annulator[iEq];
    od;
    Print("H=", H, "\n");
    for jCol in [1..n]
    do
      if IsInt(H[jCol])=false then
        return false;
      fi;
    od;
  od;
  return true;
end;








#
#
# given a system of cuts, we return the list of hypermetric inequality containing it, if possible.
ListHypermetricContainingCutFace:=function(SystemCut)
  local V, iCol, HypDim, SYSLIN, rank, position, TS, RC, Vertices, B, test, iCut, SPC, eCut;
  HypDim:=Length(SystemCut[1]);
  if RankMat(SystemCut) < HypDim then
    # the face is degenerate!!!
    return false;
  fi;
  V:=[];
  for iCol in [1..HypDim]
  do
    V[iCol]:=1;
  od;
  SYSLIN:=[V];
  rank:=0;
  position:=1;
  while (rank < HypDim)
  do
    TS:=ShallowCopy(SYSLIN);
    Add(TS, SystemCut[position]);
    RC:=RankMat(TS);
    if (RC > rank) then
      SYSLIN:=TS;
      rank:=RC;
    fi;
    position:=position+1;
  od;
  # creation of the list of vertices
  Vertices:=[];
  for eCut in ProductList([[1]], BuildSet(HypDim-1,[0,1]))
  do
    B:=SolutionMat(TransposedMat(SYSLIN), eCut);
    test:=1;
    iCol:=1;
    while(iCol<=HypDim)
    do
      if IsInt(B[iCol])=false then
        test:=0;
	break;
      fi;
      iCol:=iCol+1;
    od;
    if test=1 then
      iCut:=1;
      while(iCut<=Length(SystemCut))
      do
	SPC:=SystemCut[iCut]*B;
	if (SPC <> 0 and SPC <> 1) then
	  test:=0;
	  break;
	fi;
	iCut:=iCut+1;
      od;
    fi;
    if (test = 1) then
      Add(Vertices, B);
    fi;
  od;
  return Vertices;
end;






#
#
# work with a face spanned by cuts
# FACsymbol is a list of hypermetrics defining 
# face is a sequence of numbers 
CombinatorialObjectCutFace:=function(face, FACsymbol, HypDim)
  local GRAPH, LISTINC, CUTSYMB, test, iFac, SPC, eCut, fCut, eCutb, fCutb, Vertices, iVert, NBN, NBV, NBC, Invariant, LISTSET, iSet, eU, U, cU, LST;
  # searching the list of incident cuts
  CUTSYMB:=ProductList([[1]], BuildSet(HypDim-1,[0,1]));
  LISTINC:=[];
  for eCut in CUTSYMB
  do
    test:=1;
    iFac:=1;
    while(iFac<=Length(face))
    do
      SPC:=eCut*FACsymbol[face[iFac]];
      if (SPC <> 0 and SPC <> 1) then
	test:=0;
	break;
      fi;
      iFac:=iFac+1;
    od;
    if test=1 then
      Add(LISTINC, eCut);
    fi;
  od;
  # searching a non singular system in order to list vertices
  # of the corresponding Delaunay polytope
  Vertices:=ListHypermetricContainingCutFace(LISTINC);
  NBV:=Length(Vertices); # NumBer of Vertices
  # now creating the generalized cuts defined as sets
  # 
  LISTSET:=ShallowCopy([]);
  for eCut in LISTINC
  do
    LST:=ShallowCopy([]);
    for iVert in [1..NBV]
    do
      if (eCut*Vertices[iVert]= 0) then
        Add(LST, iVert);
      fi;
    od;
    Add(LISTSET, LST);
  od;

  NBC:=Length(LISTSET); # NumBer of Cuts
  Invariant:=[];
  for eCut in LISTSET
  do
    Add(Invariant, Set([Length(eCut), Length(Difference([1..NBV], eCut))])  );
  od;
  for eCut in LISTSET
  do
    for fCut in LISTSET
    do
      if eCut<>fCut then
	eCutb:=Difference([1..NBV], eCut);
	fCutb:=Difference([1..NBV], fCut);
        Add(Invariant, Set([Length(Intersection(eCut,fCut)), Length(Intersection(eCut,fCutb)), Length(Intersection(eCutb,fCut)), Length(Intersection(eCutb,fCutb))])   );
      fi;
    od;
  od;
  

  # now creating the graph with two CutFace isomorph
  # under geometrical switching if and only if their graphs are isomorphs
  NBN:=NBV+3*NBC+2; # NumBer of Nodes of the graph
  GRAPH:=NullGraph(Group(()),NBN);
  for iSet in [1..NBC]
  do
    U:=LISTSET[iSet];
    cU:=Difference([1..NBV], U);
    for eU in U
    do
      AddEdgeOrbit(GRAPH, [eU, NBV+iSet]);
      AddEdgeOrbit(GRAPH, [NBV+iSet, eU]);
    od;
    for eU in cU
    do
      AddEdgeOrbit(GRAPH, [eU, NBV+NBC+iSet]);
      AddEdgeOrbit(GRAPH, [NBV+NBC+iSet, eU]);
    od;
    AddEdgeOrbit(GRAPH, [NBV+iSet, NBV+2*NBC+iSet]);
    AddEdgeOrbit(GRAPH, [NBV+2*NBC+iSet, NBV+iSet]);
    AddEdgeOrbit(GRAPH, [NBV+NBC+iSet, NBV+2*NBC+iSet]);
    AddEdgeOrbit(GRAPH, [NBV+2*NBC+iSet, NBV+NBC+iSet]);
    AddEdgeOrbit(GRAPH, [NBV+2*NBC+iSet, NBV+3*NBC+1]);
    AddEdgeOrbit(GRAPH, [NBV+3*NBC+1, NBV+2*NBC+iSet]);
  od;
  AddEdgeOrbit(GRAPH, [NBN-1, NBN]);
  AddEdgeOrbit(GRAPH, [NBN, NBN-1]);
  return [GRAPH, Invariant];
end;


SubGraphInvariant:=function(DM, SubGraph)
  local DMred, d, n, i, j, k;
  DMred:=List(DM{SubGraph}, x->x{SubGraph});
  n:=Length(DMred);
  d:=Concatenation(DMred);
  for i in [1..n-2]
  do
    for j in [i+1..n-1]
    do
      for k in [j+1..n]
      do
        Add(d, Set([DMred[i][j],DMred[i][k],DMred[j][k]])   );
      od;
    od;
  od;
  Sort(d);
  return d;
end;





#DistMat:=function(G)
#  local vertices, n, i,j,x,L, M;
#  M:=[];
#  vertices:=[1..G.order];
#  for n in vertices
#  do
#    L:=Layers(G,n);
#    x:=List(vertices,n -> -1);
#    for i in [1..Length(L)]
#    do
#      for j in L[i]
#      do
#        x[j]:=i-1;
#      od;
#    od;
#    Add(M, x);
#  od;
#  return M;
#end;







ExtremeDelaunayToClassical:=function(EXT, DistVect, GroupEXT)
  local HypDim, DistMatrix, GramMatrix, MatrixGroup, NewEXT, NewGens, eMat, i, NewMat, U, eEXT;
  HypDim:=Length(EXT[1]);
  DistMatrix:=DistanceVectorToDistanceMatrix(DistVect, HypDim);
  GramMatrix:=DistanceMatrixToGramMatrix(DistMatrix);
  NewEXT:=[];
  for eEXT in EXT
  do
    U:=[1];
    Append(U, eEXT{[2..HypDim]});
    Add(NewEXT, U);
  od;
  MatrixGroup:=TranslateToMatrixGroup(NewEXT, GroupEXT);
  
  NewGens:=[];
  for eMat in GeneratorsOfGroup(MatrixGroup)
  do
    NewMat:=[];
    for i in [2..HypDim]
    do
      Add(NewMat, eMat[i]{[2..HypDim]});
    od;
    Add(NewGens, NewMat);
  od;
  return rec(MatrixGroup:=PersoGroupMatrix(NewGens, HypDim), GramMat:=GramMatrix, EXT:=NewEXT);
end;


