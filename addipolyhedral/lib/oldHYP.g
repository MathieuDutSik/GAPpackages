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
    S1:=OverDeterminateLinearSystem(A, B);
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

FindExtPolytopeIsomorphism:=function(EXT1, GraphExt1, EXT2, GraphExt2)
  local Isom;
  Isom:=IsIsomorphicGraphDutourVersion(GraphExt1, GraphExt2);
  if Isom=false then
    return false;
  fi;
  if BackbonePolytopeIsomorphism(EXT1, EXT2, Isom)=fail then
    return fail;
  else
    return true;
  fi;
end;








FindFacPolytopeIsomorphism:=function(EXT1, FAC1, GraphFac1, EXT2, FAC2, GraphFac2)
  local IsomFac, IsomExt, List1, List2, iExt, iFac, ListInc, NExt, pos;
  IsomFac:=IsIsomorphicGraphDutourVersion(GraphFac1, GraphFac2);
  if IsomFac=false then
    return false;
  fi;
  List1:=[];
  for iExt in [1..Length(EXT1)]
  do
    ListInc:=[];
    for iFac in [1..Length(FAC1)]
    do
      if FAC1[iFac]*EXT1[iExt]=0 then
        Add(ListInc, iFac);
      fi;
    od;
    Add(List1, ListInc);
  od;
  List2:=[];
  for iExt in [1..Length(EXT2)]
  do
    ListInc:=[];
    for iFac in [1..Length(FAC2)]
    do
      if FAC2[iFac]*EXT2[iExt]=0 then
        Add(ListInc, iFac);
      fi;
    od;
    Add(List2, ListInc);
  od;
  IsomExt:=[];
  for iExt in [1..Length(EXT1)]
  do
    NExt:=[];
    for iFac in List1[iExt]
    do
      AddSet(NExt, IsomFac[iFac]);
    od;
    pos:=Position(List2, NExt);
    if pos=fail then
      return fail;
    fi;
    Add(IsomExt, pos);
  od;
  if BackbonePolytopeIsomorphism(EXT1, EXT2, IsomExt)=fail then
    return fail;
  else
    return true;
  fi;
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

InvariantFormDutourVersion:=function(MatrixGenerators)
  local ListCoeff, iLin, iCol, FuncPos, ListEquations, eGen, i, j, k, l, TheEquation, pos, ListInvariantForm, eMat, U, LineForm, VR, n;
  n:=Length(MatrixGenerators[1]);
  if Length(MatrixGenerators)=0 then
    return IdentityMat(n*(n+1)/2);
  fi;
  ListCoeff:=[];
  for iLin in [1..n]
  do
    for iCol in [1..iLin]
    do
      Add(ListCoeff, [iLin, iCol]);
    od;
  od;
  FuncPos:=function(i,j)
    if i<j then
      return Position(ListCoeff, [j,i]);
    else
      return Position(ListCoeff, [i,j]);
    fi;
  end;
  ListEquations:=[];
  for eGen in MatrixGenerators
  do
    U:=eGen;
    for i in [1..n]
    do
      for j in [1..i]
      do
        TheEquation:=ListWithIdenticalEntries(Length(ListCoeff), 0);
        TheEquation[FuncPos(i,j)]:=1;
        for k in [1..n]
        do
          for l in [1..n]
          do
            pos:=FuncPos(k,l);
            TheEquation[pos]:=TheEquation[pos]-U[k][i]*U[l][j];
          od;
        od;
        AddSet(ListEquations, TheEquation);
      od;
    od;
  od;
  ListInvariantForm:=[];
  for eMat in NullspaceMat(TransposedMat(ListEquations))
  do
    VR:=RemoveFraction(eMat);
    U:=[];
    for i in [1..n]
    do
      LineForm:=[];
      for j in [1..n]
      do
        Add(LineForm, VR[FuncPos(i,j)]);
      od;
      Add(U, LineForm);
    od;
    Add(ListInvariantForm, U);
  od;
  return ListInvariantForm;
end;






IsSymmetryGroup:=function(EXT, DistVector, GroupExt)
  local DistMatrix, eGen;
  DistMatrix:=DistanceConstructionDelaunay(DistVector, EXT);
  for eGen in GeneratorsOfGroup(GroupExt)
  do
    if Permuted(List(DistMatrix, x->Permuted(x,eGen)), eGen)<>DistMatrix then
      return false;
    fi;
  od;
  return true;
end;






IdentificationWithKnownPolytope:=function(EXT, EXTembed, distEXT, EXTknown, DistMatrixKnown)
  local EXTren, iExt, U, FindCoord, EXTnew, EXTred, ListG, Aff, MatOrig, MatDest, i, TransMat, NewMat, V, EXTdiff, AdditionalVertices, pos, eVert, n, p, UNU, DMred;
  EXTren:=[];
  for iExt in [1..Length(EXTknown)]
  do
    U:=[1];
    Append(U, EXTknown[iExt]);
    Add(EXTren, U);
  od;
  n:=RankMat(EXT);
  p:=RankMat(EXTembed);

  EXTdiff:=Difference(Set(EXT), Set(EXTembed));
  FindCoord:=function()
    local eMatch, TheMat;
    while(true)
    do
      eMatch:=RandomSubset(EXTdiff, n-p);
      TheMat:=Union(Set(EXTembed), eMatch);
      if RankMat(TheMat)=n then
        return eMatch;
      fi;
    od;
  end;
  EXTnew:=ShallowCopy(EXTembed);
  Append(EXTnew, EXTdiff);
  Print("Rank EXTnew=", RankMat(EXTnew), "\n");
  DMred:=DistanceConstructionDelaunay(distEXT, EXTembed);

  ListG:=IsIsomorphicExtremeDelaunay(DMred, DistMatrixKnown);
  Aff:=CreateAffineBasis(EXTembed);

  AdditionalVertices:=FindCoord();
  MatOrig:=ShallowCopy(Aff);
  Append(MatOrig, AdditionalVertices);
  MatDest:=[];
  UNU:=ListWithIdenticalEntries(n-p, 0);
  for i in [1..Length(Aff)]
  do
    pos:=Position(EXTembed, Aff[i]);
    V:=EXTren[ListG[pos]];
    Append(V, ShallowCopy(UNU));
    Add(MatDest, V);
  od;
  V:=ListWithIdenticalEntries(n,0);
  V[1]:=1;
  for i in [p+1..n]
  do
    V[i]:=1;
    Add(MatDest, ShallowCopy(V));
    V[i]:=0;
  od;
  TransMat:=TransposedMat(MatDest)*Inverse(TransposedMat(MatOrig));

  NewMat:=[];
  for iExt in [1..Length(EXTnew)]
  do
    eVert:=TransMat*EXTnew[iExt];
    Add(NewMat, eVert{[2..n]});
  od;
  return NewMat;
end;



#
# ListPoints must contains M+1 points.
# returns (M! vol(S))^2
SquareMvolume:=function(DistMat, ListPoints)
  local M, OP, SQR, iV;
  M:=Length(ListPoints)-1;
  SQR:=1;
  for iV in [2..M+1]
  do
    OP:=OrthogonalProjection(DistMat, ListPoints[iV], ListPoints{[1..iV-1]});
    SQR:=SQR*OP.SquareDistance;
  od;
  return SQR;
end;



#
#
# this functions takes as argument one nondegenerate hypermetric vector and 
# returns true if it belongs to HYP_{HypDim} and one violated inequality
# otherwise
# DistVector should be fractionnal
IsHypermetric:=function(DistVector, HypDim)
  local GramMatrix, DistMatrix, n, Cent, CenterPolytope, V, rsquare, iCol, iLin, RS, HypV;
  n:=HypDim-1;
  DistMatrix:=DistanceVectorToDistanceMatrix(DistVector, HypDim);
  GramMatrix:=DistanceMatrixToGramMatrix(DistMatrix);
  Cent:=CenterRadiusPolytope(DistVector,HypDim);
  rsquare:=Cent.SquareRadius;
  CenterPolytope:=Cent.Center;
  V:=[];
  for iCol in [1..n]
  do
    V[iCol]:=CenterPolytope[iCol+1];
  od;
  RS:=DetectorCVP(GramMatrix, V, rsquare);
  if RS=true then
    return true;
  else
    HypV:=ListWithIdenticalEntries(HypDim, 0);
    HypV[1]:=1;
    for iCol in [1..n]
    do
      HypV[iCol+1]:=RS[iCol];
      HypV[1]:=HypV[1]-RS[iCol];
    od;
    return HypV;
  fi;
end;


#
#
# this functions takes as argument one nondegenerate hypermetric vector and 
# returns the list of incident hypermetrics
ListIncidentHypermetric:=function(DistVector, HypDim)
  local GramMatrix, DistMatrix, n, CP, V, rsquare, iCol, RS, ListV, HypV, iVert, VE;
  n:=HypDim-1;
  DistMatrix:=DistanceVectorToDistanceMatrix(DistVector, HypDim);
  GramMatrix:=DistanceMatrixToGramMatrix(DistMatrix);
  CP:=CenterRadiusPolytope(DistVector,HypDim);
  rsquare:=CP.SquareRadius;
  V:=CP.Center{[2..n+1]};
  RS:=EqualityCVP(GramMatrix, V, rsquare);
  ListV:=[];
  for iVert in [1..Length(RS)]
  do
    HypV:=ListWithIdenticalEntries(HypDim, 0);
    HypV[1]:=1;
    VE:=RS[iVert];
    for iCol in [1..n]
    do
      HypV[iCol+1]:=VE[iCol];
      HypV[1]:=HypV[1]-VE[iCol];
    od;
    ListV[iVert]:=HypV;
  od;
  return ListV;
end;


#
#
# d is assumed to be a nondegenerate hypermetric and the goal is to return
# the adjacent hypermetrics.
SettingListAdjacentHypermetric:=function(d, HypDim, ask, provide)
  local LINChyp, LINChypnew, test, dim, ColRemove, eHYP, evHYP, NEW, iCol, LPINC, LPEXT, output;
  if provide="no" then
    LINChyp:=ListIncidentHypermetric(d, HypDim);
  else
    LINChyp:=provide;
  fi;
  test:=0;
  dim:=1+HypDim*(HypDim-1)/2;
  ColRemove:=2; # in general case of GiveAdjacent, first coord can be =0
  LPINC:=[];
  LINChypnew:=[];
  for eHYP in LINChyp
  do
    evHYP:=FromHypermetricVectorToHypermetricFace(eHYP);
    if evHYP*evHYP>0 then
      NEW:=[];
      for iCol in [1..dim]
      do
        if ColRemove<>iCol then
	   Add(NEW, evHYP[iCol]);
        fi;
      od;
      Add(LPINC, NEW);
      Add(LINChypnew, eHYP);
    fi;
  od;
  if ask="data" then
    return rec(LPINC:=LPINC, LINChyp:=LINChypnew);
  else
    LPEXT:=DualDescription(LPINC);
    return rec(LPEXT:=LPEXT, LPINC:=LPINC, LINChyp:=LINChypnew);
  fi;
end;



ListAdjacentHypermetric:=function(INEXT, d, HypDim, RNKcrit)
  local LPEXT, eExt, ListAdj, FuncReturnTheSecond, TestHypermetricityByReduction, LINCR, iElt, VMA, LPINC, dse, RSU, ListRelevantHypermetricFace, LINChyp, DistMatrix, GramMatrix, VZ, eO, O, RNK, iCol, Maxi, eHyp, InitialSetFacet, SPC;

  LPEXT:=INEXT.LPEXT;
  Print("We have ", Length(LPEXT), "  extreme rays\n");
  LPINC:=INEXT.LPINC;
  LINChyp:=INEXT.LINChyp;
  InitialSetFacet:=[];
  for eHyp in LINChyp
  do
    Add(InitialSetFacet, FromHypermetricVectorToHypermetricFace(eHyp));
  od;


  FuncReturnTheSecond:=function(VM, ListFAC)
    local LV, ListCase, VO, EXT1, iD, EXT2, det12, iElt, EXTN, det1N, det2N, test, S, iV, eV, eInc, eFac;
    ListCase:=[];
    for eFac in ListFAC
    do
      VO:=[VM[1]*eFac, VM[2]*eFac];
      if VO<>[0,0] then
	AddSet(ListCase, VO);
      fi;
    od;
    EXT1:=ListCase[1];
    iD:=2;
    while(true)
    do
      EXT2:=ListCase[iD];
      det12:=EXT1[1]*EXT2[2]-EXT1[2]*EXT2[1];
      if (det12<>0) then
	break;
      fi;
      iD:=iD+1;
    od;
    for iElt in [iD+1..Length(ListCase)]
    do
      EXTN:=ListCase[iElt];
      det1N:=EXT1[1]*EXTN[2]-EXT1[2]*EXTN[1];
      det2N:=EXT2[1]*EXTN[2]-EXT2[2]*EXTN[1];
      if (det1N*det2N>0) then
        if (det12*det1N>0) then
          EXT2:=ShallowCopy(EXTN);
	  det12:=det1N;
	else
          EXT1:=ShallowCopy(EXTN);
	  det12:=-det2N;
	fi;
      fi;
    od;
    if (det12>0) then
      LV:=[[-EXT1[2], EXT1[1]], [EXT2[2], -EXT2[1]]];
    else
      LV:=[[EXT1[2], -EXT1[1]], [-EXT2[2], EXT2[1]]];
    fi;
    test:=[1,1];
    S:=[];
    for iV in [1,2]
    do
      eV:=LV[iV];
      S[iV]:=eV[1]*VM[1]+eV[2]*VM[2];
      for eInc in InitialSetFacet
      do
	if S[iV]*eInc<>0 then
	  test[iV]:=0;
	fi;
      od;
    od;
    if test=[0,0] then
      test:=NullMat(5);
    fi;
    return S[Position(test, 0)];
  end;


  #
  # this function takes a distance matrix, which is degenerate and returns
  # either an hypermetric inequality violated by it or a reduced distance vector
  TestHypermetricityByReduction:=function(DistM, rnk)
    local iPerm, DistWork, GramWork, eSet, iCol, GramRed, DistRed, DistVectRed, RS, fSet, Bvector, swp;
    Print("\n\n\n");
    Print("Running the dangerous procedure\n");
    Print("rnk=", rnk, "\n");
    Print("HypDim=", HypDim, "\n");
    Print("DistM=", DistM, "\n");
    for iPerm in [1..HypDim]
    do
      Print("iPerm=", iPerm, "\n");
      if iPerm=1 then
        DistWork:=DistM;
      else
        DistWork:=ExchangeColumnRow(DistM, 1, iPerm);
      fi;
      GramWork:=DistanceMatrixToGramMatrix(DistWork);
      Print("GramWork=");
      PrintArray(GramWork);
      for eSet in Combinations([1..HypDim-1], rnk)
      do
        Print("eSet=", eSet, "\n");
        if IsGramAffineBasis(GramWork, eSet, rnk)=true then
          GramRed:=ExtractSubMatrix(GramWork, eSet);
          DistRed:=GramMatrixToDistanceMatrix(GramRed);
          DistVectRed:=RemoveFraction(DistanceMatrixToDistanceVector(DistRed));
          RS:=IsHypermetric(DistVectRed, Length(eSet)+1);
          if RS=true then
            return rec(reply:="good", result:=DistVectRed);
          else
            Print("RS=", RS, "\n");
            Print("eSet=", eSet, "\n");
            fSet:=[1];
            for iCol in [1..Length(eSet)]
            do
              Add(fSet, 1+eSet[iCol]);
            od;
            Print("fSet=", fSet, "\n");
            Bvector:=ListWithIdenticalEntries(HypDim, 0);
            for iCol in [1..Length(fSet)]
            do
              Bvector[fSet[iCol]]:=RS[iCol];
            od;
            Print("Bvector=", Bvector, "\n");
            if iPerm<>1 then
              swp:=Bvector[iPerm];
              Bvector[iPerm]:=Bvector[1];
              Bvector[1]:=swp;
            fi;
            return rec(reply:="fail", result:=Bvector);
          fi;
        fi;
      od;
    od;
    Print("Did not find an affine basis\n");
    return fail;
  end;



  ListAdj:=[];
  for eExt in LPEXT
  do
    LINCR:=[FacetOfInfinity(1+HypDim*(HypDim-1)/2)];
    ListRelevantHypermetricFace:=MET_Facets(HypDim, "cone");
    for iElt in [1..Length(LPINC)]
    do
      if eExt*LPINC[iElt]=0 then
	Add(LINCR, FromHypermetricVectorToHypermetricFace(LINChyp[iElt]));
      fi;
      Add(ListRelevantHypermetricFace, FromHypermetricVectorToHypermetricFace(LINChyp[iElt]));
    od;
    VMA:=NullspaceMat(TransposedMat(LINCR));
    if Length(VMA)<>2 then
      VMA:=NullMat(5);
    fi;
    while(true)
    do
      Print("running the procedure of adjacency\n");
      dse:=FuncReturnTheSecond(VMA, ListRelevantHypermetricFace);
      dse:=RemoveFraction(dse);
      Maxi:=1;
      for iCol in [1..Length(dse)]
      do
        if dse[iCol]>Maxi then
          Maxi:=dse[iCol];
        fi;
      od;
      if Maxi>50 then
        Print("We skip due to MASSIVE size of the coefficients\n");
        break;
      fi;
      DistMatrix:=DistanceVectorToDistanceMatrix(dse, HypDim);

      GramMatrix:=DistanceMatrixToGramMatrix(DistMatrix);
      RNK:=RankMat(GramMatrix);
      Print("Rank Found=", RNK, "\n");
      Print("Dimension Wanabee Delaunay=", RNK, "\n");
      if RNK>6 and RNK<=RNKcrit then
        Print("testing if it is an hypermetric\n");
        RSU:=TestHypermetricityByReduction(DistMatrix, RNK);
        if RSU=fail then
          break; # we surrender
        elif RSU.reply="good" then
          Print("we find an hypermetric!!!\n");
          Print("hyper=", RSU.result, "\n");
          Add(ListAdj, RSU.result);
          break;
        else
          Print("Adding face=", RSU.result, "\n");
          SPC:=dse*FromHypermetricVectorToHypermetricFace(RSU.result);
          Print("Scal=", SPC, "\n");
          if (SPC>0) or (SPC=0) then
            break; # we surrender
          fi;
          Add(ListRelevantHypermetricFace, FromHypermetricVectorToHypermetricFace(RSU.result));
        fi;
      else
        Print("We skip due to UNINTERESTING rank\n");
        break;
      fi;
    od;
  od;
  return ListAdj;
end;

