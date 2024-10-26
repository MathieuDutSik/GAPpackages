TheResolutionMoveToOtherGroup:=function(TheResol, GRP, kLevel)
  local phi, ListGens, ImageListGens, phiRev, IsInKernel, GetMatrix, DoHomotopy, GetDimension, kLevelEffect;
  phi:=IsomorphismGroups(GRP, TheResol.GRP);
  ListGens:=GeneratorsOfGroup(GRP);
  ImageListGens:=List(ListGens, x->Image(phi, x));
  phiRev:=GroupHomomorphismByImagesNC(TheResol.GRP, GRP, ImageListGens, ListGens);
  kLevelEffect:=Maximum(kLevel, 1);
  TheResol.Initialization(kLevelEffect);
  IsInKernel:=function(jRank, TheVector)
    local eVal, TheProd;
    if jRank=0 then
      eVal:=TheVector[1];
      if Sum(eVal.ListVal)<>0 then
        return false;
      else
        return true;
      fi;
    else
      TheProd:=VectorMatrixGmoduleMultiplication(TheVector, GetMatrix(jRank));
      return IsZeroGmoduleVector(TheProd);
    fi;
  end;
  GetMatrix:=function(jRank)
    local nbLine, nbCol, TheRetMat, eLine, eVect, eEnt, NewListElt, eRec, TheDiff;
    TheDiff:=TheResol.GetDifferentiation(jRank);
    nbLine:=TheDiff.nbLine;
    nbCol:=TheDiff.nbCol;
    TheRetMat:=[];
    for eLine in TheDiff.TheMat
    do
      eVect:=[];
      for eEnt in eLine
      do
        NewListElt:=List(eEnt.ListElt, x->Image(phiRev, x));
        eRec:=rec(ListVal:=eEnt.ListVal, ListElt:=NewListElt);
        Add(eVect, eRec);
      od;
      Add(TheRetMat, eVect);
    od;
    return rec(nbLine:=nbLine, nbCol:=nbCol, TheMat:=TheRetMat);
  end;
  DoHomotopy:=function(jRank, TheVector)
    local TheNewVector, eEnt, NewListElt, eRec, ThePreImage, TheListReturn;
    TheNewVector:=[];
    for eEnt in TheVector
    do
      NewListElt:=List(eEnt.ListElt, x->Image(phi, x));
      eRec:=rec(ListVal:=eEnt.ListVal, ListElt:=NewListElt);
      Add(TheNewVector, eRec);
    od;
    ThePreImage:=TheResol.DoHomotopy(jRank, TheNewVector);
    TheListReturn:=[];
    for eEnt in ThePreImage
    do
      NewListElt:=List(eEnt.ListElt, x->Image(phiRev, x));
      eRec:=rec(ListVal:=eEnt.ListVal, ListElt:=NewListElt);
      Add(TheListReturn, eRec);
    od;
    return TheListReturn;
  end;
  GetDimension:=function(iRank)
    if iRank=0 then
      return Length(TheResol.GetDifferentiation(1).TheMat[1]);
    fi;
    return Length(TheResol.GetDifferentiation(iRank).TheMat);
  end;
  return rec(GRP:=GRP, 
             GRPresol:=TheResol.GRP, 
             GetMatrix:=GetMatrix,
             GetDimension:=GetDimension, 
             DoHomotopy:=DoHomotopy,
             IsInKernel:=IsInKernel);
end;



TheResolutionMoveToOtherGroupTwisted:=function(TheResol, GRP, RotSubgroup, kLevel)
  local phi, ListGens, ImageListGens, phiRev, IsInKernel, GetMatrix, DoHomotopy, GetDimension, kLevelEffect, TheSign;
  phi:=IsomorphismGroups(GRP, TheResol.GRP);
  ListGens:=GeneratorsOfGroup(GRP);
  ImageListGens:=List(ListGens, x->Image(phi, x));
  phiRev:=GroupHomomorphismByImagesNC(TheResol.GRP, GRP, ImageListGens, ListGens);
  kLevelEffect:=Maximum(kLevel, 1);
  TheResol.Initialization(kLevelEffect);
  IsInKernel:=function(jRank, TheVector)
    local eVal, TheProd;
    if jRank=0 then
      eVal:=TheVector[1];
      if Sum(eVal.ListVal)<>0 then
        return false;
      else
        return true;
      fi;
    else
      TheProd:=VectorMatrixGmoduleMultiplication(TheVector, GetMatrix(jRank));
      return IsZeroGmoduleVector(TheProd);
    fi;
  end;
  TheSign:=function(eElt)
    if eElt in RotSubgroup then
      return 1;
    else
      return -1;
    fi;
  end;
  GetMatrix:=function(jRank)
    local nbLine, nbCol, TheRetMat, eLine, eVect, eEnt, NewListElt, eRec, TheDiff, NewListVal;
    TheDiff:=TheResol.GetDifferentiation(jRank);
    nbLine:=TheDiff.nbLine;
    nbCol:=TheDiff.nbCol;
    TheRetMat:=[];
    for eLine in TheDiff.TheMat
    do
      eVect:=[];
      for eEnt in eLine
      do
        NewListElt:=List(eEnt.ListElt, x->Image(phiRev, x));
        NewListVal:=List([1..Length(eEnt.ListVal)], x->eEnt.ListVal[x]*TheSign(NewListElt[x]));
        eRec:=rec(ListVal:=NewListVal, ListElt:=NewListElt);
        Add(eVect, eRec);
      od;
      Add(TheRetMat, eVect);
    od;
    return rec(nbLine:=nbLine, nbCol:=nbCol, TheMat:=TheRetMat);
  end;
  DoHomotopy:=function(jRank, TheVector)
    local TheNewVector, eEnt, NewListElt, eRec, ThePreImage, TheListReturn, NewListVal;
    TheNewVector:=[];
    for eEnt in TheVector
    do
      NewListElt:=List(eEnt.ListElt, x->Image(phi, x));
      NewListVal:=List([1..Length(eEnt.ListElt)], x->eEnt.ListVal[x]*TheSign(eEnt.ListElt[x]));
      eRec:=rec(ListVal:=NewListVal, ListElt:=NewListElt);
      Add(TheNewVector, eRec);
    od;
    ThePreImage:=TheResol.DoHomotopy(jRank, TheNewVector);
    TheListReturn:=[];
    for eEnt in ThePreImage
    do
      NewListElt:=List(eEnt.ListElt, x->Image(phiRev, x));
      NewListVal:=List([1..Length(eEnt.ListVal)], x->eEnt.ListVal[x]*TheSign(NewListElt[x]));
      eRec:=rec(ListVal:=NewListVal, ListElt:=NewListElt);
      Add(TheListReturn, eRec);
    od;
    return TheListReturn;
  end;
  GetDimension:=function(iRank)
    if iRank=0 then
      return Length(TheResol.GetDifferentiation(1).TheMat[1]);
    fi;
    return Length(TheResol.GetDifferentiation(iRank).TheMat);
  end;
  return rec(GRP:=GRP, 
             GRPresol:=TheResol.GRP, 
             GetMatrix:=GetMatrix,
             GetDimension:=GetDimension, 
             DoHomotopy:=DoHomotopy,
             IsInKernel:=IsInKernel);
end;





GetPeriodicForS3:=function()
  local GRP, TheMat1, TheMat2, TheMat3, TheMat4;
  GRP:=SymmetricGroup(3);
  TheMat1:=rec( nbLine := 2, nbCol := 1, 
    TheMat := [ [ rec( ListVal := [ -1, 1 ], ListElt := [ (), (2,3) ] ) ], 
                [ rec( ListVal := [ -1, 1 ], ListElt := [ (), (1,2) ] ) ] ] );
  TheMat2:=rec( nbLine := 2, nbCol := 2, 
  TheMat := [ [ rec( ListVal := [  ], ListElt := [  ] ), 
          rec( ListVal := [ 1, 1 ], ListElt := [ (), (1,2) ] ) ], 
      [ rec( ListVal := [ 1, -1, -1 ], ListElt := [ (2,3), (1,3,2), (1,2,3) ] 
             ), 
          rec( ListVal := [ 1, -1, 1 ], ListElt := [ (), (2,3), (1,2,3) ] ) ] 
     ] );
  TheMat3:=rec( nbLine := 1, nbCol := 2, 
  TheMat := [ [ rec( ListVal := [ 1, 1, -1, -1 ], ListElt := 
                [ (), (1,2), (1,3,2), (1,2,3) ] ), 
          rec( ListVal := [ -1, 1, -1, 1 ], 
              ListElt := [ (), (2,3), (1,2), (1,2,3) ] ) ] ] );
  TheMat4:=rec( nbLine := 1, nbCol := 1, 
    TheMat := [ [ rec( ListVal := [ 1, 1, 1, 1, 1, 1 ], 
              ListElt := [ (), (2,3), (1,2), (1,3,2), (1,2,3), (1,3) ])]]);
  return rec(GRP:=GRP, 
             ListMatrix:=[TheMat1, TheMat2, TheMat3, TheMat4]);
end;




ResolutionPeriodic:=function(TheInfo)
  local nbMatrix, GetDifferentiation, DoHomotopy, Initialization, GetDimension;
  nbMatrix:=Length(TheInfo.ListMatrix);
  GetDifferentiation:=function(iRank)
    local TheRes;
    TheRes:=iRank mod nbMatrix;
    if TheRes=0 then
      return TheInfo.ListMatrix[nbMatrix];
    fi;
    return TheInfo.ListMatrix[TheRes];
  end;
  Initialization:=function(kLevel)
    # there is nothing to inialize here
  end;
  DoHomotopy:=function(kLevel, TheVect)
    if kLevel>0 and IsZeroReducedGmoduleVector(VectorMatrixGmoduleMultiplication(TheVect, GetDifferentiation(kLevel)))=false then
      Print("Error in homotopy calling for ResolutionPeriodic\n");
      Print(NullMat(5));
    fi;
    return GMOD_SolutionMatrixMultiplication(TheVect, GetDifferentiation(kLevel+1), TheInfo.GRP);
  end;
  GetDimension:=function(kLevel)
    if kLevel=0 then
      return GetDifferentiation(1).nbCol;
    fi;
    return GetDifferentiation(kLevel).nbLine;
  end;
  return rec(GRP:=TheInfo.GRP, 
             GetDifferentiation:=GetDifferentiation,
             Initialization:=Initialization, 
             GetDimension:=GetDimension, 
             DoHomotopy:=DoHomotopy);
end;


InformationResolutionCyclic:=function(n)
  local eGen, GRP, eElt, ListPower, i, TheMat1, TheMat2;
  eGen:=PermList(Concatenation([2..n], [1]));
  GRP:=Group([eGen]);
  eElt:=();
  ListPower:=[];
  for i in [1..n]
  do
    Add(ListPower, eElt);
    eElt:=eElt*eGen;
  od;
  TheMat1:=rec( nbLine := 1, nbCol := 1, 
    TheMat := [[ rec(ListVal:=[1,-1], ListElt:=[(),eGen]) ]]);
  TheMat2:=rec( nbLine := 1, nbCol := 1, 
    TheMat := [[ rec(ListVal:=ListWithIdenticalEntries(n,1), ListElt:=ListPower)]]);
  return rec(GRP:=GRP, 
             ListMatrix:=[TheMat1, TheMat2]);
end;





#
# this function is hand made for some special groups
# acting on some planar graphs with following requirements:
# --only one orbit of vertices, edge, face
# --stabilizer of vertices, edge face are cyclic
GetResolutionPlanGraph:=function(PL, TheCallG)
  local GRA, kAvailable, ListFaces, ListFacesRed, LN, TheStabVert, TheStabEdge, TheStabFace, GetDifferentialZmatrix, GetImageGmodule, GetHomotopy, eAdj, ListEdgeMappings, ListVertMappings, ListFaceMappings, eRepr, eEdgeRed, GetDifferentiationDi, DoHomotopyD0, GetDifferentiationD0, GetDifferentiationD1, eVertCan, eEdgeCan, eFaceCan, eFaceRedCan, ListEdgesRed, ListEdgesSet, MatrixDifferentialEdgeVert, MatrixDifferentialVertFace, MatrixDifferentialFaceEdge, DoHomotopy, eDiffFace, eDiffVert, eDiffEdge, eRepr1, eGenVert, eGenEdge, eGenFace, eVect, GetDifferentiation, eMultiplicationVert1, eMultiplicationVert2, eMultiplicationEdge1, eMultiplicationEdge2, eMultiplicationFace1, eMultiplicationFace2, FuncSignature, nbFace, eEdge, nbVert, eRec, eDE, iVert, nbEdge, ListEltFace, ListValFace, GetIEdgeSign, ListEdges, eFaceRed, eFace, ListDifferentiation, ListStatus, Initialization, DoDifferentiationD0, ListElementStabVert, ListElementStabFace, eElt, DoDifferentiationDi, DoDifferentiation, IsInKernel, GetDimension;
  GRA:=PlanGraphToGRAPE(PL);
  nbVert:=Length(PL);
  ListEdges:=__EdgeSet(PL);
  ListEdgesRed:=List(ListEdges, x->[x[1][1], x[2][1]]);
  ListEdgesSet:=List(ListEdgesRed, Set);
  nbEdge:=Length(ListEdges);
  ListFaces:=__FaceSet(PL);
  ListFacesRed:=List(ListFaces, x->Set(List(x, y->y[1])));
  nbFace:=Length(ListFaces);
  eAdj:=Adjacency(GRA, 1)[1];
  eVertCan:=1;
  eEdgeCan:=[1,eAdj];
  eFaceCan:=ListFaces[1];
  eFaceRedCan:=ListFacesRed[1];
  TheStabVert:=Stabilizer(TheCallG, eVertCan, OnPoints);
  TheStabEdge:=Stabilizer(TheCallG, eEdgeCan, OnSets);
  TheStabFace:=Stabilizer(TheCallG, eFaceRedCan, OnSets);
  ListVertMappings:=[];
  for iVert in [1..nbVert]
  do
    eRepr:=RepresentativeAction(TheCallG, eVertCan, iVert, OnPoints);
    Add(ListVertMappings, eRepr);
  od;
  ListEdgeMappings:=[];
  for eEdgeRed in ListEdgesRed
  do
    eRepr:=RepresentativeAction(TheCallG, eEdgeCan, eEdgeRed, OnTuples);
    Add(ListEdgeMappings, eRepr);
  od;
  ListFaceMappings:=[];
  for eFaceRed in ListFacesRed
  do
    eRepr:=RepresentativeAction(TheCallG, eFaceRedCan, eFaceRed, OnSets);
    Add(ListFaceMappings, eRepr);
  od;
  eDiffVert:=rec(ListVal:=ListWithIdenticalEntries(nbFace,1), ListElt:=ListFaceMappings);
  eRepr1:=RepresentativeAction(TheCallG, eVertCan, eAdj, OnPoints);
  eDiffEdge:=rec(ListVal:=[1,-1],ListElt:=[(), eRepr1]);
  GetIEdgeSign:=function(eDE)
    local iEdge;
    for iEdge in [1..nbEdge]
    do
      if ListEdges[iEdge][1]=eDE then
        return rec(iEdge:=iEdge, eSign:=1);
      fi;
      if ListEdges[iEdge][2]=eDE then
        return rec(iEdge:=iEdge, eSign:=-1);
      fi;
    od;
    Print(NullMat(5));
  end;
  ListValFace:=[];
  ListEltFace:=[];
  for eDE in eFaceCan
  do
    eRec:=GetIEdgeSign(eDE);
    Add(ListValFace, eRec.eSign);
    Add(ListEltFace, ListEdgeMappings[eRec.iEdge]);
  od;
  eDiffFace:=rec(ListVal:=ListValFace, ListElt:=ListEltFace);
  eGenVert:=GeneratorsOfGroup(TheStabVert)[1];
  eGenEdge:=GeneratorsOfGroup(TheStabEdge)[1];
  eGenFace:=GeneratorsOfGroup(TheStabFace)[1];
  ListElementStabVert:=[];
  for eElt in TheStabVert
  do
    Add(ListElementStabVert, eElt);
  od;
  ListElementStabFace:=[];
  for eElt in TheStabFace
  do
    Add(ListElementStabFace, eElt);
  od;
  eMultiplicationVert1:=rec(ListVal:=[1,-1], ListElt:=[(), eGenVert]);
  eMultiplicationVert2:=rec(ListVal:=ListWithIdenticalEntries(Length(ListElementStabVert), 1), ListElt:=ListElementStabVert);

  eMultiplicationEdge1:=rec(ListVal:=[1,1], ListElt:=[(), eGenEdge]); # we apply the signature operation
  eMultiplicationEdge2:=rec(ListVal:=[1,-1], ListElt:=[(), eGenEdge]);

  eMultiplicationFace1:=rec(ListVal:=[1,-1], ListElt:=[(), eGenFace]);
  eMultiplicationFace2:=rec(ListVal:=ListWithIdenticalEntries(Length(ListElementStabFace), 1), ListElt:=ListElementStabFace);
  MatrixDifferentialFaceEdge:=[];
  for eFace in ListFaces
  do
    eVect:=ListWithIdenticalEntries(nbEdge,0);
    for eDE in eFace
    do
      eRec:=GetIEdgeSign(eDE);
      eVect[eRec.iEdge]:=eRec.eSign;
    od;
    Add(MatrixDifferentialFaceEdge, eVect);
  od;
  MatrixDifferentialEdgeVert:=[];
  for eEdge in ListEdges
  do
    eVect:=ListWithIdenticalEntries(nbVert,0);
    eVect[eEdge[1][1]]:=1;
    eVect[eEdge[2][1]]:=-1;
    Add(MatrixDifferentialEdgeVert, eVect);
  od;
  MatrixDifferentialVertFace:=[];
  for iVert in [1..nbVert]
  do
    eVect:=ListWithIdenticalEntries(nbFace,1);
    Add(MatrixDifferentialVertFace, eVect);
  od;
  FuncSignature:=function(iRank, eElt)
    local iRankMod;
    iRankMod:=iRank mod 3;
    if iRankMod=1 then
      # edge case
      if eElt=() then
        return 1;
      fi;
      return -1;
    else
      return 1;
    fi;
  end;
  Initialization:=function(kLevel)
    local iRank, TheMat;
    kAvailable:=kLevel;
    ListDifferentiation:=[];
    ListStatus:=[];
    for iRank in [0..kLevel]
    do
      Add(ListStatus, NullMat(kLevel+1, kLevel+1));
      Add(ListDifferentiation, GMOD_GetZeroMatrix(kLevel+1, kLevel+1).TheMat);
    od;
    for iRank in [1..kLevel]
    do
      TheMat:=GetDifferentiation(iRank);
    od;
  end;
  GetDifferentiationD0:=function(iRank, iLevel)
    local iRankMod, eMultiplication;
    if iLevel=0 then
      Print("Wrong call do GetDifferentiationD0, please retry\n");
      Print(NullMat(5));
    fi;
    iRankMod:=iRank mod 3;
    if iRankMod=0 then
      if iLevel mod 2=1 then
        return eMultiplicationVert1;
      else
        return eMultiplicationVert2;
      fi;
    else
      if iRankMod=1 then
        if iLevel mod 2=1 then
          return eMultiplicationEdge1;
        else
          return eMultiplicationEdge2;
        fi;
      else
        if iLevel mod 2=1 then
          return eMultiplicationFace1;
        else
          return eMultiplicationFace2;
        fi;
      fi;
    fi;
  end;
  DoDifferentiationD0:=function(iRank, iLevel, TheElt)
    return GmoduleMultiplication(GetDifferentiationD0(iRank, iLevel), TheElt);
  end;
  DoHomotopyD0:=function(iRank, iLevel, TheElt)
    local iRankMod, TheRelStab, eMultiplication, ReprRightCoset, ListNewVals, ListNewElts, nbCos, eCos, iCos, eSingElt, eSol, TheReturn;
    if iLevel>0 and IsZeroReducedGmoduleElt(DoDifferentiationD0(iRank, iLevel, TheElt))=false then
      Print("INCONSISTENCY IN CALL in call to DoHomotopyD0\n");
      Print(NullMat(5));
    fi;
    iRankMod:=iRank mod 3;
    if iRankMod=0 then
      TheRelStab:=TheStabVert;
      if iLevel mod 2=0 then
        eMultiplication:=eMultiplicationVert1;
      else
        eMultiplication:=eMultiplicationVert2;
      fi;
    else
      if iRankMod=1 then
        TheRelStab:=TheStabEdge;
        if iLevel mod 2=0 then
          eMultiplication:=eMultiplicationEdge1;
        else
          eMultiplication:=eMultiplicationEdge2;
        fi;
      else
        TheRelStab:=TheStabFace;
        if iLevel mod 2=0 then
          eMultiplication:=eMultiplicationFace1;
        else
          eMultiplication:=eMultiplicationFace2;
        fi;
      fi;
    fi;
    ReprRightCoset:=RightCosetExpression(TheRelStab, TheElt);
    ListNewVals:=[];
    ListNewElts:=[];
    nbCos:=Length(ReprRightCoset);
    for iCos in [1..nbCos]
    do
      eCos:=ReprRightCoset[iCos].eCos;
      eSingElt:=rec(ListVal:=ReprRightCoset[iCos].ListVal, ListElt:=ReprRightCoset[iCos].ListElt);
      eSol:=GMOD_SolutionMultiplication(eSingElt, eMultiplication, TheRelStab);
      Append(ListNewVals, eSol.ListVal);
      Append(ListNewElts, List(eSol.ListElt, x->x*eCos));
    od;
    TheReturn:=ReducedGmoduleForm(rec(ListVal:=ListNewVals, ListElt:=ListNewElts));
    if IsEqualReducedGmoduleElt(TheElt, DoDifferentiationD0(iRank, iLevel+1, TheReturn))=false then
      Print("The homotopy was NOT correct, please correct yourself\n");
      Print(NullMat(5));
    fi;
    return TheReturn;
  end;
  GetDifferentiationD1:=function(iRank, iLevel)
    local eMatElt1, eMatElt2, eProd, eImg3, iRankMod, TheResult;
    if ListStatus[iRank+1][iLevel+1][2]=1 then
      return ListDifferentiation[iRank+1][iLevel+1][2];
    fi;
    if iRank<=0 then
      Print("Inconsistency at this stage\n");
      Print("Wrong iRank call\n");
      Print(NullMat(5));
    fi;
    if iLevel=0 then
      iRankMod:=iRank mod 3;
      if iRankMod=0 then
        return eDiffVert;
      else
        if iRankMod=1 then
          return eDiffEdge;
        else
          return eDiffFace;
        fi;
      fi;
    fi;
    eMatElt1:=GetDifferentiationD0(iRank, iLevel);
    eMatElt2:=GetDifferentiationD1(iRank, iLevel-1);
    eProd:=GmoduleMultiplication(eMatElt2, eMatElt1);
    eImg3:=rec(ListElt:=eProd.ListElt, ListVal:=-eProd.ListVal);
    TheResult:=DoHomotopyD0(iRank-1, iLevel-1, eImg3);
    ListDifferentiation[iRank+1][iLevel+1][2]:=TheResult;
    ListStatus[iRank+1][iLevel+1][2]:=1;
    return TheResult;
  end;
  DoDifferentiationDi:=function(iRank, iLevel, i, eElt)
    return GmoduleMultiplication(GetDifferentiationDi(iRank, iLevel, i), eElt);
  end;
  GetDifferentiationDi:=function(iRank, iLevel, i)
    local eSum, iH, eImg1, eImg2, TheResult, eMatElt1, eMatElt2, eProd;
    if ListStatus[iRank+1][iLevel+1][i+1]=1 then
      return ListDifferentiation[iRank+1][iLevel+1][i+1];
    fi;
    if i > iRank then
      Print("This cannot work\n");
      Print(NullMat(5));
    fi;
    if i=0 then
      return GetDifferentiationD0(iRank, iLevel);
    fi;
    if i=1 then
      return GetDifferentiationD1(iRank, iLevel);
    fi;
    eSum:=GMOD_GetZero();
    for iH in [0..i-1]
    do
      if i-iH>=0 and iLevel-1+iH >=0 then
        eMatElt1:=GetDifferentiationDi(iRank, iLevel, iH);
        eMatElt2:=GetDifferentiationDi(iRank-iH, iLevel-1+iH, i-iH);
        eProd:=GmoduleMultiplication(eMatElt2, eMatElt1);
        eSum:=GmoduleAddition(eSum, eProd);
      fi;
    od;
    TheResult:=DoHomotopyD0(iRank-i, iLevel+i-2, rec(ListVal:=-eSum.ListVal, ListElt:=eSum.ListElt));
    ListDifferentiation[iRank+1][iLevel+1][i+1]:=TheResult;
    ListStatus[iRank+1][iLevel+1][i+1]:=1;
    return TheResult;
  end;
  # The terms are R0, R1, R2, ....
  # in the resolution
  DoDifferentiation:=function(kLevel, TheVector)
    return VectorMatrixGmoduleMultiplication(TheVector, GetDifferentiation(kLevel));
  end;
  IsInKernel:=function(kLevel, TheVector)
    local eVal, TheProd;
    if kLevel=0 then
      eVal:=TheVector[1];
      if Sum(eVal.ListVal)<>0 then
        return false;
      else
        return true;
      fi;
    else
      TheProd:=DoDifferentiation(kLevel, TheVector);
      return IsZeroGmoduleVector(TheProd);
    fi;
  end;
  GetDifferentiation:=function(kLevel)
    local iComp, eMatElt, iH, TheMatrixReturn;
    TheMatrixReturn:=GMOD_GetZeroMatrix(kLevel+1, kLevel);
    if kLevel>kAvailable then
      Print("GetResolutionPlanGraph, update of resolution to kLevel=", kLevel, "\n");
      Initialization(kLevel);
    fi;
    for iComp in [0..kLevel]
    do
      for iH in [0..kLevel]
      do
        if (iComp + iH <= kLevel and iH>0) or (iComp > 0 and iH=0) then
          eMatElt:=GetDifferentiationDi(kLevel-iComp, iComp, iH);
          TheMatrixReturn.TheMat[iComp+1][iComp+iH]:=eMatElt;
        fi;
      od;
    od;
    return TheMatrixReturn;
  end;
  DoHomotopy:=function(kLevel, eModuleElt)
    local kLevelMod, TheMatrix, WorkingModuleElt, TheReturn, nbTarget, nbSource, TheVect, nbEnt, iEnt, eElt, eVal, iVert, eEdgeSet, pos, eMapping, eQuot, eNewVal, eNewListVal, eNewListElt, eHomotopElt, iCol, iH, i, eFaceRed, eSol, eMatElt, DoCheck;
    DoCheck:=false;
    if DoCheck=true then
      if Length(eModuleElt)<>kLevel+1 then
        Print("Not correct, rework\n");
        Print(NullMat(5));
      fi;
      if IsInKernel(kLevel, eModuleElt)=false then
        Print("We cannot do homotopy for plangraph\n");
        Print(NullMat(5));
      fi;
       if GMOD_IsItGmoduleVector(eModuleElt, TheCallG)=false then
       Print("The vector is not in the right space, please correct\n");
        Print(NullMat(5));
      fi;
    fi;
    kLevelMod:=kLevel mod 3;
    if kLevelMod=0 then
      TheMatrix:=MatrixDifferentialEdgeVert;
    else
      if kLevelMod=1 then
        TheMatrix:=MatrixDifferentialFaceEdge;
      else
        TheMatrix:=MatrixDifferentialVertFace;
      fi;
    fi;
    WorkingModuleElt:=StructuralCopy(eModuleElt);
    TheReturn:=GMOD_GetZeroVector(kLevel+2);
    nbTarget:=Length(TheMatrix[1]);
    nbSource:=Length(TheMatrix);
    TheVect:=ListWithIdenticalEntries(nbTarget, 0);
    nbEnt:=Length(eModuleElt[1].ListVal);
    for iEnt in [1..nbEnt]
    do
      eElt:=eModuleElt[1].ListElt[iEnt];
      eVal:=eModuleElt[1].ListVal[iEnt];
      if kLevelMod=0 then
        iVert:=OnPoints(eVertCan, eElt);
        TheVect[iVert]:=TheVect[iVert]+eVal;
      fi;
      if kLevelMod=1 then
        eEdgeSet:=OnSets(eEdgeCan, eElt);
        pos:=Position(ListEdgesSet, eEdgeSet);
        eMapping:=ListEdgeMappings[pos];
        eQuot:=eElt*(eMapping^(-1));
        if eQuot=() then
          eNewVal:=eVal;
        else
          eNewVal:=-eVal;
        fi;
        TheVect[pos]:=TheVect[pos]+eNewVal;
      fi;
      if kLevelMod=2 then
        eFaceRed:=OnSets(eFaceRedCan, eElt);
        pos:=Position(ListFacesRed, eFaceRed);
        TheVect[pos]:=TheVect[pos]+eVal;
      fi;
    od;
    eSol:=SolutionIntMat(TheMatrix, TheVect);
    if eSol=fail then
      Print("Bug or wrong call to the function, you choose and debug\n");
      Print(NullMat(5));
    fi;
    eNewListVal:=[];
    eNewListElt:=[];
    for i in [1..Length(eSol)]
    do
      if eSol[i]<>0 then
        if kLevelMod=0 then
          Add(eNewListVal, eSol[i]);
          Add(eNewListElt, ListEdgeMappings[i]);
        fi;
        if kLevelMod=1 then
          Add(eNewListVal, eSol[i]);
          Add(eNewListElt, ListFaceMappings[i]);
        fi;
        if kLevelMod=2 then
          Add(eNewListVal, eSol[i]);
          Add(eNewListElt, ListVertMappings[i]);
        fi;
      fi;
    od;
    TheReturn[1]:=rec(ListVal:=eNewListVal, ListElt:=eNewListElt);
    for iH in [1..kLevel+1]
    do
      eElt:=DoDifferentiationDi(kLevel+1, 0, iH, TheReturn[1]);
      WorkingModuleElt[iH]:=GmoduleSoustraction(WorkingModuleElt[iH], eElt);
    od;
    for iCol in [1..kLevel+1]
    do
      eHomotopElt:=DoHomotopyD0(kLevel+1-iCol, iCol-1, WorkingModuleElt[iCol]);
      TheReturn[iCol+1]:=eHomotopElt;
      for iH in [0..kLevel]
      do
        if iCol+iH<=kLevel+1 and iCol+iH>=0 then
          eElt:=DoDifferentiationDi(kLevel+1-iCol, iCol, iH, eHomotopElt);
          WorkingModuleElt[iCol+iH]:=GmoduleSoustraction(WorkingModuleElt[iCol+iH], eElt);
        fi;
      od;
    od;
    if DoCheck=true then
      if IsZeroReducedGmoduleVector(WorkingModuleElt)=false then
        Print("We should panic, just maybe\n");
        Print(NullMat(5));
      fi;
      if IsEqualGmoduleVector(DoDifferentiation(kLevel+1, TheReturn), eModuleElt)=false then
        Print("Non correct homotopy computation, please panic 1\n");
        Print(NullMat(5));
      fi;
    fi;
    return TheReturn;
  end;
  GetDimension:=function(iRank)
    return iRank+1;
  end;
  return rec(GRP:=TheCallG, 
             GetDimension:=GetDimension, 
             DoHomotopy:=DoHomotopy, 
             Initialization:=Initialization, 
             GetDifferentiation:=GetDifferentiation);
end;


GetResolutionA5:=function()
  local PL, GRA, GRP, LN, TheA5;
  PL:=ArchimedeanPolyhedra("Icosahedron");
  GRA:=PlanGraphToGRAPE(PL);
  GRP:=AutGroupGraph(GRA);
  LN:=NormalSubgroups(GRP);
  TheA5:=First(LN, x->Order(x)=60);
  return GetResolutionPlanGraph(PL, TheA5);
end;


GetResolutionA4:=function()
  local PL, GRA, GRP, LN, TheA4;
  PL:=ArchimedeanPolyhedra("Tetrahedron");
  GRA:=PlanGraphToGRAPE(PL);
  GRP:=AutGroupGraph(GRA);
  LN:=NormalSubgroups(GRP);
  TheA4:=First(LN, x->Order(x)=12);
  return GetResolutionPlanGraph(PL, TheA4);
end;


GetResolutionS4:=function()
  local PL, GRA, GRP, eLN, LN, TheS4, O;
  PL:=ArchimedeanPolyhedra("Cube");
  GRA:=PlanGraphToGRAPE(PL);
  GRP:=AutGroupGraph(GRA);
  LN:=NormalSubgroups(GRP);
  TheS4:=SymmetricGroup(4);
  for eLN in LN
  do
    if Order(eLN)=24 and IsomorphismGroups(eLN, TheS4)<>fail then
      O:=Orbits(eLN, [1..Length(PL)], OnPoints);
      if Length(O)=1 then
        return GetResolutionPlanGraph(PL, eLN);
      fi;
    fi;
  od;
end;




GetResolutionFromNormalAndQuotient:=function(TheBigGroup, TheSubgroup, TheResolSubgroup, TheResolQuotient)
  local kAvailable, QuotInfo, eQuot, TheQuotient, phi, ListGens, ImageListGens, phiRed, DoHomotopyD0, GetDifferentiation, DoHomotopy, ListStatus, ListDifferentiation, ListBeginDimension, ListEndDimension, ListMatricesQuotient, Initialization, GetDimension, ListMatricesSubgroup, DoDifferentiationDi, GetDifferentiationD0, GetDifferentiationD1, GetDifferentiationDi, PreHomotopyD1, GetMatricesQuotient, DoHomotopySubgroup, DoDifferentiationD0, FuncInsert, ResolSubgroupMapped, DoDifferentiation, ListDimResolSubgroup, ListDimResolQuotient;
  QuotInfo:=QuotientPermutationGroup(TheBigGroup, TheSubgroup);
  ListGens:=GeneratorsOfGroup(TheBigGroup);
  eQuot:=QuotInfo.Quotient;
  TheQuotient:=TheResolQuotient.GRP;
  phi:=IsomorphismGroups(eQuot, TheQuotient);
  ImageListGens:=List(ListGens, x->Image(phi, Image(QuotInfo.CanonicSurjection, x)));
  phiRed:=GroupHomomorphismByImagesNC(TheBigGroup, TheQuotient, ListGens, ImageListGens);
  DoHomotopySubgroup:=function(kLevel, TheVect)
    local ListRightCoset, DimOutput, ListPreImage, nbCos, eCos, TheSingVect, PreImage1, iCol, iVal, iCos;
    ListRightCoset:=RightCosetVectorExpression(TheSubgroup, TheVect);
    DimOutput:=ListMatricesSubgroup[kLevel+1].nbLine;
    ListPreImage:=GMOD_GetZeroVector(DimOutput);
    nbCos:=Length(ListRightCoset);
    for iCos in [1..nbCos]
    do
      eCos:=ListRightCoset[iCos].eCos;
      TheSingVect:=ListRightCoset[iCos].TheVect;
      PreImage1:=ResolSubgroupMapped.DoHomotopy(kLevel, TheSingVect);
      for iCol in [1..DimOutput]
      do
        for iVal in [1..Length(PreImage1[iCol].ListElt)]
        do
          Add(ListPreImage[iCol].ListVal, PreImage1[iCol].ListVal[iVal]);
          Add(ListPreImage[iCol].ListElt, PreImage1[iCol].ListElt[iVal]*eCos);
        od;
      od;
    od;
    return ListPreImage;
  end;
  GetDifferentiationD0:=function(iRank, iLevel)
    local eBeginSource, eEndSource, eBeginTarget, eEndTarget, dimSource, dimTarget, TheMatRed, TheSoughtMat, TheBigMat, i, iLine, iCol, iLineBig, iColBig;
    if iLevel<=0 then
      Print("Wrong call to GetDifferentiationD0\n");
      Print(NullMat(5));
    fi;
    eBeginSource:=ListBeginDimension[iRank+1][iLevel+1];
    eEndSource:=ListEndDimension[iRank+1][iLevel+1];
    eBeginTarget:=ListBeginDimension[iRank+1][iLevel];
    eEndTarget:=ListEndDimension[iRank+1][iLevel];
    dimSource:=1+eEndSource-eBeginSource;
    dimTarget:=1+eEndTarget-eBeginTarget;
    if ListStatus[iRank+1][iLevel+1][1]=1 then
      TheMatRed:=List(ListDifferentiation[iRank+iLevel].TheMat{[eBeginSource..eEndSource]}, x->x{[eBeginTarget..eEndTarget]});
      return rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=TheMatRed);
    fi;
    TheSoughtMat:=ListMatricesSubgroup[iLevel];
    TheBigMat:=GMOD_GetZeroMatrix(dimSource, dimTarget);
    for i in [1..ListDimResolSubgroup[iRank+1]]
    do
      for iLine in [1..ListDimResolQuotient[iLevel+1]]
      do
        for iCol in [1..ListDimResolQuotient[iLevel]]
        do
          iLineBig:=iLine+ListDimResolQuotient[iLevel+1]*(i-1);
          iColBig:=iCol+ListDimResolQuotient[iLevel]*(i-1);
          TheBigMat.TheMat[iLineBig][iColBig]:=TheSoughtMat.TheMat[iLine][iCol];
        od;
      od;
    od;
    ListStatus[iRank+1][iLevel+1][1]:=1;
    for iLine in [1..dimSource]
    do
      for iCol in [1..dimTarget]
      do
        ListDifferentiation[iRank+iLevel].TheMat[iLine+eBeginSource-1][iCol+eBeginTarget-1]:=TheBigMat.TheMat[iLine][iCol];
      od;
    od;
    return TheBigMat;
  end;
  DoDifferentiationD0:=function(iRank, iLevel, TheVect)
    return VectorMatrixGmoduleMultiplication(TheVect, GetDifferentiationD0(iRank, iLevel));
  end;
  DoHomotopyD0:=function(iRank, iLevel, eVect)
    local eVectRet, p, eDimBegin, eDimEnd, eVectRed, ePreImage, TheDimQuot, TheDimSub;
    if iLevel>0 and IsZeroReducedGmoduleVector(DoDifferentiationD0(iRank, iLevel, eVect))=false then
      Print("INCONSISTENCY IN CALL in call to DoHomotopyD0\n");
      Print(NullMat(5));
    fi;
    eVectRet:=[];
    TheDimQuot:=ListDimResolQuotient[iLevel+1];
    TheDimSub:=ListDimResolSubgroup[iRank+1];
    for p in [1..TheDimSub]
    do
      eDimBegin:=1+(p-1)*TheDimQuot;
      eDimEnd:=p*TheDimQuot;
      eVectRed:=eVect{[eDimBegin..eDimEnd]};
      ePreImage:=DoHomotopySubgroup(iLevel, eVectRed);
      Append(eVectRet, ePreImage);
    od;
    if IsEqualReducedGmoduleVector(eVect, DoDifferentiationD0(iRank, iLevel+1, eVectRet))=false then
      Print("The homotopy failed, sorry for that, please correct\n");
      Print(NullMat(5));
    fi;
    return eVectRet;
  end;
  ListMatricesQuotient:=[];
  GetMatricesQuotient:=function(kLevel)
    local iK, eMat, nbSource, nbTarget, TheMatrix, iLine, iCol, NewListElt, eEnt, iRank;
    TheResolQuotient.Initialization(kLevel);
    ListDimResolQuotient:=[];
    for iRank in [0..kLevel]
    do
      Add(ListDimResolQuotient, TheResolQuotient.GetDimension(iRank));
    od;
    if ListDimResolQuotient[1]<>1 then
      Print("The dimension of the first space should be 1\n");
      Print("If it is not 1 then it is easy to modify the resolution\n");
      Print("So that the first dimension is 1\n");
      Print(NullMat(5));
    fi;
    for iK in [1..kLevel]
    do
      eMat:=TheResolQuotient.GetDifferentiation(iK);
      nbSource:=eMat.nbLine;
      nbTarget:=eMat.nbCol;
      TheMatrix:=GMOD_GetZeroMatrix(iK+1, iK);
      for iLine in [1..nbSource]
      do
        for iCol in [1..nbTarget]
        do
          NewListElt:=List(eMat.TheMat[iLine][iCol].ListElt, x->PreImagesRepresentative(phiRed, x));
          eEnt:=rec(ListVal:=eMat.TheMat[iLine][iCol].ListVal, ListElt:=NewListElt);
          TheMatrix.TheMat[iLine][iCol]:=eEnt;
        od;
      od;
      Add(ListMatricesQuotient, TheMatrix);
    od;
  end;
  PreHomotopyD1:=function(iRank, eVect)
    local ListReturn, ImageVect, eEnt, eRec, ThePreImage;
    ImageVect:=[];
    for eEnt in eVect
    do
      eRec:=rec(ListVal:=eEnt.ListVal, ListElt:=List(eEnt.ListElt, x->Image(phiRed, x)));
      Add(ImageVect, ReducedGmoduleForm(eRec));
    od;
    ThePreImage:=TheResolQuotient.DoHomotopy(iRank, ImageVect);
    ListReturn:=[];
    for eEnt in ThePreImage
    do
      eRec:=rec(ListVal:=eEnt.ListVal, ListElt:=List(eEnt.ListElt, x->PreImagesRepresentative(phiRed, x)));
      Add(ListReturn, eRec);
    od;
    return ListReturn;
  end;
  GetDimension:=function(kLevel)
    local RetDim, q, p, TheDim;
    if IsBound(ListEndDimension[1][1+kLevel]) then
      return ListEndDimension[1][1+kLevel];
    fi;
    RetDim:=0;
    for q in [0..kLevel]
    do
      p:=kLevel-q;
      TheDim:=ResolSubgroupMapped.GetDimension(p)*TheResolQuotient.GetDimension(p);
      RetDim:=RetDim+TheDim;
    od;
    return RetDim;
  end;  
  Initialization:=function(kLevel)
    local iRank, p, q, ePrevEnd, TheDim, TheMat;
    ResolSubgroupMapped:=TheResolutionMoveToOtherGroup(TheResolSubgroup, TheSubgroup, kLevel);
    kAvailable:=kLevel;
    ListDimResolSubgroup:=[];
    for iRank in [0..kLevel]
    do
      Add(ListDimResolSubgroup, ResolSubgroupMapped.GetDimension(iRank));
    od;
    ListMatricesSubgroup:=List([1..kLevel], x->ResolSubgroupMapped.GetMatrix(x));
    GetMatricesQuotient(kLevel);
    ListStatus:=[];
    ListDifferentiation:=[];
    ListBeginDimension:=NullMat(kLevel+1, kLevel+1);
    ListEndDimension:=NullMat(kLevel+1, kLevel+1);
#    Print("SubgroupQuotient, kLevel=", kLevel, "\n");
    for q in [0..kLevel]
    do
      for p in [0..kLevel-q]
      do
        if q=0 then
          ePrevEnd:=0;
        else
          ePrevEnd:=ListEndDimension[1+p+1][1+q-1];
        fi;
        TheDim:=ListDimResolSubgroup[q+1]*ListDimResolQuotient[p+1];
        ListBeginDimension[1+p][1+q]:=ePrevEnd+1;
        ListEndDimension[1+p][1+q]:=ePrevEnd+TheDim;
      od;
    od;
    for iRank in [0..kLevel]
    do
      Add(ListStatus, NullMat(kLevel+1, kLevel+1));
    od;
    for iRank in [1..kLevel]
    do
      Add(ListDifferentiation, GMOD_GetZeroMatrix(GetDimension(iRank), GetDimension(iRank-1)));
    od;
    for iRank in [1..kLevel]
    do
      TheMat:=GetDifferentiation(iRank);
    od;
  end;
  GetDifferentiationD1:=function(iRank, iLevel)
    local eBeginSource, eEndSource, eBeginTarget, eEndTarget, dimSource, dimTarget, TheBigMat, TheProd, TheOpp, NewMat, iLine, iCol, TheMatRed;
    eBeginSource:=ListBeginDimension[iRank+1][iLevel+1];
    eEndSource:=ListEndDimension[iRank+1][iLevel+1];
    eBeginTarget:=ListBeginDimension[iRank][iLevel+1];
    eEndTarget:=ListEndDimension[iRank][iLevel+1];
    dimSource:=1+eEndSource-eBeginSource;
    dimTarget:=1+eEndTarget-eBeginTarget;
    if ListStatus[iRank+1][iLevel+1][2]=1 then
      TheMatRed:=List(ListDifferentiation[iRank+iLevel].TheMat{[eBeginSource..eEndSource]}, x->x{[eBeginTarget..eEndTarget]});
      return rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=TheMatRed);
    fi;
    if iLevel=0 then
      TheBigMat:=ListMatricesQuotient[iRank];
    else
      TheProd:=MatrixMatrixGmoduleMultiplication(GetDifferentiationD0(iRank, iLevel), GetDifferentiationD1(iRank, iLevel-1));
      TheOpp:=MatrixGmoduleOpposite(TheProd);
      NewMat:=List(TheOpp.TheMat, x->DoHomotopyD0(iRank-1,iLevel-1,x));
      TheBigMat:=rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=NewMat);
    fi;
    ListStatus[iRank+1][iLevel+1][2]:=1;
    for iLine in [1..dimSource]
    do
      for iCol in [1..dimTarget]
      do
        ListDifferentiation[iRank+iLevel].TheMat[iLine+eBeginSource-1][iCol+eBeginTarget-1]:=TheBigMat.TheMat[iLine][iCol];
      od;
    od;
    return TheBigMat;
  end;
  DoDifferentiationDi:=function(iRank, iLevel, i, TheVector)
    return VectorMatrixGmoduleMultiplication(TheVector, GetDifferentiationDi(iRank, iLevel, i));
  end;
  GetDifferentiationDi:=function(iRank, iLevel, i)
    local eBeginSource, eEndSource, eBeginTarget, eEndTarget, dimSource, dimTarget, TheMatRed, eBeginTargetPrev, eEndTargetPrev, dimTargetPrev, ThePrevBigMat, iH, eMat1, eMat2, eProd, TheOpp, NewMat, TheBigMat, iLine, iCol;
    if i=0 then
      return GetDifferentiationD0(iRank, iLevel);
    fi;
    if i=1 then
      return GetDifferentiationD1(iRank, iLevel);
    fi;
    eBeginSource:=ListBeginDimension[iRank+1][iLevel+1];
    eEndSource:=ListEndDimension[iRank+1][iLevel+1];
    eBeginTarget:=ListBeginDimension[iRank+1-i][iLevel+i];
    eEndTarget:=ListEndDimension[iRank+1-i][iLevel+i];
    dimSource:=1+eEndSource-eBeginSource;
    dimTarget:=1+eEndTarget-eBeginTarget;
    if ListStatus[iRank+1][iLevel+1][i+1]=1 then
      TheMatRed:=List(ListDifferentiation[iRank+iLevel].TheMat{[eBeginSource..eEndSource]}, x->x{[eBeginTarget..eEndTarget]});
      return rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=TheMatRed);
    fi;
    eBeginTargetPrev:=ListBeginDimension[iRank+1-i][iLevel+i-1];
    eEndTargetPrev:=ListEndDimension[iRank+1-i][iLevel+i-1];
    dimTargetPrev:=1+eEndTargetPrev-eBeginTargetPrev;
    ThePrevBigMat:=GMOD_GetZeroMatrix(dimSource, dimTargetPrev);
    for iH in [0..i-1]
    do
      if i-iH>=0 and iLevel-1+iH >=0 then
        eMat1:=GetDifferentiationDi(iRank, iLevel, iH);
        eMat2:=GetDifferentiationDi(iRank-iH, iLevel-1+iH, i-iH);
        eProd:=MatrixMatrixGmoduleMultiplication(eMat1, eMat2);
        ThePrevBigMat:=MatrixGmoduleAddition(ThePrevBigMat, eProd);
      fi;
    od;
    TheOpp:=MatrixGmoduleOpposite(ThePrevBigMat);
    NewMat:=List(TheOpp.TheMat, x->DoHomotopyD0(iRank-i,iLevel+i-2,x));
    TheBigMat:=rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=NewMat);
    ListStatus[iRank+1][iLevel+1][i+1]:=1;
    for iLine in [1..dimSource]
    do
      for iCol in [1..dimTarget]
      do
        ListDifferentiation[iRank+iLevel].TheMat[iLine+eBeginSource-1][iCol+eBeginTarget-1]:=TheBigMat.TheMat[iLine][iCol];
      od;
    od;
    return TheBigMat;
  end;
  GetDifferentiation:=function(kLevel)
    local iComp, eMat, iH;
    if kLevel>kAvailable then
      Print("GetResolutionNormalQuotient, update of resolution to kLevel=", kLevel, "\n");
      Initialization(kLevel);
    fi;
    for iComp in [0..kLevel]
    do
      for iH in [0..kLevel]
      do
        if (iComp + iH <= kLevel and iH>0) or (iComp > 0 and iH=0) then
          eMat:=GetDifferentiationDi(kLevel-iComp, iComp, iH);
        fi;
      od;
    od;
    return ListDifferentiation[kLevel];
  end;
  DoDifferentiation:=function(kLevel, TheVector)
    return VectorMatrixGmoduleMultiplication(TheVector, GetDifferentiation(kLevel));
  end;
  DoHomotopy:=function(kLevel, TheVect)
    local WorkingModuleElt, eBegin, eEnd, TheVectRed, ListReturn, iH, eVect, TheNew, iCol, eHomotopElt, WorkingModuleEltRed;
    if kLevel>0 and IsZeroGmoduleVector(DoDifferentiation(kLevel, TheVect))=false then
      Print("The vector has non zero differential, we cannot do homotopy\n");
      Print(NullMat(5));
    fi;
    if Length(TheVect)<>GetDimension(kLevel) then
      Print("Not correct, rework\n");
      Print(NullMat(5));
    fi;
    WorkingModuleElt:=StructuralCopy(TheVect);
    eBegin:=ListBeginDimension[kLevel+1][1];
    eEnd:=ListEndDimension[kLevel+1][1];
    TheVectRed:=WorkingModuleElt{[eBegin..eEnd]};
    ListReturn:=PreHomotopyD1(kLevel, TheVectRed);
    for iH in [1..kLevel+1]
    do
      eVect:=DoDifferentiationDi(kLevel+1, 0, iH, ListReturn);
      eBegin:=ListBeginDimension[kLevel+2-iH][iH];
      eEnd:=ListEndDimension[kLevel+2-iH][iH];
      WorkingModuleEltRed:=WorkingModuleElt{[eBegin..eEnd]};
      TheNew:=VectorGmoduleSoustraction(WorkingModuleEltRed, eVect);
      WorkingModuleElt{[eBegin..eEnd]}:=TheNew;
    od;
    for iCol in [1..kLevel+1]
    do
      eBegin:=ListBeginDimension[kLevel+2-iCol][iCol];
      eEnd:=ListEndDimension[kLevel+2-iCol][iCol];
      TheVectRed:=WorkingModuleElt{[eBegin..eEnd]};
      eHomotopElt:=DoHomotopyD0(kLevel+1-iCol, iCol-1, TheVectRed);
      Append(ListReturn, eHomotopElt);
      for iH in [0..kLevel]
      do
        if iCol+iH<=kLevel+1 and iCol+iH>=0 then
          eVect:=DoDifferentiationDi(kLevel+1-iCol, iCol, iH, eHomotopElt);
          eBegin:=ListBeginDimension[kLevel+2-iH-iCol][iH+iCol];
          eEnd:=ListEndDimension[kLevel+2-iH-iCol][iH+iCol];
          WorkingModuleEltRed:=WorkingModuleElt{[eBegin..eEnd]};
          TheNew:=VectorGmoduleSoustraction(WorkingModuleEltRed, eVect);
          WorkingModuleElt{[eBegin..eEnd]}:=TheNew;
        fi;
      od;
    od;
    if IsZeroReducedGmoduleVector(WorkingModuleElt)=false then
      Print("We should panic, just maybe\n");
      Print(NullMat(5));
    fi;
    if IsEqualGmoduleVector(DoDifferentiation(kLevel+1, ListReturn), TheVect)=false then
      Print("Non correct homotopy computation for N-G-Q, please panic\n");
      Print(NullMat(5));
    fi;
    return ListReturn;
  end;
  return rec(GRP:=TheBigGroup, 
             Initialization:=Initialization, 
             DoHomotopy:=DoHomotopy, 
             GetDifferentiation:=GetDifferentiation);
end;



GetGroup288_1026:=function()
  local EXT24, eVect, i, GRP_W4, NewListGens, TheSubgroup, FuncInsert, eElt, ListGen, GRP_576, GRPanti, O, FindPos, ListPermGens, eGen, eList, GRPperm, TheResolA4, TheResolS4, OneA4, LN;
  EXT24:=[];
  for eVect in BuildSet(4, [-1,1])
  do
    Add(EXT24, eVect);
  od;
  for i in [1..4]
  do
    eVect:=ListWithIdenticalEntries(4,0);
    eVect[i]:=2;
    Add(EXT24, ShallowCopy(eVect));
    eVect[i]:=-2;
    Add(EXT24, ShallowCopy(eVect));
  od;
  GRP_W4:=__VectorConfigurationFullDim_Automorphism(EXT24).MatrixGroup;
  NewListGens:=[];
  TheSubgroup:=Group([IdentityMat(4)]);
  FuncInsert:=function(eElt)
    if DeterminantMat(eElt)=1 then
      if eElt in TheSubgroup then
        return;
      fi;
      Add(NewListGens, eElt);
      TheSubgroup:=Group(NewListGens);
    fi;
  end;
  for eElt in GRP_W4
  do
    FuncInsert(eElt);
  od;
  #
  ListGen:=SmallGeneratingSet(TheSubgroup);
  GRP_576:=Group(ListGen);
  GRPanti:=Group([-IdentityMat(4)]);
  O:=Orbits(GRPanti, EXT24, OnPoints);
  FindPos:=function(eVect)
    local iO;
    for iO in [1..Length(O)]
    do
      if Position(O[iO], eVect)<>fail then
        return iO;
      fi;
    od;
  end;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRP_576)
  do
    eList:=List(O, x->FindPos(x[1]*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  return Group(ListPermGens);
end;


GetResolution288_1026:=function()
  local GRPperm, TheResolA4, TheResolS4, OneA4, LN;
  GRPperm:=GetGroup288_1026();
  #
  TheResolA4:=GetResolutionA4();
  TheResolS4:=GetResolutionS4();
  LN:=NormalSubgroups(GRPperm);
  OneA4:=First(LN, x->IsomorphismGroups(x, AlternatingGroup(4))<>fail);
  return GetResolutionFromNormalAndQuotient(GRPperm, OneA4, TheResolA4, TheResolS4);
end;



ResolutionsDirectProduct:=function(ListResol)
  local kAvailable, nb, ListMaxNbMovedPoints, GetListKset, GetDifferentiation, Initialization, DoHomotopy, MapElementToList, MapListToElement, GetDifferentiationDi, DoHomotopyDi, GetDimensionDetails, GetDimensionEset, GetListSetPosition, ListListDim, PreGetListKset, GRP, i, eGen, ListElement, j, NewListGens, IreductionGrpElt, IreductionElt, IreductionVect;
  nb:=Length(ListResol);
  ListMaxNbMovedPoints:=List(ListResol, x->Maximum(MovedPoints(x.GRP)));
  MapElementToList:=function(eElt)
    local pos, ListElement, i, nbMax, TheOff, eList;
    TheOff:=0;
    ListElement:=[];
    for i in [1..nb]
    do
      nbMax:=ListMaxNbMovedPoints[i];
      eList:=List([1..nbMax], x->OnPoints(x+TheOff, eElt)-TheOff);
      Add(ListElement, PermList(eList));
      TheOff:=TheOff+nbMax;
    od;
    return ListElement;
  end;
  MapListToElement:=function(ListElement)
    local TheOff, eList, i, nbMax;
    TheOff:=0;
    eList:=[];
    for i in [1..nb]
    do
      nbMax:=ListMaxNbMovedPoints[i];
      Append(eList, List([1..nbMax], x->OnPoints(x, ListElement[i])+TheOff));
      TheOff:=TheOff+nbMax;
    od;
    return PermList(eList);
  end;
  NewListGens:=[];
  for i in [1..nb]
  do
    for eGen in GeneratorsOfGroup(ListResol[i].GRP)
    do
      ListElement:=[];
      for j in [1..nb]
      do
        if j=i then
          Add(ListElement, eGen);
        else
          Add(ListElement, ());
        fi;
      od;
      Add(NewListGens, MapListToElement(ListElement));
    od;
  od;
  GRP:=Group(NewListGens);
  PreGetListKset:=function(kLevel, hLev)
    local iK, ReturnListKset;
    if hLev=1 then
      return [[kLevel]];
    fi;
    ReturnListKset:=[];
    for iK in [0..kLevel]
    do
      Append(ReturnListKset, List(PreGetListKset(kLevel-iK, hLev-1), x->Concatenation(x, [iK])));
    od;
    return ReturnListKset;
  end;
  GetListKset:=function(kLevel)
    return PreGetListKset(kLevel, nb);
  end;
  Initialization:=function(kLevel)
    local i, ListDim, iLevel;
    kAvailable:=kLevel;
    ListListDim:=[];
    for i in [1..nb]
    do
      ListResol[i].Initialization(kLevel);
      ListDim:=[];
      for iLevel in [0..kLevel]
      do
        Add(ListDim, ListResol[i].GetDimension(iLevel));
      od;
      Add(ListListDim, ListDim);
    od;
  end;
  GetDimensionEset:=function(eSet)
    local TheProd, i;
    TheProd:=1;
    for i in [1..nb]
    do
      TheProd:=TheProd*ListListDim[i][eSet[i]+1];
    od;
    return TheProd;
  end;
  GetDimensionDetails:=function(kLevel)
    local ListKset, ListDimension, ListBeginDimension, ListEndDimension, pos, eSet, TheProd, i;
    ListKset:=GetListKset(kLevel);
    ListDimension:=[];
    ListBeginDimension:=[];
    ListEndDimension:=[];
    pos:=0;
    for eSet in ListKset
    do
      TheProd:=GetDimensionEset(eSet);
      Add(ListDimension, TheProd);
      Add(ListBeginDimension, pos+1);
      pos:=pos+TheProd;
      Add(ListEndDimension, pos);
    od;
    return rec(ListDimension:=ListDimension,
               ListBeginDimension:=ListBeginDimension, 
               ListEndDimension:=ListEndDimension, 
               ListKset:=ListKset, 
               TotalDim:=pos);
  end;
#  GetPosition:=function(eSet, valSet)
#    local pos, TheProd, i;
#    pos:=1;
#    TheProd:=1;
#    for i in [1..nb]
#    do
#      if valSet[i]<=0 or valSet[i]>ListListDim[i][eSet[i]+1] then
#        Print("Inconsistency at its worst\n");
#        Print(NullMat(5));
#      fi;
#      pos:=pos+(valSet[i]-1)*TheProd;
#      TheProd:=TheProd*ListListDim[i][eSet[i]+1];
#    od;
#    return pos;
#  end;
  GetListSetPosition:=function(eSet)
    local ListSets, i;
    ListSets:=[];
    for i in [1..nb]
    do
      Add(ListSets, [1..ListListDim[i][eSet[i]+1]]);
    od;
    return BuildSetMultiple(ListSets);
  end;
  GetDifferentiationDi:=function(eSet1, i)
    local ListValSet1, ListValSet2, eSet2, dim1, dim2, RetMat, valSet, DiffI, eSign, eRec, ePos, iRow, iCol, ePosB, valSetB, MapElt, TheMat;
    eSet2:=StructuralCopy(eSet1);
    eSet2[i]:=eSet1[i]-1;
    ListValSet1:=GetListSetPosition(eSet1);
    ListValSet2:=GetListSetPosition(eSet2);
    dim1:=GetDimensionEset(eSet1);
    dim2:=GetDimensionEset(eSet2);
    RetMat:=GMOD_GetZeroMatrix(dim1, dim2);
    TheMat:=ListResol[i].GetDifferentiation(eSet1[i]);
    DiffI:=Difference([1..nb], [i]);
    eSign:=(-1)^(Sum(eSet1{[1..i-1]}));
    MapElt:=function(eElt)
      local ListElement, j;
      ListElement:=[];
      for j in [1..nb]
      do
        if j<>i then
          Add(ListElement, ());
        else
          Add(ListElement, eElt);
        fi;
      od;
      return MapListToElement(ListElement);
    end;
    for valSet in ListValSet1
    do
      ePos:=Position(ListValSet1, valSet);
      iRow:=valSet[i];
      for iCol in [1..TheMat.nbCol]
      do
        eRec:=rec(ListVal:=eSign*TheMat.TheMat[iRow][iCol].ListVal, ListElt:=List(TheMat.TheMat[iRow][iCol].ListElt, MapElt));
        valSetB:=[];
        valSetB{DiffI}:=valSet{DiffI};
        valSetB[i]:=iCol;
        ePosB:=Position(ListValSet2, valSetB);
        RetMat.TheMat[ePos][ePosB]:=eRec;
      od;
    od;
    return RetMat;
  end;
  GetDifferentiation:=function(kLevel)
    local SourceDimDetails, TargetDimDetails, nbSource, nbTarget, dim1, dim2, RetMat, iSet, eSet, eSourceBegin, eSourceEnd, eSourceDim, i, eSet2, eMat, pos, eTargetBegin, eTargetEnd, eTargetDim, iRow, iCol;
    if kLevel>kAvailable then
      Print("GetResolutionDirectProduct, update of resolution to kLevel=", kLevel, "\n");
      Initialization(kLevel);
    fi;
    SourceDimDetails:=GetDimensionDetails(kLevel);
    TargetDimDetails:=GetDimensionDetails(kLevel-1);
    nbSource:=Length(SourceDimDetails.ListKset);
    nbTarget:=Length(TargetDimDetails.ListKset);
    dim1:=SourceDimDetails.TotalDim;
    dim2:=TargetDimDetails.TotalDim;
    RetMat:=GMOD_GetZeroMatrix(dim1, dim2);
    for iSet in [1..nbSource]
    do
      eSet:=SourceDimDetails.ListKset[iSet];
      eSourceBegin:=SourceDimDetails.ListBeginDimension[iSet];
      eSourceEnd:=SourceDimDetails.ListEndDimension[iSet];
      eSourceDim:=SourceDimDetails.ListDimension[iSet];
      for i in [1..nb]
      do
        if eSet[i]>0 then
          eSet2:=StructuralCopy(eSet);
          eSet2[i]:=eSet[i]-1;
          eMat:=GetDifferentiationDi(eSet, i);
          pos:=Position(TargetDimDetails.ListKset, eSet2);
          eTargetBegin:=TargetDimDetails.ListBeginDimension[pos];
          eTargetEnd:=TargetDimDetails.ListEndDimension[pos];
          eTargetDim:=TargetDimDetails.ListDimension[pos];
          for iRow in [1..eSourceDim]
          do
            for iCol in [1..eTargetDim]
            do
              RetMat.TheMat[iRow+eSourceBegin-1][iCol+eTargetBegin-1]:=GmoduleAddition(RetMat.TheMat[iRow+eSourceBegin-1][iCol+eTargetBegin-1], eMat.TheMat[iRow][iCol]);
            od;
          od;
        fi;
      od;
    od;
    return RetMat;
  end;
  IreductionGrpElt:=function(eGrpElt, i)
    local ListElement, j;
    ListElement:=MapElementToList(eGrpElt);
    for j in [i+1..nb]
    do
      ListElement[j]:=();
    od;
    return MapListToElement(ListElement);
  end;
  IreductionElt:=function(eRec, i)
    return ReducedGmoduleForm(rec(ListVal:=eRec.ListVal, ListElt:=List(eRec.ListElt, x->IreductionGrpElt(x,i))));
  end;
  IreductionVect:=function(eVect, i)
    return List(eVect, x->IreductionElt(x,i));
  end;
  DoHomotopyDi:=function(eSet, i, TheVect)
    local ListCoset, ListVect, FuncInsertEntry, iCol, nbEnt, iEnt, nbCos, eSet2, dimSource, dimTarget, TheReturn, iCos, eHomotop, MapElt, eSign, NewVect, eEnt, ListValSetTarget, ListValSetSource, eSetSource, eSetTarget, pos, TheReturnSmall, eSmallDimSource, eSmallDimTarget, ConcatFct, ListDiffI, eSetDiffI, TheImage, ListPos;
    eSet2:=StructuralCopy(eSet);
    eSet2[i]:=eSet[i]+1;
    ListValSetTarget:=GetListSetPosition(eSet);
    ListValSetSource:=GetListSetPosition(eSet2);
    dimSource:=GetDimensionEset(eSet2);
    dimTarget:=GetDimensionEset(eSet);
    if Length(TheVect)<>dimTarget then
      Print("Inconsistency here and there\n");
      Print(NullMat(5));
    fi;
    if eSet[i]>0 then
      TheImage:=VectorMatrixGmoduleMultiplication(TheVect, GetDifferentiationDi(eSet, i));
      if IsZeroReducedGmoduleVector(IreductionVect(TheImage,i))=false then
        Print("That is most likely an inconsistency in DoHomotopyDi\n");
        Print(NullMat(5));
      fi;
    fi;
    eSign:=(-1)^(Sum(eSet{[1..i-1]}));
    TheReturn:=GMOD_GetZeroVector(dimSource);
    ListDiffI:=Set(List(ListValSetTarget, x->x{Difference([1..nb], [i])}));
    eSmallDimTarget:=ListListDim[i][eSet[i]+1];
    eSmallDimSource:=ListListDim[i][eSet2[i]+1];
    ConcatFct:=function(eSetRed, eVal)
      return Concatenation(eSetRed{[1..i-1]}, [eVal], eSetRed{[i..nb-1]});
    end;
    for eSetDiffI in ListDiffI
    do
      TheReturnSmall:=GMOD_GetZeroVector(eSmallDimSource);
      ListCoset:=[];
      ListVect:=[];
      FuncInsertEntry:=function(eVal, iCol, eElt)
        local ListElement, eEltRed, eCos, posH, eVect;
        ListElement:=MapElementToList(eElt);
        eEltRed:=ListElement[i];
        eCos:=ListElement{[1..i-1]};
        posH:=Position(ListCoset, eCos);
        if posH=fail then
          eVect:=GMOD_GetZeroVector(eSmallDimTarget);
          Add(eVect[iCol].ListVal, eVal);
          Add(eVect[iCol].ListElt, eEltRed);
          Add(ListCoset, eCos);
          Add(ListVect, StructuralCopy(eVect));
        else
          Add(ListVect[posH][iCol].ListVal, eVal);
          Add(ListVect[posH][iCol].ListElt, eEltRed);
        fi;
      end;
      ListPos:=[];
      for iCol in [1..eSmallDimTarget]
      do
        eSetTarget:=ConcatFct(eSetDiffI, iCol);
        pos:=Position(ListValSetTarget, eSetTarget);
        Add(ListPos, pos);
        nbEnt:=Length(TheVect[pos].ListVal);
        for iEnt in [1..nbEnt]
        do
          FuncInsertEntry(TheVect[pos].ListVal[iEnt], iCol, TheVect[pos].ListElt[iEnt]);
        od;
      od;
      nbCos:=Length(ListCoset);
      for iCos in [1..nbCos]
      do
        eHomotop:=ListResol[i].DoHomotopy(eSet[i], ReducedGmoduleVector(ListVect[iCos]));
        MapElt:=function(eElt)
          local ListElement, j;
          ListElement:=Concatenation(ListCoset[iCos], [eElt]);
          for j in [i+1..nb]
          do
            Add(ListElement, ());
          od;
          return MapListToElement(ListElement);
        end;
        NewVect:=[];
        for eEnt in eHomotop
        do
          Add(NewVect, rec(ListVal:=eSign*eEnt.ListVal, ListElt:=List(eEnt.ListElt, MapElt)));
        od;
        TheReturnSmall:=VectorGmoduleAddition(TheReturnSmall, NewVect);
      od;
      for iCol in [1..eSmallDimSource]
      do
        eSetSource:=ConcatFct(eSetDiffI, iCol);
        pos:=Position(ListValSetSource, eSetSource);
        TheReturn[pos]:=TheReturnSmall[iCol];
      od;
    od;
    TheImage:=VectorMatrixGmoduleMultiplication(TheReturn, GetDifferentiationDi(eSet2, i));
    if IsEqualGmoduleVector(IreductionVect(TheImage,i), IreductionVect(TheVect,i))=false then
      Print("We reached a likely inconsistency in DohomotopyDi\n");
      Print(NullMat(5));
    fi;
    return TheReturn;
  end;
  DoHomotopy:=function(kLevel, TheVector)
    local SourceDimDetails, TargetDimDetails, nbSource, nbTarget, ListStatusSource, ListOriginsTarget, i, eSet, eSet2, pos, WorkingModuleVector, TheReturn, IsFinished, eBeginTarget, eEndTarget, TheVect, eSet3, eBeginSource, eEndSource, eBegin3, eEnd3, pos3, eImage, j, eHomotopElt, iSet, DoCheck;
    if kLevel> 0 and IsZeroReducedGmoduleVector(VectorMatrixGmoduleMultiplication(TheVector, GetDifferentiation(kLevel)))=false then
      Print("You call wrongly the homotopy function of direct product construction\n");
      Print(NullMat(5));
    fi;
    DoCheck:=true;
    SourceDimDetails:=GetDimensionDetails(kLevel+1);
    TargetDimDetails:=GetDimensionDetails(kLevel);
    nbSource:=Length(SourceDimDetails.ListKset);
    nbTarget:=Length(TargetDimDetails.ListKset);
    ListOriginsTarget:=[];
    for i in [1..nbTarget]
    do
      Add(ListOriginsTarget, []);
    od;
    ListStatusSource:=ListWithIdenticalEntries(nbSource, 1);
    for iSet in [1..Length(SourceDimDetails.ListKset)]
    do
      eSet:=SourceDimDetails.ListKset[iSet];
      for i in [1..nb]
      do
        if eSet[i]>0 then
          eSet2:=StructuralCopy(eSet);
          eSet2[i]:=eSet[i]-1;
          pos:=Position(TargetDimDetails.ListKset, eSet2);
          Add(ListOriginsTarget[pos], i);
        fi;
      od;
    od;
    WorkingModuleVector:=StructuralCopy(TheVector);
    TheReturn:=GMOD_GetZeroVector(SourceDimDetails.TotalDim);
    while(true)
    do
      IsFinished:=true;
      for iSet in [1..nbTarget]
      do
        eSet:=TargetDimDetails.ListKset[iSet];
        for i in [1..nb]
        do
          eSet2:=StructuralCopy(eSet);
          eSet2[i]:=eSet[i]+1;
          pos:=Position(SourceDimDetails.ListKset, eSet2);
          if ListStatusSource[pos]=1 and i=Minimum(ListOriginsTarget[iSet]) then
            IsFinished:=false;
            ListStatusSource[pos]:=0;
            eBeginTarget:=TargetDimDetails.ListBeginDimension[iSet];
            eEndTarget:=TargetDimDetails.ListEndDimension[iSet];
            TheVect:=WorkingModuleVector{[eBeginTarget..eEndTarget]};
            eBeginSource:=SourceDimDetails.ListBeginDimension[pos];
            eEndSource:=SourceDimDetails.ListEndDimension[pos];
            eHomotopElt:=DoHomotopyDi(eSet, i, TheVect);
            TheReturn{[eBeginSource..eEndSource]}:=eHomotopElt;
            for j in [1..nb]
            do
              if eSet2[j]>0 then
                eSet3:=StructuralCopy(eSet2);
                eSet3[j]:=eSet2[j]-1;
                eImage:=VectorMatrixGmoduleMultiplication(eHomotopElt, GetDifferentiationDi(eSet2, j));
                pos3:=Position(TargetDimDetails.ListKset, eSet3);
                eBegin3:=TargetDimDetails.ListBeginDimension[pos3];
                eEnd3:=TargetDimDetails.ListEndDimension[pos3];
                WorkingModuleVector{[eBegin3..eEnd3]}:=VectorGmoduleSoustraction(WorkingModuleVector{[eBegin3..eEnd3]}, eImage);
                ListOriginsTarget[pos3]:=Difference(ListOriginsTarget[pos3], [j]);
              fi;
            od;
          fi;
        od;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    if DoCheck=true then
      if IsZeroReducedGmoduleVector(WorkingModuleVector)=false then
        Print("We should panic, just maybe\n");
        Print(NullMat(5));
      fi;
      if IsEqualGmoduleVector(VectorMatrixGmoduleMultiplication(TheReturn, GetDifferentiation(kLevel+1)), TheVector)=false then
        Print("Non correct homotopy computation for direct product, please panic\n");
        Print(NullMat(5));
      fi;
    fi;
    return TheReturn;
  end;
  return rec(GRP:=GRP, 
             GetDifferentiation:=GetDifferentiation,
             GetDifferentiationDi:=GetDifferentiationDi,
             Initialization:=Initialization, 
             DoHomotopy:=DoHomotopy);
end;


# the group is [96,227]
# it is obtained as a subgroup of [288, 1026] so it acts on 12
# points. It has a subgroup C2 x C2 with quotient S4 hence we can
# get efficient resolutions from this.
GetResolution96_227:=function()
  local TheGRP96, LN, TheInfoCyc2, ResolC2, ResolC2_C2, OneC2C2, TheResolS4;
  TheGRP96:=Group([ (1,8)(2,12)(5,7)(10,11), (1,8)(2,10)(3,6)(4,9)(5,7)(11,12), 
      (1,8)(3,9)(4,6)(5,7), (1,7)(2,11)(5,8)(10,12), (1,7,5)(2,12,11)(3,9,6), 
      (1,8,7,5)(2,3,10,9)(4,11,6,12) ]);
  LN:=NormalSubgroups(TheGRP96);
  TheInfoCyc2:=InformationResolutionCyclic(2);
  ResolC2:=ResolutionPeriodic(TheInfoCyc2);
  ResolC2_C2:=ResolutionsDirectProduct([ResolC2, ResolC2]);
  OneC2C2:=First(LN, x->IsomorphismGroups(x, ResolC2_C2.GRP)<>fail);
  TheResolS4:=GetResolutionS4();
  return GetResolutionFromNormalAndQuotient(TheGRP96, OneC2C2, ResolC2_C2, TheResolS4);
end;

