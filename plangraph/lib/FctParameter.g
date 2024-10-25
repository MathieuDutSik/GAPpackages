GetCycleOfEdgeSet:=function(nbVert, ListEdges)
  local ListVect, eEdge, eVert1, eVert2, eVect, NSP, pos, eEnt, eColl;
  ListVect:=[];
  for eEdge in ListEdges
  do
    if Length(eEdge)=1 then
      pos:=Position(ListEdges, eEdge);
      return rec(IsFinished:=false, pos:=pos);
    fi;
  od;
  eColl:=Collected(ListEdges);
  for eEnt in eColl
  do
    if eEnt[2]>1 then
      eEdge:=eEnt[1];
      pos:=Position(ListEdges, eEdge);
      return rec(IsFinished:=false, pos:=pos);
    fi;
  od;
  for eEdge in ListEdges
  do
    eVert1:=eEdge[1];
    eVert2:=eEdge[2];
    eVect:=ListWithIdenticalEntries(nbVert,0);
    eVect[eVert1]:=eVect[eVert1]+1;
    eVect[eVert2]:=eVect[eVert2]-1;
    Add(ListVect, eVect);
  od;
  if Length(ListEdges)=0 then
    return rec(IsFinished:=true);
  fi;
  NSP:=NullspaceMat(ListVect);
  if Length(NSP)>0 then
    eVect:=NSP[1];
    pos:=First([1..Length(ListEdges)], x->eVect[x]<>0);
    return rec(IsFinished:=false, pos:=pos);
  else
    return rec(IsFinished:=true);
  fi;
end;


Eisenstein_GetExpression:=function(eX)
  local a, b, a2, b2, hRet, h;
  if IsRat(eX)=true then
    return [eX, 0];
  else
    hRet:=RationalizedMat([[eX]])/2;
    h:=(1+Sqrt(-3))/2;
    a:=hRet[1][1];
    b:=(eX - a)/Sqrt(-3);
    if IsRat(b)=false then
      Print("Inconsistency in QN_GetExpression\n");
      Print(NullMat(5));
    fi;
#    a+b Sqrt(-3)= a+b (1+Sqrt(-3)-1)
#                = a+b 2h -b
    a2:=a-b;
    b2:=2*b;
    if a2 + b2*h <>eX then
      Print("Inconsistency in Eisenstein_GetExpression\n");
      Print(NullMat(5));
    fi;
    return [a2,b2];
  fi;
end;



HomologyInformation:=function(PLori)
  local eInv, eNext, nbP, eIterFace, VEFori, nbVert, nbFace, ListEdgeVert, ListEdgeFace, ListStatusDE, iDE, iDE2, eVert1, eVert2, eFace1, eFace2, nbEdge, ListPosSpann, ListPosCycle, ListStatusEdgeVert, posB, pos, eRec, eSet, GRAface, eSpannFace, eEdge, ListVertexInfo, len, ListPosSequence, ListVertSequence, eCritVert, eNextVert, idxFound, eSol, ListStatus, posNext, ListFundamentalCycleInfo, ListVertSpann, ListVectSpann, eVect, ePos, iDE1, ListIdx, idx, i, idxB, eVert, idxFoundB, LPos1, LPos2, ListPos, iNext, ListIDE, eVertNext, iDEfound, rDE;
  eInv:=PLori.invers;
  eNext:=PLori.next;
  nbP:=PLori.nbP;
  eIterFace:=eNext*eInv;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  nbVert:=Length(VEFori.VertSet);
  nbFace:=Length(VEFori.FaceSet);
  ListEdgeVert:=[];
  ListEdgeFace:=[];
  ListStatusDE:=ListWithIdenticalEntries(nbP,1);
  for eEdge in VEFori.EdgeSet
  do
    iDE1:=eEdge[1];
    iDE2:=eEdge[2];
    eVert1:=VEFori.ListOriginVert[iDE1];
    eVert2:=VEFori.ListOriginVert[iDE2];
    eFace1:=VEFori.ListOriginFace[iDE1];
    eFace2:=VEFori.ListOriginFace[iDE2];
    Add(ListEdgeVert, Set([eVert1, eVert2]));
    Add(ListEdgeFace, Set([eFace1, eFace2]));
  od;
  nbEdge:=Length(ListEdgeVert);
  ListStatusEdgeVert:=ListWithIdenticalEntries(nbEdge,1);
#  Print("eHom 1: ListStatusEdgeVert=", ListStatusEdgeVert, "\n");
  GRAface:=NullGraph(Group(()), nbFace);
  for eEdge in ListEdgeFace
  do
    if Length(eEdge)=2 then
      AddEdgeOrbit(GRAface, eEdge);
      AddEdgeOrbit(GRAface, Reversed(eEdge));
    fi;
  od;
  eSpannFace:=SpanningTreeGraph(GRAface,1);
  Print("eSpannFace=", eSpannFace, "\n");
  for eEdge in eSpannFace
  do
    pos:=Position(ListEdgeFace, eEdge);
    ListStatusEdgeVert[pos]:=0;
#    Print("eHom 2: ListStatusEdgeVert=", ListStatusEdgeVert, "\n");
  od;
  ListPosCycle:=[];
  while(true)
  do
    eSet:=Filtered([1..nbEdge],x->ListStatusEdgeVert[x]=1);
    eRec:=GetCycleOfEdgeSet(nbVert, ListEdgeVert{eSet});
    if eRec.IsFinished=true then
      break;
    fi;
    pos:=eRec.pos;
    posB:=eSet[pos];
    ListStatusEdgeVert[posB]:=0;
#    Print("eHom 3: ListStatusEdgeVert=", ListStatusEdgeVert, "\n");
    Add(ListPosCycle, posB);
  od;
  ListPosSpann:=Filtered([1..nbEdge], x->ListStatusEdgeVert[x]=1);
  ListVectSpann:=[];
  ListVertSpann:=[];
  for ePos in ListPosSpann
  do
    iDE1:=VEFori.EdgeSet[ePos][1];
    iDE2:=VEFori.EdgeSet[ePos][2];
    eVert1:=VEFori.ListOriginVert[iDE1];
    eVert2:=VEFori.ListOriginVert[iDE2];
    eVect:=ListWithIdenticalEntries(nbVert, 0);
    eVect[eVert1]:=1;
    eVect[eVert2]:=-1;
    Add(ListVectSpann, eVect);
    Add(ListVertSpann, Set([eVert1, eVert2]));
  od;
  ListFundamentalCycleInfo:=[];
  for ePos in ListPosCycle
  do
    iDE1:=VEFori.EdgeSet[ePos][1];
    iDE2:=VEFori.EdgeSet[ePos][2];
    eVert1:=VEFori.ListOriginVert[iDE1];
    eVert2:=VEFori.ListOriginVert[iDE2];
#    Print("eVert1=", eVert1, " eVert2=", eVert2, "\n");
    eVect:=ListWithIdenticalEntries(nbVert, 0);
    eVect[eVert1]:=eVect[eVert1] + 1;
    eVect[eVert2]:=eVect[eVert2] - 1;
    if Length(ListVectSpann)=0 then
      eSol:=[];
    else
      eSol:=SolutionMat(ListVectSpann, eVect);
    fi;
#    Print("eSol=", eSol, "\n");
    ListIdx:=Filtered([1..Length(ListVectSpann)], x->eSol[x]<>0);
#    Print("ListIdx=", ListIdx, "\n");
    len:=Length(ListIdx);
    ListStatus:=ListWithIdenticalEntries(len, 1);
    eCritVert:=eVert1;
#    Print("eCritVert=", eCritVert, "\n");
    ListVertSequence:=[eCritVert];
    ListPosSequence:=[ePos];
#    Print("len=", len, "\n");
    for i in [1..len]
    do
      posNext:=-1;
      for idx in [1..len]
      do
        idxB:=ListIdx[idx];
        if ListStatus[idx]=1 then
          pos:=Position(ListVertSpann[idxB], eCritVert);
          if pos<>fail then
#            Print("   idx=", idx, " eEdge=", ListVertSpann[idx], "\n");
            eNextVert:=ListVertSpann[idxB][3-pos];
#            Print("  eNextVert=", eNextVert, "\n");
            idxFound:=idx;
            idxFoundB:=idxB;
          fi;
        fi;
      od;
      eCritVert:=eNextVert;
      ListStatus[idxFound]:=0;
      Add(ListVertSequence, eNextVert);
      Add(ListPosSequence, ListPosSpann[idxFoundB]);
    od;
    if eCritVert<>eVert2 then
      Print("Error in the cycle analysis\n");
      Print(NullMat(5));
    fi;
    ListVertexInfo:=[];
    for i in [1..len+1]
    do
      eVert:=ListVertSequence[i];
      LPos1:=[ListPosSequence[i], ListPosSequence[NextIdx(len+1,i)]];
      LPos2:=List(VEFori.VertSet[eVert], x->VEFori.ListOriginEdge[x]);
      if IsSubset(Set(LPos2), Set(LPos1))=false then
        Print("Please debug from here\n");
        Print(NullMat(5));
      fi;
      eRec:=rec(eVert:=eVert, ListPos:=LPos1);
      Add(ListVertexInfo, eRec);
    od;
    if Length(ListVertexInfo)=1 then
      ListPos:=ListVertexInfo[1].ListPos;
      if ListPos[1]<>ListPos[2] then
        Print("Cear error\n");
        Print(NullMat(5));
      fi;
      ListIDE:=[ListPos[1]];
    else
      ListIDE:=[];
      for i in [1..len+1]
      do
        eVert:=ListVertexInfo[i].eVert;
        iNext:=NextIdx(len+1,i);
        eVertNext:=ListVertexInfo[iNext].eVert;
        iDEfound:=-1;
        for iDE in VEFori.VertSet[eVert]
        do
          rDE:=OnPoints(iDE, eInv);
          if iDEfound=-1 then
            if Position(VEFori.VertSet[eVertNext], rDE)<>fail then
              iDEfound:=iDE;
            fi;
          fi;
        od;
        if iDEfound=-1 then
          Print("Incorrection\n");
          Print(NullMat(5));
        fi;
        Add(ListIDE, iDEfound);
      od;
    fi;
    Add(ListFundamentalCycleInfo, rec(ListVertexInfo:=ListVertexInfo, ListIDE:=ListIDE));
  od;
  return rec(ListStatusEdgeVert:=ListStatusEdgeVert,
             ListPosCycle:=ListPosCycle,
             ListPosSpann:=ListPosSpann,
             VEFori:=VEFori,
             ListFundamentalCycleInfo:=ListFundamentalCycleInfo, 
             ListEdgeVert:=ListEdgeVert);
end;

SolutionMatSix:=function(Amat, eVect)
  local nbRow, nbCol, FindCorrespInt, AmatMod2, AmatMod3, eVect2, eVect3, eRes2, eRes3, eLine, eNewLine2, eNewLine3, eEnt, eEnt2, eEnt3, pos, eSol2, eSol3, eSol, i, eDiff;
  nbRow:=Length(Amat);
  nbCol:=Length(Amat[1]);
  FindCorrespInt:=function(eRes2, eRes3)
    local eReturn, eReturn2, eReturn3;
    eReturn:=0;
    while(true)
    do
      eReturn2:=eReturn + 0*Z(2);
      eReturn3:=eReturn + 0*Z(3);
      if eReturn2=eRes2 and eReturn3=eRes3 then
        return eReturn;
      fi;
      eReturn:=eReturn+1;
    od;
  end;
  AmatMod2:=[];
  AmatMod3:=[];
  for eLine in Amat
  do
    eNewLine2:=[];
    eNewLine3:=[];
    for eEnt in eLine
    do
      eEnt2:=eEnt + 0*Z(2);
      eEnt3:=eEnt + 0*Z(3);
      Add(eNewLine2, eEnt2);
      Add(eNewLine3, eEnt3);
    od;
    Add(AmatMod2, eNewLine2);
    Add(AmatMod3, eNewLine3);
  od;
  eVect2:=[];
  eVect3:=[];
  for eEnt in eVect
  do
    eEnt2:=eEnt + 0*Z(2);
    eEnt3:=eEnt + 0*Z(3);
    Add(eVect2, eEnt2);
    Add(eVect3, eEnt3);
  od;
  eSol2:=SolutionMat(AmatMod2, eVect2);
  eSol3:=SolutionMat(AmatMod3, eVect3);
  eSol:=[];
  for i in [1..Length(eSol2)]
  do
    Add(eSol, FindCorrespInt(eSol2[i], eSol3[i]));
  od;
  eDiff:=eSol*Amat - eVect;
  pos:=First(eDiff, x->x mod 6>0);
  if pos<>fail then
    Print("Error in solving\n");
    Print(NullMat(5));
  fi;
  return eSol;
end;



Kernel_ComputeParameterSetEisenstein:=function(GRPstruct, PLori, eHomolInfo, ListVertexDegree, ListCycleIntegral)
  local eInv, eNext, nbP, eIterFace, GRPiter, O, ListEquation, eO, eVect, eVal, eDE1, eDE2, len, NSP, Overt, GRPvert, i, eDEselect, rDEselect, ListShiftDE, eShift, SumShift, VEFori, eDE, rDE, h, pos, eSum, ListVertNbIncd, ListVertIncd, eDeg, eEdge, ListEdgeVert, posEdge, iEdge, nbEdge, ListStatusEdgeVert, iVert, nbVert, ListEdgeFace, nbFace, GRAface, eSet, eFace1, eFace2, eVert1, eVert2, eSpannFace, iDE, iDE2, eRec, posB, TheQuadFormExpanded, TheQuadFormReduced, i1_1, i1_2, i2_1, i2_2, ListRational, eVectRat1, eVectRat2, iDE1, a, b, hVal, eNSP, eEnt, eDiagInfo, TheQuadFormReducedIntegral, ListIntegralSolution, ListEquationIntegral, eEqua1, eEqua2, eEqua, eDiagInfoIntegral, ListQuadFormReducedIntegral, ListQuadFormExpanded, eMat, ListInfos, TheMethodDetermination, eRes, DoCheck1, Bside, ListEquationShift, eLine, eCycle, eVert, nbCycle, iCycle, TheConstraint, eReply, ListVector;
  eInv:=PLori.invers;
  eNext:=PLori.next;
  nbP:=PLori.nbP;
  eIterFace:=eNext*eInv;
  VEFori:=eHomolInfo.VEFori;
  nbVert:=Length(VEFori.VertSet);
  nbFace:=Length(VEFori.FaceSet);
  nbEdge:=Length(VEFori.EdgeSet);
  h:=(1+Sqrt(-3))/2;
  ListShiftDE:=ListWithIdenticalEntries(nbP,-400);
  ListEquation:=[];
  for eO in VEFori.FaceSet
  do
    if Length(eO)<>3 then
      Print("We have an orbit of length not 3, illegal\n");
      Print(NullMat(5));
    fi;
    eVect:=ListWithIdenticalEntries(nbP,0);
    eVect{eO}:=[1,1,1];
    Add(ListEquation, eVect);
  od;
  TheMethodDetermination:=2;
  if TheMethodDetermination=1 then
    ListStatusEdgeVert:=List(eHomolInfo.ListStatusEdgeVert, x->x);
    for iEdge in [1..nbEdge]
    do
      if ListStatusEdgeVert[iEdge]=0 then
        iDE1:=VEFori.EdgeSet[iEdge][1];
        iDE2:=VEFori.EdgeSet[iEdge][2];
        ListShiftDE[iDE1]:=0;
        ListShiftDE[iDE2]:=0;
      fi;
    od;
    while(true)
    do
      ListVertIncd:=[];
      for iVert in [1..nbVert]
      do
        Add(ListVertIncd, []);
      od;
      ListVertNbIncd:=ListWithIdenticalEntries(nbVert,0);
      for iEdge in [1..nbEdge]
      do
        if ListStatusEdgeVert[iEdge]=1 then
          eEdge:=eHomolInfo.ListEdgeVert[iEdge];
          Add(ListVertIncd[eEdge[1]], iEdge);
          Add(ListVertIncd[eEdge[2]], iEdge);
          ListVertNbIncd[eEdge[1]]:=ListVertNbIncd[eEdge[1]]+1;
          ListVertNbIncd[eEdge[2]]:=ListVertNbIncd[eEdge[2]]+1;
        fi;
      od;
      eSum:=Sum(ListVertNbIncd);
      if eSum=0 then
        break;
      fi;
      pos:=Position(ListVertNbIncd, 1);
      if pos=fail then
        Print("We have some inconsistency of some kind\n");
        Print(NullMat(5));
      fi;
      iEdge:=ListVertIncd[pos][1];
      ListStatusEdgeVert[iEdge]:=0;
      SumShift:=0;
      eDEselect:=-1;
      for eDE in VEFori.VertSet[pos]
      do
        rDE:=OnPoints(eDE, eInv);
        if ListShiftDE[eDE]<>-400 then
          if ListShiftDE[rDE]=-400 then
            Print("Deep inconsistency\n");
            Print(NullMat(5));
          fi;
          eShift:=ListShiftDE[eDE]-ListShiftDE[rDE];
          SumShift:=SumShift+eShift;
        else
          if eDEselect<>-1 then
            Print("Two times impossible\n");
            Print(NullMat(5));
          fi;
          eDEselect:=eDE;
        fi;
      od;
      eDeg:=ListVertexDegree[pos];
      eShift:=6 - eDeg - SumShift;
      Print("eShift=", eShift, "\n");
      rDEselect:=OnPoints(eDEselect, eInv);
      ListShiftDE[eDEselect]:=eShift;
      ListShiftDE[rDEselect]:=0;
    od;
  fi;
  if TheMethodDetermination=2 then
    ListEquationShift:=[];
    Bside:=[];
    for iVert in [1..Length(VEFori.VertSet)]
    do
      eVert:=VEFori.VertSet[iVert];
      eLine:=ListWithIdenticalEntries(nbP,0);
      for eDE in eVert
      do
        rDE:=OnPoints(eDE, eInv);
        eLine[eDE]:=1;
        eLine[rDE]:=-1;
      od;
      Add(ListEquationShift, eLine);
      eDeg:=ListVertexDegree[iVert];
      Add(Bside, 6 - eDeg);
    od;
    nbCycle:=Length(eHomolInfo.ListFundamentalCycleInfo);
    for iCycle in [1..nbCycle]
    do
      eCycle:=eHomolInfo.ListFundamentalCycleInfo[iCycle];
      eLine:=ListWithIdenticalEntries(nbP,0);
      for eDE in eCycle.ListIDE
      do
        rDE:=OnPoints(eDE, eInv);
        eLine[eDE]:=1;
        eLine[rDE]:=-1;
      od;
      Add(ListEquationShift, eLine);
      Add(Bside, ListCycleIntegral[iCycle]);
    od;
    ListShiftDE:=SolutionMatSix(TransposedMat(ListEquationShift), Bside);
  fi;
  for eEdge in VEFori.EdgeSet
  do
    eDE1:=eEdge[1];
    eDE2:=eEdge[2];
    eVect:=ListWithIdenticalEntries(nbP,0);
    eVect[eDE1]:=h^(ListShiftDE[eDE1]);
    eVect[eDE2]:=h^(ListShiftDE[eDE2]);
    Add(ListEquation, eVect);
  od;
  NSP:=NullspaceMat(TransposedMat(ListEquation));
  DoCheck1:=1;
  if DoCheck1=1 then
    for iVert in [1..Length(VEFori.VertSet)]
    do
      eVert:=VEFori.VertSet[iVert];
      eDeg:=ListVertexDegree[iVert];
      SumShift:=0;
      for eDE in eVert
      do
        rDE:=OnPoints(eDE, eInv);
        eShift:=ListShiftDE[eDE]-ListShiftDE[rDE];
        SumShift:=SumShift+eShift;
      od;
      eSum:=6-eDeg-SumShift;
      eRes:=eSum mod 6;
      if eRes>0 then
        Print("Wrong residue around vertices\n");
        Print(NullMat(5));
      fi;
    od;
  fi;
  #
  ListRational:=[];
  for eNSP in NSP
  do
    eVectRat1:=[];
    eVectRat2:=[];
    for eEnt in eNSP
    do
      hVal:=Eisenstein_GetExpression(eEnt);
      a:=hVal[1];
      b:=hVal[2];
      Append(eVectRat1, [a,b]);
      Append(eVectRat2, [0, a] + [-b,b]);
    od;
    Add(ListRational, eVectRat1);
    Add(ListRational, eVectRat2);
  od;
  ListEquationIntegral:=[];
  for eEqua in ListEquation
  do
    eEqua1:=[];
    eEqua2:=[];
#   (a+bw) (x+yw) = ax + by ww + w (bx + ay)
#                 = ax + by (-1+w) + w (bx + ay)
#                 = ax - by + w (bx + ay + by)
    for eEnt in eEqua
    do
      hVal:=Eisenstein_GetExpression(eEnt);
      a:=hVal[1];
      b:=hVal[2];
      Append(eEqua1, [a,-b]);
      Append(eEqua2, [b, a+b]);
    od;
    Add(ListEquationIntegral, eEqua1);
    Add(ListEquationIntegral, eEqua2);
  od;
  ListIntegralSolution:=NullspaceIntMat(TransposedMat(ListEquationIntegral));
  TheQuadFormExpanded:=NullMat(2*nbP, 2*nbP);
  ListQuadFormExpanded:=[];
  ListQuadFormReducedIntegral:=[];
  ListInfos:=[];
  for eO in VEFori.FaceSet
  do
    iDE1:=eO[1];
    iDE2:=OnPoints(iDE1, VEFori.eNextF);
    if Position(eO, iDE2)=fail then
      Print("Please debug from here\n");
      Print(NullMat(5));
    fi;
    i1_1:=2*iDE1-1;
    i1_2:=2*iDE1;
    i2_1:=2*iDE2-1;
    i2_2:=2*iDE2;
    eMat:=NullMat(2*nbP, 2*nbP);
    eMat[i1_1][i2_2]:=1/2;
    eMat[i2_2][i1_1]:=1/2;
    eMat[i1_2][i2_1]:=-1/2;
    eMat[i2_1][i1_2]:=-1/2;
#    Add(ListQuadFormExpanded, eMat);
    Add(ListQuadFormReducedIntegral, ListIntegralSolution*eMat*TransposedMat(ListIntegralSolution));
    TheQuadFormExpanded:=TheQuadFormExpanded+eMat;
    Add(ListInfos, rec(eList:=List(NSP, x->[x[iDE1], x[iDE2]])));
  od;
  TheQuadFormReduced:=ListRational*TheQuadFormExpanded*TransposedMat(ListRational);
  TheQuadFormReducedIntegral:=ListIntegralSolution*TheQuadFormExpanded*TransposedMat(ListIntegralSolution);
  ListVector:=List(ListQuadFormReducedIntegral, SymmetricMatrixToVector);
  TheConstraint:=rec(ListStrictlyPositive:=[],
                     ListPositive:=[1..Length(ListVector)], 
                     ListSetStrictPositive:=[ [1..Length(ListVector)] ]);
  eReply:=SearchPositiveRelation(ListVector, TheConstraint);
  if eReply<>false then
    return "invalid";
#    Print("We have a positivity relation, impossible\n");
#    Print(NullMat(5));
  fi;
#  eDiagInfo:=DiagonalizeSymmetricMatrix(TheQuadFormReduced);
  eDiagInfo:=DiagonalizeSymmetricMatrix(TheQuadFormReducedIntegral);
  return rec(NSP:=NSP, 
             ListEquation:=ListEquation, 
             ListEquationIntegral:=ListEquationIntegral, 
             ListIntegralSolution:=ListIntegralSolution, 
             TheQuadFormExpanded:=TheQuadFormExpanded, 
             TheQuadFormReduced:=TheQuadFormReduced,
             TheQuadFormReducedIntegral:=TheQuadFormReducedIntegral,
             ListQuadFormReducedIntegral:=ListQuadFormReducedIntegral,
             nbPlus:=eDiagInfo.nbPlus, 
             nbMinus:=eDiagInfo.nbMinus, 
             nbZero:=eDiagInfo.nbZero, 
             ListInfos:=ListInfos, 
             h:=h);
end;


ComputeParameterSetEisenstein:=function(GRPstruct, PLori)
  local eHomolInfo, VEFori, ListVertexDegree, nbCycle, ListCycleIntegral;
  eHomolInfo:=HomologyInformation(PLori);
  VEFori:=eHomolInfo.VEFori;
  ListVertexDegree:=List(VEFori.VertSet, Length);
  nbCycle:=Length(eHomolInfo.ListFundamentalCycleInfo);
  ListCycleIntegral:=ListWithIdenticalEntries(nbCycle,0);
  return Kernel_ComputeParameterSetEisenstein(GRPstruct, PLori, eHomolInfo, ListVertexDegree, ListCycleIntegral);
end;



AngleParameterizationFormalismComputation:=function(GRPstruct, ePLori)
  local eInv, eNext, nbP, eIterFace, eIterFaceInv, ListSpannLinear, eIdx1, eIdx2, eIdx3, eLine1, eLine2, eIdx1b, eIdx2b, MatrixDeltaLinear, MatrixDeltaAff, eProd, eRank, eLine, eFace, eEdge, eVert, eRankAff, eRankLinear, ListEquaLinear, ListEquaLinearEdge, ListEquaLinearFace, ListEquaLinearVert, ListEquaAff, eProdLinear, eProdAff, NSPlinear, NSPaff, eIdx, eDelta, eSum, eVert1, eVert2, eVert1b, eVert2b, eRankComplex, ListCycleEvaluationVert, ListCycleEvaluationHomol, eVect, eCycle, eHomolInfo, eRec, posEdge1, posEdge2, iDEsel, eSize1, eSize2, iFace1, iFace2, iDE1, iDE2, ePLoriDual, AnnulationProperties, VEFori, NSPlinearProperties, NSPkernel, NSPkernelB, ListProjection, Bside, Bsol, Bmat, NewVect, TestInvarianceEdge, InvarianceNSPlinearProperties, InvarianceProdLinear, TestInvarianceDirectedEdge, eRankLinearProj, eProdLinearProj, DirProjection;
  eInv:=ePLori.invers;
  eNext:=ePLori.next;
  nbP:=ePLori.nbP;
  eIterFace:=eNext*eInv;
  eIterFaceInv:=Inverse(eIterFace);
  VEFori:=PlanGraphOrientedToVEF(ePLori);
  ePLoriDual:=DualGraphOriented(ePLori);
  eHomolInfo:=HomologyInformation(ePLoriDual);
  if eHomolInfo.VEFori.EdgeSet<>VEFori.EdgeSet then
    Print("One hypothesis is broken\n");
    Print(NullMat(5));
  fi;
  ListSpannLinear:=[];
  ListEquaLinearFace:=[];
  ListEquaAff:=[];
  for eFace in VEFori.FaceSet
  do
    if Length(eFace)<>3 then
      Print("The size of the face is not correct\n");
      Print(NullMat(5));
    fi;
    eIdx1:=eFace[1];
    eIdx2:=OnPoints(eIdx1, eIterFace);
    eIdx3:=OnPoints(eIdx2, eIterFace);
    eLine1:=ListWithIdenticalEntries(nbP,0);
    eLine1[eIdx1]:=1;
    eLine1[eIdx2]:=-1;
    eLine2:=ListWithIdenticalEntries(nbP,0);
    eLine2[eIdx2]:=1;
    eLine2[eIdx3]:=-1;
    Add(ListSpannLinear, eLine1);
    Add(ListSpannLinear, eLine2);
    #
    eLine:=ListWithIdenticalEntries(nbP,0);
    eLine[eIdx1]:=-1;
    eLine[eIdx2]:=-1;
    eLine[eIdx3]:=-1;
    Add(ListEquaLinearFace, eLine);
    #
    eLine:=ListWithIdenticalEntries(1+nbP,0);
    eLine[1]:=1;
    eLine[1+eIdx1]:=-1;
    eLine[1+eIdx2]:=-1;
    eLine[1+eIdx3]:=-1;
    Add(ListEquaAff, eLine);
  od;
  ListEquaLinearVert:=[];
  for eVert in VEFori.VertSet
  do
    eSum:=Length(eVert);
    eDelta:=2 - eSum/3;
    eLine:=ListWithIdenticalEntries(1+nbP,0);
    eLine[1]:=eDelta;
    for eIdx in eVert
    do
      eLine[1+eIdx]:=-1;
    od;
    Add(ListEquaAff, eLine);
    #
    eLine:=ListWithIdenticalEntries(nbP,0);
    for eIdx in eVert
    do
      eLine[eIdx]:=-1;
    od;
    Add(ListEquaLinearVert, eLine);
  od;
  ListEquaLinear:=Concatenation(ListEquaLinearFace, ListEquaLinearVert);
  NSPlinear:=NullspaceMat(TransposedMat(ListEquaLinear));
  MatrixDeltaLinear:=[];
  ListEquaLinearEdge:=[];
  for eEdge in VEFori.EdgeSet
  do
    eIdx1:=eEdge[1];
    eIdx2:=eEdge[2];
    eVert1:=VEFori.ListOriginVert[eIdx1];
    eVert2:=VEFori.ListOriginVert[eIdx2];
    eIdx1b:=OnPoints(eIdx1, eIterFace);
    eIdx2b:=OnPoints(eIdx2, eIterFace);
    eVert1b:=VEFori.ListOriginVert[eIdx1b];
    eVert2b:=VEFori.ListOriginVert[eIdx2b];
    eLine:=ListWithIdenticalEntries(nbP,0);
    eLine[eIdx1b]:=1;
    eLine[eIdx2b]:=1;
    Add(ListEquaLinearEdge, eLine);
    Add(MatrixDeltaLinear, eLine);
  od;
  ListCycleEvaluationVert:=[];
  for eVert in VEFori.VertSet
  do
    eVect:=ListWithIdenticalEntries(nbP,0);
    for eIdx in eVert
    do
      eIdx1:=OnPoints(eIdx, eIterFace);
      eIdx2:=OnPoints(eIdx1, eIterFace);
      eVect[eIdx1]:=1;
      eVect[eIdx2]:=-1;
    od;
    Add(ListCycleEvaluationVert, eVect);
  od;
  ListCycleEvaluationHomol:=[];
  for eCycle in eHomolInfo.ListFundamentalCycleInfo
  do
    eVect:=ListWithIdenticalEntries(nbP,0);
    for eRec in eCycle.ListVertexInfo
    do
      posEdge1:=eRec.ListPos[1];
      posEdge2:=eRec.ListPos[2];
      iDE1:=VEFori.EdgeSet[posEdge1][1];
      iDE2:=VEFori.EdgeSet[posEdge1][2];
      iFace1:=VEFori.ListOriginFace[iDE1];
      iFace2:=VEFori.ListOriginFace[iDE2];
      eSize1:=Length(Intersection(Set(VEFori.EdgeSet[posEdge2]), Set(VEFori.FaceSet[iFace1])));
      eSize2:=Length(Intersection(Set(VEFori.EdgeSet[posEdge2]), Set(VEFori.FaceSet[iFace2])));
      if eSize1=1 then
        iDEsel:=iDE1;
      elif eSize2=1 then
        iDEsel:=iDE2;
      else
        Print("Inconsistency in finding\n");
        Print(NullMat(5));
      fi;
      eIdx1:=OnPoints(iDEsel, eIterFace);
      eIdx2:=OnPoints(eIdx1, eIterFace);
      if Position(VEFori.EdgeSet[posEdge2], eIdx1)<>fail then
        eVect[eIdx1]:=eVect[eIdx1]+1;
        eVect[eIdx2]:=eVect[eIdx2]-1;
      elif Position(VEFori.EdgeSet[posEdge2], eIdx2)<>fail then
        eVect[eIdx1]:=eVect[eIdx1]-1;
        eVect[eIdx2]:=eVect[eIdx2]+1;
      else
        Print("Inconsistency in finding 2\n");
        Print(NullMat(5));
      fi;
    od;
    Add(ListCycleEvaluationHomol, eVect);
  od;
  AnnulationProperties:=function(eVect)
    local pos, AnnulVert, AnnulHomol;
    pos:=First(ListCycleEvaluationVert, x->x*eVect<>0);
    if pos<>fail then
      AnnulVert:=false;
    else
      AnnulVert:=true;
    fi;
    pos:=First(ListCycleEvaluationHomol, x->x*eVect<>0);
    if pos<>fail then
      AnnulHomol:=false;
    else
      AnnulHomol:=true;
    fi;
    return rec(AnnulVert:=AnnulVert, AnnulHomol:=AnnulHomol);
  end;
  eProdLinear:=NSPlinear*TransposedMat(MatrixDeltaLinear);
  eRankLinear:=RankMat(eProdLinear);
  NSPkernel:=NullspaceMat(eProdLinear);
  NSPkernelB:=List(NSPkernel, x->x*NSPlinear);
  DirProjection:=NullspaceMat(TransposedMat(Concatenation(ListEquaLinearFace, ListEquaLinearEdge)));
  ListProjection:=[];
  for eVect in NSPlinear
  do
    Bside:=List(DirProjection, x->x*eVect);
    Bmat:=List(DirProjection, x->List(DirProjection, y->y*x));
    Bsol:=Bside*Inverse(Bmat);
    NewVect:=eVect - Bsol*DirProjection;
    Add(ListProjection, NewVect);
  od;
  eProdLinearProj:=ListProjection*TransposedMat(MatrixDeltaLinear);
  eRankLinearProj:=RankMat(eProdLinearProj);
  TestInvarianceEdge:=function(GRPstructInput, eVect)
    local eGen, eList, eEdge, fEdge, pos, ePerm;
    for eGen in GeneratorsOfGroup(GRPstructInput)
    do
      eList:=[];
      for eEdge in VEFori.EdgeSet
      do
        if eEdge<>Set(eEdge) then
          Print("One assumption is broken\n");
          Print(NullMat(5));
        fi;
        fEdge:=Set(List(eEdge, x->OnPoints(x, eGen)));
#        Print("eGen=", eGen, "\n");
#        Print("eEdge=", eEdge, " fEdge=", fEdge, "\n");
        pos:=Position(VEFori.EdgeSet, fEdge);
        Add(eList, pos);
      od;
      ePerm:=PermList(eList);
#      Print("ePerm=", ePerm, "\n");
      if Permuted(eVect, ePerm)<>eVect then
        return false;
      fi;
    od;
    return true;
  end;
  TestInvarianceDirectedEdge:=function(GRPstructInput, eVect)
    local eGen;
    for eGen in GeneratorsOfGroup(GRPstructInput)
    do
      if Permuted(eVect, eGen)<>eVect then
        return false;
      fi;
    od;
    return true;
  end;
  NSPlinearProperties:=List(ListProjection, AnnulationProperties);
  InvarianceNSPlinearProperties:=List(ListProjection, x->TestInvarianceDirectedEdge(GRPstruct, x));
  InvarianceProdLinear:=List(eProdLinear, x->TestInvarianceEdge(GRPstruct, x));
  eRankComplex:=(2+eRankLinear)/2;
  return rec(MatrixDeltaLinear:=MatrixDeltaLinear, 
             ListProjection:=ListProjection,
             NSPlinear:=NSPlinear, 
             VEFori:=VEFori, 
             ListCycleEvaluationVert:=ListCycleEvaluationVert, 
             ListCycleEvaluationHomol:=ListCycleEvaluationHomol, 
             ListEquaLinearEdge:=ListEquaLinearEdge, 
             ListEquaLinearVert:=ListEquaLinearVert, 
             ListEquaLinearFace:=ListEquaLinearFace, 
             ListEquaLinear:=ListEquaLinear, 
             ListSpannLinear:=ListSpannLinear,
             AnnulationProperties:=AnnulationProperties,
             NSPlinearProperties:=NSPlinearProperties,
             TestInvarianceDirectedEdge:=TestInvarianceDirectedEdge, 
             eProdLinear:=eProdLinear, 
             InvarianceNSPlinearProperties:=InvarianceNSPlinearProperties, 
             InvarianceProdLinear:=InvarianceProdLinear, 
             eProdLinearProj:=eProdLinearProj, 
             eRankLinearProj:=eRankLinearProj, 
             eRankComplex:=eRankComplex, 
             eRankLinear:=eRankLinear);
end;


PrintConjectureResult:=function(output, ePLori)
  local VEFori, nbVert, nbEdge, nbFace, PoincareChar, eGenus, ListValency, alpha, eDefect, eRecParam, nPlus, nDim, nMinus, nZero, ListAlpha, eValency, eCorrConjecture, eRecParamAngle, GRPstruct;
  VEFori:=PlanGraphOrientedToVEF(ePLori);
  nbVert:=Length(VEFori.VertSet);
  nbEdge:=Length(VEFori.EdgeSet);
  nbFace:=Length(VEFori.FaceSet);
  PoincareChar:=nbVert - nbEdge + nbFace;
  eGenus:=(2-PoincareChar)/2;
  ListValency:=List(VEFori.VertSet, Length);
  ListAlpha:=[];
  GRPstruct:=Group(());
  for eValency in ListValency
  do
    alpha:=(6 - eValency)/6;
    while(true)
    do
      if alpha < 0 then
        alpha:=alpha+1;
      else
        if alpha >= 1 then
          alpha:=alpha-1;
        else
          break;
        fi;
      fi;
    od;
    Add(ListAlpha, alpha);
  od;
  if First(ListAlpha, x->x<>0)=fail then
    eDefect:=0;
  else
    eDefect:=1;
  fi;
  AppendTo(output, "  (V,E,F)=(", nbVert, ",", nbEdge, ",", nbFace, ")\n");
  AppendTo(output, "  eGenus=", eGenus, "\n");
  AppendTo(output, "  ", nbVert, " vertices of valencies ", Collected(ListValency), "\n");
  eRecParam:=ComputeParameterSetEisenstein(GRPstruct, ePLori);
  AppendTo(output, "  |NSP|=", Length(eRecParam.NSP),
           " nbPlus=", eRecParam.nbPlus/2,
           " nbMinus=", eRecParam.nbMinus/2,
           " nbZero=", eRecParam.nbZero/2, "\n");
  nPlus:=eGenus + Sum(ListAlpha) - eDefect;
  nDim:=nbVert - 1 - eDefect + 2*eGenus;
  if eDefect=1 then
    nMinus:=nDim-nPlus;
    nZero:=0;
  else
    nMinus:=eGenus;
    nZero:=nDim-nPlus-nMinus;
  fi;
  eCorrConjecture:=true;
  if nDim<>Length(eRecParam.NSP) then
    eCorrConjecture:=false;
  fi;
  if nPlus<>eRecParam.nbPlus/2 then
    eCorrConjecture:=false;
  fi;
  if nMinus<>eRecParam.nbMinus/2 then
    eCorrConjecture:=false;
  fi;
  if nZero<>eRecParam.nbZero/2 then
    eCorrConjecture:=false;
  fi;
  AppendTo(output, "  nDim =", nDim, "  nPlus=", nPlus, "  nMinus=", nMinus, ", nZero=", nZero, "\n");
  eRecParamAngle:=AngleParameterizationFormalismComputation(GRPstruct, ePLori);
  AppendTo(output, "  Angle: nr complex=", eRecParamAngle.eRankComplex, " eRankLinear=", eRecParamAngle.eRankLinear, "\n");
  if eCorrConjecture=false then
    AppendTo(output, "Conjecture is false in that case\n");
  fi;
  AppendTo(output, "\n");
end;

