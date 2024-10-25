FileScriptReadNr:=Filename(DirectoriesPackagePrograms("plangraph"),"ScriptReadNr");
#
# 
# We are searching for ({2,3},6)-spheres.
# they satisfy nbV=2+p3/2
# The method is to take the dual of such sphere
# and to remove the vertices of degree 2 in them
# the result has p3 vertices and faces of gonality
# 6,5,4,3
# One has p3=2(nbV-2)
# For some purpose, we are searching a sphere with
# 8 vertices, i.e. 
ReadPLClogfileNr:=function(TheFileLOG)
  local TheNRfile, TheCommand, TheR;
  TheNRfile:=Filename(PLANGRAPH_tmpdir, "TheNrFile");
  TheCommand:=Concatenation(FileScriptReadNr, " ", TheFileLOG , " > ", TheNRfile);
  Exec(TheCommand);
  TheR:=ReadAsFunction(TheNRfile)();
  RemoveFile(TheNRfile);
  return TheR.nb;
end;

IsCorrectGraph123_6_graphs:=function(PLori)
  local VEFori, ListSize, p1, p2, p3, eSum;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  if First(VEFori.VertSet, x->Length(x)<>6)<>fail then
    return false;
  fi;
  ListSize:=List(VEFori.FaceSet, x->Length(x));
  p1:=Length(Filtered(ListSize, x->x=1));
  p2:=Length(Filtered(ListSize, x->x=2));
  p3:=Length(Filtered(ListSize, x->x=3));
  eSum:=p1*2 + p2;
  if eSum <> 6 then
    return false;
  fi;
  return true;
end;


123_GetTrifolium:=function()
  local eListNext, eListInv, PLori;
  eListNext:=[2,3,4,5,6,1];
  eListInv:=[2,1,4,3,6,5];
  PLori:=rec(next:=PermList(eListNext), invers:=PermList(eListInv), nbP:=6);
  return rec(PLori:=PLori, eGRP:="C3v");
end;

123_Class2_vertex2_graph1:=function()
  return rec(PLori:=rec( invers := (1,2)(3,5)(4,7)(6,8)(9,11)(10,12), nbP := 12,
                         next := (1,3,6,7,10,12)(2,4,8,5,9,11) ), 
             GRP:="C2");
end;

123_Class2_vertex2_graph2:=function()
  return rec(PLori:=rec( invers := (1,2)(3,5)(4,7)(6,8)(9,11)(10,12), nbP := 12,
                         next := (1,3,6,7,9,11)(2,4,8,10,12,5) ), 
             GRP:="C2h");
end;







Get2NgraphsFrom3valent_General:=function(TheDeg, PLori)
  local nbEdge, nbFace, ListDefect, SetMod, ListActiveEdge, iEdge, eEdge, iDE, jDE, iFace, jFace, ListSolution, i, ListNewSolution, eSolution, eRec, LPL, iType, NewSetDE, NewListDE, eListNext, eListInv, NewPLori, eDEinv, eDEnext, jEdge, VEFori, eDE, eNewListDefect, eNewEdgeVector, eNewSolution;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  nbEdge:=VEFori.nbEdge;
  nbFace:=VEFori.nbFace;
  ListDefect:=List(VEFori.FaceSet, x->TheDeg - Length(x));
  SetMod:=Set(List(ListDefect, x->x mod 2));
  if SetMod<>[0] then
    return [];
  fi;  
  ListActiveEdge:=[];
  for iEdge in [1..nbEdge]
  do
    eEdge:=VEFori.EdgeSet[iEdge];
    iDE:=eEdge[1];
    jDE:=eEdge[2];
    iFace:=VEFori.ListOriginFace[iDE];
    jFace:=VEFori.ListOriginFace[jDE];
    if Length(VEFori.FaceSet[iFace])=4 and Length(VEFori.FaceSet[jFace])=4 then
      Add(ListActiveEdge, rec(iEdge:=iEdge, ijFace:=[iFace, jFace]));
    fi;
  od;
  ListSolution:=[rec(EdgeVector:=ListWithIdenticalEntries(nbEdge,0), ListDefect:=ShallowCopy(ListDefect))];
  for i in [1..3]
  do
    ListNewSolution:=[];
    for eSolution in ListSolution
    do
      for eRec in ListActiveEdge
      do
        iEdge:=eRec.iEdge;
        iFace:=eRec.ijFace[1];
        jFace:=eRec.ijFace[2];
        if eSolution.ListDefect[iFace]=2 and eSolution.ListDefect[jFace]=2 then
          eNewEdgeVector:=ShallowCopy(eSolution.EdgeVector);
          eNewEdgeVector[iEdge]:=1;
          eNewListDefect:=ShallowCopy(eSolution.ListDefect);
          eNewListDefect[iFace]:=0;
          eNewListDefect[jFace]:=0;
          eNewSolution:=rec(EdgeVector:=eNewEdgeVector, ListDefect:=eNewListDefect);
          Add(ListNewSolution, eNewSolution);
        fi;
      od;
    od;
    ListSolution:=ShallowCopy(ListNewSolution);
  od;
  LPL:=[];
  for eSolution in ListSolution
  do
    NewListDE:=[];
    for iEdge in [1..nbEdge]
    do
      if eSolution[iEdge]=0 then
        for iDE in VEFori.EdgeSet[iEdge]
        do
          eRec:=rec(iType:=0, iDE:=iDE);
          Add(NewListDE, eRec);
        od;
      else
        for iDE in VEFori.EdgeSet[iEdge]
        do
          for iType in [1..4]
          do
            eRec:=rec(iType:=iType, iDE:=iDE);
            Add(NewListDE, eRec);
          od;
        od;
      fi;
    od;
    NewSetDE:=Set(NewListDE);
    eListNext:=[];
    eListInv:=[];
    for eDE in NewSetDE
    do
      iDE:=eDE.iDE;
      if eDE.iType=0 then
        jDE:=OnPoints(iDE, PLori.next);
        jEdge:=VEFori.ListOriginEdge[jDE];
        if eSolution[jEdge]=0 then
          eDEnext:=rec(iType:=0, iDE:=jDE);
        else
          eDEnext:=rec(iType:=4, iDE:=jDE);
        fi;
        eDEinv:=rec(iType:=0, iDE:=OnPoints(iDE, PLori.invers));
      elif eDE.iType=1 then
        eDEnext:=rec(iType:=2, iDE:=iDE);
        eDEinv:=rec(iType:=4, iDE:=iDE);
      elif eDE.iType=2 then
        eDEnext:=rec(iType:=3, iDE:=iDE);
        eDEinv:=rec(iType:=3, iDE:=OnPoints(iDE, PLori.invers));
      elif eDE.iType=3 then
        eDEnext:=rec(iType:=1, iDE:=iDE);
        eDEinv:=rec(iType:=2, iDE:=OnPoints(iDE, PLori.invers));
      else
        jDE:=OnPoints(iDE, PLori.next);
        jEdge:=VEFori.ListOriginEdge[jDE];
        if eSolution[jEdge]=0 then
          eDEnext:=rec(iType:=0, iDE:=jDE);
        else
          eDEnext:=rec(iType:=4, iDE:=jDE);
        fi;
        eDEinv:=rec(iType:=1, iDE:=iDE);
      fi;
      Add(eListNext, eDEnext);
      Add(eListInv, eDEinv);
    od;
    if Set(eListNext)<>NewSetDE then
      Print("Discontinuity 1\n");
      Print(NullMat(5));
    fi;
    if Set(eListInv)<>NewSetDE then
      Print("Discontinuity 2\n");
      Print(NullMat(5));
    fi;
    NewPLori:=rec(nbP:=Length(NewSetDE), invers:=SortingPerm(eListInv), next:=SortingPerm(eListNext));
    Add(LPL, NewPLori);
  od;
  return LPL;
end;

Get2NgraphsFrom3valent:=function(PLori)
  return Get2NgraphsFrom3valent_General(6, PLori);
end;


IsGraphPotentiallyGenerating:=function(PL)
  local DualPL, nbFace, ThePenalty, iFace, lenA, TheNb1, TheNb2, eV, TheNb;
  DualPL:=DualGraph(PL).PlanGraph;
  nbFace:=Length(DualPL);
  ThePenalty:=0;
  for iFace in [1..nbFace]
  do
    lenA:=Length(DualPL[iFace]);
    if lenA<6 then
      TheNb1:=6-lenA;
      TheNb2:=0;
      for eV in DualPL[iFace]
      do
        TheNb2:=TheNb2 + 6-Length(DualPL[eV]);
      od;
      TheNb:=Minimum(TheNb1, TheNb2);
      ThePenalty:=ThePenalty+TheNb;
    fi;
  od;
  if ThePenalty < 12 then
    return false;
  fi;
  return true;
end;


TruncationOriented:=function(PLori)
  local nbP, eNext, ePrev, GetPosition, ListDE, i, j, eListNext, eListInv, iDE, eNextDE, eInvDE, posNext, posInv, jDE, eDE, eNewNext, eNewInv;
  nbP:=PLori.nbP;
  eNext:=PLori.next;
  ePrev:=Inverse(PLori.next);
  ListDE:=[];
  for i in [1..nbP]
  do
    for j in [1..3]
    do
      Add(ListDE, [i,j]);
    od;
  od;
  eListNext:=[];
  eListInv:=[];
  for eDE in ListDE
  do
    iDE:=eDE[1];
    j:=eDE[2];
    eNextDE:=[iDE, NextIdx(3,j)];
#    Print("eDE=", eDE, "  eNextDE=", eNextDE, "\n");
    if j=1 then
      jDE:=OnPoints(iDE, PLori.invers);
      eInvDE:=[jDE, 1];
    elif j=2 then
      jDE:=OnPoints(iDE, eNext);
      eInvDE:=[jDE, 3];
    elif j=3 then
      jDE:=OnPoints(iDE, ePrev);
      eInvDE:=[jDE, 2];
    else
      Print("Inconsistency here\n");
      Print(NullMat(5));
    fi;
    posNext:=Position(ListDE, eNextDE);
    posInv:=Position(ListDE, eInvDE);
    Add(eListNext, posNext);
    Add(eListInv, posInv);
  od;
  eNewNext:=PermList(eListNext);
  eNewInv:=PermList(eListInv);
  if eNewNext=fail or eNewInv=fail then
    Error("Bug in TruncationOriented");
  fi;
  return rec(nbP:=3*nbP, next:=eNewNext, invers:=eNewInv);
end;




InverseTruncationOriented:=function(PLori)
  local VEFori, nbP, NewInv, NewNext, GRP2, O, GRPvert, GRPvertExt, LPL, IsCorrect, eO, ListVert, ListVertSets, eVert, iVert, Overt, eListNext, eListInv, iDE, iDEnext, iDEinv, NewPLori, eVertP, eVertR, NSet, test, ImageTruncPLori;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  if Set(List(VEFori.VertSet, Length))<>[3] then
    Print("only degree 3 is allowed\n");
    Print(NullMat(5));
  fi;
  nbP:=PLori.nbP;
  NewInv:=PLori.invers;
  NewNext:=PLori.next*PLori.invers*PLori.next;
  GRP2:=Group([NewInv, NewNext]);
  O:=Orbits(GRP2, [1..nbP], OnPoints);
  GRPvert:=Group([NewNext]);
  GRPvertExt:=Group([NewNext, PLori.next]);
  LPL:=[];
  IsCorrect:=function(ListSets)
    local nbSet, iSet, jSet, eInt;
    nbSet:=Length(ListSets);
    for iSet in [1..nbSet-1]
    do
      for jSet in [iSet+1..nbSet]
      do
        eInt:=Intersection(ListSets[iSet], ListSets[jSet]);
        if Length(eInt)<>0 then
          return false;
        fi;
      od;
    od;
    return true;
  end;
#  Print("|O|=", Length(O), "\n");
  for eO in O
  do
    ListVert:=Orbits(GRPvert, eO, OnPoints);
#    Print("  |eO|=", Length(eO), " |ListVert|=", Length(ListVert), "\n");
    ListVertSets:=[];
    for eVert in ListVert
    do
      eVertP:=List(eVert, x->OnPoints(x, PLori.next));
      eVertR:=List(eVert, x->OnPoints(x, Inverse(PLori.next)));
      NSet:=Set(Concatenation(eVert, eVertP, eVertR));
      Add(ListVertSets, NSet);
    od;
    if IsCorrect(ListVertSets)=true then
      eListNext:=[];
      eListInv:=[];
      for iDE in eO
      do
        iDEnext:=OnPoints(iDE, NewNext);
        iDEinv:=OnPoints(iDE, NewInv);
        Add(eListNext, Position(eO, iDEnext));
        Add(eListInv, Position(eO, iDEinv));
      od;
      NewPLori:=rec(invers:=PermList(eListInv), next:=PermList(eListNext), nbP:=Length(eO));
      ImageTruncPLori:=TruncationOriented(NewPLori);
      test:=IsIsomorphicPlanGraphOriented(ImageTruncPLori, PLori);
      if test<>true then
        Error("Inconsistency in InverseTruncationOriented");
      fi;
      Add(LPL, NewPLori);
    fi;
  od;
  return LPL;
end;


GoldbergConstructionThreeValentOriented:=function(PLori,i,j)
  local TheTrigOri, VEFori, PreListStandardPosition, ListStandardPosition, xpos, ypos, ListVertBeforeQuotient, eTrig, ePos, Rotation1, Rotation2, Rotation3, Rotation1rec, Rotation2rec, Rotation3rec, nbElt, Gra, iP, fTrig, NewPos1, NewPos2, NewPos3, Position1, Position2, Position3, eEdge1, eEdge2, eEdge3, eTrig1, eTrig2, eTrig3, nbVert, VertexSet, ListHexAdj, NewTriangulation, ListOrd,  iVert, jVert, nbadj, iHex, pos1, pos2, NewVert1, NewVert2, EltCons, iRepr, jv1, jv2, eListNext, eListInv, RetPLori, posDE1, posDE2, nbP, eDE1, eDE2, jVert1, jVert2, ListVectConn, PreListDE, ListDE, iHexB, GetPositionVBbis, GetPositionVB, iTrig, eDE, rDE, iHexM, eSetVert, NewVert, iEdgeRev1, iEdgeRev2, iEdgeRev3, iTrig1, iTrig2, iTrig3, pos, iEdge1, iEdge2, iEdge3, nbStd, iPos, pos3, Rotation, RotationRev, RotationIter, RotationRevIter, ePt1, ePt2, ePt3, ListPT, eCent, iEdge, iEdgeRev, jTrig, ePosB, ePosC, k, l, len, DoNext, NewPos, jP, ListDirectedEdgeBeforeQuotient, iDir, fPos, jPos, jDir, kPos, eRec, GetSingleDirection, nbCase, iCase, gPos;
  TheTrigOri:=DualGraphOriented(PLori);
  VEFori:=PlanGraphOrientedToVEF(TheTrigOri);
  PreListStandardPosition:=[];
  for xpos in [-j..i]
  do
    for ypos in [0..i+j]
    do
      if xpos+ypos>=0 and xpos+ypos<=i+j then
        Add(PreListStandardPosition, [xpos,ypos]);
      fi;
    od;
  od;
  ListStandardPosition:=Set(PreListStandardPosition);
  nbStd:=Length(ListStandardPosition);
  # OrdTrig:=[[0,0],[i,j],[-j,i+j]];
  # creation of the set
  ListVertBeforeQuotient:=[];
  for iTrig in [1..VEFori.nbFace]
  do
    for iPos in [1..nbStd]
    do
      Add(ListVertBeforeQuotient, [iTrig, iPos]);
    od;
  od;
  GetPositionVB:=function(ePair)
    local i,j;
    i:=ePair[1];
    j:=ePair[2];
    return nbStd*(iTrig-1)+iPos;
  end;
  GetPositionVBbis:=function(ePair)
    local pos;
    pos:=Position(ListStandardPosition, ePair[2]);
    if pos=fail then
      return fail;
    fi;
    return GetPositionVB([ePair[1], pos]);
  end;
  nbElt:=Length(ListVertBeforeQuotient);
  #rotation of angle (pi/3) stabilizing (0,0)
  Rotation:=function(k,l)
    return [-l,k+l];
  end;
  RotationRev:=function(k,l)
    return [l+k,-k];
  end;
  # rotation of x of center eCent by k (pi/3)
  RotationIter:=function(x, eCent, k)
    local eRet, i;
    eRet:=x-eCent;
    for i in [1..k]
    do
      eRet:=Rotation(eRet); 
    od;
    return eRet+eCent;
  end;
  RotationRevIter:=function(x, eCent, k)
    local eRet, i;
    eRet:=x-eCent;
    for i in [1..k]
    do
      eRet:=RotationRev(eRet); 
    od;
    return eRet+eCent;
  end;
  # quotienting the set to get the vertices
  Gra:=NullGraph(Group(()),nbElt);
  ePt1:=[0,0];
  ePt2:=[k,l];
  ePt3:=Rotation(ePt2);
  ListPT:=[ePt1, ePt2, ePt3];
  eCent:=(ePt1+ePt2+ePt3)/3;
  for iP in [1..nbElt]
  do
    iTrig:=ListVertBeforeQuotient[iP][1];
    ePos:=ListStandardPosition[ListVertBeforeQuotient[iP][2]];
    #
    for i in [1..3]
    do
      iEdge:=VEFori.FaceSet[iTrig][i];
      iEdgeRev:=OnPoints(iEdge, TheTrigOri.invers);
      jTrig:=VEFori.ListOriginFace[iEdgeRev];
      pos:=Position(VEFori.FaceSet[jTrig], iEdgeRev);
      ePosB:=RotationIter(ePos, eCent,2*(i-1));
      ePosC:=[i,j]-ePosB;
      NewPos:=RotationRevIter(ePosC, eCent, 2*(pos-1));
      jP:=GetPositionVBbis([iTrig,NewPos]);
      if jP<>fail then
        AddEdgeOrbit(Gra,[iP,jP]);
        AddEdgeOrbit(Gra,[jP,iP]);
      fi;
    od;
  od;
  VertexSet:=ConnectedComponents(Gra);
  nbVert:=Length(VertexSet);
  Print("nbVert=", nbVert, "\n");
  ListVectConn:=ListWithIdenticalEntries(nbElt,0);
  for iVert in [1..nbVert]
  do
    eSetVert:=VertexSet[iVert];
    ListVectConn{eSetVert}:=ListWithIdenticalEntries(Length(eSetVert), iVert);
  od;
  ListHexAdj:=[[1,0],[0,1],[-1,1],[-1,0],[0,-1],[1,-1]];
  ListDE:=[];
  for iVert in [1..nbVert]
  do
    len:=Length(VertexSet[iVert]);
    ListDirectedEdgeBeforeQuotient:=[];
    for iRepr in [1..len]
    do
      iP:=VertexSet[iVert][iRepr];
      iTrig:=ListVertBeforeQuotient[iP][1];
      iPos:=ListVertBeforeQuotient[iP][2];
      ePos:=ListStandardPosition[iPos];
      for iDir in [1..6]
      do
        fPos:=ePos+ListHexAdj[iDir];
        jPos:=Position(ListStandardPosition, fPos);
        jDir:=NextIdx(6,iDir);
        gPos:=ePos+ListHexAdj[jDir];
        kPos:=Position(ListStandardPosition, gPos);
        if jPos<>fail then
          jVert:=ListVectConn[jPos];
          eRec:=rec(iVert:=iVert, iP:=iP, iRepr:=iRepr, jVert:=jVert, ePos:=ePos, fPos:=fPos);
          Add(ListDirectedEdgeBeforeQuotient, eRec);
        fi;
        if kPos<>fail and jPos<>fail then

        fi;
      od;
    od;
    nbCase:=Length(ListDirectedEdgeBeforeQuotient);
    for iCase in [1..nbCase]
    do
      eRec:=ListDirectedEdgeBeforeQuotient[iCase];
      iP:=eRec.iP;
      iTrig:=ListVertBeforeQuotient[iP][1];
      iPos:=ListVertBeforeQuotient[iP][2];
      ePos:=ListStandardPosition[iPos];
    od;
  od;
  GetSingleDirection:=function(iVert)
    local iRepr, iTrig, iPos, ePos, fPos, jPos;
    iDir:=1;
    for iRepr in [1..Length(VertexSet[iVert])]
    do
      iTrig:=ListVertBeforeQuotient[iP][1];
      iPos:=ListVertBeforeQuotient[iP][2];
      ePos:=ListStandardPosition[iPos];
      fPos:=ePos+ListHexAdj[iDir];
      jPos:=Position(ListStandardPosition, fPos);
      if jPos<>fail then
        return rec(iVert:=iVert, jVert:=ListVectConn[jPos], iRepr:=iRepr, iDir:=iDir);
      fi;
    od;
  end;
  DoNext:=function(eDE)
    iVert:=eDE.iVert;
    len:=Length(VertexSet[iVert]);
    for i in [1..len]
    do
    od;
  end;
  for iVert in [1..nbVert]
  do
    for iRepr in [1..Length(VertexSet[iVert])]
    do
      EltCons:=ListVertBeforeQuotient[VertexSet[iVert][iRepr]];
      iTrig:=EltCons[1];
      ePos:=ListStandardPosition[EltCons[2]];
      for iHex in [1..6]
      do
        NewVert:=[iTrig,ePos+ListHexAdj[iHex]];
        pos:=GetPositionVBbis(NewVert);
        if pos<>fail then
          jVert:=ListVectConn[pos];
          iHexM:=iHex mod 2;
          eDE:=[iVert, jVert, iHexM];
          Add(PreListDE, eDE);
        fi;
      od;
    od;
  od;
  ListDE:=Set(PreListDE);
  nbP:=Length(ListDE);
  eListInv:=[];
  for eDE in ListDE
  do
    rDE:=[eDE[2], eDE[1], 1-eDE[3]];
    Add(eListInv, Position(ListDE, rDE));
  od;
  eListNext:=ListWithIdenticalEntries(nbP,0);
  for iVert in [1..nbVert]
  do
    ListOrd:=[];
    for iRepr in [1..Length(VertexSet[iVert])]
    do
      EltCons:=ListVertBeforeQuotient[VertexSet[iVert][iRepr]];
      iTrig:=EltCons[1];
      ePos:=ListStandardPosition[EltCons[2]];
      for iHex in [1..6]
      do
        NewVert1:=[iTrig,ePos+ListHexAdj[iHex]];
        iHexB:=NextIdx(6,iHex);
        NewVert2:=[iTrig,ePos+ListHexAdj[iHexB]];
        pos1:=GetPositionVBbis(NewVert1);
        pos2:=GetPositionVBbis(NewVert2);
        if pos1<>fail and pos2<>fail then
          jVert1:=ListVectConn[pos1];
          jVert2:=ListVectConn[pos2];
          eDE1:=[iVert, jVert1, iHex mod 2];
          eDE2:=[iVert, jVert2, iHexB mod 2];
          posDE1:=Position(ListDE, eDE1);
          posDE2:=Position(ListDE, eDE1);
          if eListNext[posDE1]=0 then
            eListNext[posDE1]:=posDE2;
          else
            if eListNext[posDE1]<>posDE2 then
              Print("We have reached a major inconsistency\n");
              Print(NullMat(5));
            fi;
          fi;
        fi;
      od;
    od;
  od;
  RetPLori:=rec(nbP:=nbP, next:=PermList(eListNext), invers:=PermList(eListInv));
  return DualGraphOriented(RetPLori);
end;




IsGraphPotentiallyGeneratingGeneralized:=function(PL)
  return true;
end;

GetEdgeAssignment:=function(TheDeg, ThePL)
  local VEF, ListEdges, ListFaces, nbFace, nbEdge, IncidenceMat, TargetVect, iFace, eFace, eDE, rDE, eEdge, iEdge, ListCandVect, ListPossibilities, ListFinished, NewListCandVect, eCand, LPO, eVert, NewCand;
  VEF:=PlanGraphToVEFsecond(ThePL);
  ListEdges:=VEF[2];
  ListFaces:=VEF[3];
  nbFace:=Length(ListFaces);
  nbEdge:=Length(ListEdges);
  IncidenceMat:=NullMat(nbEdge, nbFace);
  TargetVect:=[];
  for iFace in [1..nbFace]
  do
    eFace:=ListFaces[iFace];
    Add(TargetVect, TheDeg - Length(ListFaces[iFace]));
    for eDE in eFace
    do
      rDE:=ReverseDE(ThePL, eDE);
      eEdge:=Set([eDE, rDE]);
      iEdge:=Position(ListEdges, eEdge);
      IncidenceMat[iEdge][iFace]:=1;
    od;
  od;
  ListCandVect:=[ListWithIdenticalEntries(Length(ListEdges),0)];
  ListPossibilities:=function(TheCandVect)
    local RelVect, ForbiddenEdges, iFace, TheSel, ListFinished;
    RelVect:=TargetVect-TheCandVect*IncidenceMat;
    ForbiddenEdges:=[];
    for iFace in [1..nbFace]
    do
      if RelVect[iFace]=0 then
        TheSel:=Filtered([1..nbEdge], x->IncidenceMat[x][iFace] > 0);
        ForbiddenEdges:=Union(ForbiddenEdges, TheSel);
      fi;
    od;
    return Difference([1..nbEdge], ForbiddenEdges);
  end;
  ListFinished:=[];
  while(true)
  do
    NewListCandVect:=[];
    for eCand in ListCandVect
    do
      LPO:=ListPossibilities(eCand);
      for eVert in LPO
      do
        NewCand:=ShallowCopy(eCand);
        NewCand[eVert]:=NewCand[eVert]+1;
        if TargetVect=NewCand*IncidenceMat then
          Add(ListFinished, NewCand);
        else
          Add(NewListCandVect, NewCand);
        fi;
      od;
    od;
    ListCandVect:=Set(NewListCandVect);
    if Length(ListCandVect)=0 then
      break;
    fi;
  od;
  return Set(ListFinished);
end;












# input is a plane graph with vertices of degree in {3..6}
# and with faces of size 3.
# It can also in principle be applied to graphs with vertices of valency two
# but then some hacking may have to be done to take into account the fact
# that we cannot double some edges and as well add 1-gon on the same
# edge. The program simply does not allow for it.
GetEdgeAssignmentGeneralized:=function(PLori)
  local LDE, ePrev, eNext, eInv, GroupVert, GroupEdge, GroupFace, EdgeSet, VertSet, FaceSet, ListEnumerationThird, NewPLori, eListNext, eListInv, SetListDE, eDE, iDEinv, iDEnext, GetFromIDEnext, i, eVal, iDE, ListEdgeStatus, ListDEstatus, iEdgeRed, iEdge, ListCorresp, iP, eFinished, NewListDE, nbP, eEdge, eDE1, eDE2, eF, eRec, eRecSecond, ListFinished, ListCandVect, TheDiff, ListVertWeight, NewCand, NewListCandVect, ListCorr, nbEdgeRed, ListConfSecondStepEnum, eCand, ListVector, IsCorrect, eRec1, eRec2, iSiz, ListEdgeSecond, iVert1, iVert2, eDeg1, eDeg2, ListVertStatus, ListVertDegree, eSet, nbEdge, eFace, iFace, ListFaceDegree, eVert, iVert, nbVert, nbFace, ListConfFirstStepEnum, ListFirstType, eVect, eC, j, ListFaceStatus, ListVertDegreeSimp, ListIEdgeCorr, pos, eDEtest;
  nbP:=PLori.nbP;
  LDE:=[1..nbP];
  ePrev:=Inverse(PLori.next);
  eNext:=PLori.next;
  eInv:=PLori.invers;
  GroupVert:=Group([eNext]);
  GroupEdge:=Group([eInv]);
  GroupFace:=Group([eInv*ePrev]);
  VertSet:=Orbits(GroupVert, LDE, OnPoints);
  EdgeSet:=Orbits(GroupEdge, LDE, OnPoints);
  FaceSet:=Orbits(GroupFace, LDE, OnPoints);
  nbVert:=Length(VertSet);
  nbEdge:=Length(EdgeSet);
  nbFace:=Length(FaceSet);
  Print("nbVert=", nbVert, " nbEdge=", nbEdge, " nbFace=", nbFace, "\n");
  ListVertStatus:=ListWithIdenticalEntries(nbP,0);
  ListEdgeStatus:=ListWithIdenticalEntries(nbP,0);
  ListFaceStatus:=ListWithIdenticalEntries(nbP,0);
  ListVertDegree:=ListWithIdenticalEntries(nbP,0);
  ListFaceDegree:=ListWithIdenticalEntries(nbP,0);
  ListVertDegreeSimp:=[];
  for iVert in [1..nbVert]
  do
    eVert:=VertSet[iVert];
    Add(ListVertDegreeSimp, Length(eVert));
    ListVertStatus{eVert}:=ListWithIdenticalEntries(Length(eVert), iVert);
    ListVertDegree{eVert}:=ListWithIdenticalEntries(Length(eVert), Length(eVert));
  od;
  for iEdge in [1..nbEdge]
  do
    eEdge:=EdgeSet[iEdge];
    ListEdgeStatus{eEdge}:=ListWithIdenticalEntries(Length(eEdge), iEdge);
  od;
  for iFace in [1..nbFace]
  do
    eFace:=FaceSet[iFace];
    ListFaceStatus{eFace}:=ListWithIdenticalEntries(Length(eFace), iFace);
    ListFaceDegree{eFace}:=ListWithIdenticalEntries(Length(eFace), Length(eFace));
  od;
  #
  ListFirstType:=[];
  ListVector:=[];
  ListIEdgeCorr:=[];
  ListCorresp:=ListWithIdenticalEntries(nbEdge, 0);
  iEdgeRed:=0;
  for iEdge in [1..nbEdge]
  do
    eEdge:=EdgeSet[iEdge];
    eDE1:=eEdge[1];
    eDE2:=eEdge[2];
    iVert1:=ListVertStatus[eDE1];
    iVert2:=ListVertStatus[eDE2];
    eDeg1:=ListVertDegree[eDE1];
    eDeg2:=ListVertDegree[eDE2];
    if eDeg1 < 6 and eDeg2 < 6 then
      eRec:=rec(iVert1:=iVert1, iVert2:=iVert2, iEdge:=iEdge);
      Add(ListIEdgeCorr, iEdge);
      eVect:=ListWithIdenticalEntries(nbVert,0);
      eVect[iVert1]:=1;
      eVect[iVert2]:=1;
      Add(ListFirstType, eRec);
      Add(ListVector, eVect);
      iEdgeRed:=iEdgeRed+1;
      ListCorresp[iEdge]:=iEdgeRed;
    fi;
  od;
  nbEdgeRed:=Length(ListVector);
  #
  ListEdgeSecond:=[];
  for iEdge in [1..nbEdge]
  do
    eEdge:=EdgeSet[iEdge];
    for eC in [[1,2], [2,1]]
    do
      eDE1:=eEdge[eC[1]];
      eDE2:=eEdge[eC[2]];
      iVert1:=ListVertStatus[eDE1];
      iVert2:=ListVertStatus[eDE2];
      eDeg1:=ListVertDegree[eDE1];
      eDeg2:=ListVertDegree[eDE2];
      if eDeg1<=3 and eDeg2<=5 then
        eRec:=rec(iVert1:=iVert1, iVert2:=iVert2, eDE1:=eDE1, eDE2:=eDE2, iEdge:=iEdge);
        Add(ListEdgeSecond, eRec);
      fi;
    od;
  od;
  ListConfFirstStepEnum:=[];
  for iSiz in [1..3]
  do
    for eSet in Combinations(ListEdgeSecond, iSiz)
    do
      IsCorrect:=true;
      for i in [1..iSiz-1]
      do
        for j in [i+1..iSiz]
        do
          eRec1:=eSet[i];
          eRec2:=eSet[j];
          if eRec1.iVert1=eRec2.iVert1 then
           IsCorrect:=false;
          fi;
        od;
      od;
      if IsCorrect=true then
        Add(ListConfFirstStepEnum, eSet);
      fi;
    od;
  od;
  ListConfSecondStepEnum:=[];
  for eRec in ListConfFirstStepEnum
  do
    ListVertWeight:=List(VertSet, x->6-Length(x));
    ListCorr:=ListWithIdenticalEntries(nbEdgeRed,1);
    for eF in eRec
    do
      ListVertWeight[eF.iVert1]:=ListVertWeight[eF.iVert1]-3;
      ListVertWeight[eF.iVert2]:=ListVertWeight[eF.iVert2]-1;
      ListCorr[eF.iEdge]:=0;
    od;
    if Minimum(ListVertWeight)>=0 then 
      if Maximum(ListVertWeight)=0 then
        ListFinished:=[ListWithIdenticalEntries(nbEdgeRed,0)];
      else
        ListCandVect:=[ListWithIdenticalEntries(nbEdgeRed,0)];
        ListFinished:=[];
        while(true)
        do
          NewListCandVect:=[];
          for eCand in ListCandVect
          do
            for iEdge in [1..nbEdgeRed]
            do
              NewCand:=ShallowCopy(eCand);
              NewCand[iEdge]:=NewCand[iEdge]+1;
              TheDiff:=ListVertWeight - NewCand*ListVector;
              if Minimum(TheDiff)>=0 then
                if Maximum(TheDiff)=0 then
                  Add(ListFinished, NewCand);
                else
                  Add(NewListCandVect, NewCand);
                fi;
              fi;
            od;
          od;
          ListCandVect:=Set(NewListCandVect);
          if Length(ListCandVect)=0 then
            break;
          fi;
        od;
      fi;
      if Length(ListFinished)>0 then
        eRecSecond:=rec(eRec:=eRec, ListFinished:=Set(ListFinished));
        Add(ListConfSecondStepEnum, eRecSecond);
      fi;
    fi;
  od;
  ListEnumerationThird:=[];
  for eRecSecond in ListConfSecondStepEnum
  do
    eRec:=eRecSecond.eRec;
    for eFinished in eRecSecond.ListFinished
    do
      NewListDE:=[];
      ListDEstatus:=ListWithIdenticalEntries(nbP, 1);
      for eF in eRec
      do
        eDE1:=eF.eDE1;
        eDE2:=eF.eDE2;
        ListDEstatus[eDE1]:=-3;
        ListDEstatus[eDE2]:=-4;
        for i in [1..4]
        do
          Add(NewListDE, [2, 1, i, eDE1]);
        od;
        for i in [1..2]
        do
          Add(NewListDE, [2, 2, i, eDE2]);
        od;
      od;
      for iEdgeRed in [1..nbEdgeRed]
      do
        eVal:=eFinished[iEdgeRed];
        if eVal>0 then
          iEdge:=ListFirstType[iEdgeRed].iEdge;
          eEdge:=EdgeSet[iEdge];
          eDE1:=eEdge[1];
          eDE2:=eEdge[2];
          ListDEstatus[eDE1]:=-1;
          ListDEstatus[eDE2]:=-1;
          for i in [0..eVal]
          do
            Add(NewListDE, [1,eVal,i,eDE1]);
            Add(NewListDE, [1,eVal,i,eDE2]);
          od;
        fi;
      od;
      for iP in [1..nbP]
      do
        if ListDEstatus[iP]=1 then
          Add(NewListDE, [0,0,0,iP]);
        fi;
      od;
      SetListDE:=Set(NewListDE);
      eListNext:=[];
      eListInv:=[];
      GetFromIDEnext:=function(iDEnext)
        local pos, iEdge, iEdgeRed, eVal;
        if ListDEstatus[iDEnext]=1 then
          pos:=Position(SetListDE, [0,0,0,iDEnext]);
        fi;
        if ListDEstatus[iDEnext]=-1 then
          iEdge:=ListEdgeStatus[iDEnext];
          iEdgeRed:=ListCorresp[iEdge];
          eVal:=eFinished[iEdgeRed];
          pos:=Position(SetListDE, [1,eVal,0,iDEnext]);
        fi;
        if ListDEstatus[iDEnext]=-3 then
          pos:=Position(SetListDE, [2,1,1,iDEnext]);
        fi;
        if ListDEstatus[iDEnext]=-4 then
          pos:=Position(SetListDE, [2,2,1,iDEnext]);
        fi;
        return pos;
      end;
      for eDE in SetListDE
      do
        if eDE[1]=0 then
          iDE:=eDE[4];
          iDEinv:=OnPoints(iDE, eInv);
          pos:=Position(SetListDE, [0,0,0,iDEinv]);
          if pos=fail then
            Print("Please debug from here 1\n");
            Print(NullMat(5));
          fi;
          Add(eListInv, pos);
          iDEnext:=OnPoints(iDE, eNext);
          Add(eListNext, GetFromIDEnext(iDEnext));
        fi;
        if eDE[1]=1 then
          eVal:=eDE[2];
          i:=eDE[3];
          if i<eVal then
            pos:=Position(SetListDE, [1,eVal,i+1,eDE[4]]);
            if pos=fail then
              Print("Please debug from here 2\n");
              Print(NullMat(5));
            fi;
            Add(eListNext, pos);
          else
            iDEnext:=OnPoints(eDE[4], eNext);
            Add(eListNext, GetFromIDEnext(iDEnext));
          fi;
          iDEinv:=OnPoints(eDE[4], eInv);
          eDEtest:=[1, eVal, eVal-i,iDEinv]; 
          pos:=Position(SetListDE, eDEtest);
          if pos=fail then
            Print("Please debug from here 3\n");
            Print(NullMat(5));
          fi;
          Add(eListInv, pos);
        fi;
        if eDE[1]=2 and eDE[2]=1 then
          i:=eDE[3];
          if i<4 then
            pos:=Position(SetListDE, [2,1,i+1,eDE[4]]);
            if pos=fail then
              Print("Please debug from here 4\n");
              Print(NullMat(5));
            fi;
            Add(eListNext, pos);
          else
            iDEnext:=OnPoints(eDE[4], eNext);
            Add(eListNext, GetFromIDEnext(iDEnext));
          fi;
          if i=2 or i=3 then
            pos:=Position(SetListDE, [2,1,5-i,eDE[4]]);
            if pos=fail then
              Print("Please debug from here 5\n");
              Print(NullMat(5));
            fi;
            Add(eListInv, pos);
          fi;
          iDEinv:=OnPoints(eDE[4], eInv);
          if i=1 then
            pos:=Position(SetListDE, [2,2,2,iDEinv]);
            if pos=fail then
              Print("Please debug from here 6\n");
              Print(NullMat(5));
            fi;
            Add(eListInv, pos);
          fi;
          if i=4 then
            pos:=Position(SetListDE, [2,2,1,iDEinv]);
            if pos=fail then
              Print("Please debug from here 7\n");
              Print(NullMat(5));
            fi;
            Add(eListInv, pos);
          fi;
        fi;
        if eDE[1]=2 and eDE[2]=2 then
          i:=eDE[3];
          if i<2 then
            pos:=Position(SetListDE, [2,2,i+1,eDE[4]]);
            if pos=fail then
              Print("Please debug from here 8\n");
              Print(NullMat(5));
            fi;
            Add(eListNext, pos);
          else
            iDEnext:=OnPoints(eDE[4], eNext);
            Add(eListNext, GetFromIDEnext(iDEnext));
          fi;
          iDEinv:=OnPoints(eDE[4], eInv);
          if i=1 then
            pos:=Position(SetListDE, [2,1,4,iDEinv]);
            if pos=fail then
              Print("Please debug from here 9\n");
              Print(NullMat(5));
            fi;
            Add(eListInv, pos);
          fi;
          if i=2 then
            pos:=Position(SetListDE, [2,1,1,iDEinv]);
            if pos=fail then
              Print("Please debug from here 10\n");
              Print(NullMat(5));
            fi;
            Add(eListInv, pos);
          fi;
        fi;
      od;
      if PermList(eListNext)=fail then
        Print("Please debug from here (eListNext not a permutation)\n");
        Print(NullMat(5));
      fi;
      NewPLori:=rec(nbP:=Length(SetListDE), next:=PermList(eListNext), invers:=PermList(eListInv));
      Add(ListEnumerationThird, NewPLori);
    od;
  od;
  return ListEnumerationThird;
end;


GetEdgeAssignmentOrbitwise:=function(TheDeg, ThePL)
  local GRP, nbEdge, nbVert, ListPermGens, eGen, eList, iEdge, GRPedge, ListCandVect, O, ListRet, eO;
  GRP:=GroupPlan(ThePL);
  nbEdge:=Length(GRP.CC.ThePartition[2]);
  nbVert:=Length(GRP.CC.ThePartition[1]);
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRP.SymmetryGroup)
  do
    eList:=[];
    for iEdge in [1..nbEdge]
    do
      Add(eList, OnPoints(iEdge+nbVert, eGen)-nbVert);
    od;
    Add(ListPermGens, PermList(eList));
  od;
  GRPedge:=PersoGroupPerm(ListPermGens);
  ListCandVect:=GetEdgeAssignment(TheDeg, ThePL);
  O:=Orbits(GRPedge, ListCandVect, Permuted);
  ListRet:=[];
  for eO in O
  do
    Add(ListRet, eO[1]);
  od;
  return ListRet;
end;

SearchSpecial23_6sphere:=function(ThePL)
  local VEF, ListEdges, nbEdge, ListEdgesRed, ListEdgeOrbit, ListIncidentEdges, iVert, Linc, i, eDE, rDE, eEdge, ListCorrectVect, eVect, ListMatched, TheDeg;
  VEF:=PlanGraphToVEFsecond(ThePL);
  ListEdges:=VEF[2];
  nbEdge:=Length(ListEdges);
  TheDeg:=6;
  ListEdgesRed:=List(ListEdges, x->Set([x[1][1], x[2][1]]));
  ListEdgeOrbit:=GetEdgeAssignmentOrbitwise(TheDeg, ThePL);
  ListIncidentEdges:=[];
  for iVert in [1..Length(ThePL)]
  do
    Linc:=[];
    for i in [1..3]
    do
      eDE:=[iVert,i];
      rDE:=ReverseDE(ThePL, eDE);
      eEdge:=Set([eDE, rDE]);
      Add(Linc, Position(ListEdges, eEdge));
    od;
    Add(ListIncidentEdges, Linc);
  od;
  ListCorrectVect:=[];
  for eVect in ListEdgeOrbit
  do
    ListMatched:=Filtered([1..nbEdge], x->eVect[x]>0);
    for iVert in [1..Length(ThePL)]
    do
      if IsSubset(ListMatched, ListIncidentEdges[iVert])=true then
        Add(ListCorrectVect, eVect);
      fi;
    od;
  od;
  return ListCorrectVect;
end;


Pre_AddDegreeTwoVertices:=function(ThePL, eSE)
  local ListEdges, nbVert, NewListVert, iVert, nbEdge, ListCritDE, ListCritIDX, ListCritIEdge, iEdge, eVal, eEdge, eDE1, eDE2, RetPL, eVert, iV, jV, ListAdj, eIdx, fVert, eListAdj, eDE, pos, i;
  ListEdges:=__EdgeSet(ThePL);
  nbVert:=Length(ThePL);
  NewListVert:=[];
  for iVert in [1..nbVert]
  do
    Add(NewListVert, [0, iVert]);
  od;
  nbEdge:=Length(ListEdges);
  ListCritDE:=[];
  ListCritIDX:=[];
  ListCritIEdge:=[];
  for iEdge in [1..nbEdge]
  do
    eVal:=eSE[iEdge];
    eEdge:=ListEdges[iEdge];
    if eVal>0 then
      eDE1:=eEdge[1];
      eDE2:=eEdge[2];
      Add(ListCritDE, eDE1);
      Add(ListCritDE, eDE2);
      Add(ListCritIDX, 1);
      Add(ListCritIDX, 2);
      Add(ListCritIEdge, iEdge);
      Add(ListCritIEdge, iEdge);
      for i in [1..eVal]
      do
        Add(NewListVert, [1, rec(iEdge:=iEdge, iV:=i, jV:=eVal+1-i)]);
      od;
    fi;
  od;
  RetPL:=[];
  for eVert in NewListVert
  do
    ListAdj:=[];
    if eVert[1]=1 then
      iEdge:=eVert[2].iEdge;
      iV:=eVert[2].iV;
      jV:=eVert[2].jV;
      if iV=1 then
        eDE:=ListEdges[iEdge][1];
        fVert:=[0, eDE[1]];
      else
        fVert:=[1, rec(iEdge:=iEdge, iV:=iV-1, jV:=jV+1)];
      fi;
      Add(ListAdj, Position(NewListVert, fVert));
      if jV=1 then
        eDE:=ListEdges[iEdge][2];
        fVert:=[0, eDE[1]];
      else
        fVert:=[1, rec(iEdge:=iEdge, iV:=iV+1, jV:=jV-1)];
      fi;
      Add(ListAdj, Position(NewListVert, fVert));
    else
      iVert:=eVert[2];
      eListAdj:=ThePL[iVert];
      for i in [1..Length(eListAdj)]
      do
        eDE:=[iVert, i];
        pos:=Position(ListCritDE, eDE);
        if pos=fail then
          fVert:=[0, eListAdj[i]];
        else
          eIdx:=ListCritIDX[pos];
          iEdge:=ListCritIEdge[pos];
          eVal:=eSE[iEdge];
          if eIdx=1 then
            fVert:=[1, rec(iEdge:=iEdge, iV:=1, jV:=eVal)];
          else
            fVert:=[1, rec(iEdge:=iEdge, iV:=eVal, jV:=1)];
          fi;
        fi;
        Add(ListAdj, Position(NewListVert, fVert));
      od;
    fi;
    Add(RetPL, ListAdj);
  od;
  return RetPL;
end;

AddDegreeTwoVertices:=function(ThePL, eSE)
  return DualGraph(Pre_AddDegreeTwoVertices(ThePL, eSE)).PlanGraph;
end;





MatrixOfIntersectionsWithTypes_SAV:=function(PLori, ListVertStatus, LZZ)
  local Matri, nbZZ, ROW, iZZ, jZZ, TT;
  nbZZ:=Length(LZZ);
  Matri:=[];
  for iZZ in [1..nbZZ]
  do
    ROW:=[];
    for jZZ in [1..nbZZ]
    do
      ROW[jZZ]:=[];
    od;
    Matri[iZZ]:=ROW;
  od;
  for iZZ in [1..nbZZ]
  do
    for jZZ in [1..nbZZ]
    do
      if iZZ=jZZ then
        TT:=SelfMatchingDirEdgeOriented(PLori, ListVertStatus, LZZ[iZZ]);
        Matri[iZZ][jZZ]:=[Length(TT[2]), Length(TT[3])];
      else
        TT:=MatchingDirEdgeOriented(PLori, LZZ[iZZ], LZZ[jZZ]);
        Matri[iZZ][jZZ]:=[Length(TT[1]), Length(TT[2])];
      fi;
    od;
  od;
  return Matri;
end;




DetermineZigZagCharacteristic23_6sphereOriented:=function(PLori)
  local ZZinfo, VEFori, ListFace, eFace, len, IsIrreducible, nbZZ, ListTestIrred, eZigZag, eIrred, eRec, eDE, eDE2, pos, pos2, len2, eIrredP, eIrredN, eIrredPsecond, eIrredNsecond, IsIrreducibleSecond, IsSimple, iZZ, nbP, eNext, ePrev, eInv, ListLenZigZag, iFace, iFace2;
  ZZinfo:=ZigZagOriented(PLori);
  nbP:=PLori.nbP;
  eNext:=PLori.next;
  eInv:=PLori.invers;
  ePrev:=Inverse(PLori.next);
  VEFori:=PlanGraphOrientedToVEF(PLori);
  IsIrreducible:=true;
  IsIrreducibleSecond:=true;
  nbZZ:=Length(ZZinfo.ListZigZag);
  ListTestIrred:=[];
  ListLenZigZag:=[];
  for iZZ in [1..nbZZ]
  do
    eZigZag:=ZZinfo.ListZigZag[iZZ];
    Add(ListLenZigZag, ZZinfo.Invariants[iZZ][1]);
    eIrredP:=false;
    eIrredN:=false;
    eIrredPsecond:=false;
    eIrredNsecond:=false;
    for eRec in eZigZag
    do
      if eRec[1]="P" then
        eDE:=eRec[2];
        eDE2:=OnPoints(eDE, eNext);
        iFace:=VEFori.ListOriginFace[eDE];
        iFace2:=VEFori.ListOriginFace[eDE2];
        len:=Length(VEFori.FaceSet[iFace]);
        len2:=Length(VEFori.FaceSet[iFace2]);
        if len<>3 or len2<>3 then
          eIrredPsecond:=true;
        fi;
        if len<>3 then
          eIrredP:=true;
        fi;
      fi;
      if eRec[1]="N" then
        eDE:=eRec[2];
        eDE2:=OnPoints(eDE, ePrev);
        iFace:=VEFori.ListOriginFace[OnPoints(eDE, eInv)];
        iFace2:=VEFori.ListOriginFace[OnPoints(eDE2, eInv)];
        len:=Length(VEFori.FaceSet[iFace]);
        len2:=Length(VEFori.FaceSet[iFace2]);
        if len<>3 or len2<>3 then
          eIrredNsecond:=true;
        fi;
        if len<>3 then
          eIrredN:=true;
        fi;
      fi;
    od;
    Add(ListTestIrred, rec(eIrredP:=eIrredP, eIrredN:=eIrredN));
    if eIrredP=false or eIrredN=false then
      IsIrreducible:=false;
    fi;
    if eIrredPsecond=false or eIrredNsecond=false then
      IsIrreducibleSecond:=false;
    fi;
  od;
  IsSimple:=true;
  for iZZ in [1..nbZZ]
  do
    if ZZinfo.Zmatrix[iZZ][iZZ]<>[0,0] then
      IsSimple:=false;
    fi;
  od;
  return rec(IsIrreducible:=IsIrreducible,
             IsIrreducibleSecond:=IsIrreducibleSecond,
             ListTestIrred:=ListTestIrred,
             ListLenZigZag:=ListLenZigZag, 
             Zvector:=ZZinfo.Zvector,
             IsSimple:=IsSimple, 
             nbZZ:=nbZZ);
end;





#
# PlanGraph must be 6-valent.
23sphereCentralCircuitOriented:=function(PLori)
  local ListTot, nbDE, nbVert, ListCircuit, z, Sequence, SequenceRev, v, ListFace, ListLength, eFace, len, eDE, pos, ListIrreducible, IsIrreducible, eCircuit, IsTightR, IsTightL, eDEl, eDEr, posR, posL, lenR, lenL, ListSimple, IsSimple, IsSimpleGraph, eStatus, eVert, TheMax, IsTightRsecond, IsTightLsecond, eDEr2, eDEl2, posR2, posL2, lenR2, lenL2, IsIrreducibleSecond, ListIrreducibleSecond, nbP, eNext, ePrev, eInv, eIter, VEFori, CCstring, ListLen, mult, eStr, eInfo, i, ListStatusDE, nbCC, ListLenCircuit, GetSequence, iCC, ListSymbol, eSymb, TheInt1, TheInt2, TheLen, SetCircuit, SetCircuitImg1, SetCircuitImg2, nbDoubl, nbTriple, ListVertCircuit;
  nbP:=PLori.nbP;
  ListCircuit:=[];
  eInv:=PLori.invers;
  eNext:=PLori.next;
  ePrev:=Inverse(PLori.next);
  ListStatusDE:=ListWithIdenticalEntries(nbP,1);
  eIter:=eInv*eNext*eNext*eNext;
  GetSequence:=function(z)
    local Sequence, zInv, v, vInv;
    Sequence:=[z];
    zInv:=OnPoints(z, eInv);
    ListStatusDE[z]:=0;
    ListStatusDE[zInv]:=0;
    v:=OnPoints(z, eIter);
    vInv:=OnPoints(v, eInv);
    while(v<>z)
    do
      ListStatusDE[v]:=0;
      ListStatusDE[vInv]:=0;
      Add(Sequence, v);
      v:=OnPoints(v, eIter);
      vInv:=OnPoints(v, eInv);
    od;
    return Sequence;
  end;
  for i in [1..nbP]
  do
    if ListStatusDE[i]=1 then
      Add(ListCircuit, GetSequence(i));
    fi;
  od;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  nbVert:=Length(VEFori.VertSet);
  ListLength:=ListWithIdenticalEntries(nbP, 0);
  for eFace in VEFori.FaceSet
  do
    len:=Length(eFace);
    ListLength{eFace}:=ListWithIdenticalEntries(len, len);
  od;
  ListIrreducible:=[];
  IsIrreducible:=true;
  ListIrreducibleSecond:=[];
  IsIrreducibleSecond:=true;
  nbCC:=Length(ListCircuit);
  ListLenCircuit:=[];
  ListSymbol:=[];
  for iCC in [1..nbCC]
  do
    eCircuit:=ListCircuit[iCC];
    ListVertCircuit:=Collected(VEFori.ListOriginVert{eCircuit});
    nbDoubl:=Length(Filtered(ListVertCircuit, x->x[2]=2));
    nbTriple:=Length(Filtered(ListVertCircuit, x->x[2]=3));
    TheLen:=Length(eCircuit);
    Add(ListLenCircuit, TheLen);
    SetCircuit:=Set(eCircuit);
    SetCircuitImg1:=Set(OnTuples(eCircuit, PLori.next));
    SetCircuitImg2:=Set(OnTuples(eCircuit, PLori.next*PLori.next));
    TheInt1:=Length(Intersection(SetCircuit, SetCircuitImg1));
    TheInt2:=Length(Intersection(SetCircuit, SetCircuitImg2));
    if TheInt1=0 and TheInt2=0 then
      eSymb:=String(TheLen);
    else
      eSymb:=Concatenation(String(TheLen), "_{", String(TheInt1), ",", String(TheInt2), ",", String(nbDoubl), ",", String(nbTriple), "}");
    fi;
    Add(ListSymbol, eSymb);
    IsTightR:=false;
    IsTightL:=false;
    IsTightRsecond:=false;
    IsTightLsecond:=false;
    for eDEr in eCircuit
    do
      lenR:=ListLength[eDEr];
      if lenR<>3 then
        IsTightR:=true;
      fi;
      eDEr2:=OnPoints(eDEr, eNext);
      lenR2:=ListLength[eDEr2];
      if lenR<>3 or lenR2<>3 then
        IsTightRsecond:=true;
      fi;
      #
      eDEl:=OnPoints(eDEr, eInv);
      lenL:=ListLength[eDEl];
      if lenL<>3 then
        IsTightL:=true;
      fi;
      eDEl2:=OnPoints(eDEl, eNext);
      lenL2:=ListLength[eDEl2];
      if lenL<>3 or lenL2<>3 then
        IsTightLsecond:=true;
      fi;
    od;
    if IsTightR=false or IsTightL=false then
      IsIrreducible:=false;
    fi;
    if IsTightRsecond=false or IsTightLsecond=false then
      IsIrreducibleSecond:=false;
    fi;
    Add(ListIrreducible, rec(IsTightR:=IsTightR, IsTightL:=IsTightL));
    Add(ListIrreducibleSecond, rec(IsTightR:=IsTightRsecond, IsTightL:=IsTightLsecond));
  od;
  ListSimple:=[];
  IsSimpleGraph:=true;
  for eCircuit in ListCircuit
  do
    eStatus:=ListWithIdenticalEntries(nbVert, 0);
    for eDE in eCircuit
    do
      eVert:=VEFori.ListOriginVert[eDE];
      eStatus[eVert]:=eStatus[eVert]+1;
    od;
    TheMax:=Maximum(eStatus);
    if TheMax>1 then
      IsSimple:=false;
    else
      IsSimple:=true;
    fi;
    if IsSimple=false then
      IsSimpleGraph:=false;
    fi;
    Add(ListSimple, IsSimple);
  od;
  CCstring:="";
  eInfo:=Collected(ListSymbol);
  for i in [1..Length(eInfo)]
  do
    eStr:=eInfo[i][1];
    mult:=eInfo[i][2];
    if mult=1 then
      CCstring:=Concatenation(CCstring, eStr);
    else
      CCstring:=Concatenation(CCstring, eStr,"^",StringLatex(mult));
    fi;
    if i<Length(eInfo) then
      CCstring:=Concatenation(CCstring, ", ");
    fi;
  od;
  return rec(IsSimpleGraph:=IsSimpleGraph,
             ListSimple:=ListSimple,
             IsIrreducible:=IsIrreducible,
             ListIrreducible:=ListIrreducible, 
             IsIrreducibleSecond:=IsIrreducibleSecond, 
             ListIrreducibleSecond:=ListIrreducibleSecond, 
             ListCircuit:=ListCircuit, 
             ListLenCircuit:=ListLenCircuit, 
             CCstring:=CCstring, 
             nbCC:=nbCC);
end;







DoEnumerationSymbol:=function(nCall)
  local nSymb, TheOrder, ThePrefix, TheOrder2, TheFileInfo, H, nbFile, iFile, eFileData, LPL, ePL, LSE, ListData, TheRec, ListGroup, GRPinfo, eStab, GRP, eLSE, eLSEwork, eFilePLC, eFileLOG, TotalListData, eFileSave, TheDeg;
  nSymb:=2*(nCall-2);
  TheOrder:=Concatenation("CPF n ", String(nSymb), " f 3 f 4 f 5 f 6");
  Exec(TheOrder);
  #
  ThePrefix:="./tmpWork/PLdata";
  eFilePLC:=Concatenation("3reg_n", String(nSymb), "_f3_f4_f5_f6.plc");
  eFileLOG:=Concatenation("3reg_n", String(nSymb), "_f3_f4_f5_f6.log");
  TheOrder2:=Concatenation(FilePlanarlese2, " < ", eFilePLC, " | ", FileLeseToPG, " | ", FileSplitLPL, " ", ThePrefix, " 400");
  Exec(TheOrder2);
  Print("CPF output splitted\n");
  RemoveFileIfExist(eFilePLC);
  RemoveFileIfExist(eFileLOG);
  #
  TheFileInfo:=Concatenation(ThePrefix, "0");
  H:=ReadAsFunction(TheFileInfo)();
  RemoveFileIfExist(TheFileInfo);
  nbFile:=H[1];
  TheDeg:=6;
  for iFile in [1..nbFile]
  do
    Print("iFile=", iFile, "/", nbFile, "\n");
    eFileData:=Concatenation(ThePrefix, String(iFile));
    eFileSave:=Concatenation("./tmp/BLK", String(nCall), "_", String(iFile));
    if IsExistingFilePlusTouch(eFileSave)=false then
      ListData:=[];
      LPL:=ReadAsFunction(eFileData)();
      for ePL in LPL
      do
        if IsGraphPotentiallyGenerating(ePL)=true then
          LSE:=GetEdgeAssignmentOrbitwise(TheDeg, ePL);
          if Length(LSE) > 0 then
            GRP:=GroupPlan(ePL);
            ListGroup:=[];
            for eLSE in LSE
            do
              eLSEwork:=Concatenation(ListWithIdenticalEntries(Length(ePL), 0), eLSE);
              eStab:=Stabilizer(GRP.SymmetryGroup, eLSEwork, Permuted);
              GRPinfo:=GRP.FunctionSymmetry(eStab);
              Add(ListGroup, GRPinfo.SchoenfliesSymbol);
            od;
            TheRec:=rec(PL:=ePL, LSE:=LSE, ListGroup:=ListGroup);
            Add(ListData, TheRec);
          fi;
        fi;
      od;
      SaveDataToFilePlusTouch(eFileSave, ListData);
      RemoveFile(eFileData);
    fi;
  od;
  TotalListData:=[];
  for iFile in [1..nbFile]
  do
    eFileSave:=Concatenation("./tmp/BLK", String(nCall), "_", String(iFile));
    Append(TotalListData, ReadAsFunction(eFileSave)());
  od;  
  return TotalListData;
end;


DoEnumerationSymbolGeneralized:=function(nCall)
  local nSymb, TheOrder, ThePrefix, TheOrder2, TheFileInfo, H, nbFile, iFile, eFileData, LPL, ePL, ListData, GRPinfo, eStab, GRP, eLSE, eLSEwork, eFilePLC, eFileLOG, TotalListData, eFileSave, LPLori, iGen, jGen, ListStatus, ePLori, eGRP, test, nbGen, PLori, DualPLori;
  nSymb:=2*(nCall-2);
  TheOrder:=Concatenation("CPF n ", String(nSymb), " f 3 +1 f 4 f 5 f 6");
  Exec(TheOrder);
  #
  ThePrefix:="./tmpWork123/PLdata";
  eFilePLC:=Concatenation("3reg_n", String(nSymb), "_f3+1_f4_f5_f6.plc");
  eFileLOG:=Concatenation("3reg_n", String(nSymb), "_f3+1_f4_f5_f6.log");
  TheOrder2:=Concatenation(FilePlanarlese2, " < ", eFilePLC, " | ", FileLeseToPG, " | ", FileSplitLPL, " ", ThePrefix, " 400");
  Exec(TheOrder2);
  Print("CPF output splitted\n");
  RemoveFileIfExist(eFilePLC);
  RemoveFileIfExist(eFileLOG);
  #
  TheFileInfo:=Concatenation(ThePrefix, "0");
  H:=ReadAsFunction(TheFileInfo)();
  RemoveFileIfExist(TheFileInfo);
  nbFile:=H[1];
  for iFile in [1..nbFile]
  do
    Print("iFile=", iFile, "/", nbFile, "\n");
    eFileData:=Concatenation(ThePrefix, String(iFile));
    eFileSave:=Concatenation("./tmp123/BLK", String(nCall), "_", String(iFile));
    if IsExistingFilePlusTouch(eFileSave)=false then
      ListData:=[];
      LPL:=ReadAsFunction(eFileData)();
      for ePL in LPL
      do
        if IsGraphPotentiallyGeneratingGeneralized(ePL)=true then
          PLori:=PlanGraphToPlanGraphOriented(ePL);
          DualPLori:=DualGraphOriented(PLori);
          LPLori:=GetEdgeAssignmentGeneralized(DualPLori);
          nbGen:=Length(LPLori);
          ListStatus:=ListWithIdenticalEntries(nbGen,1);
          for iGen in [1..nbGen]
          do
            if ListStatus[iGen]=1 then
              ePLori:=LPLori[iGen];
              eGRP:=GroupPlanOriented(ePLori).SchoenfliesSymbol;
              Add(ListData, rec(PL:=ePL, PLori:=ePLori, eGRP:=eGRP));
              for jGen in [iGen+1..nbGen]
              do
                if ListStatus[jGen]=1 then
                  test:=IsIsomorphicPlanGraphOriented(LPLori[iGen], LPLori[jGen]);
                  if test=true then
                    ListStatus[jGen]:=0;
                  fi;
                fi;
              od;
            fi;
          od;
        fi;
      od;
      SaveDataToFilePlusTouch(eFileSave, ListData);
      RemoveFile(eFileData);
    fi;
  od;
  TotalListData:=[];
  for iFile in [1..nbFile]
  do
    eFileSave:=Concatenation("./tmp123/BLK", String(nCall), "_", String(iFile));
    Append(TotalListData, ReadAsFunction(eFileSave)());
  od;  
  return TotalListData;
end;


DoEnumerationSymbol13:=function(nCall)
  local nSymb, TheOrder, ThePrefix, TheOrder2, TheFileInfo, H, nbFile, iFile, eFileData, LPL, ePL, ListData, GRPinfo, eStab, GRP, eLSE, eLSEwork, eFilePLC, eFileLOG, TotalListData, eFileSave, LPLori, iGen, jGen, ListStatus, ePLori, eGRP, test, nbGen, PLori, PLoriW, LDE, GroupFace, FaceSet, DualPLori, nbT;
  nSymb:=2*(nCall-2);
  TheOrder:=Concatenation("CPF n ", String(nSymb), " f 3 +3 f 4 f 5 f 6");
  Exec(TheOrder);
  #
  ThePrefix:="./tmpWork13/PLdata";
  eFilePLC:=Concatenation("3reg_n", String(nSymb), "_f3+3_f4_f5_f6.plc");
  eFileLOG:=Concatenation("3reg_n", String(nSymb), "_f3+3_f4_f5_f6.log");
  nbT:=ReadPLClogfileNr(eFileLOG);
  if nbT=0 then
    return [];
  fi;
  TheOrder2:=Concatenation(FilePlanarlese2, " < ", eFilePLC, " | ", FileLeseToPG, " | ", FileSplitLPL, " ", ThePrefix, " 400");
  Exec(TheOrder2);
  Print("CPF output splitted\n");
  RemoveFileIfExist(eFilePLC);
  RemoveFileIfExist(eFileLOG);
  #
  TheFileInfo:=Concatenation(ThePrefix, "0");
  H:=ReadAsFunction(TheFileInfo)();
  RemoveFileIfExist(TheFileInfo);
  nbFile:=H[1];
  for iFile in [1..nbFile]
  do
    Print("iFile=", iFile, "/", nbFile, "\n");
    eFileData:=Concatenation(ThePrefix, String(iFile));
    eFileSave:=Concatenation("./tmp13/BLK", String(nCall), "_", String(iFile));
    if IsExistingFilePlusTouch(eFileSave)=false then
      ListData:=[];
      LPL:=ReadAsFunction(eFileData)();
      for ePL in LPL
      do
        PLori:=PlanGraphToPlanGraphOriented(ePL);
        DualPLori:=DualGraphOriented(PLori);
        LPLori:=GetEdgeAssignmentGeneralized(DualPLori);
        nbGen:=Length(LPLori);
        ListStatus:=ListWithIdenticalEntries(nbGen,1);
        for iGen in [1..nbGen]
        do
          PLoriW:=LPLori[iGen];
          LDE:=[1..PLoriW.nbP];
          GroupFace:=Group([PLoriW.next*PLoriW.invers]);
          FaceSet:=Orbits(GroupFace, LDE, OnPoints);
          if Position(List(FaceSet, Length), 2)<>fail then
            ListStatus[iGen]:=0;
          fi;
        od;
        for iGen in [1..nbGen]
        do
          if ListStatus[iGen]=1 then
            ePLori:=LPLori[iGen];
            eGRP:=GroupPlanOriented(ePLori).SchoenfliesSymbol;
            Add(ListData, rec(PL:=ePL, PLori:=ePLori, eGRP:=eGRP));
            for jGen in [iGen+1..nbGen]
            do
              if ListStatus[jGen]=1 then
                test:=IsIsomorphicPlanGraphOriented(LPLori[iGen], LPLori[jGen]);
                if test=true then
                  ListStatus[jGen]:=0;
                fi;
              fi;
            od;
          fi;
        od;
      od;
      SaveDataToFilePlusTouch(eFileSave, ListData);
      RemoveFile(eFileData);
    fi;
  od;
  TotalListData:=[];
  for iFile in [1..nbFile]
  do
    eFileSave:=Concatenation("./tmp13/BLK", String(nCall), "_", String(iFile));
    Append(TotalListData, ReadAsFunction(eFileSave)());
  od;  
  return TotalListData;
end;







EnumeratePossibilitiesSixValentGoldbergCoxeter_Directions:=function(MaxNorm, ListDirections, DoCheck)
  local ListSolution, ListStatus, nbSol, iSol, eDir, a, b, IsFinished, aP, h, TheSet, NewSol, eNorm, ePerm, ListNorm;
  ListSolution:=[[0,0]];
  ListNorm:=[0];
  ListStatus:=[0];
  while(true)
  do
    nbSol:=Length(ListSolution);
    IsFinished:=true;
    for iSol in [1..nbSol]
    do
      if ListStatus[iSol]=0 then
        ListStatus[iSol]:=1;
        for eDir in ListDirections
        do
          NewSol:=ListSolution[iSol]+eDir;
          a:=NewSol[1];
          b:=NewSol[2];
          eNorm:=a*a+a*b+b*b;
          if eNorm<=MaxNorm then
            if Position(ListSolution, NewSol)=fail then
              Add(ListSolution, NewSol);
              Add(ListNorm, eNorm);
              Add(ListStatus, 0);
            fi;
          fi;
        od;
        IsFinished:=false;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  nbSol:=Length(ListSolution);
  for iSol in [1..nbSol]
  do
    a:=ListSolution[iSol][1];
    b:=ListSolution[iSol][2];
    if a+b=0 then
      ListStatus[iSol]:=0;
    else
      if DoCheck=true then
        aP:=a-1;
        h:=(-aP+b)/3;
        if IsInt(h)=false then
          ListStatus[iSol]:=0;
        fi;
      fi;
    fi;
  od;
  TheSet:=Filtered([1..nbSol], x->ListStatus[x]=1);
  ePerm:=SortingPerm(ListNorm{TheSet});
  return Permuted(ListSolution{TheSet}, ePerm);
end;


EnumeratePossibilitiesSixValentGoldbergCoxeter_general:=function(MaxNorm)
  local ListDirections, DoCheck;
  ListDirections:=[[1,0], [0,1], [-1,1]];
  DoCheck:=true;
  return EnumeratePossibilitiesSixValentGoldbergCoxeter_Directions(MaxNorm, ListDirections, DoCheck);
end;


EnumeratePossibilitiesSixValentGoldbergCoxeter_planesym:=function(MaxNorm)
  local ListDirections, DoCheck;
  ListDirections:=[[1,0], [0,1]];
  DoCheck:=true;
  return EnumeratePossibilitiesSixValentGoldbergCoxeter_Directions(MaxNorm, ListDirections, DoCheck);
end;

EnumeratePossibilitiesSixValentGoldbergCoxeter_allthree_general:=function(MaxNorm)
  local ListDirections, DoCheck;
  ListDirections:=[[1,0], [0,1], [-1,1]];
  DoCheck:=false;
  return EnumeratePossibilitiesSixValentGoldbergCoxeter_Directions(MaxNorm, ListDirections, DoCheck);
end;



GetListPoints:=function(ePtStart, ListFacet, ListDirections)
  local ListSolution, ListStatus, nbSol, IsFinished, iSol, eDir, NewSol, IsOK, eIneq, ListReturn, a, b, h, SolExp;
  ListSolution:=[ePtStart];
  ListStatus:=[0];
  while(true)
  do
    nbSol:=Length(ListSolution);
    IsFinished:=true;
    for iSol in [1..nbSol]
    do
      if ListStatus[iSol]=0 then
        ListStatus[iSol]:=1;
        for eDir in ListDirections
        do
          NewSol:=ListSolution[iSol]+eDir;
          SolExp:=Concatenation([1], NewSol);
          IsOK:=true;
          for eIneq in ListFacet
          do
            if eIneq*SolExp<0 then
              IsOK:=false;
            fi;
          od;
          if IsOK=true then
            if Position(ListSolution, NewSol)=fail then
              Add(ListSolution, NewSol);
              Add(ListStatus, 0);
            fi;
          fi;
        od;
        IsFinished:=false;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  nbSol:=Length(ListSolution);
  ListReturn:=[];
  for iSol in [1..nbSol]
  do
    a:=ListSolution[iSol][1];
    b:=ListSolution[iSol][2];
    h:=(a-b)/3;
    if IsInt(h)=true or IsInt(h-1/3)=true then
      Add(ListReturn, [a,b]);
    fi;
  od;
  return ListReturn;
end;

#
# This is a limitation of the program: for k=1 and l=0
# we simply return the original, otherwise, it fails.
GoldbergConstructionSixValent:=function(PLori, k, l)
  local DualPL, Rotation60degrees, Rotation60degreesRev, LDE, ePrev, eNext, eInv, GroupVert, GroupEdge, GroupFace, VertSet, EdgeSet, FaceSet, nbFace, ListEXT, ListFacet, ListPoints, GetIFace, EdgeRotation, NewListVert, iFace, eRec, ePt, eCent, SetListVert, InversEList, NextEList, DoNext, DoInvers, nbDE, eDE, ListDE, lenAdj, h, iDE, i, iConn, Lconn, nbConn, PartListDE, ListConnIdx, GRA, eFace, eNewVert, nbVertFull, ListDirections, GetSingleDirection, eConn, pos, RecCorr, iVert, iBnd, eDErev, len, jConn, PLoriRet, ListVerticesHexagon, ListMiddlePoint, eTransVect, eMiddle, iNext, iBndP3, eVert, Rotation120degreesRev, eCentHexVert, Rotation120degrees, iBndNext, EdgeRotationIndex, PrintRecord, NbRot, NbRotCorr, nbPoint, iPoint, jPoint, ListStatusForTransform, test, eTestPt, iIneq, GetIneq, ListIneq, eSet, GetHexagon, ListPreEXT, ListVert;
  if k=1 and l=0 then
    return rec(invers:=PLori.invers, next:=PLori.next, nbP:=PLori.nbP);
  fi;
  DualPL:=DualGraphOriented(PLori);
  if l<0 then
    Print("Not in allowed range 1\n");
    Print(NullMat(5));
  fi;
  if k+l<=0 then
    Print("Not in allowed range 2\n");
    Print(NullMat(5));
  fi;
  if IsInt((k-1-l)/3)=false then
    Print("Not in the right multiplication invariant subset\n");
    Print(NullMat(5));
  fi;
  eCent:=[-l, k+l];
  Rotation60degrees:=function(eCent, ePt)
    local h, a, b, hTimesJ;
    h:=ePt-eCent;
    a:=h[1];
    b:=h[2];
    hTimesJ:=[-b, a+b];
    return eCent + hTimesJ;
  end;
  Rotation120degrees:=function(eCent, ePt)
    local h, a, b, hTimesJ;
    h:=ePt-eCent;
    a:=h[1];
    b:=h[2];
    hTimesJ:=[-a-b, a];
    return eCent + hTimesJ;
  end;
  Rotation60degreesRev:=function(eCent, ePt)
    local h, a, b, hTimesJr;
    h:=ePt-eCent;
    a:=h[1];
    b:=h[2];
    hTimesJr:=[a+b, -a];
    return eCent + hTimesJr;
  end;
  Rotation120degreesRev:=function(eCent, ePt)
    local h, a, b, hTimesJr;
    h:=ePt-eCent;
    a:=h[1];
    b:=h[2];
    hTimesJr:=[b, -a-b];
    return eCent + hTimesJr;
  end;
  ListVerticesHexagon:=[[0,0]];
  for i in [2..6]
  do
    Add(ListVerticesHexagon, Rotation60degrees(eCent, ListVerticesHexagon[i-1]));
  od;
  ListMiddlePoint:=[];
  for i in [1..6]
  do
    iNext:=NextIdx(6,i);
    eMiddle:=(ListVerticesHexagon[i]+ListVerticesHexagon[iNext])/2;
    Add(ListMiddlePoint, eMiddle);
  od;
#  Print("ListVerticesHexagon=", ListVerticesHexagon, "\n");
  LDE:=[1..DualPL.nbP];
  ePrev:=Inverse(DualPL.next);
  eNext:=DualPL.next;
  eInv:=DualPL.invers; 
  GroupVert:=Group([eNext]);
  GroupEdge:=Group([eInv]);
  GroupFace:=Group([eInv*ePrev]);
  VertSet:=Orbits(GroupVert, LDE, OnPoints);
  EdgeSet:=Orbits(GroupEdge, LDE, OnPoints);
  FaceSet:=Orbits(GroupFace, LDE, OnPoints);
  nbFace:=Length(FaceSet);
  ListDirections:=[[1,0], [0,1], [-1,1], [-1,0], [0,-1], [1,-1]];
  GetHexagon:=function(eFirstPoint, iDir, TheLen)
    local ListPoints, jDir, i, eNewPoint;
    ListPoints:=[eFirstPoint];
    jDir:=iDir;
    for i in [2..6]
    do
      eNewPoint:=ListPoints[i-1] + TheLen*ListDirections[jDir];
      Add(ListPoints, eNewPoint);
      jDir:=NextIdx(6,jDir);
    od;
    return ListPoints;
  end; 
  if k>0 then
    if l>0 or k=1 then
      ListEXT:=[[-l,0], [k,0], [k,k+l], [-l,2*k+2*l],
                [-k-2*l, 2*k+2*l], [-k-2*l, k+l]];
    else
      ListEXT:=GetHexagon([0,-1], 1, k+1);
    fi;
  else
    if k<0 then
      ListEXT:=GetHexagon([0,k], 2, l);
    else
      ListEXT:=[[1,-1], [1, l], [-l,2*l+1], [-2*l-1, 2*l+1],
                [-2*l-1,l], [-l,-1]];
    fi;
  fi;
  ListFacet:=DualDescription(List(ListEXT, x->Concatenation([1],x)));
  ListPoints:=GetListPoints([0,0], ListFacet, ListDirections);
  if l=0 then
    ListPoints:=Difference(Set(ListPoints), Set(ListEXT));
  fi;
  nbPoint:=Length(ListPoints);
  #
  GetIFace:=function(eDEidx)
    local iFace, pos;
    for iFace in [1..nbFace]
    do
      pos:=Position(FaceSet[iFace], eDEidx);
      if pos<>fail then
        return rec(iFace:=iFace, pos:=pos);
      fi;
    od;
    Print("Error !!!\n");
    Print(NullMat(5));
  end;
  EdgeRotation:=function(ePt)
    return [k,l] - ePt;
  end;
  ListStatusForTransform:=NullMat(nbPoint,6);
  GetIneq:=function(PassPt1, PassPt2, PossPt)
    local eHomPPt1, eHomPPt2, eNSP, eTestPt;
    eHomPPt1:=Concatenation([1], PassPt1);
    eHomPPt2:=Concatenation([1], PassPt2);
    eNSP:=NullspaceMat(TransposedMat([eHomPPt1, eHomPPt2]))[1];
    eTestPt:=Concatenation([1], PossPt);
    if eNSP*eTestPt>0 then
      return eNSP;
    fi;
    return -eNSP;
  end;
  ListIneq:=[];
  Add(ListIneq, -GetIneq(ListVerticesHexagon[1], ListVerticesHexagon[2], ListVerticesHexagon[3]));
  Add(ListIneq, GetIneq(ListVerticesHexagon[1], ListVerticesHexagon[5], ListVerticesHexagon[2]));
  Add(ListIneq, GetIneq(ListVerticesHexagon[2], ListVerticesHexagon[4], ListVerticesHexagon[1]));
  for iPoint in [1..nbPoint]
  do
    test:=true;
    eTestPt:=Concatenation([1], ListPoints[iPoint]);
    for iIneq in [1..Length(ListIneq)]
    do
      if ListIneq[iIneq]*eTestPt<0 then
        test:=false;
      fi;
    od;
    if test=true then
      ListStatusForTransform[iPoint][1]:=1;
    fi;
  od;
  for iPoint in [1..nbPoint]
  do
    if ListStatusForTransform[iPoint][1]=1 then
      ePt:=ListPoints[iPoint];
      ePt:=EdgeRotation(ePt);
      jPoint:=Position(ListPoints, ePt);
      if jPoint<>fail then
        ListStatusForTransform[jPoint][1]:=1;
      fi;
    fi;
  od;
  for i in [2..6]
  do
    for iPoint in [1..nbPoint]
    do
      ePt:=ListPoints[iPoint];
      ePt:=Rotation60degrees(eCent, ePt);
      jPoint:=Position(ListPoints, ePt);
      ListStatusForTransform[jPoint][i]:=ListStatusForTransform[iPoint][i-1];
    od;
  od;
  EdgeRotationIndex:=function(ePt, idx)
    local ePtW, i;
    ePtW:=[ePt[1], ePt[2]];
    for i in [2..idx]
    do
      ePtW:=Rotation60degreesRev(eCent, ePtW);
    od;
    ePtW:=EdgeRotation(ePtW);
    for i in [2..idx]
    do
      ePtW:=Rotation60degrees(eCent, ePtW);
    od;
    return ePtW;
  end;
  NewListVert:=[];
  for iFace in [1..nbFace]
  do
    for ePt in ListPoints
    do
      eRec:=rec(iFace:=iFace, ePt:=ePt);
      Add(NewListVert, eRec);
    od;
  od;
  SetListVert:=Set(NewListVert);
  nbVertFull:=Length(SetListVert);
  GRA:=NullGraph(Group(()), nbVertFull);
  for iVert in [1..nbVertFull]
  do
    eRec:=SetListVert[iVert];
    iPoint:=Position(ListPoints, eRec.ePt);
    iFace:=eRec.iFace;
    eFace:=FaceSet[iFace];
    for iBnd in [1..6]
    do
      if ListStatusForTransform[iPoint][iBnd]=1 then
        eDE:=eFace[iBnd];
        eDErev:=OnPoints(eDE, eInv);
        RecCorr:=GetIFace(eDErev);
        NbRot:=iBnd-1;
        ePt:=[eRec.ePt[1], eRec.ePt[2]];
        for h in [1..NbRot]
        do
          ePt:=Rotation60degreesRev(eCent, ePt);
        od;
        ePt:=EdgeRotation(ePt);
        NbRotCorr:=RecCorr.pos-1;
        for h in [1..NbRotCorr]
        do
          ePt:=Rotation60degrees(eCent, ePt);
        od;
        eNewVert:=rec(iFace:=RecCorr.iFace, ePt:=ePt);
        pos:=Position(SetListVert, eNewVert);
        if pos<>fail then
          if iVert<>pos then
            AddEdgeOrbit(GRA, [iVert, pos]);
            AddEdgeOrbit(GRA, [pos, iVert]);
          fi;
        fi;
      fi;
    od;
  od;
  Lconn:=ConnectedComponents(GRA);
  nbConn:=Length(Lconn);
  ListConnIdx:=ListWithIdenticalEntries(nbVertFull,0);
  for iConn in [1..nbConn]
  do
    ListConnIdx{Lconn[iConn]}:=ListWithIdenticalEntries(Length(Lconn[iConn]), iConn);
  od;
  GetSingleDirection:=function(iConn)
    local idx, eRec, iDir, eNvert, pos;
    idx:=1;
    eRec:=SetListVert[Lconn[iConn][idx]];
    iDir:=1;
    while(true)
    do
      eNvert:=rec(iFace:=eRec.iFace, ePt:=eRec.ePt+ListDirections[iDir]);
      pos:=Position(SetListVert, eNvert);
      if pos<>fail then
        return rec(eRec:=eRec, eNvert:=eNvert, pos:=pos, iConn:=ListConnIdx[pos]);
      fi;
      iDir:=NextIdx(6, iDir);
    od;
  end;
  DoNext:=function(eDE)
    local posI, iConn, eConn, len, idx, eRec, iDir, iFace, eNvert, pos, IsMatch, iHex, jDir;
    posI:=Position(SetListVert, eDE.eRec);
    iConn:=ListConnIdx[posI];
    eConn:=Lconn[iConn];
    len:=Length(eConn);
    for idx in [1..len]
    do
      eRec:=SetListVert[eConn[idx]];
      for iDir in [1..6]
      do
        iFace:=eRec.iFace;
        eNvert:=rec(iFace:=iFace, ePt:=eRec.ePt+ListDirections[iDir]);
        pos:=Position(SetListVert, eNvert);
        if pos<>fail then
          if ListConnIdx[pos]=eDE.iConn then
            IsMatch:=true;
            jDir:=iDir;
            for iHex in [1..4]
            do
              jDir:=NextIdx(6,jDir);
              eNvert:=rec(iFace:=iFace, ePt:=eNvert.ePt+ListDirections[jDir]);
              pos:=Position(SetListVert, eNvert);
              if pos=fail then
                IsMatch:=false;
              fi;
            od;
            if IsMatch=true then
              return rec(eRec:=eRec, eNvert:=eNvert, pos:=pos, iConn:=ListConnIdx[pos]);
            fi;
          fi;
        fi;
      od;
    od;
    Print("We should return something, just maybe\n");
    Print(NullMat(5));
  end;
  DoInvers:=function(eDE)
    local posI, iConn, jConn, iDE, pos;
    posI:=Position(SetListVert, eDE.eRec);
    iConn:=ListConnIdx[posI];
    jConn:=eDE.iConn;
    for iDE in [1..nbDE]
    do
      if ListDE[iDE].iConn=iConn then
        pos:=Position(SetListVert, ListDE[iDE].eRec);
        if ListConnIdx[pos]=jConn then
          return iDE;
        fi;
      fi;
    od;
    Print("We failed!!!!!\n");
    Print(NullMat(5));
  end;
  ListDE:=[];
  NextEList:=[];
  for iConn in [1..nbConn]
  do
    eConn:=Lconn[iConn];
    len:=Length(eConn);
    PartListDE:=[];
    eDE:=GetSingleDirection(iConn);
    Add(PartListDE, eDE);
    jConn:=eDE.iConn;
    while(true)
    do
      eDE:=DoNext(eDE);
      if eDE.iConn=jConn then
        break;
      fi;
      Add(PartListDE, eDE);
    od;
    lenAdj:=Length(PartListDE);
    nbDE:=Length(ListDE);
    h:=[];
    for i in [1..lenAdj]
    do
      Add(h, nbDE+NextIdx(lenAdj,i));
    od;
    Append(ListDE, PartListDE);
    Append(NextEList, h);
  od;
  nbDE:=Length(ListDE);
  InversEList:=[];
  for iDE in [1..nbDE]
  do
    eDE:=ListDE[iDE];
    Add(InversEList, DoInvers(eDE));
  od;
  PLoriRet:=rec(next:=PermList(NextEList), invers:=PermList(InversEList), nbP:=nbDE);
  return DualGraphOriented(PLoriRet);
end;

EliminationByGoldbergCoxeter:=function(LPL)
  local ListNBV, ePL, VEFori, nbG, MaxNBV, ListStatus, FindMatching, i, MaxNorm, ListPoss, ePoss, k, l, newPLori, eMatch;
  ListNBV:=[];
  for ePL in LPL
  do
    VEFori:=PlanGraphOrientedToVEF(ePL);
    Add(ListNBV, Length(VEFori.VertSet));
  od;
  nbG:=Length(LPL);
  Print("nbG=", nbG, "\n");
  MaxNBV:=Maximum(ListNBV);
  ListStatus:=ListWithIdenticalEntries(nbG,1);
  FindMatching:=function(ePL)
    local i, test, VEFori, nbVert;
    VEFori:=PlanGraphOrientedToVEF(ePL);
    nbVert:=Length(VEFori.VertSet);
    for i in [1..nbG]
    do
      if nbVert=ListNBV[i] then
        test:=IsIsomorphicPlanGraphOriented(ePL, LPL[i]);
        if test=true then
          return i;
        fi;
      fi;
    od;
    return fail;
  end;
  for i in [1..nbG]
  do
    Print("i=", i, "\n");
    if ListStatus[i]=1 then
      MaxNorm:=MaxNBV/ListNBV[i];
      ListPoss:=EnumeratePossibilitiesSixValentGoldbergCoxeter_general(MaxNorm);
      Print("MaxNorm=", MaxNorm, " |ListPoss|=", Length(ListPoss), "\n");
      for ePoss in Filtered(ListPoss, x->x<>[1,0])
      do
        k:=ePoss[1];
        l:=ePoss[2];
        Print("k=", k, " l=", l, "\n");
        Print("step 1\n");
        newPLori:=GoldbergConstructionSixValent(LPL[i], k, l);
        Print("step 2\n");
        eMatch:=FindMatching(newPLori);
        Print("step 3\n");
        if eMatch=fail then
          Print("This contradict the list being complete up to sought nr.\n");
          Print(NullMat(5));
        fi;
        if eMatch<>i then
          ListStatus[eMatch]:=0;
        fi;
        Print("k=", k, " l=", l, " eMatch=", eMatch, "\n");
      od;
    fi;
  od;
  return Filtered([1..nbG], x->ListStatus[x]=1);
end;

PrintStandardInfoOrientedGraph:=function(PLori)
  local VEFori, nbVert, nbEdge, nbFace, eGRP;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  nbVert:=Length(VEFori.VertSet);
  nbEdge:=Length(VEFori.EdgeSet);
  nbFace:=Length(VEFori.FaceSet);
  Print("nbVert=", nbVert, " nbEdge=", nbEdge, " nbFace=", nbFace, "\n");
  Print("CollDegVert=", Collected(List(VEFori.VertSet, Length)), "\n");
  Print("CollDegFace=", Collected(List(VEFori.FaceSet, Length)), "\n");
  eGRP:=GroupPlanOriented(PLori).SchoenfliesSymbol;
  Print("eGRP=", eGRP, "\n");
end;

OrientedTriplingSixValent:=function(PLori)
  local nbDE, GRA, eImg1, eImg2, ePrev, i, j, BipartVect, ListLPL, eVal, eSet, TotalListDE, SetListDE, eV, eListNext, eListInv, hdx, fDE2, ePermNext, ePermInv, PLoriNew, eNext, eInv, ListImgNext, ListImgInv, eDE2, rDE2;
  nbDE:=PLori.nbP;
  GRA:=NullGraph(Group(()), nbDE);
  ePrev:=Inverse(PLori.next);
  eNext:=PLori.next;
  eInv:=PLori.invers;
  eImg1:=Permuted([1..nbDE], eInv);
  eImg2:=Permuted([1..nbDE], eNext);
  for i in [1..nbDE]
  do
    j:=eImg1[i];
    AddEdgeOrbit(GRA, [i,j]);
    AddEdgeOrbit(GRA, [j,i]);
    j:=eImg2[i];
    AddEdgeOrbit(GRA, [i,j]);
    AddEdgeOrbit(GRA, [j,i]);
  od;
  BipartVect:=GetBipartition(GRA);
  ListLPL:=[];
  for eVal in [1,2]
  do
    eSet:=Filtered([1..nbDE], x->BipartVect[x]=eVal);
    TotalListDE:=[];
    for eV in eSet
    do
      for i in [1..3]
      do
        Add(TotalListDE, [eV, i]);
        Add(TotalListDE, [eV, -i]);
      od;
    od;
    SetListDE:=Set(TotalListDE);
    ListImgNext:=[];
    ListImgInv:=[];
    for eDE2 in SetListDE
    do
      rDE2:=[eDE2[1], -eDE2[2]];
      Add(ListImgInv, rDE2);
      if eDE2[2]=1 then
        fDE2:=[eDE2[1], -3];
      elif eDE2[2]=2 then
        fDE2:=[eDE2[1], -1];
      elif eDE2[2]=3 then
        fDE2:=[eDE2[1], -2];
      elif eDE2[2]=-1 then
        hdx:=OnPoints(eDE2[1], ePrev*ePrev);
        fDE2:=[hdx, 1];
      elif eDE2[2]=-2 then
        hdx:=OnPoints(eDE2[1], eInv*eNext);
        fDE2:=[hdx, 2];
      elif eDE2[2]=-3 then
        hdx:=OnPoints(eDE2[1], eNext*eInv);
        fDE2:=[hdx, 3];
      else
        Print("No point to be here\n");
        Print(NullMat(5));
      fi;
      Add(ListImgNext, fDE2);
    od;
    if Set(ListImgNext)<>SetListDE then
      Print("OrientedTripling discontinuity 1\n");
      Print(NullMat(5));
    fi;
    if Set(ListImgInv)<>SetListDE then
      Print("OrientedTripling discontinuity 2\n");
      Print(NullMat(5));
    fi;
    ePermNext:=SortingPerm(ListImgNext);
    ePermInv:=SortingPerm(ListImgInv);
    PLoriNew:=rec(nbP:=Length(TotalListDE), invers:=ePermInv, next:=ePermNext);
    Add(ListLPL, PLoriNew);
  od;
  return ListLPL;
end;


# this is not entirely satisfying since we do not have an overall
# understanding of the Goldberg construction
GoldbergConstructionSixValentGeneralized:=function(PLori, k, l)
  local sLevel, kBas, lBas, kN, lN, nbIter, ListPLori, iS, NewListPLori, LPL, RetPLori, ePLori, FuncInsert, RetLPLori;
  sLevel:=0;
  kBas:=k;
  lBas:=l;
  while(true)
  do
    if IsInt((kBas-lBas)/3) then
      sLevel:=sLevel+1;
      kN:=(2*kBas+lBas)/3;
      lN:=(lBas-kBas)/3;
      kBas:=kN;
      lBas:=lN;
    else
      break;
    fi;
  od;
  nbIter:=0;
  while(true)
  do
    if IsInt((kBas-1-lBas)/3) and lBas>=0 and kBas+lBas>0 then
      break;
    else
      kN:=-lBas;
      lN:=kBas+lBas;
      kBas:=kN;
      lBas:=lN;
      nbIter:=nbIter+1;
#      Print("nbIter=", nbIter, " kBas=", kBas, " lBas=", lBas, "\n");
    fi;
  od;
  ListPLori:=[StructuralCopy(PLori)];
#  Print("sLevel=", sLevel, "\n");
  for iS in [1..sLevel]
  do
    NewListPLori:=[];
    FuncInsert:=function(eNewPLori)
      local ePLori;
      for ePLori in NewListPLori
      do
        if IsIsomorphicPlanGraphOriented(eNewPLori, ePLori)=true then
          return;
        fi;
      od;
      Add(NewListPLori, eNewPLori);
    end;
    for ePLori in ListPLori
    do
      LPL:=OrientedTriplingSixValent(ePLori);
      FuncInsert(LPL[1]);
      FuncInsert(LPL[2]);
    od;
    ListPLori:=ShallowCopy(NewListPLori);
  od;
  if Length(ListPLori)>2 then
    Print("It is quite possible that we did something wrong\n");
    Print(NullMat(5));
  fi;
  RetLPLori:=[];
#  Print("kBas=", kBas, " lBas=", lBas, "\n");
#  Print("ListPLori=", ListPLori, "\n");
  for ePLori in ListPLori
  do
    Add(RetLPLori, GoldbergConstructionSixValent(ePLori, kBas, lBas));
  od;
  return RetLPLori;
end;









# m is the number of sides and p the number of 2-gons that
# have been put
MPfoil:=function(m,p)
  local NewListDE, i, j, nbDE, eListNext, eListInv, iDE, eDE, rDE, nDE, PLori;
  NewListDE:=[];
  for i in [1..m]
  do
    for j in [1..p+1]
    do
      Add(NewListDE, [i,j-1,0]);
      Add(NewListDE, [i,j-1,1]);
    od;
  od;
  nbDE:=Length(NewListDE);
  eListNext:=[];
  eListInv:=[];
  for iDE in [1..nbDE]
  do
    eDE:=NewListDE[iDE];
    if eDE[3]=0 then
      j:=NextIdx(m, eDE[1]);
    else
      j:=PrevIdx(m, eDE[1]);
    fi;
    rDE:=[j, p-eDE[2], 1-eDE[3]];
    Add(eListInv, Position(NewListDE, rDE));
    if eDE[2]<p then
      nDE:=[eDE[1], eDE[2]+1, eDE[3]];
    else
      nDE:=[eDE[1], 0, 1-eDE[3]];
    fi;     
    Add(eListNext, Position(NewListDE, nDE));
  od;
  PLori:=rec(nbP:=nbDE, invers:=PermList(eListInv), next:=PermList(eListNext));
  return rec(PLori:=PLori);
end;


InfiniteSeriesOneGonAdjTwoGon:=function(n)
  local NewListDE, i, j, nbDE, eListNext, eListInv, iDE, eDE, eStat, idx, rDE, nDE, jdx, PLori;
  NewListDE:=[];
  for i in [1..4]
  do
    Add(NewListDE, [-1, i]);
  od;
  for j in [1..n-1]
  do
    for i in [1..6]
    do
      Add(NewListDE, [j, i]);
    od;
  od;
  for i in [1..2]
  do
    Add(NewListDE, [-2, i]);
  od;
  nbDE:=6*n;
  eListNext:=[];
  eListInv:=[];
  for iDE in [1..nbDE]
  do
    eDE:=NewListDE[iDE];
    eStat:=eDE[1];
    idx:=eDE[2];
    if eStat=-1 then
      rDE:=[eStat, 5-idx];
      if idx < 4 then
        nDE:=[eStat, idx+1];
      else
        if n>1 then
          nDE:=[1, 3];
        else
          nDE:=[-2, 1];
        fi;
      fi;
    elif eStat=-2 then
      rDE:=[eStat, 3-idx];
      if idx=1 then
        nDE:=[eStat,2];
      else
        if n>1 then
          nDE:=[n-1,6];
        else
          nDE:=[-1,1];
        fi;
      fi;
    else
      if idx=1 then
        jdx:=2;
      elif idx=2 then
        jdx:=1;
      elif idx=3 then
        jdx:=4;
      elif idx=4 then
        jdx:=3;
      elif idx=5 then
        jdx:=6;
      elif idx=6 then
        jdx:=5;
      else
        Print(NullMat(5));
      fi;
      rDE:=[eStat, jdx];
      #
      if idx=3 then
        nDE:=[eStat,1];
      elif idx=2 then
        nDE:=[eStat,5];
      elif idx=6 then
        nDE:=[eStat,4];
      elif idx=4 then
        nDE:=[eStat,2];
      elif idx=1 then
        if eStat>1 then
          nDE:=[eStat-1,6];
        else
          nDE:=[-1,1];
        fi;
      elif idx=5 then
        if eStat<n-1 then
          nDE:=[eStat+1,3];
        else
          nDE:=[-2,1];
        fi;
      else
        Print(NullMat(6));
      fi;
    fi;
    Add(eListNext, Position(NewListDE, nDE));
    Add(eListInv, Position(NewListDE, rDE));
  od;
  if PermList(eListNext)=fail then
    Print("Please debug from here 1\n");
    Print(NullMat(5));
  fi;
  PLori:=rec(nbP:=nbDE, invers:=PermList(eListInv), next:=PermList(eListNext));
  if IsCorrectGraph123_6_graphs(PLori)=false then
    Error("Generated graph is not correct");
  fi;
  return rec(PLori:=PLori, eGRP:="C2h");
end;


InfiniteSeries1adj3adj2:=function(n, eChoice)
  local NewListDE, i, j, nbDE, eListNext, eListInv, iDE, eDE, eStat, idx, rDE, nDE, jdx, pos, rList, nList1, nList2, PLori;
  NewListDE:=[];
  for i in [1..8]
  do
    Add(NewListDE, [-1, i]);
  od;
  for j in [1..n-2]
  do
    for i in [1..6]
    do
      Add(NewListDE, [j, i]);
    od;
  od;
  for i in [1..4]
  do
    Add(NewListDE, [-2, i]);
  od;
  nbDE:=6*n;
  eListNext:=[];
  eListInv:=[];
  for iDE in [1..nbDE]
  do
    eDE:=NewListDE[iDE];
    eStat:=eDE[1];
    idx:=eDE[2];
    if eStat=-1 then
      rList:=[2,1,4,3,6,5,8,7];
      nList1:=[7,1,6,2,3,4];
      nList2:=[1,5,2,3,4,8];
      rDE:=[eStat,rList[idx]];
      pos:=Position(nList1, idx);
      if pos<>fail then
        nDE:=[eStat, nList2[pos]];
      else
        if idx=5 then
          if n>2 then
            nDE:=[1, 4];
          else
            if eChoice=1 then
              nDE:=[-2, 2];
            else
              nDE:=[-2, 4];
            fi;
          fi;
        fi;
        if idx=8 then
          if n>2 then
            nDE:=[1, 1];
          else
            nDE:=[-2, 1];
          fi;
        fi;
      fi;
    elif eStat=-2 then
      if eChoice=1 then
        rList:=[2,1,4,3];
        nList1:=[2,3];
        nList2:=[3,4];
        rDE:=[eStat,rList[idx]];
        pos:=Position(nList1, idx);
        if pos<>fail then
          nDE:=[eStat, nList2[pos]];
        else
          if idx=1 then
            if n>2 then
              nDE:=[n-2, 6];
            else
              nDE:=[-1,  6];
            fi;
          fi;
          if idx=4 then
            if n>2 then
              nDE:=[n-2, 3];
            else
              nDE:=[-1, 7];
            fi;
          fi;
        fi;
      else
        rList:=[2,1,4,3];
        nList1:=[4,3];
        nList2:=[3,2];
        rDE:=[eStat,rList[idx]];
        pos:=Position(nList1, idx);
        if pos<>fail then
          nDE:=[eStat, nList2[pos]];
        else
          if idx=1 then
            if n>2 then
              nDE:=[n-2, 6];
            else
              nDE:=[-1,  6];
            fi;
          fi;
          if idx=2 then
            if n>2 then
              nDE:=[n-2, 3];
            else
              nDE:=[-1, 7];
            fi;
          fi;
        fi;
      fi;
    else
      rList:=[2,1,4,3,6,5];
      nList1:=[3,2];
      nList2:=[2,5];
      rDE:=[eStat,rList[idx]];
      pos:=Position(nList1, idx);
      if pos<>fail then
        nDE:=[eStat, nList2[pos]];
      else
        if idx=1 then
          if eStat>1 then
            nDE:=[eStat-1, 6];
          else
            nDE:=[-1, 6];
          fi;
        fi;
        if idx=4 then
          if eStat<n-2 then
            nDE:=[eStat+1, 1];
          else
            nDE:=[-2, 1];
          fi;
        fi;
        if idx=5 then
          if eStat<n-2 then
            nDE:=[eStat+1, 4];
          else
            if eChoice=1 then
              nDE:=[-2, 2];
            else
              nDE:=[-2, 4];
            fi;
          fi;
        fi;
        if idx=6 then
          if eStat>1 then
            nDE:=[eStat-1, 3];
          else
            nDE:=[-1, 7];
          fi;
        fi;
      fi;
    fi;
    Add(eListNext, Position(NewListDE, nDE));
    Add(eListInv, Position(NewListDE, rDE));
  od;
  if PermList(eListNext)=fail then
    Print("Please debug from here 2\n");
    Print(NullMat(5));
  fi;
  PLori:=rec(nbP:=nbDE, invers:=PermList(eListInv), next:=PermList(eListNext));
  if IsCorrectGraph123_6_graphs(PLori)=false then
    Error("Generated graph is not correct");
  fi;
  return rec(PLori:=PLori, eGRP:=GroupPlanOriented(PLori).SchoenfliesSymbol);
end;



InfiniteSeriesVariantFromSingular3N_V1:=function(n)
  local NewListDE, i, j, nbDE, eListNext, eListInv, iDE, eDE, eStat, idx, rDE, nDE, jdx, pos, rList, nList1, nList2, PLori, p, eChoice, res;
  NewListDE:=[];
  res:=n mod 2;
  if res=0 then
    p:=(n-4)/2;
    eChoice:=2;
  else
    p:=(n-3)/2;
    eChoice:=1;
  fi;
  for i in [1..14]
  do
    Add(NewListDE, [-1, i]);
  od;
  for j in [1..p]
  do
    for i in [1..12]
    do
      Add(NewListDE, [j, i]);
    od;
  od;
  if eChoice=1 then
    for i in [1..4]
    do
      Add(NewListDE, [-2, i]);
    od;
  else
    for i in [1..10]
    do
      Add(NewListDE, [-2, i]);
    od;
  fi;
  nbDE:=6*n;
  eListNext:=[];
  eListInv:=[];
  for iDE in [1..nbDE]
  do
    eDE:=NewListDE[iDE];
    eStat:=eDE[1];
    idx:=eDE[2];
    if eStat=-1 then
      rList:=[2,1,4,3,6,5,8,7,10,9,12,11,14,13];
      nList1:=[2,3,4,6,7,9,14,10,8 ,11,5,1 ];
      nList2:=[3,4,6,7,9,2,10,8 ,12,5 ,1,13];
      rDE:=[eStat,rList[idx]];
      pos:=Position(nList1, idx);
      if pos<>fail then
        nDE:=[eStat, nList2[pos]];
      else
        if idx=13 then
          if p>0 then
            nDE:=[1, 12];
          else
            nDE:=[-2, 3];
          fi;
        fi;
        if idx=12 then
          if p>0 then
            nDE:=[1, 2];
          else
            if eChoice=1 then
              nDE:=[-2, 2];
            else
              nDE:=[-2, 8];
            fi;
          fi;
        fi;
      fi;
    elif eStat=-2 then
      if eChoice=1 then
        rList:=[2,1,4,3];
        nList1:=[3,2];
        nList2:=[1,4];
        rDE:=[eStat,rList[idx]];
        pos:=Position(nList1, idx);
        if pos<>fail then
          nDE:=[eStat, nList2[pos]];
        else
          if idx=1 then
            if p>0 then
              nDE:=[p, 3];
            else
              nDE:=[-1, 11];
            fi;
          fi;
          if idx=4 then
            if p>0 then
              nDE:=[p, 8];
            else
              nDE:=[-1, 14];
            fi;
          fi;
        fi;
      else
        rList:=[2,1,4,3,6,5,8,7,10,9];
        nList1:=[3,2,5,6,4,9,7,8];
        nList2:=[1,5,6,4,9,7,2,10];
        rDE:=[eStat,rList[idx]];
        pos:=Position(nList1, idx);
        if pos<>fail then
          nDE:=[eStat, nList2[pos]];
        else
          if idx=1 then
            if p>0 then
              nDE:=[p, 3];
            else
              nDE:=[-1, 11];
            fi;
          fi;
          if idx=10 then
            if p>0 then
              nDE:=[p, 8];
            else
              nDE:=[-1, 14];
            fi;
          fi;
        fi;
      fi;
    else
      rList:=[2,1,4,3,6,5,8,7,10,9,12,11];
      nList1:=[12,2,3,1,9,8 ,11,5];
      nList2:=[10,6,1,9,7,11,5 ,4];
      rDE:=[eStat,rList[idx]];
      pos:=Position(nList1, idx);
      if pos<>fail then
        nDE:=[eStat, nList2[pos]];
      else
        if idx=10 then
          if eStat>1 then
            nDE:=[eStat-1, 3];
          else
            nDE:=[-1, 11];
          fi;
        fi;
        if idx=6 then
          if eStat>1 then
            nDE:=[eStat-1, 8];
          else
            nDE:=[-1, 14];
          fi;
        fi;
        if idx=7 then
          if eStat<p then
            nDE:=[eStat+1, 12];
          else
            nDE:=[-2, 3];
          fi;
        fi;
        if idx=4 then
          if eStat<p then
            nDE:=[eStat+1, 2];
          else
            if eChoice=1 then
              nDE:=[-2, 2];
            else
              nDE:=[-2, 8];
            fi;
          fi;
        fi;
      fi;
    fi;
    Add(eListNext, Position(NewListDE, nDE));
    Add(eListInv, Position(NewListDE, rDE));
  od;
  if PermList(eListNext)=fail then
    Print("Please debug from here 2\n");
    Print(NullMat(5));
  fi;
  PLori:=rec(nbP:=nbDE, invers:=PermList(eListInv), next:=PermList(eListNext));
  if IsCorrectGraph123_6_graphs(PLori)=false then
    Error("Generated graph is not correct");
  fi;
  return rec(PLori:=PLori, eGRP:=GroupPlanOriented(PLori).SchoenfliesSymbol);
end;





# For n odd this is the series R (symmetry Cs)
# For n even this is the series S (symmetry seems problematic
InfiniteSeriesVariantFromSingular3N:=function(n, PreSecChoice)
  local NewListDE, i, j, nbDE, eListNext, eListInv, iDE, eDE, eStat, idx, rDE, nDE, jdx, pos, rList, nList1, nList2, PLori, p, eChoice, res, SecChoice;
  NewListDE:=[];
  res:=n mod 2;
  if res=0 then
    p:=(n-4)/2;
    eChoice:=2;
    # SecChoice only relevant for eChoice=2
    SecChoice:=PreSecChoice;
  else
    p:=(n-3)/2;
    eChoice:=1;
    SecChoice:=1;
  fi;
  for i in [1..14]
  do
    Add(NewListDE, [-1, i]);
  od;
  for j in [1..p]
  do
    for i in [1..12]
    do
      Add(NewListDE, [j, i]);
    od;
  od;
  if eChoice=1 then
    for i in [1..4]
    do
      Add(NewListDE, [-2, i]);
    od;
  else
    for i in [1..10]
    do
      Add(NewListDE, [-2, i]);
    od;
  fi;
  nbDE:=6*n;
  eListNext:=[];
  eListInv:=[];
  for eDE in NewListDE
  do
    eStat:=eDE[1];
    idx:=eDE[2];
    if eStat=-1 then
      rList :=[2,1,4,3,6,5,8 ,7 ,10,9 ,12,11,14,13];
      nList1:=[2,3,4,6,7,9,14,10,8 ,11,5,1 ];
      nList2:=[3,4,6,7,9,2,10,8 ,12,5 ,1,13];
      rDE:=[eStat,rList[idx]];
      pos:=Position(nList1, idx);
      if pos<>fail then
        nDE:=[eStat, nList2[pos]];
      else
        if idx=13 then
          if p>0 then
            nDE:=[1, 12];
          else
            if SecChoice=1 then
              nDE:=[-2, 3];
            else
              nDE:=[-2, 8];
            fi;
          fi;
        fi;
        if idx=12 then
          if p>0 then
            nDE:=[1, 2];
          else
            if eChoice=1 then
              nDE:=[-2, 2];
            else
              if SecChoice=1 then
                nDE:=[-2, 8];
              else
                nDE:=[-2, 3];
              fi;
            fi;
          fi;
        fi;
      fi;
    elif eStat=-2 then
      if eChoice=1 then
        rList:=[2,1,4,3];
        nList1:=[3,2];
        nList2:=[1,4];
        rDE:=[eStat,rList[idx]];
        pos:=Position(nList1, idx);
        if pos<>fail then
          nDE:=[eStat, nList2[pos]];
        else
          if idx=1 then
            if p>0 then
              nDE:=[p, 3];
            else
              nDE:=[-1, 11];
            fi;
          fi;
          if idx=4 then
            if p>0 then
              nDE:=[p, 8];
            else
              nDE:=[-1, 14];
            fi;
          fi;
        fi;
      else
        rList:=[2,1,4,3,6,5,8,7,10,9];
        nList1:=[3,2,5,6,4,9,7,8];
        nList2:=[1,5,6,4,9,7,2,10];
        rDE:=[eStat,rList[idx]];
        pos:=Position(nList1, idx);
        if pos<>fail then
          nDE:=[eStat, nList2[pos]];
        else
          if idx=1 then
            if SecChoice=1 then
              if p>0 then
                nDE:=[p, 3];
              else
                nDE:=[-1, 11];
              fi;
            else
              if p>0 then
                nDE:=[p, 8];
              else
                nDE:=[-1, 14];
              fi;
            fi;
          fi;
          if idx=10 then
            if SecChoice=1 then
              if p>0 then
                nDE:=[p, 8];
              else
                nDE:=[-1, 14];
              fi;
            else
              if p>0 then
                nDE:=[p, 3];
              else
                nDE:=[-1, 11];
              fi;
            fi;
          fi;
        fi;
      fi;
    else
      rList:=[2,1,4,3,6,5,8,7,10,9,12,11];
      nList1:=[12,2,3,1,9,8 ,11,5];
      nList2:=[10,6,1,9,7,11,5 ,4];
      rDE:=[eStat,rList[idx]];
      pos:=Position(nList1, idx);
      if pos<>fail then
        nDE:=[eStat, nList2[pos]];
      else
        if idx=10 then
          if eStat>1 then
            nDE:=[eStat-1, 3];
          else
            nDE:=[-1, 11];
          fi;
        fi;
        if idx=6 then
          if eStat>1 then
            nDE:=[eStat-1, 8];
          else
            nDE:=[-1, 14];
          fi;
        fi;
        if idx=7 then
          if eStat<p then
            nDE:=[eStat+1, 12];
          else
            if SecChoice=1 then
              nDE:=[-2, 3];
            else
              nDE:=[-2, 8];
            fi;
          fi;
        fi;
        if idx=4 then
          if eStat<p then
            nDE:=[eStat+1, 2];
          else
            if eChoice=1 then
              nDE:=[-2, 2];
            else
              if SecChoice=1 then
                nDE:=[-2, 8];
              else
                nDE:=[-2, 3];
              fi;
            fi;
          fi;
        fi;
      fi;
    fi;
    Add(eListNext, Position(NewListDE, nDE));
    Add(eListInv, Position(NewListDE, rDE));
  od;
  if PermList(eListNext)=fail then
    Error("Please debug from here 2");
  fi;
  PLori:=rec(nbP:=nbDE, invers:=PermList(eListInv), next:=PermList(eListNext));
  if IsCorrectGraph123_6_graphs(PLori)=false then
    Error("Generated graph is not correct");
  fi;
  return rec(PLori:=PLori, eGRP:=GroupPlanOriented(PLori).SchoenfliesSymbol);
end;

FromThreeValentToSixValent:=function(PL)
  local NewPL, iVert, nbVert, a, b, c;
  NewPL:=[];
  nbVert:=Length(PL);
  for iVert in [1..nbVert]
  do
    a:=PL[iVert][1];
    b:=PL[iVert][2];
    c:=PL[iVert][3];
    Add(NewPL, [a,a,b,b,c,c]);
  od;
  return NewPL;
end;





123_Insert_2gon:=function(PLori, eEdge)
  local nbP, nbP_new, eListNext, iDE, LNext, i, eListInv, a, b, NewPLori;
  nbP:=PLori.nbP;
  nbP_new:=nbP + 6;
  eListNext:=[];
  for iDE in [1..nbP]
  do
    Add(eListNext, OnPoints(iDE, PLori.next));
  od;
  LNext:=[2,3,1,5,6,4];
  for i in [1..6]
  do
    Add(eListNext, nbP + LNext[i]);
  od;
  #
  eListInv:=ListWithIdenticalEntries(nbP_new, 0);
  for iDE in [1..nbP]
  do
    eListInv[iDE]:=OnPoints(iDE, PLori.invers);
  od;
  a:=eEdge[1];
  b:=eEdge[2];
  eListInv[a]:=nbP+1;
  eListInv[nbP+1]:=a;
  eListInv[b]:=nbP+4;
  eListInv[nbP+4]:=b;
  eListInv[nbP+3]:=nbP+5;
  eListInv[nbP+5]:=nbP+3;
  eListInv[nbP+2]:=nbP+6;
  eListInv[nbP+6]:=nbP+2;
  NewPLori:=rec(next:=PermList(eListNext), invers:=PermList(eListInv), nbP:=nbP_new);
  if NewPLori.next=fail or NewPLori.invers=fail then
    Print("Concistency error in NewPLori. Please debug\n");
    Print(NullMat(5));
  fi;
  return NewPLori;
end;

123_GetGeneratedGraphs:=function(ePLori, MaxNbV, MaxFaceSize)
  local LPL, LStatus, FuncInsert, IsFinished, nbG, iG, iEdge, nbEdge, eEdge, iFace, jFace, NewPLori, NewVEFori, VEFori, nbWork;
  Print("MaxNbV=", MaxNbV, "\n");
  LPL:=[];
  LStatus:=[];
  FuncInsert:=function(ePLori)
    local fPLori;
    for fPLori in LPL
    do
      if ePLori.nbP=fPLori.nbP then
        if IsIsomorphicPlanGraphOriented(fPLori, ePLori)=true then
          return;
        fi;
      fi;
    od;
    Add(LPL, ePLori);
    Add(LStatus, 1);
  end;
  FuncInsert(ePLori);
  while(true)
  do
    IsFinished:=true;
    nbG:=Length(LPL);
    for iG in [1..nbG]
    do
      if LStatus[iG]=1 then
        IsFinished:=false;
        LStatus[iG]:=0;
        ePLori:=LPL[iG];
        VEFori:=PlanGraphOrientedToVEF(ePLori);
        nbEdge:=Length(VEFori.EdgeSet);
        for iEdge in [1..nbEdge]
        do
          eEdge:=VEFori.EdgeSet[iEdge];
          iFace:=VEFori.ListOriginFace[eEdge[1]];
          jFace:=VEFori.ListOriginFace[eEdge[2]];
          if Length(VEFori.FaceSet[iFace]) <= MaxFaceSize-2 and Length(VEFori.FaceSet[jFace]) <= MaxFaceSize-2 then
            NewPLori:=123_Insert_2gon(ePLori, eEdge);
            NewVEFori:=PlanGraphOrientedToVEF(ePLori);
            if Length(NewVEFori.VertSet)<=MaxNbV then
              FuncInsert(NewPLori);
            fi;
          fi;
        od;
      fi;
    od;
    if IsFinished then
      break;
    fi;
    nbWork:=Length(Filtered(LStatus, x->x=1));
    Print("nbWork=", nbWork, " |LPL|=", Length(LPL), " Coll(ListNb)=", Collected(List(LPL, x->x.nbP)), "\n");
  od;
  return LPL;
end;


PrintSignaturePlanGraphOriented:=function(PLori)
  local VEFori, ListVertSize, ListFaceSize;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  ListVertSize:=List(VEFori.VertSet, Length);
  ListFaceSize:=List(VEFori.FaceSet, Length);
  Print("P-vect=", Collected(ListVertSize), " F-vect=", Collected(ListFaceSize), "\n");
end;


123_GetAdmissibleGraphs:=function(nbV, TheOpt)
  local GetGraphs, LPLtot, nbVert, res, LPLpart, LPL, fPLori, ePLori, IsCorrect;
  GetGraphs:=function(nbVert)
    local p4, p6, ListFaceDesc, LPL, ePL, PLori;
    if nbVert=2 then
      return [Mbundle(3)];
    fi;
    p4:=6;
    p6:=(3*nbVert - 4*p4)/6;
    ListFaceDesc:=[[4, rec(eNature:="plus", nb:=p4)], 
                   [6, rec(eNature:="plus", nb:=p6)]];
    LPL:=[];
    for ePL in GetList3valentPlaneGraphSpecifiedFaces(nbVert, ListFaceDesc)
    do
      PLori:=PlanGraphToPlanGraphOriented(ePL);
      Add(LPL, PLori);
    od;
    return LPL;
  end;
  LPLtot:=[];
  IsCorrect:=function(fPLori)
    local VEFori;
    VEFori:=PlanGraphOrientedToVEF(fPLori);
    nbVert:=Length(VEFori.VertSet);
    if TheOpt="equality" then
      return nbVert=nbV;
    else
      return nbVert<=nbV;
    fi;
  end;
  for nbVert in [2..nbV]
  do
    res:=nbVert mod 2;
    if res=0 then
      LPL:=GetGraphs(nbVert);
      Print("nbVert=", nbVert, " |LPL|=", Length(LPL), "\n");
      for ePLori in LPL
      do
        LPLpart:=123_GetGeneratedGraphs(ePLori, nbV, 6);
        for fPLori in LPLpart
        do
          if IsCorrect(fPLori) then
            Add(LPLtot, fPLori);
          fi;
        od;
      od;
    fi;
  od;
  return LPLtot;
end;

GetAll_123spheres:=function(nbV, TheOpt)
  local nbVtot, p4, p6, ListFaceDesc, LPL, LPLret, ePL, PLori, NewLPL, NewPLori, VEFori, ListAdmi, FuncInsert, nPLori, iClass, i, pos, ListReturn;
  nbVtot:=6*nbV;
  LPL:=123_GetAdmissibleGraphs(nbVtot, TheOpt);
  ListReturn:=[];
  for i in [1..nbV]
  do
    LPLret:=[];
    for iClass in [0..3]
    do
      Add(LPLret, rec(class:=iClass, LPL:=[]));
    od;
    Add(ListReturn, LPLret);
  od;
  for PLori in LPL
  do
    NewLPL:=InverseTruncationOriented(PLori);
    ListAdmi:=[];
    FuncInsert:=function(ePLori)
      local fPLori;
      for fPLori in ListAdmi
      do
        if IsIsomorphicPlanGraphOriented(fPLori, ePLori)=true then
          return;
        fi;
      od;
      Add(ListAdmi, ePLori);
    end;
    for NewPLori in NewLPL
    do
      VEFori:=PlanGraphOrientedToVEF(NewPLori);
      if Set(List(VEFori.VertSet, Length))=[6] then
        FuncInsert(NewPLori);
      fi;
    od;
    for nPLori in ListAdmi
    do
      VEFori:=PlanGraphOrientedToVEF(nPLori);
      iClass:=Length(Filtered(VEFori.FaceSet, x->Length(x)=1));
      pos:=Length(VEFori.VertSet);
      Add(ListReturn[pos][iClass+1].LPL, nPLori);
    od;
  od;
  if TheOpt="equality" then
    return ListReturn[nbV];
  else
    return ListReturn;
  fi;
end;



GetAll_123spheres_compact:=function(nbV)
  local nbVtot, GetGraphs, IsCorrect, ListReturn, i, LPLret, iClass, nbVert, res, LPL, LPLgen, ePLori, LPLpart, fPLori, NewLPL, ListAdmi, FuncInsert, NewPLori, VEFori, nPLori, pos;
  nbVtot:=6*nbV;
  GetGraphs:=function(nbVert)
    local p4, p6, ListFaceDesc, LPL, ePL, PLori;
    if nbVert=2 then
      return [Mbundle(3)];
    fi;
    p4:=6;
    p6:=(3*nbVert - 4*p4)/6;
    ListFaceDesc:=[[4, rec(eNature:="plus", nb:=p4)], 
                   [6, rec(eNature:="plus", nb:=p6)]];
    LPL:=[];
    for ePL in GetList3valentPlaneGraphSpecifiedFaces(nbVert, ListFaceDesc)
    do
      PLori:=PlanGraphToPlanGraphOriented(ePL);
      Add(LPL, PLori);
    od;
    return LPL;
  end;
  IsCorrect:=function(fPLori)
    local VEFori;
    VEFori:=PlanGraphOrientedToVEF(fPLori);
    nbVert:=Length(VEFori.VertSet);
    return nbVert<=nbVtot;
  end;
  ListReturn:=[];
  for i in [1..nbV]
  do
    LPLret:=[];
    for iClass in [0..3]
    do
      Add(LPLret, rec(class:=iClass, LPL:=[]));
    od;
    Add(ListReturn, LPLret);
  od;
  for nbVert in [2..nbVtot]
  do
    res:=nbVert mod 2;
    if res=0 then
      LPL:=GetGraphs(nbVert);
      LPLgen:=[];
      for ePLori in LPL
      do
        LPLpart:=123_GetGeneratedGraphs(ePLori, nbVtot, 6);
        for fPLori in LPLpart
        do
          if IsCorrect(fPLori) then
            NewLPL:=InverseTruncationOriented(fPLori);
            ListAdmi:=[];
            FuncInsert:=function(ePLori)
              local fPLori;
              for fPLori in ListAdmi
              do
                if IsIsomorphicPlanGraphOriented(fPLori, ePLori)=true then
                  return;
                fi;
              od;
              Add(ListAdmi, ePLori);
            end;
            for NewPLori in NewLPL
            do
              VEFori:=PlanGraphOrientedToVEF(NewPLori);
              if Set(List(VEFori.VertSet, Length))=[6] then
                FuncInsert(NewPLori);
              fi;
            od;
            for nPLori in ListAdmi
            do
              VEFori:=PlanGraphOrientedToVEF(nPLori);
              iClass:=Length(Filtered(VEFori.FaceSet, x->Length(x)=1));
              pos:=Length(VEFori.VertSet);
              Add(ListReturn[pos][iClass+1].LPL, nPLori);
            od;
          fi;
        od;
      od;
    fi;
  od;
  return ListReturn;
end;


