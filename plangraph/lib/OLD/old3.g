



# PlanGraph is a 3-valent oriented triangulation of a map
PreparationParametrization:=function(PlanGraph)
  local CC, VEF, VertSet, EdgeSet, FaceSet, ListFlags1, ListFlags, iVert, eEdge, test, MatchedDE, OtherDE, eFac, StabilizedSet, eFlag, fFlag, GRP, ListGenOrig, ListGenMapped, iGen, eGen, LER, iFlag, Stab, i, GrpFlag, GrpStab, RotationGroup, phi, FlagMapping, ListGen;
  CC:=CellComplex(PlanGraph);
  VEF:=PlanGraphToVEFsecond(PlanGraph);
  VertSet:=[];
  for i in [1..VEF[1]]
  do
    Add(VertSet, i);
  od;
  EdgeSet:=VEF[2];
  FaceSet:=VEF[3];
  ListFlags1:=[];
  ListFlags:=[];
  for iVert in VertSet
  do
    for eEdge in EdgeSet
    do
      test:=false;
      if eEdge[1][1]=iVert then
        MatchedDE:=eEdge[1];
        OtherDE:=eEdge[2];
        test:=true;
      fi;
      if eEdge[2][1]=iVert then
        MatchedDE:=eEdge[2];
        OtherDE:=eEdge[1];
        test:=true;
      fi;
      if test=true then
        for eFac in FaceSet
        do
          if Position(eFac, MatchedDE)<>fail then
            Add(ListFlags1, [iVert, eEdge, eFac]);
            Add(ListFlags, [iVert, eEdge, eFac]);
          fi;
          if Position(eFac, OtherDE)<>fail then
            Add(ListFlags, [iVert, eEdge, eFac]);
          fi;
        od;
      fi;
    od;
  od;
  StabilizedSet:=[];
  for eFlag in ListFlags1
  do
    AddSet(StabilizedSet, Position(ListFlags, eFlag));
  od;
  GRP:=AutGroupGraph(CC.CellGraph);
  ListGenOrig:=GeneratorsOfGroup(GRP);
  ListGenMapped:=[];
  FlagMapping:=function(eFlag, eGen)
    local pos1, pos2, pos3, pos1b, pos2b, pos3b;
    pos1:=Position(CC.ListCells, eFlag[1]);
    pos2:=Position(CC.ListCells, eFlag[2]);
    pos3:=Position(CC.ListCells, eFlag[3]);
    pos1b:=OnPoints(pos1, eGen);
    pos2b:=OnPoints(pos2, eGen);
    pos3b:=OnPoints(pos3, eGen);
    return [CC.ListCells[pos1b], CC.ListCells[pos2b], CC.ListCells[pos3b]];
  end;

  for iGen in [1..Length(ListGenOrig)]
  do
    eGen:=ListGenOrig[iGen];
    LER:=[];
    for iFlag in [1..Length(ListFlags)]
    do
      eFlag:=ListFlags[iFlag];
      Add(LER, Position(ListFlags, FlagMapping(eFlag, eGen)));
    od;
    Add(ListGenMapped, PermList(LER));
  od;
  GrpFlag:=Group(ListGenMapped);
  GrpStab:=Stabilizer(GrpFlag, StabilizedSet, OnSets);
  ListGen:=[];
  phi:=GroupHomomorphismByImages(GRP, GrpStab, ListGenOrig, ListGenMapped);
  RotationGroup:=PreImage(phi, GrpStab);
  for eGen in GeneratorsOfGroup(RotationGroup)
  do
    LER:=[];
    for iFlag in [1..Length(ListFlags1)]
    do
      eFlag:=ListFlags1[iFlag];
      Add(LER, Position(ListFlags1, FlagMapping(eFlag, eGen)));
    od;
    Add(ListGen, PermList(LER));
  od;
  return rec(CC:=CC, RotationGroup:=RotationGroup,
             ListFlags:=ListFlags,
             PlanGraph:=PlanGraph,
             ListFlags1:=ListFlags1,
             FlagMapping:=FlagMapping,
             RotationGroupFlag:=GrpStab, 
             RotationGroupFlag1:=Group(ListGen), 
             FaceSet:=FaceSet,
             EdgeSet:=EdgeSet);
end;





ExtractionParameter:=function(PLE, SymGRP)
  local iVert, ListFlagByVert, ListEquationsBasic, ListMatched, TheEqua, iFlag, eFlag, nbFac, GRA, iFac, eDE, rDE, jFac, TheSpann, ListCurvature, FuncDEtoFlag, Ladj, ListEdgeDualGraph, FuncFindEdge, fEdge, TheSpannEdges, ListPos, eEdge, iEdge, IsFinished, jEdge, TheVert, OthVert, MatchedDE, OtherDE, jFlag, ListListAdj, u, testOK, NULLS, EquaSet, ListSeto, PowerOrder, nb, ListGen, iGen, BSE, eGen, eCase;
  ListFlagByVert:=[];
  ListEquationsBasic:=[];
  for iVert in [1..Length(PLE.PlanGraph)]
  do
    ListMatched:=[];
    TheEqua:=[];
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      Add(TheEqua, 0);
    od;
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      eFlag:=PLE.ListFlags1[iFlag];
      if eFlag[1]=iVert then
        Add(ListMatched, eFlag);
        TheEqua[iFlag]:=1;
      fi;
    od;
    Add(ListFlagByVert, ListMatched);
    Add(ListEquationsBasic, TheEqua);
  od;
  nbFac:=Length(PLE.FaceSet);
  GRA:=NullGraph(Group(()), nbFac);
  ListCurvature:=[];
  DualGraph:=[];
  for iFac in [1..nbFac]
  do
    Ladj:=[];
    for eDE in PLE.FaceSet[iFac]
    do
      rDE:=Reverse(PLE.PlanGraph, eDE);
      for jFac in [1..nbFac]
      do
        if Position(PLE.FaceSet[jFac], rDE)<>fail then
          AddEdgeOrbit(GRA, [iFac, jFac]);
          Add(Ladj, jFac);
        fi;
      od;
    od;
    Add(DualGraph, Ladj);
    Add(ListCurvature, 6-Length(PLE.FaceSet[iFac]));
  od;
  ListEdgeDualGraph:=__EdgeSet(DualGraph);
  FuncFindEdge:=function(eEdge)
    local fEdge, fSet;
    for fEdge in ListEdgeDualGraph
    do
      fSet:=Set([fEdge[1][1], fEdge[2][1]]);
      if fSet=eEdge then
        return fEdge;
      fi;
    od;
  end;
  TheSpann:=SpanningTreeGraph(GRA, 1);
  TheSpannEdges:=[];
  ListMatched:=[];
  for iEdge in [1..Length(TheSpann)]
  do
    eEdge:=TheSpann[iEdge];
    fEdge:=FuncFindEdge(eEdge);
    RemoveSet(ListEdgeDualGraph, fEdge);
    Add(TheSpannEdges, fEdge);
    Add(ListMatched, 0);
  od;
  FuncDEtoFlag:=function(eDE)
    local iFac, jFac, eFac, fFac, ListIE, ListJF, ListEdgeIE, ListEdgeJF, iFlag, fFlag, INTS, posIE;
    iFac:=eDE[1];
    jFac:=DualGraph[eDE[1]][eDE[2]];
    eFac:=PLE.FaceSet[iFac];
    fFac:=PLE.FaceSet[jFac];
    ListIE:=[];
    ListJF:=[];
    ListEdgeIE:=[];
    ListEdgeJF:=[];
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      fFlag:=PLE.ListFlags1[iFlag];
      if eFac=fFlag[3] then
        Add(ListIE, iFlag);
        Add(ListEdgeIE, fFlag[2]);
      fi;
      if fFac=fFlag[3] then
        Add(ListJF, iFlag);
        Add(ListEdgeJF, fFlag[2]);
      fi;
    od;
    INTS:=Intersection(Set(ListEdgeIE), Set(ListEdgeJF));
    posIE:=Position(ListEdgeIE, INTS[1]);
    return ListIE[posIE];
  end;

  for eEdge in ListEdgeDualGraph
  do
    ListPos:=[];
    for eDE in eEdge
    do
      Add(ListPos, FuncDEtoFlag(eDE));
    od;
    TheEqua:=[];
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      Add(TheEqua, 0);
    od;
    TheEqua[ListPos[1]]:=1;
    TheEqua[ListPos[2]]:=1;
    Add(ListEquationsBasic, TheEqua);
  od;
  while(true)
  do
    IsFinished:=true;
    for iEdge in [1..Length(TheSpann)]
    do
      if ListMatched[iEdge]=0 then
        IsFinished:=false;
        Ladj:=[];
        ListListAdj:=[[],[]];
        for jEdge in [1..Length(TheSpann)]
        do
          if iEdge<>jEdge and ListMatched[jEdge]=0 then
            for u in [1,2]
            do
              iVert:=TheSpann[iEdge][u];
              if iVert in TheSpann[jEdge] then
                Add(ListListAdj[u], jEdge);
              fi;
            od;
          fi;
        od;
        testOK:=false;
        u:=1;
        while(u<=2)
        do
          if Length(ListListAdj[u])=0 then
            TheVert:=TheSpann[iEdge][u];
            OthVert:=TheSpann[iEdge][3-u];
            testOK:=true;
            break;
          fi;
          u:=u+1;
        od;
        if testOK=true then
          ListMatched[iEdge]:=1;
          for eDE in TheSpannEdges[iEdge]
          do
            if eDE[1]=TheVert then
              MatchedDE:=eDE;
            fi;
            if eDE[1]=OthVert then
              OtherDE:=eDE;
            fi;
          od;
          TheEqua:=[];
          for iFlag in [1..Length(PLE.ListFlags1)]
          do
            Add(TheEqua, 0);
          od;
          iFlag:=FuncDEtoFlag(MatchedDE);
          jFlag:=FuncDEtoFlag(OtherDE);
          TheEqua[iFlag]:=1;
          TheEqua[jFlag]:=E(6)^(ListCurvature[TheVert]);
          Add(ListEquationsBasic, TheEqua);
          ListCurvature[OthVert]:=ListCurvature[OthVert]+ListCurvature[TheVert];
          ListCurvature[TheVert]:=0;
        fi;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  # now going for the groups
  Print("SymGRP=", SymGRP, "\n");
  ListGen:=GeneratorsOfGroup(SymGRP);
  PowerOrder:=function(eElt)
    local fElt, ord;
    fElt:=();
    ord:=1;
    while(not(fElt*eElt=()))
    do
      fElt:=fElt*eElt;
      ord:=ord+1;
    od;
    return ord;
  end;
  ListSeto:=[];
  for iGen in [1..Length(ListGen)]
  do
    nb:=PowerOrder(ListGen[iGen]);
    if nb=6 then
      Add(ListSeto, [0..5]);
    elif nb=3 then
      Add(ListSeto, [0,2,4]);
    elif nb=2 then
      Add(ListSeto, [0,3]);
    else
      Add(ListSeto, [0]);
    fi;
  od;
  BSE:=BuildSetMultiple(ListSeto);
  Print("dim=", Length(NullspaceMat(TransposedMat(ListEquationsBasic))), "\n");

  for eCase in BSE
  do
    EquaSet:=ShallowCopy(ListEquationsBasic);
    for iGen in [1..Length(ListGen)]
    do
      eGen:=ListGen[iGen];
      for iFlag in [1..Length(PLE.ListFlags1)]
      do
        TheEqua:=ListWithIdenticalEntries(Length(PLE.ListFlags1), 0);
        jFlag:=OnPoints(iFlag, eGen);
        if jFlag<>iFlag then
          TheEqua[jFlag]:=1;
          TheEqua[iFlag]:=-(E(6)^(eCase[iGen]));
          Add(EquaSet, TheEqua);
        fi;
      od;
    od;
    NULLS:=NullspaceMat(TransposedMat(EquaSet));
    Print("eCase=", eCase, "\n");
    Print("number parameter=", Length(NULLS), "\n");
  od;
  return EquaSet;
end;



