#
# return the number k such that 
# NextKIdx(nbU, iPos1, k)=iPos2
DifferenceIndex:=function(nbU, iPos1, iPos2)
  local nb, idx;
  nb:=0;
  idx:=iPos1;
  while(true)
  do
    if idx=iPos2 then
      break;
    fi;
    idx:=NextIdx(nbU, idx);
    nb:=nb+1;
  od;
  return nb;
end;

CyclicInterval:=function(nbU, iPos1, iPos2)
  local RetSEQ, idx;
  idx:=iPos1;
  RetSEQ:=[];
  while(true)
  do
    Add(RetSEQ, idx);
    if idx=iPos2 then
      break;
    fi;
    idx:=NextIdx(nbU, idx);
  od;
  return RetSEQ;
end;

#CyclicInterval:=function(NBU, h1, h2)
#  local idx, ListValue;
#  idx:=h1;
#  ListValue:=[h1];
#  while(true)
#  do
#    idx:=NextIdx(NBU, idx);
#    Add(ListValue, idx);
#    if idx=h2 then
#      break;
#    fi;
#  od;
#  return ListValue;
#end;







PatchKgon:=function(K)
  local SEQ, MAP, GRA, i;
  GRA:=NullGraph(Group(()), K);
  MAP:=[1..K];
  SEQ:=ListWithIdenticalEntries(K, 2);
  for i in [1..K]
  do
    AddEdgeOrbit(GRA, [i, NextIdx(K, i)]);
    AddEdgeOrbit(GRA, [NextIdx(K, i), i]);
  od;
  return [GRA, rec(SEQ:=SEQ, MAP:=MAP), Reversed(MAP)];
end;


FuncTestPgonality:=function(eREQ, P)
  local nbNotP, eFac;
  if eREQ=false then
    return true;
  fi;
  nbNotP:=0;
  for eFac in eREQ[3]
  do
    if Length(eFac)<>P then
      nbNotP:=nbNotP+1;
    fi;
  od;
  if nbNotP>0 then
    return false;
  else
    return false;
  fi;
end;


#I code the patch by:
#--the sequence of 2 and 3
#--the graph of the skeleton
#--the mapping of vertices to the sequence
# this works only for pentagons.
ExtensionPatch:=function(REQ, InsertPt, P)
  local SEQ, GRA, MAP, Pos1, Pos2, pos, newSEQ, newMAP, i, returnedMAP, returnedGRA, returnedSEQ, PathAdd, iVert, jVert, newPos1, newPos2, NbNewVert, nbSE, NBA;
  SEQ:=REQ.SEQ;
  GRA:=REQ.GRA;
  MAP:=REQ.MAP;
  Pos1:=InsertPt;
  Pos2:=NextIdx(Length(SEQ), InsertPt);
  NBA:=2;
  while(true)
  do
    if SEQ[Pos2]=2 then
      break;
    fi;
    Pos2:=NextIdx(Length(SEQ), Pos2);
    NBA:=NBA+1;
  od;
  if Pos1=Pos2 then
    return false;
  fi;
  newSEQ:=[];
  newMAP:=[];
  pos:=Pos1;
  for i in [1..Length(SEQ)]
  do
    Add(newSEQ, SEQ[pos]);
    Add(newMAP, MAP[pos]);
    pos:=NextIdx(Length(SEQ), pos);
  od;
  newPos1:=1;
  newPos2:=NBA;
  nbSE:=newPos2-newPos1;
  NbNewVert:=P-1-nbSE;
  if NbNewVert<0 then
    return false;
  fi;
  returnedSEQ:=[];
  returnedMAP:=[];
  returnedGRA:=NullGraph(Group(()), GRA.order+NbNewVert);
  for iVert in [1..GRA.order-1]
  do
    for jVert in [iVert+1..GRA.order]
    do
      if IsEdge(GRA, [iVert, jVert]) then
        AddEdgeOrbit(returnedGRA, [iVert, jVert]);
        AddEdgeOrbit(returnedGRA, [jVert, iVert]);
      fi;
    od;
  od;
  Add(returnedSEQ, 3);
  Add(returnedMAP, newMAP[1]);
  PathAdd:=[newMAP[1]];
  for i in [1..NbNewVert]
  do
    Add(returnedSEQ, 2);
    Add(returnedMAP, GRA.order+i);
    Add(PathAdd, GRA.order+i);
  od;
  Add(returnedSEQ, 3);
  Add(returnedMAP, newMAP[newPos2]);
  Add(PathAdd, newMAP[newPos2]);
  for iVert in [newPos2+1..Length(SEQ)]
  do
    Add(returnedSEQ, newSEQ[iVert]);
    Add(returnedMAP, newMAP[iVert]);
  od;
  for iVert in [1..Length(PathAdd)-1]
  do
    AddEdgeOrbit(returnedGRA, [PathAdd[iVert], PathAdd[iVert+1]]);
    AddEdgeOrbit(returnedGRA, [PathAdd[iVert+1], PathAdd[iVert]]);
  od;
  return rec(SEQ:=returnedSEQ, MAP:=returnedMAP, GRA:=returnedGRA);
end;



__PartitionnedGraph:=function(ExtendedREQ)
  local nbBound, GRA, n, GR, i, j, iBound, eBound, eVert;
  nbBound:=Length(ExtendedREQ[2]);
  GRA:=ExtendedREQ[1];
  n:=GRA.order;
  GR:=NullGraph(Group(()), n+nbBound);
  for i in [1..n]
  do
    for j in Adjacency(GRA, i)
    do
      AddEdgeOrbit(GR, [i,j]);
    od;
  od;
  for iBound in [1..nbBound]
  do
    eBound:=ExtendedREQ[2][iBound];
    for eVert in eBound.MAP
    do
      AddEdgeOrbit(GR, [eVert, n+iBound]);
    od;
  od;
  return GR;
end;


GeneralizedPolycycleIsometryGroup:=function(ExtendedREQ)
  local nbBound, GRA, ThePartition, TheGraph, GRP;
  nbBound:=Length(ExtendedREQ[2]);
  GRA:=ExtendedREQ[1];
  ThePartition:=[[1..GRA.order], [GRA.order+1..GRA.order+nbBound]];
  TheGraph:=__PartitionnedGraph(ExtendedREQ);
  GRP:=SymmetryGroupVertexColoredGraph(TheGraph, ThePartition);
  return GRP;
end;


IsIsomorphicGeneralizedPolycycle:=function(ExtendedREQ1, ExtendedREQ2)
  local nbBound, GRA, ThePartition, TheGraph1, TheGraph2, test;
  nbBound:=Length(ExtendedREQ1[2]);
  GRA:=ExtendedREQ1[1];
  ThePartition:=[[1..GRA.order], [GRA.order+1..GRA.order+nbBound]];
  TheGraph1:=__PartitionnedGraph(ExtendedREQ1);
  TheGraph2:=__PartitionnedGraph(ExtendedREQ2);
  test:=EquivalenceVertexColoredGraph(TheGraph1, TheGraph2, ThePartition);
  return test;
end;






FindFaces:=function(REQ)
  local ListFaces, TheGra, TheSEQ, TheMap, iPos1, iPos2, idx, idx2, TheNewSEQ, TheNewMap, eFac, ePath, i, eVert;
  ListFaces:=[];
  TheGra:=ShallowCopy(REQ.GRA);
  TheSEQ:=ShallowCopy(REQ.SEQ);
  TheMap:=ShallowCopy(REQ.MAP);
  while(true)
  do
    iPos1:=Position(TheSEQ, 3);
    if iPos1=fail then
      return ListFaces;
    fi;
    iPos2:=PositionNthOccurrence(TheSEQ, 3, 2);
    idx:=iPos1;
    eFac:=[];
    while(true)
    do
      if idx<>iPos1 then
        Add(eFac, TheMap[idx]);
      fi;
      idx2:=NextIdx(Length(TheSEQ), idx);
      RemoveEdgeOrbit(TheGra, [TheMap[idx], TheMap[idx2]]);
      RemoveEdgeOrbit(TheGra, [TheMap[idx2], TheMap[idx]]);
      idx:=idx2;
      if idx=iPos2 then
        break;
      fi;
    od;
    ePath:=FindShortestPath(TheGra, TheMap[iPos1], TheMap[iPos2]);
    TheNewSEQ:=[];
    TheNewMap:=[];
    for i in [1..Length(ePath)-1]
    do
      if i=1 then
        Add(TheNewSEQ, 2);
      else
        Add(TheNewSEQ, 3);
      fi;
      Add(TheNewMap, ePath[i]);
    od;
    idx:=iPos2;
    while(true)
    do
      eVert:=TheMap[idx];
      Add(TheNewSEQ, Length(Adjacency(TheGra, eVert)));
      Add(TheNewMap, eVert);
      idx:=NextIdx(Length(TheSEQ), idx);
      if idx=iPos1 then
        break;
      fi;
    od;
    TheSEQ:=ShallowCopy(TheNewSEQ);
    TheMap:=ShallowCopy(TheNewMap);
    eFac:=Reversed(eFac);
    Append(eFac, ePath);
    Add(ListFaces, eFac);
  od;
  return ListFaces;
end;


ElementaryKgon:=function(nGon)
  local TheFac, SEQ, MAP, i, Gra, iNext;
  TheFac:=[];
  SEQ:=[];
  MAP:=[];
  for i in [1..nGon]
  do
    Add(TheFac, i);
    Add(SEQ, 2);
    Add(MAP, i);
  od;
  Gra:=NullGraph(Group(()), nGon);
  for i in [1..nGon]
  do
    iNext:=NextIdx(nGon, i);
    AddEdgeOrbit(Gra, [i, iNext]);
    AddEdgeOrbit(Gra, [iNext, i]);
  od;
  return [Gra, rec(SEQ:=SEQ, MAP:=MAP), [TheFac]];
end;




FindGenus:=function(ExtendedREQ)
  local nbVert, nbFace, nbEdge, iVert, eGenus;
  nbVert:=ExtendedREQ[1].order;
  nbFace:=Length(ExtendedREQ[3])+Length(ExtendedREQ[2]);
  nbEdge:=0;
  for iVert in [1..nbVert]
  do
    nbEdge:=nbEdge+Length(Adjacency(ExtendedREQ[1], iVert));
  od;
  nbEdge:=nbEdge/2;
  eGenus:=(2-(nbFace-nbEdge+nbVert))/2;
  return eGenus;
end;






ListNBofExtendedREQ:=function(ExtendedREQ, Pgon, Qgon)
  local iVert, ListNB, x, nbFacCont, eFac;
  ListNB:=[0,0,0,0];
  for iVert in [1..ExtendedREQ[1].order]
  do
    x:=0;
    nbFacCont:=0;
    for eFac in ExtendedREQ[3]
    do
      if Position(eFac, iVert)<>fail then
        nbFacCont:=nbFacCont+1;
        if Length(eFac)=Pgon then
          x:=x+1;
        fi;
      fi;
    od;
    if nbFacCont=3 then
      ListNB[x+1]:=ListNB[x+1]+1;
    fi;
  od;
  return ListNB;
end;



Vsplit:=function(eList)
  return List([1..Length(eList)], x->[eList[x], eList[NextIdx(Length(eList), x)]]);
end;




# ListGonalities should be of the form [Pgon,Qgon]
#
AdjacencyPattern:=function(RestrictedREQ, TheFac, ListGonalities)
  local FindFac, Sadj, ePair, VC, pos, ListListPair;
  ListListPair:=List(RestrictedREQ[3], x->List(Vsplit(x), y->Set(y)));
  FindFac:=function(ePair)
    local eFac, iFac;
    for iFac in [1..Length(RestrictedREQ[3])]
    do
      eFac:=RestrictedREQ[3][iFac];
      if eFac<>TheFac then
        if Position(ListListPair[iFac], Set(ePair))<>fail then
          return eFac;
        fi;
      fi;
    od;
    return [];
  end;
  Sadj:=ListWithIdenticalEntries(Length(ListGonalities), 0);
  for ePair in Vsplit(TheFac)
  do
    VC:=FindFac(ePair);
    if Length(VC)>0 then
      pos:=Position(ListGonalities, Length(VC));
      Sadj[pos]:=Sadj[pos]+1;
    fi;
  od;
  return Sadj;
end;



LowerBoundNumberOfVertices:=function(ExtendedREQ)
  local nbVert, nbEdge, iVert, jVert, eBoundary, nb2, u;
  nbVert:=ExtendedREQ[1].order;
  nbEdge:=0;
  for iVert in [1..nbVert-1]
  do
    for jVert in [iVert+1..nbVert]
    do
      if IsEdge(ExtendedREQ[1], [iVert, jVert])=true then
        nbEdge:=nbEdge+1;
      fi;
    od;
  od;
  for eBoundary in ExtendedREQ[2]
  do
    nb2:=0;
    for u in eBoundary.SEQ
    do
      if u=2 then
        nb2:=nb2+1;
      fi;
    od;
    if nb2 mod 2=0 then
      nbEdge:=nbEdge+nb2/2;
    else
      nbEdge:=nbEdge+(nb2+3)/2;
    fi;
  od;
  return nbEdge*(2/3);
end;









FromWorkingPentHexToListOfGraphs:=function(TheMaps)
  local LPL, eMap, FaceSet, eBoundary, nbVert, EdgeSet, iVert, jVert, PL;
  LPL:=[];
  for eMap in TheMaps
  do
    FaceSet:=Set(eMap[3]);
    for eBoundary in eMap[2]
    do
      Add(FaceSet, Set(eBoundary.MAP));
    od;
    nbVert:=eMap[1].order;
    EdgeSet:=[];
    for iVert in [1..nbVert]
    do
      for jVert in Adjacency(eMap[1], iVert)
      do
        AddSet(EdgeSet, Set([iVert, jVert]));
      od;
    od; 
    PL:=VEFtoPlanGraph([nbVert, EdgeSet, FaceSet]);
    Add(LPL, PL);
  od;
  return LPL;
end;



ProcedureSetEnumerationWeakFaceRegularQRj:=function(Pgon, Qgon, j, FuncGlobalKilling, FuncGlobalKillingSec, TheDeg)
  local FuncGlobalKillingInfo, FuncAppendGlobalKillingInfo, FuncAppendLocalKillingInfo, FuncLocalKilling, ListGonalities, LocalPossibleGonalities;

  FuncGlobalKillingInfo:=function(ExtendedREQ)
    return ListNBofExtendedREQ(ExtendedREQ, Pgon, Qgon);
  end;
  FuncAppendGlobalKillingInfo:=function(KI1, KI2)
    return KI1+KI2;
  end;
  FuncAppendLocalKillingInfo:=function(KI1, KI2)
    return KI1+KI2;
  end;
  FuncLocalKilling:=function(H, LocalKillingInfo)
    if H=Qgon then
      if LocalKillingInfo[1]>Qgon-j then
        return false;
      fi;
      if LocalKillingInfo[2]>j then
        return false;
      fi;
    fi;
    return true;
  end;
  ListGonalities:=[Pgon,Qgon];
  LocalPossibleGonalities:=function(RestrictedREQ, ListPair)
    local PossibleP, PossibleQ, iVert, ListAdj, pos, nb_ScenaryP, nb_ScenaryQ, x, FindFac, eFac, u, i, ePair, ListPoss, MatchedVertices, MatchedTwoTimes, AdjPat, TotalExclusion;
    PossibleP:=true;
    PossibleQ:=true;
    MatchedVertices:=[];
    MatchedTwoTimes:=[];
    for ePair in ListPair
    do
      for iVert in ePair
      do
        if iVert in MatchedVertices then
          AddSet(MatchedTwoTimes, iVert);
        else
          AddSet(MatchedVertices, iVert);
        fi;
      od;
    od;
    nb_ScenaryP:=ListWithIdenticalEntries(TheDeg+1, 0);
    nb_ScenaryQ:=ListWithIdenticalEntries(TheDeg+1, 0);
    for iVert in MatchedTwoTimes
    do
      x:=0;
      for eFac in RestrictedREQ[3]
      do
        if Position(eFac, iVert)<>fail then
          if Length(eFac)=Pgon then
            x:=x+1;
          fi;
        fi;
      od;
      nb_ScenaryP[x+2]:=nb_ScenaryP[x+2]+1;
      nb_ScenaryQ[x+1]:=nb_ScenaryQ[x+1]+1;
    od;
    FindFac:=function(ePair)
      local eFac;
      for eFac in RestrictedREQ[3]
      do
        if IsSubset(Set(eFac),Set(ePair))=true then
          return eFac;
        fi;
      od;
    end;
    TotalExclusion:=false;
    ListAdj:=[0,0];
    for ePair in ListPair
    do
      eFac:=FindFac(ePair);
      pos:=Position(ListGonalities, Length(eFac));
      ListAdj[pos]:=ListAdj[pos]+1;
      AdjPat:=AdjacencyPattern(RestrictedREQ, eFac, ListGonalities);
      if Length(eFac)=Qgon then
        if AdjPat[2]=j then
          PossibleQ:=false;
        fi;
        if AdjPat[2]>j then
          TotalExclusion:=true;
        fi;
        if AdjPat[1]=Qgon-j then
          PossibleP:=false;
        fi;
        if AdjPat[1]>Qgon-j then
          TotalExclusion:=true;
        fi;
      fi;
    od;
    ListPoss:=[];
    if TotalExclusion=true then
      return [];
    fi;
    if PossibleP=true then
      Add(ListPoss, rec(Gonality:=Pgon, GlobalKillingInfo:=nb_ScenaryP, LocalKillingInfo:=ListAdj));
    fi;
    if PossibleQ=true then
      Add(ListPoss, rec(Gonality:=Qgon, GlobalKillingInfo:=nb_ScenaryQ, LocalKillingInfo:=ListAdj));
    fi;
    return ListPoss;
  end;
  return rec(FuncGlobalKillingInfo:=FuncGlobalKillingInfo,
             FuncGlobalKilling:=FuncGlobalKilling, 
             FuncGlobalKillingSec:=FuncGlobalKillingSec, 
             FuncLocalKilling:=FuncLocalKilling, 
             LocalPossibleGonalities:=LocalPossibleGonalities,
             FuncAppendLocalKillingInfo:=FuncAppendLocalKillingInfo,
             FuncAppendGlobalKillingInfo:=FuncAppendGlobalKillingInfo,
             ListGonalities:=ListGonalities, TheDeg:=TheDeg);
end;







ProcedureSetEnumerationFaceRegularPRiQRj:=function(Pgon, Qgon, iAuth, jAuth, FuncGlobalKilling, FuncGlobalKillingSec, TheDeg)
  local FuncGlobalKillingInfo, FuncAppendGlobalKillingInfo, FuncAppendLocalKillingInfo, FuncLocalKilling, ListGonalities, LocalPossibleGonalities;

  FuncGlobalKillingInfo:=function(ExtendedREQ)
    return ListNBofExtendedREQ(ExtendedREQ, Pgon, Qgon);
  end;
  FuncAppendGlobalKillingInfo:=function(KI1, KI2)
    return KI1+KI2;
  end;
  FuncAppendLocalKillingInfo:=function(KI1, KI2)
    return KI1+KI2;
  end;
  FuncLocalKilling:=function(H, LocalKillingInfo)
    if H=Qgon then
      if LocalKillingInfo[1]>Qgon-jAuth then
        return false;
      fi;
      if LocalKillingInfo[2]>jAuth then
        return false;
      fi;
    else
      if LocalKillingInfo[1]>iAuth then
        return false;
      fi;
      if LocalKillingInfo[2]>Pgon-iAuth then
        return false;
      fi;
    fi;
    return true;
  end;
  ListGonalities:=[Pgon,Qgon];
  LocalPossibleGonalities:=function(RestrictedREQ, ListPair)
    local PossibleP, PossibleQ, iVert, ListAdj, pos, nb_ScenaryP, nb_ScenaryQ, x, FindFac, eFac, u, i, ePair, ListPoss, MatchedVertices, MatchedTwoTimes, AdjPat, TotalExclusion;
    PossibleP:=true;
    PossibleQ:=true;
    MatchedVertices:=[];
    MatchedTwoTimes:=[];
    for ePair in ListPair
    do
      for iVert in ePair
      do
        if iVert in MatchedVertices then
          AddSet(MatchedTwoTimes, iVert);
        else
          AddSet(MatchedVertices, iVert);
        fi;
      od;
    od;
    nb_ScenaryP:=ListWithIdenticalEntries(TheDeg+1, 0);
    nb_ScenaryQ:=ListWithIdenticalEntries(TheDeg+1, 0);
    for iVert in MatchedTwoTimes
    do
      x:=0;
      for eFac in RestrictedREQ[3]
      do
        if Position(eFac, iVert)<>fail then
          if Length(eFac)=Pgon then
            x:=x+1;
          fi;
        fi;
      od;
      nb_ScenaryP[x+2]:=nb_ScenaryP[x+2]+1;
      nb_ScenaryQ[x+1]:=nb_ScenaryQ[x+1]+1;
    od;
    FindFac:=function(ePair)
      local eFac;
      for eFac in RestrictedREQ[3]
      do
        if IsSubset(Set(eFac),Set(ePair))=true then
          return eFac;
        fi;
      od;
    end;
    ListAdj:=[0,0];
    TotalExclusion:=false;
    for ePair in ListPair
    do
      eFac:=FindFac(ePair);
      pos:=Position(ListGonalities, Length(eFac));
      ListAdj[pos]:=ListAdj[pos]+1;
      AdjPat:=AdjacencyPattern(RestrictedREQ, eFac, ListGonalities);
      if Length(eFac)=Qgon then
        if AdjPat[2]=jAuth then
          PossibleQ:=false;
        fi;
        if AdjPat[2]>jAuth then
          TotalExclusion:=true;
        fi;
        if AdjPat[1]=Qgon-jAuth then
          PossibleP:=false;
        fi;
        if AdjPat[1]>Qgon-jAuth then
          TotalExclusion:=true;
        fi;
      else
        if AdjPat[2]=Pgon-iAuth then
          PossibleQ:=false;
        fi;
        if AdjPat[2]>Pgon-iAuth then
          TotalExclusion:=true;
        fi;
        if AdjPat[1]=iAuth then
          PossibleP:=false;
        fi;
        if AdjPat[1]>iAuth then
          TotalExclusion:=true;
        fi;
      fi;
    od;
    ListPoss:=[];
    if TotalExclusion=true then
      return [];
    fi;
    if PossibleP=true then
      Add(ListPoss, rec(Gonality:=Pgon, GlobalKillingInfo:=nb_ScenaryP, LocalKillingInfo:=ListAdj));
    fi;
    if PossibleQ=true then
      Add(ListPoss, rec(Gonality:=Qgon, GlobalKillingInfo:=nb_ScenaryQ, LocalKillingInfo:=ListAdj));
    fi;
    return ListPoss;
  end;
  return rec(FuncGlobalKillingInfo:=FuncGlobalKillingInfo,
             FuncGlobalKilling:=FuncGlobalKilling, 
             FuncGlobalKillingSec:=FuncGlobalKillingSec, 
             FuncLocalKilling:=FuncLocalKilling, 
             LocalPossibleGonalities:=LocalPossibleGonalities,
             FuncAppendLocalKillingInfo:=FuncAppendLocalKillingInfo,
             FuncAppendGlobalKillingInfo:=FuncAppendGlobalKillingInfo,
             ListGonalities:=ListGonalities, TheDeg:=TheDeg);
end;


ProcedureComputeAllFillings:=function(Pgon)
  local FuncGlobalKilling, FuncGlobalKillingSec, FuncGlobalKillingInfo, FuncAppendGlobalKillingInfo, FuncAppendLocalKillingInfo, FuncLocalKilling, ListGonalities, LocalPossibleGonalities;
  FuncGlobalKilling:=function(GlobalKillingInfo, nbVert)
    return true;
  end;
  FuncGlobalKillingSec:=function(GlobalKillingInfo, ExtendedREQ)
    local eBoundary, nb2, nb3, eVal, x, fp;
    for eBoundary in ExtendedREQ[2]
    do
      nb2:=0;
      nb3:=0;
      for eVal in eBoundary.SEQ
      do
        if eVal=2 then
          nb3:=nb3+1;
        fi;
        if eVal=3 then
          nb2:=nb2+1;
        fi;
      od;
      if Pgon=6 then
        if nb2<>6+nb3 then
          return false;
        fi;
      else
        fp:=(nb2-nb3-6)/(Pgon-6);
        x:=2*fp-2-nb3;
        if IsInt(x)=false or IsInt(fp)=false then
          return false;
        fi;
        if x<0 or fp<0 then
          return false;
        fi;
      fi;
    od;
    return true;
  end;
  FuncGlobalKillingInfo:=function(ExtendedREQ)
    return 0;
  end;
  FuncAppendGlobalKillingInfo:=function(KI1, KI2)
    return KI1+KI2;
  end;
  FuncAppendLocalKillingInfo:=function(KI1, KI2)
    return KI1+KI2;
  end;
  FuncLocalKilling:=function(H, LocalKillingInfo)
    return true;
  end;
  ListGonalities:=[Pgon];
  LocalPossibleGonalities:=function(RestrictedREQ, ListPair)
    return [rec(Gonality:=Pgon, GlobalKillingInfo:=0, LocalKillingInfo:=0)];
  end;
  return rec(FuncGlobalKillingInfo:=FuncGlobalKillingInfo,
             FuncGlobalKilling:=FuncGlobalKilling, 
             FuncGlobalKillingSec:=FuncGlobalKillingSec, 
             FuncLocalKilling:=FuncLocalKilling, 
             LocalPossibleGonalities:=LocalPossibleGonalities,
             FuncAppendLocalKillingInfo:=FuncAppendLocalKillingInfo,
             FuncAppendGlobalKillingInfo:=FuncAppendGlobalKillingInfo,
             ListGonalities:=ListGonalities, TheDeg:=3);
end;

ProcedureSetEnumerationSchemeNanodisk:=function(Pgon, Qgon, nbPgon, nbQgon, TheDeg)
  local FuncGlobalKilling, FuncGlobalKillingSec, FuncGlobalKillingInfo, FuncAppendGlobalKillingInfo, FuncAppendLocalKillingInfo, FuncLocalKilling, ListGonalities, LocalPossibleGonalities;
  FuncGlobalKilling:=function(GlobalKillingInfo, nbVert)
    return true;
  end;
  FuncGlobalKillingSec:=function(GlobalKillingInfo, ExtendedREQ)
    local LowerEstNbFace, nbPgonAlready, nbQgonAlready;
    LowerEstNbFace:=Length(ExtendedREQ[2]) + Length(ExtendedREQ[3])-1;
#    Print("LowerEstNbFace=", LowerEstNbFace, "\n");
    if nbPgon + nbQgon < LowerEstNbFace then
#      Print("nbPgon=", nbPgon, "\n");
#      Print("nbQgon=", nbQgon, "\n");
      return false;
    fi;
    nbPgonAlready:=Length(Filtered(ExtendedREQ[3], x->Length(x)=Pgon));
    nbQgonAlready:=Length(Filtered(ExtendedREQ[3], x->Length(x)=Qgon));
#    Print("nbPgonAlready=", nbPgonAlready, "  nbQgonAlready=", nbQgonAlready, "\n");
    if nbPgonAlready > nbPgon then
#       Print("Kill by nbPgonAlready\n");
      return false;
    fi;
    if nbQgonAlready > nbQgon then
#       Print("Kill by nbQgonAlready\n");
      return false;
    fi;
    return true;
  end;
  FuncGlobalKillingInfo:=function(ExtendedREQ)
    return 0;
  end;
  FuncAppendGlobalKillingInfo:=function(KI1, KI2)
    return KI1+KI2;
  end;
  FuncAppendLocalKillingInfo:=function(KI1, KI2)
    return KI1+KI2;
  end;
  FuncLocalKilling:=function(H, LocalKillingInfo)
    return true;
  end;
  ListGonalities:=[Pgon, Qgon];
  LocalPossibleGonalities:=function(RestrictedREQ, ListPair)
    return [rec(Gonality:=Pgon, GlobalKillingInfo:=0, LocalKillingInfo:=0),
            rec(Gonality:=Qgon, GlobalKillingInfo:=0, LocalKillingInfo:=0)];
  end;
  return rec(FuncGlobalKillingInfo:=FuncGlobalKillingInfo,
             FuncGlobalKilling:=FuncGlobalKilling, 
             FuncGlobalKillingSec:=FuncGlobalKillingSec, 
             FuncLocalKilling:=FuncLocalKilling, 
             LocalPossibleGonalities:=LocalPossibleGonalities,
             FuncAppendLocalKillingInfo:=FuncAppendLocalKillingInfo,
             FuncAppendGlobalKillingInfo:=FuncAppendGlobalKillingInfo,
             ListGonalities:=ListGonalities, TheDeg:=TheDeg);
end;






















Procedure7R2:=function()
  local FuncGlobalKilling, FuncGlobalKillingSec;
  FuncGlobalKilling:=function(GlobalKillingInfo, nbVert)
    local nb03;
    nb03:=GlobalKillingInfo[1]+GlobalKillingInfo[4];
    if nb03>3 then
      return false;
    fi;
    if nbVert+4*nb03>100 then
      return false;
    fi;
    return true;
  end;
  FuncGlobalKillingSec:=function(GlobalKillingInfo, ExtendedREQ)
    local nb5, nb7, eFac;
    nb5:=0;
    nb7:=0;
    for eFac in ExtendedREQ[3]
    do
      if Length(eFac)=5 then
        nb5:=nb5+1;
      else
        nb7:=nb7+1;
      fi;
    od;
    if nb5>32 then
      return false;
    fi;
    if nb7>20 then
      return false;
    fi;
    return true;
  end;
  return ProcedureSetEnumerationWeakFaceRegularQRj(5, 7, 2, FuncGlobalKilling, FuncGlobalKillingSec);
end;





FuncListPositionTwo:=function(eList, TheDeg)
  return Filtered([1..Length(eList)], x->eList[x]<TheDeg);
end;


PartitionSet:=function(nbPart, nbElt)
  local ListP, i, eP, H;
  if nbPart=1 then
    return [[nbElt]];
  fi;
  ListP:=[];
  for i in [0..nbElt]
  do
    Append(ListP, List(PartitionSet(nbPart-1, nbElt-i), x->Concatenation([i], x)));
  od;
  return ListP;
end;


Usplit:=function(ListVert)
  return List([1..Length(ListVert)-1], x->[ListVert[x], ListVert[x+1]]);
end;





#
# input is a RestrictedREQ or ExtendedREQ
# output is a list of RestrictedREQ but with second entry being "void"
#
# SOEP stand for "Set Of Enumeration Procedure"
CompletionProcedure:=function(TheREQ, SOEP)
  local ListFillings, FCTprev, FCTnew, iRK, uRK, testFirst, CaseMinimum, iBoundary, ListListPositionTwo, ListPositionTwo, h1, h2, H, VE, VEnew, eVE, nbCase, ListTotalCases, ListPoss, u, ExtendedREQ2, eCand, reply, TheCases, testIsCompletable, SListNB, ListListScenary, SCEN, ListScenary, ClearingAndTestFinish, CompletionOperation, PossibleTuples, CompletionByTuples, GlobalKillingInfo, nb, iPos1, iPos2, iter, RestrictedREQ, HRL1, HRLprov, TheMinCons, ListGenerated, ListListPositionSEQ, ListPositionSEQ;



  #
  #
  # we complete the graph
  # input a RestrictedREQ
  # output an ExtendedREQ
  CompletionByTuples:=function(RestrictedREQ, TuplesPosition)
    local SEQ, MAP, GRA, Cyc, ListAdditionalVertices, nbVert, i, nbR, Granew, LV, iVert, jVert, ListPairSEQMAP, NewCycle, idx, iNext, iPos1, iPos2, iPos1next, NewSEQ, NewMAP, h, ePair, eUples, iPos2next;
    GRA:=RestrictedREQ[1];
    SEQ:=RestrictedREQ[2].SEQ;
    MAP:=RestrictedREQ[2].MAP;
    Cyc:=ShallowCopy(RestrictedREQ[3]);
    ListAdditionalVertices:=[];
    nbVert:=GRA.order;
    for eUples in TuplesPosition
    do
      nbR:=eUples.nb;
      LV:=[nbVert+1..nbVert+nbR];
      nbVert:=nbVert+nbR;
      Add(ListAdditionalVertices, LV);
    od;
    Granew:=NullGraph(Group(()), nbVert);
    for iVert in [1..GRA.order-1]
    do
      for jVert in [iVert+1..GRA.order]
      do
        if IsEdge(GRA, [iVert, jVert])=true then
          AddEdgeOrbit(Granew, [iVert, jVert]);
          AddEdgeOrbit(Granew, [jVert, iVert]);
        fi;
      od;
    od;
    ListPairSEQMAP:=[];
    NewCycle:=[];
    for i in [1..Length(TuplesPosition)]
    do
      iPos2:=TuplesPosition[i].iPos2;
      iPos1:=TuplesPosition[i].iPos1;
      Append(NewCycle, MAP{CyclicInterval(Length(SEQ), iPos1, iPos2)});
      Append(NewCycle, ListAdditionalVertices[i]);
      iNext:=NextIdx(Length(TuplesPosition), i);
      iPos1next:=TuplesPosition[iNext].iPos1;
      iPos2next:=TuplesPosition[iNext].iPos2;
      LV:=Concatenation([MAP[iPos2]], ListAdditionalVertices[i], [MAP[iPos1next]]);
      for ePair in Usplit(LV)
      do
        AddEdgeOrbit(Granew, ePair);
        AddEdgeOrbit(Granew, Reversed(ePair));
      od;
      NewSEQ:=[];
      NewMAP:=[];
      for h in CyclicInterval(Length(SEQ), iPos2, iPos1next)
      do
        if h=iPos1next and iPos1next=iPos2next then
          Add(NewSEQ, SEQ[h]+2);
        elif h=iPos2 and iPos1=iPos2 then
          Add(NewSEQ, SEQ[h]+2);
        elif h=iPos1next or h=iPos2 then
          Add(NewSEQ, SEQ[h]+1);
        else
          Add(NewSEQ, SEQ[h]);
        fi;
        Add(NewMAP, MAP[h]);
      od;
      Append(NewMAP, Reversed(ListAdditionalVertices[i]));
      for u in ListAdditionalVertices[i]
      do
        Add(NewSEQ, 2);
      od;
      Add(ListPairSEQMAP, rec(SEQ:=NewSEQ, MAP:=NewMAP));
    od;
    Add(Cyc, NewCycle);
    return [Granew, ListPairSEQMAP, Cyc];
  end;

  CompletionOperation:=function(ExtendedREQ, iBoundary, TuplesPosition)
    local RestrictedREQ, Diffe, NewRestrictedREQ;
    RestrictedREQ:=[ExtendedREQ[1], ExtendedREQ[2][iBoundary], ExtendedREQ[3]];
    Diffe:=ExtendedREQ[2]{Difference([1..Length(ExtendedREQ[2])], [iBoundary])};
    NewRestrictedREQ:=CompletionByTuples(RestrictedREQ, TuplesPosition);
    Append(Diffe, NewRestrictedREQ[2]);
    return [NewRestrictedREQ[1], Diffe, NewRestrictedREQ[3]];
  end;


  #
  #
  # return the list of Tuples containing t1, t2
  #
  # TuplesPosition is a list of t-elements rec(iPos1:=iPos1, iPos2:=iPos2,
  # nb:=nb) which encodes the possible extension by a T-uple.
  #
  PossibleTuples:=function(RestrictedREQ, ListPositionSEQ, h1, h2, ListScenary, H, GlobalKillingInfo)
    local eBoundary, Snb_Scenary, SListAdj, ListProvScal, iter, NewList, eCase, Val, INTV, ListPotential, h3, h4, iPos3, iPos4, Status, nb34, eS, i, eP, nb03, Defect, ePart, UP, eV, nbPart, VCR, nbS;
    ListPositionTwo:=FuncListPositionTwo(ListPositionSEQ, SOEP.TheDeg);
    eBoundary:=RestrictedREQ[2];
    Status:=First(ListScenary[h1], x->x.Gonality=H);
    if Status=fail then
      return [];
    fi;
    ListProvScal:=[[rec(ListTriple:=[rec(h1:=h1, h2:=h2, nb12:=DifferenceIndex(Length(eBoundary.SEQ), ListPositionTwo[h1], ListPositionTwo[h2]))],
GlobalKillingInfo:=SOEP.FuncAppendGlobalKillingInfo(GlobalKillingInfo, Status.GlobalKillingInfo), LocalKillingInfo:=Status.LocalKillingInfo)]];
    for iter in [2..H-1]
    do
      NewList:=[];
      for eCase in ListProvScal[iter-1]
      do
        nbS:=Length(eCase.ListTriple);
        Val:=Sum(eCase.ListTriple, x->x.nb12)+nbS;
        INTV:=CyclicInterval(Length(ListPositionTwo), eCase.ListTriple[nbS].h2, eCase.ListTriple[1].h1);
        for h3 in INTV{[2..Length(INTV)-2]}
        do
          h4:=NextIdx(Length(ListPositionTwo), h3);
          iPos3:=ListPositionTwo[h3];
          iPos4:=ListPositionTwo[h4];
          Status:=First(ListScenary[h3], x->x.Gonality=H);
          nb34:=DifferenceIndex(Length(eBoundary.SEQ), iPos3, iPos4);
          if nb34+Val+1<=H and Status<>fail then
            eS:=Concatenation(eCase.ListTriple, [rec(h1:=h3, h2:=h4, nb12:=nb34)]);
            Add(NewList, rec(ListTriple:=eS, GlobalKillingInfo:=SOEP.FuncAppendGlobalKillingInfo(eCase.GlobalKillingInfo, Status.GlobalKillingInfo), LocalKillingInfo:=SOEP.FuncAppendLocalKillingInfo(eCase.LocalKillingInfo, Status.LocalKillingInfo)));
          fi;
        od;
        for h3 in INTV{[2..Length(INTV)-1]}
        do
          Status:=First(ListScenary[h3], x->x.Gonality=H);
          if ListPositionSEQ[ListPositionTwo[h3]]<SOEP.TheDeg-1 and Val+1<=H then
            eS:=Concatenation(eCase.ListTriple, [rec(h1:=h3, h2:=h3, nb12:=0)]);
            Add(NewList, rec(ListTriple:=eS, GlobalKillingInfo:=eCase.GlobalKillingInfo, LocalKillingInfo:=eCase.LocalKillingInfo));
          fi;
        od;
      od;
      Add(ListProvScal, NewList);
    od;
    ListPotential:=[];
    for eP in ListProvScal
    do
      for eCase in eP
      do
        nbPart:=Length(eCase.ListTriple);
        Val:=nbPart+Sum(eCase.ListTriple, x->x.nb12);
        Defect:=H-Val;
        if SOEP.FuncGlobalKilling(eCase.GlobalKillingInfo, Defect+RestrictedREQ[1].order)=true and SOEP.FuncLocalKilling(H, eCase.LocalKillingInfo)=true then
          for ePart in PartitionSet(nbPart, Defect)
          do
            UP:=[];
            for i in [1..nbPart]
            do
              VCR:=eCase.ListTriple[i];
              Add(UP, rec(iPos1:=ListPositionTwo[VCR.h1], iPos2:=ListPositionTwo[VCR.h2], nb:=ePart[i]));
            od;
            Add(ListPotential, UP);
          od;
        fi;
      od;
    od;
    return ListPotential;
  end;




  ClearingAndTestFinish:=function(ExtendedREQ)
    local ListBoundary, Cyc, eBoundary, TheFac, TheInfo, u, LPOS, pos, testFind;
    ListBoundary:=[];
    GlobalKillingInfo:=SOEP.FuncGlobalKillingInfo(ExtendedREQ);
    Cyc:=ShallowCopy(ExtendedREQ[3]);
    for eBoundary in ExtendedREQ[2]
    do
      LPOS:=Filtered(eBoundary.SEQ, x->x<SOEP.TheDeg);
      if Length(LPOS)=1 and SOEP.TheDeg=3 then
        return false;
      fi;
      if Length(LPOS)=0 then
        pos:=Position(SOEP.ListGonalities, Length(eBoundary.SEQ));
        if pos=fail then
          return false;
        fi;
        TheFac:=Reversed(eBoundary.MAP);
        testFind:=false;
        for u in SOEP.LocalPossibleGonalities([ExtendedREQ[1], eBoundary, ExtendedREQ[3]], Vsplit(TheFac))
        do
          if u.Gonality=Length(TheFac) then
            TheInfo:=u;
            testFind:=true;
          fi;
        od;
        if testFind=true then
          GlobalKillingInfo:=SOEP.FuncAppendGlobalKillingInfo(GlobalKillingInfo, TheInfo.GlobalKillingInfo);
          if SOEP.FuncLocalKilling(Length(TheFac), TheInfo.LocalKillingInfo)=false then
            return false;
          fi;
          Add(Cyc, TheFac);
        else
          return false;
        fi;
      else
        Add(ListBoundary, eBoundary);
      fi;
    od;
    if SOEP.FuncGlobalKillingSec(GlobalKillingInfo, ExtendedREQ)=true and SOEP.FuncGlobalKilling(GlobalKillingInfo, ExtendedREQ[1].order)=true then
      return [ExtendedREQ[1], ListBoundary, Cyc];
    else
      return false;
    fi;
  end;









  ListFillings:=[];
  # list potential Candidates is composed of extendedREQ
  FCTprev:=FuncStocking(1000, PLANGRAPH_tmpdir, "initiator");
  if IsRecord(TheREQ[2])=true then
    FCTprev.FuncAdd([TheREQ[1], [TheREQ[2]], TheREQ[3]]);
  else
    FCTprev.FuncAdd(TheREQ);
  fi;
  iter:=0;
  while(true)
  do
    ListGenerated:=[];
    TheMinCons:=0;
    iter:=iter+1;
    Print("iter=", iter, "  Nr graph to be treated at this stage : ", FCTprev.FuncNbrElement(), "\n");
    FCTnew:=FuncStocking(1000, PLANGRAPH_tmpdir, Concatenation("StockIteration",String(iter), "_"));
    for iRK in [1..FCTprev.FuncNbrElement()]
    do
      uRK:=FCTprev.FuncGet(iRK);
      GlobalKillingInfo:=SOEP.FuncGlobalKillingInfo(uRK);
      testIsCompletable:=true;
      ListListPositionSEQ:=List(uRK[2], x->x.SEQ);
      ListListPositionTwo:=List(ListListPositionSEQ, x->FuncListPositionTwo(x,SOEP.TheDeg));
      ListListScenary:=[];
      for iBoundary in [1..Length(uRK[2])]
      do
        RestrictedREQ:=[uRK[1], uRK[2][iBoundary], uRK[3]];
        ListPositionTwo:=ListListPositionTwo[iBoundary];
        ListScenary:=[];
        for h1 in [1..Length(ListPositionTwo)]
        do
          h2:=NextIdx(Length(ListPositionTwo), h1);
          iPos1:=ListPositionTwo[h1];
          iPos2:=ListPositionTwo[h2];
          nb:=DifferenceIndex(Length(RestrictedREQ[2].SEQ), iPos1, iPos2);
          HRL1:=RestrictedREQ[2].MAP{CyclicInterval(Length(RestrictedREQ[2].SEQ), iPos1, iPos2)};
          VE:=SOEP.LocalPossibleGonalities(RestrictedREQ, Usplit(HRL1));
          VEnew:=Filtered(VE, x->nb<=x.Gonality-1);
          if Length(VEnew)=0 then
            testIsCompletable:=false;
          fi;
          Add(ListScenary, VEnew);
        od;
        Add(ListListScenary, ListScenary);
      od;
      testFirst:=true;
      CaseMinimum:=0;
      if testIsCompletable=true then
        for iBoundary in [1..Length(uRK[2])]
        do
          RestrictedREQ:=[uRK[1], uRK[2][iBoundary], uRK[3]];
          ListPositionTwo:=ListListPositionTwo[iBoundary];
          ListPositionSEQ:=ListListPositionSEQ[iBoundary];
          for h1 in [1..Length(ListPositionTwo)]
          do
            h2:=NextIdx(Length(ListPositionTwo), h1);
            ListTotalCases:=[];
            nbCase:=0;
            for SCEN in ListListScenary[iBoundary][h1]
            do
              VE:=PossibleTuples(RestrictedREQ, ListPositionSEQ, h1, h2, ListListScenary[iBoundary], SCEN.Gonality, GlobalKillingInfo);
              nbCase:=nbCase+Length(VE);
              Add(ListTotalCases, [SCEN.Gonality, iBoundary, VE]);
            od;
            if testFirst=true or CaseMinimum>nbCase then
              CaseMinimum:=nbCase;
              TheCases:=ShallowCopy(ListTotalCases);
              testFirst:=false;
            fi;
          od;
        od;
        for u in TheCases
        do
          H:=u[1];
          iBoundary:=u[2];
          for eCand in u[3]
          do
            ExtendedREQ2:=CompletionOperation(uRK, iBoundary, eCand);
            reply:=ClearingAndTestFinish(ExtendedREQ2);
            if reply<>false then
              if Length(reply[2])=0 then
                Add(ListFillings, reply);
#                Print("PL=", DualGraph(Planar(reply[1]).PlanGraph), "\n");
                SaveDataToFile("listFound", ListFillings);
                Print("Find a new graph with ", reply[1].order, " vertices\n");
              else
                FCTnew.FuncAdd(reply);
                Add(ListGenerated, reply);
                if TheMinCons=0 then
                  TheMinCons:=reply[1].order;
                else
                  TheMinCons:=Minimum(reply[1].order, TheMinCons);
                fi;
              fi;
            fi;
          od;
        od;
      fi;
    od;
    Print("iter=", iter, "  Minimal size of considered graphs=", TheMinCons, "\n");
    if FCTnew.FuncNbrElement()=0 then
      FCTprev.FuncClear();
      break;
    else
      FCTprev.FuncClear();
      Unbind(FCTprev);
      FCTprev:=FCTnew;
    fi;
  od;
  return ListFillings;
end;









AddRingOfQGon:=function(RestrictedREQ, Q)
  local SEQ, MAP, nbVert, ListPositionTwo, NbVal2, i, ListNbRequiredVert, SomReq, SomReq2, pos, nb, SEQnew, MAPnew, GRAnew, iVert, jVert, LV, u, GRA, Cyc, idx, NewCycle;
  GRA:=RestrictedREQ[1];
  SEQ:=RestrictedREQ[2].SEQ;
  MAP:=RestrictedREQ[2].MAP;
  Cyc:=ShallowCopy(RestrictedREQ[3]);
  nbVert:=GRA.order;
  ListPositionTwo:=[];
  for i in [1..Length(SEQ)]
  do
    if SEQ[i]=2 then
      Add(ListPositionTwo, i);
    fi;
  od;
  NbVal2:=Length(ListPositionTwo);
  ListNbRequiredVert:=[];
  SomReq:=0;
  for i in [1..NbVal2]
  do
    pos:=ListPositionTwo[i];
    nb:=0;
    while(true)
    do
      if (NextIdx(Length(SEQ), pos) = ListPositionTwo[NextIdx(Length(ListPositionTwo), i)]) then
        break;
      fi;
      nb:=nb+1;
      pos:=NextIdx(Length(SEQ), pos);
    od;
    if (nb > Q-4) then
      return false;
    fi;
    Add(ListNbRequiredVert, Q-4-nb);
    SomReq:=SomReq+Q-4-nb;
  od;
  GRAnew:=NullGraph(Group(()), nbVert+NbVal2+SomReq);
  for iVert in [1..nbVert-1]
  do
    for jVert in [iVert+1..nbVert]
    do
      if IsEdge(GRA, [iVert, jVert]) then
        AddEdgeOrbit(GRAnew, [iVert, jVert]);
        AddEdgeOrbit(GRAnew, [jVert, iVert]);
      fi;
    od;
  od;
  for iVert in [1..NbVal2]
  do
    AddEdgeOrbit(GRAnew, [MAP[ListPositionTwo[iVert]], nbVert+iVert]);
    AddEdgeOrbit(GRAnew, [nbVert+iVert, MAP[ListPositionTwo[iVert]]]);
  od;
  SomReq2:=0;
  for iVert in [1..NbVal2]
  do
    LV:=[nbVert+iVert];
    for i in [1..ListNbRequiredVert[iVert]]
    do
      Add(LV, nbVert+NbVal2+SomReq2+i);
    od;
    Add(LV, nbVert+NextIdx(NbVal2, iVert));
    for u in [1..Length(LV)-1]
    do
      AddEdgeOrbit(GRAnew, [LV[u], LV[u+1]]);
      AddEdgeOrbit(GRAnew, [LV[u+1], LV[u]]);
    od;
    SomReq2:=SomReq2+ListNbRequiredVert[iVert];
  od;
  SEQnew:=[];
  MAPnew:=[];
  SomReq2:=0;
  for iVert in [1..NbVal2]
  do
    Add(SEQnew, 3);
    Add(MAPnew, nbVert+iVert);
    for i in [1..ListNbRequiredVert[iVert]]
    do
      Add(SEQnew, 2);
      Add(MAPnew, nbVert+NbVal2+SomReq2+i);
    od;
    SomReq2:=SomReq2+ListNbRequiredVert[iVert];
  od;
  #
  SomReq2:=0;
  for iVert in [1..NbVal2]
  do
    NewCycle:=[nbVert+iVert];
    for i in [1..ListNbRequiredVert[iVert]]
    do
      Add(NewCycle, nbVert+NbVal2+SomReq2+i);
    od;
    Add(NewCycle, nbVert+NextIdx(NbVal2, iVert));
    idx:=ListPositionTwo[NextIdx(NbVal2, iVert)];
    while(true)
    do
      Add(NewCycle, MAP[idx]);
      if idx=ListPositionTwo[iVert] then
        break;
      fi;
      idx:=PrevIdx(Length(SEQ), idx);
    od;
    Add(Cyc, Reversed(NewCycle));
    SomReq2:=SomReq2+ListNbRequiredVert[iVert];
  od;
  return [GRAnew, rec(SEQ:=SEQnew, MAP:=MAPnew), Cyc];
end;



BreakPlanGraphIntoPatchesAlongPath:=function(PlanGraph, Path)
  local VEF, FaceSet, Gra, i, j, INTS, TheConn, ListPatches, eCon, ListVert, iFac, GRA, pos, eFac, fFac, TheSEQ, NewFaceSet, ListEdgePath, TheMAP, TheEdge, NBInc;
  VEF:=PlanGraphToVEF(PlanGraph);
  ListEdgePath:=[];
  for i in [1..Length(Path)]
  do
    AddSet(ListEdgePath, Set([Path[i], Path[NextIdx(Length(Path), i)]]));
  od;
  FaceSet:=VEF[3];
  Gra:=NullGraph(Group(()), Length(FaceSet));
  for i in [1..Length(FaceSet)-1]
  do
    for j in [i+1..Length(FaceSet)]
    do
      INTS:=Intersection(Set(FaceSet[i]), Set(FaceSet[j]));
      if Length(INTS)=2 and (INTS in ListEdgePath)=false then
        AddEdgeOrbit(Gra, [i,j]);
        AddEdgeOrbit(Gra, [j,i]);
      fi;
    od;
  od;
  TheConn:=ConnectedComponents(Gra);
  ListPatches:=[];
  for eCon in TheConn
  do
    ListVert:=[];
    for iFac in eCon
    do
      ListVert:=Union(ListVert, FaceSet[iFac]);
    od;
    GRA:=NullGraph(Group(()), Length(ListVert));
    for i in [1..Length(ListVert)-1]
    do
      for j in [i+1..Length(ListVert)]
      do
        TheEdge:=Set([ListVert[i], ListVert[j]]);
        NBInc:=0;
        for iFac in eCon
        do
          if IsSubset(Set(FaceSet[iFac]), TheEdge)=true then
            NBInc:=NBInc+1;
          fi;
        od;
        if TheEdge in VEF[2] and NBInc>=1 then
          AddEdgeOrbit(GRA, [i,j]);
          AddEdgeOrbit(GRA, [j,i]);
        fi;
      od;
    od;
    TheSEQ:=[];
    TheMAP:=[];
    for i in [1..Length(Path)]
    do
      pos:=Position(ListVert, Path[i]);
      Add(TheSEQ, Length(Adjacency(GRA, pos)));
      Add(TheMAP, pos);
    od;
    NewFaceSet:=[];
    for iFac in eCon
    do
      eFac:=[];
      fFac:=FaceSet[iFac];
      for i in [1..Length(fFac)]
      do
        pos:=Position(ListVert, fFac[i]);
        Add(eFac, pos);
      od;
      Add(NewFaceSet, eFac);
    od;
    Add(ListPatches, [GRA, rec(SEQ:=TheSEQ, MAP:=TheMAP), NewFaceSet]);
  od;
  return ListPatches;
end;








MovementGroup:=function(n)
  local LIS1, LIS2;
  LIS1:=List([1..n], x->NextIdx(n, x));
  LIS2:=Reversed([1..n]);
  return Group([PermList(LIS1), PermList(LIS2)]);
end;



InvariantOfREQ:=function(REQ)
  local LIS;
  LIS:=REQ.SEQ;
  return Minimum(Orbit(MovementGroup(Length(LIS)), LIS, Permuted));
end;



BreakingUniquenessSeveralIsomorphFilling:=function(REQ)
  local LIS, Stab, ord1, ord2;
  LIS:=REQ.SEQ;
  Stab:=Stabilizer(MovementGroup(Length(LIS)), LIS, Permuted);
  ord1:=Order(Stab);
  ord2:=Order(AutGroupGraph(REQ.GRA));
  if ord1>ord2 then
    return true;
  else
    if ord1=ord2 then
      return false;
    else
      return "error !!!!!";
      return fail;
    fi;
  fi;
end;

PatchCriticalInvariant:=function(REQ)
  local v2, v3, i, f5, x;
  v2:=0;
  v3:=0;
  for i in [1..Length(REQ.SEQ)]
  do
    if REQ.SEQ[i]=2 then
      v2:=v2+1;
    else
      v3:=v3+1;
    fi;
  od;
  f5:=6+v3-v2;
  x:=10+v3-2*v2;
  return rec(f5:=f5, x:=x);
end;

ExtendedREQtoPlanGraph:=function(ExtendedREQ)
  local Edges, Faces, GRA, i, u, eBou;
  Edges:=[];
  GRA:=ExtendedREQ[1];
  for i in [1..GRA.order]
  do
    for u in Adjacency(GRA, i)
    do
      if u>i then
        Add(Edges, [i,u]);
      fi;
    od;
  od;
  Faces:=ExtendedREQ[3];
  for eBou in ExtendedREQ[2]
  do
    Add(Faces, eBou.MAP);
  od;
  return VEFtoPlanGraph([GRA.order, Edges, Faces]);
end;

