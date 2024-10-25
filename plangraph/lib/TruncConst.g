Get3valentGraphsWith2gons:=function(nbV, ListFacePair)
  local ePair2, ePair, MaxFaceSize, p2, GetGraphs, IsCorrect, LPLfinal, nbVert, res, LPLpart, nbV_search, FuncInsert, ePLori, fPLori;
  ePair2:="unset";
  for ePair in ListFacePair
  do
    if ePair[1]=2 then
      ePair2:=ePair;
    fi;
  od;
  MaxFaceSize:=Maximum(List(ListFacePair, x->x[1]));
  if ePair2="unset" then
    Error("No point of calling Get3valentGraphWith2gons");
  fi;
  p2:=ePair2[2];
  #
  GetGraphs:=function(nbVert)
    local ListFaceDesc, LPL, ePL, PLori, PreLPL;
    if nbVert=2 then
      return [Mbundle(3)];
    fi;
    ListFaceDesc:=[];
    for ePair in ListFacePair
    do
      if ePair[1]<>2 then
        Add(ListFaceDesc, [ePair[1], rec(eNature:="unspec")]);
      fi;
    od;
    LPL:=[];
    Print("nbVert=", nbVert, " ListFaceDesc=", ListFaceDesc, "\n");
    PreLPL:=GetList3valentPlaneGraphSpecifiedFaces(nbVert, ListFaceDesc);
    Print("|PreLPL|=", Length(PreLPL), "\n");
    for ePL in PreLPL
    do
      PLori:=PlanGraphToPlanGraphOriented(ePL);
      Add(LPL, PLori);
    od;
    return LPL;
  end;
  nbV_search:=nbV - 2*p2;
  IsCorrect:=function(ePLori)
    local VEFori, ListColl, eColl;
    VEFori:=PlanGraphOrientedToVEF(ePLori);
    ListColl:=Collected(List(VEFori.FaceSet, Length));
    for eColl in ListColl
    do
      if Position(ListFacePair, eColl)=fail then
        return false;
      fi;
    od;
    return true;
  end;
  LPLfinal:=[];
  FuncInsert:=function(ePLori)
    local fPLori;
    for fPLori in LPLfinal
    do
      if IsIsomorphicPlanGraphOriented(fPLori, ePLori)=true then
        return;
      fi;
    od;
    Add(LPLfinal, ePLori);
    Print("|LPLfinal|=", Length(LPLfinal), "\n");
  end;
  Print("nbV_search=", nbV_search, "\n");
  for nbVert in [2..nbV_search]
  do
    res:=nbVert mod 2;
    if res=0 then
      Print("nbVert=", nbVert, "\n");
      for ePLori in GetGraphs(nbVert)
      do
        LPLpart:=123_GetGeneratedGraphs(ePLori, nbV, MaxFaceSize);
        for fPLori in LPLpart
        do
          if IsCorrect(fPLori) then
            FuncInsert(fPLori);
          fi;
        od;
      od;
    fi;
  od;
  return LPLfinal;
end;



GetKvalentGraphs:=function(nbV, k, ListFacePair)
  local nbVtot, ListFaceSize, iV, ePair, eVal, ListColl, LPLfinal, FuncInsert, IsIndependentSubset, eSet, eSetB, VEFori, ListFaceCand, eDE, ePLori, GRA, rDE, iFace, jFace, iFaceCand, jFaceCand, eRecINV, nbFaceCand, nbFace;
  nbVtot:=k*nbV;
  ListFaceSize:=[];
  for iV in [1..nbV]
  do
    Add(ListFaceSize, k);
  od;
  for ePair in ListFacePair
  do
    for eVal in [1..ePair[2]]
    do
      Add(ListFaceSize, 2*ePair[1]);
    od;
  od;
  ListColl:=Collected(ListFaceSize);
  LPLfinal:=[];
  FuncInsert:=function(ePLori)
    local fPLori;
    for fPLori in LPLfinal
    do
      if IsIsomorphicPlanGraphOriented(fPLori, ePLori)=true then
        return;
      fi;
    od;
    Add(LPLfinal, ePLori);
  end;
  Print("nbVtot=", nbVtot, " ListColl=", ListColl, "\n");
  for ePLori in Get3valentGraphsWith2gons(nbVtot, ListColl)
  do
    VEFori:=PlanGraphOrientedToVEF(ePLori);
    nbFace:=Length(VEFori.FaceSet);
    ListFaceCand:=[];
    for iFace in [1..nbFace]
    do
      if Length(VEFori.FaceSet[iFace])=k then
        Add(ListFaceCand, iFace);
      fi;
    od;
    nbFaceCand:=Length(ListFaceCand);
    GRA:=NullGraph(Group(()), nbFaceCand);
    for iFaceCand in [1..nbFaceCand]
    do
      iFace:=ListFaceCand[iFaceCand];
      for eDE in VEFori.FaceSet[iFace]
      do
        rDE:=OnPoints(eDE, ePLori.invers);
        jFace:=VEFori.ListFaceOrigin[rDE];
        jFaceCand:=Position(ListFaceCand, jFace);
        if jFaceCand<>fail then
          AddEdgeOrbit(GRA, [iFaceCand, jFaceCand]);
          AddEdgeOrbit(GRA, [jFaceCand, iFaceCand]);
        fi;
      od;
    od;
    IsIndependentSubset:=function(eSet)
      local i, j, len;
      len:=Length(eSet);
      for i in [1..len-1]
      do
        for j in [i+1..len]
        do
          if Position(Adjacency(GRA, i), j)<>fail then
            return false;
          fi;
        od;
      od;
      return true;
    end;
    for eSet in Combinations([1..nbFaceCand], nbV)
    do
      if IsIndependentSubset(eSet) then
        eSetB:=ListFaceCand{eSet};
        eRecINV:=InverseTruncationOrientedSelect(ePLori, VEFori, eSetB);
        if eRecINV.success=true then
          FuncInsert(eRecINV.PLori);
        fi;
      fi;
    od;
  od;
  return LPLfinal;
end;
