
#
#
# this procedure change fuleren to another fulerene
LeapFrog:=function(PlanGraph)
  local VEF, EdgeSet, FaceSet, NewVertexSet, NewPlanGraph, eEdge, eFace, nbNew, iVert, jVert, a, b, aprev, bnext, Pos1, Pos2, eEdge1, eEdge2, LADJ, LEN;
  VEF:=PlanGraphToVEF(PlanGraph);
  EdgeSet:=VEF[2];
  FaceSet:=VEF[3];
  # the new set of vertices
  NewVertexSet:=[];
  for eEdge in EdgeSet
  do
    for eFace in FaceSet
    do
      if Length(Intersection(eEdge, eFace))=2 then
        Add(NewVertexSet, [eEdge, eFace]);
      fi;
    od;
  od;
  nbNew:=Length(NewVertexSet);
  # the clockwise adjacencies
  NewPlanGraph:=[];
  for iVert in [1..nbNew]
  do
    eEdge:=NewVertexSet[iVert][1];
    eFace:=NewVertexSet[iVert][2];
    LEN:=Length(eFace);
    LADJ:=ShallowCopy([]);
    for jVert in Difference([1..nbNew],[iVert])
    do
      if NewVertexSet[jVert][1]=eEdge then
        LADJ[1]:=jVert;
      fi;
    od;
    a:=eEdge[1];
    b:=eEdge[2];
    Pos1:=Position(eFace,a);
    Pos2:=Position(eFace,b);
    if Pos2<>NextIdx(LEN,Pos1) then
      a:=eEdge[2];
      b:=eEdge[1];
      Pos1:=Position(eFace,a);
      Pos2:=Position(eFace,b);
    fi;
    bnext:=eFace[NextIdx(LEN, Pos2)];
    aprev:=eFace[PrevIdx(LEN, Pos1)];
    eEdge1:=Set([b,bnext]);
    eEdge2:=Set([a,aprev]);
    LADJ[2]:=Position(NewVertexSet, [eEdge1, eFace]);
    LADJ[3]:=Position(NewVertexSet, [eEdge2, eFace]);
    NewPlanGraph[iVert]:=LADJ;
  od;
  return rec(VertexSet:=NewVertexSet, PlanGraph:=NewPlanGraph);
end;






#
#
# some transformations procedure for graphs


#
#
# take a planar graph and define the medial graph to be the set of edges 
# with two edges adjacent if they share a vertex and if they belong to 
# the same face.
MedialGraph:=function(PlanGraph)
  local VEF, EdgeSet, PlanGraphNew, iEdge, jEdge, a, b, A1, A2, B1, B2, DEA1, DEA2, DEB1, DEB2;
  VEF:=PlanGraphToVEFsecond(PlanGraph);
  EdgeSet:=VEF[2];
  PlanGraphNew:=[];
  for iEdge in [1..Length(EdgeSet)]
  do
    a:=EdgeSet[iEdge][1];
    b:=EdgeSet[iEdge][2];
    DEA1:=NextDE(PlanGraph, a);
    DEA2:=PrevDE(PlanGraph, a);
    DEB1:=NextDE(PlanGraph, b);
    DEB2:=PrevDE(PlanGraph, b);
    for jEdge in [1..Length(EdgeSet)]
    do
      if DEA1 in EdgeSet[jEdge] then
        A1:=jEdge;
      fi;
      if DEA2 in EdgeSet[jEdge] then
        A2:=jEdge;
      fi;
      if DEB1 in EdgeSet[jEdge] then
        B1:=jEdge;
      fi;
      if DEB2 in EdgeSet[jEdge] then
        B2:=jEdge;
      fi;
    od;
    PlanGraphNew[iEdge]:=[A1, B2, B1, A2];
  od;
  return rec(VertexSet:=EdgeSet, PlanGraph:=PlanGraphNew);
end;


MedialGraphOriented:=function(PLori)
  local eNext, ePrev, VEFori, nbEdge, NewNbDE, NewListDE, iEdge, eEdge, eDE1, eDE2, eDE1next, eDE2next, eDE1prev, eDE2prev, posDE1next, posDE1prev, posDE2next, posDE2prev, eListNext, eListInvers, eNewDE, eDE, corDE, pos, NewDE1next, NewDE1prev, NewDE2next, NewDE2prev, ePermInv, ePermNext, stat;
  eNext:=PLori.next;
  ePrev:=Inverse(eNext);
  VEFori:=PlanGraphOrientedToVEF(PLori);
  nbEdge:=Length(VEFori.EdgeSet);
  NewNbDE:=4*nbEdge;
  eListNext:=ListWithIdenticalEntries(NewNbDE,0);
  NewListDE:=[];
  for iEdge in [1..nbEdge]
  do
    eEdge:=VEFori.EdgeSet[iEdge];
    eDE1:=eEdge[1];
    eDE2:=eEdge[2];
    eDE1next:=OnPoints(eDE1, eNext);
    eDE2next:=OnPoints(eDE2, eNext);
    eDE1prev:=OnPoints(eDE1, ePrev);
    eDE2prev:=OnPoints(eDE2, ePrev);
    NewDE1next:=rec(iEdge:=iEdge, eDE:=eDE1, corDE:=eDE1next, stat:=1);
    NewDE2next:=rec(iEdge:=iEdge, eDE:=eDE2, corDE:=eDE2next, stat:=1);
    NewDE1prev:=rec(iEdge:=iEdge, eDE:=eDE1, corDE:=eDE1prev, stat:=-1);
    NewDE2prev:=rec(iEdge:=iEdge, eDE:=eDE2, corDE:=eDE2prev, stat:=-1);
    Append(NewListDE, [NewDE1prev, NewDE2next, NewDE2prev, NewDE1next]);
    posDE1next:=Position(NewListDE, NewDE1next);
    posDE1prev:=Position(NewListDE, NewDE1prev);
    posDE2next:=Position(NewListDE, NewDE2next);
    posDE2prev:=Position(NewListDE, NewDE2prev);
    eListNext[posDE1prev]:=posDE2next;
    eListNext[posDE2next]:=posDE2prev;
    eListNext[posDE2prev]:=posDE1next;
    eListNext[posDE1next]:=posDE1prev;
  od;
  eListInvers:=[];
  for eNewDE in NewListDE
  do
    eDE:=eNewDE.eDE;
    corDE:=eNewDE.corDE;
    stat:=eNewDE.stat;
    pos:=First([1..NewNbDE], x->NewListDE[x].eDE=corDE and NewListDE[x].corDE=eDE and NewListDE[x].stat=-stat);
    Add(eListInvers, pos);
  od;
  ePermInv:=PermList(eListInvers);
  ePermNext:=PermList(eListNext);
  if ePermInv=fail or ePermNext=fail then
    Error("Need to debug the construction");
  fi;
  return rec(invers:=ePermInv, next:=ePermNext, nbP:=NewNbDE);
end;


# Wythoff construction for oriented maps
# For subset {0} : PL
# For subset {0,1} : Tr(PL)
# For subset {1} : Med(PL)
# For subset {2} : Dual(PL)
# For subset {1,2} : Tr(Dual(PL))
# For subset {0,2} : Med(Med(PL))
# For subset {0,1,2} : Tr(Med(PL))
#
GetWythoffMaps:=function(PLori)
  local ListRet;
  ListRet:=[];
  Add(ListRet, rec(eSymb:=[0], PLori:=PLori));
  Add(ListRet, rec(eSymb:=[0,1], PLori:=TruncationOriented(PLori)));
  Add(ListRet, rec(eSymb:=[1], PLori:=MedialGraphOriented(PLori)));
  Add(ListRet, rec(eSymb:=[2], PLori:=DualGraphOriented(PLori)));
  Add(ListRet, rec(eSymb:=[1,2], PLori:=TruncationOriented(DualGraphOriented(PLori))));
  Add(ListRet, rec(eSymb:=[0,2], PLori:=MedialGraphOriented(MedialGraphOriented(PLori))));
  Add(ListRet, rec(eSymb:=[0,1,2], PLori:=TruncationOriented(MedialGraphOriented(PLori))));
  return ListRet;
end;




OneSubdivisionRelatedToMedial:=function(PlanGraph)
  local VertexSet, VEF, nbV, nbE, nbF, NewPlanGraph, iVert, iEdge, iFac, Ladj, eEdge, eDE1, eDE2, eDE3, eDE4, eEdge1, eEdge2, eEdge3, eEdge4, pos1, pos2, eDE, u, eFac, rDE;
  VertexSet:=[];
  VEF:=PlanGraphToVEFsecond(PlanGraph);
  nbV:=VEF[1];
  nbE:=Length(VEF[2]);
  nbF:=Length(VEF[3]);
  for iVert in [1..VEF[1]]
  do
    Add(VertexSet, iVert);
  od;
  for iEdge in [1..Length(VEF[2])]
  do
    Add(VertexSet, VEF[2][iEdge] );
  od;
  for iFac in [1..Length(VEF[3])]
  do
    Add(VertexSet, VEF[3][iFac]);
  od;
  NewPlanGraph:=[];
  for iVert in [1..nbV]
  do
    Ladj:=[];
    for u in [1..Length(PlanGraph[iVert])]
    do
      eDE:=[iVert, u];
      rDE:=ReverseDE(PlanGraph, eDE);
      eEdge:=Set([eDE, rDE]);
      Add(Ladj, Position(VertexSet, eEdge));
    od;
    Add(NewPlanGraph, Ladj);
  od;
  for iEdge in [1..nbE]
  do
    eEdge:=VEF[2][iEdge];
    for iFac in [1..Length(VEF[3])]
    do
      if Position(VEF[3][iFac], eEdge[1])<>fail then
        pos1:=nbV+nbE+iFac;
      fi;
      if Position(VEF[3][iFac], eEdge[2])<>fail then
        pos2:=nbV+nbE+iFac;
      fi;
    od;
    eDE1:=NextDE(PlanGraph, eEdge[1]);
    eDE2:=PrevDE(PlanGraph, eEdge[1]);
    eDE3:=NextDE(PlanGraph, eEdge[2]);
    eDE4:=PrevDE(PlanGraph, eEdge[2]);
    eEdge1:=Set([eDE1, ReverseDE(PlanGraph, eDE1)]);
    eEdge2:=Set([eDE2, ReverseDE(PlanGraph, eDE2)]);
    eEdge3:=Set([eDE3, ReverseDE(PlanGraph, eDE3)]);
    eEdge4:=Set([eDE4, ReverseDE(PlanGraph, eDE4)]);
    Ladj:=[eEdge[1][1], Position(VertexSet, eEdge2), pos2, Position(VertexSet, eEdge3), eEdge[2][1], Position(VertexSet, eEdge4), pos1, Position(VertexSet, eEdge1)];
    Add(NewPlanGraph, Ladj);
  od;
  for iFac in [1..nbF]
  do
    eFac:=VEF[3][iFac];
    Ladj:=[];
    for u in [1..Length(eFac)]
    do
      eDE:=eFac[u];
      eEdge:=Set([eDE, ReverseDE(PlanGraph, eDE)]);
      Add(Ladj, Position(VertexSet, eEdge));
    od;
    Add(NewPlanGraph, Ladj);
  od;
  return NewPlanGraph;
end;









MedialGraphSecond:=function(PlanGraph)
  local nbE, EdgeSET, ListTot, z, eEdge, iEdge, jEdge, fEdge,  DE1, DE2, DE3, DE4, pos1, pos2, pos3, pos4, NewPlanGraph;
  nbE:=Length(PlanGraph.Struct);
  EdgeSET:=[];
  ListTot:=[1..nbE];
  while (Length(ListTot)>0)
  do
    z:=ListTot[1];
    eEdge:=[z, PlanGraph.Struct[z][1]];
    ListTot:=Difference(ListTot, Set(eEdge));
    AddSet(EdgeSET, eEdge);
  od;
  NewPlanGraph:=[];
  for iEdge in [1..Length(EdgeSET)]
  do
    eEdge:=EdgeSET[iEdge];
    DE1:=PlanGraph.Struct[eEdge[1]][2];
    DE2:=PlanGraph.Struct[eEdge[1]][3];
    DE3:=PlanGraph.Struct[eEdge[2]][2];
    DE4:=PlanGraph.Struct[eEdge[2]][3];
    for jEdge in [1..Length(EdgeSET)]
    do
      fEdge:=EdgeSET[jEdge];
      if DE1 in fEdge then
        pos1:=jEdge;
      fi;
      if DE2 in fEdge then
        pos2:=jEdge;
      fi;
      if DE3 in fEdge then
        pos3:=jEdge;
      fi;
      if DE4 in fEdge then
        pos4:=jEdge;
      fi;
    od;
    NewPlanGraph[iEdge]:=[pos1, pos2, pos3, pos4];
  od;
  return NewPlanGraph;
end;





TruncatedGraph:=function(PlanGraph)
  local H, PlanGraphNew, iOrEdge, OrEdge, h1, h2, h3, pos1, pos2, pos3;
  H:=ListDirectedEdges(PlanGraph);
  PlanGraphNew:=[];
  for iOrEdge in [1..Length(H)]
  do
    OrEdge:=H[iOrEdge];  
    h1:=NextDE(PlanGraph, OrEdge);
    h2:=ReverseDE(PlanGraph, OrEdge);
    h3:=PrevDE(PlanGraph, OrEdge);
    pos1:=Position(H, h1);
    pos2:=Position(H, h2);
    pos3:=Position(H, h3);
    PlanGraphNew[iOrEdge]:=[pos1, pos2, pos3];
  od;
  return PlanGraphNew;
end;

MedialToOriginalsOriented:=function(PLori)
  local eInv, eNext, ePrev, eElt, GRPface, Ofac, nbFac, FindFace, GRAadj, ListVert1, ListVert2, TheBipartition, ListPLori, ListImageInvers, ListImageNext, iDE, jDE, kDE, ePos, fPos, eNewOri, jFac, ListListVert, eListVert, ListDE, iVal, eDE, nbP, FindPos, eRec, jElt, iFac, iElt;
  eInv:=PLori.invers;
  eNext:=PLori.next;
  ePrev:=eNext^(-1);
  if eNext^4<>() then
    Print("The input graph is not 4-valent,\n");
    Print("This is an error\n");
    Print(NullMat(5)); 
  fi;
  eElt:=eNext*eInv;
  GRPface:=Group([eElt]);
  Ofac:=Orbits(GRPface, [1..PLori.nbP], OnPoints);
  nbFac:=Length(Ofac);
  FindFace:=function(iElt)
    local iFac;
    for iFac in [1..nbFac]
    do
      if Position(Ofac[iFac], iElt)<>fail then
        return iFac;
      fi;
    od;
    Print(NullMat(5));
  end;
  GRAadj:=NullGraph(Group(()), nbFac);
  for iFac in [1..Length(Ofac)]
  do
    for iElt in Ofac[iFac]
    do
      jElt:=OnPoints(iElt, eInv);
      jFac:=FindFace(jElt);
      AddEdgeOrbit(GRAadj, [iFac, jFac]);
    od;
  od;
  TheBipartition:=GetBipartition(GRAadj);
  ListVert1:=Filtered([1..nbFac], x->TheBipartition[x]=1);
  ListVert2:=Filtered([1..nbFac], x->TheBipartition[x]=2);
  ListListVert:=[ListVert1, ListVert2];
  ListPLori:=[];
  for eListVert in ListListVert
  do
    ListDE:=[];
    for iFac in eListVert
    do
      for iVal in Ofac[iFac]
      do
        eRec:=rec(iFac:=iFac, iDE:=iVal);
        Add(ListDE, eRec);
      od;
    od;
    nbP:=Length(ListDE);
    FindPos:=function(iDE)
      return First([1..nbP], x->ListDE[x].iDE=iDE);
    end;
    ListImageInvers:=[];
    ListImageNext:=[];
    for eDE in ListDE
    do
      iDE:=eDE.iDE;
      jDE:=OnPoints(iDE, eNext*eNext);
      ePos:=FindPos(jDE);
      Add(ListImageInvers, ePos);
      kDE:=OnPoints(iDE, eNext*eInv);
      fPos:=FindPos(kDE);
      Add(ListImageNext, fPos);
    od;
    eNewOri:=rec(invers:=PermList(ListImageInvers), next:=PermList(ListImageNext), nbP:=Length(ListDE));
    Add(ListPLori, eNewOri);
  od;
  return ListPLori;
end;


#
#
# This functions takes as argument a medial graph and returns the
# two graphs constructed from chess construction
MedialToOriginals:=function(PlanGraph)
  local ListFaces, Treated, Black, White, nbTreated, nbFac, iFac, eFac, fFac, PlanGraphWhite, PlanGraphBlack, LADJ, iVert, jVert, fDE, u, eDE, nbVert;
  ListFaces:=PlanGraphToVEFsecond(PlanGraph)[3];
  Treated:=ListWithIdenticalEntries(Length(ListFaces),0);
  nbVert:=Length(PlanGraph);
  for iVert in [1..nbVert]
  do
    if Length(PlanGraph[iVert])<>4 then
      Print("The vertex degree is not always 4, please correct\n");
      Print(NullMat(5));
    fi;
  od;
  #
  Black:=[];
  White:=[];
  Black[1]:=ListFaces[1];
  Treated[1]:=1;
  nbTreated:=1;
  nbFac:=Length(ListFaces);
  Treated[1]:=1;
  while (nbTreated<nbFac)
  do
    for iFac in [1..Length(ListFaces)]
    do
      if Treated[iFac]=0 then
        eFac:=[];
        for eDE in ListFaces[iFac]
        do
          AddSet(eFac, ReverseDE(PlanGraph, eDE));
        od;
        for fFac in Black
        do
          if Intersection(eFac,fFac)<>[] then
            AddSet(White,ListFaces[iFac]);
            Treated[iFac]:=1;
            nbTreated:=nbTreated+1;
          fi;
        od;
        for fFac in White
        do
          if Intersection(eFac,fFac)<>[] then
            AddSet(Black,ListFaces[iFac]);
            Treated[iFac]:=1;
            nbTreated:=nbTreated+1;
          fi;
        od;
      fi;
    od;
  od;
  PlanGraphBlack:=[];
  for iVert in [1..Length(Black)]
  do
    LADJ:=[];
    for jVert in [1..Length(Black[iVert])]
    do
      fDE:=NextDE(PlanGraph, NextDE(PlanGraph, Black[iVert][jVert]));
      for u in [1..Length(Black)]
      do
        if fDE in Black[u] then
          Add(LADJ, u);
        fi;
      od;
    od;
    PlanGraphBlack[iVert]:=LADJ;
  od;
  PlanGraphWhite:=[];
  for iVert in [1..Length(White)]
  do
    LADJ:=[];
    for jVert in [1..Length(White[iVert])]
    do
      fDE:=NextDE(PlanGraph, NextDE(PlanGraph, White[iVert][jVert]));
      for u in [1..Length(White)]
      do
        if fDE in White[u] then
          Add(LADJ, u);
        fi;
      od;
    od;
    PlanGraphWhite[iVert]:=LADJ;
  od;
  return [rec(PlanGraph:=PlanGraphBlack, Faces:=Black), rec(PlanGraph:=PlanGraphWhite, Faces:=White)];
end;


