RubikCubeFormalism:=function(PL)
  local ListFaces, FuncCreateGenerators, List1, List2, List3, List4, GRP1, GRP2, GRP3, GRP4, phi12, phi23, phi34;
  ListFaces:=__FaceSet(PL);
  FuncCreateGenerators:=function(TheVect)
    local ListVertex, iFac, eFace, iDE, eDE, rDE, FuncFind, ListGenerators, LV1, LV2, LV3, LV4, LV5, LV6, LV7, fFace, eList, iVertex, i;
    # TheVect[1] for corners
    # TheVect[2] for edge side
    # TheVect[3] for edges
    # TheVect[4] for vertices
    ListVertex:=[];
    for iFac in [1..Length(ListFaces)]
    do
      eFace:=ListFaces[iFac];
      for iDE in [1..Length(eFace)]
      do
        eDE:=eFace[iDE];
        rDE:=ReverseDE(PL, eDE);
        if TheVect[1]=1 then
          AddSet(ListVertex, [eFace, eDE[1]]);
        fi;
        if TheVect[2]=1 then
          AddSet(ListVertex, [eFace, Set([eDE, rDE])]);
        fi;
        if TheVect[3]=1 then
          AddSet(ListVertex, Set([eDE, rDE]));
        fi;
        if TheVect[4]=1 then
          AddSet(ListVertex, eDE[1]);
        fi;
      od;
    od;
    FuncFind:=function(eDE)
      local eFac;
      for eFac in ListFaces
      do
        if Position(eFac, eDE)<>fail then
          return eFac;
        fi;
      od;
    end;
    ListGenerators:=[];
    for iFac in [1..Length(ListFaces)]
    do
      eFace:=ListFaces[iFac];
      LV1:=[];
      LV2:=[];
      LV3:=[];
      LV4:=[];
      LV5:=[];
      LV6:=[];
      LV7:=[];
      for iDE in [1..Length(eFace)]
      do
        eDE:=eFace[iDE];
        rDE:=ReverseDE(PL, eDE);
        fFace:=FuncFind(rDE);
        if TheVect[1]=1 then
          Add(LV1, Position(ListVertex, [eFace, eDE[1]]));
          Add(LV2, Position(ListVertex, [fFace, eDE[1]]));
          Add(LV3, Position(ListVertex, [fFace, rDE[1]]));
        fi;
        if TheVect[4]=1 then
          Add(LV4, Position(ListVertex, eDE[1]));
        fi;
        if TheVect[2]=1 then
          Add(LV5, Position(ListVertex, [eFace, Set([eDE, rDE])]));
          Add(LV6, Position(ListVertex, [fFace, Set([eDE, rDE])]));
        fi;
        if TheVect[3]=1 then
          Add(LV7, Position(ListVertex, Set([eDE, rDE]))  );
        fi;
      od;
      #
      eList:=[];
      for iVertex in [1..Length(ListVertex)]
      do
        Add(eList, iVertex);
      od;
      for i in [1..Length(eFace)]
      do
        if TheVect[1]=1 then
          eList[LV1[i]]:=LV1[NextIdx(Length(LV1), i)];
          eList[LV2[i]]:=LV2[NextIdx(Length(LV2), i)];
          eList[LV3[i]]:=LV3[NextIdx(Length(LV3), i)];
        fi;
        if TheVect[2]=1 then
          eList[LV5[i]]:=LV5[NextIdx(Length(LV5), i)];
          eList[LV6[i]]:=LV6[NextIdx(Length(LV6), i)];
        fi;
        if TheVect[3]=1 then
          eList[LV7[i]]:=LV7[NextIdx(Length(LV7), i)];
        fi;
        if TheVect[4]=1 then
          eList[LV4[i]]:=LV4[NextIdx(Length(LV4), i)];
        fi;
      od;
      Add(ListGenerators, PermList(eList));
    od;
    return ListGenerators;
  end;
  List1:=FuncCreateGenerators([1,1,0,0]);
  GRP1:=Group(List1);
  List2:=FuncCreateGenerators([1,0,1,0]);
  GRP2:=Group(List2);
  List3:=FuncCreateGenerators([1,0,0,0]);
  GRP3:=Group(List3);
  List4:=FuncCreateGenerators([0,0,0,1]);
  GRP4:=Group(List4);
  phi12:=GroupHomomorphismByImages(GRP1, GRP2, List1, List2);
  phi23:=GroupHomomorphismByImages(GRP2, GRP3, List2, List3);
  phi34:=GroupHomomorphismByImages(GRP3, GRP4, List3, List4);
  return rec(GRP1:=GRP1,
             GRP2:=GRP2,
             GRP3:=GRP3,
             GRP4:=GRP4,
             phi12:=phi12,
             phi23:=phi23,
             phi34:=phi34);
end;


RubikCubeMedialFormalism:=function(PLori)
  local ListGensDE, ListGensEdge, EdgeSet, nbEdge, nbDE, VEFori, eVert, hDE, ListDE, i, eListDE, rDE, eListEdge, iNext, GRP1_de, GRP2_edge, phi12, pos1, pos2, eEdge1, eEdge2, ListDErev, SetSet_Face, SetSet_Vert, ListSet_Face, ListSet_Vert, eList, eFace;
  ListGensDE:=[];
  ListGensEdge:=[];
  nbDE:=PLori.nbP;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  EdgeSet:=VEFori.EdgeSet;
  nbEdge:=Length(EdgeSet);
  for eVert in VEFori.VertSet
  do
    hDE:=eVert[1];
    ListDE:=[];
    ListDErev:=[];
    for i in [1..Length(eVert)]
    do
      hDE:=OnPoints(hDE, PLori.next);
      Add(ListDE, hDE);
      rDE:=OnPoints(hDE, PLori.invers);
      Add(ListDErev, rDE);
    od;
    #
    eListDE:=[];
    for i in [1..nbDE]
    do
      eListDE[i]:=i;
    od;
    for i in [1..Length(eVert)]
    do
      iNext:=NextIdx(Length(eVert), i);
      eListDE[ListDE[i]]:=ListDE[iNext];
      eListDE[ListDErev[i]]:=ListDErev[iNext];
    od;
    Add(ListGensDE, PermList(eListDE));
    #
    eListEdge:=[];
    for i in [1..nbEdge]
    do
      eListEdge[i]:=i;
    od;
    for i in [1..Length(eVert)]
    do
      iNext:=NextIdx(Length(eVert), i);
      eEdge1:=Set([ListDE[i], ListDErev[i]]);
      eEdge2:=Set([ListDE[iNext], ListDErev[iNext]]);
      pos1:=Position(EdgeSet, eEdge1);
      pos2:=Position(EdgeSet, eEdge2);
      eListEdge[pos1]:=pos2;
    od;
    Add(ListGensEdge, PermList(eListEdge));
  od;
  ListSet_Face:=[];
  for eFace in VEFori.FaceSet
  do
    eList:=List(eFace, x->VEFori.ListOriginEdge[x]);
    Add(ListSet_Face, Set(eList));
  od;
  SetSet_Face:=Set(ListSet_Face);
  ListSet_Vert:=[];
  for eVert in VEFori.EdgeSet
  do
    eList:=List(eVert, x->VEFori.ListOriginEdge[x]);
    Add(ListSet_Vert, Set(eList));
  od;
  SetSet_Vert:=Set(ListSet_Vert);
  GRP1_de:=Group(ListGensDE);
  GRP2_edge:=Group(ListGensEdge);
  phi12:=GroupHomomorphismByImages(GRP1_de, GRP2_edge, ListGensDE, ListGensEdge);
  return rec(GRP1_de:=GRP1_de,
             GRP2_edge:=GRP2_edge,
             SetSet_Face:=SetSet_Face,
             SetSet_Vert:=SetSet_Vert,
             phi12:=phi12);
end;
