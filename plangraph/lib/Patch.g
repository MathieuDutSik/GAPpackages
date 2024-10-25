
# ListPatch is a series of patch (3-valent). Format of a patch is PlanGraph with 
# adjacent non-existent vertex marked as a "R"
# ListMerge is a list of vertices to be merged
MergePatch:=function(ListPatch, ListMerge)
  local ListVert, ListMapping, ePatch, iVert, testM, MaxNb, NewPatch, ListPair, ePair, fPair, eMerge, Ladj, u;
  ListVert:=[];
  ListMapping:=[];
  for ePatch in ListPatch
  do
    for iVert in [1..Length(ePatch)]
    do
      if ePatch[iVert]<>[] then
        testM:=0;
        for eMerge in ListMerge
        do
          if iVert in eMerge then
            testM:=1;
            ListMapping[iVert]:=eMerge[1];
            AddSet(ListVert, eMerge[1]);
          fi;
        od;
        if testM=0 then
          AddSet(ListVert, iVert);
        fi;
      fi;
    od;
  od;
  #
  MaxNb:=Maximum(ListVert);
  NewPatch:=[];
  for iVert in [1..MaxNb]
  do
    if iVert in ListVert then
      ListPair:=[];
      for ePatch in ListPatch
      do
        Ladj:=ePatch[iVert];
        if Ladj<>[] then
          for u in [1..Length(Ladj)]
          do
            ePair:=[Ladj[u], Ladj[NextIdx(Length(Ladj), u)]];
            fPair:=[];
            if ePair[1]="R" then
              fPair[1]:="R";
            else
              fPair[1]:=ListMapping[ePair[1]];
            fi;
            if ePair[2]="R" then
              fPair[2]:="R";
            else
              fPair[2]:=ListMapping[ePair[2]];
            fi;
            AddSet(ListPair, fPair);
          od;
        fi;
      od;
      for ePair in ListPair
      do
        if ePair[1]="R" then
          for fPair in Difference(ListPair, ePair)
          do
            if fPair[2]=ePair[2] then
              ListPair:=Difference(ListPair, ePair);
            fi;
          od;
        fi;
        if ePair[2]="R" then
          for fPair in Difference(ListPair, ePair)
          do
            if fPair[1]=ePair[1] then
              ListPair:=Difference(ListPair, ePair);
            fi;
          od;
        fi;
      od;
      NewPatch[iVert]:=CreateOrderedListAdj(ListPair);
    else
      NewPatch[iVert]:=[];
    fi;
  od;
  return NewPatch;
end;






ShiftPatch:=function(Patch, ShiftIndex)
  local NewPatch, iVert, Radj, Sadj, iDx, jV;
  NewPatch:=[];
  for iDx in [1..ShiftIndex]
  do
    NewPatch[iDx]:=[];
  od;
  for iVert in [1..Length(Patch)]
  do
    Radj:=Patch[iVert];
    Sadj:=[];
    for jV in [1..Length(Radj)]
    do
      if Radj[jV]="R" then
        Sadj[jV]:="R";
      else
        Sadj[jV]:=Radj[jV]+ShiftIndex;
      fi;
    od;
    NewPatch[iVert+ShiftIndex]:=Sadj;
  od;
  return NewPatch;
end;


#
#
# take a patch and complete it with hexagons until no "R" exist
CompletePatch:=function(Patch)
  local PatchWork, testFinish, iVert, Ladj, VertexAdd, PosAdd, DEnext, DEprev, iV;
  PatchWork:=Patch;
  testFinish:=0;
  repeat
    testFinish:=1;
    for iVert in [1..Length(PatchWork)]
    do
      Ladj:=PatchWork[iVert];
      if Ladj<>[] then
        for iV in [1..Length(Ladj)]
        do
          if Ladj[iV]="R" then
            testFinish:=0;
            VertexAdd:=iVert;
            PosAdd:=iV;
          fi;
        od;
      fi;
    od;
    if testFinish=0 then
      DEnext:=[VertexAdd, NextIdx(Length(PatchWork[VertexAdd]), PosAdd)];
      DEprev:=[VertexAdd, PrevIdx(Length(PatchWork[VertexAdd]), PosAdd)];
    fi;
  until testFinish=0;
  return Renormalisation(PatchWork);
end;

