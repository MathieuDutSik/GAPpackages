SliceNumberOneSection:=function(EXT, ListInc)
  local ListEqua, ListValues, eEXT;
  ListEqua:=NullspaceMat(TransposedMat(EXT{ListInc}));
  ListValues:=[];
  for eEXT in EXT
  do
    Add(ListValues, List(ListEqua, x->eEXT*x));
  od;
  return Length(Set(ListValues));
end;



RankedListPlaneOrbit:=function(EXT, GroupEXT, AskedRank)
  local rnk, ord, nbV, O2, ListCand, i, RPL, eCand, Stab, O, eO, fCand, ListEqua, vZero, gCand;
  ord:=Order(GroupEXT);
  nbV:=Length(EXT);
  O2:=Orbits(GroupEXT, [1..nbV], OnPoints);
  ListCand:=List(O2, x->[x[1]]);
  Print("nbCand=", Length(ListCand), "\n");
  for i in [1..AskedRank]
  do
    RPL:=OrbitGroupFormalism(GroupEXT, "/irrelevant", false);
    for eCand in ListCand
    do
      Stab:=Stabilizer(GroupEXT, eCand, OnSets);
      O:=Orbits(Stab, Difference([1..nbV], eCand), OnPoints);
      for eO in O
      do
        fCand:=Union(eCand, [eO[1]]);
        ListEqua:=NullspaceMat(TransposedMat(EXT{fCand}));
        vZero:=ListWithIdenticalEntries(Length(ListEqua), 0);
        gCand:=Filtered([1..nbV], x->List(ListEqua, y->y*EXT[x])=vZero);
        RPL.FuncInsert(gCand);
      od;
    od;
    ListCand:=RPL.FuncListOrbitIncidence();
    Print("nbCand=", Length(ListCand), "  rnk=", RankMat(EXT{ListCand[1]}), "\n");
  od;
  return ListCand;
end;




RandomSubspace:=function(EXT, AskedRank)
  local nbV, TheCand, i, TheDiff, uVert, fCand, ListEqua, vZero;
  nbV:=Length(EXT);
  TheCand:=[Random(Length(EXT))];
  for i in [1..AskedRank]
  do
    TheDiff:=Difference([1..nbV], TheCand);
    uVert:=Random(TheDiff);
    fCand:=Union(TheCand, [uVert]);
    ListEqua:=NullspaceMat(TransposedMat(EXT{fCand}));
    vZero:=ListWithIdenticalEntries(Length(ListEqua), 0);
    TheCand:=Filtered([1..nbV], x->List(ListEqua, y->y*EXT[x])=vZero);
  od;
  return TheCand;
end;





SliceNumber:=function(EXT, GroupEXT)
  local rnk, FAC, ListMatch2, ListMatch3, eFac, eInc, slc, AskedRank, i, rSub, ListCand, ListSliceNr, MinSlice, ListSelect;
  rnk:=RankMat(EXT);
  Print("Total rank=", rnk, "\n");
  FAC:=DualDescription(EXT);
  ListMatch2:=[];
  ListMatch3:=[];
  for eFac in FAC
  do
    eInc:=List([1..Length(EXT)], x->EXT[x]*eFac=0);
    slc:=SliceNumberOneSection(EXT, eInc);
    if slc=2 then
      Add(ListMatch2, eInc);
    fi;
    if slc=3 then
      Add(ListMatch3, eInc);
    fi;
  od;
  if Length(ListMatch2)<>0 then
    return rec(ListInc:=ListMatch2, SliceNr:=2, TotalList:=true);
  fi;
  if Length(ListMatch3)<>0 then
    return rec(ListInc:=ListMatch3, SliceNr:=3, TotalList:=false);
  fi;
  AskedRank:=rnk-2;
  for i in [1..1000]
  do
    rSub:=RandomSubspace(EXT, AskedRank);
    slc:=SliceNumberOneSection(EXT, rSub);
    if slc=3 then
      return rec(ListInc:=[rSub], SliceNr:=3, TotalList:=false);
    fi;
  od;
  ListCand:=RankedListPlaneOrbit(EXT, GroupEXT, AskedRank);
  ListSliceNr:=List(ListCand, x->SliceNumberOneSection(EXT, x));
  MinSlice:=Minimum(ListSliceNr);
  ListSelect:=Filtered([1..Length(ListSliceNr)], x->ListSliceNr[x]=MinSlice);
  return rec(ListInc:=ListCand{ListSelect}, SliceNr:=MinSlice, TotalList:=true);
end;



SliceNumberEXT_FAC:=function(EXT, FAC)
  local eFac, SliceList, SFAC, Aff, LD, eEXT, TheMat;
  SliceList:=[];
  for eFac in FAC
  do
    SFAC:=Filtered(EXT, x->x*eFac=0);
    Aff:=BaseIntMat(SFAC);
    LD:=[];
    for eEXT in EXT
    do
      TheMat:=ShallowCopy(Aff);
      Add(TheMat, eEXT);
      Add(LD, DeterminantMat(TheMat));
    od;
    Add(SliceList, Length(Set(LD)));
  od;
  return Minimum(SliceList);
end;





