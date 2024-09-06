
  FuncSelfIntersection:=function(ZigZag, ZigZagRev)
    NbTypeI:=0;
    NbTypeII:=0;
    for iFlag in [1..Length(ZigZag)]
    do
      rRev:=FuncMovement(ZigZag[iFlag], 1);
      if rRev in ZigZag then
        NbTypeI:=NbTypeI+1;
      elif rRev in ZigZagRev then
        NbTypeII:=NbTypeII+1;
      fi;
    od;
    return [NbTypeI, NbTypeII];
  end;

  FuncIntersection:=function(ZigZag1, ZigZagRev1, ZigZag2, ZigZagRev2)
    NbTypeI:=0;
    NbTypeII:=0;
    for iFlag in [1..Length(ZigZag1)]
    do
      rRev:=FuncInversionChange(ZigZag1[iFlag]);
      if rRev in ZigZag2 then
        NbTypeI:=NbTypeI+1;
      elif rRev in ZigZagRev2 then
        NbTypeII:=NbTypeII+1;
      fi;
    od;
    return [NbTypeI, NbTypeII];
  end;


#  IntInfo:=ZZ.FuncIntVectorLocalMethod(Petrie, ZZ.PetrieReversal(Petrie));
#  , IntInfo.SelfInt, SyncTextOccurrence(ListOcc)
#  ListOcc:=ExtractOccurrence(IntInfo.ListInt);

  FuncIntVector:=function(ZigZagEnumerationOutput, iPetrie)
    local Zsymbol, ListOcc, swp;
    jPetrie:=ZigZagEnumerationOutput.ListPairing[iPetrie];
    Zsymbol:=[];
    for kPetrie in [1..Length(ZigZagEnumerationOutput.ListPetrie)]
    do
      lPetrie:=ZigZagEnumerationOutput.ListPairing[kPetrie];
      if kPetrie<>iPetrie and kPetrie<>jPetrie and kPetrie>lPetrie then
        TypeInt:=FuncIntersection(ZigZagEnumerationOutput.ListPetrie[iPetrie], ZigZagEnumerationOutput.ListPetrie[jPetrie], ZigZagEnumerationOutput.ListPetrie[kPetrie], ZigZagEnumerationOutput.ListPetrie[lPetrie]);
        if TypeInt[2]>TypeInt[1] then
          swp:=TypeInt[1];
          TypeInt[1]:=TypeInt[2];
          TypeInt[2]:=swp;
        fi;
        Sstring:=Concatenation("(", String(TypeInt[1]), ",", String(TypeInt[2]), ")");
        Add(Zsymbol, Sstring);
      fi;
    od;
    ListOcc:=ExtractOccurrence(Zsymbol);
    return SyncTextOccurrence(ListOcc);
  end;
  #
  #
  # computation of the zigzags
  FuncZigZagEnumeration:=function()
    ListChain:=ListOfChain(SAU);
    Print("Find ", Length(ListChain), " Chains\n");
    ListPetrie:=[];
    while (Length(ListChain)>0)
    do
      Sequence:=FuncZigZagProlongation(ListChain[1]);
      Add(ListPetrie, Sequence);
      Print("Find zigzag with l=", Length(Sequence));
      Print("|Remains ", Length(ListChain), " chains|");
      Print("Total ", Length(ListPetrie), " zigzags");
      Print("\n");
      ListChain:=Difference(ListChain, Sequence);
    od;
    ListPairing:=[];
    for iPetrie in [1..Length(ListPetrie)]
    do
      ListPairing[iPetrie]:=-1;
    od;
    for iPetrie in [1..Length(ListPetrie)]
    do
      if ListPairing[iPetrie]=-1 then
        rRev:=FuncReverse(ListPetrie[iPetrie][1]);
        jPetrie:=iPetrie+1;
        while(ListPairing[iPetrie]=-1 and jPetrie<=Length(ListPetrie))
        do
          if rRev in ListPetrie[jPetrie] then
            ListPairing[iPetrie]:=jPetrie;
            ListPairing[jPetrie]:=iPetrie;
          fi;
          jPetrie:=jPetrie+1;
        od;
      fi;
    od;
    return rec(ListPairing:=ListPairing, ListPetrie:=ListPetrie);
  end;


CreateFlagFormalismSAU:=function(SAU)
  local FlagMov;
  FlagMov:=function(Flag, iMov)

    FlagNew:=ShallowCopy(eElt);
    if iMov=1 then
      FlagNew[1]:=Difference(SAU.ListUnder[1][FlagNew[2]], [FlagNew[1]])[1];
    elif iMoc=nRank-1 then
      FlagNew[nRank-1]:=Difference(SAU.ListAbove[nRank-2][FlagNew[nRank-2]], [FlagNew[nRank-1]])[1];
    else
      FlagNew[iMov]:=Difference(Intersection(SAU.ListAbove[iMov-1][FlagNew[iMov-1]], SAU.ListUnder[iMov][FlagNew[iMov+1]]), [FlagNew[iMov]])[1];
    fi;
    return FlagNew;
  end;
  return FlagMov;
end;







ReverseBasic:=function(BElt)
  local u, ResReturn;
  ResReturn:=[];
  for u in [1..Length(BElt)]
  do
    ResReturn[u]:=Reversed(BElt[u]);
  od;
  return ResReturn;
end;

ReversePetrie:=function(Petrie)
  local iZ, RPetrie; 
  RPetrie:=[];
  for iZ in [1..Length(Petrie)]
  do
    RPetrie[iZ]:=ReverseBasic(Petrie[iZ]);
  od;
  return Reversed(RPetrie);
end;



PetriePolygon:=function(nRank, EltR, HasseList, lowest)
  local BasicElt, test, ListR, iRank, eSet, ListPrev, BElt, eInc, NewElt, jRank, Below, Upper, kElt, eElt, fElt, FollowBasic, ListPetrie, z, v,  Sequence,
   Zmatr, Type1, Type2, TypeFound, iZZ, jZZ, nbZZ, FuncType, FuncTestIntersect, Zsymbol, ZVEC, ListOcc;
  #
  #
  #
  ListR:=[];
  for iRank in [1..nRank]
  do
    ListR[iRank]:=[];
  od;
  for eSet in EltR
  do
    if eSet[2]>0 then
      AddSet(ListR[eSet[2]], eSet[1]);
    fi;
  od;
#  Print("Assignment by rank finished\n");
  BasicElt:=[];
  for eElt in ListR[1]
  do
    Add(BasicElt, [[eElt]]);
  od;
  for iRank in [2..nRank-1]
  do
    ListPrev:=StructuralCopy(BasicElt);
    BasicElt:=ShallowCopy([]);
    for BElt in ListPrev
    do
      for eInc in HasseList
      do
        if eInc[1]=BElt[iRank-1][1] then
          NewElt:=StructuralCopy(BElt);
          NewElt[iRank]:=[eInc[2]];
          for jRank in Reversed([1..iRank-1])
          do
            if jRank=1 then 
              Below:=lowest;
            else
              Below:=NewElt[jRank-1][Length(NewElt[jRank-1])];
            fi;
            Upper:=NewElt[jRank+1][Length(NewElt[jRank+1])];
            test:=0;
            for kElt in ListR[jRank]
            do
              if [Below, kElt] in HasseList and [kElt, Upper] in HasseList and kElt<>NewElt[jRank][Length(NewElt[jRank])] and test=0 then
                Add(NewElt[jRank], kElt);
		        test:=1;
              fi;
            od;
          od;
          Add(BasicElt, NewElt);
        fi;
      od;
    od;
#    Print("Generation iRank=", iRank, "finished\n");
  od;
#  Print("We find ", Length(BasicElt), " elements\n");
  FollowBasic:=function(BElt)
    local LCTA, iElt;
    NewElt:=[];
    for iRank in [1..nRank-1]
    do
      LCTA:=ShallowCopy([]);
      for iElt in [2..Length(BElt[iRank])]
      do
        LCTA[iElt-1]:=BElt[iRank][iElt];
      od;
      NewElt[iRank]:=LCTA;
    od;
    for iRank in Reversed([1..nRank-1])
    do
      if iRank=nRank-1 then
        Below:=NewElt[nRank-2][Length(NewElt[nRank-2])];
        Upper:=ListR[nRank][1];
      elif iRank=1 then
        Below:=lowest;
        Upper:=NewElt[2][Length(NewElt[2])];
      else
        Below:=NewElt[iRank-1][Length(NewElt[iRank-1])];
        Upper:=NewElt[iRank+1][Length(NewElt[iRank+1])];
      fi;
      test:=0;
      for kElt in ListR[iRank]
      do
        if [Below, kElt] in HasseList and [kElt, Upper] in HasseList and kElt<>BElt[iRank][Length(BElt[iRank])] and test=0 then
          Add(NewElt[iRank], kElt);
          test:=1;
        fi;
      od;
    od;
    return NewElt;
  end;
  #
  #
  # computation of the zigzags
  ListPetrie:=[];
  while (Length(BasicElt)>0)
  do
    z:=BasicElt[1];
    Sequence:=ShallowCopy([z]);
    v:=FollowBasic(z);
    while (v<>z)
    do
      Add(Sequence, v);
      v:=FollowBasic(v);
    od;
    Add(ListPetrie, Sequence);
    BasicElt:=Difference(BasicElt, Union(Sequence, ReversePetrie(Sequence)));
  od;
  #
  #
  #
  FuncTestIntersect:=function(BElt1, BElt2)
    local Line1, Line2, kPos;
    for iRank in [1..nRank-2]
    do
      Line1:=BElt1[iRank];
      Line2:=BElt2[iRank];
      for kPos in [2..nRank-iRank]
      do
        if Line1[kPos]<>Line2[kPos] then
          return false;
        fi;
      od;
    od;
    return true;
  end;
  #
  #
  #
  FuncType:=function(BElt1, BElt2)
    if FuncTestIntersect(BElt1, BElt2)=true then
      return 2;
    elif FuncTestIntersect(BElt1, ReverseBasic(BElt2))=true then
      return 1;
    else
      return 0;
    fi;
  end;
  nbZZ:=Length(ListPetrie);
  Zmatr:=NullMat(nbZZ, nbZZ);
  for iZZ in [1..nbZZ]
  do
    for jZZ in [1..nbZZ]
    do
      Type1:=0;
      Type2:=0;
      for eElt in ListPetrie[iZZ]
      do
        for fElt in ListPetrie[jZZ]
        do
          if iZZ<jZZ or eElt<>fElt then
            TypeFound:=FuncType(eElt, fElt);
            if TypeFound=2 then 
              Type2:=Type2+1;
            elif TypeFound=1 then 
              Type1:=Type1+1;
            fi;
           fi;
        od;
      od;
      Zmatr[iZZ][jZZ]:=[Type1, Type2];
    od;
  od;
  #
  #
  #
  Zsymbol:=[];
  for iZZ in [1..nbZZ]
  do
    Add(Zsymbol, Concatenation(String(Length(ListPetrie[iZZ])), "_{", String(Zmatr[iZZ][iZZ][1]),",", String(Zmatr[iZZ][iZZ][2]), "}"));
  od;
  ListOcc:=ExtractOccurrence(Zsymbol);
  ZVEC:=SyncTextOccurrence(ListOcc);
  return rec(ListZigZag:=ListPetrie, Zmatrix:=Zmatr, Zvector:=ZVEC);
end;


CallPetriePolygon:=function(Poset)
  local nRank, EltR, HasseList, lowest;
  nRank:=RankOfPoset(Poset);
  EltR:=ElementRank(Poset);
  HasseList:=PosetToHasseList(Poset);
  lowest:=FindLowest(Poset);
  return PetriePolygon(nRank, EltR, HasseList, lowest);
end;
