# a poset is coded as a list of incidence relations:
# for instance [[1,2],[2,3],[1,3]] encodes the natural ordering of [1,2,3]



#
#
#
# General stuff about posets
ListOfVertices:=function(Poset)
  local ListVert, eInc;
  ListVert:=[];
  for eInc in Poset
  do
    AddSet(ListVert, eInc[1]);
    AddSet(ListVert, eInc[2]);
  od;
  return ListVert;
end;



PosetToHasseList:=function(Poset)
  local HasseList, ListVert, eInc, FuncTest, eV;
  ListVert:=ListOfVertices(Poset);
  FuncTest:=function(fInc)
    for eV in ListVert
    do
      if eV<>fInc[1] and eV<>fInc[2] then
        if [fInc[1],eV] in Poset and [eV,fInc[2]] in Poset then
          return false;
        fi;
      fi;
    od;
    return true;
  end;
  HasseList:=[];
  for eInc in Poset
  do
    if FuncTest(eInc)=true then
      AddSet(HasseList, eInc);
#      Print("HasseList=", Length(HasseList), "\n");
    fi;
  od;
  return HasseList;
end;




HasseListToPoset:=function(HasseList)
  local ListVert, eInc, fInc, PosetOld, PosetNew;
  ListVert:=ListOfVertices(HasseList);
  PosetOld:=[];
  PosetNew:=Set(HasseList);
  repeat
    PosetOld:=PosetNew;
    for eInc in PosetOld
    do
      for fInc in PosetOld
      do
        if eInc[2]=fInc[1] then
          AddSet(PosetNew, [eInc[1],fInc[2]]);
        fi;
      od;
    od;
  until PosetNew=PosetOld;
  return PosetNew;
end;

# Find local lowest, greedy search
FindLowest:=function(Poset)
  local eElt, FuncTestLow, T;
  eElt:=Poset[1][1];
  FuncTestLow:=function(fElt)
    local fInc;
    for fInc in Poset
    do
      if fInc[2]=fElt then
        return fInc[1];
      fi;
    od;
    return true;
  end;
  repeat
    T:=FuncTestLow(eElt);
    if T<>true then
      eElt:=T;
    fi;
  until T=true;
  return eElt;
end;

RemoveLowest:=function(Poset)
  local lowest, NewPoset, eInc;
  lowest:=FindLowest(Poset);
  NewPoset:=[];
  for eInc in Poset
  do
    if eInc[1]<>lowest then
      Add(NewPoset, eInc);
    fi;
  od;
  return NewPoset;
end;

AddLowest:=function(Poset)
  local ListVert, pos, NewPoset, eInc, u;
  ListVert:=ListOfVertices(Poset);
  pos:=Maximum(ListVert)+1;
#  Print("pos=", pos, "\n");
  NewPoset:=[];
  for eInc in Poset
  do
    Add(NewPoset, eInc);
  od;
  for u in ListVert
  do
    Add(NewPoset, [pos, u]);
  od;
  return NewPoset;
end;


DualPoset:=function(Poset)
  local ListComp, eInc;
  ListComp:=[];
  for eInc in Poset
  do
    Add(ListComp, [eInc[2],eInc[1]]);
  od;
  return ListComp;
end;




FindHighest:=function(Poset)
  local eElt, FuncTestLow, T;
  eElt:=Poset[1][1];
  FuncTestLow:=function(fElt)
    local fInc;
    for fInc in Poset
    do
      if fInc[1]=fElt then
        return fInc[2];
      fi;
    od;
    return true;
  end;
  repeat
    T:=FuncTestLow(eElt);
    if T<>true then
      eElt:=T;
    fi;
  until T=true;
  return eElt;
end;




PosetToGRAPE:=function(Poset)
  local ListVert, G, eInc, p1, p2;
  ListVert:=ListOfVertices(Poset);
  G:=NullGraph(Group(()), Length(ListVert));
  for eInc in Poset
  do
    p1:=Position(ListVert, eInc[1]);
    p2:=Position(ListVert, eInc[2]);
    AddEdgeOrbit(G, [p1, p2]);
  od;
  return G;
end;


IsIsomorphicPoset:=function(Poset1, Poset2)
  return IsIsomorphicGraph(PosetToGRAPE(Poset1), PosetToGRAPE(Poset2));
end;









#
#
#
# return a list [[elt, nRank], ....]
# with the rank for each element.
ElementRank:=function(Poset)
  local ListVert, HasseList, lowest, ListRanked, ListRanks, iVert, Pos, eInc, pos1, pos2;
  ListVert:=ListOfVertices(Poset);
  HasseList:=PosetToHasseList(Poset);
  lowest:=FindLowest(Poset);
  ListRanked:=[lowest];
  ListRanks:=[];
  for iVert in [1..Length(ListVert)]
  do
    ListRanks[iVert]:=[ListVert[iVert],-1];
  od;
  Pos:=Position(ListVert, lowest);
  ListRanks[Pos]:=[lowest, 0];
  repeat
    for eInc in HasseList
    do
      pos1:=Position(ListVert, eInc[1]);
      pos2:=Position(ListVert, eInc[2]);
      if ListRanks[pos1][2]>-1 and ListRanks[pos2][2]=-1 then
        ListRanks[pos2][2]:=ListRanks[pos1][2]+1;
        AddSet(ListRanked, eInc[2]);
      fi;
    od;
  until Length(ListRanked)=Length(ListVert);
  return ListRanks;
end;




RankOfPoset:=function(Poset)
  local ListRanks, nRank, eElt;
  ListRanks:=ElementRank(Poset);
  nRank:=0;
  for eElt in ListRanks
  do
    if eElt[2]>nRank then
      nRank:=eElt[2];
    fi;
  od;
  return nRank;
end;


IsRankedPoset:=function(Poset)
  local HasseList, EltR, eR, FuncRank, eInc;
  EltR:=ElementRank(Poset);
  FuncRank:=function(eElt)
    for eR in EltR
    do
      if eR[1]=eElt then
        return eR[2];
      fi;
    od;
    return false;
  end;
  for eInc in PosetToHasseList(Poset)
  do
    if FuncRank(eInc[2])<>1+FuncRank(eInc[1]) then
      return false;
    fi;
  od;
  return true;
end;

#
#
# reorder the elements by increasing rank
# and moreover, change numbers to 1...nbElt
RenormalizePoset:=function(Poset)
  local nRank, ListRanks, TranslationTable, lowest, Posi, iRank, eElt, FuncReverse, PosetNew, eInc;
  nRank:=RankOfPoset(Poset);
  ListRanks:=ElementRank(Poset);
  TranslationTable:=[];
  lowest:=FindLowest(Poset);
  Add(TranslationTable, [1,lowest]);
  Posi:=1;
  for iRank in [1..nRank]
  do
    for eElt in ListRanks
    do
      if eElt[2]=iRank then
        Posi:=Posi+1;
        Add(TranslationTable, [Posi, eElt[1]]);
      fi;
    od;
  od;
  FuncReverse:=function(OldPos)
    local fElt;
    for fElt in TranslationTable
    do
      if fElt[2]=OldPos then
        return fElt[1];
      fi;
    od;
  end;
  PosetNew:=[];
  for eInc in Poset
  do
    Add(PosetNew, [FuncReverse(eInc[1]),FuncReverse(eInc[2])]);
  od;
  return rec(Poset:=PosetNew, TranslationTable:=TranslationTable);
end;



MaximalRank:=function(ListRanks)
  local MaxRank, eElt;
  MaxRank:=0;
  for eElt in ListRanks
  do
    if eElt[2]>MaxRank then
      MaxRank:=eElt[2];
    fi;
  od;
  return MaxRank;
end;



IsSelfDualPoset:=function(Poset)
  return IsIsomorphicPoset(Poset, DualPoset(Poset));
end;



BruhatInterval:=function(Poset, low, high)
  local ListVert, ListNewVert, eVert, NewPoset, eInc;
  ListVert:=ListOfVertices(Poset);
  ListNewVert:=[low, high];
  for eVert in ListVert
  do
    if [low, eVert] in Poset and [eVert, high] in Poset then
      Add(ListNewVert, eVert);
    fi;
  od;
  NewPoset:=[];
  for eInc in Poset
  do
    if eInc[1] in ListNewVert and eInc[2] in ListNewVert then
      Add(NewPoset, eInc);
    fi;
  od;
  return NewPoset;
end;

IsRankedPoset:=function(Poset)
  local ListRanks, HasseList, FuncRank, eInc, eR1, eR2;
  ListRanks:=ElementRank(Poset);
  HasseList:=PosetToHasseList(Poset);
  FuncRank:=function(eElt)
    local eRank;
    for eRank in ListRanks
    do
      if eRank[1]=eElt then
        return eRank[2];
      fi;
    od;
    return false;
  end;
  for eInc in HasseList
  do
    eR1:=FuncRank(eInc[1]);
    eR2:=FuncRank(eInc[2]);
    if eR2<>eR1+1 then
      return false;
    fi;
  od;
  return true;
end;



IsEulerianPoset:=function(Poset)
  local eInc, NbEven, NbOdd, eRank;
  for eInc in Poset
  do
    NbEven:=0;
    NbOdd:=0;
    for eRank in ElementRank(BruhatInterval(Poset, eInc[1], eInc[2]))
    do
      if (eRank[2] mod 2)=0 then
        NbEven:=NbEven+1;
      else
        NbOdd:=NbOdd+1;
      fi;
    od;
    if NbEven<>NbOdd then
	return false;
    fi;
  od;
  return true;
end;



__IsLattice:=function(Poset)
  local ListVert, FuncTransformList, iVert, jVert, kVert, ListInferiorBound;
  ListVert:=ListOfVertices(Poset);
  FuncTransformList:=function(ListElt, NewCand)
    local ListLow, eElt, ListNew;
    ListLow:=[];
    for eElt in ListElt
    do
      if [eElt, NewCand] in Poset then
        Add(ListLow, eElt);
      fi;
      if [NewCand, eElt] in Poset then
        return ListElt;
      fi;
    od;
    ListNew:=ShallowCopy(ListElt);
    AddSet(ListNew, NewCand);
    for eElt in ListLow
    do
      RemoveSet(ListNew, eElt);
    od;
    return ListNew;
  end;
  for iVert in ListVert
  do
    for jVert in ListVert
    do
      if iVert<>jVert and not([iVert, jVert] in Poset) and not([jVert, iVert] in Poset) then
        ListInferiorBound:=[];
        for kVert in ListVert
        do
          if ([kVert, iVert] in Poset) and ([kVert, jVert] in Poset) then
            ListInferiorBound:=FuncTransformList(ListInferiorBound, kVert);
          fi;
        od;
        if Length(ListInferiorBound)<>1 then
          return false;
        fi;
      fi;
    od;
  od;
  return true;
end;



IsLattice:=function(Poset)
  if __IsLattice(Poset)=false then
    return false;
  elif __IsLattice(DualPoset(Poset))=false then
    return false;
  fi;
  return true;
end;





#
#
# the function mobius, denoted by mu(x,y) should satisfy to
# sum_{x<= z<=y} mu(x,z)=0 if x<>y,
# mu(x,x)=1,
# and mu(x,y)=0 if x is not inferior to y
MobiusFunction:=function(Poset)
  local ListVert, FuncMobius, highest, FuncMatrixMobius;
  ListVert:=ListOfVertices(Poset);
  highest:=FindHighest(Poset);
#  Print("ListVert=", ListVert, "\n");
  FuncMobius:=function(x, y)
    local ListZ, ListValueMuxz, z, NbUnk, iY, Sum, test, iZ, pos;
    ListZ:=[x,y];
    ListValueMuxz:=[1,"unk"];
    for z in ListVert
    do
      if ([x,z] in Poset) and ([z,y] in Poset) then
        Add(ListZ, z);
        if z=x then
          Add(ListValueMuxz, 1);
        else
          Add(ListValueMuxz, "unk");
        fi;
      fi;
    od;
#    Print("ListValueMuxz=", ListValueMuxz, "\n");
    NbUnk:=Length(ListValueMuxz)-1;
    while (NbUnk>0)
    do
      for iY in [1..Length(ListZ)]
      do
        if ListValueMuxz[iY]="unk" then
          Sum:=0;
          test:=true;
          for iZ in [1..Length(ListValueMuxz)]
          do
            if [ListZ[iZ],ListZ[iY]] in Poset then
              if iY<>iZ then
                if ListValueMuxz[iZ]="unk" then
                  test:=false;
                fi;
                if test=true then
                  Sum:=Sum+ListValueMuxz[iZ];
                fi;
              fi;
            fi;
          od;
          if test=true then
            ListValueMuxz[iY]:=-Sum;
            NbUnk:=NbUnk-1;
          fi;
        fi;
      od;
#      Print("ListValueMuxz=", ListValueMuxz, "\n");
    od;
    return rec(ListZ:=ListZ, ListValueMuxz:=ListValueMuxz);
  end;
  FuncMatrixMobius:=function()
    local MobiusMatrixMuxy, iCol, LC, ROW, jCol, iZ, pos;
    MobiusMatrixMuxy:=[];
    for iCol in [1..Length(ListVert)]
    do
      LC:=FuncMobius(ListVert[iCol], highest);
      ROW:=[];
      for jCol in [1..Length(ListVert)]
      do
        if iCol=jCol then
          Add(ROW, 1);
        elif not([ListVert[iCol],ListVert[jCol]] in Poset) then
          Add(ROW, 0);
        else
          Add(ROW, "unk");
        fi;
      od;
      for iZ in [1..Length(LC.ListZ)]
      do
        pos:=Position(ListVert, LC.ListZ[iZ]);
        ROW[pos]:=LC.ListValueMuxz[iZ];
      od;
      Add(MobiusMatrixMuxy, ROW);
    od;
    return MobiusMatrixMuxy;
  end;
  MobiusFunction:=function(Poset, x, y)
    local LC, pos;
    if x=y then
      return 1;
    fi;
    if not([x,y] in Poset) then
      return 0;
    fi;
    LC:=FuncMobius(Poset, x, y);
    pos:=Position(LC.ListZ, y);
    return LC.ListValueMuxz[pos];
  end;
  return rec(MobiusFunction:=MobiusFunction, FuncMatrixMobius:=FuncMatrixMobius, FuncMobius:=FuncMobius);
end;




#
#
# work only for small groups
PosetOfSubgroups:=function(Group)
  local CJ, ListSubgroups, eCJ, NewPoset, iGroup, jGroup;
  CJ:=ConjugacyClassesSubgroups;
  ListSubgroups:=[];
  for eCJ in CJ
  do
    ListSubgroups:=Union(ListSubgroups, AsList(eCJ));
  od;
  NewPoset:=[];
  for iGroup in [1..Length(ListSubgroups)]
  do
    for jGroup in [1..Length(ListSubgroups)]
    do
      if iGroup<>jGroup then
        if IsSubgroup(ListSubgroups[jGroup], ListSubgroups[jGroup])=true then
          Add(NewPoset, [jGroup, iGroup]);
        fi;
      fi;
    od;
  od;
  return rec(Element:=ListSubgroups, Poset:=NewPoset);
end;







#
#
# In RankInf and RankSup, the elements Elt1 and Elt2 must
# be of the same rank
RankInf:=function(HasseList, Elt1, Elt2)
  local Prec1, Prec2, NbOpe, NewPrec1, NewPrec2, eInc;
  Prec1:=[Elt1];
  Prec2:=[Elt2];
  NbOpe:=0;
  while Intersection(Prec1, Prec2)=[]
  do
    NewPrec1:=[];
    NewPrec2:=[];
    for eInc in HasseList
    do
      if eInc[2] in Prec1 then
        Add(NewPrec1, eInc[1]);
      fi;
      if eInc[2] in Prec2 then
        Add(NewPrec2, eInc[1]);
      fi;
    od;
    Prec1:=StructuralCopy(NewPrec1);
    Prec2:=StructuralCopy(NewPrec2);
    NbOpe:=NbOpe+1;
  od;
  return NbOpe;
end;


RankSup:=function(HasseList, Elt1, Elt2)
  local Prec1, Prec2, NbOpe, NewPrec1, NewPrec2, eInc;
  Prec1:=[Elt1];
  Prec2:=[Elt2];
  NbOpe:=0;
  while Intersection(Prec1, Prec2)=[]
  do
    NewPrec1:=[];
    NewPrec2:=[];
    for eInc in HasseList
    do
      if eInc[1] in Prec1 then
        Add(NewPrec1, eInc[2]);
      fi;
      if eInc[1] in Prec2 then
        Add(NewPrec2, eInc[2]);
      fi;
    od;
    Prec1:=StructuralCopy(NewPrec1);
    Prec2:=StructuralCopy(NewPrec2);
    NbOpe:=NbOpe+1;
  od;
  return NbOpe;
end;


SkelettonsOfPoset:=function(Poset, kRank)
  local ListVert, ListRanks, ListVertSkel, eElt, SkeletonGraph, iVert, jVert, N1, N2, nRank;
  ListVert:=ListOfVertices(Poset);
  ListRanks:=ElementRank(Poset);
  ListVertSkel:=[];
  nRank:=RankOfPoset(Poset);
  for eElt in ListRanks
  do
    if eElt[2]=kRank then
      Add(ListVertSkel, eElt[1]);
    fi;
  od;
  SkeletonGraph:=NullGraph(Group(()), Length(ListVertSkel));
  for iVert in [1..Length(ListVertSkel)]
  do
    for jVert in [1..Length(ListVertSkel)]
    do
      if iVert<>jVert then
        N1:=1;
        N2:=1;
        if kRank=1 then
          N2:=RankSup(ListVertSkel[iVert], ListVertSkel[jVert]);
        elif kRank=nRank-1 then
          N1:=RankInf(ListVertSkel[iVert], ListVertSkel[jVert]);
        else
          N1:=RankInf(ListVertSkel[iVert], ListVertSkel[jVert]);
          N2:=RankSup(ListVertSkel[iVert], ListVertSkel[jVert]);
        fi;
        if N1=1 and N2=1 then
          AddEdgeOrbit(SkeletonGraph, [iVert, jVert]);
          AddEdgeOrbit(SkeletonGraph, [jVert, iVert]);
        fi;
      fi;
    od;
  od;
  return rec(Names:=ListVertSkel, Graph:=SkelettonsOfPoset);
end;


#
# test if the poset correspond to an oriented manifold
# if so, then compute the zigzags
CreateListAboveListUnder:=function(Poset)
  local nRank, EltR, HasseList, SEQE, iRank, eElt, ListAbove, ListAB, iVert, jVert, ListUnder, ListFound;
  nRank:=RankOfPoset(Poset);
  EltR:=ElementRank(Poset);
  HasseList:=PosetToHasseList(Poset);
  SEQE:=[];
  for iRank in [1..nRank-1]
  do
    SEQE[iRank]:=[];
  od;
  for eElt in EltR
  do
    iRank:=eElt[2];
    if iRank>0 and iRank<nRank then
      AddSet(SEQE[iRank], eElt[1]);
    fi;
  od;
  ListAbove:=[];
  for iRank in [1..nRank-2]
  do
    ListAB:=[];
    for iVert in [1..Length(SEQE[iRank])]
    do
      ListFound:=[];
      for jVert in [1..Length(SEQE[iRank+1])]
      do
        if [SEQE[iRank][iVert], SEQE[iRank+1][jVert]] in HasseList then
          Add(ListFound, jVert);
        fi;
      od;
      Add(ListAB, ListFound);
    od;
    Add(ListAbove, ListAB);
  od;
  ListUnder:=[];
  for iRank in [1..nRank-2]
  do
    ListAB:=[];
    for iVert in [1..Length(SEQE[iRank+1])]
    do
      ListFound:=[];
      for jVert in [1..Length(SEQE[iRank])]
      do
        if [SEQE[iRank][jVert], SEQE[iRank+1][iVert]] in HasseList then
          Add(ListFound, jVert);
        fi;
      od;
      Add(ListAB, ListFound);
    od;
    Add(ListUnder, ListAB);
  od;
  return rec(SEQE:=SEQE, ListAbove:=ListAbove, ListUnder:=ListUnder);
end;


ListOfChain:=function(SAU)
  local BasicElt, eElt, iRank, ListPrev, BElt, eF, SEF, iElt, ePrev, LastElt;
  BasicElt:=[];
  for eElt in [1..Length(SAU.SEQE[1])]
  do
    Add(BasicElt, [eElt]);
  od;
  for iRank in [2..Length(SAU.SEQE)]
  do
#    Print("Running for iRank=", iRank, "\n");
    ListPrev:=[];
    for ePrev in BasicElt
    do
      Add(ListPrev, ShallowCopy(ePrev));
    od;
    BasicElt:=[];
    for iElt in [1..Length(ListPrev)]
    do
      LastElt:=ListPrev[iElt][iRank-1];
      for eF in SAU.ListAbove[iRank-1][LastElt]
      do
        SEF:=ShallowCopy(ListPrev[iElt]);
        Add(SEF, eF);
        Add(BasicElt, SEF);
      od;
    od;
  od;
  return BasicElt;
end;


ListOrbitChain:=function(SAU, GroupEXT)
  local ListVert, eElt, BasicElt, eOrb, pos, iRank, ListPrev, ePrev, iElt, LastElt, UpSetPossible, UpSetIndex, eF, SEF, Idx, FlagAction, FuncReducedForm, nRank, ListOrbit;
  ListVert:=[1..Length(SAU.SEQE[1])];
  nRank:=Length(SAU.SEQE)+1;
  BasicElt:=[];
  for eOrb in Orbits(GroupEXT, ListVert, OnPoints)
  do
    pos:=Position(SAU.SEQE[1], [eOrb[1]]);
    Add(BasicElt, [[pos], Stabilizer(GroupEXT, eOrb[1], OnPoints)]);
  od;
  for iRank in [2..Length(SAU.SEQE)]
  do
    ListPrev:=[];
    for ePrev in BasicElt
    do
      Add(ListPrev, ShallowCopy(ePrev));
    od;
    BasicElt:=[];
    for iElt in [1..Length(ListPrev)]
    do
      eElt:=ListPrev[iElt];
      LastElt:=eElt[1][iRank-1];
      UpSetPossible:=[];
      UpSetIndex:=[];
      for eF in SAU.ListAbove[iRank-1][LastElt]
      do
        Add(UpSetIndex, eF);
        Add(UpSetPossible, SAU.SEQE[iRank][eF]);
      od;
      for eOrb in Orbits(eElt[2], UpSetPossible, OnSets)
      do
        SEF:=ShallowCopy(eElt[1]);
        Idx:=UpSetIndex[Position(UpSetPossible, eOrb[1])];
        Add(SEF, Idx);
        Add(BasicElt, [SEF, Stabilizer(eElt[2], eOrb[1], OnSets)]);
      od;
    od;
  od;
  ListOrbit:=[];
  for eF in BasicElt
  do
    Add(ListOrbit, eF[1]);
  od;
  FlagAction:=function(Flag, g)
    local ReturnedFlag, iRank;
    ReturnedFlag:=[];
    for iRank in [1..nRank-1]
    do
      ReturnedFlag[iRank]:=Position(SAU.SEQE[iRank], OnSets(SAU.SEQE[iRank][Flag[iRank]], g));
    od;
    return ReturnedFlag;
  end;
  FuncReducedForm:=function(Flag)
    local g, ReturnedFlag, GrpStab, iRank, O;
    ReturnedFlag:=ShallowCopy(Flag);
    GrpStab:=ShallowCopy(GroupEXT);
    for iRank in [1..nRank-1]
    do
      O:=Set(Orbit(GrpStab, SAU.SEQE[iRank][ReturnedFlag[iRank]], OnSets));
      g:=RepresentativeAction(GrpStab, SAU.SEQE[iRank][ReturnedFlag[iRank]], O[1], OnSets);
      ReturnedFlag:=FlagAction(ReturnedFlag, g);
      GrpStab:=Stabilizer(GrpStab, SAU.SEQE[iRank][ReturnedFlag[iRank]], OnSets);
    od;
    return ReturnedFlag;
  end;
  return rec(ListOrbit:=ListOrbit, FlagAction:=FlagAction, FuncReducedForm:=FuncReducedForm);
end;





#
# this function is faster than the pure enumeration of chains
NumberOfChain:=function(SAU)
  local nRank, ListPrev, iPrev, iRank, ListNew, iNew, eUp, NbChain;
  nRank:=Length(SAU.SEQE)+1;
  ListPrev:=[];
  for iPrev in [1..Length(SAU.SEQE[1])]
  do
    ListPrev[iPrev]:=1;
  od;
  for iRank in [2..nRank-1]
  do
    ListNew:=[];
    for iNew in [1..Length(SAU.SEQE[iRank])]
    do
      ListNew[iNew]:=0;
    od;
    for iPrev in [1..Length(SAU.SEQE[iRank-1])]
    do
      for eUp in SAU.ListAbove[iRank-1][iPrev]
      do
        ListNew[eUp]:=ListNew[eUp]+ListPrev[iPrev];
      od;
    od;
    ListPrev:=[];
    for iNew in [1..Length(SAU.SEQE[iRank])]
    do
      ListPrev[iNew]:=ShallowCopy(ListNew[iNew]);
    od;
  od;
  NbChain:=0;
  for iPrev in [1..Length(ListPrev)]
  do
    NbChain:=NbChain+ListPrev[iPrev];
  od;
  return NbChain;
end;





IsOriented:=function(Poset)
  local SAU, nRank, BasicElt, FuncMovement, ListNew, nbChain, ListStatus, ListColor, iChain, ListDone, NewColor, jChain, pos;
  SAU:=CreateListAboveListUnder(Poset);
  nRank:=Length(SAU.SEQE)+1;
  BasicElt:=ListOfChain(SAU);
  FuncMovement:=function(eElt, pos)
    ListNew:=ShallowCopy(eElt);
    if pos=1 then
      ListNew[1]:=Difference(SAU.ListUnder[1][eElt[2]], [eElt[1]])[1];
      return ListNew;
    elif pos=nRank-1 then
      ListNew[nRank-1]:=Difference(SAU.ListAbove[nRank-2][eElt[nRank-2]], [eElt[nRank-1]])[1];
      return ListNew;
    else
      ListNew[pos]:=Difference(Intersection(SAU.ListAbove[pos-1][eElt[pos-1]], SAU.ListUnder[pos][eElt[pos+1]]), [eElt[pos]])[1];
      return ListNew;
    fi;
  end;

  nbChain:=Length(BasicElt);
  ListStatus:=[];
  ListColor:=[];
  for iChain in [1..nbChain]
  do
    ListStatus[iChain]:=-1;
    ListColor[iChain]:=-1;
  od;
  ListDone:=0;
  ListColor[1]:=1;
  while (ListDone<nbChain)
  do
    for iChain in [1..nbChain]
    do
      if ListColor[iChain]<>-1 and ListStatus[iChain]<>1 then
        ListStatus[iChain]:=1;
        NewColor:=1-ListColor[iChain];
        ListDone:=ListDone+1;
        for pos in [1..nRank-1]
        do
          jChain:=Position(BasicElt, FuncMovement(BasicElt[iChain], pos));
          if ListColor[jChain]<> -1 and ListColor[jChain]<>NewColor then
            return false;
          fi;
          ListColor[jChain]:=NewColor;
        od;
      fi;
    od;
  od;
  return true;
end;


LatticeDescriptionToSAU:=function(ListFaces)
  local dimension, ListAbove, ListUnder, iRank, ListAB, iVert, jVert, ListFound;
  dimension:=Length(ListFaces);
  ListAbove:=[];
#  Print("Computing list of Above elements\n");
  for iRank in [1..dimension-1]
  do
    ListAB:=[];
    for iVert in [1..Length(ListFaces[iRank])]
    do
      ListFound:=[];
      for jVert in [1..Length(ListFaces[iRank+1])]
      do
        if IsSubset(ListFaces[iRank+1][jVert], ListFaces[iRank][iVert])=true then
          Add(ListFound, jVert);
        fi;
      od;
      Add(ListAB, ListFound);
    od;
    Add(ListAbove, ListAB);
  od;
#  Print("Computing list of Under elements\n");
  ListUnder:=[];
  for iRank in [1..dimension-1]
  do
    ListAB:=[];
    for iVert in [1..Length(ListFaces[iRank+1])]
    do
      ListFound:=[];
      for jVert in [1..Length(ListFaces[iRank])]
      do
        if IsSubset(ListFaces[iRank+1][iVert], ListFaces[iRank][jVert])=true then
          Add(ListFound, jVert);
        fi;
      od;
      Add(ListAB, ListFound);
    od;
    Add(ListUnder, ListAB);
  od;
  return rec(SEQE:=ListFaces, ListAbove:=ListAbove, ListUnder:=ListUnder);
end;

LatticeDescriptionToPoset:=function(SEQE)
  local ListElt, ListVert, u, iRank, NewPoset, iElt, jElt;
  ListElt:=[[]];
  ListVert:=[];
  for u in SEQE[1]
  do
    Add(ListVert, u[1]);
  od;
  Add(ListElt, ListVert);
  for iRank in [1..Length(SEQE)]
  do
    ListElt:=Union(ListElt, SEQE[iRank]);
  od;
  NewPoset:=[];
  for iElt in [1..Length(ListElt)]
  do
    for jElt in [1..Length(ListElt)]
    do
      if iElt<>jElt then
        if IsSubset(ListElt[jElt], ListElt[iElt])=true then
          Add(NewPoset, [iElt, jElt]);
        fi;
      fi;
    od;
  od;
  return NewPoset;
end;



ReorderingLatticeDescription:=function(LatticeDesc)
  local NewLatticeDesc, iRank, NewListFace, eFac, fFac, eVert, ListVert;
  ListVert:=[];
  for eVert in LatticeDesc[1]
  do
    Add(ListVert, eVert[1]);
  od;
  NewLatticeDesc:=[];
  for iRank in [1..Length(LatticeDesc)]
  do
    NewListFace:=[];
    for eFac in LatticeDesc[iRank]
    do
      fFac:=[];
      for eVert in eFac
      do
        Add(fFac, Position(ListVert, eVert));
      od;
      Add(NewListFace, fFac);
    od;
    Add(NewLatticeDesc, NewListFace);
  od;
  return NewLatticeDesc;
end;


PosetToLatticeDescription:=function(Poset)
  local EltR, ListVert, MaxRank, eRank, LatticeDesc, iRank, LV, eVert, rnk;
  EltR:=ElementRank(Poset);
  ListVert:=[];
  MaxRank:=0;
  for eRank in EltR
  do
    if eRank[2]=1 then
      AddSet(ListVert, eRank[1]);
    fi;
    if eRank[2]>MaxRank then
      MaxRank:=eRank[2];
    fi;
  od;
  LatticeDesc:=[];
  for iRank in [1..MaxRank-1]
  do
    Add(LatticeDesc, []);
  od;
  for eRank in EltR
  do
    rnk:=eRank[2];
    if rnk>0 and rnk<MaxRank then
      if rnk>1 then
        LV:=[];
        for eVert in ListVert
        do
          if [eVert, eRank[1]] in Poset then
            AddSet(LV, eVert);
          fi;
        od;
      else
        LV:=[eRank[1]];
      fi;
#      Print("LV=", LV, "\n");
      if Position(LatticeDesc[rnk], LV)<>fail then
        return false;
      fi;
      Add(LatticeDesc[rnk], LV);
    fi;
  od;
  return ReorderingLatticeDescription(LatticeDesc);
end;


LatticeDescriptionToSkeleton:=function(SEQE, k, GroupEXT)
  local NewGroup, nbVert, Gra, Overt, dimE, FuncTestAdj, iOrb, jOrb, Stab, OvertSec, eV, fV;
  NewGroup:=TranslateGroup(GroupEXT, SEQE[k], OnSets);
  nbVert:=Length(SEQE[k]);
  Gra:=NullGraph(NewGroup, nbVert);
  dimE:=Length(SEQE);

  FuncTestAdj:=function(eV, fV)
    local test1, test2, INTS, eSet;
    test1:=true;
    if k>1 then
      INTS:=Intersection(SEQE[k][eV], SEQE[k][fV]);
      if Position(SEQE[k-1], INTS)<>fail then
        test1:=true;
      else
        test1:=false;
      fi;
    fi;
    test2:=true;
    if k<dimE and test1=true then
      INTS:=Union(SEQE[k][eV], SEQE[k][fV]);
      test2:=false;
      for eSet in SEQE[k+1]
      do
        if IsSubset(eSet, INTS)=true then
          return true;
        fi;
      od;
    fi;
    if test1=true and test2=true then
      return true;
    else
      return false;
    fi;
  end;
  #
  Overt:=Orbits(NewGroup, [1..nbVert], OnPoints);
  for iOrb in [1..Length(Overt)]
  do
    eV:=Overt[iOrb][1];
    Stab:=Stabilizer(NewGroup, eV, OnPoints);
    OvertSec:=Orbits(Stab, Difference([1..nbVert],[eV]),OnPoints);
    for jOrb in [1..Length(OvertSec)]
    do
      fV:=OvertSec[jOrb][1];
      if FuncTestAdj(eV, fV)=true then
        AddEdgeOrbit(Gra, [eV,fV]);
      fi;
    od;
  od;
  return Gra;
end;




# latticedesc should be reordered.
GroupEXTofLatticeDescription:=function(LatticeDesc)
  local nbE, nbVert, pos, Gra, iRank, iFac, eVert, GroupF, NewGens, eGen, ListE, iVert;
  nbE:=0;
  nbVert:=Length(LatticeDesc[1]);
  for iRank in [1..Length(LatticeDesc)]
  do
    nbE:=nbE+Length(LatticeDesc[iRank]);
  od;
  pos:=nbVert;
  Gra:=NullGraph(Group(()), nbE);
  for iRank in [2..Length(LatticeDesc)]
  do
    for iFac in [1..Length(LatticeDesc[iRank])]
    do
      for eVert in LatticeDesc[iRank][iFac]
      do
        AddEdgeOrbit(Gra, [eVert, pos+iFac]);
      od;
    od;
    pos:=pos+Length(LatticeDesc[iRank]);
  od;
  GroupF:=AutGroupGraph(Gra);
  NewGens:=[];
  for eGen in GeneratorsOfGroup(GroupF)
  do
    ListE:=[];
    for iVert in [1..nbVert]
    do
      Add(ListE, OnPoints(iVert, eGen));
    od;
    Add(NewGens, PermList(ListE));
  od;
  if Length(NewGens)=0 then
    return Group(());
  else
    return Group(NewGens);
  fi;
end;



PosetToSAU:=function(Poset)
  local EltR, iRank, nRank, eR, dimension, ListFaces, ListAbove, ListUnder, ListAdd, iElt, jElt, ListA;
  EltR:=ElementRank(Poset);
  nRank:=0;
  for eR in EltR
  do
    if eR[2]>nRank then
      nRank:=eR[2];
    fi;
  od;
  dimension:=nRank-1;
  ListFaces:=[];
  for iRank in [1..dimension]
  do
    ListFaces[iRank]:=[];
  od;
  for eR in EltR
  do
    if eR[2]>0 and eR[2]<nRank then
      Add(ListFaces[eR[2]], eR[1]);
    fi;
  od;
  ListAbove:=[];
  for iRank in [1..dimension-1]
  do
    ListAdd:=[];
    for iElt in [1..Length(ListFaces[iRank])]
    do
      ListA:=[];
      for jElt in [1..Length(ListFaces[iRank+1])]
      do
        if [ListFaces[iRank][iElt],ListFaces[iRank+1][jElt]] in Poset then
          Add(ListA, jElt);
        fi;
      od;
      Add(ListAdd, ListA);
    od;
    Add(ListAbove, ListAdd);
  od;
  ListUnder:=[];
  for iRank in [1..dimension-1]
  do
    ListAdd:=[];
    for iElt in [1..Length(ListFaces[iRank+1])]
    do
      ListA:=[];
      for jElt in [1..Length(ListFaces[iRank])]
      do
        if [ListFaces[iRank][jElt], ListFaces[iRank+1][iElt]] in Poset then
          Add(ListA, jElt);
        fi;
      od;
      Add(ListAdd, ListA);
    od;
    Add(ListUnder, ListAdd);
  od;
  return rec(SEQE:=ListFaces, ListAbove:=ListAbove, ListUnder:=ListUnder);
end;


#
# given a flag, we move the element in position i by changing it,
# while remaining a flag. Only one solution to the problem possibility.
FlagDisplacementLatticeSetting:=function(FlagEXT, nbEXT, FAC, iMov)
  local FlagEXTnew, LFAC, iFac, iExt, test, ListSET, ListLFAC, jMov, LSE;
  FlagEXTnew:=ShallowCopy(FlagEXT);
  if iMov=1 then
    FlagEXTnew[1]:=[Difference(FlagEXT[2],FlagEXT[1])[1]];
    return FlagEXTnew;
  fi;
  if iMov=Length(FlagEXT) then
    LFAC:=[];
    for iFac in [1..Length(FAC)]
    do
      iExt:=1;
      test:=true;
      while(iExt<=Length(FlagEXT[iMov-1]))
      do
        if not(FlagEXT[iMov-1][iExt] in FAC[iFac]) then
          test:=false;
          break;
        fi;
        iExt:=iExt+1;
      od;
      if test=true then
        Add(LFAC, iFac);
      fi;
    od;
    ListSET:=[[],[]];
    for iExt in [1..nbEXT]
    do
      if iExt in FAC[LFAC[1]] then
        AddSet(ListSET[1], iExt);
      fi;
      if iExt in FAC[LFAC[2]] then
        AddSet(ListSET[2], iExt);
      fi;
    od;
    if FlagEXT[iMov]=ListSET[1] then
      FlagEXTnew[iMov]:=ListSET[2];
      return FlagEXTnew;
    fi;
    if FlagEXT[iMov]=ListSET[2] then
      FlagEXTnew[iMov]:=ListSET[1];
      return FlagEXTnew;
    fi;
  fi;
  ListLFAC:=[[], []];
  for jMov in [1..2]
  do
    for iFac in [1..Length(FAC)]
    do
      iExt:=1;
      test:=true;
      while(iExt<=Length(FlagEXT[jMov+iMov-2]))
      do
        if not(FlagEXT[jMov+iMov-2][iExt] in FAC[iFac]) then
          test:=false;
          break;
        fi;
        iExt:=iExt+1;
      od;
      if test=true then
        Add(ListLFAC[jMov], iFac);
      fi;
    od;
  od;
  for iFac in Difference(ListLFAC[1], ListLFAC[2])
  do
    LSE:=[];
    for iExt in FlagEXT[iMov+1]
    do
      if iExt in FAC[iFac] then
        Add(LSE, iExt);
      fi;
    od;
    if LSE<>FlagEXT[iMov-1] then
      FlagEXTnew[iMov]:=LSE;
      return FlagEXTnew;
    fi;
  od;
end;









ListFlagOrbitLatticeSetting:=function(GroupEXT, ListFaces)
  local dimension, O, ListOrbitPrec, i, ListOrbitNew, eOrbPrec, eface, FlagNew;
  dimension:=Length(ListFaces);
  O:=Orbits(GroupEXT, [1..Length(ListFaces[1])]);
  ListOrbitPrec:=[];
  for i in [1..Length(O)]
  do
    Add(ListOrbitPrec, [[O[i][1]]]);
  od;
  for i in [2..dimension]
  do
    ListOrbitNew:=[];
    for eOrbPrec in ListOrbitPrec
    do
      for eface in ListFaces[i]
      do
        if IsSubset(eface, eOrbPrec[i-1])=true then
          FlagNew:=ShallowCopy(eOrbPrec);
          Add(FlagNew, eface);
          AddSet(ListOrbitNew, OnTuplesSetsCanonicalization(FlagNew, GroupEXT));
        fi;
      od;
    od;
    ListOrbitPrec:=ShallowCopy(ListOrbitNew);
    Print("For i=", i, "  one finds ", Length(ListOrbitPrec), " orbits\n");
  od;
  return ListOrbitNew;
end;






PetriePolygonLatticeSetting:=function(GroupEXT, ListFaces)
  local ListO, nRank, FuncDisplacement, GrpSize, FuncCanonicalization, FuncFindRepresentative;
  ListO:=ListFlagOrbitLatticeSetting(GroupEXT, ListFaces);
  nRank:=Length(ListO[1])+1;
  FuncDisplacement:=function(Flag, iMov)
    return FlagDisplacementLatticeSetting(Flag, Length(ListFaces[1]), ListFaces[nRank-1], iMov);
  end;
  GrpSize:=Order(GroupEXT);
  FuncCanonicalization:=function(Flag)
    return OnTuplesSetsCanonicalization(GroupEXT, Flag);
  end;
  FuncFindRepresentative:=function(Flag1, Flag2)
    return OnTuplesSetsRepresentativeAction(GroupEXT, Flag1, Flag2);
  end;
  return rec(FuncDisplacement:=FuncDisplacement, ListOrbitFlag:=ListO, nRank:=nRank, GrpSize:=GrpSize, FuncCanonicalization:=FuncCanonicalization, FuncFindRepresentative:=FuncFindRepresentative, FA:=OnTuplesSets);
end;





PetriePolygonPolytope:=function(GroupEXT, EXT, FAC)
  local ListO, nRank, FuncDisplacement, GrpSize, FuncCanonicalization, FuncFindRepresentative;
  ListO:=ListFlagOrbit(GroupEXT, EXT, FAC);
  nRank:=Length(ListO[1])+1;
  FuncDisplacement:=function(Flag, iMov)
    return FlagDisplacement(Flag, EXT, FAC, iMov);
  end;
  GrpSize:=Order(GroupEXT);
  FuncCanonicalization:=function(Flag)
    return OnTuplesSetsCanonicalization(GroupEXT, Flag);
  end;
  FuncFindRepresentative:=function(Flag1, Flag2)
    return OnTuplesSetsRepresentativeAction(GroupEXT, Flag1, Flag2);
  end;
  return rec(FuncDisplacement:=FuncDisplacement, ListOrbitFlag:=ListO, nRank:=nRank, GrpSize:=GrpSize, FuncCanonicalization:=FuncCanonicalization, FuncFindRepresentative:=FuncFindRepresentative, FA:=OnTuplesSets);
end;





CanonicalizationHasseList:=function(Flag, GroupEXT)
  local g, ReturnedFlag, GrpStab, iRank, O;
  ReturnedFlag:=ShallowCopy(Flag);
  GrpStab:=ShallowCopy(GroupEXT);
  for iRank in [1..Length(Flag)]
  do
    O:=Set(Orbit(GrpStab, ReturnedFlag[iRank], OnPoints));
    g:=RepresentativeAction(GrpStab, ReturnedFlag[iRank], O[1], OnPoints);
    ReturnedFlag:=OnTuples(ReturnedFlag, g);
    GrpStab:=Stabilizer(GrpStab, ReturnedFlag[iRank], OnPoints);
  od;
  return ReturnedFlag;
end;






ListFlagOrbitHasseList:=function(POS, GroupFace)
  local dimension, eO, ListOrbitPrec, i, ListOrbitNew, eOrbPrec, SumFace, eface, FlagNew;
  dimension:=Length(POS.Fvector);
  ListOrbitPrec:=[];
  for eO in Orbits(GroupFace, [1..POS.Fvector[1]], OnPoints)
  do
    Add(ListOrbitPrec, [Minimum(eO)]);
  od;
  SumFace:=POS.Fvector[1];
  for i in [2..dimension]
  do
    ListOrbitNew:=[];
    for eOrbPrec in ListOrbitPrec
    do
      for eface in [SumFace+1..SumFace+POS.Fvector[i]]
      do
        if Position(POS.ReducedHasseList, [eOrbPrec[i-1], eface])<>fail then
          FlagNew:=ShallowCopy(eOrbPrec);
          Add(FlagNew, eface);
          AddSet(ListOrbitNew, CanonicalizationHasseList(FlagNew, GroupFace));
        fi;
      od;
    od;
    ListOrbitPrec:=ShallowCopy(ListOrbitNew);
    Print("For i=", i, "  one finds ", Length(ListOrbitPrec), " orbits\n");
    SumFace:=SumFace+POS.Fvector[i];
  od;
  return ListOrbitNew;
end;



PetriePolygonGeneralPoset:=function(POS, GroupFace)
  local ListO, nRank, FuncDisplacement, GrpSize, FuncCanonicalization, FuncFindRepresentative;
  ListO:=ListFlagOrbitHasseList(POS, GroupFace);
  nRank:=Length(POS.Fvector)+1;
  FuncDisplacement:=function(Flag, iMov)
    local SumFace, i, test1, test2, FlagNew;
    SumFace:=0;
    for i in [1..iMov-1]
    do
      SumFace:=SumFace+POS.Fvector[i];
    od;
    for i in [SumFace+1..SumFace+POS.Fvector[iMov]]
    do
      if iMov=1 then
        test1:=true;
      else
        if Position(POS.ReducedHasseList, [Flag[iMov-1], i])<>fail then
          test1:=true;
        else
          test1:=false;
        fi;
      fi;
      if test1=true then
        if iMov=nRank-1 then
          test2:=true;
       else
          if Position(POS.ReducedHasseList, [i, Flag[iMov+1]])<>fail then
            test2:=true;
          else
            test2:=false;
          fi;
        fi;
        if test2=true and i<>Flag[iMov] then
          FlagNew:=ShallowCopy(Flag);
          FlagNew[iMov]:=i;
          return FlagNew;
        fi;
      fi;
    od;
  end;
  GrpSize:=Order(GroupFace);
  FuncCanonicalization:=function(Flag)
    return CanonicalizationHasseList(Flag, GroupFace);
  end;
  FuncFindRepresentative:=function(Flag1, Flag2)
    return RepresentativeAction(GroupFace, Flag1, Flag2, OnTuples);
  end;
  return rec(FuncDisplacement:=FuncDisplacement, ListOrbitFlag:=ListO, nRank:=nRank, GrpSize:=GrpSize, FuncCanonicalization:=FuncCanonicalization, FuncFindRepresentative:=FuncFindRepresentative, FA:=OnTuples);
end;








PetriePolygonGeneralSetting:=function(FlagFormalism)
  local ListO, FA, GrpSize, nRank, FuncSelfIntersection, FuncIntVectorLocalMethod, FuncMovement, FuncReverse, FlagNew, CreateZigZagFromFlag, ZigZagProlongation, ZigZagReversal, OrbitZigZagEnumeration, FuncZvector, FuncZvectorWithIntersection, ZigZagAction;
  GrpSize:=FlagFormalism.GrpSize;
  nRank:=FlagFormalism.nRank;
  FA:=FlagFormalism.FA;
  ListO:=FlagFormalism.ListOrbitFlag;
  FuncMovement:=function(Flag)
    local ipos;
    FlagNew:=ShallowCopy(Flag);
    for ipos in [1..nRank-1]
    do
      FlagNew:=FlagFormalism.FuncDisplacement(FlagNew, ipos);
    od;
    return FlagNew;
  end;
  FuncReverse:=function(Flag)
    local ipos, jpos;
    FlagNew:=ShallowCopy(Flag);
    for ipos in [1..nRank-2]
    do
      for jpos in Reversed([1..ipos])
      do
        FlagNew:=FlagFormalism.FuncDisplacement(FlagNew, jpos);
      od;
    od;
    return FlagNew;
  end;
  CreateZigZagFromFlag:=function(Flag)
    local FlagBegin, ListMatchedOrbitFlag, SequenceFlag, FlagCopy, FlagCan, g;
    FlagBegin:=FlagFormalism.FuncCanonicalization(Flag);
    ListMatchedOrbitFlag:=[FlagBegin];
    FlagCopy:=ShallowCopy(Flag);
    SequenceFlag:=[];
    repeat
      Add(SequenceFlag, FlagCopy);
      FlagCopy:=FuncMovement(FlagCopy);
      FlagCan:=FlagFormalism.FuncCanonicalization(FlagCopy);
      AddSet(ListMatchedOrbitFlag, FlagCan);
    until FlagCan=FlagBegin;
    g:=FlagFormalism.FuncFindRepresentative(Flag, FlagCopy);
    return rec(GroupRepresentative:=g, ListMatchedOrbitFlag:=ListMatchedOrbitFlag, FirstFlags:=SequenceFlag);
  end;
  ZigZagProlongation:=function(FirstFlags, g)
    local h, SequenceFlag, iFlag;
    h:=();
    SequenceFlag:=[];
    repeat
      for iFlag in [1..Length(FirstFlags)]
      do
        Add(SequenceFlag, FA(FirstFlags[iFlag], h));
      od;
      h:=h*g;
    until h=();
    return SequenceFlag;
  end;
  ZigZagAction:=function(ZigZag, g)
    local LSU, iFlag, LSnew, pos;
    LSU:=[];
    for iFlag in [1..Length(ZigZag)]
    do
      Add(LSU, FA(ZigZag[iFlag], g));
    od;
    pos:=Position(LSU, Minimum(LSU));
    LSnew:=[];
    for iFlag in [1..Length(ZigZag)]
    do
      Add(LSnew, LSU[pos]);
      pos:=NextIdx(Length(ZigZag), pos);
    od;
    return LSnew;
  end;


  ZigZagReversal:=function(ZigZag)
    local ZigZagRev, iFlag, ZR, iRank;
    ZigZagRev:=[];
    for iFlag in [1..Length(ZigZag)]
    do
      ZR:=[];
      for iRank in [1..nRank-1]
      do
        ZR[iRank]:=ZigZag[PrevKIdx(Length(ZigZag), iFlag, iRank-1)][iRank];
      od;
      Add(ZigZagRev, ZR);
    od;
    return Reversed(ZigZagRev);
  end;
  OrbitZigZagEnumeration:=function()
    local OrbitFlagStatus, ListOrbitZigZag, ZigZagSymbolicInformation, iOrb, eOrb, Zig, eO, len;
    OrbitFlagStatus:=[];
    ListOrbitZigZag:=[];
    ZigZagSymbolicInformation:=[];
    for iOrb in [1..Length(ListO)]
    do
      OrbitFlagStatus[iOrb]:=-1;
    od;
    for iOrb in [1..Length(ListO)]
    do
      eOrb:=ListO[iOrb];
      if OrbitFlagStatus[iOrb]=-1 then
        Zig:=CreateZigZagFromFlag(eOrb);
        for eO in Zig.ListMatchedOrbitFlag
        do
          OrbitFlagStatus[Position(ListO, eO)]:=0;
        od;
        len:=Order(Zig.GroupRepresentative);
        Add(ListOrbitZigZag, [len*Length(Zig.FirstFlags), GrpSize/(2*len)]);
        Add(ZigZagSymbolicInformation, Zig);
      fi;
    od;
    return rec(ListOrbitZigZag:=ListOrbitZigZag, ZigZagSymbolicInformation:=ZigZagSymbolicInformation);
  end;
  FuncSelfIntersection:=function(ZigZag, ZigZagRev, asked)
    local iFlag, NbTypeI, NbTypeII, rRev;
    NbTypeI:=0;
    NbTypeII:=0;
    for iFlag in [1..Length(ZigZag)]
    do
      rRev:=FlagFormalism.FuncDisplacement(ZigZag[iFlag], asked);
      if rRev in ZigZag then
        NbTypeI:=NbTypeI+1;
      elif rRev in ZigZagRev then
        NbTypeII:=NbTypeII+1;
      fi;
    od;
    return [NbTypeI, NbTypeII];
  end;
  FuncIntVectorLocalMethod:=function(ZigZag, ZigZagRev, asked)
    local ListStatus, NbTypeI, NbTypeII, iFlag, rRev, SelfInt, ListInt, ZigZagInt, ZigZagIntRev, jFlag, Zig, VCE;
    ListStatus:=[];
    NbTypeI:=0;
    NbTypeII:=0;
    for iFlag in [1..Length(ZigZag)]
    do
      rRev:=FlagFormalism.FuncDisplacement(ZigZag[iFlag], asked);
      if Position(ZigZag, rRev)<>fail then
        NbTypeI:=NbTypeI+1;
        ListStatus[iFlag]:=0;
      elif Position(ZigZagRev, rRev)<>fail then
        NbTypeII:=NbTypeII+1;
        ListStatus[iFlag]:=0;
      else
        ListStatus[iFlag]:=-1;
      fi;
    od;
    SelfInt:=[NbTypeI/2, NbTypeII/2];
    ListInt:=[];
    for iFlag in [1..Length(ZigZag)]
    do
      if ListStatus[iFlag]=-1 then
        rRev:=FlagFormalism.FuncDisplacement(ZigZag[iFlag], asked);
        Zig:=CreateZigZagFromFlag(rRev);
        ZigZagInt:=ZigZagProlongation(Zig.FirstFlags, Zig.GroupRepresentative);
        ZigZagIntRev:=ZigZagReversal(ZigZagInt);
        NbTypeI:=0;
        NbTypeII:=0;
        for jFlag in [1..Length(ZigZag)]
        do
          if ListStatus[jFlag]=-1 then
            rRev:=FlagFormalism.FuncDisplacement(ZigZag[jFlag], asked);
            if Position(ZigZagInt, rRev)<>fail then
              NbTypeI:=NbTypeI+1;
              ListStatus[jFlag]:=0;
            fi;
            if Position(ZigZagIntRev, rRev)<>fail then
              NbTypeII:=NbTypeII+1;
              ListStatus[jFlag]:=0;
            fi;
          fi;
        od;
        VCE:=[NbTypeI, NbTypeII];
        Sort(VCE);
        Add(ListInt, Concatenation("(", String(VCE[1]), ",", String(VCE[2]), ")"));
      fi;
    od;
    return rec(SelfInt:=SelfInt, ListInt:=ListInt);
  end;
  FuncZvector:=function(ListOrbitZigZag)
    local ListZsymbol, ListOcc, ListOccurence, eOrbZigZag, i;
    ListZsymbol:=[];
    ListOccurence:=[];
    for eOrbZigZag in ListOrbitZigZag.ListOrbitZigZag
    do
      Add(ListZsymbol, String(eOrbZigZag[1]));
      Add(ListOccurence, eOrbZigZag[2]);
    od;
    ListOcc:=Collected(ListZsymbol, ListOccurence);
    return SyncTextOccurrence(ListOcc);
  end;
  FuncZvectorWithIntersection:=function(ListOrbitZigZag, asked)
    local ListZsymbol, eOrbZigZag, ZigZag, ZigZagRev, INTE, nbZ, Sstring1, Sstring2, i, ListOcc, ListOccurence;
    ListZsymbol:=[];
    ListOccurence:=[];
    for eOrbZigZag in ListOrbitZigZag.ZigZagSymbolicInformation
    do
      ZigZag:=ZigZagProlongation(eOrbZigZag.FirstFlags, eOrbZigZag.GroupRepresentative);
      ZigZagRev:=ZigZagReversal(ZigZag);
      INTE:=FuncIntVectorLocalMethod(ZigZag, ZigZagRev, asked);
      nbZ:=GrpSize/(2*Order(eOrbZigZag.GroupRepresentative));
      if INTE.SelfInt<>[0,0] then
        Sstring1:=Concatenation(String(Length(ZigZag)), "_{", String(INTE.SelfInt[1]), ", ",  String(INTE.SelfInt[2]), "}");
      else
        Sstring1:=String(Length(ZigZag));
      fi;
      ListOcc:=Collected(INTE.ListInt, ListWithIdenticalEntries(Length(INTE.ListInt), 1));
      Sstring2:=SyncTextOccurrence(ListOcc);
      Add(ListZsymbol, [Sstring1, Sstring2]);
      Add(ListOccurence, nbZ);
    od;
    ListOcc:=Collected(ListZsymbol, ListOccurence);
    return ListOcc;
  end;
  return rec(FuncMovement:=FuncMovement,
             FuncReverse:=FuncReverse,
             OrbitZigZagEnumeration:=OrbitZigZagEnumeration, 
             FuncSelfIntersection:=FuncSelfIntersection,
             FuncIntVectorLocalMethod:=FuncIntVectorLocalMethod,
             FuncZvector:=FuncZvector,
             ZigZagReversal:=ZigZagReversal,
             ZigZagAction:=ZigZagAction,
             ZigZagProlongation:=ZigZagProlongation,
             FuncZvectorWithIntersection:=FuncZvectorWithIntersection);
end;







Rank3EulerianPosetToKgon:=function(Poset)
  local nRank, EltR, ListR, eSet, iRank, ListVertex, ListEdge, ListOrdVertex, ListOrdEdge, test, iVert, iEdge, iOrd;
  nRank:=RankOfPoset(Poset);
  EltR:=ElementRank(Poset);
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
  ListVertex:=ListR[1];
  ListEdge:=ListR[2];
  ListOrdVertex:=[ListVertex[1]];
  ListOrdEdge:=[];
  test:=1;
  for iVert in [2..Length(ListVertex)]
  do
    for iEdge in [1..Length(ListEdge)]
    do
      if test=1 and [ListVertex[1], ListEdge[iEdge]] in Poset and [ListVertex[iVert], ListEdge[iEdge]] in Poset then
        Add(ListOrdVertex, ListVertex[iVert]);
        Add(ListOrdEdge, ListEdge[iEdge]);
        test:=0;
      fi;
    od;
  od;
  for iOrd in [3..Length(ListVertex)]
  do
    test:=1;
    for iVert in [1..Length(ListVertex)]
    do
      for iEdge in [1..Length(ListEdge)]
      do
        if test=1 and [ListOrdVertex[iOrd-1], ListEdge[iEdge]] in Poset and [ListVertex[iVert], ListEdge[iEdge]] in Poset and ListVertex[iVert]<>ListOrdVertex[iOrd-1] and ListEdge[iEdge]<>ListOrdEdge[iOrd-2] then
          Add(ListOrdVertex, ListVertex[iVert]);
          Add(ListOrdEdge, ListEdge[iEdge]);
          test:=0;
        fi;
      od;
    od;
  od;
  Add(ListOrdEdge, Difference(ListEdge, ListOrdEdge)[1]);
  return rec(Vertex:=ListOrdVertex, Edge:=ListOrdEdge);
end;



#
#
# This procedure convert an Eulerian poset of Rank 4
# into a planar graph
Rank4EulerianPosetToPlanGraph:=function(Poset)
  local nRank, EltR, lowest, ListR, iRank, eSet, highest, ListClockwiseSolutionVertices, ListClockwiseSolutionFace, iVert, eVert, PosetEvert, ListEdge, ListStatusVertices, ListStatusFace, PlanGraphNew, ListOrdAdj, jVert, SolSvert, posV1, posV2, iFac, eFac, PosetEfac, SolSfac, posF1, posF2, nbTODO, iEdge, InterSec;

  EltR:=ElementRank(Poset);
#  Print("Find Basic informations\n");
  nRank:=RankOfPoset(Poset);
  lowest:=FindLowest(Poset);
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
  highest:=ListR[4][1];
  ListClockwiseSolutionVertices:=[];
  ListClockwiseSolutionFace:=[];
  for iVert in [1..Length(ListR[1])]
  do
    eVert:=ListR[1][iVert];
    PosetEvert:=BruhatInterval(Poset, eVert, highest);
    ListEdge:=Rank3EulerianPosetToKgon(PosetEvert).Vertex;
    Add(ListClockwiseSolutionVertices, ListEdge);
  od;
  for iFac in [1..Length(ListR[3])]
  do
    eFac:=ListR[3][iFac];
    PosetEfac:=BruhatInterval(Poset, lowest, eFac);
    ListEdge:=Rank3EulerianPosetToKgon(PosetEfac).Edge;
    Add(ListClockwiseSolutionFace, ListEdge);
  od;
  ListStatusVertices:=ListWithIdenticalEntries(Length(ListClockwiseSolutionVertices), -1);
  ListStatusVertices[1]:=0;
  ListStatusFace:=ListWithIdenticalEntries(Length(ListClockwiseSolutionFace), -1);
  nbTODO:=Length(ListClockwiseSolutionVertices)+Length(ListClockwiseSolutionFace)-1;
  while(nbTODO>0)
  do
    for iVert in [1..Length(ListClockwiseSolutionVertices)]
    do
      for iFac in [1..Length(ListClockwiseSolutionFace)]
      do
        SolSvert:=ListClockwiseSolutionVertices[iVert];
        SolSfac:=ListClockwiseSolutionFace[iFac];
        InterSec:=Intersection(Set(ListClockwiseSolutionVertices[iVert]), Set(ListClockwiseSolutionFace[iFac]));
        if ListStatusVertices[iVert]=0 and ListStatusFace[iFac]=-1 and Length(InterSec)=2 then
          posV1:=Position(SolSvert, InterSec[1]);
          posV2:=Position(SolSvert, InterSec[2]);
          if posV2=PrevIdx(Length(SolSvert), posV1) then
            InterSec:=Reversed(InterSec);
          fi;
          posF1:=Position(SolSfac, InterSec[1]);
          posF2:=Position(SolSfac, InterSec[2]);
          if posF2=NextIdx(Length(SolSfac), posF1) then
            ListClockwiseSolutionFace[iFac]:=Reversed(SolSfac);
          fi;
          ListStatusFace[iFac]:=0;
          nbTODO:=nbTODO-1;
        fi;
        if ListStatusVertices[iVert]=-1 and ListStatusFace[iFac]=0 and Length(InterSec)=2 then
          posF1:=Position(SolSfac, InterSec[1]);
          posF2:=Position(SolSfac, InterSec[2]);
          if posF2=NextIdx(Length(SolSfac), posF1) then
            InterSec:=Reversed(InterSec);
          fi;
          posV1:=Position(SolSvert, InterSec[1]);
          posV2:=Position(SolSvert, InterSec[2]);
          if posV2=PrevIdx(Length(SolSvert), posV1) then
            ListClockwiseSolutionVertices[iVert]:=Reversed(SolSvert);
          fi;
          ListStatusVertices[iVert]:=0;
          nbTODO:=nbTODO-1;
        fi;
      od;
    od;
  od;
  PlanGraphNew:=[];
  for iVert in [1..Length(ListClockwiseSolutionVertices)]
  do
    ListEdge:=ListClockwiseSolutionVertices[iVert];
    ListOrdAdj:=[];
    for iEdge in [1..Length(ListEdge)]
    do
      for jVert in [1..Length(ListR[1])]
      do
        if iVert<>jVert and [ListR[1][jVert], ListEdge[iEdge]] in Poset then
          Add(ListOrdAdj, jVert);
        fi;
      od;
    od;
    Add(PlanGraphNew, ListOrdAdj);
  od;
  return PlanGraphNew;
end;
