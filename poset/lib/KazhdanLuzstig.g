


#
#
#
# The Kazhdan Lusztig stuff 



FuncReturnUnk:=function(ListVert, Poset)
  local MatrixRpol, ListUnk, i, j;
  MatrixRpol:=NullMat(Length(ListVert), Length(ListVert));
  ListUnk:=[];
  for i in [1..Length(ListVert)]
  do
    for j in [1..Length(ListVert)]
    do
      if i=j then
        MatrixRpol[i][j]:=1;
      else
        if [ListVert[i],ListVert[j]] in Poset then
          MatrixRpol[i][j]:="unk";
          Add(ListUnk, [i,j]);
        else
          MatrixRpol[i][j]:=0;
        fi;
      fi;
    od;
  od;
  return rec(list:=ListUnk, matrix:=MatrixRpol);
end;






BruhatGraph:=function(Poset)
  local HasseList, nRank, lowest, highest, EltR, ListR, ListElement, iRank, eSet, SizePrev, SizeNext, eVert, fVert, Up_eVert, Below_fVert, eInc, a1, a2, b1, b2, BruhatList, nBruhat, iBruhat, Elt1, Elt2, iElt, Rk1, Rk2, NLU, uPair, bPair,
  ePath, fPath, ListRefinatedPath, len, ListPath, LastElt, ListIteration, NewListIteration, NewNewListIteration;


  HasseList:=PosetToHasseList(Poset);
  nRank:=RankOfPoset(Poset);
  EltR:=ElementRank(Poset);
  ListR:=[];
  ListElement:=[];
  for iRank in [1..nRank]
  do
    ListR[iRank]:=[];
  od;
  for eSet in EltR
  do
    if eSet[2]>0 then
      AddSet(ListR[eSet[2]], eSet[1]);
    fi;
    Add(ListElement, eSet[1]);
  od;
  lowest:=FindLowest(Poset);
  highest:=FindHighest(Poset);
  #
  #
  # computation
  SizePrev:=0;
  SizeNext:=Length(HasseList);
  while(SizePrev<SizeNext)
  do
#    Print("SizePrev=", SizePrev, "  SizeNext=", SizeNext, "\n");
    for eVert in ListElement
    do
      for fVert in ListElement
      do
        if [eVert,fVert] in Poset and not([eVert, fVert] in HasseList) then
          Up_eVert:=[];
          Below_fVert:=[];
          for eInc in HasseList
          do
            if eInc[1]=eVert and [eInc[2], fVert] in Poset then
              Add(Up_eVert, eInc[2]);
            fi;
            if eInc[2]=fVert and [eVert, eInc[1]] in Poset then
              Add(Below_fVert, eInc[1]);
            fi;
          od;
          if eVert=1 and fVert=20 then
#            Print("eVert=", eVert, "  fVert=", fVert, "\n");
#            Print("UP    eVert=", Up_eVert, "\n");
#            Print("BELOW fVert=", Below_fVert, "\n");
          fi;
          for uPair in Combinations(Up_eVert, 2)
          do
            for bPair in Combinations(Below_fVert, 2)
            do
              a1:=uPair[1];
              a2:=uPair[2];
              b1:=bPair[1];
              b2:=bPair[2];
              if [a1,b1] in HasseList and [a1, b2] in HasseList and [a2,b1] in HasseList and [a2,b2] in HasseList then
                AddSet(HasseList, [eVert, fVert]);
#                Print("uPair=", uPair, "  bPair=", bPair, "\n");
              fi;
            od;
          od;
        fi;
      od;
    od;
    SizePrev:=SizeNext;
    SizeNext:=Length(HasseList);
#    Print("SizePrev=", SizePrev, "  SizeNext=", SizeNext, "\n");
  od;
  #
  # refinating the results
  BruhatList:=[];
  if nRank mod 2=0 then
    nBruhat:=nRank/2;
  else
    nBruhat:=(nRank+1)/2;
  fi;
  for iBruhat in [1..nBruhat]
  do
    BruhatList[iBruhat]:=[];
  od;
  for eInc in HasseList
  do
    Elt1:=eInc[1];
    Elt2:=eInc[2];
    for iElt in [1..Length(EltR)]
    do
      eSet:=EltR[iElt];
      if eSet[1]=Elt1 then
        Rk1:=eSet[2];
      fi;
      if eSet[1]=Elt2 then
        Rk2:=eSet[2];
      fi;
    od;
    NLU:=(1+Rk2-Rk1)/2;
    Add(BruhatList[NLU], eInc);
  od;
  #
  # finding number of Bruhat Path
  ListIteration:=[[lowest]];
  ListPath:=[];
  for iRank in [1..nRank]
  do
#    Print("Beginning for loop\n");
#    Print("ListIteration=", ListIteration, "\n");
    NewListIteration:=[];
    for ePath in ListIteration
    do
      LastElt:=ePath[Length(ePath)];
      for eInc in HasseList
      do
        if eInc[1]=LastElt then
          fPath:=StructuralCopy(ePath);
          Add(fPath, eInc[2]);
          Add(NewListIteration, fPath);
        fi;
      od;
    od;
#    Print("ListIteration=", ListIteration, "\n");
#    Print("NewListIteration=", NewListIteration, "\n");
    NewNewListIteration:=[];
    for ePath in NewListIteration
    do
      if ePath[Length(ePath)]=highest then
        Add(ListPath, ePath);
      else
        Add(NewNewListIteration, ePath);
      fi;
    od;
    ListIteration:=StructuralCopy(NewNewListIteration);
#    Print("Ending for loop\n");
  od;
  #
  # refinating the list of Path
  ListRefinatedPath:=[];
  for iRank in [1..nRank]
  do
    ListRefinatedPath[iRank]:=[];
  od;
  for ePath in ListPath
  do
    len:=Length(ePath)-1;
    Add(ListRefinatedPath[len], ePath);
  od;
  return rec(BruhatGraph:=HasseList, BruhatList:=BruhatList, ListPath:=ListPath, ListRefinatedPath:=ListRefinatedPath);
end;










SearchSpecialMatching:=function(Poset)
  local HasseList, ListRanks, MaxRank, nbe, TotalListVert, Possibilities, FuncTestRelevance, iter, Pos, ePoss, ListVert, OthList, eInc, MinRank, Authorized, pos, eElt;
  HasseList:=PosetToHasseList(Poset);
  ListRanks:=ElementRank(Poset);
  MaxRank:=MaximalRank(ListRanks);
  TotalListVert:=ListOfVertices(Poset);
  nbe:=Length(TotalListVert)/2;
  Possibilities:=[[]];
  #
  FuncTestRelevance:=function(ePoss, AddInc)
    local fInc;
    for fInc in ePoss
    do
      if [fInc[1], AddInc[1]] in HasseList then
        if not([fInc[2], AddInc[2]] in Poset) then
          return false;
        fi;
      fi;
      if [fInc[1], AddInc[2]] in HasseList then
        if not([fInc[2], AddInc[1]] in Poset) then
          return false;
        fi;
      fi;
      if [fInc[2], AddInc[1]] in HasseList then
        if not([fInc[1], AddInc[2]] in Poset) then
          return false;
        fi;
      fi;
      if [fInc[2], AddInc[2]] in HasseList then
        if not([fInc[1], AddInc[1]] in Poset) then
          return false;
        fi;
      fi;
    od;
    return true;
  end;
  #
  for iter in [1..nbe]
  do
#    Print("Possibilities=", Possibilities, "\n");
    Pos:=[];
    for ePoss in Possibilities
    do
      ListVert:=[];
      for eInc in ePoss
      do
        AddSet(ListVert, eInc[1]);
        AddSet(ListVert, eInc[2]);
      od;
      OthList:=Difference(TotalListVert, ListVert);
      #
      MinRank:=MaxRank;
      for eElt in OthList
      do
        pos:=Position(TotalListVert, eElt);
        if ListRanks[pos][2]<MinRank then
          MinRank:=ListRanks[pos][2];
        fi;
      od;
      #
      Authorized:=[];
      for eElt in ListRanks
      do
        if eElt[2]=MinRank and eElt[1] in OthList then
          AddSet(Authorized, eElt[1]);
        fi;
      od;
      #
      for eInc in HasseList
      do
        if eInc[1] in Authorized and eInc[2] in OthList then
          if FuncTestRelevance(ePoss, eInc)=true then
            Add(Pos, Union(ePoss, [eInc]));
          fi;
        fi;
      od;
    od;
    Possibilities:=Set(Pos);
  od;
  #
  return Possibilities;
end;






R_polynomialSpecialMatching:=function(Poset)
  local ListVert, HasseList, nbV, MatrixRpol, ListUnk, i, j, lowest, ListSpecialMatching,  iVert, BruhatInt, eUnk, iU, iV, U, V, ListSolution, eSpec, eInc, MU, iMU, MV, iMV, ESU, q;
  q:=Indeterminate(Rationals, 1);
  ListVert:=ListOfVertices(Poset);
  HasseList:=PosetToHasseList(Poset);
  ESU:=FuncReturnUnk(ListVert,Poset);
  MatrixRpol:=ESU.matrix;
  ListUnk:=ESU.list;


  nbV:=Length(ListVert);
  lowest:=FindLowest(Poset);
  ListSpecialMatching:=[];
  for iVert in [1..Length(ListVert)]
  do
    if ListVert[iVert]<>lowest then
      BruhatInt:=BruhatInterval(Poset, lowest, ListVert[iVert]);
      ListSpecialMatching[iVert]:=SearchSpecialMatching(BruhatInt);
      if Length(ListSpecialMatching[iVert])=0 then
        Print("Error, no special matching found\n");
        return false;
      fi;
    else
      ListSpecialMatching[iVert]:=[];
    fi;
  od;
  while Length(ListUnk)>0
  do
    for eUnk in ListUnk
    do
      iU:=eUnk[1];
      iV:=eUnk[2];
      U:=ListVert[iU];
      V:=ListVert[iV];
      ListSolution:=[];
      for eSpec in ListSpecialMatching[iV]
      do
        for eInc in eSpec
        do
          if ListVert[iU] in eInc then
            MU:=Difference(eInc, [ListVert[iU]])[1];
            iMU:=Position(ListVert, MU);
          fi;
          if ListVert[iV] in eInc then
            MV:=Difference(eInc, [ListVert[iV]])[1];
            iMV:=Position(ListVert, MV);
          fi;
        od;
        if [MU,U] in HasseList then
          if MatrixRpol[iMU][iMV]<>"unk" then
            AddSet(ListSolution, MatrixRpol[iMU][iMV]);
          fi;
        else
          if MatrixRpol[iMU][iMV]<>"unk" and MatrixRpol[iU][iMV]<>"unk" then
            AddSet(ListSolution, q*MatrixRpol[iMU][iMV]+(q-1)*MatrixRpol[iU][iMV]);
          fi;
        fi;
      od;
      if Length(ListSolution)>1 then
        Print("Error, method give incoherent results\n");
        return false;
      fi;
      if Length(ListSolution)=1 then
        MatrixRpol[iU][iV]:=ListSolution[1];
        ListUnk:=Difference(ListUnk, [[iU, iV]]);
      fi;
    od;
  od;
  return MatrixRpol;
end;













#
# idea is to transform the poset by transforming a facet
# into a vertex
FuncDegenerescence:=function(Poset, facet)
  local lowest, NewPoset, eInc;
  lowest:=FindLowest(Poset);
  NewPoset:=[];
  AddSet(NewPoset, [lowest, facet]);
  for eInc in Poset
  do
    if eInc[1]=lowest then
      if not([eInc[2], facet] in Poset) then
        AddSet(NewPoset, [eInc[1], eInc[2]]);
      fi;
    elif not([eInc[1], facet] in Poset) then
      if [eInc[2],facet] in Poset then
        AddSet(NewPoset, [eInc[1], facet]);
      else
        AddSet(NewPoset, [eInc[1], eInc[2]]);
      fi;
    else
      if not([eInc[2], facet] in Poset) and facet<>eInc[2] then
        AddSet(NewPoset, [facet, eInc[2]]);
      fi;
    fi;
  od;
  return NewPoset;
end;


#
# 
# 
MeasureNonLatticeNess:=function(Poset)
  local ListVert, ListViol, iVert, jVert, BInt;
  ListVert:=ListOfVertices(Poset);
  ListViol:=[];
  for iVert in ListVert
  do
    for jVert in ListVert
    do
      if [iVert, jVert] in Poset then
        BInt:=BruhatInterval(Poset, iVert, jVert);
        if IsLattice(BInt)=false then
          Add(ListViol, [iVert, jVert]);
        fi;
      fi;
    od;
  od;
  return ListViol;
end;





#
# Idea is by G.Kalai
#
R_polynomialKalaiSpecialMatching:=function(Poset)
  local q, __RPOL, __RpolynomialPosetMaxRank4;
  q:=Indeterminate(Rationals, 1);
  __RpolynomialPosetMaxRank4:=function(Poset)
    local RkPoset, HasseList, ListRanks, ListR1, ListR2, eRank, ListUpDown, kVert, ListVert;
    RkPoset:=RankOfPoset(Poset);
    HasseList:=PosetToHasseList(Poset);
    ListRanks:=ElementRank(Poset);
    ListVert:=ListOfVertices(Poset);
    if RkPoset=1 then
      return 1;
    elif RkPoset=2 then
      return 1;
    elif RkPoset=3 then
      ListR1:=[];
      for eRank in ListRanks
      do
        if eRank[2]=2 then
          Add(ListR1, eRank[1]);
        fi;
      od;
      if Length(ListR1)=2 then
        return (q-1)^3+q*(q-1);
      else
        return (q-1)^3;
      fi;
    elif RkPoset=4 then
      ListR1:=[];
      ListR2:=[];
      for eRank in ListRanks
      do
        if eRank[2]=1 then
          ListUpDown:=[];
          for kVert in ListVert
          do
            if [eRank[1], kVert] in Poset then
              Add(ListUpDown, kVert);
            fi;
          od;
          if Length(ListUpDown)=2 then
            Add(ListR1, eRank[1]);
          fi;
        fi;
        if eRank[2]=3 then
          ListUpDown:=[];
          for kVert in ListVert
          do
            if [kVert, eRank[1]] in Poset then
              Add(ListUpDown, kVert);
            fi;
          od;
          if Length(ListUpDown)=2 then
            Add(ListR2, eRank[1]);
          fi;
        fi;
      od;
      return (q-1)^4+(Length(ListR1)+Length(ListR2))/2*q*(q-1)^2;
    fi;
  end;
  __RPOL:=function(Poset)
    local RkPoset, ListRanks, ListFacet, eRank, ListPossibilities, LIST, eSM, PosetDeg, eFacet, MeasureOrig, ListFacets;
    RkPoset:=RankOfPoset(Poset);
    if RkPoset<=4 then
      return __RpolynomialPosetMaxRank4(Poset);
    fi;
    ListRanks:=ElementRank(Poset);
    ListFacet:=[];
    for eRank in ListRanks
    do
      if eRank[2]=RkPoset-1 then
        Add(ListFacets, eRank[1]);
      fi;
    od;
    MeasureOrig:=MeasureNonLatticeNess(Poset);
    ListPossibilities:=[];
    for eFacet in ListFacet
    do
      PosetDeg:=FuncDegenerescence(Poset, eFacet);
      LIST:=SearchSpecialMatching(PosetDeg);
      for eSM in LIST
      do
        
      od;
    od;
    if Length(ListPossibilities)>1 then
      return false;
    else
      return ListPossibilities[1];
    fi;
  end;
  return __RPOL(Poset);
end;




FuncAddToListOcc:=function(List, OBJ, Symbol)
  local ListNew, eElt;
  ListNew:=List;
  for eElt in ListNew
  do
    if eElt[1]=OBJ then
      Add(eElt[2], Symbol);
      return ListNew;
    fi;
  od;
  Add(ListNew, [OBJ, [Symbol]]);
  return ListNew;
end;




#
#
#
# The symmetric group
# and its Bruhat order.
RpolynomialSymmetricGroupDescentMethod:=function(n)
  local ListElt, Grp, eElt, gElt, ReflectionSet, eRef, iRefl, Pos, LengthElt, RankSize, iRank, uPos, vPos, usPos, vsPos, MatrixRpol, LineRpol, ListUnk, eUnk, iElt, jElt, q;
  q:=Indeterminate(Rationals, 1);
  ListElt:=[];
  Grp:=SymmetricGroup([1..n]);
  for eElt in Grp
  do
    Add(ListElt, eElt);
  od;
  # 
  # 
  # The reflextion set
  ReflectionSet:=[];
  for iRefl in [1..n-1]
  do
    eElt:=(iRefl,iRefl+1);
    AddSet(ReflectionSet, Position(ListElt, eElt));
  od;
  #
  #
  # Building of the lengths set
  LengthElt:=[];
  for iElt in [1..Factorial(n)]
  do
    LengthElt[iElt]:=-1;
  od;
  Pos:=Position(ListElt, ());
  LengthElt[Pos]:=0;
  for eRef in ReflectionSet
  do
    LengthElt[eRef]:=1;
  od;

  RankSize:=n*(n-1)/2;
  for iRank in [2..RankSize]
  do
    for iElt in [1..Factorial(n)]
    do
      if LengthElt[iElt]=iRank-1 then
        for eRef in ReflectionSet
        do
          gElt:=Position(ListElt, ListElt[iElt]*ListElt[eRef]);
          if LengthElt[gElt]<>iRank-2 and LengthElt[gElt]<>iRank-1 then
            LengthElt[gElt]:=iRank;
          fi;
        od;
      fi;
    od;
  od;
  Print("LengthElt=", LengthElt, "\n");
  #
  #
  #
  ListUnk:=[];
  MatrixRpol:=[];
  for iElt in [1..Factorial(n)]
  do
    LineRpol:=[];
    for jElt in [1..Factorial(n)]
    do
      if iElt=jElt then
        Add(LineRpol, 1);
      elif LengthElt[iElt]>LengthElt[jElt] then
        Add(LineRpol, 0);
      else
        AddSet(ListUnk, [iElt, jElt]);
        Add(LineRpol, -1);
      fi;
    od;
    Add(MatrixRpol, LineRpol);
  od;
  while (Length(ListUnk)>1)
  do
    for eUnk in ListUnk
    do
      uPos:=eUnk[1];
      vPos:=eUnk[2];
      for eRef in ReflectionSet
      do
        usPos:=Position(ListElt, ListElt[uPos]*ListElt[eRef]);
        vsPos:=Position(ListElt, ListElt[vPos]*ListElt[eRef]);
        if LengthElt[vsPos]<LengthElt[vPos] then
          # We want s in D(v)
          if LengthElt[usPos]<LengthElt[uPos] then
            # We want s in D(u)
            if MatrixRpol[usPos][vsPos]<>-1 then
              MatrixRpol[uPos][vPos]:=MatrixRpol[usPos][vsPos];
              ListUnk:=Difference(ListUnk, [eUnk]);
            fi;
          else
            # We do not want s in D(u)
            if MatrixRpol[usPos][vsPos]<>-1 and MatrixRpol[uPos][vsPos]<>-1 then
              MatrixRpol[uPos][vPos]:=q*MatrixRpol[usPos][vsPos]+(q-1)*MatrixRpol[uPos][vsPos];
              ListUnk:=Difference(ListUnk, [eUnk]);
            fi;
          fi;
        fi;
      od;
    od;
    Print("Nb Unk=", Length(ListUnk), "\n");
  od;
  return rec(Names:=ListElt, Rpol:=MatrixRpol);
end;







#
#
# Constructions particular to the symmetric group
SymmetricTestBruhat:=function(Perm1, Perm2, nOrd)
  local i, j, List1, List2, Set1, Set2;
  List1:=OnTuples([1..nOrd], Perm1);
  List2:=OnTuples([1..nOrd], Perm2);
  for i in [1..nOrd-1]
  do
    Set1:=Set(List1{[1..i]});
    Set2:=Set(List2{[1..i]});
    for j in [1..i]
    do
      if Set1[j] > Set2[j] then
        return false;
      fi;
    od;
  od;
  return true;
end;

SymmetricRankBruhat:=function(Perm1, nOrd)
  local iCol, jCol, NbInv, List1;
  List1:=OnTuples([1..nOrd], Perm1);
  NbInv:=0;
  for iCol in [1..nOrd-1]
  do
    for jCol in [iCol+1..nOrd]
    do
      if List1[iCol]>List1[jCol] then
        NbInv:=NbInv+1;
      fi;
    od;
  od;
  return NbInv;
end;

#
#
# return the list of permutations just above a given permutation
# in the symmetric group
SymmetricJustAbove:=function(Perm1, nOrd)
  local iCol, jCol, SimpleRoot, fPerm, ListAbove, RankPerm;
  RankPerm:=SymmetricRankBruhat(Perm1, nOrd);
  ListAbove:=[];
  for iCol in [1..nOrd-1]
  do
    for jCol in [iCol+1..nOrd]
    do
      SimpleRoot:=(iCol, jCol);
      fPerm:=Perm1*SimpleRoot;
      if SymmetricRankBruhat(fPerm, nOrd)=RankPerm+1 then
        Add(ListAbove, fPerm);
      fi;
    od;
  od;
  return ListAbove;
end;


SymmetricEnumerationPair:=function(nOrd, nRank)
  local ListPoset, g1, LIST, iRank, vElt, Hset, BruhatPoset, iElt, jElt, sElt, Lelt, Lest;
  ListPoset:=[];
  for g1 in SymmetricGroup(nOrd)
  do
    LIST:=[[g1]];
    for iRank in [1..nRank]
    do
      Lest:=[];
      for vElt in LIST[iRank]
      do
        Lest:=Union(Lest, SymmetricJustAbove(vElt, nOrd));
      od;
      LIST[iRank+1]:=Lest;
    od;
    Hset:=[];
    for iRank in [2..nRank]
    do
      Hset:=Union(Hset, LIST[iRank]);
    od;
    for vElt in LIST[nRank+1]
    do
      Lelt:=Set([g1, vElt]);
      for sElt in Hset
      do
        if SymmetricTestBruhat(g1, sElt, nOrd)=true and SymmetricTestBruhat(sElt, vElt, nOrd)=true then
          Add(Lelt, sElt);
        fi;
      od;
      BruhatPoset:=[];
      for iElt in [1..Length(Lelt)]
      do
        for jElt in [1..Length(Lelt)]
        do
          if iElt<>jElt then
            if SymmetricTestBruhat(Lelt[iElt], Lelt[jElt], nOrd)=true then
              Add(BruhatPoset, [iElt, jElt]);
            fi;
          fi;
        od;
      od;
      Add(ListPoset, BruhatPoset);
      if IsEulerianPoset(BruhatPoset)=false then
        Print("Error, the poset is not Eulerian\n");
        Hset:=NullMat(5);
      fi;
    od;
  od;
  return ListPoset;
end;






#
#
# Construction of the Bruhat order on the symmetric group
PosetOfSymmetricGroup:=function(n)
  local ListElt, Grp, eElt, FuncTestBruhat, iElt, jElt, PosetList, HasseList, ListRanks;
  ListElt:=[];
  Grp:=SymmetricGroup([1..n]);
  for eElt in Grp
  do
    Add(ListElt, eElt);
  od;

  #
  #
  # computation of the Poset
  PosetList:=[];
  HasseList:=[];
  for iElt in [1..Length(ListElt)]
  do
    for jElt in [1..Length(ListElt)]
    do
      if iElt<> jElt then
        if SymmetricTestBruhat(ListElt[iElt], ListElt[jElt], n)=true then
          Add(PosetList, [iElt, jElt]);
          if SymmetricRankBruhat(ListElt[jElt], n)=SymmetricRankBruhat(ListElt[iElt], n)+1 then
            Add(HasseList, [iElt, jElt]);
          fi;
        fi;
      fi;
    od;
  od;
  ListRanks:=[];
  for iElt in [1..Length(ListElt)]
  do
    ListRanks[iElt]:=SymmetricRankBruhat(ListElt[iElt], n);
  od;
  return rec(Names:=ListElt, Poset:=PosetList, ListRanks:=ListRanks, HasseList:=HasseList);
end;




#
#
# Given an Fvector and a poset, we search the value 
# of this generalized Fvector for the poset.
SolutionSetFvector:=function(Poset, Fvector)
  local ListRanks, nRank, ListByRank, iRank, eElt, fElt, lowest, SolutionSet, nbTrans, iTrans, NewSolutionSet, eSol, HighInSol, ValTrans, fSol, nbFound;
  ListRanks:=ElementRank(Poset);
  nRank:=Fvector[Length(Fvector)];
  ListByRank:=[];
  for iRank in [1..nRank+1]
  do
    ListByRank[iRank]:=[];
  od;
  for eElt in ListRanks
  do
    Add(ListByRank[eElt[2]+1], eElt[1]);
  od;
  lowest:=ListByRank[1][1];
  SolutionSet:=[[lowest]];
  nbTrans:=(Length(Fvector)-1)/2;
  for iTrans in [1..nbTrans]
  do
    NewSolutionSet:=[];
    for eSol in SolutionSet
    do
      HighInSol:=eSol[Length(eSol)];
      ValTrans:=Fvector[2*iTrans+1];
      for eElt in ListByRank[ValTrans+1]
      do
        if [HighInSol,eElt] in Poset then
          fSol:=StructuralCopy(eSol);
          Add(fSol, eElt);
          if Fvector[2*iTrans]="-" then
            nbFound:=0;
            for fElt in ListByRank[ValTrans-1]
            do
              if ([HighInSol,fElt] in Poset) and ([fElt,eElt] in Poset) then
                nbFound:=nbFound+1;
              fi;
            od;
            if nbFound=2 then
              Add(NewSolutionSet, fSol);
            fi;
          else
            Add(NewSolutionSet, fSol);
          fi;
        fi;
      od;
    od;
    SolutionSet:=StructuralCopy(NewSolutionSet);
#    Print("SolutionSet=", SolutionSet, "\n");
  od;
  return SolutionSet;
end;
















FirstIdeaForRpolynomial:=function(Poset)
  local ListVert, HasseList, ListRanks, MaxRank, ValueRank, pos, ESU, MatrixRpol, ListUnk, ListLadder, eInc, iter, eSol, ListNewLadder, SeqX, SeqY, NewSeqX, NewSeqY, LastX, LastY, FirstX, FirstY, fInc, eUnk, iU, iV, U, V, ListSolution, eS, iFirstX, iFirstY, iLastX, iLastY, TrackListPossibleSolution, PossibleSolution, eLadder, q;
  q:=Indeterminate(Rationals, 1);
  ListVert:=ListOfVertices(Poset);
  HasseList:=PosetToHasseList(Poset);
  ListRanks:=ElementRank(Poset);
  MaxRank:=MaximalRank(ListRanks);
  ValueRank:=[];
  for eS in ListRanks
  do
    pos:=Position(ListVert, eS[1]);
    ValueRank[pos]:=eS[2];
  od;
  ESU:=FuncReturnUnk(ListVert,Poset);
  MatrixRpol:=ESU.matrix;
  ListUnk:=ESU.list;
  ListLadder:=[];
  for eInc in HasseList
  do
    AddSet(ListLadder, [[eInc[1]], [eInc[2]]]);
  od;
#  Print("ListLadder=", ListLadder, "\n");
  for iter in [1..MaxRank-1]
  do
    ListNewLadder:=[];
    for eSol in ListLadder
    do
      SeqX:=eSol[1];
      SeqY:=eSol[2];
      LastX:=SeqX[Length(SeqX)];
      LastY:=SeqY[Length(SeqY)];
      for eInc in HasseList
      do
        if eInc[1]=LastX and eInc[2]<>LastY  then
          for fInc in HasseList
          do
            if fInc[1]=LastY and [eInc[2],fInc[2]] in HasseList then
              NewSeqX:=ShallowCopy(SeqX);
              NewSeqY:=ShallowCopy(SeqY);
              NewSeqX[Length(SeqX)+1]:=eInc[2];
              NewSeqY[Length(SeqY)+1]:=fInc[2];
              AddSet(ListNewLadder, [NewSeqX, NewSeqY]);
            fi;
          od;
        fi;
      od;
    od;
    ListLadder:=Union(ListNewLadder, ListLadder);
#    Print("ListLadder=", ListLadder, "\n");
  od;


  while Length(ListUnk)>0
  do
    for eUnk in ListUnk
    do
      iU:=eUnk[1];
      iV:=eUnk[2];
      U:=ListVert[iU];
      V:=ListVert[iV];
      ListSolution:=[];
      TrackListPossibleSolution:=[];
      for eLadder in ListLadder
      do
        FirstX:=eLadder[1][1];
        FirstY:=eLadder[2][1];
        LastX:=eLadder[1][Length(eLadder[1])];
        LastY:=eLadder[2][Length(eLadder[2])];
        iFirstX:=Position(ListVert, FirstX);
        iFirstY:=Position(ListVert, FirstY);
        iLastX:=Position(ListVert, LastX);
        iLastY:=Position(ListVert, LastY);
        if FirstX=U and LastX=V and MatrixRpol[iFirstY][iLastY]<>"unk" then
          PossibleSolution:=MatrixRpol[iFirstY][iLastY];
          AddSet(ListSolution, PossibleSolution);
          FuncAddToListOcc(TrackListPossibleSolution, PossibleSolution, [eLadder, Concatenation("First Case", String(iFirstY),"-",String(iLastY))]);
        fi;
        if FirstY=U and LastY=V and MatrixRpol[iFirstX][iLastX]<>"unk" then
          PossibleSolution:=MatrixRpol[iFirstX][iLastX];
          AddSet(ListSolution, PossibleSolution);
          FuncAddToListOcc(TrackListPossibleSolution, PossibleSolution, [eLadder, Concatenation("Second Case", String(iFirstX),"-",String(iLastX))]);
        fi;
        if FirstX=U and LastY=V and MatrixRpol[iFirstY][iLastX]<>"unk" and MatrixRpol[iFirstX][iLastX]<>"unk" then
          PossibleSolution:=q*MatrixRpol[iFirstY][iLastX]+(q-1)*MatrixRpol[iFirstX][iLastX];
          AddSet(ListSolution, PossibleSolution);
          FuncAddToListOcc(TrackListPossibleSolution, PossibleSolution, [eLadder, Concatenation("Third Case", String(iFirstY),"-",String(iLastX))]);
        fi;
      od;
      if Length(ListSolution)>1 then
        Print("Error, method give incoherent results\n");
#        Print(TrackListPossibleSolution,"\n");
        Print("eUnk=", eUnk, "\n");
        Print("Proposed valueS are:\n");
        for eSol in TrackListPossibleSolution
        do
          Print("Solution=", eSol[1], " for ", eSol[2], "\n");
        od;
        return false;
      fi;
      if Length(ListSolution)=1 then
        MatrixRpol[iU][iV]:=ListSolution[1];
        ListUnk:=Difference(ListUnk, [[iU, iV]]);
      fi;
    od;
  od;
  return MatrixRpol;
end;



FGpolynomial:=function(Poset)
  local ListVert, ESU, MatrixFpol, MatrixGpol, ListUnk, ListRanks, ValueRank, eS, eUnk, iU, iV, U, V, test, nRNK, S, iZ, LS, Gpol, iDeg, pos, q;
  q:=Indeterminate(Rationals, 1);
  ListVert:=ListOfVertices(Poset);
  ESU:=FuncReturnUnk(ListVert,Poset);
  MatrixFpol:=ShallowCopy(ESU.matrix);
  MatrixGpol:=ShallowCopy(ESU.matrix);
  ListUnk:=ESU.list;
  ListRanks:=ElementRank(Poset);
  ValueRank:=[];
  for eS in ListRanks
  do
    pos:=Position(ListVert, eS[1]);
    ValueRank[pos]:=eS[2];
  od;
  while Length(ListUnk)>0
  do
    for eUnk in ListUnk
    do
      iU:=eUnk[1];
      iV:=eUnk[2];
      U:=ListVert[iU];
      V:=ListVert[iV];
      test:=1;
      nRNK:=ValueRank[iV]-ValueRank[iU]-1;
      S:=(q-1)^(nRNK);
      for iZ in [1..Length(ListVert)]
      do
        if [ListVert[iU],ListVert[iZ]] in Poset and [ListVert[iZ], ListVert[iV]] in Poset then
          if test=1 then
            if MatrixGpol[iU][iZ]="unk" then
              test:=0;
            else
              S:=S+MatrixGpol[iU][iZ]*(q-1)^(nRNK-(ValueRank[iZ]-ValueRank[iU]));
            fi;
          fi;
        fi;
      od;
      if test=1 then
        MatrixFpol[iU][iV]:=S;
        LS:=PolynomialCoefficientsOfPolynomial(S,q);
        Gpol:=LS[1];
        for iDeg in [1..nRNK]
        do
          if iDeg<=nRNK/2 then
            Gpol:=Gpol+(LS[iDeg+1]-LS[iDeg])*q^(iDeg);
          fi;
        od;
        MatrixGpol[iU][iV]:=Gpol;
        ListUnk:=Difference(ListUnk, [[iU, iV]]);
      fi;
    od;
  od;
  return rec(Fpoly:=MatrixFpol, Gpoly:=MatrixGpol);
end;






KazdanLuzstigPolynomial:=function(Poset, MatrixRpol)
  local ListVert, HasseList, ListRanks, ValueRank, eS, pos, nbV, ListUnk, MatrixKLpol, i, j, eUnk, iU, iV, U, V, test, S, iZ, LS, r, W, iDX, ESU, q;
  q:=Indeterminate(Rationals, 1);
  ListVert:=ListOfVertices(Poset);
  HasseList:=PosetToHasseList(Poset);
  ListRanks:=ElementRank(Poset);
  ValueRank:=[];
  for eS in ListRanks
  do
    pos:=Position(ListVert, eS[1]);
    ValueRank[pos]:=eS[2];
  od;
  #
  nbV:=Length(ListVert);
  ESU:=FuncReturnUnk(ListVert, Poset);
  MatrixKLpol:=ESU.matrix;
  ListUnk:=ESU.list;
  #
  while Length(ListUnk)>0
  do
    for eUnk in ListUnk
    do
      iU:=eUnk[1];
      iV:=eUnk[2];
      U:=ListVert[iU];
      V:=ListVert[iV];
      test:=1;
      S:=MatrixRpol[iU][iV];
      for iZ in [1..Length(ListVert)]
      do
        if [ListVert[iU],ListVert[iZ]] in Poset and [ListVert[iZ], ListVert[iV]] in Poset then
          if test=1 then
            if MatrixKLpol[iZ][iV]="unk" then
              test:=0;
            else
              S:=S+MatrixRpol[iU][iZ]*MatrixKLpol[iZ][iV];
            fi;
          fi;
        fi;
      od;
      if test=1 then
        r:=ValueRank[iV]-ValueRank[iU];
        LS:=PolynomialCoefficientsOfPolynomial(S,q);
        W:=0;
        for iDX in [0..r]
        do
          test:=LS[r-iDX+1]+LS[iDX+1];
          if LeadingCoefficient(test)<>0 then
            Print("r=",r,"\n");
            Print("iDX=",iDX,"\n");
            Print("LS=",LS,"\n");
            Print("S=",S,"\n");
            Print("Error in computing Kazdan Luztig polynomial\n");
            MatrixRpol:=NullMat(5);
            return false;
          fi;
          if iDX<r/2 then
            W:=W-LeadingCoefficient(LS[iDX+1])*q^iDX;
          fi;
        od;
        MatrixKLpol[iU][iV]:=W;
        ListUnk:=Difference(ListUnk, [[iU, iV]]);
      fi;
    od;
  od;
  return MatrixKLpol;
end;





ProductFvector:=function(Rel1, Rel2)
  local RankAdd, ESR, iS;
  RankAdd:=Rel1[Length(Rel1)];
  ESR:=[];
  for iS in [2..Length(Rel2)]
  do
    if (iS mod 2)=0 then
      Add(ESR, Rel2[iS]);
    else
      Add(ESR, Rel2[iS]+RankAdd);
    fi;
  od;
  return Concatenation(Rel1,ESR);
end;




#
#
# [] correspond to value $1$
# n is the rank of the poset
GenerateElement:=function(nRank)
  local iRank, LUK, ePart, LTriples, ePos, ESU, LtoAdd, ListOfGeneralizedFvector, SetS3, eS3, kPos, fPart, eFvector, TotalListOfRelations, Sign, VectorRelation, AddedPos, addFvector, pos, posPrev, posNext, posDashComma, iPos, nb, ChainLength, IsPolytope, Differ, DimFspace, Vbase, ListBase, ListRelations, Rnk, MatTransfert, C, iter, FindElt, VZ, iCol, jCol, FuncCanonicalize, ReducedMatrix, ReducedLine, Negatio, MinimalSubset, TotalLine, iC;
  IsPolytope:=false;
  ListOfGeneralizedFvector:=[[0,",",nRank]];
  if nRank=3 then
    Add(ListOfGeneralizedFvector, [0,"-",nRank]);
  fi;
  for iRank in [1..nRank-1]
  do
    LUK:=Reversed(Combinations([1..nRank-1],iRank));
    for ePart in LUK
    do
      fPart:=Concatenation([0],ePart, [nRank]);
      ChainLength:=iRank+2;	
#      Print("ePart=", ePart, "  fPart=", fPart, "\n");
      LTriples:=[];
      for ePos in [1..ChainLength-1]
      do
	if fPart[ePos+1]=fPart[ePos]+3 then
	  Add(LTriples, ePos);
	fi;
      od;
      if IsPolytope=true then
	SetS3:=[ListWithIdenticalEntries(ChainLength-1, 0)];
      else
	SetS3:=BuildSet(Length(LTriples), [0,1]);
      fi;
      for eS3 in SetS3
      do
	ESU:=ListWithIdenticalEntries(ChainLength-1, ",");
	for kPos in [1..Length(LTriples)]
	do
	  if eS3[kPos]=1 then
	    ESU[LTriples[kPos]]:="-";
	  fi;
	od;
	LtoAdd:=[];
#	Print("fPart=", fPart, "\n");
        for ePos in [1..ChainLength-1]
	do
	  Add(LtoAdd, fPart[ePos]);
	  Add(LtoAdd, ESU[ePos]);
	od;
	Add(LtoAdd, fPart[ChainLength]);
#	Print("iRank=", iRank, "\n");
#	Print("LtoAdd=", LtoAdd, "\n");
#	Print("------------------------------\n");
	Add(ListOfGeneralizedFvector, LtoAdd);
      od;
    od;
  od;
  #
  #
  # generation of all euler relations by 
  TotalListOfRelations:=[];
  for eFvector in ListOfGeneralizedFvector
  do
    nb:=(Length(eFvector)-1)/2;
    for iPos in [1..nb]
    do
      posDashComma:=2*iPos;
      posPrev:=2*iPos-1;
      posNext:=2*iPos+1;
      Differ:=eFvector[posNext]-eFvector[posPrev];
      if Differ>1 and eFvector[posDashComma]="," then
	VectorRelation:=ListWithIdenticalEntries(Length(ListOfGeneralizedFvector), 0);
	pos:=Position(ListOfGeneralizedFvector, eFvector);
	VectorRelation[pos]:=1+(-1)^Differ;
	Sign:=-1;
	for AddedPos in [eFvector[posPrev]+1..eFvector[posNext]-1]
	do
	  addFvector:=Concatenation(eFvector{[1..posPrev]},[",",AddedPos, ","], eFvector{[posNext..Length(eFvector)]});
	  pos:=Position(ListOfGeneralizedFvector, addFvector);
	  VectorRelation[pos]:=Sign;
	  Sign:=-Sign;
	od;
	Add(TotalListOfRelations, VectorRelation);
      fi;
    od;
  od;
  Rnk:=0;
  MinimalSubset:=[];
  for iter in [1..Length(TotalListOfRelations)]
  do
    if RankMat(Concatenation(MinimalSubset, [TotalListOfRelations[iter]]))>Rnk then
      Add(MinimalSubset, TotalListOfRelations[iter]);
      Rnk:=Rnk+1;
    fi;
  od;
#  Print("Total=", TotalListOfRelations,"\n");
#  Print("Minimal=", MinimalSubset, "\n");


  DimFspace:=Length(ListOfGeneralizedFvector)-RankMat(MinimalSubset);
  ListBase:=[];
  ListRelations:=StructuralCopy(MinimalSubset);
  Rnk:=RankMat(ListRelations);
  for iter in [1..DimFspace]
  do
    FindElt:=0;
    if Length(ListBase)=0 then
      iPos:=1;
    else
      iPos:=ListBase[Length(ListBase)]+1;
    fi;
    repeat
      VZ:=ListWithIdenticalEntries(Length(ListOfGeneralizedFvector), 0);
      VZ[iPos]:=1;
      if RankMat(Concatenation(ListRelations, [VZ]))>Rnk then
        FindElt:=iPos;
        Add(ListRelations, VZ);
        Rnk:=Rnk+1;
      else
        iPos:=iPos+1;
      fi;
    until FindElt<>0;
    AddSet(ListBase, FindElt);
  od;
  Negatio:=Difference([1..Length(ListOfGeneralizedFvector)], ListBase);
  ReducedMatrix:=[];
  for jCol in [1..Length(MinimalSubset)]
  do
    TotalLine:=MinimalSubset[jCol];
    ReducedLine:=[];
    for iC in [1..Length(ListOfGeneralizedFvector)]
    do
      if iC in Negatio then
	Add(ReducedLine, TotalLine[iC]);
      fi;
    od;
    Add(ReducedMatrix, ReducedLine);
  od;


  MatTransfert:=[];
  for iCol in [1..Length(ListOfGeneralizedFvector)]
  do
    if iCol in ListBase then
      VZ:=ListWithIdenticalEntries(Length(ListOfGeneralizedFvector), 0);
      Add(MatTransfert, VZ);
    else
      pos:=Position(Negatio, iCol);
      VZ:=ListWithIdenticalEntries(Length(Negatio), 0);
      VZ[pos]:=1;
      C:=SolutionMat(ReducedMatrix, VZ);
      VZ:=ListWithIdenticalEntries(Length(ListOfGeneralizedFvector), 0);
      for iCol in [1..Length(Negatio)]
      do
	VZ:=VZ+C[iCol]*MinimalSubset[iCol];
      od;
      Add(MatTransfert, VZ);
    fi;
  od;
#  Print("MatTransfert=", MatTransfert, "\n");
#  Vbase:=NullspaceMat(TransposedMat(TotalListOfRelations));
#  for iCol in [1..Length(Vbase)]
#  do
#    for jCol in [1..Length(TotalListOfRelations)]
#    do
#      Print("PS=", Vbase[iCol]*TotalListOfRelations[jCol], "\n");
#    od;
#  od;





  #
  #
  # FuncCanonicalize is a function that transform an expression
  # sum a_S f_{S}
  # written as a list [.......]
  # into something standart 
  # 
  # 
  FuncCanonicalize:=function(VectorPos)
    local iCol, U;
    U:=VectorPos;
    for iCol in [1..Length(ListOfGeneralizedFvector)]
    do
      U:=U-U[iCol]*MatTransfert[iCol];
    od;
    return U;
  end;

  return rec(Fvector:=ListOfGeneralizedFvector, DFspace:=DimFspace, ListEuler:=MinimalSubset, FunctionCanonicalize:=FuncCanonicalize, ListCoord:=ListBase);
end;



gpolTOhpol:=function(gpol, Fvector)
  local nRank, VZ, HCoeff, iCoeff, nb, pos;
  nRank:=Fvector[1][Length(Fvector[1])];
  pos:=Position(Fvector, [0,",",nRank]);
  VZ:=ListWithIdenticalEntries(Length(Fvector), 0);
  VZ[pos]:=1;
  HCoeff:=[VZ];
  for iCoeff in [2..Length(gpol)]
  do
    HCoeff[iCoeff]:=HCoeff[iCoeff-1]+gpol[iCoeff];
  od;
  nb:=Length(HCoeff);
  if (nRank mod 2)=0 then
    for iCoeff in [1..Length(HCoeff)]
    do
      HCoeff[iCoeff+nb]:=HCoeff[nb+1-iCoeff];
    od;
  else
    for iCoeff in [1..Length(HCoeff)-1]
    do
      HCoeff[iCoeff+nb]:=HCoeff[nb-iCoeff];
    od;
  fi;
  return HCoeff;
end;


PolToSk:=function(OnePolynomial)
  local LS, ExprSk, i, hConst, q;
  q:=Indeterminate(Rationals, 1);
  LS:=PolynomialCoefficientsOfPolynomial(OnePolynomial,q);
  if Length(LS) mod 2=0 then
    hConst:=Length(LS)/2;
    ExprSk:=[];
    for i in [1..hConst]
    do
      ExprSk[i]:=-LeadingCoefficient(LS[i]);
    od;
  else
    hConst:=(Length(LS)+1)/2;
    ExprSk:=[];
    for i in [1..hConst]
    do
      ExprSk[i]:=LeadingCoefficient(LS[i]);
    od;
  fi;
  return ExprSk;
end;





ReduceFvector:=function(eFvector)
  local newFvector, iPos;
  newFvector:=[eFvector[1]];
  iPos:=1;
  repeat
    if eFvector[iPos+2]=eFvector[iPos] then
      iPos:=iPos+2;
    else
      Add(newFvector, eFvector[iPos+1]);
      Add(newFvector, eFvector[iPos+2]);
      iPos:=iPos+2;
    fi;
  until iPos=Length(eFvector);
  return newFvector;
end;



#
#
# This function takes a given Fvector and returns the 
# reverse of this Fvector.
ReverseFvector:=function(Fvector)
  local len, nRank, hConst, newFvector, iCol;
  nRank:=Fvector[Length(Fvector)];
  len:=Length(Fvector);
  hConst:=(len-1)/2;
  newFvector:=[];
  for iCol in [1..hConst]
  do
    newFvector[2*iCol-1]:=nRank-Fvector[len+2-2*iCol];
    newFvector[2*iCol]:=Fvector[len+1-2*iCol];
  od;
  newFvector[len]:=nRank;
  return newFvector;
end;




#
# Consider a eulerian poset of rank n
# corresponding to a CW sphere S
# and consider the CW sphere Sx[0,1]
# then one can express f-vector of the new 
# in terms of f-vectors of the old one
TransformExpressions:=function(FvectorRankN, FvectorRankNminus1)
  local MatrixCorresp, iElt, eFvector, VectorZero, nbPossibleTrans, neweFvector, iCol, ReducedFvector, pos, iTrans;
  MatrixCorresp:=[];
  for iElt in [1..Length(FvectorRankN)]
  do
    eFvector:=FvectorRankN[iElt];
    VectorZero:=ListWithIdenticalEntries(Length(FvectorRankNminus1), 0);
    nbPossibleTrans:=(Length(eFvector)-1)/2;
    for iTrans in [1..nbPossibleTrans]
    do
      if eFvector[2*iTrans]="," then
	neweFvector:=[];
	for iCol in [1..2*iTrans]
	do
	  neweFvector[iCol]:=eFvector[iCol];
	od;
	for iCol in [2*iTrans+1..Length(eFvector)]
	do
	  if (iCol mod 2)=0 then
	    neweFvector[iCol]:=eFvector[iCol];
	  else
	    neweFvector[iCol]:=eFvector[iCol]-1;
	  fi;
	od;
	ReducedFvector:=ReduceFvector(neweFvector);
	pos:=Position(FvectorRankNminus1, ReducedFvector);
        if iTrans=1 then
	  if eFvector[3]-eFvector[1]>1 then
	    VectorZero[pos]:=VectorZero[pos]+1;
	  fi;
	else
	  VectorZero[pos]:=VectorZero[pos]+2;
	fi;
      fi;
    od;
    Add(MatrixCorresp, VectorZero);
  od;
  return MatrixCorresp;
end;


#
# The Kazhdan-Lusztig polynomial satisfy the formula
# KL(P x Q)=KL(P).KL(Q)
# what we do here is to consider the simpler product KL(P x single)=K(P)
# with single the unique eulerian poset of rank 1.
# we express the generalized F-vector of the product "P x single" in
# terms of generalized F-vector of P.
TransformExpressionsSecond:=function(FvectorRankN, FvectorRankNminus1)
  local MatrixCorresp, iElt, eFvector, VectorZero, nbPossibleTrans, neweFvector, iCol, ReducedFvector, pos, iTrans;
  MatrixCorresp:=[];
  for iElt in [1..Length(FvectorRankN)]
  do
    eFvector:=FvectorRankN[iElt];
    VectorZero:=ListWithIdenticalEntries(Length(FvectorRankNminus1), 0);
    nbPossibleTrans:=(Length(eFvector)-1)/2;
    for iTrans in [1..nbPossibleTrans]
    do
      if eFvector[2*iTrans]="," then
	neweFvector:=[];
	for iCol in [1..2*iTrans]
	do
	  neweFvector[iCol]:=eFvector[iCol];
	od;
	for iCol in [2*iTrans+1..Length(eFvector)]
	do
	  if (iCol mod 2)=0 then
	    neweFvector[iCol]:=eFvector[iCol];
	  else
	    neweFvector[iCol]:=eFvector[iCol]-1;
	  fi;
	od;
#	Print("neweFvector=", neweFvector, "\n");
	ReducedFvector:=ReduceFvector(neweFvector);
	pos:=Position(FvectorRankNminus1, ReducedFvector);
	VectorZero[pos]:=VectorZero[pos]+1;
      fi;
    od;
    Add(MatrixCorresp, VectorZero);
  od;
  return MatrixCorresp;
end;




LocalDualities:=function(Fvector)
  local ListDuals, nRank, nbTrans, iTrans, jTrans, val1, val2, LoDual, iPos;
  nRank:=Fvector[Length(Fvector)];
  nbTrans:=(Length(Fvector)+1)/2;
  ListDuals:=[];
  for iTrans in [1..nbTrans-1]
  do
    for jTrans in [iTrans+1..nbTrans]
    do
      if jTrans>iTrans+1 then
        LoDual:=[];
        for iPos in [1..iTrans-1]
        do
          Add(LoDual, Fvector[2*iPos-1]);
          Add(LoDual, Fvector[2*iPos]);
        od;
        val1:=Fvector[2*iTrans-1];
        val2:=Fvector[2*jTrans-1];

        for iPos in [2*iTrans-1..2*jTrans-1]
	do
	  if (iPos mod 2)=0 then
	    Add(LoDual, Fvector[2*(iTrans+jTrans)-2-iPos]);
	  else
	    Add(LoDual, val1+val2-Fvector[2*(iTrans+jTrans)-2-iPos]);
	  fi;
	od;
        for iPos in [jTrans+1..nbTrans]
        do
          Add(LoDual, Fvector[2*iPos-2]);
          Add(LoDual, Fvector[2*iPos-1]);
        od;
        Add(ListDuals, LoDual);
      fi;
    od;
  od;
  return ListDuals;
end;




PolToList:=function(Pol, undeter, degree)
  local LS, iCol, ListReturn;
  LS:=PolynomialCoefficientsOfPolynomial(Pol, undeter);
  ListReturn:=[];
  for iCol in [1..Length(LS)]
  do
    ListReturn[iCol]:=LeadingCoefficient(LS[iCol]);
  od;  
  for iCol in [Length(LS)+1..degree+1]
  do
    ListReturn[iCol]:=0;
  od;  
  return ListReturn;
end;




#
#
# The family of polynomials
# P_k = q^k (q-1)^(n-2k) with 0 <= k <= n/2
# is expressed in terms of the family 
# S_k=q^(n-k)-q^k with 0 <= k <= (n-1)/2 if n is odd
# S_k=q^(n-k)+q^k with 0 <= k < n/2     
# S_{n/2}=q^{n/2} if k=n/2              if n is even
MatrixPolynom:=function(nRank)
  local MatrixFamily, Pk, LS, eLine, iL, NbCoeff, k, q;
  q:=Indeterminate(Rationals, 1);
  MatrixFamily:=[];
  if nRank mod 2=0 then
    NbCoeff:=(nRank)/2;
  else
    NbCoeff:=(nRank-1)/2;
  fi;
  for k in [0..NbCoeff]
  do
    Pk:=q^(k)*(q-1)^(nRank-2*k);
    LS:=PolToList(Pk, q, nRank);
    eLine:=[];
    for iL in [0..NbCoeff]
    do
      eLine[iL+1]:=LS[nRank+1-iL]; 
    od;
    Add(MatrixFamily, eLine);
  od;
  return MatrixFamily;
end;


ExpressionSkToPk:=function(ExprSk, nRank)
  local n, Zmatr, ExprPk, iCoeff, iCol, U;
  ExprPk:=[];
  Zmatr:=Inverse(MatrixPolynom(nRank));
  n:=Length(ExprSk);
  for iCoeff in [1..n]
  do
    U:=0;
    for iCol in [1..n]
    do
      U:=U+Zmatr[iCol][iCoeff]*ExprSk[iCol];
    od;
    Add(ExprPk, U);
  od;
  return ExprPk;
end;

ExpressionPkToSk:=function(ExprPk, nRank)
  local n, ExprSk, Zmatr, iCoeff, iCol, U;
  ExprSk:=[];
  Zmatr:=MatrixPolynom(nRank);
  n:=Length(ExprPk);
  for iCoeff in [1..n]
  do
    U:=0;
    for iCol in [1..n]
    do
      U:=U+Zmatr[iCol][iCoeff]*ExprPk[iCol];
    od;
    Add(ExprSk, U);
  od;
  return ExprSk;
end;






FunctionTranslationFvector:=function(FvectorSymbol, Fvector)
  local ChainRet, iCol, iPos, eSymbFvector, iC, hConst;
  ChainRet:="";
  iPos:=0;
  for iCol in [1..Length(Fvector)]
  do
    if Fvector[iCol]<>0 then
      iPos:=iPos+1;
      if Fvector[iCol]=-1 then
        ChainRet:=Concatenation(ChainRet, "-");
      elif Fvector[iCol]=1 then
        if iPos>1 then
          ChainRet:=Concatenation(ChainRet, "+");
        fi;
      elif Fvector[iCol]<0 then
        ChainRet:=Concatenation(ChainRet, String(Fvector[iCol]));
      elif Fvector[iCol]>0 then
        if iPos>1 then
          ChainRet:=Concatenation(ChainRet, "+");
        fi;
        ChainRet:=Concatenation(ChainRet, String(Fvector[iCol]));
      fi;
      ChainRet:=Concatenation(ChainRet, "f^*_{");
      eSymbFvector:=FvectorSymbol[iCol];
      hConst:=(Length(eSymbFvector)-1)/2;
      for iC in [1..hConst]
      do
        ChainRet:=Concatenation(ChainRet,  String(eSymbFvector[2*iC-1]), eSymbFvector[2*iC]);
      od;
      ChainRet:=Concatenation(ChainRet,  String(eSymbFvector[2*hConst+1]));
      ChainRet:=Concatenation(ChainRet,  "}");
    fi;
  od;
  return ChainRet;
end;

























#
#
# The R-pol are written as 
# a0*(q-1)^s+a1*q(q-1)^(s-2)+a2*q^2*(q-1)^{s-4}+\dots+a_h q^h(q-1)^{s-2h}
# The KL-pol are written as
# b0+b1q+\dots+b_h q^h
# and the a_i, b_i are expressed in terms of the Generalized Fvector
#
# The Kazhdan-Lusztig polynomial are defined by the relation
# q^{Rnk}P_{0,1}(1/q)-P_{0,1}(q)-R_{0,1}(q)=\sum_{0<z<1}R_{0,z}KL_{z,1}
#
# The computation of general Kazhdan Lusztig formula
# for all nRank positive.
GeneralKazhdanLusztigFormula:=function(nRank)
  local q, ExprRpol, ExprKLpol, DSI, pos, pos1, pos2, V1, V2, iCoeff, nb, HnewPol, Hpol, gpol, UINF, FvectorDimMinusOne, invZmatr, Zmatr, VectorZero, iH, iCol, hConst, ListCoeffWinXk, LS, VZ, ProdPol, iA, iB, LineCoeff_iA, LineCoeff_iB, iF, iS, FirstListFV, SecondListFV, ListAcoeff, ListBcoeff, iRank, Elt, Wtest, gnewPol, ListCoeffInOld, MatrixCorresp, iLine, eLineCoeff, HformulaRpolInOldInPk, ListCoeffRInOldCoordInSk, FuncRed, ListCoeffRInNewCoordPk,
  MatrixCorrespSecond, ListRminusKLinOldinPk, 
  iPos, jPos, ListEquations, Rnk, MinimalSubset, ListMatched, ListTotalRightTerms, ListSelectRightTerms, eLine, B,
  RW, jCol,
  KLpolInOldInSk, KLpolInOldInPk,
  ListCoeffWinOldInSk, KLformulaListEquations, HformulaListEquations, ListCoeffRInOldInSk, KLformulaRpolInOldInPk, 
  eDual, SelfDualityEquations, SelfDualityRightTerms, FV;
  if nRank=1 then
    return rec(Rpol:=[[1]], KLpol:=[[1]], Fvector:=[[0,",",1]]);
  fi;
  if nRank=2 then
    DSI:=GenerateElement(2);
    pos1:=Position(DSI.Fvector, [0,",",2]);
    V1:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
    V1[pos1]:=1;
    ExprRpol:=[V1];
    ExprKLpol:=[V1];
    return rec(Rpol:=ExprRpol, KLpol:=ExprKLpol, Fvector:=DSI.Fvector);
  fi;
  if nRank=3 then
    DSI:=GenerateElement(3);
    V1:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
    pos1:=Position(DSI.Fvector, [0,",",3]);
    V1[pos1]:=1;
    V2:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
    pos2:=Position(DSI.Fvector, [0,"-",3]);
    V2[pos2]:=1;
    ExprRpol:=[StructuralCopy(V1),StructuralCopy(V2)];
    #
    pos2:=Position(DSI.Fvector, [0,",",3]);
    V2[pos2]:=-3;
    pos2:=Position(DSI.Fvector, [0,",", 2,",", 3]);
    V2[pos2]:=1;
    pos2:=Position(DSI.Fvector, [0,"-",3]);
    V2[pos2]:=1;
    ExprKLpol:=[StructuralCopy(V1),StructuralCopy(V2)];
    return rec(Rpol:=ExprRpol, KLpol:=ExprKLpol, Fvector:=DSI.Fvector);
  fi;
  UINF:=[];
  for iRank in [1..nRank-1]
  do
    UINF[iRank]:=GeneralKazhdanLusztigFormula(iRank);
  od;
  DSI:=GenerateElement(nRank);
  ListCoeffWinXk:=[];
  for iCoeff in [0..nRank]
  do
    ListCoeffWinXk[iCoeff+1]:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
  od;
  for iRank in [1..nRank-1]
  do
    FirstListFV:=UINF[iRank].Fvector;
    SecondListFV:=UINF[nRank-iRank].Fvector;
    ListAcoeff:=UINF[iRank].Rpol;
    ListBcoeff:=UINF[nRank-iRank].KLpol;
    for iA in [0..Length(ListAcoeff)-1]
    do
      LineCoeff_iA:=ListAcoeff[iA+1];
      for iB in [0..Length(ListBcoeff)-1]
      do
	LineCoeff_iB:=ListBcoeff[iB+1];
	VectorZero:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
        for iF in [1..Length(FirstListFV)]
        do
          for iS in [1..Length(SecondListFV)]
          do
	    Elt:=ProductFvector(FirstListFV[iF], SecondListFV[iS]);
	    pos:=Position(DSI.Fvector, Elt);
	    VectorZero[pos]:=VectorZero[pos]+LineCoeff_iA[iF]*LineCoeff_iB[iS];
	  od;
	od;
	ProdPol:=(q-1)^(iRank-2*iA)*q^(iA)*q^(iB);
#	Print("ProdPol=", ProdPol, "\n");
#        Print("     VZ=", VectorZero, "\n");
	LS:=PolynomialCoefficientsOfPolynomial(ProdPol, q);
	for iCoeff in [1..Length(LS)]
	do
	  ListCoeffWinXk[iCoeff]:=ListCoeffWinXk[iCoeff]+LeadingCoefficient(LS[iCoeff])*VectorZero;
	od;
      od;
    od;
  od;
#  Print("ListCoeffWinXk=", ListCoeffWinXk, "\n");
  for iCoeff in [1..Length(ListCoeffWinXk)]
  do
    ListCoeffWinXk[iCoeff]:=DSI.FunctionCanonicalize(ListCoeffWinXk[iCoeff]);
  od;
#  Print("ListCoeffWinXk(Simpl)=", ListCoeffWinXk, "\n");
  if (nRank mod 2)=0 then
    #
    #
    # it is the straighforward case: just solve a linear system
    #

    #
    # we pose h=nRank/2
    # we find the coefficients by solving a linear system
    # LS must be equal to [a0,a1,....,ah,b0,...,b(h-1)]
    hConst:=nRank/2;
    Zmatr:=[];
    # The a_i
    for iH in [0..hConst]
    do
      ProdPol:=-(q-1)^(nRank-2*iH)*q^(iH);
      VZ:=ListWithIdenticalEntries(nRank+1, 0);
      LS:=PolynomialCoefficientsOfPolynomial(ProdPol, q);
      for iCoeff in [1..Length(LS)]
      do
	VZ[iCoeff]:=LeadingCoefficient(LS[iCoeff]);
      od;
      Add(Zmatr, VZ);
    od;
    for iH in [0..hConst-1]
    do
      ProdPol:=q^(nRank-iH)-q^(iH);
      VZ:=ListWithIdenticalEntries(nRank+1, 0);
      LS:=PolynomialCoefficientsOfPolynomial(ProdPol, q);
      for iCoeff in [1..Length(LS)]
      do
	VZ[iCoeff]:=LeadingCoefficient(LS[iCoeff]);
      od;
      Add(Zmatr, VZ);
    od;
    invZmatr:=Inverse(TransposedMat(Zmatr));
    ExprRpol:=[];
    for iH in [0..hConst]
    do
      VectorZero:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
      for iCol in [1..nRank+1]
      do
	VectorZero:=VectorZero+invZmatr[iH+1][iCol]*ListCoeffWinXk[iCol];
      od;
      VectorZero:=DSI.FunctionCanonicalize(VectorZero);
      Add(ExprRpol, VectorZero);
    od;
    ExprKLpol:=[];
    for iH in [0..hConst-1]
    do
      VectorZero:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
      for iCol in [1..nRank+1]
      do
	VectorZero:=VectorZero+invZmatr[iH+hConst+2][iCol]*ListCoeffWinXk[iCol];
      od;
      VectorZero:=DSI.FunctionCanonicalize(VectorZero);
      Add(ExprKLpol, VectorZero);
    od;
  else
  #
  #
  # The case that cause many challenging problems
  # The big goal is an expression of the R-polynomial.
  # in terms of the old variables



  #
  #
  #
  # First STEP: checking the sign condition
    hConst:=(nRank+1)/2;
    VectorZero:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
    for iCoeff in [1..hConst]
    do
      Wtest:=ListCoeffWinXk[iCoeff]+ListCoeffWinXk[nRank+2-iCoeff];
      if Wtest<>VectorZero then
	Print("Sign Error: Wtest=", Wtest, "\n");
	return false;
      fi;
    od;
    Print("Signs are ok\n");
  #
  #
  # 
  # Second STEP: The equations coming from H(P x [0,1])=H(P)(1+q)
    #
    #
    # first operation, construction of h-pol and do the product operation
    # and get the KL-pol of Px[0,1] with old variables.
    gpol:=UINF[nRank-1].KLpol;
    FvectorDimMinusOne:=UINF[nRank-1].Fvector;
    Hpol:=gpolTOhpol(gpol, FvectorDimMinusOne);
#    Print("gpol=", gpol, "\n");
#    Print("Hpol=", Hpol, "\n");
    HnewPol:=[Hpol[1]];
    for iCoeff in [2..nRank-1]
    do
      HnewPol[iCoeff]:=Hpol[iCoeff]+Hpol[iCoeff-1];
    od;
    HnewPol[nRank]:=Hpol[nRank-1];
    VectorZero:=ListWithIdenticalEntries(Length(FvectorDimMinusOne), 0);
    pos:=Position(FvectorDimMinusOne, [0,",",nRank-1]);
    VectorZero[pos]:=1;
    gnewPol:=[StructuralCopy(VectorZero)];
    for iCoeff in [2..hConst]
    do
      gnewPol[iCoeff]:=HnewPol[iCoeff]-HnewPol[iCoeff-1];
    od;
#    Print("HnewPol=", HnewPol, "\n");
#    Print("gnewPol=", gnewPol, "\n");
    #
    #
    # second operation, express ListCoeff in terms of old variables
    ListCoeffInOld:=[];
    MatrixCorresp:=TransformExpressions(DSI.Fvector, FvectorDimMinusOne);
    for iLine in [1..Length(ListCoeffWinXk)]
    do
      eLineCoeff:=ListCoeffWinXk[iLine];
      VectorZero:=ListWithIdenticalEntries(Length(FvectorDimMinusOne), 0);
      for iCoeff in [1..Length(DSI.Fvector)]
      do
        VectorZero:=VectorZero+eLineCoeff[iCoeff]*MatrixCorresp[iCoeff];
      od;
      Add(ListCoeffInOld, StructuralCopy(VectorZero));
    od;
#    Print("ListCoeffInOld=", ListCoeffInOld, "\n");
    #
    # third operation: finding the expression of the R-polynomial 
    # in old coordinates
    # and setting the Matrix and Right terms
    FuncRed:=GenerateElement(nRank-1).FunctionCanonicalize;
    ListCoeffRInOldCoordInSk:=[];
    for iCoeff in [1..hConst]
    do
      ListCoeffRInOldCoordInSk[iCoeff]:=FuncRed(gnewPol[iCoeff]+ListCoeffInOld[iCoeff]);
    od;
#    Print("ListCoeffRInOldCoordInSk=", ListCoeffRInOldCoordInSk, "\n");
    HformulaRpolInOldInPk:=ExpressionSkToPk(ListCoeffRInOldCoordInSk);
    HformulaListEquations:=[];
    for iLine in [1..Length(FvectorDimMinusOne)]
    do
      eLine:=[];
      for iCol in [1..Length(DSI.ListCoord)]
      do
        eLine[iCol]:=MatrixCorresp[DSI.ListCoord[iCol]][iLine];
      od;
      Add(HformulaListEquations, eLine);
    od;




  #
  #
  # THIRD STEP: find expression of KL(P x dash)=KL(P)
  # In old coordinates
    #
    #
    # first operation: find expression of q^{nRank}KL(1/q)-KL(q) in
    # terms of Pk and in old coordinates
    ListRminusKLinOldinPk:=[];
    Print("hConst      =", hConst, "\n");
    Print("Length KLpol=", Length(UINF[nRank-1].KLpol), "\n");
    KLpolInOldInSk:=Concatenation(UINF[nRank-1].KLpol, [ListWithIdenticalEntries(Length(FvectorDimMinusOne),0)]); # ADD one term to the polynomial

    #
    #
    # second operation: 
    #
    MatrixCorrespSecond:=TransformExpressionsSecond(DSI.Fvector, FvectorDimMinusOne);
    ListCoeffWinOldInSk:=[];
    for iLine in [1..hConst]
    do
      eLineCoeff:=ListCoeffWinXk[2+nRank-iLine];
      VectorZero:=ListWithIdenticalEntries(Length(FvectorDimMinusOne), 0);
      for iCoeff in [1..Length(DSI.Fvector)]
      do
        VectorZero:=VectorZero+eLineCoeff[iCoeff]*MatrixCorrespSecond[iCoeff];
      od;
      Add(ListCoeffWinOldInSk, StructuralCopy(VectorZero));
    od;
    ListCoeffRInOldInSk:=[];
    for iCoeff in [1..hConst]
    do
      ListCoeffRInOldInSk[iCoeff]:=FuncRed(KLpolInOldInSk[iCoeff]-ListCoeffWinOldInSk[iCoeff]);
    od;
    KLformulaRpolInOldInPk:=ExpressionSkToPk(ListCoeffRInOldInSk);
    Print("KLformulaRpolInOldInPk=", KLformulaRpolInOldInPk, "\n");
    #
    #
    # third operation: 
    #
    KLformulaListEquations:=[];
    for iLine in [1..Length(FvectorDimMinusOne)]
    do
      eLine:=[];
      for iCol in [1..Length(DSI.ListCoord)]
      do
        eLine[iCol]:=MatrixCorrespSecond[DSI.ListCoord[iCol]][iLine];
      od;
      Add(KLformulaListEquations, eLine);
    od;







  #
  #
  # FOURTH STEP: write the equation of self duality satisfied by 
  # the R-polynomial
    #
    #
    # first operation.
    SelfDualityEquations:=[]; # this enclose the self duality equations 
    for iPos in DSI.ListCoord
    do
      FV:=DSI.Fvector[iPos];
      for eDual in LocalDualities(FV)
      do
        jPos:=Position(DSI.Fvector, eDual);
        VectorZero:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
	VectorZero[iPos]:=VectorZero[iPos]+1;
	VectorZero[jPos]:=VectorZero[jPos]-1;
        VectorZero:=DSI.FunctionCanonicalize(VectorZero);
        Add(SelfDualityEquations, VectorZero{DSI.ListCoord});
      od;
    od;
    SelfDualityRightTerms:=ListWithIdenticalEntries(Length(SelfDualityEquations),0);



  #
  #
  # FIFTH STEP: The resolution of the linear system
  # and finding of the expression of R-pol and KL-pol.
    #
    # first operation: finding expression of R-polynomial in 
    # NEW coordinates



    #
    #
    # critical parameter to change.
    ListEquations:=Concatenation(SelfDualityEquations, HformulaListEquations);
    Print("Self Duality equations=", SelfDualityEquations, "\n");
    Rnk:=RankMat(ListEquations);
    if Rnk<Length(DSI.ListCoord) then
      Print("The rank is insufficient, need to search another method\n");
      Print("Rnk=", Rnk, "  nbUnk=", Length(DSI.ListCoord), "\n");
      B:=NullspaceMat(TransposedMat(ListEquations));
      VectorZero:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
      for iCol in [1..Length(DSI.ListCoord)]
      do
        VectorZero[DSI.ListCoord[iCol]]:=B[1][iCol];
      od;
      Print("Nullspace=", VectorZero, "\n");
      Print("Trs=", FunctionTranslationFvector(DSI.Fvector, VectorZero), "\n");
#      Print("Fvector=", DSI.Fvector, "\n");
      return false;
    fi;

    MinimalSubset:=[];
    ListMatched:=[];
    Rnk:=0;
    for iLine in [1..Length(ListEquations)]
    do
      if RankMat(Concatenation(MinimalSubset, [ListEquations[iLine]]))>Rnk then
        Add(MinimalSubset, ListEquations[iLine]);
        Rnk:=Rnk+1;
        Add(ListMatched, iLine);
      fi;
    od;
    ListCoeffRInNewCoordPk:=[];
    for iCoeff in [1..hConst]
    do
      #
      #
      # critical parameter to change.
      ListTotalRightTerms:=Concatenation(SelfDualityRightTerms, HformulaRpolInOldInPk[iCoeff]);
      ListSelectRightTerms:=ListTotalRightTerms{ListMatched};
      B:=SolutionMat(TransposedMat(MinimalSubset), ListSelectRightTerms);
      for iLine in [1..Length(ListEquations)]
      do
        if ListEquations[iLine]*B<>ListTotalRightTerms[iLine] then
	  Print("The system has no solution\n");
	  eDual:=NullMat(5);
	  return false;
        fi;
      od;
      VectorZero:=ListWithIdenticalEntries(Length(DSI.Fvector), 0);
      for iCol in [1..Length(DSI.ListCoord)]
      do
        VectorZero[DSI.ListCoord[iCol]]:=B[iCol];
      od;
      Add(ListCoeffRInNewCoordPk, VectorZero);
    od;
    Print("ListCoeffRInNewCoordPk=", ListCoeffRInNewCoordPk, "\n");
    ExprRpol:=ListCoeffRInNewCoordPk;


    #
    #
    # second operation, computation of the Kazhdan-Lusztig polynomial
    # in new coordinates
    RW:=StructuralCopy(ListCoeffWinXk);
    for iCol in [0..hConst-1]
    do
      ProdPol:=(q-1)^(nRank-2*iCol)*q^(iCol);
      LS:=PolynomialCoefficientsOfPolynomial(ProdPol, q);
      for jCol in [1..Length(LS)]
      do
        RW[jCol]:=RW[jCol]+LeadingCoefficient(LS[jCol])*ExprRpol[iCol+1];
      od;
    od;
    ExprKLpol:=[];
    for iCol in [1..hConst]
    do
      ExprKLpol[iCol]:=RW[nRank+2-iCol];
    od;
  fi;
  return rec(Rpol:=ExprRpol, KLpol:=ExprKLpol, Fvector:=DSI.Fvector);
end;
