FileGrpLinearSpaceEquivalence:=GetBinaryFilename("GRP_LinearSpace_Equivalence");
FileGrpLinearSpaceStabilizer:=GetBinaryFilename("GRP_LinearSpace_Stabilizer");


ReducePrimeMultiplicity:=function(TheValue)
    local ListInt, SetInt;
    if TheValue = 1 then
        return 1;
    fi;
    ListInt:=FactorsInt(TheValue);
    SetInt:=Set(ListInt);
    return Product(SetInt);
end;


GetRationalInvariant:=function(GRPmatr)
    local ListPrimes, eGen, TheDen, ListInt, SetInt;
    ListPrimes:=[];
    for eGen in GeneratorsOfGroup(GRPmatr)
    do
        if IsIntegralMat(eGen)=false then
            TheDen:=GetDenominatorMatrix(eGen);
            ListInt:=FactorsInt(TheDen);
            SetInt:=Set(ListInt);
            Append(ListPrimes, SetInt);
        fi;
    od;
    if Length(ListPrimes) = 0 then
        return 1;
    fi;
    return Product(Set(ListPrimes));
end;




CheapSmallGeneratingSet:=function(PermGRP)
    local ListGen, nGen, TheOrd, GetSmallGeneratingSet, CurrLGen, GRPsym, iter, ePermRand, ListGenRand, FoundLGen;
    ListGen:=GeneratorsOfGroup(PermGRP);
    nGen:=Length(ListGen);
    TheOrd:=Order(PermGRP);
    GetSmallGeneratingSet:=function(TheList)
        local CurrOrd, CurrLGen, eGen, TestLGen, TestGRP, TestOrd;
        CurrOrd:=1;
        CurrLGen:=[];
        for eGen in TheList
        do
            TestLGen:=Concatenation(CurrLGen, [eGen]);
            TestGRP:=Group(TestLGen);
            TestOrd:=Order(TestGRP);
            if TestOrd > CurrOrd then
                CurrOrd:=TestOrd;
                CurrLGen:=TestLGen;
                if CurrOrd=TheOrd then
                    return CurrLGen;
                fi;
            fi;
        od;
        Error("We should not reach that stage");
    end;
    CurrLGen:=ListGen;
    GRPsym:=SymmetricGroup(nGen);
    for iter in [1..20]
    do
        ePermRand:=Random(GRPsym);
        ListGenRand:=Permuted(ListGen, ePermRand);
        FoundLGen:=GetSmallGeneratingSet(ListGenRand);
        if Length(FoundLGen) < Length(CurrLGen) then
            CurrLGen:=FoundLGen;
        fi;
    od;
    return CurrLGen;
end;


LLLMatrixGroupReduction:=function(n, GRPmatr)
    local PosDefMat, LGen, eMat, eProd, eRec, Pmat, PmatInv, ListMatrNew, eMatNew;
#    Print("Begin of LLLMatrixGroupReduction\n");
    PosDefMat:=IdentityMat(n);
    LGen:=GeneratorsOfGroup(GRPmatr);
    for eMat in LGen
    do
        if eMat<>IdentityMat(n) then
            eProd:=eMat * TransposedMat(eMat);
            PosDefMat:=PosDefMat + eProd;
        fi;
    od;
    eRec:=LLLReducedGramMat(PosDefMat);
    Pmat:=eRec.transformation;
    PmatInv:=Inverse(Pmat);
    ListMatrNew:=[];
    for eMat in LGen
    do
        eMatNew:=Pmat * eMat * PmatInv;
        Add(ListMatrNew, eMatNew);
    od;
#    Print("End of LLLMatrixGroupReduction\n");
    return rec(GRPred:=Group(ListMatrNew), Pmat:=Pmat);
end;





LinearSpace_OutGroup_CPP:=function(n, GRPmatr, FileGRP)
    local ListGen, output, iGen, eGen;
    ListGen:=GeneratorsOfGroup(GRPmatr);
    if Length(ListGen)=0 then
        Add(ListGen, IdentityMat(n));
    fi;
    Print("|ListGen|=", Length(ListGen), "\n");
    #
    RemoveFileIfExist(FileGRP);
    output:=OutputTextFile(FileGRP, true);
    AppendTo(output, Length(ListGen), "\n");
    iGen:=0;
    for eGen in ListGen
    do
        iGen:=iGen+1;
        Print("iGen=", iGen, " / ", Length(ListGen), "\n");
        SYMPOL_PrintMatrixStream(output, eGen);
    od;
    CloseStream(output);
end;



LinearSpace_Equivalence_CPP:=function(GRPmatr, TheSpace1_pre, TheSpace2_pre)
    local n, FileGRP, FileSpace1, FileSpace2, FileResult, TheCommand, TheResult;
    n:=Length(TheSpace1_pre);
    FileGRP:=Filename(POLYHEDRAL_tmpdir,"LinearSpace_Equivalence.grp");
    FileSpace1:=Filename(POLYHEDRAL_tmpdir,"LinearSpace_Equivalence.space1");
    FileSpace2:=Filename(POLYHEDRAL_tmpdir,"LinearSpace_Equivalence.space2");
    FileResult:=Filename(POLYHEDRAL_tmpdir,"LinearSpace_Equivalence.result");
    Print("FileGRP    = ", FileGRP, "\n");
    Print("FileSpace1 = ", FileSpace1, "\n");
    Print("FileSpace2 = ", FileSpace2, "\n");
    RemoveFileIfExist(FileResult);
    LinearSpace_OutGroup_CPP(n, GRPmatr, FileGRP);
    SYMPOL_PrintMatrix(FileSpace1, TheSpace1_pre);
    SYMPOL_PrintMatrix(FileSpace2, TheSpace2_pre);
    #
    TheCommand:=Concatenation(FileGrpLinearSpaceEquivalence, " ", FileGRP, " ", FileSpace1, " ", FileSpace2, " ", FileResult);
    Print("TheCommand=", TheCommand, "\n");
    Exec(TheCommand);
    #
    TheResult:=ReadAsFunction(FileResult)();
    RemoveFileIfExist([FileGRP, FileSpace1, FileSpace2, FileResult]);
    return TheResult;
end;



LinearSpace_Stabilizer_CPP:=function(GRPmatr, TheSpace_pre)
    local n, FileGRP, FileSpace, FileResult, TheCommand, TheResult;
    n:=Length(TheSpace_pre);
    FileGRP:=Filename(POLYHEDRAL_tmpdir,"LinearSpace_Stabilizer.grp");
    FileSpace:=Filename(POLYHEDRAL_tmpdir,"LinearSpace_Stabilizer.space");
    FileResult:=Filename(POLYHEDRAL_tmpdir,"LinearSpace_Stabilizer.result");
    Print("FileGRP   = ", FileGRP, "\n");
    Print("FileSpace = ", FileSpace, "\n");
    RemoveFileIfExist(FileResult);
    LinearSpace_OutGroup_CPP(n, GRPmatr, FileGRP);
    SYMPOL_PrintMatrix(FileSpace, TheSpace_pre);
    #
    TheCommand:=Concatenation(FileGrpLinearSpaceStabilizer, " ", FileGRP, " ", FileSpace, " ", FileResult);
    Exec(TheCommand);
    #
    TheResult:=ReadAsFunction(FileResult)();
    RemoveFileIfExist([FileGRP, FileSpace, FileResult]);
    return TheResult;
end;





PermutedStabilizer:=function(TheGRP, eVect)
  local TheStab, Hset, eVal, ListIdx;
  TheStab:=ShallowCopy(TheGRP);
  Hset:=Set(eVect);
  for eVal in Hset
  do
    ListIdx:=Filtered([1..Length(eVect)], x->eVect[x]=eVal);
    TheStab:=Stabilizer(TheStab, ListIdx, OnSets);
  od;
  return TheStab;
end;

PermutedRepresentativeAction:=function(TheGRP, eVect1, eVect2)
  local TheStab, eVect1img, n, eSet1, eSet2, g, eVal, ListIdx1, ListIdx2, gT;
  eVect1img:=ShallowCopy(eVect1);
  n:=Length(eVect1);
  eSet1:=Set(eVect1);
  eSet2:=Set(eVect2);
  if eSet1<>eSet2 then
    return fail;
  fi;
  g:=();
  TheStab:=ShallowCopy(TheGRP);
  for eVal in eSet1
  do
    ListIdx1:=Filtered([1..n], x->eVect1img[x]=eVal);
    ListIdx2:=Filtered([1..n], x->eVect2[x]=eVal);
    gT:=RepresentativeAction(TheStab, ListIdx1, ListIdx2, OnSets);
    if gT=fail then
      return fail;
    fi;
    eVect1img:=Permuted(eVect1img, gT);
    g:=g*gT;
    if eVect1img=eVect2 then
      return g;
    fi;
    TheStab:=Stabilizer(TheStab, ListIdx2, OnSets);
  od;
end;



OnTuplesRepresentativeAction:=function(SymGrp, Tuple1, Tuple2)
  local Tuple1Second, GrpStab, eEltSearch, i, eGen;
  if Length(Tuple1)<>Length(Tuple2) then
    return fail;
  fi;
  Tuple1Second:=ShallowCopy(Tuple1);
  GrpStab:=ShallowCopy(SymGrp);
  eEltSearch:=();
  for i in [1..Length(Tuple1)]
  do
    eGen:=RepresentativeAction(GrpStab, Tuple1Second[i], Tuple2[i], OnPoints);
    if eGen=fail then
      return fail;
    fi;
    eEltSearch:=eEltSearch*eGen;
    Tuple1Second:=OnTuples(Tuple1Second, eGen);
    if Tuple1Second=Tuple2 then
      return eEltSearch;
    fi;
    GrpStab:=Stabilizer(GrpStab, Tuple1Second[i], OnPoints);
    GrpStab:=PersoGroupPerm(SmallGeneratingSet(GrpStab));
  od;
end;

OnTuplesStabilizer:=function(GRP, eTuple)
  local ReturnedStab, ePoint;
  ReturnedStab:=PersoGroupPerm(GeneratorsOfGroup(GRP));
  for ePoint in eTuple
  do
    ReturnedStab:=Stabilizer(ReturnedStab, ePoint, OnPoints);
  od;
  return ReturnedStab;
end;




IntersectionRightCoset:=function(cos1, cos2)
    local H1, H2, x1, x2, shift, sigma, LMoved_H1, LMoved_H2, LMoved_H12, LMoved_sigma, TheInt, LMoved_Int, set2, set1, eRepr, set2_img, set1_img, H1_sigma, H2_sigma, test, GRPtot, swap, eCos, rho, CosTest, diff12, diff21, fset1, fset2;
    # RightCoset(U,g) is actually U g.
    H1:=ActingDomain(cos1);
    H2:=ActingDomain(cos2);
    x1:=Representative(cos1);
    x2:=Representative(cos2);
    shift:=x1;
    sigma:=x2 * Inverse(x1);
    # Initial very easy check
    LMoved_H1:=MovedPoints(H1);
    LMoved_H2:=MovedPoints(H2);
    LMoved_H12:=Union(LMoved_H1, LMoved_H2);
    LMoved_sigma:=MovedPoints(sigma);
    if IsSubset(LMoved_H12, LMoved_sigma)=false then
        Print("Return case 1\n");
        return [];
    fi;
    # We pass it, now getting into the hard computation
    TheInt:=Intersection(H1, H2);
    LMoved_Int:=MovedPoints(TheInt);
    Print("TheInt=", TheInt, "\n");
    # Reducing as much as possible in advance
    while(true)
    do
        LMoved_H1:=MovedPoints(H1);
        LMoved_H2:=MovedPoints(H2);
        LMoved_H12:=Union(LMoved_H1, LMoved_H2);
        LMoved_sigma:=MovedPoints(sigma);
        # First exclusion case
        if IsSubset(LMoved_H12, LMoved_sigma)=false then
            Print("Return case 2\n");
            return [];
        fi;
        # Outcommented so far the code for the iterating.
        # Easy reductions: points that are moved by sigma outside of one group allow us to reduce the problem
        diff12:=Difference(LMoved_H1, LMoved_H2);
        diff21:=Difference(LMoved_H2, LMoved_H1);
        set2:=Intersection(diff21, LMoved_sigma);
        if Length(set2) > 0 then
            Print("Reduction case 1\n");
            set2_img:=OnTuples(set2, Inverse(sigma));
            eRepr:=RepresentativeAction(H2, set2, set2_img, OnTuples);
            if eRepr=fail then
                Print("Return case 3\n");
                return [];
            fi;
            sigma:=eRepr * sigma;
            if OnTuples(set2, sigma)<>set2 then
                Error("Preservation of set2 has failed");
            fi;
            H2:=Stabilizer(H2, set2, OnTuples);
            continue;
        fi;
        set1:=Intersection(diff12, LMoved_sigma);
        if Length(set1) > 0 then
            # int = (H1 \cap H2 sigma) shift
            #     = (H1 sigma^{-1} \cap H2) sigma shift
            #     = (stab(H1) repr sigma^{-1} \cap H2) sigma shift
            #     = (stab(H1) \cap H2 sigma repr^{-1} )    repr shift
            Print("Reduction case 2\n");
            set1_img:=OnTuples(set1, sigma);
            eRepr:=RepresentativeAction(H1, set1, set1_img, OnTuples);
            if eRepr=fail then
                Print("Return case 4\n");
                return [];
            fi;
            H1:=Stabilizer(H1, set1, OnTuples);
            sigma:=sigma * Inverse(eRepr);
            shift:=eRepr * shift;
            continue;
        fi;
        # easy termination criterion
        if sigma in H2 then
            Print("Return case 5\n");
            return RightCoset(TheInt, shift);
        fi;
        if sigma in H1 then
            # int = (H1 \cap H2 sigma) shift
            #     = (H1 sigma^{-1} \cap H2) sigma shift
            Print("Return case 6\n");
            return RightCoset(TheInt, sigma * shift);
        fi;
        # reduction on sets which is easy
        fset1:=Difference(LMoved_H1, Union(LMoved_H2, LMoved_sigma));
        if Length(fset1) > 0 then
            H1:=Stabilizer(H1, fset1, OnTuples);
            continue;
        fi;
        fset2:=Difference(LMoved_H2, Union(LMoved_H1, LMoved_sigma));
        if Length(fset2) > 0 then
            H2:=Stabilizer(H2, fset2, OnTuples);
            continue;
        fi;
        # More general but more expensive than previous check
        H1_sigma:=Group(Concatenation(GeneratorsOfGroup(H1), [sigma]));
        if IsSubgroup(H1_sigma, H2) = false then
            Print("Reduction case 3\n");
            H2:=Intersection(H1_sigma, H2);
            continue;
        fi;
        H2_sigma:=Group(Concatenation(GeneratorsOfGroup(H2), [sigma]));
        if IsSubgroup(H2_sigma, H1) = false then
            Print("Reduction case 4\n");
            H1:=Intersection(H2_sigma, H1);
            continue;
        fi;
        # No more reduction tricks available
        break;
    od;
    # A final termination criterion
    GRPtot:=Group(Concatenation(GeneratorsOfGroup(H1), GeneratorsOfGroup(H2)));
    test:=sigma in GRPtot;
    if test = false then
        Print("Return case 7\n");
        return [];
    fi;
    # We are now inspired by the algorithm from
    # Lazlo Babai, Coset Intersection in Moderately Exponential Time
    #
    # We use the algorithm from Page 10 of coset analysis and we reformulate
    # it here in order to avoid errors:
    # --- The naive algorithm for computing H1 \cap H2 sigma is to iterate
    # over elements of H1 and testing if one belongs to H2 sigma. If we find
    # one such z then the result is the coset RightCoset(TheInt, z). If not
    # then it is empty.
    # --- Since the result depends is independent of the cosets TheInt, what
    # we can do is iterate over the RightCosets(H1, TheInt). The algorithm is
    # the one of Proposition 3.2
    # for r in RightCosets(H1, TheInt)
    # do
    #   if r in H1 sigma then
    #     return RightCoset(TheInt, r shift)
    #   fi;
    # od;
    # --- The question is how to use AscendingChains between TheInt and H1.
    # The iteration over the conjugacy classes. We need to understand
    # Section 3.4 of the Babai paper.
    #
    # We select the smallest group for that computation in order to have
    # as few cosets
    if Order(H2) < Order(H1) then
        # int = (H1 \cap H2 sigma) shift
        #     = (H1 sigma^{-1} \cap H2) sigma shift
        Print("Reduction case 5\n");
        swap:=H1;
        H1:=H2;
        H2:=swap;
        shift:=sigma * shift;
        sigma:=Inverse(sigma);
    fi;
    # So now Order(H1) <= Order(H2)
    Print("Return case 8\n");
    CosTest:=RightCoset(H2, sigma);
    for eCos in RightCosets(H1, TheInt)
    do
        rho:=Representative(eCos);
        if rho in CosTest then
            return RightCoset(TheInt, rho * shift);
        fi;
    od;
    return [];
end;







OnTuplesCanonicalization:=function(GroupEXT, ListPts)
  local g, ReturnedTuple, GrpStab, iRank, TheMin;
  ReturnedTuple:=ShallowCopy(ListPts);
  GrpStab:=ShallowCopy(GroupEXT);
  for iRank in [1..Length(ListPts)]
  do
    TheMin:=Minimum(Orbit(GrpStab, ReturnedTuple[iRank], OnPoints));
    g:=RepresentativeAction(GrpStab, ReturnedTuple[iRank], TheMin, OnPoints);
    ReturnedTuple:=OnTuples(ReturnedTuple, g);
    GrpStab:=Stabilizer(GrpStab, ReturnedTuple[iRank], OnPoints);
  od;
  return ReturnedTuple;
end;

OnTuplesSetsStabilizer:=function(GRP, eTuple)
  local ReturnedStab, ListLen, ePerm, eTupleReord, eSet;
  ReturnedStab:=PersoGroupPerm(GeneratorsOfGroup(GRP));
  ListLen:=List(eTuple, Length);
  ePerm:=SortingPerm(ListLen);
  eTupleReord:=Permuted(eTuple, ePerm);
  for eSet in eTupleReord
  do
#    Print("|eSet|=", Length(eSet), "\n");
    ReturnedStab:=Stabilizer(ReturnedStab, eSet, OnSets);
#    Print("|ReturnedStab|=", Order(ReturnedStab), "\n");
  od;
  return ReturnedStab;
end;




OnTuplesSetsRepresentativeAction:=function(GroupEXT, FlagEXT1, FlagEXT2)
  local GroupElement, FlagPrev1, GrpStab, iRank, g;
  GroupElement:=();
  FlagPrev1:=ShallowCopy(FlagEXT1);
  GrpStab:=ShallowCopy(GroupEXT);
  for iRank in [1..Length(FlagEXT1)]
  do
    g:=RepresentativeAction(GrpStab, FlagPrev1[iRank], FlagEXT2[iRank], OnSets);
    if g=fail then
      return fail;
    fi;
    FlagPrev1:=OnTuplesSets(FlagPrev1, g);
    GrpStab:=Stabilizer(GrpStab, FlagPrev1[iRank], OnSets);
    GroupElement:=GroupElement*g;
  od;
  return GroupElement;
end;

OnTuplesSetsCanonicalization:=function(GroupEXT, ListSet)
  local g, ReturnedTuple, GrpStab, iRank, TheMin;
  ReturnedTuple:=ShallowCopy(ListSet);
  GrpStab:=ShallowCopy(GroupEXT);
  for iRank in [1..Length(ListSet)]
  do
    TheMin:=Minimum(Orbit(GrpStab, ReturnedTuple[iRank], OnSets));
    g:=RepresentativeAction(GrpStab, ReturnedTuple[iRank], TheMin, OnSets);
    ReturnedTuple:=OnTuplesSets(ReturnedTuple, g);
    GrpStab:=Stabilizer(GrpStab, ReturnedTuple[iRank], OnSets);
  od;
  return ReturnedTuple;
end;







OnSetsSetsRepresentativeAction:=function(GRP, eSetSet1, eSetSet2)
  local InitialCase, nbSet, WorkingCase, NextInTree, GoUpNextInTree, result;
  if Length(eSetSet1)<>Length(eSetSet2) then
    return fail;
  fi;
  nbSet:=Length(eSetSet1);
  WorkingCase:=rec(len:=0,
                   ListAssignment:=ListWithIdenticalEntries(nbSet, 0),
                   ListIndices:=ListWithIdenticalEntries(nbSet, 0),
                   ListCases:=[rec(g:=(), TheGrp:=PersoGroupPerm(GeneratorsOfGroup(GRP)))]);
  NextInTree:=function()
    local len, nbCase, eTrySet, TheDiff, idx, gRel, GRPrel, eSet2, h, RedGrp;
    len:=WorkingCase.len;
    nbCase:=len+1;
    eTrySet:=eSetSet1[nbCase];
    TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len]}));
    gRel:=WorkingCase.ListCases[nbCase].g;
    GRPrel:=WorkingCase.ListCases[nbCase].TheGrp;
    idx:=1;
    while(true)
    do
      eSet2:=OnSets(eTrySet, gRel);
      h:=RepresentativeAction(GRPrel, eSet2, eSetSet2[TheDiff[idx]], OnSets);
      if h<>fail then
        RedGrp:=Stabilizer(GRPrel, eSetSet2[TheDiff[idx]], OnSets);
        WorkingCase.ListCases[nbCase+1]:=rec(g:=gRel*h, TheGrp:=RedGrp);
        WorkingCase.len:=nbCase;
        WorkingCase.ListAssignment[nbCase]:=TheDiff[idx];
        WorkingCase.ListIndices[nbCase]:=idx;
        if nbCase=nbSet then
          return gRel*h;
        else
          return "unfinished";
        fi;
      fi;
      if idx=Length(TheDiff) then
        break;
      fi;
      idx:=idx+1;
    od;
    return GoUpNextInTree();
  end;
  GoUpNextInTree:=function()
    local len, nbCase, idx, TheDiff, eTrySet, gRel, GRPrel, eSet2, h, RedGrp;
    while(true)
    do
      if WorkingCase.len=0 then
        return fail;
      fi;
      len:=WorkingCase.len;
      nbCase:=len+1;
      idx:=WorkingCase.ListIndices[nbCase-1];
      TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len-1]}));
      eTrySet:=eSetSet1[len];
      gRel:=WorkingCase.ListCases[nbCase-1].g;
      GRPrel:=WorkingCase.ListCases[nbCase-1].TheGrp;
      while(true)
      do
        if idx=Length(TheDiff) then
          break;
        fi;
        idx:=idx+1;
        eSet2:=OnSets(eTrySet, gRel);
        h:=RepresentativeAction(GRPrel, eSet2, eSetSet2[TheDiff[idx]], OnSets);
        if h<>fail then
          RedGrp:=Stabilizer(GRPrel, eSetSet2[TheDiff[idx]], OnSets);
          WorkingCase.ListCases[nbCase]:=rec(g:=gRel*h, TheGrp:=RedGrp);
          WorkingCase.ListAssignment[nbCase-1]:=TheDiff[idx];
          WorkingCase.ListIndices[nbCase-1]:=idx;
          if nbCase=nbSet+1 then
            return gRel*h;
          else
            return "unfinished";
          fi;
        fi;
      od;
      WorkingCase.len:=len-1;
      Unbind(WorkingCase.ListCases[nbCase]);
      WorkingCase.ListAssignment[len]:=0;
      WorkingCase.ListIndices[len]:=0;
    od;
  end;
  while(true)
  do
    result:=NextInTree();
    if result=fail then
      return fail;
    fi;
    if result<>"unfinished" then
      if OnSetsSets(eSetSet1, result)<>eSetSet2 then
        Error("We have inconsistency in OnSetsSetsRepr..");
      fi;
      return result;
    fi;
  od;
end;




OnSetsSetsStabilizer:=function(GRP, eSetSet)
  local ListGens, eStab, GetGroupOnListSets, SoughtGroup, SetInducedGroup, NextInTree, GoUpNextInTree, FuncInsertSolvedCase, IsItASolvedCase, FuncInsertGenerators, nbSet, O, WorkingCase, result, ListSolvedCases, eGen;
  ListGens:=[];
  eStab:=Stabilizer(GRP, eSetSet, OnTuplesSets);
  GetGroupOnListSets:=function(ListGen)
    local NewListGens, eGen, eList;
    NewListGens:=[];
    for eGen in ListGen
    do
      eList:=List(eSetSet, x->Position(eSetSet, OnSets(x, eGen)));
      Add(NewListGens, PermList(eList));
    od;
    return PersoGroupPerm(NewListGens);
  end;
  Append(ListGens, GeneratorsOfGroup(eStab));
  SoughtGroup:=PersoGroupPerm(ListGens);
  SetInducedGroup:=GetGroupOnListSets(ListGens);
  ListSolvedCases:=[];
  FuncInsertSolvedCase:=function(eCase)
    local ListKept, iCase, fCase, iStatus, fSetRed, eRepr;
    ListKept:=[];
    for iCase in [1..Length(ListSolvedCases)]
    do
      fCase:=ListSolvedCases[iCase];
      iStatus:=1;
      if fCase.len>=eCase.len then
        fSetRed:=fCase.eList{[1..eCase.len]};
        eRepr:=RepresentativeAction(SetInducedGroup, fSetRed, eCase.eList, OnTuples);
        if eRepr<>fail then
          iStatus:=0;
        fi;
      fi;
      if iStatus=1 then
        Add(ListKept, iCase);
      fi;
    od;
    ListSolvedCases:=Concatenation(ListSolvedCases{ListKept}, [eCase]);
  end;
  IsItASolvedCase:=function(eCase)
    local fCase, fSetRed, eRepr;
    for fCase in ListSolvedCases
    do
      if fCase.len>=eCase.len then
        fSetRed:=fCase.eList{[1..eCase.len]};
        eRepr:=RepresentativeAction(SetInducedGroup, fSetRed, eCase.eList, OnTuples);
        if eRepr<>fail then
          return true;
        fi;
      fi;
    od;
    return false;
  end;
  FuncInsertGenerators:=function(eGen)
    if not(eGen in SoughtGroup) then
      Add(ListGens, eGen);
      SoughtGroup:=PersoGroupPerm(ListGens);
      SetInducedGroup:=GetGroupOnListSets(ListGens);
    fi;
  end;
  nbSet:=Length(eSetSet);
  WorkingCase:=rec(len:=0,
                   ListAssignment:=ListWithIdenticalEntries(nbSet, 0),
                   ListIndices:=ListWithIdenticalEntries(nbSet, 0),
                   ListCases:=[rec(g:=(), TheGrp:=PersoGroupPerm(GeneratorsOfGroup(GRP)))]);
  NextInTree:=function()
    local len, nbCase, eTrySet, TheDiff, idx, gRel, GRPrel, eSet2, h, RedGrp, eCase;
    len:=WorkingCase.len;
    if len=nbSet then
      return GoUpNextInTree();
    fi;
    nbCase:=len+1;
    eCase:=rec(len:=WorkingCase.len, eList:=WorkingCase.ListAssignment{[1..len]});
    if IsItASolvedCase(eCase)=true then
      return GoUpNextInTree();
    fi;
    eTrySet:=eSetSet[nbCase];
    TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len]}));
    gRel:=WorkingCase.ListCases[nbCase].g;
    GRPrel:=WorkingCase.ListCases[nbCase].TheGrp;
    idx:=1;
    while(true)
    do
      eSet2:=OnSets(eTrySet, gRel);
      h:=RepresentativeAction(GRPrel, eSet2, eSetSet[TheDiff[idx]], OnSets);
      if h<>fail then
        RedGrp:=Stabilizer(GRPrel, eSetSet[TheDiff[idx]], OnSets);
        WorkingCase.ListCases[nbCase+1]:=rec(g:=gRel*h, TheGrp:=RedGrp);
        WorkingCase.len:=nbCase;
        WorkingCase.ListAssignment[nbCase]:=TheDiff[idx];
        WorkingCase.ListIndices[nbCase]:=idx;
        if nbCase=nbSet then
          return gRel*h;
        else
          return "unfinished";
        fi;
      fi;
      if idx=Length(TheDiff) then
        break;
      fi;
      idx:=idx+1;
    od;
    return GoUpNextInTree();
  end;
  GoUpNextInTree:=function()
    local len, nbCase, idx, TheDiff, eTrySet, gRel, GRPrel, eSet2, h, RedGrp;
    while(true)
    do
      if WorkingCase.len=0 then
        return fail;
      fi;
      len:=WorkingCase.len;
      nbCase:=len+1;
      idx:=WorkingCase.ListIndices[nbCase-1];
      TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len-1]}));
      eTrySet:=eSetSet[len];
      gRel:=WorkingCase.ListCases[nbCase-1].g;
      GRPrel:=WorkingCase.ListCases[nbCase-1].TheGrp;
      while(true)
      do
        if idx=Length(TheDiff) then
          break;
        fi;
        idx:=idx+1;
        eSet2:=OnSets(eTrySet, gRel);
        h:=RepresentativeAction(GRPrel, eSet2, eSetSet[TheDiff[idx]], OnSets);
        if h<>fail then
          RedGrp:=Stabilizer(GRPrel, eSetSet[TheDiff[idx]], OnSets);
          WorkingCase.ListCases[nbCase]:=rec(g:=gRel*h, TheGrp:=RedGrp);
          WorkingCase.ListAssignment[nbCase-1]:=TheDiff[idx];
          WorkingCase.ListIndices[nbCase-1]:=idx;
          if nbCase=nbSet+1 then
            return gRel*h;
          else
            return "unfinished";
          fi;
        fi;
      od;
      WorkingCase.len:=len-1;
      Unbind(WorkingCase.ListCases[nbCase]);
      WorkingCase.ListAssignment[len]:=0;
      WorkingCase.ListIndices[len]:=0;
    od;
  end;
  while(true)
  do
    result:=NextInTree();
    if result=fail then
      break;
    fi;
    if result<>"unfinished" then
      FuncInsertGenerators(result);
    fi;
  od;
  for eGen in GeneratorsOfGroup(SoughtGroup)
  do
    if OnSetsSets(eSetSet, eGen)<>eSetSet then
      Error("We have inconsistency here, please check");
    fi;
  od;
  return SoughtGroup;
end;



OnSetsListSets:=function(eSetListSet, g)
  return Set(List(eSetListSet, x->OnTuplesSets(x,g)));
end;


OnSetsListSetsRepresentativeAction:=function(GRP, eSetListSet1, eSetListSet2)
  local InitialCase, nbSet, WorkingCase, NextInTree, GoUpNextInTree, result;
  if Length(eSetListSet1)<>Length(eSetListSet2) then
    return fail;
  fi;
  nbSet:=Length(eSetListSet1);
  WorkingCase:=rec(len:=0,
                   ListAssignment:=ListWithIdenticalEntries(nbSet, 0),
                   ListIndices:=ListWithIdenticalEntries(nbSet, 0),
                   ListCases:=[rec(g:=(), TheGrp:=PersoGroupPerm(GeneratorsOfGroup(GRP)))]);
  NextInTree:=function()
    local len, nbCase, eTrySet, TheDiff, idx, gRel, GRPrel, eSet2, h, RedGrp;
    len:=WorkingCase.len;
    nbCase:=len+1;
    eTrySet:=eSetListSet1[nbCase];
    TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len]}));
    gRel:=WorkingCase.ListCases[nbCase].g;
    GRPrel:=WorkingCase.ListCases[nbCase].TheGrp;
    idx:=1;
    while(true)
    do
      eSet2:=OnTuplesSets(eTrySet, gRel);
      h:=OnTuplesSetsRepresentativeAction(GRPrel, eSet2, eSetListSet2[TheDiff[idx]]);
      if h<>fail then
        RedGrp:=OnTuplesSetsStabilizer(GRPrel, eSetListSet2[TheDiff[idx]]);
        WorkingCase.ListCases[nbCase+1]:=rec(g:=gRel*h, TheGrp:=RedGrp);
        WorkingCase.len:=nbCase;
        WorkingCase.ListAssignment[nbCase]:=TheDiff[idx];
        WorkingCase.ListIndices[nbCase]:=idx;
        if nbCase=nbSet then
          return gRel*h;
        else
          return "unfinished";
        fi;
      fi;
      if idx=Length(TheDiff) then
        break;
      fi;
      idx:=idx+1;
    od;
    return GoUpNextInTree();
  end;
  GoUpNextInTree:=function()
    local len, nbCase, idx, TheDiff, eTrySet, gRel, GRPrel, eSet2, h, RedGrp;
    while(true)
    do
      if WorkingCase.len=0 then
        return fail;
      fi;
      len:=WorkingCase.len;
      nbCase:=len+1;
      idx:=WorkingCase.ListIndices[nbCase-1];
      TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len-1]}));
      eTrySet:=eSetListSet1[len];
      gRel:=WorkingCase.ListCases[nbCase-1].g;
      GRPrel:=WorkingCase.ListCases[nbCase-1].TheGrp;
      while(true)
      do
        if idx=Length(TheDiff) then
          break;
        fi;
        idx:=idx+1;
        eSet2:=OnTuplesSets(eTrySet, gRel);
        h:=OnTuplesSetsRepresentativeAction(GRPrel, eSet2, eSetListSet2[TheDiff[idx]]);
        if h<>fail then
          RedGrp:=OnTuplesSetsStabilizer(GRPrel, eSetListSet2[TheDiff[idx]]);
          WorkingCase.ListCases[nbCase]:=rec(g:=gRel*h, TheGrp:=RedGrp);
          WorkingCase.ListAssignment[nbCase-1]:=TheDiff[idx];
          WorkingCase.ListIndices[nbCase-1]:=idx;
          if nbCase=nbSet+1 then
            return gRel*h;
          else
            return "unfinished";
          fi;
        fi;
      od;
      WorkingCase.len:=len-1;
      Unbind(WorkingCase.ListCases[nbCase]);
      WorkingCase.ListAssignment[len]:=0;
      WorkingCase.ListIndices[len]:=0;
    od;
  end;
  while(true)
  do
    result:=NextInTree();
    if result=fail then
      return fail;
    fi;
    if result<>"unfinished" then
      if OnSetsListSets(eSetListSet1, result)<>eSetListSet2 then
        Error("We have inconsistency in OnSetsListSetsRepr..");
      fi;
      return result;
    fi;
  od;
end;




OnSetsListSetsStabilizer:=function(GRP, eSetListSet)
  local ListGens, eStab, GetGroupOnListSets, SoughtGroup, SetInducedGroup, NextInTree, GoUpNextInTree, FuncInsertSolvedCase, IsItASolvedCase, FuncInsertGenerators, nbSet, O, WorkingCase, result, ListSolvedCases, eGen;
  ListGens:=[];
  eStab:=Stabilizer(GRP, eSetListSet, OnTuplesSets);
  GetGroupOnListSets:=function(ListGen)
    local NewListGens, eGen, eList;
    NewListGens:=[];
    for eGen in ListGen
    do
      eList:=List(eSetListSet, x->Position(eSetListSet, OnTuplesSets(x, eGen)));
      Add(NewListGens, PermList(eList));
    od;
    return PersoGroupPerm(NewListGens);
  end;
  Append(ListGens, GeneratorsOfGroup(eStab));
  SoughtGroup:=PersoGroupPerm(ListGens);
  SetInducedGroup:=GetGroupOnListSets(ListGens);
  ListSolvedCases:=[];
  FuncInsertSolvedCase:=function(eCase)
    local ListKept, iCase, fCase, iStatus, fSetRed, eRepr;
    ListKept:=[];
    for iCase in [1..Length(ListSolvedCases)]
    do
      fCase:=ListSolvedCases[iCase];
      iStatus:=1;
      if fCase.len>=eCase.len then
        fSetRed:=fCase.eList{[1..eCase.len]};
        eRepr:=RepresentativeAction(SetInducedGroup, fSetRed, eCase.eList, OnTuples);
        if eRepr<>fail then
          iStatus:=0;
        fi;
      fi;
      if iStatus=1 then
        Add(ListKept, iCase);
      fi;
    od;
    ListSolvedCases:=Concatenation(ListSolvedCases{ListKept}, [eCase]);
  end;
  IsItASolvedCase:=function(eCase)
    local fCase, fSetRed, eRepr;
    for fCase in ListSolvedCases
    do
      if fCase.len>=eCase.len then
        fSetRed:=fCase.eList{[1..eCase.len]};
        eRepr:=RepresentativeAction(SetInducedGroup, fSetRed, eCase.eList, OnTuples);
        if eRepr<>fail then
          return true;
        fi;
      fi;
    od;
    return false;
  end;
  FuncInsertGenerators:=function(eGen)
    if not(eGen in SoughtGroup) then
      Add(ListGens, eGen);
      SoughtGroup:=PersoGroupPerm(ListGens);
      SetInducedGroup:=GetGroupOnListSets(ListGens);
    fi;
  end;
  nbSet:=Length(eSetListSet);
  WorkingCase:=rec(len:=0,
                   ListAssignment:=ListWithIdenticalEntries(nbSet, 0),
                   ListIndices:=ListWithIdenticalEntries(nbSet, 0),
                   ListCases:=[rec(g:=(), TheGrp:=PersoGroupPerm(GeneratorsOfGroup(GRP)))]);
  NextInTree:=function()
    local len, nbCase, eTrySet, TheDiff, idx, gRel, GRPrel, eSet2, h, RedGrp, eCase;
    len:=WorkingCase.len;
    if len=nbSet then
      return GoUpNextInTree();
    fi;
    nbCase:=len+1;
    eCase:=rec(len:=WorkingCase.len, eList:=WorkingCase.ListAssignment{[1..len]});
    if IsItASolvedCase(eCase)=true then
      return GoUpNextInTree();
    fi;
    eTrySet:=eSetListSet[nbCase];
    TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len]}));
    gRel:=WorkingCase.ListCases[nbCase].g;
    GRPrel:=WorkingCase.ListCases[nbCase].TheGrp;
    idx:=1;
    while(true)
    do
      eSet2:=OnTuplesSets(eTrySet, gRel);
      h:=OnTuplesSetsRepresentativeAction(GRPrel, eSet2, eSetListSet[TheDiff[idx]]);
      if h<>fail then
        RedGrp:=OnTuplesSetsStabilizer(GRPrel, eSetListSet[TheDiff[idx]]);
        WorkingCase.ListCases[nbCase+1]:=rec(g:=gRel*h, TheGrp:=RedGrp);
        WorkingCase.len:=nbCase;
        WorkingCase.ListAssignment[nbCase]:=TheDiff[idx];
        WorkingCase.ListIndices[nbCase]:=idx;
        if nbCase=nbSet then
          return gRel*h;
        else
          return "unfinished";
        fi;
      fi;
      if idx=Length(TheDiff) then
        break;
      fi;
      idx:=idx+1;
    od;
    return GoUpNextInTree();
  end;
  GoUpNextInTree:=function()
    local len, nbCase, idx, TheDiff, eTrySet, gRel, GRPrel, eSet2, h, RedGrp;
    while(true)
    do
      if WorkingCase.len=0 then
        return fail;
      fi;
      len:=WorkingCase.len;
      nbCase:=len+1;
      idx:=WorkingCase.ListIndices[nbCase-1];
      TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len-1]}));
      eTrySet:=eSetListSet[len];
      gRel:=WorkingCase.ListCases[nbCase-1].g;
      GRPrel:=WorkingCase.ListCases[nbCase-1].TheGrp;
      while(true)
      do
        if idx=Length(TheDiff) then
          break;
        fi;
        idx:=idx+1;
        eSet2:=OnTuplesSets(eTrySet, gRel);
        h:=OnTuplesSetsRepresentativeAction(GRPrel, eSet2, eSetListSet[TheDiff[idx]]);
        if h<>fail then
          RedGrp:=OnTuplesSetsStabilizer(GRPrel, eSetListSet[TheDiff[idx]]);
          WorkingCase.ListCases[nbCase]:=rec(g:=gRel*h, TheGrp:=RedGrp);
          WorkingCase.ListAssignment[nbCase-1]:=TheDiff[idx];
          WorkingCase.ListIndices[nbCase-1]:=idx;
          if nbCase=nbSet+1 then
            return gRel*h;
          else
            return "unfinished";
          fi;
        fi;
      od;
      WorkingCase.len:=len-1;
      Unbind(WorkingCase.ListCases[nbCase]);
      WorkingCase.ListAssignment[len]:=0;
      WorkingCase.ListIndices[len]:=0;
    od;
  end;
  while(true)
  do
    result:=NextInTree();
    if result=fail then
      break;
    fi;
    if result<>"unfinished" then
      FuncInsertGenerators(result);
    fi;
  od;
  for eGen in GeneratorsOfGroup(SoughtGroup)
  do
    if OnSetsListSets(eSetListSet, eGen)<>eSetListSet then
      Error("We have inconsistency here");
    fi;
  od;
  return SoughtGroup;
end;



OrbitsSafe:=function(GRP, ListPt, TheAction)
  local nbPt, ListStatus, ListRepr, ListLen, pos, ePtRepr, eOrb, ePt, posB;
  nbPt:=Length(ListPt);
  ListStatus:=ListWithIdenticalEntries(nbPt, 1);
  ListRepr:=[];
  ListLen:=[];
  while(true)
  do
    pos:=Position(ListStatus,1);
    if pos=fail then
      break;
    fi;
    ePtRepr:=ListPt[pos];
    Add(ListRepr, ePtRepr);
    eOrb:=Orbit(GRP, ePtRepr, TheAction);
    Add(ListLen, Length(eOrb));
    for ePt in eOrb
    do
      posB:=Position(ListPt, ePt);
      if posB=fail then
        Error("point does not belong to ListPt");
      fi;
      if ListStatus[posB]=0 then
        Error("The point is already assigned");
      fi;
      ListStatus[posB]:=0;
    od;
  od;
  return rec(ListRepr:=ListRepr, ListLen:=ListLen);
end;







OrbitWithAction:=function(TheGRP, ThePoint, TheAction)
  local ListCoset, ListStatus, ListElement, IsFinished, eGen, nbCos, iCos, fCos;
  ListCoset:=[ThePoint];
  ListStatus:=[1];
  ListElement:=[Identity(TheGRP)];
  while(true)
  do
    IsFinished:=true;
    nbCos:=Length(ListCoset);
    for iCos in [1..nbCos]
    do
      if ListStatus[iCos]=1 then
        ListStatus[iCos]:=0;
        IsFinished:=false;
        for eGen in GeneratorsOfGroup(TheGRP)
        do
          fCos:=TheAction(ListCoset[iCos], eGen);
          if Position(ListCoset, fCos)=fail then
            Add(ListCoset, fCos);
            Add(ListStatus, 1);
            Add(ListElement, ListElement[iCos]*eGen);
          fi;
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  return rec(ListCoset:=ListCoset, ListElement:=ListElement);
end;


# this is the right cosets that are enumerated.
GetCosetsBySplittingFunction:=function(TheGRP, TheSplitFct)
  local ListCoset, ListStatus, IsFinished, eGen, nbCos, iCos, fCos, GetPosition, pos, eElt, ListGeneratorSubgroup;
  ListCoset:=[Identity(TheGRP)];
  ListGeneratorSubgroup:=[];
  ListStatus:=[1];
  GetPosition:=function(eElt)
    local iCos, InvElt, eProd;
    InvElt:=Inverse(eElt);
    for iCos in [1..Length(ListCoset)]
    do
      eProd:=ListCoset[iCos]*InvElt;
      if TheSplitFct(eProd)=true then
        Add(ListGeneratorSubgroup, eProd);
        return iCos;
      fi;
    od;
    return fail;
  end;
  while(true)
  do
    IsFinished:=true;
    nbCos:=Length(ListCoset);
    for iCos in [1..nbCos]
    do
      if ListStatus[iCos]=1 then
        ListStatus[iCos]:=0;
        IsFinished:=false;
        for eGen in GeneratorsOfGroup(TheGRP)
        do
          eElt:=ListCoset[iCos]*eGen;
          pos:=GetPosition(eElt);
          if pos=fail then
            Add(ListCoset, eElt);
            Add(ListStatus, 1);
          fi;
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  return rec(ListCoset:=ListCoset, ListGeneratorSubgroup:=ListGeneratorSubgroup);
end;

GetKernelOfMapping:=function(GRP1, GRP2, ListGens1, ListGens2)
  local phi, TheId1, TheId2, NewListGens, TheSubgroup, FuncInsert, eElt;
  phi:=GroupHomomorphismByImagesNC(GRP1, GRP2, ListGens1, ListGens2);
  TheId1:=Identity(GRP1);
  TheId2:=Identity(GRP2);
  NewListGens:=[];
  TheSubgroup:=Group([TheId1]);
  FuncInsert:=function(eElt)
    if Image(phi, eElt)=TheId2 then
      if eElt in TheSubgroup then
        return;
      fi;
      Add(NewListGens, eElt);
      TheSubgroup:=Group(NewListGens);
    fi;
  end;
  for eElt in GRP1
  do
    FuncInsert(eElt);
  od;
  return TheSubgroup;
end;



CosetRepresentative_Stabilizer_TwoAct:=function(Id1, ListGen1, ListGen2, ePt, TheAct)
    local ListPt, ListCoset, nbGen, FuncAction, ThePos, LastPos, pos, aPt, iGen, eGen1, eGen2, uPt;
    ListPt:=[ePt];
    ListCoset:=[Id1];
    nbGen:=Length(ListGen1);
    FuncAction:=function(uPt, eGen1)
        if Position(ListPt, uPt)=fail then
            Add(ListPt, uPt);
            Add(ListCoset, eGen1);
        fi;
    end;
    ThePos:=0;
    LastPos:=1;
    while(true)
    do
        for pos in [ThePos+1..LastPos]
        do
            aPt:=ListPt[pos];
            for iGen in [1..nbGen]
            do
                eGen1:=ListCoset[pos] * ListGen1[iGen];
                eGen2:=ListGen2[iGen];
                uPt:=TheAct(aPt, eGen2);
                FuncAction(uPt, eGen1);
            od;
        od;
        ThePos:=LastPos;
        LastPos:=Length(ListPt);
        if ThePos=LastPos then
            break;
        fi;
    od;
    return ListCoset;
end;




GetIndexOneTwoKernelOfMapping:=function(GRP1, GRP2, ListGens1, ListGens2)
  local nbGen, ListPosPlus, ListPosMinus, ListGenRet, x1, TheId, eGenMinus, eGenPlus, List1, List2, i1, i2;
  if First(ListGens2, x->x<>() and x<>(1,2))<>fail then
    Error("The ListGens2 must be only () or (1,2)");
  fi;
  if GRP2<>SymmetricGroup(2) then
    Error("The second group must be SymmetricGroup(2)");
  fi;
  nbGen:=Length(ListGens2);
  ListPosPlus:=Filtered([1..nbGen], x->ListGens2[x]=());
  ListPosMinus:=Filtered([1..nbGen], x->ListGens2[x]=(1,2));
  if Length(ListPosMinus)=0 then
    return GRP1;
  fi;
  ListGenRet:=ListGens1{ListPosPlus};
  x1:=ListGens1[ListPosMinus[1]];
  TheId:=Identity(GRP1);
  for eGenMinus in ListGens1{ListPosMinus}
  do
    for eGenPlus in Concatenation(ListPosPlus, TheId)
    do
      List1:=[eGenMinus, Inverse(eGenMinus)];
      List2:=[x1, Inverse(x1)];
      for i1 in [1,2]
      do
        for i2 in [1,2]
        do
          Add(ListGenRet, List1[i1]*eGenPlus*List2[i2]);
          Add(ListGenRet, List2[i2]*eGenPlus*List1[i1]);
        od;
      od;
    od;
  od;
  return PersoGroup(ListGenRet, Identity(GRP1));
end;







MatrixGroupPermutationRepresentation:=function(GRP1, GRP2, nbPoint, ListGens1, ListGens2)
  local phi, GetKernel_meth1, TheKer, GetPreImage, GetStabilizerPoint_meth1, GetKernel_meth2, GetStabilizerPoint_meth2;
  phi:=GroupHomomorphismByImagesNC(GRP1, GRP2, ListGens1, ListGens2);
  GetKernel_meth1:=function()
    local ListGen, TheKer;
    ListGen:=CoKernelGensPermHom(InverseGeneralMapping(phi));
    TheKer:=PersoGroup(ListGen, Identity(GRP1));
    return TheKer;
  end;
  GetKernel_meth2:=function()
    return Stabilizer(GRP1, [1..nbPoint], ListGens1, ListGens2, OnTuples);
  end;
  # An alternative method is provided by an e-mail of Alexander Hulpke
  TheKer:=GetKernel_meth1();
#  TheKer:=GetKernel_meth2();
  GetPreImage:=function(ePerm)
    return PreImagesRepresentative(phi, ePerm);
  end;
  GetStabilizerPoint_meth1:=function(ePt)
    local GRPstab, ListGens1, ListGens2, ListGen;
    GRPstab:=Stabilizer(GRP2, ePt, OnPoints);
    ListGens1:=List(GeneratorsOfGroup(GRPstab), GetPreImage);
    ListGens2:=GeneratorsOfGroup(TheKer);
    ListGen:=Concatenation(ListGens1, ListGens2);
#    Print("|TheKer|=", Order(TheKer), "\n");
    return PersoGroup(ListGen, Identity(GRP1));
  end;
  GetStabilizerPoint_meth2:=function(ePt)
    return Stabilizer(GRP1, ePt, ListGens1, ListGens2, OnPoints);
  end;
  return rec(TheKer:=TheKer,
             GetStabilizerPoint:=GetStabilizerPoint_meth2);
end;




GetRotationSubgroup:=function(GRP, FctSign)
  local ListMatrGens, ListSignGens, eGen, eDet, GRPsym;
  ListMatrGens:=GeneratorsOfGroup(GRP);
  ListSignGens:=[];
  for eGen in ListMatrGens
  do
    eDet:=FctSign(eGen);
    if eDet=-1 then
      Add(ListSignGens, (1,2));
    else
      Add(ListSignGens, ());
    fi;
  od;
  GRPsym:=Group([(1,2)]);
  return GetKernelOfMapping(GRP, GRPsym, ListMatrGens, ListSignGens);
end;

LinearSpace_GetDivisor:=function(TheSpace)
  local n, TheDet, eDiv, eMat, IsOK, eVect, eSol;
  n:=Length(TheSpace);
  TheDet:=AbsInt(DeterminantMat(TheSpace));
  eDiv:=1;
  while(true)
  do
    eMat:=eDiv*IdentityMat(n);
    IsOK:=true;
    for eVect in eMat
    do
      eSol:=SolutionIntMat(TheSpace, eVect);
      if eSol=fail then
        IsOK:=false;
      fi;
    od;
    if IsOK=true then
      return eDiv;
    fi;
#    Print("eDiv=", eDiv, "\n");
   eDiv:=eDiv+1;
  od;
  Error("We should never reach that stage");
end;




OrbitComputationGeneral_limited:=function(GRPmatr, start_obj, TheAction, MaxSize)
    local TheList, TheDict, f_insert, ListGen, CurrPos, len, eGen, idx, new_obj;
    TheList:=[];
    TheDict:=NewDictionary(start_obj, true);
    f_insert:=function(eVect)
        if LookupDictionary(TheDict, eVect)<>fail then
            return;
        fi;
        Add(TheList, eVect);
        AddDictionary(TheDict, eVect, true);
    end;
    f_insert(start_obj);
    ListGen:=GeneratorsOfGroup(GRPmatr);
    CurrPos:=1;
    while(true)
    do
        len:=Length(TheList);
        Print("OrbitComputationGeneral_limited len=", len, "\n");
        for eGen in ListGen
        do
            for idx in [CurrPos..len]
            do
                new_obj:=TheAction(TheList[idx], eGen);
                f_insert(new_obj);
            od;
            if MaxSize > 0 and Length(TheList) > MaxSize then
                Print("Orbit enumeration terminated because of too large size\n");
                return fail;
            fi;
        od;
        if Length(TheList)=len then
            break;
        fi;
        CurrPos:=len+1;
    od;
    return Set(TheList);
end;



OrbitComputation_limited:=function(GRPmatr, start_vect, TheMod, MaxSize)
    local TheList, TheDict, f_insert, ListGen, CurrPos, len, eGen, idx, eVect1, eVect2;
    TheList:=[];
    TheDict:=NewDictionary(start_vect, true);
    f_insert:=function(eVect)
        if LookupDictionary(TheDict, eVect)<>fail then
            return;
        fi;
        Add(TheList, eVect);
        AddDictionary(TheDict, eVect, true);
    end;
    f_insert(start_vect);
    ListGen:=GeneratorsOfGroup(GRPmatr);
    CurrPos:=1;
    while(true)
    do
        len:=Length(TheList);
        Print("OrbitComputation_limited len=", len, "\n");
        for eGen in ListGen
        do
            for idx in [CurrPos..len]
            do
                eVect1:=TheList[idx] * eGen;
                eVect2:=List(eVect1, x->x mod TheMod);
                f_insert(eVect2);
            od;
            if MaxSize > 0 and Length(TheList) > MaxSize then
                Print("Orbit enumeration terminated because of too large size\n");
                return fail;
            fi;
        od;
        if Length(TheList)=len then
            break;
        fi;
        CurrPos:=len+1;
    od;
    return Set(TheList);
end;



IsStabilizingMod:=function(TheGRP, RecSpace)
  local eVect, eGen, eSol;
  for eVect in RecSpace.TheSpace
  do
    for eGen in GeneratorsOfGroup(TheGRP)
    do
      eSol:=SolutionIntMat(RecSpace.TheSpaceMod, eVect*eGen);
      if eSol=fail then
        return List(eVect, x->x mod RecSpace.TheMod);
      fi;
    od;
  od;
  return true;
end;

IsStabilizing:=function(TheGRP, TheSpace)
  local eVect, eGen, eSol;
  for eVect in TheSpace
  do
    for eGen in GeneratorsOfGroup(TheGRP)
    do
      eSol:=SolutionIntMat(TheSpace, eVect*eGen);
      if eSol=fail then
        return false;
      fi;
    od;
  od;
  return true;
end;


#GetListPermGenOrderedOrbit
MapToPermutationOrderedOrbit:=function(eInput, TheAction, O)
  local GetListPermGenOrderedOrbit;
  GetListPermGenOrderedOrbit:=function(ListGens)
    local ListPermGens, eGen, eListImg, ePerm1, eList, ePerm2;
    ListPermGens:=[];
    for eGen in ListGens
    do
      eListImg:=List(O, x->TheAction(x, eGen));
      ePerm1:=SortingPerm(eListImg);
#      eList:=List(O, x->Position(O, TheAction(x, eGen)));
#      ePerm2:=PermList(eList);
#      if ePerm1<>ePerm2 then
#        Error("ePerm1 <> ePerm2");
#      fi;
      Add(ListPermGens, ePerm1);
    od;
    return ListPermGens;
  end;
  if IsList(eInput) then
    return GetListPermGenOrderedOrbit(eInput);
  fi;
  if IsGroup(eInput) then
    return PersoGroupPerm(GetListPermGenOrderedOrbit(GeneratorsOfGroup(eInput)));
  fi;
  Error("Failed to find a mathing type");
end;





LinearSpace_ModStabilizer:=function(GRPmatr, TheSpace, TheMod)
  local n, TheSpaceMod, RecSpace, TheAction, GRPret, test, O, ListMatrGens, ListPermGens, eGen, eList, GRPperm, eSet, eStab, phi, ePerm1, ePerm2, eListImg, MaxSize;
  n:=Length(TheSpace);
  Print("TheMod=", TheMod, "\n");
  TheSpaceMod:=Concatenation(TheSpace, TheMod*IdentityMat(n));
  RecSpace:=rec(TheSpace:=TheSpace, TheSpaceMod:=TheSpaceMod, TheMod:=TheMod);
  TheAction:=function(eClass, eElt)
    local eVect;
    eVect:=eClass*eElt;
    return List(eVect, x->x mod TheMod);
  end;
  GRPret:=Group(GeneratorsOfGroup(GRPmatr));
  MaxSize:=100000;
#  Print("Order(GRPmatr)=", Order(GRPmatr), "\n");
  while(true)
  do
    test:=IsStabilizingMod(GRPret, RecSpace);
    if test=true then
      return GRPret;
    fi;
    O:=OrbitComputation_limited(GRPret, test, TheMod, MaxSize);
    if O=fail then
        return -1;
    fi;
    ListMatrGens:=GeneratorsOfGroup(GRPret);
    ListPermGens:=MapToPermutationOrderedOrbit(ListMatrGens, TheAction, O);
    eSet:=Filtered([1..Length(O)], x->SolutionIntMat(TheSpaceMod, O[x])<>fail);
#    Print("|O|=", Length(O), " |eSet|=", Length(eSet), "\n");
    GRPret:=Stabilizer(GRPret, eSet, ListMatrGens, ListPermGens, OnSets);
    Print("|O|=", Length(O), " |eSet|=", Length(eSet), " |ListPermGens|=", Length(ListPermGens), " |ListGen(GRPret)|=", Length(GeneratorsOfGroup(GRPret)), " |GRPperm|=", Order(Group(ListPermGens)), " |Oset|=", Length(Orbit(Group(ListPermGens), eSet, OnSets)), "\n");
  od;
end;


LinearSpace_ModStabilizer_RightCoset:=function(RecMatr, TheSpace, TheMod)
  local n, TheSpaceMod, RecSpace, TheAction, GRPret, test, O, ListMatrGens, ListPermGens, eGen, eList, GRPperm, eSet, eStab, ListListCoset, Id1, ListCoset, ePerm1, ePerm2, eListImg;
  n:=Length(TheSpace);
  TheSpaceMod:=Concatenation(TheSpace, TheMod*IdentityMat(n));
  RecSpace:=rec(TheSpace:=TheSpace, TheSpaceMod:=TheSpaceMod, TheMod:=TheMod);
  TheAction:=function(eClass, eElt)
    local eVect;
    eVect:=eClass*eElt;
    return List(eVect, x->x mod TheMod);
  end;
  GRPret:=PersoGroup(GeneratorsOfGroup(RecMatr.GRPmatr), Identity(RecMatr.GRPmatr));
  ListListCoset:=ShallowCopy(RecMatr.ListListCoset);
  Id1:=IdentityMat(n);
  while(true)
  do
    test:=IsStabilizingMod(GRPret, RecSpace);
    if test=true then
      return rec(ListListCoset:=ListListCoset, GRPmatr:=GRPret);
    fi;
    O:=Set(Orbit(GRPret, test, TheAction));
    Print("|O|=", Length(O), "\n");
    ListMatrGens:=GeneratorsOfGroup(GRPret);
    ListPermGens:=MapToPermutationOrderedOrbit(ListMatrGens, TheAction, O);
    eSet:=Filtered([1..Length(O)], x->SolutionIntMat(TheSpaceMod, O[x])<>fail);
    GRPret:=Stabilizer(GRPret, eSet, ListMatrGens, ListPermGens, OnSets);
    ListCoset:=CosetRepresentative_Stabilizer_TwoAct(Id1, ListMatrGens, ListPermGens, eSet, OnSets);
    Add(ListListCoset, ListCoset);
  od;
end;


LinearSpace_Stabilizer_RightCoset:=function(GRPmatr, TheSpace_pre)
  local TheSpace, LFact, eList, GRPret, TheMod, i, RecGRP;
  TheSpace:=LLLReducedBasis(TheSpace_pre).basis;
  RecGRP:=rec(ListListCoset:=[], GRPmatr:=PersoGroup(GeneratorsOfGroup(GRPmatr), Identity(GRPmatr)));
  if IsStabilizing(GRPmatr, TheSpace) then
    return RecGRP;
  fi;
  LFact:=LinearSpace_GetDivisor(TheSpace);
  eList:=FactorsInt(LFact);
  Print("LFact=", LFact, " eList=", eList, "\n");
  for i in [1..Length(eList)]
  do
    TheMod:=Product(eList{[1..i]});
    RecGRP:=LinearSpace_ModStabilizer_RightCoset(RecGRP, TheSpace, TheMod);
    if IsStabilizing(RecGRP.GRPmatr, TheSpace) then
      return RecGRP;
    fi;
  od;
  if IsStabilizing(RecGRP.GRPmatr, TheSpace)=false then
    Error("Algorithm error");
  fi;
  return RecGRP;
end;



LinearSpace_ModDoubleCosets:=function(RecDoubleCoset, GRPmatr1, TheSpace, TheMod)
  local n, TheSpaceMod, RecSpace, TheAction, GRPret, ListDoubleCoset, test, O, eSet, ListBigMatrGens, ListBigPermGens, GRPbigPerm, phi, LDCS, eDCS, eCos, eCosInv, fCos, GRPsubMatrConj, GRPsubPermConj, NewGRPbigMatr, NewGRPbigPerm, NewListDoubleCoset, ListSubMatrGens, ListSubPermGens, NewGRPsubMatr;
  n:=Length(TheSpace);
  TheSpaceMod:=Concatenation(TheSpace, TheMod*IdentityMat(n));
  RecSpace:=rec(TheSpace:=TheSpace, TheSpaceMod:=TheSpaceMod, TheMod:=TheMod);
  TheAction:=function(eClass, eElt)
    local eVect;
    eVect:=eClass*eElt;
    return List(eVect, x->x mod TheMod);
  end;
  while(true)
  do
    test:=IsStabilizingMod(RecDoubleCoset.GRPbigMatr, RecSpace);
    if test=true then
      return RecDoubleCoset;
    fi;
    O:=Set(Orbit(RecDoubleCoset.GRPbigMatr, test, TheAction));
    Print("|O|=", Length(O), "\n");
    ListBigMatrGens:=GeneratorsOfGroup(RecDoubleCoset.GRPbigMatr);
    ListBigPermGens:=MapToPermutationOrderedOrbit(ListBigMatrGens, TheAction, O);
    GRPbigPerm:=PersoGroupPerm(ListBigPermGens);
    phi:=GroupHomomorphismByImagesNC(RecDoubleCoset.GRPbigMatr, GRPbigPerm, ListBigMatrGens, ListBigPermGens);
    eSet:=Filtered([1..Length(O)], x->SolutionIntMat(TheSpaceMod, O[x])<>fail);
    NewGRPbigMatr:=Stabilizer(RecDoubleCoset.GRPbigMatr, eSet, ListBigMatrGens, ListBigPermGens, OnSets);
    NewGRPbigPerm:=MapToPermutationOrderedOrbit(NewGRPbigMatr, TheAction, O);
    ListSubMatrGens:=GeneratorsOfGroup(RecDoubleCoset.GRPsubMatr);
    ListSubPermGens:=MapToPermutationOrderedOrbit(ListSubMatrGens, TheAction, O);
    NewGRPsubMatr:=Stabilizer(RecDoubleCoset.GRPsubMatr, eSet, ListSubMatrGens, ListSubPermGens, OnSets);
    NewListDoubleCoset:=[];
    for eCos in RecDoubleCoset.ListDoubleCoset
    do
      eCosInv:=Inverse(eCos);
      GRPsubMatrConj:=PersoGroupMatrix(List(GeneratorsOfGroup(RecDoubleCoset.GRPsubMatr), x->eCosInv * x * eCos), n);
      GRPsubPermConj:=MapToPermutationOrderedOrbit(GRPsubMatrConj, TheAction, O);
      LDCS:=DoubleCosets(GRPbigPerm, GRPsubPermConj, NewGRPbigPerm);
      for eDCS in LDCS
      do
          fCos:=eCos * PreImagesRepresentative(phi, Representative(eDCS));
          Add(NewListDoubleCoset, fCos);
      od;
    od;
    RecDoubleCoset:=rec(ListDoubleCoset:=NewListDoubleCoset, GRPbigMatr:=NewGRPbigMatr, GRPsubMatr:=NewGRPsubMatr);
  od;
end;



# Computing the
# We will have GRPmatr2 is the stabilizer of TheSpace_pre
# We are looking for the decomposition of the GRPbig as
# GRPbig = \cup_{i\in S}    GRPmatr1 y_i GRPmatr2
LinearSpace_DoubleCosets:=function(GRPsubMatr, GRPbigMatr, TheSpace_pre)
  local TheSpace, n, ListDoubleCoset, RecDoubleCoset, LFact, eList, i, TheMod;
  TheSpace:=LLLReducedBasis(TheSpace_pre).basis;
  n:=Length(TheSpace);
  ListDoubleCoset:=[IdentityMat(n)];
  RecDoubleCoset:=rec(ListDoubleCoset:=ListDoubleCoset, GRPbigMatr:=GRPbigMatr, GRPsubMatr:=GRPsubMatr);
  if IsStabilizing(RecDoubleCoset.GRPbigMatr, TheSpace) then
    return RecDoubleCoset.ListDoubleCoset;
  fi;
  LFact:=LinearSpace_GetDivisor(TheSpace);
  eList:=FactorsInt(LFact);
  Print("LFact=", LFact, " eList=", eList, "\n");
  for i in [1..Length(eList)]
  do
    TheMod:=Product(eList{[1..i]});
    RecDoubleCoset:=LinearSpace_ModDoubleCosets(RecDoubleCoset, TheSpace, TheMod);
    if IsStabilizing(RecDoubleCoset.GRPbigMatr, TheSpace) then
      return RecDoubleCoset.ListDoubleCoset;
    fi;
  od;
  if IsStabilizing(RecDoubleCoset.GRPbigMatr, TheSpace)=false then
    Error("Algorithm error");
  fi;
  return RecDoubleCoset.ListDoubleCoset;
end;










LinearSpace_ExpandListListCoset:=function(n, ListListCoset)
    local ListCosetRet, eListCoset, ListCosetNew, eCos, fCos;
    ListCosetRet:=[IdentityMat(n)];
    for eListCoset in ListListCoset
    do
        ListCosetNew:=[];
        for eCos in ListCosetRet
        do
            for fCos in eListCoset
            do
                Add(ListCosetNew, eCos * fCos);
            od;
        od;
        ListCosetRet:=ListCosetNew;
    od;
    return ListCosetRet;
end;




LinearSpace_Stabilizer_Direct:=function(GRPmatr, TheSpace)
    local TheSpaceCan, TheAction;
    Print("Beginning of LinearSpace_Stabilizer_Direct\n");
    TheSpaceCan:=HermiteNormalFormIntegerMat(TheSpace);
    TheAction:=function(eSpace, eElt)
        return HermiteNormalFormIntegerMat(eSpace * eElt);
    end;
    Print("|O|=", Length(OrbitComputationGeneral_limited(GRPmatr, TheSpaceCan, TheAction, -1)), "\n");
    return Stabilizer(GRPmatr, TheSpaceCan, TheAction);
end;


LinearSpace_Equivalence_Direct:=function(GRPmatr, eSpace, fSpace)
    local eSpaceCan, fSpaceCan, TheAction, TheEquiv;
    eSpaceCan:=HermiteNormalFormIntegerMat(eSpace);
    fSpaceCan:=HermiteNormalFormIntegerMat(fSpace);
    TheAction:=function(uSpace, eElt)
        return HermiteNormalFormIntegerMat(uSpace * eElt);
    end;
    TheEquiv:=RepresentativeAction(GRPmatr, eSpaceCan, fSpaceCan, TheAction);
    return TheEquiv;
end;









#
#
# for L a linear space of finite index in Z^n
LinearSpace_Stabilizer_Kernel_Reduced:=function(GRPmatr, TheSpace_pre)
  local TheSpace, LFact, eList, GRPret, TheMod, i, result;
  TheSpace:=LLLReducedBasis(TheSpace_pre).basis;
  if IsStabilizing(GRPmatr, TheSpace) then
    return GRPmatr;
  fi;
  GRPret:=PersoGroup(GeneratorsOfGroup(GRPmatr), Identity(GRPmatr));
  LFact:=LinearSpace_GetDivisor(TheSpace);
  Print("LFact=", LFact, "\n");
  eList:=FactorsInt(LFact);
  for i in [1..Length(eList)]
  do
    TheMod:=Product(eList{[1..i]});
    result:=LinearSpace_ModStabilizer(GRPret, TheSpace, TheMod);
    if result=-1 then
        return LinearSpace_Stabilizer_Direct(GRPret, TheSpace);
    fi;
    GRPret := result;
    if IsStabilizing(GRPret, TheSpace) then
      return GRPret;
    fi;
  od;
  if IsStabilizing(GRPret, TheSpace)=false then
    Error("Algorithm error");
  fi;
  return GRPret;
end;


LinearSpace_ComputeOrbit:=function(GRPmatr, TheSpace)
    local ListSpaces, n_new, n_old, f_equal, f_insert, ListGen, CurrentPos, len, i, eGen, NewSpace, NewLen;
    ListSpaces:=[];
    n_new:=0;
    n_old:=0;
    f_insert:=function(eSpace)
        local eSpaceCan, quot;
        # SpaceCan = P * eSpace
        eSpaceCan:=HermiteNormalFormIntegerMat(eSpace);
        if Position(ListSpaces, eSpaceCan)<>fail then
            n_old:=n_old+1;
            return;
        fi;
        n_new:=n_new+1;
        Add(ListSpaces, eSpaceCan);
        quot:=(n_old + 0.0) / (n_new + 0.0);
        Print("Now |ListSpaces|=", Length(ListSpaces), " n_old=", n_old, " n_new=", n_new, " quot=", quot, "\n");
    end;
    f_insert(TheSpace);
    ListGen:=GeneratorsOfGroup(GRPmatr);
    CurrentPos:=1;
    while(true)
    do
        len:=Length(ListSpaces);
        for i in [CurrentPos..len]
        do
            for eGen in ListGen
            do
                NewSpace:=ListSpaces[i] * eGen;
                f_insert(NewSpace);
            od;
        od;
        NewLen:=Length(ListSpaces);
        if len = NewLen then
            break;
        fi;
        CurrentPos:=len+1;
    od;
    return ListSpaces;
end;






LinearSpace_Stabilizer_Kernel:=function(GRPmatr, TheSpace_pre)
    local n, eRec, Pmat, PmatInv, TheSpace_B, TheSpace_C, GRPret, ListGenNew, eGen, eGenNew;
    n:=Length(TheSpace_pre);
    eRec:=LLLMatrixGroupReduction(n, GRPmatr);
    Pmat:=eRec.Pmat;
    PmatInv:=Inverse(Pmat);
    TheSpace_B:=TheSpace_pre * PmatInv;
    TheSpace_C:=LLLbasisReduction(TheSpace_B).LattRed;
#    Print("|ListSpaces|=", Length(LinearSpace_ComputeOrbit(eRec.GRPred, TheSpace_C)), "\n");
    GRPret:=LinearSpace_Stabilizer_Kernel_Reduced(eRec.GRPred, TheSpace_C);
    ListGenNew:=[];
    for eGen in GeneratorsOfGroup(GRPret)
    do
        eGenNew:=PmatInv * eGen * Pmat;
        Add(ListGenNew, eGenNew);
    od;
    return Group(ListGenNew);
end;



LinearSpace_Stabilizer:=function(GRPmatr, TheSpace_pre)
    local result, TheAnswer;
    result:=LinearSpace_Stabilizer_Kernel(GRPmatr, TheSpace_pre);
    TheAnswer:=rec(GRPmatr:=GRPmatr, TheSpace_pre:=TheSpace_pre, result:=result);
#    SaveDebugInfo("LinearSpace_Stabilizer", TheAnswer);
    return result;
end;






LinearSpace_ModEquivalence:=function(GRPmatr, NeedStabilizer, TheSpace1, TheSpace2, TheMod)
    local MaxSize, n, TheSpace1Mod, TheSpace2Mod, RecSpace2, TheAction, IsEquiv, GRPwork, eElt, test, eVect, O, ListMatrGens, ListPermGens, eGen, eList, GRPperm, eSet1, eSet2, eTest, eStab, eMat, TheSpace1work, GenerateGroupInfo, GetFace, GrpInf, test1, test2;
    Print("LinearSpace_ModEquivalence, TheMod=", TheMod, "\n");
#    Print("TheSpace1=\n");
#    PrintArray(TheSpace1);
#    Print("TheSpace2=\n");
#    PrintArray(TheSpace2);
    Print("det(TheSpace1)=", DeterminantMat(TheSpace1), " det(TheSpace2)=", DeterminantMat(TheSpace2), "\n");
    MaxSize:=100000;
    n:=Length(TheSpace1);
    TheSpace1Mod:=Concatenation(TheSpace1, TheMod*IdentityMat(n));
    TheSpace2Mod:=Concatenation(TheSpace2, TheMod*IdentityMat(n));
    RecSpace2:=rec(TheSpace:=TheSpace2, TheSpaceMod:=TheSpace2Mod, TheMod:=TheMod);
    TheAction:=function(eClass, eElt)
        local eVect;
        eVect:=eClass*eElt;
        return List(eVect, x->x mod TheMod);
    end;
    IsEquiv:=function(eEquiv)
        local eVect, eGen, eSol;
        for eVect in TheSpace1
        do
            eSol:=SolutionIntMat(TheSpace2Mod, eVect*eEquiv);
            if eSol=fail then
                return List(eVect*eEquiv, x->x mod TheMod);
            fi;
        od;
        return true;
    end;
    GenerateGroupInfo:=function(test)
      local ListMatrGens, ListPermGens, eGen, eList, eListImg, ePerm1, ePerm2;
      O:=OrbitComputation_limited(GRPwork, test, TheMod, MaxSize);
      if O=fail then
          return -1;
      fi;
      Print("|O|=", Length(O), "\n");
      ListMatrGens:=GeneratorsOfGroup(GRPwork);
      ListPermGens:=[];
      for eGen in ListMatrGens
      do
          eListImg:=List(O, x->TheAction(x, eGen));
          ePerm1:=SortingPerm(eListImg);
          eList:=List(O, x->Position(O, TheAction(x, eGen)));
          ePerm2:=PermList(eList);
          if ePerm1<>ePerm2 then
              Error("ePerm1 <> ePerm2");
          fi;
          Add(ListPermGens, ePerm2);
      od;
      Print("ListPermGens built\n");
      return rec(O:=O, ListMatrGens:=ListMatrGens, ListPermGens:=ListPermGens);
    end;
    GetFace:=function(TheO, TheSpace)
        return Filtered([1..Length(TheO)], x->SolutionIntMat(TheSpace, TheO[x])<>fail);
    end;
    GRPwork:=PersoGroup(GeneratorsOfGroup(GRPmatr), Identity(GRPmatr));
    eElt:=IdentityMat(n);
    while(true)
    do
      Print("Before test1, test2 equivalence\n");
      test1:=IsEquiv(eElt);
      if NeedStabilizer=false then
          test2:=true;
      else
          test2:=IsStabilizingMod(GRPwork, RecSpace2);
      fi;
      Print("test1=true=", test1=true, " test2=true=", test2=true, "\n");
      if test1=true and test2=true then
          Print("Returning from LinearSpace_ModEquivalence\n");
          return rec(GRPwork:=GRPwork, eEquiv:=eElt);
      fi;
      if test1<>true then
        GrpInf:=GenerateGroupInfo(test1);
        if GrpInf=-1 then
          return -1;
        fi;
        TheSpace1work:=TheSpace1Mod*eElt;
        eSet1:=GetFace(GrpInf.O, TheSpace1work);
        eSet2:=GetFace(GrpInf.O, TheSpace2Mod);
        Print("|eSet1|=", Length(eSet1), " |eSet2|=", Length(eSet2), " |GrpInf.O|=", Length(GrpInf.O), " |GrpInf.ListMatrGens|=", Length(GrpInf.ListMatrGens), "\n");
        eMat:=RepresentativeAction(GRPwork, eSet1, eSet2, GrpInf.ListMatrGens, GrpInf.ListPermGens, OnSets);
        Print("We have eMat\n");
        if eMat=fail then
            return fail;
        fi;
        Print("Before computing GRPwork\n");
        GRPwork:=Stabilizer(GRPwork, eSet2, GrpInf.ListMatrGens, GrpInf.ListPermGens, OnSets);
        Print("After stabilization |GRPwork|=", Order(GRPwork), "\n");
        eElt:=eElt*eMat;
      fi;
      if test2<>true then
        Print("Before GrpInf\n");
        GrpInf:=GenerateGroupInfo(test2);
        if GrpInf=-1 then
          return -1;
        fi;
        Print("We have GrpInf\n");
        eSet2:=GetFace(GrpInf.O, TheSpace2Mod);
        Print("|eSet2|=", Length(eSet2), " |GrpInf.O|=", Length(GrpInf.O), "\n");
        GRPwork:=Stabilizer(GRPwork, eSet2, GrpInf.ListMatrGens, GrpInf.ListPermGens, OnSets);
        Print("We have GRPwork\n");
      fi;
    od;
end;

LinearSpace_Equivalence_Kernel_Reduced:=function(GRPmatr, TheSpace1_pre, TheSpace2_pre)
  local TheSpace1, TheSpace2, n, LFact1, LFact2, eList, IsEquivalence, GRPwork, eElt, TheMod, TheSpace1Img, eTest, i, eDet1, eDet2, NeedStabilizer;
  TheSpace1:=LLLReducedBasis(TheSpace1_pre).basis;
  TheSpace2:=LLLReducedBasis(TheSpace2_pre).basis;
  n:=Length(TheSpace1);
  LFact1:=LinearSpace_GetDivisor(TheSpace1);
  LFact2:=LinearSpace_GetDivisor(TheSpace2);
#  eDet1:=AbsInt(DeterminantMat(TheSpace1));
#  eDet2:=AbsInt(DeterminantMat(TheSpace2));
#  Print("eDet1=", eDet1, " eDet2=", eDet2, "\n");
  Print("LFact1=", LFact1, " LFact2=", LFact2, "\n");
  if LFact1<>LFact2 then
    return fail;
  fi;
  eList:=FactorsInt(LFact1);
  IsEquivalence:=function(eEquiv)
    local eVect, eSol;
    Print("Beginning of IsEquivalence\n");
    for eVect in TheSpace1
    do
      eSol:=SolutionIntMat(TheSpace2, eVect*eEquiv);
      if eSol=fail then
        Print("Returning false from IsEquivalence\n");
        return false;
      fi;
    od;
    Print("Returning true from IsEquivalence\n");
    return true;
  end;
  GRPwork:=PersoGroup(GeneratorsOfGroup(GRPmatr), Identity(GRPmatr));
  eElt:=IdentityMat(n);
  for i in [1..Length(eList)]
  do
    TheMod:=Product(eList{[1..i]});
    Print("i=", i, " TheMod=", TheMod, "\n");
    if IsEquivalence(eElt) then
      Print("Returning eElt 1\n");
      return eElt;
    fi;
    TheSpace1Img:=List(TheSpace1, x->x*eElt);
    NeedStabilizer:=true;
    if i = Length(eList) then
        NeedStabilizer:=false;
    fi;
    eTest:=LinearSpace_ModEquivalence(GRPwork, NeedStabilizer, TheSpace1Img, TheSpace2, TheMod);
    if eTest=-1 then
        Print("Using the direct approach\n");
        eTest:=LinearSpace_Equivalence_Direct(GRPwork, TheSpace1Img, TheSpace2);
        if eTest=fail then
            Print("Returning fail by direct approach\n");
            return fail;
        fi;
        eElt:=eElt * eTest;
        if IsEquivalence(eElt)=false then
            Error("Algorithm error 1");
        fi;
        return eElt;
    fi;
    Print("We have eTest\n");
    if eTest=fail then
      Print("Returning fail\n");
      return fail;
    fi;
    eElt:=eElt*eTest.eEquiv;
    if NeedStabilizer then
        GRPwork:=eTest.GRPwork;
    fi;
  od;
  if IsEquivalence(eElt)=false then
    Error("Algorithm error 2");
  fi;
  Print("Returning eElt 2\n");
  return eElt;
end;


LinearSpace_Equivalence_Kernel:=function(GRPmatr, TheSpace1_pre, TheSpace2_pre)
    local n, eRec, Pmat, PmatInv, TheSpace1_B, TheSpace2_B, TheSpace1_C, TheSpace2_C, opt, RetMat;
    n:=Length(TheSpace1_pre);
#    Print("Generators(GRPmatr)=", GeneratorsOfGroup(GRPmatr), "\n");
    eRec:=LLLMatrixGroupReduction(n, GRPmatr);
#    Print("Generators(eRec.GRPred)=", GeneratorsOfGroup(eRec.GRPred), "\n");
    Pmat:=eRec.Pmat;
    PmatInv:=Inverse(Pmat);
    TheSpace1_B:=TheSpace1_pre * PmatInv;
    TheSpace2_B:=TheSpace2_pre * PmatInv;
    TheSpace1_C:=LLLbasisReduction(TheSpace1_B).LattRed;
    TheSpace2_C:=LLLbasisReduction(TheSpace2_B).LattRed;
#    Print("TheSpace1_C=", TheSpace1_C, "\n");
#    Print("TheSpace2_C=", TheSpace2_C, "\n");
    opt:=LinearSpace_Equivalence_Kernel_Reduced(eRec.GRPred, TheSpace1_C, TheSpace2_C);
    if opt=fail then
        return fail;
    fi;
    RetMat:=PmatInv * opt * Pmat;
    return RetMat;
end;


LinearSpace_Equivalence:=function(GRPmatr, TheSpace1_pre, TheSpace2_pre)
    local result, TheAnswer;
#    SaveDebugInfo("LinearSpace_Equivalence_Query", rec(GRPmatr:=GRPmatr, TheSpace1_pre:=TheSpace1_pre, TheSpace2_pre:=TheSpace2_pre));
    result:=LinearSpace_Equivalence_Kernel(GRPmatr, TheSpace1_pre, TheSpace2_pre);
    TheAnswer:=rec(GRPmatr:=GRPmatr, TheSpace1_pre:=TheSpace1_pre, TheSpace2_pre:=TheSpace2_pre, result:=result);
#    SaveDebugInfo("LinearSpace_Equivalence_Result", TheAnswer);
    return result;
end;





# We want to find an invariant lattice for the group.
# This allows to conjugate the matrix group into an integral group.
#
# Such a lattice do not necessarily exists:
# ---For example if there are matrices of determinant a with |a| > 1.
# then no lattice exist.
#
# Such a lattice exist in many cases:
# ---For example if the group is finite.
# ---In application case such as indefinite forms and
#
#
MatrixIntegral_GetInvariantSpace:=function(n, GRPrat)
    local LGen, LGenTot, TheSpace, TheDet, IncreaseSpace;
    LGen:=GeneratorsOfGroup(GRPrat);
    LGenTot:=Set(Concatenation(LGen, List(LGen, Inverse)));
    Print("LGen|=", Length(LGen), " |LGenTot|=", Length(LGenTot), "\n");
    TheSpace:=IdentityMat(n);
    TheDet:=1;
    IncreaseSpace:=function()
        local eGen, ConcatSpace, NewSpace, NewDet;
        for eGen in LGenTot
        do
            ConcatSpace:=Concatenation(TheSpace, TheSpace * eGen);
            NewSpace:=GetZbasis(ConcatSpace);
            NewDet:=AbsInt(DeterminantMat(NewSpace));
            if NewDet<>TheDet then
                TheSpace:=ShallowCopy(NewSpace);
                TheDet:=NewDet;
                return false;
            fi;
        od;
        return true;
    end;
    while(true)
    do
        if IncreaseSpace() then
            break;
        fi;
    od;
    return TheSpace;
end;


InvariantSpaceOfGroup:=function(n, GRPmatr)
    local LGen, LSeq, EquaSyst, NSP, eVect, eGen;
    LGen:=GeneratorsOfGroup(GRPmatr);
    if Length(LGen)=0 then
        return IdentityMat(n);
    fi;
    LSeq:=List(LGen, x->TransposedMat(x) - IdentityMat(n));
    EquaSyst:=TransposedMat(Concatenation(LSeq));
    NSP:=NullspaceMat(EquaSyst);
    for eVect in NSP
    do
        for eGen in LGen
        do
            if eVect * eGen<>eVect then
                Error("Vector is not invariant");
            fi;
        od;
    od;
    return NSP;
end;





MatrixIntegral_Stabilizer:=function(n, GRPrat)
    local LGen, TheSpace, TheSpaceInv, ListGenInt, GRPint, eStab, ListGenIntSpace;
    LGen:=GeneratorsOfGroup(GRPrat);
    TheSpace:=MatrixIntegral_GetInvariantSpace(n, GRPrat);
    TheSpaceInv:=Inverse(TheSpace); # Also known as LattToStab
    ListGenInt:=List(LGen, x->TheSpace * x * TheSpaceInv);
    GRPint:=Group(ListGenInt);
    if First(ListGenInt, x->IsIntegralMat(x)=false)<>fail then
        Error("Some geneatorsmatrix are not integral");
    fi;
    if IsIntegralMat(TheSpaceInv)=false then
        Error("TheSpaceInv is not integral");
    fi;
    eStab:=LinearSpace_Stabilizer(GRPint, TheSpaceInv);
    ListGenIntSpace:=List(GeneratorsOfGroup(eStab), x->TheSpaceInv * x * TheSpace);
    return PersoGroupMatrix(ListGenIntSpace, n);
end;


MatrixIntegral_RightCosets:=function(n, GRPrat)
    local LGen, TheSpace, TheSpaceInv, ListGenInt, GRPint, RecStab_RightCoset, ListCoset, ListCosetRet;
    LGen:=GeneratorsOfGroup(GRPrat);
    TheSpace:=MatrixIntegral_GetInvariantSpace(n, GRPrat);
    TheSpaceInv:=Inverse(TheSpace);
    ListGenInt:=List(LGen, x->TheSpace * x * TheSpaceInv);
    GRPint:=Group(ListGenInt);
    RecStab_RightCoset:=LinearSpace_Stabilizer_RightCoset(GRPint, TheSpaceInv);
#    Print("RecStab_RightCoset=", RecStab_RightCoset, "\n");
    ListCoset:=LinearSpace_ExpandListListCoset(n, RecStab_RightCoset.ListListCoset);
#    Print("ListCoset=", ListCoset, "\n");
    ListCosetRet:=List(ListCoset, x->TheSpaceInv * x * TheSpace);
    return ListCosetRet;
end;




MatrixIntegral_Equivalence_TestFeasibility:=function(GRPrat, EquivRat)
    local TheDenEquiv, TheDenGRP;
    TheDenEquiv:=ReducePrimeMultiplicity(GetDenominatorMatrix(EquivRat));
    TheDenGRP:=GetRationalInvariant(GRPrat);
    if IsInt(TheDenGRP / TheDenEquiv) = false then
        Print("Some prime numbers in the equivalence are not in the group. No equivalence possible");
        return false;
    fi;
    return true;
end;



# Find a matrix g in GRPrat such that   g * EquivRat   in   GL(n,Z)
MatrixIntegral_Equivalence:=function(GRPrat, EquivRat)
    local n, LGen, TheSpace, TheSpaceInv, ListGenInt, GRPspace, TheSpaceImg, TheSpaceImgInv, eSpaceEquiv, eMatFinal, eProd;
    if MatrixIntegral_Equivalence_TestFeasibility(GRPrat, EquivRat)=false then
        return fail;
    fi;
    n:=Length(EquivRat);
    LGen:=GeneratorsOfGroup(GRPrat);
    TheSpace:=MatrixIntegral_GetInvariantSpace(n, GRPrat);
    Print("DeterminantMat(TheSpace)=", DeterminantMat(TheSpace), "\n");
    # We have TheSpace * g in TheSpace
    # So, in other words TheSpace * g = g_int * TheSpace
    # which gets us TheSpace * g * TheSpaceInv = g_int
    TheSpaceInv:=Inverse(TheSpace);
    ListGenInt:=List(LGen, x->TheSpace * x * TheSpaceInv);
    if First(ListGenInt, x->IsIntegralMat(x)=false)<>fail then
        Error("Some geneatorsmatrix are not integral");
    fi;
    GRPspace:=PersoGroup(ListGenInt, Identity(GRPrat));
    if IsIntegralMat(TheSpaceInv)=false then
        Error("TheSpaceInv is not integral. That should not hapen since TheSpace is built by accretting to Z^n");
    fi;
    # We search for g in GRPrat s.t. g * EquivRat in GL_n(Z).
    # So, we search g in GRPrat s.t. Z^n * g * EquivRat = Z^n
    # Writing g = TheSpaceInv g_int TheSpace we get
    # TheSpaceInv g TheSpace EquivRat = Z^n
    # Or TheSpaceInv g = Inverse(TheSpace * EquivRat)
    TheSpaceImg:=TheSpace * EquivRat;
    TheSpaceImgInv:=Inverse(TheSpaceImg);
    if IsIntegralMat(TheSpaceImgInv)=false then
        return fail;
    fi;
    eSpaceEquiv:=LinearSpace_Equivalence(GRPspace, TheSpaceInv, TheSpaceImgInv);
#    Print("Invariant(GRPspace)=", InvariantSpaceOfGroup(n, GRPspace), "\n");
    if eSpaceEquiv=fail then
        return fail;
    fi;
    eMatFinal:=TheSpaceInv * eSpaceEquiv * TheSpace;
    eProd:=eMatFinal * EquivRat;
    if IsIntegralMat(eProd)=false then
        Error("The matrix should be integral");
    fi;
    return eProd;
end;



# Find a matrix g in GRPrat such that   EquivRat * g   in   GL(n,Z)
MatrixIntegral_Equivalence_Bis:=function(GRPrat, EquivRat)
    local EquivRatInv, n, TheSol;
    EquivRatInv:=Inverse(EquivRat);
    n:=Length(EquivRat);
    TheSol:=MatrixIntegral_Equivalence(GRPrat, EquivRatInv);
    if TheSol=fail then
        return fail;
    fi;
    # So we have TheSol = g * Inverse(EquivRat) in GL(n,Z)
    # Inverse(TheSol) = EquivRat * g in GL(n,Z)
    return Inverse(TheSol);
end;




# eSet does not have to be left invariant by GRP
OrbitDecomposition:=function(eSet, GRP, eAction)
  local ListOrbitRepr, TotSet, eRepr, eO;
  ListOrbitRepr:=[];
  TotSet:=Set(eSet);
  while(true)
  do
    if Length(TotSet)=0 then
      break;
    fi;
    eRepr:=TotSet[1];
    Add(ListOrbitRepr, eRepr);
    eO:=Orbit(GRP, eRepr, eAction);
    TotSet:=Difference(TotSet, Set(eO));
  od;
  return ListOrbitRepr;
end;
