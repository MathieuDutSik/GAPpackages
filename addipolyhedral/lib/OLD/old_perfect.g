TspaceFormalismRyshkov:=function(eCase, SHV, TheMatrGRP)
  local ListIneq, ListIneqRed, eVect, eLine, SetIneqRed, nbClass, ListGroups, ListNbGroups, ListRep, iIneqRed, ListPos, eIneqRed, eVectRay, iCanIdx, n, ListExpressionRays, TheMat, ePos, TheMatExpand, eSol, BasisExpand, eList, ListMatrGens, ListPermGens, GRPonGroups, TheStabMatr, ListPermGensBis, eMat, eGen, TheStabMatrTrans, ListMatrGensTrans;
  n:=Length(SHV[1]);
  ListIneq:=[];
  ListIneqRed:=[];
  ListPermGens:=[];
  ListMatrGens:=[];
  ListMatrGensTrans:=[];
  BasisExpand:=List(eCase.Basis, SymmetricMatrixToVector);
  for eGen in GeneratorsOfGroup(TheMatrGRP)
  do
    eList:=List(SHV, x->Position(SHV, x*eGen));
    eMat:=List(eCase.Basis, x->SolutionMat(BasisExpand, SymmetricMatrixToVector(eGen*x*TransposedMat(eGen))));
    Add(ListPermGens, PermList(eList));
    Add(ListMatrGens, eMat);
    Add(ListMatrGensTrans, TransposedMat(eMat));
  od;
  TheStabMatr:=Group(ListMatrGens);
  TheStabMatrTrans:=Group(ListMatrGensTrans);
  for eVect in SHV
  do
    eLine:=List(eCase.Basis, x->eVect*x*eVect);
    Add(ListIneq, eLine);
    Add(ListIneqRed, RemoveFraction(eLine));
  od;
  SetIneqRed:=Set(ListIneqRed);
  nbClass:=Length(SetIneqRed);
  ListGroups:=[];
  ListNbGroups:=ListWithIdenticalEntries(Length(SHV), 0);
  ListRep:=ListWithIdenticalEntries(nbClass, 0);
  ListExpressionRays:=[];
  for iIneqRed in [1..nbClass]
  do
    eIneqRed:=SetIneqRed[iIneqRed];
    ListPos:=Filtered([1..Length(SHV)], x->ListIneqRed[x]=eIneqRed);
    Add(ListGroups, ListPos);
    ListNbGroups{ListPos}:=ListWithIdenticalEntries(Length(ListPos), iIneqRed);
    iCanIdx:=ListPos[1];
    ListRep[iIneqRed]:=iCanIdx;
  od;
  ListPermGensBis:=[];
  for eGen in ListPermGens
  do
    eList:=List(ListGroups, x->Position(ListGroups, OnSets(x, eGen)));
    Add(ListPermGensBis, PermList(eList));
  od;
  GRPonGroups:=Group(ListPermGensBis);
  return rec(ListGroups:=ListGroups,
             ListNbGroups:=ListNbGroups, 
             ListRep:=ListRep, 
             ListIneqRed:=ListIneqRed, 
             GRPonGroups:=GRPonGroups, 
             TheStabMatr:=TheStabMatr, 
             TheStabMatrTrans:=TheStabMatrTrans, 
             SetIneqRed:=SetIneqRed);
end;

GetEnumerationPerfectForm:=function(n)
  local TheTesselation, FuncInsert, IsFinished, nbRecord, SHVgroups, GramMat, GRP, ListPermGens, eGen, eList, PermGRP, ListSymm, ListOrbit, ListAdj, eOrb, FlippedGram, TheAdj, iRecord, GlobSymmGrp, eFac, TransformGroup, FuncDoRetraction, MyStab, OrbSize, iOrb, NewListPermGens, ePerm, eTransGen, FindPosition;
  TheTesselation:=[];
  GlobSymmGrp:=Group([-IdentityMat(n)]);
  TransformGroup:=function(TheGroup)
    local ListTransGens, eGen;
    ListTransGens:=List(GeneratorsOfGroup(TheGroup), TRS_SymmRep);
    return Group(ListTransGens);
  end;
  FuncInsert:=function(TheNewGram)
    local iRecord, eRecord, eEquiv, SHV, SHVgroups;
    for iRecord in [1..Length(TheTesselation)]
    do
      eRecord:=TheTesselation[iRecord];
      eEquiv:=ArithmeticEquivalenceMatrixFamily_Souvignier("", [eRecord.GramMat], [], [TheNewGram], []);
      if eEquiv<>false then
        return rec(iRecord:=iRecord, eEquiv:=TRS_SymmRep(Inverse(eEquiv)));
      fi;
    od;
    SHV:=ShortestVectorDutourVersion(TheNewGram);
    SHVgroups:=Orbits(GlobSymmGrp, SHV, OnPoints);
    eRecord:=rec(SHVgroups:=SHVgroups, GramMat:=TheNewGram, Status:="NO");
    Add(TheTesselation, eRecord);
    return rec(iRecord:=Length(TheTesselation), eEquiv:=TRS_SymmRep(IdentityMat(n)));
  end;
  FuncDoRetraction:=function(eVect)
    local nbDim, eMat;
    nbDim:=n*(n+1)/2;
    eMat:=VectorToSymmetricMatrix(eVect, n);
#    maybe this code is needed to get the correct
#    values of the fields.
#    for i in [1..n]
#    do
#      eMat[i][i]:=2*eMat[i][i];
#    od;
    if RankMat(eMat) < n then
      return true;
    else
      return false;
    fi;
  end;
  FuncInsert(LatticeAn(n));
  while(true)
  do
    IsFinished:=true;
    nbRecord:=Length(TheTesselation);
    for iRecord in [1..nbRecord]
    do
      if TheTesselation[iRecord].Status="NO" then
        TheTesselation[iRecord].Status:="YES";
        IsFinished:=false;
        SHVgroups:=TheTesselation[iRecord].SHVgroups;
        GramMat:=TheTesselation[iRecord].GramMat;
        GRP:=ArithmeticAutomorphismMatrixFamily_Souvignier("", [GramMat], []);
        ListPermGens:=[];
        FindPosition:=function(eVect)
          local iGroup;
          for iGroup in [1..Length(SHVgroups)]
          do
            if Position(SHVgroups[iGroup], eVect)<>fail then
              return iGroup;
            fi;
          od;
        end;
        for eGen in GeneratorsOfGroup(GRP)
        do
          eList:=List(SHVgroups, x->FindPosition(x[1]*eGen));
          Add(ListPermGens, PermList(eList));
        od;
        PermGRP:=Group(ListPermGens);
        ListSymm:=List(SHVgroups, x->SymmetricMatrixToVector(TransposedMat([x[1]])*[x[1]]));
        ListOrbit:=DualDescriptionStandard(ListSymm, PermGRP);
        NewListPermGens:=[];
        for eGen in GeneratorsOfGroup(GRP)
        do
          eTransGen:=TRS_SymmRep(eGen);
          eList:=List(ListSymm, x->Position(ListSymm, x*eTransGen));
          ePerm:=PermList(eList);
          if ePerm=fail then
            Print("Please debug from here\n");
            Print(NullMat(5));
          fi;
          Add(NewListPermGens, ePerm);
        od;
        Print("|PermGRP|=", Order(PermGRP), "\n");
        for iOrb in [1..Length(ListOrbit)]
        do
          MyStab:=Stabilizer(PermGRP, ListOrbit[iOrb], OnSets);
          OrbSize:=Order(PermGRP)/Order(MyStab);
          Print(" iOrb=", iOrb, " |eOrb|=", Length(ListOrbit[iOrb]), " sizorb=", OrbSize, "\n");
        od;
        TheTesselation[iRecord].ListSymm:=ListSymm;
        TheTesselation[iRecord].PermGRP:=PermGRP;
        TheTesselation[iRecord].MatrixStab:=TransformGroup(GRP);
        ListAdj:=[];
        for eOrb in ListOrbit
        do
          FlippedGram:=DoFlipping_perfectform(SHVgroups, eOrb);
          TheAdj:=FuncInsert(FlippedGram);
          eFac:=__FindFacetInequality(ListSymm, eOrb);
          TheAdj.eFac:=eFac;
          Add(ListAdj, TheAdj);
        od;
        TheTesselation[iRecord].ListAdj:=ListAdj;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  for iRecord in [1..Length(TheTesselation)]
  do
    Unbind(TheTesselation[iRecord].Status);
  od;
  return rec(TheTesselation:=TheTesselation, FuncDoRetraction:=FuncDoRetraction, TheGroup:=TransformGroup(GL(n, Integers)));
end;




TestRealizabilityShortestFamily_V1:=function(ListVect)
  local n, ListVectTot, ListRankOneFormMat, ListRankOneFormVect, ListDiff, TheBasis, TheFamilyVect, eVect, GetListIneq, ToBeMinimized, ListIneq, TheLP, ListNorm, SHV, NewSet, eMatFirst, eMatSec, i, j, DiffNew, SHVdiff, eVectBas, eEnt, TheDim, NewVect, eVectEmb, rVect, eScal1, eScal2, iVect, NSP, ListScal, DiagInfo, BasisToSymmetricMatrix, SymmetricMatrixToBasis, eVectTest, eSetIncd, eVertH, eExpr, eSymmEuct, eVertEuct, eVectEuct, ListScalEuct, ListVal, ePerm, ListValSort, DoLimitSize, eMaxVal, LimitSize, IdxSel, nbIter, ListOptimal, ListMatSec, IdxKillSel, IdxKillNotSel, IdxKill, ListKillVect, eOptimal, eOptimalPrev, SetIneq, eVectPrimalDir, EllapsedTime, TotalEllapsedTime, TheDate1, TheDate2, CritTime, eList;
  n:=Length(ListVect[1]);
  TheDim:=n*(n+1)/2;
  ListVectTot:=Set(Concatenation(ListVect, -ListVect));
  ListRankOneFormMat:=List(ListVect, x->TransposedMat([x])*[x]);
  ListRankOneFormVect:=List(ListRankOneFormMat, SymmetricMatrixToVector);
  ListDiff:=List([2..Length(ListVect)], x->ListRankOneFormVect[x] - ListRankOneFormVect[1]);
  TheBasis:=NullspaceMat(TransposedMat(ListDiff));
  TheFamilyVect:=[];
  for eVect in ListVect
  do
    Append(TheFamilyVect, List(IdentityMat(n), x->RemoveFraction(eVect+x)));
    Append(TheFamilyVect, List(IdentityMat(n), x->RemoveFraction(eVect-x)));
  od;
  LimitSize:=3*TheDim;
  DoLimitSize:=false;
  TheFamilyVect:=Difference(Set(TheFamilyVect), Union(ListVectTot, [ListWithIdenticalEntries(n,0)]));
  Print("|TheFamilyVect|=", Length(TheFamilyVect), "\n");
  GetListIneq:=function(TheFamVect)
    local ListIneq, eFamVect, eSymmVect, eIneq, eVectBas;
    ListIneq:=[];
    for eFamVect in TheFamVect
    do
      eSymmVect:=SymmetricMatrixToVector(TransposedMat([eFamVect])*[eFamVect]);
      eIneq:=[-1];
      for eVectBas in TheBasis
      do
        Add(eIneq, eVectBas*eSymmVect);
      od;
      Add(ListIneq, eIneq);
    od;
    return ListIneq;
  end;
  ToBeMinimized:=[0];
  for eVectBas in TheBasis
  do
    Add(ToBeMinimized, eVectBas*ListRankOneFormVect[1]);
  od;
  BasisToSymmetricMatrix:=function(eVect)
    local eVectBas, i, j, eMatFirst, eMatSec;
    eVectBas:=ListWithIdenticalEntries(TheDim,0);
    for i in [1..Length(TheBasis)]
    do
      eVectBas:=eVectBas + eVect[i]*TheBasis[i];
    od;
    eMatFirst:=VectorToSymmetricMatrix(eVectBas, n);
    eMatSec:=NullMat(n,n);
    for i in [1..n]
    do
      for j in [1..n]
      do
        if i=j then
          eMatSec[i][j]:=eMatFirst[i][j];
        else
          eMatSec[i][j]:=eMatFirst[i][j]/2;
        fi;
      od;
    od;
    return eMatSec;
  end;
  SymmetricMatrixToBasis:=function(eMatSec)
    local eMatFirst, i, j;
    eMatFirst:=NullMat(n,n);
    for i in [1..n]
    do
      for j in [1..n]
      do
        if i=j then
          eMatFirst[i][j]:=eMatSec[i][j];
        else
          eMatFirst[i][j]:=eMatSec[i][j]*2;
        fi;
      od;
    od;
    return SolutionMat(TheBasis, SymmetricMatrixToVector(eMatFirst));
  end;
  nbIter:=0;
  ListOptimal:=[];
  ListMatSec:=[];
  ListKillVect:=[];
  TotalEllapsedTime:=0;
  CritTime:=10;
  while(true)
  do
    if nbIter >=2 then
      eOptimalPrev:=eOptimal;
    fi;
    nbIter:=nbIter+1;
    Print("nbIter=", nbIter, "\n");
    ListIneq:=GetListIneq(TheFamilyVect);
    if Length(Intersection(TheFamilyVect, ListVectTot))> 0 then
      Error("Intersection is non-empty. Cause of major bugs");
    fi;
    SetIneq:=Set(ListIneq);
    Print("|ListIneq|=", Length(ListIneq), " |SetIneq|=", Length(SetIneq), "\n");
    TheDate1:=GetDate();
    TheLP:=LinearProgramming(SetIneq, ToBeMinimized);
    TheDate2:=GetDate();
    EllapsedTime:=TheDate2 - TheDate1;
    TotalEllapsedTime:=TotalEllapsedTime + EllapsedTime;
    if IsBound(TheLP.primal_direction)=true then
      eVectPrimalDir:=ListWithIdenticalEntries(Length(TheBasis),0);
      for eEnt in TheLP.primal_direction
      do
        eVectPrimalDir[eEnt[1]]:=eEnt[2];
      od;
      AddSet(TheFamilyVect, 2*ListVect[1]);
    else
      if IsBound(TheLP.primal_solution)=false then
        Error("I think we have a real problem. Please debug");
      fi;
      eOptimal:=TheLP.optimal;
      if nbIter=1 then
        eOptimalPrev:=eOptimal;
      fi;
      Add(ListOptimal, eOptimal);
      eVectEmb:=ListWithIdenticalEntries(Length(TheBasis),0);
      for eEnt in TheLP.primal_solution
      do
        eVectEmb[eEnt[1]]:=eEnt[2];
      od;
      eVertH:=Concatenation([1], eVectEmb);
      eSetIncd:=Filtered([1..Length(ListIneq)], x->ListIneq[x]*eVertH=0);
      eVectTest:=Concatenation([ToBeMinimized[1]-TheLP.optimal],ToBeMinimized{[2..Length(ToBeMinimized)]});
      eExpr:=SolutionMatNonnegative(ListIneq{eSetIncd}, eVectTest);
      if eExpr=fail then
        Error("Error in the solutioning");
      fi;
      eMatSec:=BasisToSymmetricMatrix(eVectEmb);
      Add(ListMatSec, eMatSec);
      TheFamilyCorr:=TheFamilyFiltered
      ListNorm:=List(TheFamilyVect, x->x*eMatSec*x);
      rVect:=Concatenation([1], eVectEmb);
      for iVect in [1..Length(TheFamilyVect)]
      do
        eScal1:=rVect*ListIneq[iVect]+1;
        eScal2:=TheFamilyVect[iVect]*eMatSec*TheFamilyVect[iVect];
        if eScal1<>eScal2 then
          Error("A few bugs remaining to be solved");
        fi;
      od;
      ListScal:=List(ListVect, x->x*eMatSec*x);
      if Length(Set(ListScal))<>1 then
        Error("Error in computation of norms");
      fi;
      if ListScal[1]<>TheLP.optimal then
        Error("Error in objective function value");
      fi;
      if Minimum(ListNorm)<1 then
        Error("We have a clear inconsistency in the code");
      fi;
      DiagInfo:=DiagonalizeSymmetricMatrix(eMatSec);
      Print("   nbMinus=", DiagInfo.nbMinus, " nbPlus=", DiagInfo.nbPlus, " nbZero=", DiagInfo.nbZero, "\n");
      Print("   eOptimal=", eOptimal, "\n");
      if IsPositiveDefiniteSymmetricMatrix(eMatSec) then
        SHV:=ShortestVectorDutourVersion(eMatSec);
        Print("|SHV|=", Length(SHV), "\n");
        if Set(SHV)=ListVectTot then
          return rec(reply:=true, eMat:=eMatSec);
        else
          SHVdiff:=Difference(Set(SHV), ListVectTot);
          DiffNew:=Difference(SHVdiff, TheFamilyVect);
          if Length(DiffNew)>0 then
            TheFamilyVect:=Union(TheFamilyVect, DiffNew);
          else
            return rec(reply:=false, SHV:=SHV);
          fi;
        fi;
      else
        if RankMat(eMatSec)<n then
          NSP:=NullspaceMat(eMatSec);
          NewVect:=RemoveFraction(NSP[1]);
          if Position(ListVectTot, NewVect)<>fail then
            NewVect:=2*NewVect;
          fi;
          Print("NSP : NewVect=", NewVect, "\n");
          AddSet(TheFamilyVect, NewVect);
        else
          NewVect:=EigenvalueFindNegativeVect(eMatSec);
          if Position(ListVectTot, NewVect)<>fail then
            NewVect:=2*NewVect;
          fi;
          Print("EIG : NewVect=", NewVect, "\n");
          AddSet(TheFamilyVect, NewVect);
        fi;
      fi;
    fi;
    if DoLimitSize then
      ListIneq:=GetListIneq(TheFamilyVect);
      ListVal:=List(ListIneq, x->x*eVertH);
      ePerm:=SortingPerm(ListVal);
      ListValSort:=Permuted(ListVal, ePerm);
      eMaxVal:=ListValSort[Minimum([LimitSize, Length(TheFamilyVect)])];
      IdxSel:=Filtered([1..Length(ListIneq)], x->ListIneq[x]*eVertH<=eMaxVal);
      # a vector can get killed only once if eOptimal=eOptimalPrev
      if eOptimal=eOptimalPrev then
        IdxKill:=Difference([1..Length(ListIneq)], IdxSel);
        IdxKillSel:=Filtered(IdxKill, x->Position(ListKillVect, CanonicalizeVectForPerfect(TheFamilyVect[x]))=fail);
        IdxKillNotSel:=Difference(IdxKill, IdxKillSel);
        Append(ListKillVect, List(TheFamilyVect{IdxKillSel}, CanonicalizeVectForPerfect));
        TheFamilyVect:=Set(TheFamilyVect{Union(IdxSel, IdxKillNotSel)});
      else
        ListKillVect:=[];
        TheFamilyVect:=Set(TheFamilyVect{IdxSel});
      fi;
    fi;
    Print("TotalEllapsedTime=", TotalEllapsedTime, "\n");
    if TotalEllapsedTime>CritTime then
      TotalEllapsedTime:=0;
      Print("Before ReductionLinearProgram\n");
      ListIneq:=GetListIneq(TheFamilyVect);
      eList:=ReductionLinearProgram(ListIneq, ToBeMinimized);
      Print("After ReductionLinearProgram\n");
      TheFamilyVect:=TheFamilyVect{eList};
    fi;
  od;
end;



#
# old programs
#
#





#
#
# return the generators of the group of matrices U
# satisfying to
# U*F*TransposedMat(U)=F
#
# this method seem to be non-working with aberrant non-positive
# definite matrix error appearing
Method1AutomorphismLattice:=function(GramMat)
  local dim, FileIn, FileOut, FileGap, output, iLin, iCol, REP, GramMatRed, eGen;
  FileIn:=Filename(POLYHEDRAL_tmpdir, "AUTO.in");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "AUTO.out");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "AUTO.gap");
  dim:=Length(GramMat);
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Print("Matrix should be positive definite\n");
    return fail;
  fi;
  output:=OutputTextFile(FileIn, true);;
  AppendTo(output, dim, "\n");
  GramMatRed:=RemoveFractionMatrix(GramMat);
  for iLin in [1..dim]
  do
    for iCol in [1..iLin]
    do
      AppendTo(output, " ", GramMatRed[iLin][iCol]);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
  Exec(FileAUTO, " ", FileIn, " > ", FileOut);
  Exec(FileAUTOMtoGAP, " ", FileOut, " > ", FileGap);
  REP:=ReadAsFunction(FileGap)();
  Exec("cp ", FileIn, " /tmp/VRCL2");
  RemoveFile(FileIn);
  RemoveFile(FileOut);
  RemoveFile(FileGap);
  for eGen in GeneratorsOfGroup(REP)
  do
    if eGen*GramMat*TransposedMat(eGen)<>GramMat then
      Error("Error in Method1Automorphism");
    fi;
  od;
  return REP;
end;








