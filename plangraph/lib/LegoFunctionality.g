GetListRecClusterPair:=function(a, b)
  local eEnt1, eEnt2, ListRecCluster;
  eEnt1:=rec(p:=a, ListSymb:=[]);
  eEnt2:=rec(p:=b, ListSymb:=["i"]);
  ListRecCluster:=[rec(LEnt:=[eEnt1, eEnt2])];
  return ListRecCluster;
end;


# The polycycle format is similar to standard classical plangraph
# We have a list of adjacent points:
# [ [rec(assigned:=true, AdjVert:=3, posAdj:=1), rec(assigned:=false), ....], [
POLYCYCLE_SingleVertex:=function(eDeg)
  local LAdj, i;
  LAdj:=[];
  for i in [1..eDeg]
  do
    Add(LAdj, rec(assigned:=false));
  od;
  return [LAdj];
end;


POLYCYCLE_SpanFixedDegreeExtension:=function(ePolycycle, eDeg)
  local ListSpann, nbVert, iVert, len, i, NewPolycycle, LAdj, u;
  ListSpann:=[];
  nbVert:=Length(ePolycycle);
  for iVert in [1..nbVert]
  do
    len:=Length(ePolycycle[iVert]);
    for i in [1..len]
    do
      if ePolycycle[iVert][i].assigned=false then
        NewPolycycle:=StructuralCopy(ePolycycle);
	NewPolycycle[iVert][i].assigned:=true;
	NewPolycycle[iVert][i].AdjVert:=nbVert+1;
	NewPolycycle[iVert][i].posAdj:=1;
        LAdj:=[rec(assigned:=true, AdjVert:=iVert, posAdj:=i)];
        for u in [2..eDeg]
        do
	  Add(LAdj, rec(assigned:=false));
        od;
	Add(NewPolycycle, LAdj);
	Add(ListSpann, NewPolycycle);
      fi;
    od;
  od;
  return ListSpann;
end;


POLYCYCLE_SaturationFilterCodegree:=function(ePolycycle, kCodeg)
  local RetPolycycle, nbVert, DoWork, iVert, len, i, iNext, eBlock, ListBlock, DoAction, eFirstBlock, eLastBlock, NewListBlock, eRecDEfirst, eRecDElast, AdjVert, posAdj, lenAdj, posAdjPrev, posAdjNext, NewBlock, IsLoop;
  RetPolycycle:=List(ePolycycle, x->x);
  nbVert:=Length(RetPolycycle);
  while(true)
  do
    DoWork:=false;
#    Print("Passing by mainLoop of POLYCYCLE_SaturationFilterCodegree\n");
    for iVert in [1..nbVert]
    do
      len:=Length(RetPolycycle[iVert]);
      for i in [1..len]
      do
        iNext:=NextIdx(len, i);
        eBlock:=[[iVert, i], [iVert, iNext]];
        ListBlock:=[eBlock];
        IsLoop:=false;
        while(true)
        do
          DoAction:=false;
          eFirstBlock:=ListBlock[1][1];
          eLastBlock:=ListBlock[Length(ListBlock)][2];
          NewListBlock:=[];
          eRecDEfirst:=RetPolycycle[eFirstBlock[1]][eFirstBlock[2]];
          if eRecDEfirst.assigned=true then
            AdjVert:=eRecDEfirst.AdjVert;
            posAdj:=eRecDEfirst.posAdj;
            lenAdj:=Length(RetPolycycle[AdjVert]);
            posAdjPrev:=PrevIdx(lenAdj, posAdj);
            NewBlock:=[[AdjVert, posAdjPrev], [AdjVert, posAdj]];
            if NewBlock<>ListBlock[Length(ListBlock)] then
              Add(NewListBlock, NewBlock);
              DoAction:=true;
            else
              IsLoop:=true;
            fi;
          fi;
          Append(NewListBlock, ListBlock);
          eRecDElast:=RetPolycycle[eLastBlock[1]][eLastBlock[2]];
          if eRecDElast.assigned=true then
            AdjVert:=eRecDElast.AdjVert;
            posAdj:=eRecDElast.posAdj;
            lenAdj:=Length(RetPolycycle[AdjVert]);
            posAdjNext:=NextIdx(lenAdj, posAdj);
            NewBlock:=[[AdjVert, posAdj], [AdjVert, posAdjNext]];
            if NewBlock<>NewListBlock[1] then
              Add(NewListBlock, NewBlock);
              DoAction:=true;
            else
              IsLoop:=true;
            fi;
          fi;
          if Length(Set(NewListBlock))<>Length(NewListBlock) then
            Print("Duplication error in NewListBlock\n");
            Error("Please correct that bug");
          fi;
          if DoAction=true then
            ListBlock:=List(NewListBlock, x->x);
          else
            break;
          fi;
        od;
        if Length(ListBlock)>kCodeg then
          return false;
        fi;
        if Length(ListBlock)=kCodeg and IsLoop=false then
	  DoWork:=true;
          eFirstBlock:=ListBlock[1][1];
	  eLastBlock:=ListBlock[Length(ListBlock)][2];
	  RetPolycycle[eFirstBlock[1]][eFirstBlock[2]].assigned:=true;
	  RetPolycycle[eFirstBlock[1]][eFirstBlock[2]].AdjVert:=eLastBlock[1];
	  RetPolycycle[eFirstBlock[1]][eFirstBlock[2]].posAdj:=eLastBlock[2];
	  RetPolycycle[eLastBlock[1]][eLastBlock[2]].assigned:=true;
	  RetPolycycle[eLastBlock[1]][eLastBlock[2]].AdjVert:=eFirstBlock[1];
	  RetPolycycle[eLastBlock[1]][eLastBlock[2]].posAdj:=eFirstBlock[2];
	fi;
      od;
    od;
    if DoWork=false then
      break;
    fi;
  od;
  return RetPolycycle;
end;


POLYCYCLE_TestIsomorphismOriented:=function(ePolycycle1, ePolycycle2)
  local nbVert, eDeg1, GetNakedCorresp, iVert, eDeg2, result, i2, TestEquivalence;
  if Length(ePolycycle1)<>Length(ePolycycle2) then
    return false;
  fi;
  nbVert:=Length(ePolycycle1);
  eDeg1:=Length(ePolycycle1[1]);
  GetNakedCorresp:=function(ePolycycle)
    local TheCorresp, iVert, eDeg, LCorr, i;
    TheCorresp:=[];
    for iVert in [1..nbVert]
    do
      eDeg:=Length(ePolycycle[iVert]);
      LCorr:=[];
      for i in [1..eDeg]
      do
        Add(LCorr, "unset");
      od;
      Add(TheCorresp, LCorr);
    od;
    return TheCorresp;
  end;
  TestEquivalence:=function(iVertIns, i2ins)
    local TheCorresp12, TheCorresp21, DoSomething, iVert1, eDeg1, i1, eVal, iVert2, i2, i2next, i1next, eValNext, AdjVert1, posAdj1, AdjVert2, posAdj2, eValNew, eDeg2;
    TheCorresp12:=GetNakedCorresp(ePolycycle1);
    TheCorresp21:=GetNakedCorresp(ePolycycle2);
    TheCorresp12[1][1]:=[iVertIns, i2ins];
    TheCorresp21[iVertIns][i2ins]:=[1,1];
    while(true)
    do
      DoSomething:=false;
      for iVert1 in [1..nbVert]
      do
        eDeg1:=Length(ePolycycle1[iVert1]);
        for i1 in [1..eDeg1]
        do
          eVal:=TheCorresp12[iVert1][i1];
          if eVal<>"unset" then
            iVert2:=eVal[1];
            eDeg2:=Length(ePolycycle2[iVert2]);
            if eDeg1<>eDeg2 then
              return false;
            fi;
            i2:=eVal[2];
            i2next:=NextIdx(eDeg1, i2);
            i1next:=NextIdx(eDeg1, i1);
            eValNext:=[iVert2,i2next];
            if TheCorresp12[iVert1][i1next]<>"unset" then
              if TheCorresp12[iVert1][i1next]<>eValNext then
                return false;
              fi;
            else
              TheCorresp12[iVert1][i1next]:=eValNext;
              DoSomething:=true;
            fi;
            if ePolycycle1[iVert1][i1].assigned<>ePolycycle2[iVert2][i2].assigned then
              return false;
            fi;
            if ePolycycle1[iVert1][i1].assigned=true then
              AdjVert1:=ePolycycle1[iVert1][i1].AdjVert;
              posAdj1:=ePolycycle1[iVert1][i1].posAdj;
              AdjVert2:=ePolycycle2[iVert2][i2].AdjVert;
              posAdj2:=ePolycycle2[iVert2][i2].posAdj;
              eValNew:=[AdjVert2, posAdj2];
              if TheCorresp12[AdjVert1][posAdj1]<>"unset" then
                if TheCorresp12[AdjVert1][posAdj1]<>eValNew then
                  return false;
                fi;
              else
                TheCorresp12[AdjVert1][posAdj1]:=eValNew;
                DoSomething:=true;
              fi;
            fi;
          fi;
        od;
      od;
      if DoSomething=false then
        break;
      fi;
    od;
    for iVert1 in [1..nbVert]
    do
      eDeg1:=Length(ePolycycle1[iVert1]);
      for i1 in [1..eDeg1]
      do
        if TheCorresp12[iVert1][i1]="unset" then
          Error("We should not have unset values at this stage");
        fi;
      od;
    od;
    return true;
  end;
  for iVert in [1..nbVert]
  do
    eDeg2:=Length(ePolycycle2[iVert]);
    if eDeg1=eDeg2 then
      for i2 in [1..eDeg2]
      do
        result:=TestEquivalence(iVert, i2);
        if result=true then
          return true;
        fi;
      od;
    fi;
  od;
  return false;
end;

POLYCYCLE_PlaneSymmetry:=function(ePolycycle)
  local RetPolycycle, nbVert, iVert, eDeg, LAdj, iNew, iOld, eAdj, AdjVert, posAdjOld, eDegAdj, posAdjNew;
  RetPolycycle:=[];
  nbVert:=Length(ePolycycle);
  for iVert in [1..nbVert]
  do
    eDeg:=Length(ePolycycle[iVert]);
    LAdj:=[];
    for iNew in [1..eDeg]
    do
      iOld:=1 + eDeg - iNew;
      if ePolycycle[iVert][iOld].assigned=false then
        eAdj:=rec(assigned:=false);
      else
        AdjVert:=ePolycycle[iVert][iOld].AdjVert;
        posAdjOld:=ePolycycle[iVert][iOld].posAdj;
        eDegAdj:=Length(ePolycycle[AdjVert]);
        posAdjNew:=1 + eDegAdj - posAdjOld;
        eAdj:=rec(assigned:=true, AdjVert:=AdjVert, posAdj:=posAdjNew);
      fi;
      Add(LAdj, eAdj);
    od;
    Add(RetPolycycle, LAdj);
  od;
  return RetPolycycle;
end;




POLYCYCLE_ConvertToRecCluster:=function(ePolycycle)
  local AttainmentSequence, nbVert, iVert, eDeg, LVal, i, DoSomething, eSeqVal, iNext, iPrev, eSeqNext, eSeqPrev, eSeqInv, ListRet, AdjVert, posAdj, eEnt, Securization;
  AttainmentSequence:=[];
  nbVert:=Length(ePolycycle);
  for iVert in [1..nbVert]
  do
    eDeg:=Length(ePolycycle[iVert]);
    LVal:=[];
    for i in [1..eDeg]
    do
      Add(LVal, "unset");
    od;
    Add(AttainmentSequence, LVal);
  od;
  Securization:=function(iVert)
    local eDeg, pos, TheSeq, i;
    eDeg:=Length(ePolycycle[iVert]);
    pos:=First([1..eDeg], x->AttainmentSequence[iVert][x]<>"unset");
    TheSeq:=AttainmentSequence[iVert][pos];
    for i in [1..eDeg]
    do
      pos:=NextIdx(eDeg,pos);
      TheSeq:=Concatenation(TheSeq, ["n"]);
      if AttainmentSequence[iVert][pos]="unset" then
        AttainmentSequence[iVert][pos]:=TheSeq;
      fi;
    od;
  end;
  AttainmentSequence[1][1]:=[];
  Securization(1);  
  while(true)
  do
    DoSomething:=false;
    for iVert in [1..nbVert]
    do
      eDeg:=Length(ePolycycle[iVert]);
      for i in [1..eDeg]
      do
        if AttainmentSequence[iVert][i]<>"unset" then
          eSeqVal:=AttainmentSequence[iVert][i];
          if ePolycycle[iVert][i].assigned=true then
            AdjVert:=ePolycycle[iVert][i].AdjVert;
            posAdj:=ePolycycle[iVert][i].posAdj;
            if AttainmentSequence[AdjVert][posAdj]="unset" then
              eSeqInv:=Concatenation(eSeqVal, ["i"]);
              AttainmentSequence[AdjVert][posAdj]:=eSeqInv;
              Securization(AdjVert);
              DoSomething:=true;
            fi;
          fi;
        fi;
      od;
    od;
    if DoSomething=false then
      break;
    fi;
  od;
  ListRet:=[];
  for iVert in [1..nbVert]
  do
    eDeg:=Length(ePolycycle[iVert]);
    for i in [1..eDeg]
    do
      if AttainmentSequence[iVert][i]="unset" then
        Print("We have unset value at iVert=", iVert, " i=", i, "\n");
        Error("Please debug your problem");
      fi;
    od;
    eEnt:=rec(p:=eDeg, ListSymb:=AttainmentSequence[iVert][1]);
    Add(ListRet, eEnt);
  od;
  return rec(LEnt:=ListRet);
end;



POLYCYCLE_ConvertFromRecCluster:=function(eRecCluster)
  local LEnt, nbVert, ListDegree;
  LEnt:=eRecCluster.LEnt;
  nbVert:=Length(LEnt);
  ListDegree:=List(LEnt, x->x.p);
end;






POLYCYCLE_Enumerate:=function(kCodeg, ListDegree, FilteringFunction)
  local eDeg, ePolycycle, ListCases, i, NewListCases, FuncInsert, eCaseOld, ListSpann, eSpann, eFinal, nbCase, GetPosition, ListCorresp, eCase, eCaseRev, iCase, jCase, eCluster, fCluster, ListReturn, pos, GetDifferencePossibleDegree, ListDegOccur, ListDegDiff, fDeg;
  eDeg:=ListDegree[1];
  ePolycycle:=POLYCYCLE_SingleVertex(eDeg);
  ListCases:=[ePolycycle];
  GetDifferencePossibleDegree:=function(ListDegBig, ListDegSma)
    local nbBig, ListStatus, nbSma, iSma, eSma, IsDone, iBig, ListPos, ListRemain;
    nbBig:=Length(ListDegBig);
    ListStatus:=ListWithIdenticalEntries(nbBig,1);
    nbSma:=Length(ListDegSma);
    for iSma in [1..nbSma]
    do
      eSma:=ListDegSma[iSma];
      IsDone:=false;
      for iBig in [1..nbBig]
      do
        if IsDone=false then
          if ListDegBig[iBig]=eSma and ListStatus[iBig]=1 then
            ListStatus[iBig]:=0;
            IsDone:=true;
          fi;
        fi;
      od;
      if IsDone=false then
        Error("Did not find a position for eSma");
      fi;
    od;
    ListPos:=Filtered([1..nbBig], x->ListStatus[x]=1);
    ListRemain:=ListDegBig{ListPos};
#    Print("ListDegBig=", ListDegBig, " ListDegSma=", ListDegSma, " ListRemain=", ListRemain, "\n");
    return ListRemain;
  end;
  for i in [2..Length(ListDegree)]
  do
    NewListCases:=[];
    FuncInsert:=function(eCase)
      local fCase;
      for fCase in NewListCases
      do
        if POLYCYCLE_TestIsomorphismOriented(eCase, fCase)=true then
          return;
        fi;
      od;
      Add(NewListCases, eCase);
    end;
    for eCaseOld in ListCases
    do
      ListDegOccur:=List(eCaseOld, Length);
      ListDegDiff:=GetDifferencePossibleDegree(ListDegree, ListDegOccur);
      for fDeg in Set(ListDegDiff)
      do
        ListSpann:=POLYCYCLE_SpanFixedDegreeExtension(eCaseOld, fDeg);
        for eSpann in ListSpann
        do
          eFinal:=POLYCYCLE_SaturationFilterCodegree(eSpann, kCodeg);
          if eFinal<>false then
            if FilteringFunction(eFinal)=true then
              FuncInsert(eFinal);
            fi;
          fi;
        od;
      od;
    od;
    ListCases:=Set(NewListCases);
    Print("Now i=", i, " |ListCases|=", Length(ListCases), "\n");
  od;
  nbCase:=Length(ListCases);
  GetPosition:=function(eCase)
    local iCase;
    for iCase in [1..nbCase]
    do
      if POLYCYCLE_TestIsomorphismOriented(eCase, ListCases[iCase])=true then
        return iCase;
      fi;
    od;
    return -1;
  end;
  ListCorresp:=[];
  for eCase in ListCases
  do
    eCaseRev:=POLYCYCLE_PlaneSymmetry(eCase);
    pos:=GetPosition(eCaseRev);
    Add(ListCorresp, pos);
  od;
  Print("ListCorresp=", ListCorresp, "\n");
  ListReturn:=[];
  SaveDataToFile("ListCases", ListCases);
  for iCase in [1..nbCase]
  do
    jCase:=ListCorresp[iCase];
    if iCase=jCase then
#      eCluster:=ListCases[iCase];
      eCluster:=POLYCYCLE_ConvertToRecCluster(ListCases[iCase]);
      Add(ListReturn, rec(planesym:=true, ListCluster:=[eCluster]));
    else
      if jCase > iCase then
#        eCluster:=ListCases[iCase];
#        fCluster:=ListCases[jCase];
        eCluster:=POLYCYCLE_ConvertToRecCluster(ListCases[iCase]);
        fCluster:=POLYCYCLE_ConvertToRecCluster(ListCases[jCase]);
        Add(ListReturn, rec(planesym:=false, ListCluster:=[eCluster, fCluster]));
      fi;
    fi;
  od;
  return ListReturn;
end;





TestAdmissibilityEmbeddingLego:=function(ListDegree, ListRecCluster, PLori)
  local DualPLori, eInv, eNext, ePrev, VEFori, nbVert, ListVertAttainedStatus, iDE, eRecCluster, ListP, ListMissDeg, GetSingleBlock, eBlock, eDeg, len, nbDE, iVert;
  DualPLori:=DualGraphOriented(PLori);
  eInv:=DualPLori.invers;
  eNext:=DualPLori.next;
  ePrev:=Inverse(DualPLori.next);
  nbDE:=PLori.nbP;
  VEFori:=PlanGraphOrientedToVEF(DualPLori);
  nbVert:=Length(VEFori.VertSet);
  len:=Length(ListRecCluster[1]);
  if Length(ListDegree)>len then
    Error("length error in ListDegree");
  fi;
  for eRecCluster in ListRecCluster
  do
    ListP:=List(eRecCluster, x->x.eP);
    if ListP<>ListDegree{[1..len]} then
      Error("Logical inconsistencies in the degrees");
    fi;
  od;
  ListMissDeg:=ListDegree{[len+1..Length(ListDegree)]};
  GetSingleBlock:=function(iDE, eRecCluster)
    local eBlock, eEnt, eP, jDE, eVal, iVert, siz;
    eBlock:=[];
    for eEnt in eRecCluster.LEnt
    do
      eP:=eEnt.p;
      jDE:=iDE;
      for eVal in eEnt.ListSymb
      do
        if eVal="i" then
          jDE:=OnPoints(jDE, eInv);
        fi;
        if eVal="n" then
          jDE:=OnPoints(jDE, eNext);
        fi;
        if eVal="p" then
          jDE:=OnPoints(jDE, ePrev);
        fi;
      od;
      iVert:=VEFori.ListOriginVert[jDE];
      siz:=Length(VEFori.VertSet[iVert]);
      if siz<>eP then
        return fail;
      fi;
      Add(eBlock, iVert);
    od;
    return Set(eBlock);
  end;
  ListVertAttainedStatus:=ListWithIdenticalEntries(nbVert,0);
  for iDE in [1..nbDE]
  do
    for eRecCluster in ListRecCluster
    do
      eBlock:=GetSingleBlock(iDE, eRecCluster);
      if eBlock<>fail then
        ListVertAttainedStatus{eBlock}:=ListWithIdenticalEntries(Length(eBlock),1);
      fi;
    od;
  od;
  for iVert in [1..nbVert]
  do
    if ListVertAttainedStatus[iVert]=0 then
      eDeg:=Length(VEFori.VertSet[iVert]);
      if Position(ListMissDeg, eDeg)=fail then
        return rec(feasible:="no");
      fi;
    fi;
  od;
  return rec(feasible:="maybe");
end;












DoLegoPreparation:=function(PLori)
  local DualPLori, eNext, ePrev, eInv, VEFori, nbDE, nbVert, nbEdge, nbFace, GRPori, ListEdges, ListDualEdges, ListPairDE, iEdge, eEdgeDE, iDE, jDE, iVert, jVert, iFace, jFace, eEdge, eDualEdge, PL, LAdj, len, i, rDE, eNextPL, ePermNext, ePermInv, eListNext, eListInv, PLoriRet;
  DualPLori:=DualGraphOriented(PLori);
  eInv:=DualPLori.invers;
  eNext:=DualPLori.next;
  ePrev:=Inverse(DualPLori.next);
  VEFori:=PlanGraphOrientedToVEF(DualPLori);
  nbDE:=DualPLori.nbP;
  nbVert:=Length(VEFori.VertSet);
  nbEdge:=Length(VEFori.EdgeSet);
  nbFace:=Length(VEFori.FaceSet);
  GRPori:=GroupPlanOriented(DualPLori);
  ListEdges:=[];
  ListDualEdges:=[];
  ListPairDE:=[];
  for iEdge in [1..nbEdge]
  do
    eEdgeDE:=VEFori.EdgeSet[iEdge];
    iDE:=eEdgeDE[1];
    jDE:=eEdgeDE[2];
    iVert:=VEFori.ListOriginVert[iDE];
    jVert:=VEFori.ListOriginVert[jDE];
    iFace:=VEFori.ListOriginFace[iDE];
    jFace:=VEFori.ListOriginFace[jDE];
    eEdge:=[iVert, jVert];
    eDualEdge:=[iFace, jFace];
    Add(ListEdges, eEdge);
    Add(ListDualEdges, Set(eDualEdge));
    Add(ListPairDE, eEdgeDE);
  od;
  PL:=[];
  eNextPL:=eNext*eInv;
  for iFace in [1..nbFace]
  do
    LAdj:=[];
    len:=Length(VEFori.FaceSet[iFace]);
    iDE:=VEFori.FaceSet[iFace][1];
    for i in [1..len]
    do
      iDE:=OnPoints(iDE, eNextPL);
      rDE:=OnPoints(iDE, eInv);
      jFace:=VEFori.ListOriginFace[rDE];
      Add(LAdj, jFace);
    od;
    Add(PL, LAdj);
  od;
  return rec(DualPLori:=DualPLori, PLori:=PLori, PL:=PL, VEFori:=VEFori, GRPori:=GRPori, ListEdges:=ListEdges, ListDualEdges:=ListDualEdges, ListPairDE:=ListPairDE);
end;


ConvertRecCluster_Kernel:=function(eDegFace, eRecCluster)
  local nbVertCluster, ListDeg, iVert, eDeg, ListVertExtent, ListListStatus, eLine, eLineStat, FirstVertFree, eEnt, i, pos, nbSymb, iSymb, eVal, MatchVert, MatchPos, MatchDeg, nbAction, iAdj, iAdjNext, iAdjPrev, eEdge, PrevPos, NextPos, ListShiftDE, NewLEnt, NewEnt;
  nbVertCluster:=Length(eRecCluster.LEnt);
  ListDeg:=[];
  for iVert in [1..nbVertCluster]
  do
    eDeg:=eRecCluster.LEnt[iVert].p;
    Add(ListDeg, eDeg);
  od;
  ListVertExtent:=[];
  ListListStatus:=[];
  for iVert in [1..nbVertCluster]
  do
    eLine:=[];
    eLineStat:=[];
    eDeg:=ListDeg[iVert];
    for i in [1..eDeg]
    do
      Add(eLine, rec(status:="unset"));
      Add(eLineStat, 0);
    od;
    Add(ListVertExtent, eLine);
    Add(ListListStatus, eLineStat);
  od;
  FirstVertFree:=2;
  for eEnt in eRecCluster.LEnt
  do
#    Print("iEnt=", Position(eRecCluster.LEnt, eEnt), "\n");
    iVert:=1;
    pos:=1;
    nbSymb:=Length(eEnt.ListSymb);
#    Print("  nbSymb=", nbSymb, "\n");
    for iSymb in [1..nbSymb]
    do
      eVal:=eEnt.ListSymb[iSymb];
#      Print("  iSymb=", iSymb, " eVal=", eVal, "\n");
      if eVal="n" then
        eDeg:=ListDeg[iVert];
        pos:=NextIdx(eDeg, pos);
      fi;
      if eVal="p" then
        eDeg:=ListDeg[iVert];
        pos:=PrevIdx(eDeg,pos);
      fi;
      if eVal="i" then
        if ListVertExtent[iVert][pos].status="unset" then
          ListVertExtent[iVert][pos]:=rec(status:="set", MatchVert:=FirstVertFree, MatchPos:=1);
          ListVertExtent[FirstVertFree][1]:=rec(status:="set", MatchVert:=iVert, MatchPos:=pos);
#          Print("Assigning FirstVertFree=", FirstVertFree, "\n");
          ListListStatus[iVert][pos]:=1;
          ListListStatus[FirstVertFree][1]:=1;
          FirstVertFree:=FirstVertFree+1;
        else
          MatchVert:=ListVertExtent[iVert][pos].MatchVert;
          MatchPos:=ListVertExtent[iVert][pos].MatchPos;
          iVert:=MatchVert;
          pos:=MatchPos;
        fi;
      fi;
    od;
  od;
  if FirstVertFree<>nbVertCluster+1 then
    Error("We have a logical error in the construction");
  fi;
  while(true)
  do
    nbAction:=0;
    for iVert in [1..nbVertCluster]
    do
      eDeg:=ListDeg[iVert];
      for iAdj in [1..eDeg]
      do
        iAdjNext:=NextIdx(eDeg, iAdj);
        if ListVertExtent[iVert][iAdj].status="set" and ListVertExtent[iVert][iAdjNext].status="unset" then
          eEdge:=ListVertExtent[iVert][iAdj];
          for i in [1..eDegFace-2]
          do
            if eEdge.status="set" then
              MatchVert:=eEdge.MatchVert;
              MatchPos:=eEdge.MatchPos;
              MatchDeg:=ListDeg[MatchVert];
              PrevPos:=PrevIdx(MatchDeg, MatchPos);
              eEdge:=ListVertExtent[MatchVert][PrevPos];
            fi;
          od;
          if eEdge.status="set" then
            MatchVert:=eEdge.MatchVert;
            MatchPos:=eEdge.MatchPos;
            MatchDeg:=ListDeg[MatchVert];
            PrevPos:=PrevIdx(MatchDeg, MatchPos);
            ListVertExtent[iVert][iAdjNext]:=rec(status:="set", MatchVert:=MatchVert, MatchPos:=PrevPos);
            ListVertExtent[MatchVert][PrevPos]:=rec(status:="set", MatchVert:=iVert, MatchPos:=iAdjNext);
            nbAction:=nbAction+1;
          fi;
        fi;
        iAdjPrev:=PrevIdx(eDeg, iAdj);
        if ListVertExtent[iVert][iAdj].status="set" and ListVertExtent[iVert][iAdjPrev].status="unset" then
          eEdge:=ListVertExtent[iVert][iAdj];
          for i in [1..eDegFace-2]
          do
            if eEdge.status="set" then
              MatchVert:=eEdge.MatchVert;
              MatchPos:=eEdge.MatchPos;
              MatchDeg:=ListDeg[MatchVert];
              NextPos:=NextIdx(MatchDeg, MatchPos);
              eEdge:=ListVertExtent[MatchVert][NextPos];
            fi;
          od;
          if eEdge.status="set" then
            MatchVert:=eEdge.MatchVert;
            MatchPos:=eEdge.MatchPos;
            MatchDeg:=ListDeg[MatchVert];
            NextPos:=NextIdx(MatchDeg, MatchPos);
            ListVertExtent[iVert][iAdjPrev]:=rec(status:="set", MatchVert:=MatchVert, MatchPos:=NextPos);
            ListVertExtent[MatchVert][NextPos]:=rec(status:="set", MatchVert:=iVert, MatchPos:=iAdjPrev);
            nbAction:=nbAction+1;
          fi;
        fi;
      od;
    od;
    if nbAction=0 then
      break;
    fi;
  od;
  return rec(ListDeg:=ListDeg, ListListStatus:=ListListStatus, ListVertExtent:=ListVertExtent);
end;


ConvertRecCluster:=function(eDegFace, eRecCluster)
  local nbVertCluster, TotalRec, NewLEnt, iVert, eDeg, ListShiftDE, iAdj, eEdge, MatchVert, MatchPos, eEnt, NewEnt;
  nbVertCluster:=Length(eRecCluster.LEnt);
  TotalRec:=ConvertRecCluster_Kernel(eDegFace, eRecCluster);
  NewLEnt:=[];
  for iVert in [1..nbVertCluster]
  do
    eDeg:=TotalRec.ListDeg[iVert];
    ListShiftDE:=[];
    for iAdj in [1..eDeg]
    do
      if TotalRec.ListListStatus[iVert][iAdj]=0 and TotalRec.ListVertExtent[iVert][iAdj].status="set" then
        eEdge:=TotalRec.ListVertExtent[iVert][iAdj];
        MatchVert:=eEdge.MatchVert;
        MatchPos:=eEdge.MatchPos;
        TotalRec.ListListStatus[iVert][iAdj]:=1;
        TotalRec.ListListStatus[MatchVert][MatchPos]:=1;
        Add(ListShiftDE, iAdj-1);
      fi;
    od;
    if iVert>1 then
      Add(ListShiftDE, 0);
    fi;
    eEnt:=eRecCluster.LEnt[iVert];
    NewEnt:=rec(p:=eEnt.p, ListSymb:=eEnt.ListSymb, ListShiftDE:=ListShiftDE);
    Add(NewLEnt, NewEnt);
  od;
  return rec(LEnt:=NewLEnt);
end;



WriteConvertedRecCluster_Kernel:=function(eDegFace, eRecCluster)
  local TotalRec, len, lenBound, nbVert, iVert, eDeg, iAdj, ListDE, eListNext, eListPrev, eListInv, RetListNext, RetListPrev, RetListInv, posNext, posInv, iDE, eDE, MatchVert, MatchPos, iAdjPrev, NextDE, InvDE, TheFirstDEnoprev, PreListInternalDeg, ListInternalDeg, TheCycle, eInternalDeg, ListIDEnoprev, TheDEnoprev, iMap, iMapNext, iMapPrev, iMapInv, iNext, iPrev, iInv, i, nextDE, NewListIndex, NewListIndexRev;
  TotalRec:=ConvertRecCluster_Kernel(eDegFace, eRecCluster);
  len:=0;
  lenBound:=0;
  nbVert:=Length(eRecCluster.LEnt);
  for iVert in [1..nbVert]
  do
    eDeg:=TotalRec.ListDeg[iVert];
    for iAdj in [1..eDeg]
    do
      if TotalRec.ListVertExtent[iVert][iAdj].status="set" then
        len:=len + 1;
      else
        len:=len + 2;
        lenBound:=lenBound + 1;
      fi;
    od;
  od;
  ListDE:=[];
  for iVert in [1..nbVert]
  do
    eDeg:=TotalRec.ListDeg[iVert];
    for iAdj in [1..eDeg]
    do
      if TotalRec.ListVertExtent[iVert][iAdj].status="set" then
        Add(ListDE, rec(iVert:=iVert, iAdj:=iAdj, status:="set"));
      else
        Add(ListDE, rec(iVert:=iVert, iAdj:=iAdj, status:="unset", val:=0)); # from the vertex
        Add(ListDE, rec(iVert:=iVert, iAdj:=iAdj, status:="unset", val:=1)); # opposite
      fi;
    od;
  od;
  eListNext:=ListWithIdenticalEntries(len,-1);
  eListPrev:=ListWithIdenticalEntries(len,-1);
  eListInv :=ListWithIdenticalEntries(len,-1);
  if len<>Length(ListDE) then
    Error("LEngth has been wrongly assigned");
  fi;
  for iDE in [1..len]
  do
    eDE:=ListDE[iDE];
    iVert:=eDE.iVert;
    iAdj:=eDE.iAdj;
    eDeg:=TotalRec.ListDeg[iVert];
    iAdjPrev:=PrevIdx(eDeg, iAdj);
    if eDE.status="unset" then
      if eDE.val=0 then
        if TotalRec.ListVertExtent[iVert][iAdjPrev].status="unset" then
          NextDE:=rec(iVert:=iVert, iAdj:=iAdjPrev, status:="unset", val:=1);
        else
          MatchVert:=TotalRec.ListVertExtent[iVert][iAdjPrev].MatchVert;
          MatchPos :=TotalRec.ListVertExtent[iVert][iAdjPrev].MatchPos;
          NextDE:=rec(iVert:=MatchVert, iAdj:=MatchPos, status:="set");
        fi;
        posNext:=Position(ListDE, NextDE);
        eListNext[iDE]:=posNext;
        eListPrev[posNext]:=iDE;
      fi;
      InvDE:=rec(iVert:=iVert, iAdj:=iAdj, status:="unset", val:=1-eDE.val);
    else
      if TotalRec.ListVertExtent[iVert][iAdjPrev].status="unset" then
        NextDE:=rec(iVert:=iVert, iAdj:=iAdjPrev, status:="unset", val:=1);
      else
        MatchVert:=TotalRec.ListVertExtent[iVert][iAdjPrev].MatchVert;
        MatchPos :=TotalRec.ListVertExtent[iVert][iAdjPrev].MatchPos;
        NextDE:=rec(iVert:=MatchVert, iAdj:=MatchPos, status:="set");
      fi;
      posNext:=Position(ListDE, NextDE);
      eListNext[iDE]:=posNext;
      eListPrev[posNext]:=iDE;
      #
      MatchVert:=TotalRec.ListVertExtent[iVert][iAdj].MatchVert;
      MatchPos :=TotalRec.ListVertExtent[iVert][iAdj].MatchPos;
      InvDE:=rec(iVert:=MatchVert, iAdj:=MatchPos, status:="set");
    fi;
    posInv:=Position(ListDE, InvDE);
    eListInv[iDE]:=posInv;
  od;
  ListIDEnoprev:=Filtered([1..len], x->eListPrev[x]=-1);
  if Length(ListIDEnoprev)<>lenBound then
    Error("Clear thinking error 1");
  fi;
  TheFirstDEnoprev:=ListIDEnoprev[1];
  TheDEnoprev:=TheFirstDEnoprev;
  TheCycle:=[];
  PreListInternalDeg:=[];
  for i in [1..lenBound]
  do
    eInternalDeg:=0;
    iDE:=TheDEnoprev;
    while(true)
    do
      nextDE:=eListNext[iDE];
      if nextDE=-1 then
        break;
      fi;
      eInternalDeg:=eInternalDeg+1;
      iDE:=nextDE;
    od;
    Add(TheCycle, TheDEnoprev);
    Add(PreListInternalDeg, eInternalDeg);
    TheDEnoprev:=eListInv[iDE];
  od;
  if TheDEnoprev<>TheFirstDEnoprev then
    Error("Inconsistency error in the iteration");
  fi;
  if Set(TheCycle)<>Set(ListIDEnoprev) then
    Error("Our logic has been broken");
  fi;
  NewListIndex:=Reversed(TheCycle);
  ListInternalDeg:=Reversed(PreListInternalDeg);
  for i in [1..len]
  do
    if eListPrev[i]<>-1 then
      Add(NewListIndex, i);
    fi;
  od;
  NewListIndexRev:=ListWithIdenticalEntries(len,-1);
  for i in [1..len]
  do
    iMap:=NewListIndex[i];
    NewListIndexRev[iMap]:=i;
  od;
  RetListNext:=[];
  RetListPrev:=[];
  RetListInv:=[];
  for i in [1..len]
  do
    iMap:=NewListIndex[i];
    iMapNext:=eListNext[iMap];
    iMapPrev:=eListPrev[iMap];
    iMapInv :=eListInv [iMap];
    if iMapNext=-1 then
      iNext:=-1;
    else
      iNext:=NewListIndexRev[iMapNext];
    fi;
    if iMapPrev=-1 then
      iPrev:=-1;
    else
      iPrev:=NewListIndexRev[iMapPrev];
    fi;
    iInv:=NewListIndexRev[iMapInv];
    RetListNext[i]:=iNext;
    RetListPrev[i]:=iPrev;
    RetListInv [i]:=iInv;
  od;
  #
  return rec(len:=len, lenBound:=lenBound,
             ListInternalDeg:=ListInternalDeg,
             ListNext:=RetListNext,
             ListPrev:=RetListPrev,
             ListInv:=RetListInv);
end;


WriteConvertedRecCluster:=function(output, eDegFace, eRecCluster)
  local TotRec, i, iNext, iPrev, iInv;
  TotRec:=WriteConvertedRecCluster_Kernel(eDegFace, eRecCluster);
  AppendTo(output, TotRec.len, "\n");
  AppendTo(output, TotRec.lenBound, "\n");
  for i in [1..TotRec.lenBound]
  do
    AppendTo(output, " ", TotRec.ListInternalDeg[i]);
  od;
  AppendTo(output, "\n");
  for i in [1..TotRec.len]
  do
    iNext:=TotRec.ListNext[i];
    iPrev:=TotRec.ListPrev[i];
    iInv:=TotRec.ListInv[i];
    if iNext >= 1 then
      iNext:=iNext-1;
    fi;
    if iPrev >= 1 then
      iPrev:=iPrev-1;
    fi;
    if iInv >= 1 then
      iInv:=iInv-1;
    fi;
    AppendTo(output, " ", iNext, " ", iPrev, " ", iInv, "\n");
  od;
end;





DoLegoTilingEnumeration:=function(LegoInfo, ListRecCluster)
  local VEFori, eInv, eNext, ePrev, nbDE, nbFace, GetRecordBlock, TheMat, ListRecBlock, eRecCluster, eRecBlock, eLine, ListSol, ListSolFinal, eSol, eVectXcond, eVectYcond, nbRow, nbCol, DualPLori, ListEdges, ListDualEdges, ListPairDE, iEdge, iFace, jFace, iVert, jVert, iDE, jDE, eNextPL, len, i, nbVert, nbEdge, GRPori, rDE, eO, O, iBlock, nbBlock, ListColor, eRecPLover, ListCases, LAdj, eSolFinal, eEdge, ListClusterOrigin, iCluster, nbCluster, SetClusterOrigin, PreListRecBlockSet, eSetBlock, PreTheMat, PreListRecBlock, PreListClusterOrigin, ListIedge, eBlEdge, eBlVert, eIdx, ListListEdgeStatus, ListEdgeStatus, eListEdgeStatus, pos;
  DualPLori:=LegoInfo.DualPLori;
  eInv:=DualPLori.invers;
  eNext:=DualPLori.next;
  ePrev:=Inverse(DualPLori.next);
  nbDE:=DualPLori.nbP;
  nbVert:=Length(LegoInfo.VEFori.VertSet);
  nbEdge:=Length(LegoInfo.VEFori.EdgeSet);
  nbFace:=Length(LegoInfo.VEFori.FaceSet);
  GetRecordBlock:=function(iDE, eRecCluster)
    local eBlockVert, eBlockEdge, eEnt, eP, jDE, kDE, eVal, iVert, siz, i, eShift;
    eBlockVert:=[];
    eBlockEdge:=[];
    for eEnt in eRecCluster.LEnt
    do
      eP:=eEnt.p;
      jDE:=iDE;
      for eVal in eEnt.ListSymb
      do
        if eVal="i" then
          jDE:=OnPoints(jDE, eInv);
        fi;
        if eVal="n" then
          jDE:=OnPoints(jDE, eNext);
        fi;
        if eVal="p" then
          jDE:=OnPoints(jDE, ePrev);
        fi;
      od;
      iVert:=LegoInfo.VEFori.ListOriginVert[jDE];
      for eShift in eEnt.ListShiftDE
      do
        kDE:=jDE;
        for i in [1..eShift]
        do
          kDE:=OnPoints(kDE, eNext);
        od;
        iEdge:=LegoInfo.VEFori.ListOriginEdge[kDE];
        Add(eBlockEdge, iEdge);
      od;
      siz:=Length(LegoInfo.VEFori.VertSet[iVert]);
      if siz<>eP then
        return fail;
      fi;
      Add(eBlockVert, iVert);
    od;
    return rec(BlockVert:=Set(eBlockVert), BlockEdge:=Set(eBlockEdge));
  end;
  PreTheMat:=[];
  PreListRecBlock:=[];
  PreListClusterOrigin:=[];
  nbCluster:=Length(ListRecCluster);
  for iDE in [1..nbDE]
  do
    for iCluster in [1..nbCluster]
    do
      eRecCluster:=ListRecCluster[iCluster];
      eRecBlock:=GetRecordBlock(iDE, eRecCluster);
      if eRecBlock<>fail then
        eLine:=ListWithIdenticalEntries(nbVert, 0);
        eLine{eRecBlock.BlockVert}:=ListWithIdenticalEntries(Length(eRecBlock.BlockVert),1);
        Add(PreTheMat, eLine);
        Add(PreListRecBlock, eRecBlock);
        Add(PreListClusterOrigin, iCluster);
      fi;
    od;
  od;
  #
  # We can have duplications. Yes.
  #
  PreListRecBlockSet:=Set(PreListRecBlock);
  eSetBlock:=List(PreListRecBlockSet, x->Position(PreListRecBlock, x));
  TheMat:=PreTheMat{eSetBlock};
  ListRecBlock:=PreListRecBlock{eSetBlock};
  ListClusterOrigin:=PreListClusterOrigin{eSetBlock};
  #
  nbRow:=Length(TheMat);
  if nbRow=0 then
    return rec(ListSolFinal:=[], ListCases:=[]);
  fi;
  nbCol:=Length(TheMat[1]);
  eVectXcond:=ListWithIdenticalEntries(nbRow,1);
  eVectYcond:=ListWithIdenticalEntries(nbCol,1);
  ListSol:=EnumerateLibexactSolution(TheMat, eVectXcond, eVectYcond);
  #
  ListSolFinal:=[];
  ListListEdgeStatus:=[];
  for eSol in ListSol
  do
    SetClusterOrigin:=Set(ListClusterOrigin{eSol});
    if Length(SetClusterOrigin)=nbCluster then
      ListEdgeStatus:=ListWithIdenticalEntries(nbEdge,1);
      for eIdx in eSol
      do
        eBlEdge:=ListRecBlock[eIdx].BlockEdge;
        ListEdgeStatus{eBlEdge}:=ListWithIdenticalEntries(Length(eBlEdge),0);
      od;
      Add(ListListEdgeStatus, ListEdgeStatus);
      Add(ListSolFinal, eSol);
    fi;
  od;
  O:=Orbits(LegoInfo.GRPori.SymmetryGroupEdge, ListListEdgeStatus, Permuted);
  ListCases:=[];
  for eO in O
  do
    eListEdgeStatus:=eO[1];
    pos:=Position(ListListEdgeStatus, eListEdgeStatus);
    eSol:=ListSolFinal[pos];
    ListColor:=ListWithIdenticalEntries(nbVert,0);
    for i in [1..Length(eSol)]
    do
      eBlVert:=ListRecBlock[eSol[i]].BlockVert;
      ListColor{eBlVert}:=ListWithIdenticalEntries(Length(eBlVert), i);
    od;
    ListIedge:=Filtered([1..nbEdge], x->eListEdgeStatus[x]=1);
    eRecPLover:=rec(PLori:=LegoInfo.PLori, ListIedge:=ListIedge, ListColor:=ListColor);
    Add(ListCases, eRecPLover);
  od;
  return rec(ListSolFinal:=ListSolFinal, ListCases:=ListCases);
end;



SingleExportForGraph:=function(PrePrefixMerge, PLori, RecRequest)
  local VEFori, nbVert, nbEdge, nbFace, Charac, PrefixMerge, SetEdge, ListTraitIDE, iEdge, iDE, eStab, GPU, PRefixMerge, DoCageOutput, FileNameCaGe, PL, RecSplit, eRecPLoverWork, FileNameRec, File_FinalSVG, File_FinalSVGred, File_PlaneGraph, File_PlaneGraphRed, DoCaGeOutput, DoSVGoutput, File_View, File_ViewRed, eRec, File_Option, File_OptionRed, eExtInfo, TheDir, eComm, TheCommand, MaxIter, DoEPS, DoPNG, DoPDF, File_EPS, File_EPS_red, File_PNG, File_PNG_red, File_PDF, File_PDF_red, eCommINK, FundamentalTraitSize, DrawFundamentalDomain, FundamentalRGB, eRecPLover, GRPori, ListExportFormat, DoOverwrite, DoOper;
  if IsBound(RecRequest.eRecPLover) then
    eRecPLover:=RecRequest.eRecPLover;
  else
    eRecPLover:=rec(ListIedge:=[]);
  fi;
  if IsBound(RecRequest.GRPori) then
    GRPori:=RecRequest.GRPori;
  else
    GRPori:=GroupPlanOriented(PLori);
  fi;
  VEFori:=GRPori.CC.VEF;
  nbVert:=Length(VEFori.VertSet);
  nbFace:=Length(VEFori.FaceSet);
  nbEdge:=Length(VEFori.EdgeSet);
  Charac:=nbVert - nbEdge + nbFace;
  SetEdge:=Set(List(eRecPLover.ListIedge, x->nbVert + x));
  DoEPS:=false;
  DoPNG:=false;
  DoPDF:=false;
  if IsBound(RecRequest.DoEPS) then
    DoEPS:=RecRequest.DoEPS;
  fi;
  if IsBound(RecRequest.DoPNG) then
    DoPNG:=RecRequest.DoPNG;
  fi;
  if IsBound(RecRequest.DoPDF) then
    DoPDF:=RecRequest.DoPDF;
  fi;
  ListExportFormat:=[];
  if DoEPS then
    Add(ListExportFormat, "eps");
  fi;
  if DoPNG then
    Add(ListExportFormat, "png");
  fi;
  if DoPDF then
    Add(ListExportFormat, "pdf");
  fi;
  #
  DrawFundamentalDomain:=false;
  if IsBound(RecRequest.DrawFundamentalDomain) then
    DrawFundamentalDomain:=RecRequest.DrawFundamentalDomain;
  fi;
  FundamentalTraitSize:=1;
  if IsBound(RecRequest.FundamentalTraitSize) then
    FundamentalTraitSize:=RecRequest.FundamentalTraitSize;
  fi;
  FundamentalRGB:=1;
  if IsBound(RecRequest.FundamentalRGB) then
    FundamentalRGB:=RecRequest.FundamentalRGB;
  fi;
  #
  ListTraitIDE:=[];
  for iEdge in eRecPLover.ListIedge
  do
    for iDE in VEFori.EdgeSet[iEdge]
    do
      Add(ListTraitIDE, iDE-1);
    od;
  od;
  if Length(ListTraitIDE)<>Length(Set(ListTraitIDE)) then
    Error("Repetitions in ListTraitIDE");
  fi;
  #
  eStab:=Stabilizer(GRPori.SymmetryGroup, SetEdge, OnSets);
  GPU:=GRPori.FunctionSymmetry(eStab);
  PrefixMerge:=Concatenation(PrePrefixMerge, "_", GPU.GenSymbol);
  TheDir:=GetDirectoryFromFile(PrefixMerge);
  DoCaGeOutput:=false;
  FileNameCaGe:=Concatenation(PrefixMerge,".cage");
  if DoCaGeOutput and IsExistingFile(FileNameCaGe)=false then
    PL:=eRecPLover.PL;
    RecSplit:=GetSplitOperationPlanGraph(PL);
    if RecSplit.split="nosplit" then
      eRecPLoverWork:=eRecPLover;
    fi;
    if RecSplit.split="vertsplit" then
      eRecPLoverWork:=RemoveVertexOverlined(eRecPLover, RecSplit.eVert);
    fi;
    if RecSplit.split="edgesplit" then
      eRecPLoverWork:=RemoveEdgeOverlined(eRecPLover, RecSplit.eEdge);
    fi;
    PlanGraphToCaGeOverlined(FileNameCaGe, eRecPLoverWork);
    FileNameRec:=Concatenation(PrefixMerge, ".rec");
    SaveDataToFile(FileNameRec, eRecPLover);
  fi;
  #
  DoSVGoutput:=true;
  File_FinalSVG:=Concatenation(PrefixMerge, ".svg");
  File_FinalSVGred:=GetFinalFile(File_FinalSVG);
  if IsBound(RecRequest.DoOverwrite) then
    DoOverwrite:=RecRequest.DoOverwrite;
  else
    DoOverwrite:=true;
  fi;
  DoOper:=true;
  if DoOverwrite=false then
    if IsExistingFile(File_FinalSVG) then
      DoOper:=false;
    fi;
  fi;
  if DoSVGoutput and DoOper then
    #
    File_PlaneGraph:=Concatenation(PrefixMerge, ".plane");
    File_PlaneGraphRed:=GetFinalFile(File_PlaneGraph);
    WritePlanGraphOrientedToCpp(File_PlaneGraph, PLori);
    #
    File_Option:=Concatenation(PrefixMerge, ".option");
    File_OptionRed:=GetFinalFile(File_Option);
    File_EPS:=Concatenation(PrefixMerge, ".eps");
    File_PNG:=Concatenation(PrefixMerge, ".png");
    File_PDF:=Concatenation(PrefixMerge, ".pdf");
    File_EPS_red:=GetFinalFile(File_EPS);
    File_PNG_red:=GetFinalFile(File_PNG);
    File_PDF_red:=GetFinalFile(File_PDF);
    eRec:=rec(Charac:=Charac,
    
              PlaneFile:=File_PlaneGraphRed,
              OutFile:=File_FinalSVGred,
              MAX_ITER_PrimalDual:=-1,
              MAX_ITER_CaGe:=1000,
	      ListExportFormat:=ListExportFormat,
	      CaGeProcessPolicy:=2,
              width:=600,
              height:=600,
              RoundMethod:=2,
              MethodInsert:=2,
	      
              MultTangent:=1/2,
              DoMethod1:=true,
              DoMethod2:=false,
              DoMethod3:=false,
              EDGE_NormalTraitSize:=1,
              EDGE_ListTraitIDE:=ListTraitIDE,
              EDGE_ListTraitGroup:=ListWithIdenticalEntries(Length(ListTraitIDE),0),
              EDGE_ListTraitSize:=[4],
              EDGE_DefaultRGB:=[0,0,0],
              EDGE_SpecificRGB_iDE:=[],
              EDGE_SpecificRGB_Group:=[],
              EDGE_SpecificRGB_R:=[],
              EDGE_SpecificRGB_G:=[],
              EDGE_SpecificRGB_B:=[],

              VERT_NormalRadius:=1/200,
              VERT_ListRadiusIDE:=[],
              VERT_ListRadiusGroup:=[],
              VERT_ListRadius:=[],
              VERT_DefaultRGB:=[0,0,0],
              VERT_SpecificRGB_iDE:=[],
              VERT_SpecificRGB_Group:=[],
              VERT_SpecificRGB_R:=[],
              VERT_SpecificRGB_G:=[],
              VERT_SpecificRGB_B:=[]);
    #
    if Charac=2 then
      File_View:=Concatenation(PrefixMerge, ".view");
      File_ViewRed:=GetFinalFile(File_View);
      eExtInfo:=GetSplitOperationPlanGraphOriented(PLori);
      WriteExtViewPlanGraphOrientedToCPP(File_View, eExtInfo);
      eRec.ViewFile:=File_ViewRed;
      eRec.DoExternalArrow:=true;
      eRec.ScalExtensionArrow:=2;
      eRec.LengthExtensionArrow:=1/2;
    fi;
    if Charac=0 then
      eRec.minimal:=10^(-11);
      eRec.tol:=10^(-5);
      eRec.AngDeg:=0;
      eRec.scal:=1/2;
      eRec.shiftX:=0;
      eRec.shiftY:=0;
      eRec.FundamentalRGB:=[255,0,0];
      eRec.FundamentalTraitSize:=FundamentalTraitSize;
      eRec.DrawFundamentalDomain:=DrawFundamentalDomain;
    fi;
    #
    Print("File_Option=", File_Option, "\n");
    WriteOptionToPlottingCpp(File_Option, eRec);
    #
    eComm:="CombPlaneToSVG";
    TheCommand:=Concatenation("(cd ", TheDir, " && ", eComm, " ", File_OptionRed, ")");
    Exec(TheCommand);
    if IsExistingFile(File_FinalSVG)=false then
      Error("The program CombPlaneToSVG has not completed its function");
    fi;
  fi;
end;







ExportForGraph:=function(ListRecAnswer, PrefixOut, RecRequest)
  local len, posFirst, PLori, GRPori, eSymbol, i, ListCases, nbCase, iCase, eRecPLover, PrePrefixMerge, NewRecRequest;
  len:=Length(ListRecAnswer);
  posFirst:=First([1..len], x->Length(ListRecAnswer[x].ListCases)>0);
  if posFirst=fail then
    Error("No cases to print. Likely to be an error");
  fi;
  PLori:=ListRecAnswer[posFirst].ListCases[1].PLori;
  GRPori:=GroupPlanOriented(PLori);
  eSymbol:=GRPori.GenSymbol;
  for i in [1..len]
  do
    ListCases:=ListRecAnswer[i].ListCases;
    nbCase:=Length(ListCases);
    for iCase in [1..nbCase]
    do
      eRecPLover:=ListCases[iCase];
      PrePrefixMerge:=Concatenation(PrefixOut, "_", eSymbol, "_", String(i), "_-_", String(iCase));
      NewRecRequest:=RecRequest;
      NewRecRequest.eRecPLover:=eRecPLover;
      NewRecRequest.GRPori:=GRPori;
      NewRecRequest.DoOverwrite:=false;
      SingleExportForGraph(PrePrefixMerge, PLori, NewRecRequest);
    od;
  od;
end;


ExportMostSymmetricLegoGraph:=function(ListRecAnswer, iCase, PrefixOut, RecRequest)
  local PLori, GRPori, VEFori, nbVert, eSymbol, ListCases, nbOrb, ListStabSize, iOrb, eRecPLover, SetEdge, eStab, eStabSize, MaxStabSize, iOrbMax, eRecPLoverMax, PrePrefixMerge, NewRecRequest;
  PLori:=ListRecAnswer[iCase].ListCases[1].PLori;
  GRPori:=GroupPlanOriented(PLori);
  VEFori:=GRPori.CC.VEF;
  nbVert:=Length(VEFori.VertSet);
  eSymbol:=GRPori.GenSymbol;
  #
  ListCases:=ListRecAnswer[iCase].ListCases;
  nbOrb:=Length(ListCases);
  ListStabSize:=[];
  for iOrb in [1..nbOrb]
  do
    eRecPLover:=ListCases[iOrb];
    SetEdge:=Set(List(eRecPLover.ListIedge, x->nbVert + x));
    eStab:=Stabilizer(GRPori.SymmetryGroup, SetEdge, OnSets);
    eStabSize:=Order(eStab);
    Add(ListStabSize, eStabSize);
  od;
  MaxStabSize:=Maximum(ListStabSize);
  iOrbMax:=First([1..nbOrb], x->ListStabSize[x]=MaxStabSize);
  #
  eRecPLoverMax:=ListCases[iOrbMax];
  PrePrefixMerge:=Concatenation(PrefixOut, "_", eSymbol, "_", String(iCase), "_-_", String(iOrbMax));
  Print("MostSymmetricExport iCase=", iCase, " eSymbol=", eSymbol, " MaxStabSize=", MaxStabSize, "\n");
  NewRecRequest:=RecRequest;
  NewRecRequest.eRecPLover:=eRecPLoverMax;
  NewRecRequest.GRPori:=GRPori;
  NewRecRequest.DoOverwrite:=false;
  SingleExportForGraph(PrePrefixMerge, PLori, NewRecRequest);
end;




ExportMostSymmetricLego_SingleGraph:=function(ListRecAnswer, PrefixOut, RecRequest)
  local PLori, GRPori, VEFori, nbVert, eSymbol, ListCases, nbOrb, ListStabSize, iOrb, eRecPLover, SetEdge, eStab, eStabSize, MaxStabSize, iOrbMax, eRecPLoverMax, PrePrefixMerge, ListCons, ListICase, ListIOrb, nbWork, iMax, iCaseMax, iCase, nbCase, GetPLori, NewRecRequest;
  GetPLori:=function()
    local eRecAnswer, eCase;
    for eRecAnswer in ListRecAnswer
    do
      for eCase in eRecAnswer.ListCases
      do
        return eCase.PLori;
      od;
    od;
    Error("Failed to find an entry. Likely there are no lego");
  end;
  PLori:=GetPLori();
  GRPori:=GroupPlanOriented(PLori);
  VEFori:=GRPori.CC.VEF;
  nbVert:=Length(VEFori.VertSet);
  eSymbol:=GRPori.GenSymbol;
  #
  nbCase:=Length(ListRecAnswer);
  ListStabSize:=[];
  ListCons:=[];
  ListICase:=[];
  ListIOrb:=[];
  for iCase in [1..nbCase]
  do
    ListCases:=ListRecAnswer[iCase].ListCases;
    nbOrb:=Length(ListCases);
    for iOrb in [1..nbOrb]
    do
      eRecPLover:=ListCases[iOrb];
      SetEdge:=Set(List(eRecPLover.ListIedge, x->nbVert + x));
      eStab:=Stabilizer(GRPori.SymmetryGroup, SetEdge, OnSets);
      eStabSize:=Order(eStab);
      Add(ListICase, iCase);
      Add(ListIOrb, iOrb);
      Add(ListCons, eRecPLover);
      Add(ListStabSize, eStabSize);
    od;
  od;
  MaxStabSize:=Maximum(ListStabSize);
  nbWork:=Length(ListCons);
  iMax:=First([1..nbWork], x->ListStabSize[x]=MaxStabSize);
  #
  eRecPLoverMax:=ListCons[iMax];
  iCaseMax:=ListICase[iMax];
  iOrbMax:=ListIOrb[iMax];
  PrePrefixMerge:=Concatenation(PrefixOut, "_", eSymbol, "_", String(iCaseMax), "_-_", String(iOrbMax));
  Print("MostSymmetricExport iCase=", iCase, " eSymbol=", eSymbol, " MaxStabSize=", MaxStabSize, "\n");
  NewRecRequest:=RecRequest;
  NewRecRequest.eRecPLover:=eRecPLoverMax;
  NewRecRequest.GRPori:=GRPori;
  NewRecRequest.DoOverwrite:=false;
  SingleExportForGraph(PrePrefixMerge, PLori, NewRecRequest);
end;




ExportMostSymmetricLego_AllLegoGraph:=function(ListRecAnswer, PrefixOut, RecRequest)
  local PLori, GRPori, VEFori, nbVert, eSymbol, ListCases, nbOrb, ListStabSize, iOrb, eRecPLover, SetEdge, eStab, eStabSize, MaxStabSize, iOrbMax, eRecPLoverMax, PrePrefixMerge, ListCons, ListICase, ListIOrb, nbWork, iMax, iCaseMax, iCase, nbCase, GetPLori, NewRecRequest;
  GetPLori:=function()
    local eRecAnswer, eCase;
    for eRecAnswer in ListRecAnswer
    do
      for eCase in eRecAnswer.ListCases
      do
        return eCase.PLori;
      od;
    od;
    Error("Failed to find an entry. Likely there are no lego");
  end;
  PLori:=GetPLori();
  GRPori:=GroupPlanOriented(PLori);
  VEFori:=GRPori.CC.VEF;
  nbVert:=Length(VEFori.VertSet);
  eSymbol:=GRPori.GenSymbol;
  #
  nbCase:=Length(ListRecAnswer);
  ListStabSize:=[];
  ListCons:=[];
  ListICase:=[];
  ListIOrb:=[];
  for iCase in [1..nbCase]
  do
    ListCases:=ListRecAnswer[iCase].ListCases;
    nbOrb:=Length(ListCases);
    for iOrb in [1..nbOrb]
    do
      eRecPLover:=ListCases[iOrb];
      SetEdge:=Set(List(eRecPLover.ListIedge, x->nbVert + x));
      eStab:=Stabilizer(GRPori.SymmetryGroup, SetEdge, OnSets);
      eStabSize:=Order(eStab);
      #
      PrePrefixMerge:=Concatenation(PrefixOut, "_", eSymbol, "_", String(iCase), "_-_", String(iOrb));
      NewRecRequest:=RecRequest;
      NewRecRequest.eRecPLover:=eRecPLover;
      NewRecRequest.GRPori:=GRPori;
      NewRecRequest.DoOverwrite:=false;
      SingleExportForGraph(PrePrefixMerge, PLori, NewRecRequest);
    od;
  od;
end;










GetPrefixOut:=function(eCase)
  local ListPair, g, kCodeg, eSumIncd, ePair, nbV, PrefixOut;
  ListPair:=eCase.ListPair;
  g:=eCase.g;
  kCodeg:=eCase.kCodeg;
  eSumIncd:=0;
  for ePair in ListPair
  do
    eSumIncd:=eSumIncd + ePair[1]*ePair[2];
  od;
  nbV:=eSumIncd/kCodeg;
  #
  PrefixOut:=Concatenation("CASE_g", String(g), "_k", String(kCodeg), "_n", String(nbV), "_-_", String(ListPair[1][1]), "_", String(ListPair[1][2]), "_-_", String(ListPair[2][1]), "_", String(ListPair[2][2]));
  return PrefixOut;
end;


GetFileNameStore_Kernel:=function(eCase)
  local ListPair, g, kCodeg, nbV, FileName, nbPair, iPair, ePair;
  ListPair:=eCase.ListPair;
  g:=eCase.g;
  kCodeg:=eCase.kCodeg;
  nbV:=eCase.nbV;
  FileName:=Concatenation("LPL_g", String(g), "_k", String(kCodeg), "_p");
  nbPair:=Length(ListPair);
  for iPair in [1..nbPair]
  do
    if iPair>1 then
      FileName:=Concatenation(FileName, "_-_");
    fi;
    ePair:=ListPair[iPair];
    FileName:=Concatenation(FileName, String(ePair[1]), "_", String(ePair[2]));
  od;
  return Concatenation(FileName, "_n", String(nbV));
end;

GetFileNameStore:=function(eCase)
  return Concatenation(GetFileNameStore_Kernel(eCase), ".data");
end;





MultifacedKregularEnumeration:=function(eCase)
  local ListPair, g, kCodeg, nbV, ListNumber, eSumIncd, ePair, PrefixOut, ListBlockType, ListMult, FilteringFunction, ListCases, specCase, TheFileOutRed, TheFileOut, output, nbBlockType, i, eVal, SelfAdj, TheTarget;
  ListPair:=eCase.ListPair;
  g:=eCase.g;
  kCodeg:=eCase.kCodeg;
  nbV:=eCase.nbV;
  ListNumber:=List(ListPair, x->x[2]);
  eSumIncd:=0;
  for ePair in ListPair
  do
    eSumIncd:=eSumIncd + ePair[1]*ePair[2];
  od;
  if nbV<>eSumIncd/kCodeg then
    Error("Inconsistency in number of vertices");
  fi;
  Print("ListPair=", ListPair, "\n");
  Print("kCodeg=", kCodeg, "\n");
  Print("nbV=", nbV, "\n");
  PrefixOut:=Concatenation("DATAmultigraph/CASE_g", String(g), "_k", String(kCodeg), "_n", String(nbV));
  for ePair in ListPair
  do
    PrefixOut:=Concatenation(PrefixOut, "_-_", String(ePair[1]), "_", String(ePair[2]));
  od;
  PrefixOut:=Concatenation(PrefixOut, "/");
  Print("After PrefixOut assignation\n");
  Exec("mkdir -p ", PrefixOut);
  #
  # Now creation
  #
  ListBlockType:=[];
  ListMult:=[];
  for ePair in ListPair
  do
    FilteringFunction:=function(eCaseI)
      return true;
    end;
    ListCases:=POLYCYCLE_Enumerate(kCodeg, [ePair[1]], FilteringFunction);
    if Length(ListCases)<>1 then
      Error("We should have only 1 entry");
    fi;
    specCase:=ListCases[1];
    if Length(specCase.ListCluster)<>1 then
      Error("We should have only one cluster");
    fi;
    Add(ListBlockType, specCase.ListCluster[1]);
    Add(ListMult, ePair[2]);
  od;
  TheFileOutRed:="INPUT_SAT";
  TheFileOut:=Concatenation(PrefixOut, TheFileOutRed);
  RemoveFileIfExist(TheFileOut);
  output:=OutputTextFile(TheFileOut, true);
  nbBlockType:=Length(ListBlockType);
  AppendTo(output, " ", nbBlockType, "\n");
  for i in [1..nbBlockType]
  do
    WriteConvertedRecCluster(output, kCodeg, ListBlockType[i]);
  od;
  CloseStream(output);
  #
  if g=1 then
    SelfAdj:=true;
  else
    SelfAdj:=false;
  fi;
  #
  TheFileOut:=Concatenation(PrefixOut, "INPUT_SAT.nml");
  TheTarget:=GetFileNameStore(eCase);
  RemoveFileIfExist(TheFileOut);
  output:=OutputTextFile(TheFileOut, true);
  AppendTo(output, "&ENUM\n");
  AppendTo(output, "  FileListBlockType = \"", TheFileOutRed, "\", \n");
  AppendTo(output, "  OutFile = \"", TheTarget, "\", \n");
  AppendTo(output, "  Approach = \"EXHAUST\", \n");
  AppendTo(output, "!  Approach = \"SAT\", \n");
  AppendTo(output, "  ListMult = ");
  for eVal in ListMult
  do
    AppendTo(output, eVal, ", ");
  od;
  AppendTo(output, "\n");
  AppendTo(output, "  deg = ", kCodeg, ", \n");
  if SelfAdj=true then
    AppendTo(output, "  SelfAdj = T,\n");
  else
    AppendTo(output, "  SelfAdj = F,\n");
  fi;
  AppendTo(output, "  MAX_ITER = -1,\n");
  AppendTo(output, "  MAX_NB_GRAPH = -1,\n");
  AppendTo(output, "/\n\n");
  CloseStream(output);
end;





LegoFunctionEnumeration:=function(eCase, RecRequest)
  local ListPair, g, kCodeg, nbPair, ListNumber, ListNumberRed, ListDegree, eSumIncd, iPair, eNb, eGon, nbV, ListCases, nbCase, nbCaseRed, eFileOut, output, iFileCurrent, iPL, FileSaveLEGO, FileSaveGRP, iPos, iCase, iCaseRed, PLori, ListRecAnswer, LegoInfo, IsRotationGroup, eCaseRed, RecAnswer, RecGRPsave, ListSiz, RecAnswer1, RecAnswer2, SumListCases, eSumSum, TheFilePOLYCYCLE, NbAdmitUnique, NbAdmitOnlyIt, RED_SumListCases, RED_NbAdmitOnlyIt, RED_NbAdmitUnique, FileSaveLEGOred, RecAnswerBoth, ListRecAnswerRed, RecAnswerTot, nbFound, ListSizRed, outputStat, eFileStat, ListFaceSize, NumberWithoutLego, eQuery, idx, eNature, eFileLEGOred, eFileLEGO, PrefixOutPartial, outputRed, eFileOutRed, eSum, eSumRed, eRecStatistics, eFileData, ListQuery, PrefixOut, eGenSymb, DoCasesPrint, idxP, ListIdx, eMaxOrder, pos, ListSymbInfo, OrderGRP, eSymbInfo, ListOrder, ListMatch, nbCaseReal, nbCaseRedReal, MaxNumberOrbitLego, MinNumberOrbitLego, RecAnswerB, FilteringFunction, eIter, FullPolycycleEnumeration, ListCasesExtended, ListClusterMap, nbBlock, WriteSATinput, WriteEXHAUSTinput, TheFileOutRed, TheFileOut, nbCluster, TheTarget, SelfAdj, i, eCaseWork, GlobalComputation, PrintMostSymmetricCases, PrintLegoForEach, PrintAllLego;
  #
  # Initial paperwork computations
  #
  ListPair:=eCase.ListPair;
  g:=eCase.g;
  kCodeg:=eCase.kCodeg;
  nbPair:=Length(ListPair);
  ListNumber:=List(ListPair, x->x[2]);
  ListNumberRed:=RemoveFraction(ListNumber);
  nbBlock:=ListNumber[1] / ListNumberRed[1];
  ListDegree:=[];
  eSumIncd:=0;
  for iPair in [1..nbPair]
  do
    eNb:=ListNumberRed[iPair];
    eGon:=ListPair[iPair][1];
    Append(ListDegree, ListWithIdenticalEntries(eNb, eGon));
    eSumIncd:=eSumIncd + ListNumber[iPair]*eGon;
  od;
  nbV:=eSumIncd/kCodeg;
  Print("ListPair=", ListPair, "\n");
  Print("kCodeg=", kCodeg, "\n");
  Print("ListDegree=", ListDegree, "\n");
  Print("nbV=", nbV, "\n");
  PrefixOut:=Concatenation("DATAcase/CASE_g", String(g), "_k", String(kCodeg), "_n", String(nbV), "_-_", String(ListPair[1][1]), "_", String(ListPair[1][2]), "_-_", String(ListPair[2][1]), "_", String(ListPair[2][2]), "/");
  Print("After PrefixOut assignation\n");
  Exec("mkdir -p ", PrefixOut);
  #
  # Do the SAT enumeration if asked
  #
  if IsBound(RecRequest.WriteSATinput) then
    WriteSATinput:=RecRequest.WriteSATinput;
  else
    WriteSATinput:=false;
  fi;
  if IsBound(RecRequest.WriteEXHAUSTinput) then
    WriteEXHAUSTinput:=RecRequest.WriteEXHAUSTinput;
  else
    WriteEXHAUSTinput:=false;
  fi;
  Print("WriteSATinput=", WriteSATinput, "  WriteEXHAUSTinput=", WriteEXHAUSTinput, "\n");
  if WriteSATinput and WriteEXHAUSTinput then
    Error("Select only one of WriteSATinput and WriteEXHAUSTinput");
  fi;
  if WriteSATinput or WriteEXHAUSTinput then
    FilteringFunction:=function(eCaseI)
      return true;
    end;
    ListCases:=POLYCYCLE_Enumerate(kCodeg, ListDegree, FilteringFunction);
    iCase:=0;
    nbCaseRed:=Length(ListCases);
    for iCaseRed in [1..nbCaseRed]
    do
      Print("WriteSATinput  iCaseRed=", iCaseRed, " / ", nbCaseRed, "\n");
      eCaseWork:=ListCases[iCaseRed];
      TheFileOutRed:=Concatenation("INPUT_SAT", String(iCaseRed));
      TheFileOut:=Concatenation(PrefixOut, TheFileOutRed);
      RemoveFileIfExist(TheFileOut);
      output:=OutputTextFile(TheFileOut, true);
      nbCluster:=Length(eCaseWork.ListCluster);
      AppendTo(output, " ", nbCluster, "\n");
      for i in [1..nbCluster]
      do
        WriteConvertedRecCluster(output, kCodeg, eCaseWork.ListCluster[i]);
      od;
      CloseStream(output);
      #
      if g=1 then
        SelfAdj:=true;
      else
        SelfAdj:=false;
      fi;
      #
      TheFileOut:=Concatenation(PrefixOut, "INPUT_SAT", String(iCaseRed), ".nml");
      TheTarget:=Concatenation(GetFileNameStore(eCase), "_", String(iCaseRed));
      RemoveFileIfExist(TheFileOut);
      output:=OutputTextFile(TheFileOut, true);
      AppendTo(output, "&ENUM\n");
      AppendTo(output, "  FileListBlockType = \"", TheFileOutRed, "\", \n");
      AppendTo(output, "  OutFile = \"", TheTarget, "\", \n");
      if WriteSATinput then
        AppendTo(output, "  Approach = \"SAT\", \n");
      fi;
      if WriteEXHAUSTinput then
        AppendTo(output, "  Approach = \"EXHAUST\", \n");
      fi;
      if nbCluster=1 then
        AppendTo(output, "  ListMult = ", nbBlock, ", \n");
      else
        AppendTo(output, "  ListMult = ", nbBlock, ", 0, \n");
      fi;
      AppendTo(output, "  deg = ", kCodeg, ", \n");
      if SelfAdj=true then
        AppendTo(output, "  SelfAdj = T,\n");
      else
        AppendTo(output, "  SelfAdj = F,\n");
      fi;
      AppendTo(output, "  MAX_ITER = -1,\n");
      AppendTo(output, "  MAX_NB_GRAPH = -1,\n");
      AppendTo(output, "/\n\n");
      CloseStream(output);
    od;
  fi;
  #
  # Check if more is needed
  #
  if IsBound(RecRequest.GlobalComputation) then
    GlobalComputation:=RecRequest.GlobalComputation;
  else
    GlobalComputation:=true;
  fi;
  if GlobalComputation=false then
    return rec();
  fi;
  #
  # The computation of list of relevant graphs
  #
  eIter:=IteratorListPlanGraph(PrefixOut, eCase);
  #
  # Polycycle computations
  #
  TheFilePOLYCYCLE:=Concatenation(PrefixOut, "ListPolycycle");
  if IsBound(eCase.FullPolycycleEnumeration) then
    FullPolycycleEnumeration:=eCase.FullPolycycleEnumeration;
  else
    FullPolycycleEnumeration:=true;
  fi;
  if FullPolycycleEnumeration=true then
    FilteringFunction:=function(eCaseI)
      return true;
    end;
  else
    FilteringFunction:=function(eCaseI)
      local LPLtot, eCaseRev, eCluster, fCluster, ListRecCluster, PLori, RecTest;
      LPLtot:=eIter.GetAll();
      eCaseRev:=POLYCYCLE_PlaneSymmetry(eCaseI);
      if POLYCYCLE_TestIsomorphismOriented(eCaseRev, eCaseI)=true then
        eCluster:=POLYCYCLE_ConvertToRecCluster(eCaseI);
        ListRecCluster:=[eCluster];
      else
        eCluster:=POLYCYCLE_ConvertToRecCluster(eCaseI);
        fCluster:=POLYCYCLE_ConvertToRecCluster(eCaseRev);
        ListRecCluster:=[eCluster, fCluster];
      fi;
      for PLori in LPLtot
      do
        RecTest:=TestAdmissibilityEmbeddingLego(ListDegree, ListRecCluster, PLori);
        if RecTest.feasible="maybe" then
          return true;
        fi;
      od;
      return false;
    end;
  fi;
  if IsExistingFile(TheFilePOLYCYCLE)=false then
    ListCases:=POLYCYCLE_Enumerate(kCodeg, ListDegree, FilteringFunction);
    SaveDataToFile(TheFilePOLYCYCLE, ListCases);
  else
    ListCases:=ReadAsFunction(TheFilePOLYCYCLE)();
  fi;
  Print("We have ListCases\n");
  nbCase:=Sum(List(ListCases, x->Length(x.ListCluster)));
  nbCaseRed:=Length(ListCases);
  Print("nbCase=", nbCase, "  nbCaseRed=", nbCaseRed, "\n");
  Print("Before computations of ListCases extended\n");
  ListCasesExtended:=[];
  for eCase in ListCases
  do
    ListClusterMap:=List(eCase.ListCluster, x->ConvertRecCluster(kCodeg, x));
    Add(ListCasesExtended, rec(planesym:=eCase.planesym, ListCluster:=ListClusterMap));
  od;
  Print("We have ListCasesExtended\n");
  #
  #
  #
  #
  eFileOut:=Concatenation(PrefixOut, "result");
  eFileOutRed:=Concatenation(PrefixOut, "resultred");
  RemoveFileIfExist(eFileOut);
  RemoveFileIfExist(eFileOutRed);
  output:=OutputTextFile(eFileOut, true);
  outputRed:=OutputTextFile(eFileOutRed, true);
  AppendTo(output, "nbCase=", nbCase, " nbCaseRed=", nbCaseRed, "\n");
  AppendTo(outputRed, "nbCase=", nbCase, " nbCaseRed=", nbCaseRed, "\n");
  #
  SumListCases:=ListWithIdenticalEntries(nbCase,0);
  NbAdmitOnlyIt:=ListWithIdenticalEntries(nbCase,0);
  NbAdmitUnique:=ListWithIdenticalEntries(nbCase,0);
  RED_SumListCases:=ListWithIdenticalEntries(nbCaseRed,0);
  RED_NbAdmitOnlyIt:=ListWithIdenticalEntries(nbCaseRed,0);
  RED_NbAdmitUnique:=ListWithIdenticalEntries(nbCase,0);
  NumberWithoutLego:=0;
  if IsBound(RecRequest.DoCasesPrint) then
    DoCasesPrint:=RecRequest.DoCasesPrint;
  else
    DoCasesPrint:=false;
  fi;
  if IsBound(RecRequest.PrintMostSymmetricCases) then
    PrintMostSymmetricCases:=RecRequest.PrintMostSymmetricCases;
  else
    PrintMostSymmetricCases:=true;
  fi;
  if IsBound(RecRequest.PrintLegoForEach) then
    PrintLegoForEach:=RecRequest.PrintLegoForEach;
  else
    PrintLegoForEach:=false;
  fi;
  if IsBound(RecRequest.PrintAllLego) then
    PrintAllLego:=RecRequest.PrintAllLego;
  else
    PrintAllLego:=false;
  fi;
  ListSymbInfo:=[];
  MaxNumberOrbitLego:=0;
  MinNumberOrbitLego:=-1;
  for iPL in [1..eIter.nbG]
  do
    Print("iPL=", iPL, "/", eIter.nbG, "\n");
    FileSaveLEGO:=Concatenation(PrefixOut, "PL_", String(iPL), ".lego");
    FileSaveLEGOred:=Concatenation(PrefixOut, "PL_", String(iPL), ".legored");
    FileSaveGRP:=Concatenation(PrefixOut, "PL_", String(iPL), ".grp");
    if IsExistingFile(FileSaveLEGO)=false or IsExistingFile(FileSaveLEGOred)=false or IsExistingFile(FileSaveGRP)=false then
      Print("iPL=", iPL, "/", eIter.nbG, "\n");
      PLori:=eIter.RetrievePlanGraphOriented(iPL);
      ListRecAnswer:=[];
      ListRecAnswerRed:=[];
      LegoInfo:=DoLegoPreparation(PLori);
      IsRotationGroup:=LegoInfo.GRPori.TotalGroup.IsRotationGroup;
      iCase:=0;
      for iCaseRed in [1..nbCaseRed]
      do
        Print("  iCaseRed=", iCaseRed, " / ", nbCaseRed, "\n");
        eCaseRed:=ListCasesExtended[iCaseRed];
        if eCaseRed.planesym=true then
          iCase:=iCase+1;
          RecAnswer:=DoLegoTilingEnumeration(LegoInfo, eCaseRed.ListCluster);
          Add(ListRecAnswer, RecAnswer);
          Add(ListRecAnswerRed, RecAnswer);
        else
          iCase:=iCase+1;
          RecAnswerBoth := DoLegoTilingEnumeration(LegoInfo, eCaseRed.ListCluster);
          Add(ListRecAnswer, RecAnswerBoth);
          #
          iCase:=iCase+1;
          if IsRotationGroup=true then
            RecAnswer1:=DoLegoTilingEnumeration(LegoInfo, [eCaseRed.ListCluster[1]]);
            RecAnswer2:=DoLegoTilingEnumeration(LegoInfo, [eCaseRed.ListCluster[2]]);
            RecAnswer:=rec(ListSolFinal:=Concatenation(RecAnswer1.ListSolFinal, RecAnswer2.ListSolFinal),
                           ListCases:=Concatenation(RecAnswer1.ListCases, RecAnswer2.ListCases));
          else
            RecAnswer:=DoLegoTilingEnumeration(LegoInfo, [eCaseRed.ListCluster[1]]);
          fi;
#          Print("  iCase=", iCase, "  |ListSolFinal|=", Length(RecAnswer.ListSolFinal), "  |ListCases|=", Length(RecAnswer.ListCases), "\n");
          Add(ListRecAnswer, RecAnswer);
          #
          RecAnswerTot:=rec(ListSolFinal:=Concatenation(RecAnswer.ListSolFinal, RecAnswerBoth.ListSolFinal), ListCases:=Concatenation(RecAnswer.ListCases, RecAnswerBoth.ListCases));
          Add(ListRecAnswerRed, RecAnswerTot);
        fi;
      od;
      RecGRPsave:=rec(GenSymbol:=LegoInfo.GRPori.GenSymbol);
      SaveDataToFile(FileSaveLEGO, ListRecAnswer);
      SaveDataToFile(FileSaveLEGOred, ListRecAnswerRed);
      SaveDataToFile(FileSaveGRP, RecGRPsave);
    else
      ListRecAnswer:=ReadAsFunction(FileSaveLEGO)();
      ListRecAnswerRed:=ReadAsFunction(FileSaveLEGOred)();
      RecGRPsave:=ReadAsFunction(FileSaveGRP)();
    fi;
    #
    # After data is read now we process it.
    #
    if IsBound(RecGRPsave.GenSymbol) then
      eGenSymb:=RecGRPsave.GenSymbol;
    else
      eGenSymb:=RecGRPsave.SchoenfliesSymbol;
    fi;
    ListSiz:=List(ListRecAnswer, x->Length(x.ListCases));
    ListSizRed:=List(ListRecAnswerRed, x->Length(x.ListCases));
    if DoCasesPrint then
      OrderGRP:=GetOrderGroupPlanSize(eGenSymb);
      eSymbInfo:=rec(eGenSymb:=eGenSymb, OrderGRP:=OrderGRP, ListSizRed:=ListSizRed);
      Add(ListSymbInfo, eSymbInfo);
    fi;
    eSum:=Sum(ListSiz);
    if iPL=1 then
      MaxNumberOrbitLego:=eSum;      
    else
      if eSum>MaxNumberOrbitLego then
        MaxNumberOrbitLego:=eSum;
      fi;
    fi;
    if eSum<>0 then
      if MinNumberOrbitLego=-1 then
        MinNumberOrbitLego:=eSum;
      fi;
      if eSum<MinNumberOrbitLego then
        MinNumberOrbitLego:=eSum;
      fi;
    fi;
    if DoCasesPrint and PrintLegoForEach and eSum>0 then
      PrefixOutPartial:=Concatenation(PrefixOut, "PLOT_SING_-_PL_", String(iPL));
      ExportMostSymmetricLego_SingleGraph(ListRecAnswer, PrefixOutPartial, RecRequest);
    fi;
    if DoCasesPrint and PrintAllLego and eSum>0 then
      PrefixOutPartial:=Concatenation(PrefixOut, "PLOT_ALL_-_PL_", String(iPL));
      ExportMostSymmetricLego_AllLegoGraph(ListRecAnswer, PrefixOutPartial, RecRequest);
    fi;
    eSumRed:=Sum(ListSizRed);
    if Sum(ListSiz)=0 then
      NumberWithoutLego:=NumberWithoutLego+1;
    fi;
    AppendTo(output, "iPL=", iPL, " G=", eGenSymb, " tot=", eSum, " ListSiz=", ListSiz, "\n");
    AppendTo(outputRed, "iPL=", iPL, " G=", eGenSymb, " tot=", eSumRed, " ListSizRed=", ListSizRed, "\n");
    SumListCases:=SumListCases + ListSiz;
    RED_SumListCases:=RED_SumListCases + ListSizRed;
    nbFound:=0;
    iPos:=-1;
    for iCase in [1..nbCase]
    do
      if ListSiz[iCase]>0 then
        iPos:=iCase;
        nbFound:=nbFound+1;
      fi;
    od;
    if nbFound=1 then
      NbAdmitOnlyIt[iPos]:=NbAdmitOnlyIt[iPos]+1;
      if ListSiz[iPos]=1 then
        NbAdmitUnique[iPos]:=NbAdmitUnique[iPos]+1;
      fi;
    fi;
    #
    nbFound:=0;
    iPos:=-1;
    for iCase in [1..nbCaseRed]
    do
      if ListSizRed[iCase]>0 then
        iPos:=iCase;
        nbFound:=nbFound+1;
      fi;
    od;
    if nbFound=1 then
      RED_NbAdmitOnlyIt[iPos]:=RED_NbAdmitOnlyIt[iPos]+1;
      if ListSizRed[iPos]=1 then
        RED_NbAdmitUnique[iPos]:=RED_NbAdmitUnique[iPos]+1;
      fi;
    fi;
  od;
  #
  # Now global results
  #
  AppendTo(output, "Total number of cases=", SumListCases, "\n");
  AppendTo(outputRed, "Total number of cases=", RED_SumListCases, "\n");
  eSumSum:=Sum(SumListCases);
  nbCaseReal:=Length(Filtered([1..nbCase], x->SumListCases[x]>0));
  nbCaseRedReal:=Length(Filtered([1..nbCaseRed], x->RED_SumListCases[x]>0));
  AppendTo(output, "eSumSum=", eSumSum, "\n");
  AppendTo(outputRed, "eSumSum=", eSumSum, "\n");
  CloseStream(output);
  CloseStream(outputRed);
  #
  eFileStat:=Concatenation(PrefixOut, "stat");
  RemoveFileIfExist(eFileStat);
  outputStat:=OutputTextFile(eFileStat, true);
  AppendTo(outputStat, "Statistics when distinguishing orientation of the legos:\n");
  AppendTo(outputStat, "Total number structure & Number attained only & Number attained uniquely\n");
  Print("nbCase=", nbCase, "\n");
  for iCase in [1..nbCase]
  do
    AppendTo(outputStat, SumListCases[iCase], " ", NbAdmitOnlyIt[iCase], " ", NbAdmitUnique[iCase], "\n");
  od;
  #
  AppendTo(outputStat, "\n\n");
  AppendTo(outputStat, "Statistics when NOT distinguishing orientation of the legos:\n");
  AppendTo(outputStat, "Total number structure & Number attained only & Number attained uniquely\n");
  for iCase in [1..nbCaseRed]
  do
    AppendTo(outputStat, RED_SumListCases[iCase], " ", RED_NbAdmitOnlyIt[iCase], " ", RED_NbAdmitUnique[iCase], "\n");
  od;
  AppendTo(outputStat, "Total number of orbits = ", eSumSum, "\n");
  AppendTo(outputStat, "\n\n");
  AppendTo(outputStat, "Number of graphs without any lego=", NumberWithoutLego, "\n");
  CloseStream(outputStat);
  Print("nbV=", nbV, "\n");
  #
  eRecStatistics:=rec(IsFull:=eIter.IsFull,
                      IsPolyFull:=FullPolycycleEnumeration,
                      nbG:=eIter.nbG,
                      nbV:=nbV,
                      ListNumberRed:=ListNumberRed, 
                      eSumSum:=eSumSum,
                      MaxNumberOrbitLego:=MaxNumberOrbitLego, 
                      MinNumberOrbitLego:=MinNumberOrbitLego, 
                      NumberWithoutLego:=NumberWithoutLego,
                      nbCase:=nbCase, nbCaseRed:=nbCaseRed,
                      nbCaseReal:=nbCaseReal, nbCaseRedReal:=nbCaseRedReal,
                      SumListCases:=SumListCases,
                      RED_SumListCases:=RED_SumListCases);
  eFileData:=Concatenation(PrefixOut, "data");
  SaveDataToFile(eFileData, eRecStatistics);
  #
  if DoCasesPrint and PrintMostSymmetricCases then
    idxP:=0;
    for iCaseRed in [1..nbCaseRed]
    do
      if RED_SumListCases[iCaseRed]>0 then
        idxP:=idxP+1;
        ListIdx:=Filtered([1..eIter.nbG], x->ListSymbInfo[x].ListSizRed[iCaseRed]>0);
        ListOrder:=List(ListIdx, x->ListSymbInfo[x].OrderGRP);
        eMaxOrder:=Maximum(ListOrder);
        ListMatch:=Filtered(ListIdx, x->ListSymbInfo[x].OrderGRP=eMaxOrder);
        pos:=ListMatch[1];
        eFileLEGOred:=Concatenation(PrefixOut, "PL_", String(pos), ".legored");
        ListRecAnswerRed:=ReadAsFunction(eFileLEGOred)();
        PrefixOutPartial:=Concatenation(PrefixOut, "PLOT_", String(idxP), "_PL_", String(pos));
#        ExportForGraph(ListRecAnswerRed, PrefixOutPartial, RecRequest);
        ExportMostSymmetricLegoGraph(ListRecAnswerRed, iCaseRed, PrefixOutPartial, RecRequest);
      fi;
    od;
  fi;
  if IsBound(RecRequest.ListQuery) then
    ListQuery:=RecRequest.ListQuery;
  else
    ListQuery:=[];
  fi;
  for eQuery in ListQuery
  do
    idx:=eQuery.idx;
    eNature:=eQuery.eNature;
    Print("idx=", idx, " eNature=", eNature, "\n");
    if eNature="red" then
      eFileLEGO:=Concatenation(PrefixOut, "PL_", String(idx), ".legored");
    else
      eFileLEGO:=Concatenation(PrefixOut, "PL_", String(idx), ".lego");
    fi;
    ListRecAnswer:=ReadAsFunction(eFileLEGO)();
    PrefixOutPartial:=Concatenation(PrefixOut, "PLOT_PL_", String(idx));
    ExportForGraph(ListRecAnswer, PrefixOutPartial, RecRequest);
  od;
  return eRecStatistics;
end;





IndividualSearchLego:=function(PL)
  local PLdual, kCodeg, ListDegTot, ListDegree, ListCases, nbCaseRed, PLori, LegoInfo, IsRotationGroup, iCaseRed, eCaseRed, RecAnswer, RecAnswerBoth, RecAnswer1, RecAnswer2, RecAnswerTot, ListTotal, ListTotalRed, ListRecAnswer, ListRecAnswerRed, ListMult, ListDegreeTot, ListDegreeRed, i, eNb, eGon;
  PLdual:=DualGraph(PL).PlanGraph;
  kCodeg:=Length(PL[1]);
  ListDegTot:=List(PLdual, Length);
  Print("ListDegTot=", ListDegTot, "\n");
  ListMult:=Collected(ListDegTot);
  Print("ListMult=", ListMult, "\n");
  ListDegreeTot:=List(ListMult, x->x[2]);
  Print("ListDegreeTot=", ListDegreeTot, "\n");
  ListDegreeRed:=RemoveFraction(ListDegreeTot);
  Print("ListDegreeRed=", ListDegreeRed, "\n");
  ListDegree:=[];
  for i in [1..Length(ListDegreeTot)]
  do
    eNb:=ListDegreeRed[i];
    eGon:=ListMult[i][1];
    Print("i=", i, " eNb=", eNb, " eGon=", eGon, "\n");
    Append(ListDegree, ListWithIdenticalEntries(eNb, eGon));
  od;
  Print("ListDegree=", ListDegree, "\n");
  ListCases:=POLYCYCLE_Enumerate(kCodeg, ListDegree);
  nbCaseRed:=Length(ListCases);
  PLori:=PlanGraphToPlanGraphOriented(PL);
  LegoInfo:=DoLegoPreparation(PLori);
  IsRotationGroup:=LegoInfo.GRPori.TotalGroup.IsRotationGroup;
  ListRecAnswer:=[];
  ListRecAnswerRed:=[];
  for iCaseRed in [1..nbCaseRed]
  do
    eCaseRed:=ListCases[iCaseRed];
    if eCaseRed.planesym=true then
      RecAnswer:=DoLegoTilingEnumeration(LegoInfo, eCaseRed.ListCluster);
      Add(ListRecAnswer, RecAnswer);
      Add(ListRecAnswerRed, RecAnswer);
    else
      RecAnswerBoth:=DoLegoTilingEnumeration(LegoInfo, eCaseRed.ListCluster);
      Add(ListRecAnswer, RecAnswerBoth);
      #
      if IsRotationGroup=true then
        RecAnswer1:=DoLegoTilingEnumeration(LegoInfo, [eCaseRed.ListCluster[1]]);
        RecAnswer2:=DoLegoTilingEnumeration(LegoInfo, [eCaseRed.ListCluster[2]]);
        RecAnswer:=rec(ListSolFinal:=Concatenation(RecAnswer1.ListSolFinal, RecAnswer2.ListSolFinal),
                       ListCases:=Concatenation(RecAnswer1.ListCases, RecAnswer2.ListCases));
      else
        RecAnswer:=DoLegoTilingEnumeration(LegoInfo, [eCaseRed.ListCluster[1]]);
      fi;
      Add(ListRecAnswer, RecAnswer);
      #
      RecAnswerTot:=rec(ListSolFinal:=Concatenation(RecAnswer.ListSolFinal, RecAnswerBoth.ListSolFinal), ListCases:=Concatenation(RecAnswer.ListCases, RecAnswerBoth.ListCases));
      Add(ListRecAnswerRed, RecAnswerTot);
    fi;
  od;
  ListTotal:=List(ListRecAnswer, x->Length(x.ListCases));
  ListTotalRed:=List(ListRecAnswerRed, x->Length(x.ListCases));
  Print("ListTotal = ", ListTotal, "\n");
  Print("ListTotalRed = ", ListTotalRed, "\n");
  Print("eSumSum = ", Sum(ListTotal), "\n");
end;




EnumeratePossibilitiesKvalent_sphere:=function(k, a, b)
  local pAmin, ePairMin, ListEqua, eSol, IsPairLego, ListInputLego, i, ePair, nbV, eRecInput, GetF, f;
  pAmin:=4*k/(2*k-(k-2)*a);
  ListEqua:=[[2*k-(k-2)*a, 2*k-(k-2)*b]];
  ePairMin:=[pAmin, 0];
  eSol:=NullspaceIntMat(TransposedMat(ListEqua))[1];
  IsPairLego:=function(ePair)
    if IsInt(ePair[1]/ePair[2])=true or IsInt(ePair[2]/ePair[1])=true then
      return true;
    fi;
    return false;
  end;
  GetF:=function(ePair)
    local f1, f2;
    f1:=ePair[1]/ePair[2];
    f2:=ePair[2]/ePair[1];
    if IsInt(f1)=true then
      return f1;
    fi;
    if IsInt(f2)=true then
      return f2;
    fi;
    Error("Should not reach that stage");
  end;
  ListInputLego:=[];
  for i in [1..100]
  do
    ePair:=ePairMin + i*eSol;
    if IsPairLego(ePair)=true then
      nbV:=(a*ePair[1] + b*ePair[2])/k;
      f:=GetF(ePair);
      eRecInput:=rec(kCodeg:=k, ListPair:=[[a, ePair[1]], [b, ePair[2]]], f:=f, g:=0, nbV:=nbV);
      Add(ListInputLego, eRecInput);
    fi;
  od;
  return ListInputLego;
end;


EnumeratePossibilitiesKvalent_torus:=function(k, a, b)
  local ListEqua, eSol, PreSol, ListInputLego, i, ePair, nbV, nbEdge, eRecInput, f, f_pre, MaxNbV;
  ListEqua:=[[2*k-(k-2)*a, 2*k-(k-2)*b]];
  PreSol:=RemoveFraction(NullspaceIntMat(TransposedMat(ListEqua))[1]);
  if Position(PreSol, 0)<>fail then
    Error("We have a zero in PreSol");
  fi;
  if PreSol[1]<0 then
    eSol:=-PreSol;
  else
    eSol:=PreSol;
  fi;
  if Minimum(eSol)<0 then
    Error("Inconsistent eSol");
  fi;
  if IsInt(eSol[1]/eSol[2])=false and IsInt(eSol[2]/eSol[1])=false then
    Print("No lego is possible\n");
    return [];
  fi;
  f_pre:=eSol[1]/eSol[2];
  if IsInt(f_pre)=true then
    f:=f_pre;
  else
    f:=1/f_pre;
  fi;
  ListInputLego:=[];
  MaxNbV:=70;
  for i in [1..1000]
  do
    ePair:=i*eSol;
    nbEdge:=(a*ePair[1] + b*ePair[2])/2;
    nbV:=(a*ePair[1] + b*ePair[2])/k;
    if IsInt(nbEdge) and IsInt(nbV) and nbV <= MaxNbV then
      eRecInput:=rec(kCodeg:=k, ListPair:=[[a, ePair[1]], [b, ePair[2]]], f:=f, g:=1, nbV:=nbV);
      Add(ListInputLego, eRecInput);
    fi;
  od;
  return ListInputLego;
end;






DoTableListCases:=function(ListCases, eFileTex, RecRequest)
  local output, a, b, Pa, Pb, nbListPair, iPair, nbCaseReal, nbCaseRedReal, eCase, ListPair, kCodeg, eRecStatistics, ListNumberRed, strLego, nbV, nbG, strVect, i, eVectRed, eSumSum, strP, strWrite, NumberWithout, nbCase, nbCaseRed, strSign, strN, strCase, strCaseRed, strMaxMin, MaxNumberOrbitLego, MinNumberOrbitLego, g, strCase1, strCase2, strCaseRed1, strCaseRed2, strSumSum, strMax, strMin, iCaseWork, nbCaseWork, CaseSignature, PreCaseSignature, GlobalComputation;
  RemoveFileIfExist(eFileTex);
  output:=OutputTextFile(eFileTex, true);
  AppendTo(output, "\\begin{center}\n");
  AppendTo(output, "\\begin{tabular}{|c|c|c|c|c|c|c|c|c|}\n");
  AppendTo(output, "\\hline\n");
  AppendTo(output, "k & lego & \$(p_a, p_b)\$ & v & nbG/real. & nbCases/real. & nbCasesRed/real. & Max./Min. & total\\\\\n");
#  AppendTo(output, "\\hline\n");
  nbListPair:=Length(ListCases);
  PreCaseSignature:=[-1,-1];
  nbCaseWork:=Length(ListCases);
  if IsBound(RecRequest.GlobalComputation) then
    GlobalComputation:=RecRequest.GlobalComputation;
  else
    GlobalComputation:=true;
  fi;
  for iCaseWork in [1..nbCaseWork]
  do
    eCase:=ListCases[iCaseWork];
    eRecStatistics:=LegoFunctionEnumeration(eCase, RecRequest);
    if GlobalComputation then
      ListNumberRed:=eRecStatistics.ListNumberRed;
      a:=eCase.ListPair[1][1];
      b:=eCase.ListPair[2][1];
      CaseSignature:=[eCase.kCodeg, a];
      Pa:=eCase.ListPair[1][2];
      Pb:=eCase.ListPair[2][2];
      if ListNumberRed=[1,1] then
        strLego:=Concatenation(String(a), String(b));
      else
        if ListNumberRed[1]>1 then
          strLego:=Concatenation(String(a), "^{", String(ListNumberRed[1]), "}", String(b));
        else
          strLego:=Concatenation(String(a), String(b), "^{", String(ListNumberRed[2]), "}");
        fi;
      fi;
      strLego:=Concatenation("\$", strLego, "\$");
      nbV:=eRecStatistics.nbV;
      nbG:=eRecStatistics.nbG;
      nbCase:=eRecStatistics.nbCase;
      nbCaseRed:=eRecStatistics.nbCaseRed;
      nbCaseReal:=eRecStatistics.nbCaseReal;
      nbCaseRedReal:=eRecStatistics.nbCaseRedReal;
      eVectRed:=Filtered(eRecStatistics.RED_SumListCases, x->x>0);
      eSumSum:=eRecStatistics.eSumSum;
      NumberWithout:=eRecStatistics.NumberWithoutLego;
      strVect:="\$(";
      for i in [1..nbCaseRedReal]
      do
        if i>1 then
          strVect:=Concatenation(strVect, ",");
        fi;
        strVect:=Concatenation(strVect, String(eVectRed[i]));
      od;
      strVect:=Concatenation(strVect, ")\$");
      strP:=Concatenation("(", String(Pa), ",", String(Pb), ")");
      strSign:=Concatenation(String(eCase.kCodeg), " & ", strLego, " & ", strP, " & ", String(nbV));
      if eRecStatistics.IsFull=true then
        strN:=Concatenation(String(nbG), "/", String(nbG - NumberWithout));
      else
        strN:=Concatenation("\\geq ", String(nbG), "/", "\\geq ", String(nbG - NumberWithout));
      fi;
      strN:=Concatenation("\$", strN, "\$");
      #
      if eRecStatistics.IsPolyFull=true then
        strCase1:=String(nbCase);
        strCaseRed1:=String(nbCaseRed);
      else
        strCase1:=Concatenation("\\geq ", String(nbCase));
        strCaseRed1:=Concatenation("\\geq ", String(nbCaseRed));
      fi;
      if eRecStatistics.IsPolyFull=true or eRecStatistics.IsFull then
        strCase2:=String(nbCaseReal);
        strCaseRed2:=String(nbCaseRedReal);
      else
        strCase2:=Concatenation("\\geq ", String(nbCaseReal));
        strCaseRed2:=Concatenation("\\geq ", String(nbCaseRedReal));
      fi;
      strCase:=Concatenation("\$", strCase1, "/", strCase2, "\$");
      strCaseRed:=Concatenation("\$", strCaseRed1, "/", strCaseRed2, "\$");
      #
      MaxNumberOrbitLego:=eRecStatistics.MaxNumberOrbitLego;
      MinNumberOrbitLego:=eRecStatistics.MinNumberOrbitLego;
      if MinNumberOrbitLego=-1 then
        strMaxMin:="N/A";
      else
        if eRecStatistics.IsFull=true then
          strMax:=String(MaxNumberOrbitLego);
        else
          strMax:=Concatenation("\\geq ", String(MaxNumberOrbitLego));
        fi;
        if eRecStatistics.IsFull=true then
          strMin:=String(MinNumberOrbitLego);
        else
          if MinNumberOrbitLego=1 then
            strMin:=String(MinNumberOrbitLego);
          else
            strMin:=Concatenation("\\leq ", String(MinNumberOrbitLego));
          fi;
        fi;
        strMaxMin:=Concatenation("\$", strMax, "/", strMin, "\$");
      fi;
      #
      if eRecStatistics.IsFull=true then
        strSumSum:=String(eSumSum);
      else
        strSumSum:=Concatenation("\$\\geq ", String(eSumSum), "\$");
      fi;
      if PreCaseSignature<>CaseSignature then
        AppendTo(output, "\\hline\n");
      fi;
      strWrite:=Concatenation(strSign, " & ", strN, " & ", strCase, " & ", strCaseRed, " & ", strMaxMin, " & ", strSumSum, "\\\\\n");
      WriteAll(output, strWrite);
      #
      PreCaseSignature:=CaseSignature;
    fi;
  od;
  AppendTo(output, "\\hline\n");
  AppendTo(output, "\\end{tabular}\n");
  AppendTo(output, "\\end{center}\n");
  CloseStream(output);
  LATEX_Compilation(eFileTex);
end;



MakeFileStatisticsExport:=function(ListCases)
  local TreatEntry, eCase, PrefixOut;
  TreatEntry:=function(eStr)
    local eFile1, eFile2, eComm;
    eFile1:=Concatenation("DATAcase/", PrefixOut, "/", eStr);
    eFile2:=Concatenation("RawStats/", PrefixOut, "_", eStr);
    eComm:=Concatenation("cp ", eFile1, " ", eFile2);
    Exec(eComm);
  end;
  for eCase in ListCases
  do
    PrefixOut:=GetPrefixOut(eCase);
    TreatEntry("stat");
    TreatEntry("result");
    TreatEntry("resultred");
  od;
end;











GetListCases_Theorem1:=function()
  return [rec(k:=3, ListP:=[ [[4,7],[12,12]], [[3,8],[12,12]], [[3,7], [6,6]], [[3,7],[12,24]], 
[[2,9], [12,12]], 
[[2,8], [6,6]], [[2,7],[4,4]], [[2,7],[6,12]], [[2,7],[12,36]],
[[1,10], [12,12]],
[[1,9],[6,6]],
[[1,8],[4,4]],
[[1,8],[12,24]],
[[1,7],[3,3]], 
[[1,7],[4,8]],
[[1,7],[6,18]],
[[1,7],[12,48]] ]),

rec(k:=4, ListP:=[
[[2,5],[8,8]], 
[[1,6],[8,8]],
[[1,5],[4,4]],
[[1,5],[8,16]] ]),

rec(k:=5, ListP:=[
[[2,4],[10,10]],
[[1,5],[10,10]],
[[1,4],[4,4]],
[[1,4],[20,60]] ]),

rec(k:=6, ListP:=[
[[1,4],[6,6]] ]),

rec(k:=7, ListP:=[
[[2,3],[14,28]],
[[2,3],[28,84]],
[[1,3],[4,8]],
[[1,3],[7,35]],
[[1,3],[14,98]],
[[1,3],[28,224]] ]),

rec(k:=8, ListP:=[
[[2,3],[16,16]],
[[1,4],[16,16]],
[[1,3],[8,24]],
[[1,3],[16,64]] ]),

rec(k:=9, ListP:=[
[[2,3],[36,36]],
[[1,4],[36,36]],
[[1,3],[18,54]] ]),


rec(k:=10, ListP:=[
[[1,3],[10,20]] ]),

rec(k:=12, ListP:=[
[[1,3],[24,48]] ]),

rec(k:=13, ListP:=[
[[1,3],[52,104]] ])];
end;


PrintTable_Cases1:=function(eFileTex, nbCol)
  local ListEntries, ListStr, eEnt, k, eP, a, b, Pa, Pb, ListVal, strLego, strPvect, strDesc, nbV, output;
  ListEntries:=GetListCases_Theorem1();
  ListStr:=[];
  for eEnt in ListEntries
  do
    k:=eEnt.k;
    for eP in eEnt.ListP
    do
      a:=eP[1][1];
      b:=eP[1][2];
      Pa:=eP[2][1];
      Pb:=eP[2][2];
      nbV:=(a * Pa + b * Pb)/k;
      ListVal:=RemoveFraction(eP[2]);
      if ListVal=[1,1] then
        strLego:=Concatenation(String(a), String(b));
      else
        if ListVal[1] > 1 then
	  strLego:=Concatenation(String(a), "^{", String(ListVal[1]), "}", String(b));
	else
	  strLego:=Concatenation(String(a), String(b), "^{", String(ListVal[2]), "}");
	fi;
      fi;
      strPvect:=Concatenation("\$(p_{", String(a), "}, p_{", String(b), "}) = (", String(Pa), ",", String(Pb));
      strDesc:=Concatenation(String(k), " & ", strLego, " & ", strPvect, " & ", String(nbV));
      Add(ListStr, strDesc);
    od;
  od;
  #
  RemoveFileIfExist(eFileTex);
  output:=OutputTextFile(eFileTex, true);
  CloseStream(output);
  LATEX_Compilation(eFileTex);
end;



EnumeratePairing:=function(PLori)
  local GRPori, CCori, VEFori, nbP, ListDE, nbVert, iDE, iVert, iEdge, ListPermGenDE, eGen, eList, eRecDE, iVertImg, iEdgeImg, eRecDEimg, pos, GRPde, FaceSet, nbFace, ListSol, GetPossibleCandidatesAFace, IsComplete, ListFinal, FuncInsert, eSol, recCand, ePos, NewSol, ListOption, NewListSol, RecCand, eGRP;
  GRPori:=GroupPlanOriented(PLori);
  CCori:=GRPori.CC;
  VEFori:=CCori.VEF;
  nbP:=PLori.nbP;
  ListDE:=[];
  nbVert:=Length(VEFori.VertSet);
  for iDE in [1..nbP]
  do
    iVert:=VEFori.ListOriginVert[iDE];
    iEdge:=VEFori.ListOriginEdge[iDE];
    Add(ListDE, rec(iVert:=iVert, iEdge:=iEdge));
  od;
  ListPermGenDE:=[];
  eGRP:=GRPori.TotalGroup.RotationSubgroup;
  for eGen in GeneratorsOfGroup(eGRP)
  do
    eList:=[];
    for iDE in [1..nbP]
    do
      eRecDE:=ListDE[iDE];
      iVert:=eRecDE.iVert;
      iEdge:=eRecDE.iEdge;
      iVertImg:=OnPoints(iVert, eGen);
      iEdgeImg:=OnPoints(iEdge + nbVert, eGen) - nbVert;
      eRecDEimg:=rec(iVert:=iVertImg, iEdge:=iEdgeImg);
      pos:=Position(ListDE, eRecDEimg);
      if pos=fail then
        Error("Please correct from that point");
      fi;
      Add(eList, pos);
    od;
    Add(ListPermGenDE, PermList(eList));
  od;
  GRPde:=Group(ListPermGenDE);
  FaceSet:=VEFori.FaceSet;
  nbFace:=Length(FaceSet);
  ListSol:=[ [] ];
  GetPossibleCandidatesAFace:=function(eSol)
    local ListStatusA, ListStatusB, eDE, iFaceA, rDE, iFaceB, IsFirst, MinListOption;
    ListStatusA:=ListWithIdenticalEntries(nbFace,0);
    ListStatusB:=ListWithIdenticalEntries(nbFace,0);
    for eDE in eSol
    do
      iFaceA:=VEFori.ListOriginFace[eDE];
      ListStatusA[iFaceA]:=1;
      #
      rDE:=OnPoints(eDE, PLori.invers);
      iFaceB:=VEFori.ListOriginFace[rDE];
      ListStatusB[iFaceB]:=1;
    od;
    IsFirst:=true;
    for iFaceA in [1..nbFace]
    do
      if ListStatusA[iFaceA]=0 then
        ListOption:=[];
        for eDE in FaceSet[iFaceA]
        do
          rDE:=OnPoints(eDE, PLori.invers);
          iFaceB:=VEFori.ListOriginFace[rDE];
          if ListStatusB[iFaceB]=0 then
            Add(ListOption, eDE);
          fi;
        od;
        if Length(ListOption) > 0 then
          if IsFirst=true then
            IsFirst:=false;
            MinListOption:=List(ListOption, x->x);
          else
            if Length(ListOption) < Length(MinListOption) then
              MinListOption:=List(ListOption, x->x);
            fi;
          fi;
        fi;
      fi;
    od;
    if IsFirst=true then
      return rec(wefind:=false);
    else
      return rec(wefind:=true, ListOption:=MinListOption);
    fi;
  end;
  IsComplete:=function(eSol)
    local ListStatusA, ListStatusB, eDE, iFaceA, rDE, iFaceB;
    ListStatusA:=ListWithIdenticalEntries(nbFace,0);
    ListStatusB:=ListWithIdenticalEntries(nbFace,0);
    for eDE in eSol
    do
      iFaceA:=VEFori.ListOriginFace[eDE];
      ListStatusA[iFaceA]:=1;
      #
      rDE:=OnPoints(eDE, PLori.invers);
      iFaceB:=VEFori.ListOriginFace[rDE];
      ListStatusB[iFaceB]:=1;
    od;
    if Position(ListStatusA, 0)<>fail then
      return false;
    fi;
    if Position(ListStatusB, 0)<>fail then
      return false;
    fi;
    return true;
  end;
  ListFinal:=[];
  while(true)
  do
    NewListSol:=[];
    FuncInsert:=function(NewSol)
      local rSol, test;
      for rSol in NewListSol
      do
        test:=RepresentativeAction(GRPde, rSol, NewSol, OnSets);
        if test<>fail then
	  return;
        fi;
      od;
      Add(NewListSol, NewSol);
    end;
    for eSol in ListSol
    do
      RecCand:=GetPossibleCandidatesAFace(eSol);
      if RecCand.wefind=true then
        for ePos in RecCand.ListOption
        do
          NewSol:=Set(Concatenation(eSol, [ePos]));
          if IsComplete(NewSol)=true then
            Add(ListFinal, NewSol);
          else
            FuncInsert(NewSol);
          fi;
        od;
      fi;
    od;
    if Length(NewListSol)=0 then
      break;
    fi;
    Print("|NewListSol|=", Length(NewListSol), "  |ListFinal|=", Length(ListFinal), "\n");
    ListSol:=Set(NewListSol);
  od;
  return ListFinal;
end;



#
# The splitting of some edges into a pair of a 3-gon and a 1-gon.
SplitEdges13gonOfPlanGraphOriented:=function(PLori, DEstatus)
  local nbP, ListDirectedEdgeStatus, iDE, rDE, NewListDE, eStat, i, eDE, eVal, kDE, posNext, posInv, eDEnext, eDEinv, eListNext, eListInv, GetDEnext, eNext, eInv, ListImgNext, ListImgInv;
  nbP:=PLori.nbP;
  ListDirectedEdgeStatus:=ListWithIdenticalEntries(nbP, 0);
  for iDE in [1..nbP]
  do
    if DEstatus[iDE]=1 then
      rDE:=OnPoints(iDE, PLori.invers);
      if ListDirectedEdgeStatus[iDE]<>0 then
        Error("Problem 1");
      fi;
      if ListDirectedEdgeStatus[rDE]<>0 then
        Error("Problem 2");
      fi;
      ListDirectedEdgeStatus[iDE]:=1;
      ListDirectedEdgeStatus[rDE]:=2;
    fi;
  od;
  #
  NewListDE:=[];
  for iDE in [1..nbP]
  do
    eStat:=ListDirectedEdgeStatus[iDE];
    if eStat=0 then
      Add(NewListDE, [iDE, 0, 0]);
    fi;
    if eStat=1 then
      for i in [1..4]
      do
        Add(NewListDE, [iDE, 1, i]);
      od;
    fi;
    if eStat=2 then
      for i in [1..2]
      do
        Add(NewListDE, [iDE, 2, i]);
      od;
    fi;
  od;
  eListNext:=[];
  eListInv:=[];
  GetDEnext:=function(iDE)
    local jDE, eStat;
    jDE:=OnPoints(iDE, PLori.next);
    eStat:=ListDirectedEdgeStatus[jDE];
    if eStat=0 then
      return [jDE, 0, 0];
    fi;
    if eStat=1 then
      return [jDE, 1, 1];
    fi;
    if eStat=2 then
      return [jDE, 2, 1];
    fi;
    Error("clear problem");
  end;
#  Print("NewListDE=", NewListDE, "\n");
  ListImgNext:=[];
  ListImgInv:=[];
  for eDE in NewListDE
  do
    iDE:=eDE[1];
    eVal:=eDE[3];
    kDE:=OnPoints(iDE, PLori.invers);
    if eDE[2]=0 then
      eDEnext:=GetDEnext(iDE);
      eDEinv:=[kDE, 0,0];
    fi;
    if eDE[2]=1 then
      if eVal<4 then
        eDEnext:=[iDE, 1, eVal+1];
      else
        eDEnext:=GetDEnext(iDE);
      fi;
      if eVal=1 then
        eDEinv:=[kDE,2,2];
      fi;
      if eVal=2 then
        eDEinv:=[iDE,1,3];
      fi;
      if eVal=3 then
        eDEinv:=[iDE,1,2];
      fi;
      if eVal=4 then
        eDEinv:=[kDE,2,1];
      fi;
    fi;
    if eDE[2]=2 then
      if eVal<2 then
        eDEnext:=[iDE, 2, eVal+1];
      else
        eDEnext:=GetDEnext(iDE);
      fi;
      if eVal=1 then
        eDEinv:=[kDE,1,4];
      fi;
      if eVal=2 then
        eDEinv:=[kDE,1,1];
      fi;
    fi;
    posNext:=Position(NewListDE, eDEnext);
    posInv:=Position(NewListDE, eDEinv);
    Add(ListImgNext, eDEnext);
    Add(ListImgInv, eDEinv);
    Add(eListNext, posNext);
    Add(eListInv, posInv);
  od;
  eNext:=PermList(eListNext);
  eInv:=PermList(eListInv);
  if eNext=fail or eInv=fail then
    Error("Inconsistency in the next and inv operator");
  fi;
  return rec(nbP:=Length(NewListDE), next:=eNext, invers:=eInv);
end;




SecondLevelDirectedEdgeSplit:=function(PLori, VEFori, ListIDE)
  local nbP, ListDEstatus, nbVert, eNext, ePrev, eInv, MappingVertDE, GRPvert, iDE, iDEnext, iDEprev, eDEnext, eDEinv, eO, jDE, NewListDE, i, GetNewDirectedEdge, eDE, GetDEnext, eVert, GetPositioningDEstat1, eListInv, eListNext, posNext, posInv, eNewNext, eNewInv, eStat, kDE, eRecPos, eValNext, eVal, kStat, iDEsearch, kDEsearch, eVertNext, eVertPrev;
  nbP:=PLori.nbP;
  nbVert:=Length(VEFori.VertSet);
  eNext:=PLori.next;
  ePrev:=Inverse(eNext);
  eInv:=PLori.invers;
  ListDEstatus:=ListWithIdenticalEntries(nbP, 0);
  MappingVertDE:=ListWithIdenticalEntries(nbVert, 0);
  GRPvert:=Group([eNext]);
  for iDE in ListIDE
  do
    eVert:=VEFori.ListOriginVert[iDE];
    MappingVertDE[eVert]:=iDE;
    iDEnext:=OnPoints(iDE, eNext*eInv);
    iDEprev:=OnPoints(iDE, ePrev*eInv);
    eVertNext:=VEFori.ListOriginVert[iDEnext];
    eVertPrev:=VEFori.ListOriginVert[iDEprev];
#    Print("Assigning eVert(N/P)=", eVert, ",", eVertNext, ",", eVertPrev, "\n");
    if ListDEstatus[iDE]<>0 or ListDEstatus[iDEnext]<>0 or ListDEstatus[iDEprev]<>0 then
      Error("Assignment problem in the directed edges");
    fi;
    ListDEstatus[iDE]:=1;
    ListDEstatus[iDEnext]:=3;
    ListDEstatus[iDEprev]:=4;
    eO:=Orbit(GRPvert, iDE, OnPoints);
    for jDE in eO
    do
      if jDE<>iDE then
        if ListDEstatus[jDE]<>0 then
	  Error("We have a problem");
	fi;
        ListDEstatus[jDE]:=-1;
      fi;
    od;
  od;
  NewListDE:=[];
  for iDE in [1..nbP]
  do
    eStat:=ListDEstatus[iDE];
    if eStat=0 then
      Add(NewListDE, [iDE, 0, 0]);
    fi;
    if eStat=1 then
      for i in [1..7]
      do
        Add(NewListDE, [iDE, 1, i]);
        Add(NewListDE, [iDE, 2, i]);
      od;
    fi;
    if eStat=3 then
      for i in [1..2]
      do
        Add(NewListDE, [iDE, 3, i]);
      od;
    fi;
    if eStat=4 then
      for i in [1..2]
      do
        Add(NewListDE, [iDE, 4, i]);
      od;
    fi;
  od;
  #
  GetDEnext:=function(iDE)
    local jDE, fStat;
    jDE:=OnPoints(iDE, eNext);
    fStat:=ListDEstatus[jDE];
    if fStat=0 then
      return [jDE, 0, 0];
    fi;
    if fStat=1 or fStat=-1 then
      Error("Should not work here");
    fi;
    if fStat=3 then
      return [jDE, 3, 1];
    fi;
    if fStat=4 then
      return [jDE, 4, 1];
    fi;
    Error("Should not reach that stage");
  end;
  GetPositioningDEstat1:=function(iDE)
    local eVert, iDEcan, iDEwork, i;
    eVert:=VEFori.ListOriginVert[iDE];
    iDEcan:=MappingVertDE[eVert];
    iDEwork:=iDEcan;
    for i in [1..6]
    do
      if iDEwork=iDE then
        return rec(iDEcan:=iDEcan, pos:=i);
      fi;
      iDEwork:=OnPoints(iDEwork, eNext);
    od;
    Error("We should not reached that stage");
  end;
  GetNewDirectedEdge:=function(iDE)
    local uStat, eRecPos;
    uStat:=ListDEstatus[iDE];
    if uStat=0 then
      return [iDE, 0,0];
    fi;
    if uStat=3 or uStat=4 then
      Error("We cannot do the deduction here");
    fi;
    if uStat=1 or uStat=-1 then
      eRecPos:=GetPositioningDEstat1(iDE);
      if eRecPos.pos=2 or eRecPos.pos=6 then
        Error("It is imposible to conclude here");
      fi;
      if eRecPos.pos=1 then
        return [eRecPos.iDEcan, 1, 1];
      fi;
      if eRecPos.pos=3 then
        return [eRecPos.iDEcan, 2, 7];
      fi;
      if eRecPos.pos=4 then
        return [eRecPos.iDEcan, 2, 1];
      fi;
      if eRecPos.pos=5 then
        return [eRecPos.iDEcan, 2, 2];
      fi;
    fi;
    Error("Should not reach that stage");
  end;
  eListNext:=[];
  eListInv:=[];
  for eDE in NewListDE
  do
    iDE:=eDE[1];
    eStat:=eDE[2];
    eVal:=eDE[3];
    jDE:=OnPoints(iDE, eNext);
    kDE:=OnPoints(iDE, eInv);
    eDEnext:="unset";
    eDEinv:="unset";
    if eStat=0 then
      eDEnext:=GetDEnext(iDE);
      kStat:=ListDEstatus[kDE];
      if kStat=3 or kStat=4 then
        Error("This case should not happen 1");
      fi;
      if kStat=0 then
        eDEinv:=[kDE, 0, 0];
      fi;
      if kStat=1 then
        eDEinv:=[kDE, 1,1];
      fi;
      if kStat=-1 then
        eRecPos:=GetPositioningDEstat1(kDE);
        if Position([2,1,6], eRecPos.pos)<>fail then
          Error("This case should not happen 2");
        fi;
        if eRecPos.pos=3 then
          eDEinv:=[eRecPos.iDEcan, 2, 7];
        fi;
        if eRecPos.pos=4 then
          eDEinv:=[eRecPos.iDEcan, 2, 1];
        fi;
        if eRecPos.pos=5 then
          eDEinv:=[eRecPos.iDEcan, 2, 2];
        fi;
      fi;
    fi;
    if eStat=1 then
      eValNext:=NextIdx(7,eVal);
      eDEnext:=[iDE, 1, eValNext];
      #
      if eVal=1 then
	eDEinv:=GetNewDirectedEdge(kDE);
      fi;
      if eVal=2 then
        iDEnext:=OnPoints(iDE, eNext*eInv);
	eDEinv:=[iDEnext, 3, 2];
      fi;
      if eVal=3 then
        eDEinv:=[iDE, 2, 5];
      fi;
      if eVal=4 then
        eDEinv:=[iDE, 1, 5];
      fi;
      if eVal=5 then
        eDEinv:=[iDE, 1, 4];
      fi;
      if eVal=6 then
        eDEinv:=[iDE, 2, 4];
      fi;
      if eVal=7 then
        iDEprev:=OnPoints(iDE, ePrev*eInv);
	eDEinv:=[iDEprev, 4, 1];
      fi;
    fi;
    if eStat=2 then
      eValNext:=NextIdx(7,eVal);
      eDEnext:=[iDE, 2, eValNext];
      #
      if eVal=1 then
        iDEsearch:=OnPoints(iDE, eNext*eNext*eNext);
	kDEsearch:=OnPoints(iDEsearch, eInv);
	eDEinv:=GetNewDirectedEdge(kDEsearch);
      fi;
      if eVal=2 then
        iDEsearch:=OnPoints(iDE, ePrev*ePrev);
	kDEsearch:=OnPoints(iDEsearch, eInv);
	eDEinv:=GetNewDirectedEdge(kDEsearch);
      fi;
      if eVal=3 then
        iDEprev:=OnPoints(iDE, ePrev*eInv);
	eDEinv:=[iDEprev, 4, 2];
      fi;
      if eVal=4 then
        eDEinv:=[iDE, 1, 6];
      fi;
      if eVal=5 then
        eDEinv:=[iDE, 1, 3];
      fi;
      if eVal=6 then
        iDEnext:=OnPoints(iDE, eNext*eInv);
        eDEinv:=[iDEnext, 3, 1];
      fi;
      if eVal=7 then
        iDEsearch:=OnPoints(iDE, eNext*eNext);
	kDEsearch:=OnPoints(iDEsearch, eInv);
	eDEinv:=GetNewDirectedEdge(kDEsearch);
      fi;
    fi;
    if eStat=3 then
      if eVal=1 then
        eDEnext:=[iDE, 3, 2];
      else
        eDEnext:=GetDEnext(iDE);
      fi;
      eRecPos:=GetPositioningDEstat1(kDE);
      if eVal=1 then
        eDEinv:=[eRecPos.iDEcan, 2, 6];
      fi;
      if eVal=2 then
        eDEinv:=[eRecPos.iDEcan, 1, 2];
      fi;
    fi;
    if eStat=4 then
      if eVal=1 then
        eDEnext:=[iDE, 4, 2];
      else
        eDEnext:=GetDEnext(iDE);
      fi;
      eRecPos:=GetPositioningDEstat1(kDE);
      if eVal=1 then
        eDEinv:=[eRecPos.iDEcan, 1, 7];
      fi;
      if eVal=2 then
        eDEinv:=[eRecPos.iDEcan, 2, 3];
      fi;
    fi;
    posNext:=Position(NewListDE, eDEnext);
    posInv:=Position(NewListDE, eDEinv);
    if posNext=fail or posInv=fail then
      Error("Not found in NewListDE");
    fi;
    Add(eListNext, posNext);
    Add(eListInv, posInv);
  od;
  eNewNext:=PermList(eListNext);
  eNewInv:=PermList(eListInv);
  if eNewNext=fail or eNewInv=fail then
    Error("Wrong construction of eNewNext or eNewInv");
  fi;
  if eNewInv*eNewInv<>() then
    Error("Problem in eNewInv");
  fi;
  return rec(nbP:=Length(NewListDE), next:=eNewNext, invers:=eNewInv);
end;


InsertStructureOnDirectedEdge:=function(PLori, ListPLori, ListInsert)
  local ListDE, nbP, i, nbInsert, iInsert, ListPairInv, iIns, eInsert, eEdge, iDE, rDE, nbBlock, eSymbEdge, ListSymbEdge, iBlock, iPLori, eEdgeIns, nbPins, SymbEdge, eDE1, eDE2, eListNext, eListInv, eDE, eVal, iNext, iInv, NextDE, InvDE, posNext, posInv, ePermNext, ePermInv, nbIns, NewNbP, ePair;
  ListDE:=[];
  nbP:=PLori.nbP;
  for i in [1..nbP]
  do
    Add(ListDE, [0, i]);
  od;
  nbIns:=Length(ListInsert);
  iInsert:=0;
  ListPairInv:=[];
  for iIns in [1..nbIns]
  do
    eInsert:=ListInsert[iIns];
    eEdge:=eInsert.eEdge;
    iDE:=eEdge[1];
    rDE:=eEdge[2];
    nbBlock:=Length(eInsert.ListBlock);
    eSymbEdge:=rec(eDE1:=[0,iDE], eDE2:=[0,rDE]);
    ListSymbEdge:=[];
    for iBlock in [1..nbBlock]
    do
      iInsert:=iInsert+1;
      iPLori:=eInsert.ListBlock[iBlock].iPLori;
      eEdgeIns:=eInsert.ListBlock[iBlock].eEdge;
      nbPins:=ListPLori[iPLori].nbP;
      for i in [1..nbPins]
      do
        Add(ListDE, [1, iPLori, i, iInsert]);
      od;
      SymbEdge:=rec(eDE1:=[1,iPLori,eEdgeIns[1],iInsert], eDE2:=[1,iPLori,eEdgeIns[2],iInsert]);
      Add(ListSymbEdge, SymbEdge);
    od;
    for iBlock in [0..nbBlock]
    do
      if iBlock=0 then
        eDE1:=eSymbEdge.eDE1;
      else
        eDE1:=ListSymbEdge[iBlock].eDE1;
      fi;
      if iBlock<nbBlock then
        eDE2:=ListSymbEdge[iBlock+1].eDE2;
      else
        eDE2:=eSymbEdge.eDE2;
      fi;
      Add(ListPairInv, rec(eDE1:=eDE1, eDE2:=eDE2));
    od;
  od;
  NewNbP:=Length(ListDE);
  eListNext:=[];
  eListInv:=[];
  for eDE in ListDE
  do
    eVal:=eDE[1];
    if eVal=0 then
      i:=eDE[2];
      iNext:=OnPoints(i, PLori.next);
      NextDE:=[0,iNext];
    else
      iPLori:=eDE[2];
      i:=eDE[3];
      iInsert:=eDE[4];
      iNext:=OnPoints(i, ListPLori[iPLori].next);
      NextDE:=[1,iPLori,iNext,iInsert];
    fi;
    InvDE:="unset";
    for ePair in ListPairInv
    do
      if ePair.eDE1=eDE then
        InvDE:=ePair.eDE2;
      fi;
      if ePair.eDE2=eDE then
        InvDE:=ePair.eDE1;
      fi;
    od;
    if InvDE="unset" then
      if eVal=0 then
        iInv:=OnPoints(i, PLori.invers);
        InvDE:=[0,iInv];
      else
        iPLori:=eDE[2];
        i:=eDE[3];
        iInsert:=eDE[4];
        iInv:=OnPoints(i, ListPLori[iPLori].invers);
        InvDE:=[1,iPLori,iInv,iInsert];
      fi;
    fi;
    posNext:=Position(ListDE, NextDE);
    posInv :=Position(ListDE, InvDE);
    if posNext=fail or posInv=fail then
      Error("Need to correct that problem");
    fi;
    Add(eListNext, posNext);
    Add(eListInv, posInv);
  od;
  ePermNext:=PermList(eListNext);
  ePermInv:=PermList(eListInv);
  if ePermNext=fail or ePermInv=fail then
    Error("Please correct");
  fi;
  return rec(nbP:=NewNbP, next:=ePermNext, invers:=ePermInv);
end;

