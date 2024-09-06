
LORENTZ_SearchInitialPerfect_SelectLP:=function(LorMat, ListIso, fLev)
  local n, eIso, ListIneq, NegVect, nbIter, eVect, i, eVal, ToBeMinimized, TheLP, eVectEmb, eEnt, eInc, ListVect, TheRec;
  eIso:=Isobarycenter(ListIso);
  n:=Length(LorMat);
  ListIneq:=List(ListIso, x->Concatenation([1],x - eIso));
  NegVect:=EigenvalueFindNegativeVect(LorMat);
  nbIter:=0;
  while(true)
  do
    nbIter:=nbIter+1;
    Print("nbIter=", nbIter, "\n");
    eVect:=ListWithIdenticalEntries(n,0);
    for i in [1..n]
    do
      eVal:=Random([-fLev..fLev]);
      eVect[i]:=eVal;
    od;
    while(true)
    do
      if eVect*LorMat*eVect < 0 then
        break;
      fi;
      eVect:=eVect + NegVect;
    od;
    ToBeMinimized:=Concatenation([0], eVect*LorMat);
    TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
    if IsBound(TheLP.primal_solution) then
      Print("  IsBound\n");
      eVectEmb:=ListWithIdenticalEntries(1+n,0);
      eVectEmb[1]:=1;
      for eEnt in TheLP.primal_solution
      do
        eVectEmb[1+eEnt[1]]:=eEnt[2];
      od;
      eInc:=Filtered([1..Length(ListIneq)], x->ListIneq[x]*eVectEmb=0);
      Print("  |eInc|=", Length(eInc), "\n");
      ListVect:=ListIso{eInc};
      TheRec:=LORENTZ_IsPerfectConf(LorMat, ListVect);
      if TheRec.reply then
        return rec(ListVect:=TheRec.ListVect, eVect:=TheRec.eVect);
      fi;
      Print("  reason=", TheRec.reason, "\n");
    fi;
  od;
end;


LORENTZ_SearchInitialPerfect_RandomWalk:=function(LorMat, ListIso)
  local n, CritVal, EXT, nb, ListCand, WeFound, eCand, TheInit, ListVect, TheRec, RPLift, EXTcand, GRP, ListOrb, ListInc, eOrb, fInc, MinSiz, nbIter;
  n:=Length(LorMat);
  CritVal:=n+20;
  EXT:=List(ListIso, x->Concatenation([1],x));  
  while(true)
  do
    nb:=20;
    ListCand:=GetInitialRays_LinProg(EXT, nb);
    WeFound:=false;
    for eCand in ListCand
    do
      if Length(eCand) < CritVal then
        if WeFound then
          if Length(eCand) < Length(TheInit) then
            TheInit:=eCand;
          fi;
        else
          WeFound:=true;
          TheInit:=eCand;
        fi;
      fi;
    od;
    if WeFound then
      break;
    fi;
  od;
  #
  Print("|eCand|=", Length(eCand), "\n");
  ListVect:=ListIso{eCand};
  TheRec:=LORENTZ_IsPerfectConf(LorMat, ListVect);
  if TheRec.reply then
    return rec(ListVect:=TheRec.ListVect, eVect:=TheRec.eVect);
  fi;
  #
  nbIter:=0;
  while(true)
  do
    nbIter:=nbIter+1;
    Print("  nbIter=", nbIter, "\n");
    RPLift:=__ProjectionLiftingFramework(EXT, eCand);
    EXTcand:=EXT{eCand};
#    GRP:=LinPolytope_Automorphism(EXTcand);
#    ListOrb:=DualDescriptionStandard(EXTcand, GRP);
    ListOrb:=DualDescriptionSets(EXTcand);
    Print("|ListOrb|=", Length(ListOrb), "\n");
    ListInc:=[];
    for eOrb in ListOrb
    do
      fInc:=RPLift.FuncLift(eOrb);
      Add(ListInc, fInc);
      ListVect:=ListIso{eCand};
      TheRec:=LORENTZ_IsPerfectConf(LorMat, ListVect);
      if TheRec.reply then
        return rec(ListVect:=TheRec.ListVect, eVect:=TheRec.eVect);
      else
        Print("   reason=", TheRec.reason, "\n");
      fi;
    od;
    MinSiz:=Minimum(List(ListInc, Length));
    eCand:=First(ListInc, x->Length(x)=MinSiz);
  od;

end;

