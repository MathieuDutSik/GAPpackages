PlanGraphOrientedToABC_V1:=function(PLori, VEFori)
  local ePrev, ListFlags, nbDE, iDE, jDE, iFace, jFace, SetFlags, eListA, eListB, eListC, eFlag, eFlagA, nDE1, nDE2, eFlagB, eFlagC;
  ePrev:=Inverse(PLori.next);
  ListFlags:=[];
  nbDE:=PLori.nbP;
  for iDE in [1..nbDE]
  do
    jDE:=OnPoints(iDE, PLori.invers);
    iFace:=VEFori.ListOriginFace[iDE];
    jFace:=VEFori.ListOriginFace[jDE];
    Add(ListFlags, [iDE, iFace]);
    Add(ListFlags, [iDE, jFace]);
  od;
  SetFlags:=Set(ListFlags);
  if Length(SetFlags)<>Length(ListFlags) then
    Error("There are repetition in ListFlags. Not allowed");
  fi;
  eListA:=[];
  eListB:=[];
  eListC:=[];
  for eFlag in SetFlags
  do
    iDE:=eFlag[1];
    jDE:=OnPoints(iDE, PLori.invers);
    iFace:=VEFori.ListOriginFace[iDE];
    jFace:=VEFori.ListOriginFace[jDE];
    eFlagA:=[jDE, eFlag[2]];
    nDE1:=OnPoints(iDE, PLori.next);
    nDE2:=OnPoints(iDE, ePrev);
    if iFace=eFlag[2] then
      eFlagB:=[nDE1, eFlag[2]];
      eFlagC:=[iDE, jFace];
    else
      eFlagB:=[nDE2, eFlag[2]];
      eFlagC:=[iDE, iFace];
    fi;
    Add(eListA, eFlagA);
    Add(eListB, eFlagB);
    Add(eListC, eFlagC);
  od;
  return rec(nbP:=Length(SetFlags),
             permA:=SortingPerm(eListA),
             permB:=SortingPerm(eListB),
             permC:=SortingPerm(eListC),
             ListFlags:=SetFlags);
end;

POLYCYCLE_ConvertToRecCluster_V1:=function(ePolycycle)
  local AttainmentSequence, nbVert, iVert, eDeg, LVal, i, DoSomething, eSeqVal, iNext, iPrev, eSeqNext, eSeqPrev, eSeqInv, ListRet, AdjVert, posAdj, eEnt;
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
  AttainmentSequence[1][1]:=[];
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
	  iNext:=NextIdx(eDeg, i);
	  iPrev:=PrevIdx(eDeg, i);
	  if AttainmentSequence[iVert][iNext]="unset" then
	    eSeqNext:=Concatenation(eSeqVal, ["n"]);
	    AttainmentSequence[iVert][iNext]:=eSeqNext;
            DoSomething:=true;
	  fi;
	  if AttainmentSequence[iVert][iPrev]="unset" then
	    eSeqPrev:=Concatenation(eSeqVal, ["p"]);
	    AttainmentSequence[iVert][iPrev]:=eSeqPrev;
            DoSomething:=true;
	  fi;
          if ePolycycle[iVert][i].assigned=true then
            AdjVert:=ePolycycle[iVert][i].AdjVert;
            posAdj:=ePolycycle[iVert][i].posAdj;
            if AttainmentSequence[AdjVert][posAdj]="unset" then
              eSeqInv:=Concatenation(eSeqVal, ["i"]);
              AttainmentSequence[AdjVert][posAdj]:=eSeqInv;
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

