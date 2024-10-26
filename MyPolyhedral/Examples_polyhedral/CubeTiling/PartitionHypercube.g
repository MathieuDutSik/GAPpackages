Read("CubeTiling.g");

n:=4;

VE:=SymmetryGroup(n);
BasicSpann:=BuildSet(n, [0,1]);

SpanSet:=function(eVert)
  local NewSpan, eVect, fVert, eVal, i;
  NewSpan:=[];
  for eVect in BasicSpann
  do
    fVert:=[];
    for i in [1..4]
    do
      eVal:=eVert[i] + eVect[i];
      if eVal = 4 then
        Add(fVert, 0);
      else
        Add(fVert, eVal);
      fi;
    od;
    Add(NewSpan, fVert);
  od;
  return NewSpan;
end;

ListSet:=[];
for eVert in VE.VertexSet
do
  eListVert:=SpanSet(eVert);
  eSet:=Set(List(eListVert, x->Position(VE.VertexSet, x)));
  Add(ListSet, eSet);
od;

FuncRespawn:=function(n, nbSet, sizGRP)
  if n<225 then
    return false;
  fi;
  if sizGRP<200 then
    return false;
  fi;
  return true;
end;

FuncAddiSymm:=function(n, nbSet, sizGRP)
  return true;
end;

RecFunc:=rec(FuncRespawn:=FuncRespawn, FuncAddiSymm:=FuncAddiSymm);

FileSave:="DATA/ListOrbitPartition";
if IsExistingFilePlusTouch(FileSave)=false then
  O:=PARTITION_EnumerateEquivariant_NextGen(4^n, ListSet, VE.SymmetryGroup, RecFunc);
  SaveDataToFilePlusTouch(FileSave, O);
else
  O:=ReadAsFunction(FileSave)();
fi;

IsDirectAdjacent:=function(eVert, fVert)
  local nbEqualCoord, i;
  nbEqualCoord:=0;
  for i in [1..n]
  do
    if eVert[i]=fVert[i] then
      nbEqualCoord:=nbEqualCoord+1;
    fi;
  od;
  if nbEqualCoord=n-1 then
    return true;
  fi;
  return false;
end;


IsZAdjacent:=function(eVert, fVert)
  local nbDiff1, eDiff, i;
  nbDiff1:=0;
  for i in [1..n]
  do
    eDiff:=AbsInt(eVert[i] - fVert[i]);
    if eDiff=3 then
      eDiff:=1;
    fi;
    if eDiff=1 then
      nbDiff1:=nbDiff1 + 1;
    fi;
  od;
  if nbDiff1=0 then
    return true;
  fi;
  return false;
end;



GetSignatureInfo:=function(ListVert)
  local IsLayered, i, ListVal, nbTwinPair, nbVert, iVert, jVert, GRA, LConn, eConn, nbSimpleComponent;
  IsLayered:=false;
  for i in [1..n]
  do
    ListVal:=List(ListVert, x->x[i]);
    if Length(Set(ListVal))=2 then
      IsLayered:=true;
    fi;
  od;
  #
  nbTwinPair:=0;
  nbVert:=Length(ListVert);
  for iVert in [1..nbVert]
  do
    for jVert in [iVert+1..nbVert]
    do
      if IsDirectAdjacent(ListVert[iVert], ListVert[jVert]) then
        nbTwinPair:=nbTwinPair+1;
      fi;
    od;
  od;
  #
  GRA:=NullGraph(Group(()), nbVert);
  for iVert in [1..nbVert]
  do
    for jVert in [iVert+1..nbVert]
    do
      if IsZAdjacent(ListVert[iVert], ListVert[jVert]) then
        AddEdgeOrbit(GRA, [iVert, jVert]);
        AddEdgeOrbit(GRA, [jVert, iVert]);
      fi;
    od;
  od;
  LConn:=ConnectedComponents(GRA);
  nbSimpleComponent:=Length(LConn);
  #
  return rec(IsLayered:=IsLayered, nbTwinPair:=nbTwinPair, nbSimpleComponent:=nbSimpleComponent);
end;


PrintSignatureInfo:=function(ListVert)
  local ListVal, nbVert, iVert, jVert, GRA, LConn, eConn, eVert, fVert;
  #
  nbVert:=Length(ListVert);
  for iVert in [1..nbVert]
  do
    for jVert in [iVert+1..nbVert]
    do
      eVert:=ListVert[iVert];
      fVert:=ListVert[jVert];
      if IsDirectAdjacent(eVert, fVert) then
        Print("Twin pair eVert=", eVert, " fVert=", fVert, "\n");
      fi;
    od;
  od;
  #
  GRA:=NullGraph(Group(()), nbVert);
  for iVert in [1..nbVert]
  do
    for jVert in [iVert+1..nbVert]
    do
      if IsZAdjacent(ListVert[iVert], ListVert[jVert]) then
        AddEdgeOrbit(GRA, [iVert, jVert]);
        AddEdgeOrbit(GRA, [jVert, iVert]);
      fi;
    od;
  od;
  LConn:=ConnectedComponents(GRA);
  for eConn in LConn
  do
    Print("Simple Component eComp=", ListVert{eConn}, "\n");
  od;
end;





ListInv:=[];
ListInvNonLay:=[];
ListListVert:=[];
FileSave:="List183.txt";
RemoveFileIfExist(FileSave);
output:=OutputTextFile(FileSave, true);
idx:=0;
ListSet183:=[];
ListListVert183:=[];
for eO in O
do
  TheListVert:=VE.VertexSet{eO};
  Add(ListListVert, TheListVert);
  eInv:=GetSignatureInfo(TheListVert);
  Add(ListInv, eInv);
  if eInv.IsLayered=false then
    Add(ListSet183, eO);
    Add(ListInvNonLay, eInv);
    Add(ListListVert183, TheListVert);
    idx:=idx+1;
    AppendTo(output, idx, " // nbTwinPair=", eInv.nbTwinPair, " nbSimpleComponent=", eInv.nbSimpleComponent, "\n");
    for eVert in TheListVert
    do
      for eVal in eVert
      do
        AppendTo(output, " ", eVal);
      od;
      AppendTo(output, "\n");
    od;
  fi;
od;
CloseStream(output);

FindNumber:=function(nbTwinPair, nbSimpleComponent)
  local nb, eInv;
  nb:=0;
  for eInv in ListInvNonLay
  do
    if eInv.nbTwinPair=nbTwinPair and eInv.nbSimpleComponent=nbSimpleComponent then
      nb:=nb+1;
    fi;
  od;
  return nb;
end;




IsCorrectConfiguration:=function(ListVert)
  local nbVert, iVert, jVert, nbDiff, i, eDiff, eVert, fVert;
  nbVert:=Length(ListVert);
  for iVert in [1..nbVert]
  do
    for jVert in [iVert+1..nbVert]
    do
      eVert:=ListVert[iVert];
      fVert:=ListVert[jVert];
      nbDiff:=0;
      for i in [1..n]
      do
        eDiff:=AbsInt(eVert[i] - fVert[i]);
	if eDiff=2 then
	  nbDiff:=nbDiff+1;
	fi;
      od;
      if nbDiff=0 then
        Print("Collision for eVert=", eVert, " fVert=", fVert, "\n");
        return false;
      fi;
    od;
  od;
  return true;
end;


ListVert65:=[
[1,1,1,1],
[1,1,1,3],
[1,3,3,1],
[1,3,3,3],
[2,1,3,2],
[2,3,1,2],
[0,1,3,2],
[0,3,1,2],
[3,2,2,0],
[3,0,2,0],
[1,1,3,0],
[1,3,1,0],
[3,1,1,2],
[3,3,3,2],
[3,1,0,0],
[3,3,0,0]];

test65:=IsCorrectConfiguration(ListVert65);

PrintSignatureInfo(ListVert65);

CheckConformance:=function(OtherList)
  local nbOther, ListOrbitOth, ListSetOth, ListTestCorr, i, eList, testCorr, eSet, j, eSet1, eSet2, ListMatched;
  Print("Begin of CheckConformance\n");
  nbOther:=Length(OtherList);
  ListOrbitOth:=[];
  ListSetOth:=[];
  ListTestCorr:=[];
  for i in [1..nbOther]
  do
    Print("i=", i, "\n");
    eList:=OtherList[i];
    testCorr:=IsCorrectConfiguration(eList);
    eSet:=Set(List(eList, x->Position(VE.VertexSet, x)));
    Add(ListOrbitOth, eList);
    Add(ListTestCorr, testCorr);
    Add(ListSetOth, eSet);
  od;
  Print("Arrays created\n");
  #
  for i in [1..nbOther]
  do
    for j in [i+1..nbOther]
    do
      eSet1:=ListSetOth[i];
      eSet2:=ListSetOth[j];
      test:=RepresentativeAction(VE.SymmetryGroup, eSet1, eSet2, OnSets);
      if test<>fail then
        Print("Find isomorphism between other-packing i=", i, " and other-packing j=", j, "\n");
      fi;
    od;
  od;
  Print("Isomorphism checks done\n");
  #
  ListMatched:=[];
  for i in [1..183]
  do
    Add(ListMatched, []);
  od;
  for i in [1..nbOther]
  do
    for j in [1..183]
    do
      eSet1:=ListSetOth[i];
      eSet2:=ListSet183[j];
      test:=RepresentativeAction(VE.SymmetryGroup, eSet1, eSet2, OnSets);
      if test<>fail then
        Add(ListMatched[j], i);
      fi;
    od;
  od;
  for i in [1..183]
  do
    if Length(ListMatched[i])=0 then
      Print("Orbit i=", i, " is unmatched\n");
    fi;
  od;
end;


PrintPaperInvariant:=function(ListListVert)
  local nbList, iList, eListVert, eSignInfo;
  nbList:=Length(ListListVert);
  for iList in [1..nbList]
  do
    eListVert:=ListListVert[iList];
    eSignInfo:=GetSignatureInfo(eListVert);
    Print("iList=", iList, " nbTwinPair=", eSignInfo.nbTwinPair, " nbSimpleComponent=", eSignInfo.nbSimpleComponent, "\n");
  od;
end;







TreatList187:=false;
if TreatList187 then
  U:=ReadVectorFile("structureD4_B.txt");
  Ufilt:=Filtered(U, x->Length(x)=4);

  ListOrbit187:=[];
  for i in [1..187]
  do
    Print("i=", i, "\n");
    iBegin:=16*(i-1) + 1;
    iEnd  :=16*(i-1) + 16;
    eList:=Ufilt{[iBegin..iEnd]};
    Add(ListOrbit187, eList);
  od;
  CheckConformance(ListOrbit187);
fi;

TreatList183_v9:=false;
if TreatList183_v9 then
  U:=ReadVectorFile("ListStruct183_v9.txt");
  ListOrbit183_v9:=[];
  for i in [1..183]
  do
    Print("i=", i, "\n");
    iBegin:=16*(i-1) + 1;
    iEnd  :=16*(i-1) + 16;
    eList:=U{[iBegin..iEnd]};
    Add(ListOrbit183_v9, eList);
  od;
  CheckConformance(ListOrbit183_v9);
fi;

TreatList183_v11:=false;
if TreatList183_v11 then
  U:=ReadVectorFile("ListStruct183_v11.txt");
  ListOrbit183_v11:=[];
  for i in [1..183]
  do
    Print("i=", i, "\n");
    iBegin:=16*(i-1) + 1;
    iEnd  :=16*(i-1) + 16;
    eList:=U{[iBegin..iEnd]};
    Add(ListOrbit183_v11, eList);
  od;
#  CheckConformance(ListOrbit183_v11);
  PrintPaperInvariant(ListOrbit183_v11);
fi;



TreatList183_v12:=true;
if TreatList183_v12 then
  U:=ReadVectorFile("ListStruct183_v12.txt");
  ListOrbit183_v12:=[];
  for i in [1..183]
  do
    Print("i=", i, "\n");
    iBegin:=16*(i-1) + 1;
    iEnd  :=16*(i-1) + 16;
    eList:=U{[iBegin..iEnd]};
    Add(ListOrbit183_v12, eList);
  od;
  CheckConformance(ListOrbit183_v12);
#  PrintPaperInvariant(ListOrbit183_v12);
fi;


