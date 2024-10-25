BindGlobal("PLANGRAPH_tmpdir",DirectoryTemporary());


GetHostName:=function()
  local FileD1, FileD2, reply;
  FileD1:="/tmp/HostName1";
  FileD2:="/tmp/HostName2";
  Exec("echo $HOSTNAME > ", FileD1);
  reply:=ReadAsFunction(FileD2)();
  RemoveFile(FileD1);
  RemoveFile(FileD2);
  return reply;
end;





PrintNumber:=function(output, nbr)
  AppendTo(output, "\$", nbr, "\$");
end;


StringLatex:=function(nbr)
  if nbr<10 then
    return String(nbr);
  else
    return Concatenation("{", String(nbr),"}");
  fi;
end;



SyncTextOccurrence:=function(ListOcc)
  local SString, iC, Obj, mult;
  SString:="";
  for iC in [1..Length(ListOcc)]
  do
    Obj:=ListOcc[iC][1];
    mult:=ListOcc[iC][2];
    if mult=1 then
      SString:=Concatenation(SString, String(Obj));
    else
      SString:=Concatenation(SString, String(Obj), "^{", String(mult), "}");
    fi;
    if iC<Length(ListOcc) then
      SString:=Concatenation(SString, ", ");
    fi;
  od;
  return SString;
end;










# this procedure Build the Set:  Seto x Seto x .... x Seto
BuildSet:=function(n, Seto)
  local DO, i, iCol, U, V,C, iSet;
  DO:=[[]];
  for iCol in [1..n]
  do
    C:=ShallowCopy(DO);
    DO:=ShallowCopy([]);
    for i in [1..Length(C)]
    do
      for iSet in [1..Length(Seto)]
      do
	U:=ShallowCopy(C[i]);
        Add(U, Seto[iSet]);
        Add(DO, U);
      od;
    od;
  od;
  return DO;
end;




# this procedure Build the Set:  Seto1 x Seto2 x .... x SetoN
BuildSetMultiple:=function(ListSeto)
  local DO, i, iCol, U, V,C, iSet;
  DO:=[[]];
  for iCol in [1..Length(ListSeto)]
  do
    C:=ShallowCopy(DO);
    DO:=ShallowCopy([]);
    for i in [1..Length(C)]
    do
      for iSet in [1..Length(ListSeto[iCol])]
      do
	U:=ShallowCopy(C[i]);
        Add(U, ListSeto[iCol][iSet]);
        Add(DO, U);
      od;
    od;
  od;
  return DO;
end;





ProductList:=function(SetList1, SetList2)
  local idx1, idx2, ListR, iCol, h, S, U;
  ListR:=[];
  for idx1 in [1..Length(SetList1)]
  do
    h:=Length(SetList1[idx1]);
    for idx2 in [1..Length(SetList2)]
    do
      U:=SetList2[idx2];
      S:=ShallowCopy(SetList1[idx1]);
      for iCol in [1..Length(U)]
      do
	S[h+iCol]:=U[iCol];
      od;
      Add(ListR, S);
    od;
  od;
  return ListR;
end;



FromHypermetricVectorToHypermetricFace:=function(HypV)
  local HypDim, V, i, j, S, k, iCol;
  HypDim:=Length(HypV);
  S:=0;
  for iCol in [1..HypDim]
  do
    S:=S+HypV[iCol];
  od;
  k:=(S-1)/2;
  V:=[k*(k+1)];
  #
  for i in [1..HypDim-1]
  do
    for j in [i+1..HypDim]
    do
      Add(V, -HypV[i]*HypV[j]);
    od;
  od;
  return V;
end;






#
#
# remove isomorphic objects using a function of isomorphy testing and a list
# of invariants to speed up computations
RemoveByIsomorphy:=function(ListObject, ListInvariantObject, FuncIsomorph)
  local ClassBelong, STATUS, iA, iB, Lrep, Linvariant, Lmatch, Lsample, Matched;
  ClassBelong:=[];
  STATUS:=[];
  for iA in [1..Length(ListObject)]
  do
    ClassBelong[iA]:=-1;
    STATUS[iA]:=1;
  od;
#  Print("SIZ=", Order(AutGroupGraph(Gr)), "\n");
  for iA in [1..Length(ListObject)]
  do
    if ClassBelong[iA]=-1 then
      ClassBelong[iA]:=iA;
      for iB in [iA+1..Length(ListObject)]
      do
	if ListInvariantObject[iA]=ListInvariantObject[iB] and STATUS[iB]=1 then
	  if FuncIsomorph(ListObject[iA], ListObject[iB])=true then
	    ClassBelong[iB]:=iA;
            STATUS[iB]:=0;
	  fi;
	fi;
      od;
    fi;
  od;
  Lrep:=[];
  Linvariant:=[];
  Lmatch:=[];
  Lsample:=[];
  for iA in [1..Length(ListObject)]
  do
    if STATUS[iA]<>0 then
      Matched:=[];
      for iB in [1..Length(ListObject)]
      do
        if ClassBelong[iB]=iA then
          Add(Matched, iB);
        fi;
      od;
      Add(Lrep, ListObject[iA]);
      Add(Linvariant, ListInvariantObject[iA]);
      Add(Lmatch, Matched);
      Add(Lsample, iA);
    fi;
  od;
  return rec(NonIsomorphRepresentant:=Lrep, IsomorphyClass:=Lmatch, ListInvariant:=Linvariant, ListSample:=Lsample);
end;


CanonicalizationOnTuplesAction:=function(Tuple, GroupEXT)
  local g, ReturnedTuple, GrpStab, iRank, O;
  ReturnedTuple:=ShallowCopy(Tuple);
  GrpStab:=ShallowCopy(GroupEXT);
  for iRank in [1..Length(Tuple)]
  do
    O:=Set(Orbit(GrpStab, ReturnedTuple[iRank], OnPoints));
    g:=RepresentativeAction(GrpStab, ReturnedTuple[iRank], O[1], OnPoints);
    ReturnedTuple:=OnTuples(ReturnedTuple, g);
    GrpStab:=Stabilizer(GrpStab, ReturnedTuple[iRank], OnPoints);
  od;
  return ReturnedTuple;
end;


CanonicalizationOnSetAction:=function(eSet, eSubSet, Group)
  local FuncCanonicalizationMultipleOrbit, FuncCanonicalizationSingleOrbit;
  #
  # return the canonicalized and the element of the group doing it.
  FuncCanonicalizationMultipleOrbit:=function(eSet, eSubSet, Group)
    local eOrb, Can, Diffe, Stab, fSubSet, Can2;
    eOrb:=Set(Orbit(Group, Minimum(eSet), OnPoints));
    Can:=FuncCanonicalizationSingleOrbit(eOrb, Intersection(eOrb, eSubSet), Group);
    Diffe:=Difference(eSet, eOrb);
    if Length(Diffe)=0 then
      return Can.eSet;
    else
      fSubSet:=OnSets(eSubSet, Can.g);
      Stab:=Stabilizer(Group, Can.eSet, OnSets);
      Can2:=FuncCanonicalizationMultipleOrbit(Diffe, Intersection(Diffe, fSubSet), Stab);
      return Union(Can2, fSubSet);
    fi;
  end;
  FuncCanonicalizationSingleOrbit:=function(eSet, eSubSet, Group)
    local Orb, Stab, eSet2, RatingList, fSubSetList, GroupEltList, iElt, g, fSubSet, Rate, iOrb, RatedMaxi, ListPossibility, ListPos, ePos, iPos, MiniM;
    if eSubSet=[] then
      return [];
    elif Length(eSubSet)=1 then
      return [eSet[1]];
    elif eSet=eSubSet then
      return eSubSet;
    fi;
    Stab:=Stabilizer(Group, eSet[1], OnPoints);
    eSet2:=Difference(eSet, [eSet[1]]);
    Orb:=Orbits(Stab, eSet2, OnPoints);
    Sort(Orb);
    RatingList:=[];
    GroupEltList:=[];
    fSubSetList:=[];
    for iElt in [1..Length(eSubSet)]
    do
      g:=RepresentativeAction(Group, eSubSet[iElt], eSet[1], OnPoints);
      fSubSet:=Difference(OnSets(eSubSet, g), [eSet[1]]);
      Add(fSubSetList, fSubSet);
      Add(GroupEltList, g);
      Rate:=[];
      for iOrb in [1..Length(Orb)]
      do
        Add(Rate, Length(Intersection(fSubSet, Orb[iOrb])));
      od;
      Add(RatingList, Rate);
    od;
    RatedMaxi:=RatingList[1];
    ListPossibility:=[];
    for iElt in [2..Length(eSubSet)]
    do
      if RatingList[iElt]>RatedMaxi then
        RatedMaxi:=[];
        ListPossibility:=[iElt];
      elif RatingList[iElt]=RatedMaxi then
        Add(ListPossibility, iElt);
      fi;
    od;
    ListPos:=[];
    for iPos in [1..Length(ListPossibility)]
    do
      ePos:=ListPossibility[iPos];
      Add(ListPos, FuncCanonicalizationMultipleOrbit(eSet2, fSubSetList[ePos], Stab));
    od;
    MiniM:=Minimum(ListPos);
    iPos:=Position(ListPos, MiniM);
    AddSet(MiniM, eSet[1]);
    return rec(eSet:=MiniM, g:=GroupEltList[ListPossibility[iPos]]);
  end;
  return FuncCanonicalizationMultipleOrbit(eSet, eSubSet, Group);
end;





Is3connected:=function(GRA)
  local nbVert, iVert, jVert, eCand, IndGra;
  nbVert:=GRA.order;
  for iVert in [1..nbVert-1]
  do
    for jVert in [iVert+1..nbVert]
    do
      eCand:=[iVert, jVert];
      IndGra:=InducedSubgraph(GRA, Difference([1..nbVert], eCand));
      if IsConnectedGraph(IndGra)=false then
        return false;
      fi;
    od;
  od;  
  return true;
end;



#
#
# An API for saving large list on disk and hence avoid
# a memory problem, while retaining most of the speed.
FuncStocking:=function(nbPerFile, DirName, StockName)
  local FuncClear, FuncAdd, FuncNbrElement, FuncGet, TheOrder, CurrentFileSave, CurrentFileGet, NbObject, CurrentListObjSave, CurrentListObjGet, LastRawposSave;
  CurrentFileSave:="void";
  CurrentFileGet:="void";
  NbObject:=0;
  CurrentListObjSave:=[];
  CurrentListObjGet:=[];
  LastRawposSave:=0;
  FuncAdd:=function(TheObject)
    local rawpos;
    NbObject:=NbObject+1;
    Add(CurrentListObjSave, TheObject);
    if (NbObject mod nbPerFile)=0 then
      rawpos:=NbObject/nbPerFile;
      LastRawposSave:=rawpos;
      Print("Creating FileSave", rawpos, "\n");
      CurrentFileSave:=Filename(DirName,Concatenation(StockName, String(rawpos)));
      SaveDataToFile(CurrentFileSave, CurrentListObjSave);
      CurrentListObjSave:=[];
      TheOrder:=Concatenation("gzip ", CurrentFileSave);
      Exec(TheOrder);
    fi;
  end;
  FuncNbrElement:=function()
    return NbObject;
  end;
  FuncGet:=function(idx)
    local idx2, rawpos, FileGet, FileTmp;
    idx2:=idx mod nbPerFile;
    if idx2=0 then
      idx2:=nbPerFile;
    fi;
    rawpos:=1+((idx-idx2)/nbPerFile);
    if rawpos>LastRawposSave then
      return CurrentListObjSave[idx2];
    fi;
    FileGet:=Filename(DirName,Concatenation(StockName, String(rawpos), ".gz"));
    if FileGet<>CurrentFileGet then
      Print("Loading FileSave", rawpos, "\n");
      FileTmp:=Filename(DirName, Concatenation(StockName, String(rawpos)));
      TheOrder:=Concatenation("gunzip ", FileGet);
      Exec(TheOrder);
      CurrentListObjGet:=ReadAsFunction(FileTmp)();
      RemoveFile(FileTmp);
      CurrentFileGet:=FileGet;
    fi;
    return CurrentListObjGet[idx2];
  end;
  FuncClear:=function()
    local NbFile, a, iF, FileDestroy;
    a:=NbObject mod nbPerFile;
    NbFile:=(NbObject-a)/nbPerFile;
    for iF in [1..NbFile]
    do
      FileDestroy:=Filename(DirName,Concatenation(StockName, String(iF), ".gz"));
      RemoveFile(FileDestroy);
    od;
    Unbind(CurrentListObjSave);
    Unbind(CurrentListObjGet);
  end;
  return rec(FuncAdd:=FuncAdd, FuncNbrElement:=FuncNbrElement, FuncGet:=FuncGet, FuncClear:=FuncClear);
end;



