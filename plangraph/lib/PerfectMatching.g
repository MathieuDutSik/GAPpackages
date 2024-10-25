FilePerfectMatch:=Filename(DirectoriesPackagePrograms("plangraph"),"PerfectMatch");

MakeInputForPerfectMatching:=function(TheGRA, TheGamma)
  local FileGRA, FileGamma, FileOutput, output, nbVert, ListDeg, MaxDeg, i, ListAdj, eAdj, nbElt, eElt, TheCommand, TheReply, eList;
  FileGRA:=Filename(PLANGRAPH_tmpdir, "TheGRA");
  FileGamma:=Filename(PLANGRAPH_tmpdir, "TheGamma");
  FileOutput:=Filename(PLANGRAPH_tmpdir, "TheOut");
  RemoveFileIfExist(FileGRA);
  RemoveFileIfExist(FileGamma);
  RemoveFileIfExist(FileOutput);
  output:=OutputTextFile(FileGRA, true);
  nbVert:=TheGRA.order;
  AppendTo(output, nbVert, "\n");
  ListDeg:=List([1..nbVert], x->Length(Adjacency(TheGRA, x)));
  MaxDeg:=Maximum(ListDeg);
  AppendTo(output, MaxDeg, "\n");
  for i in [1..nbVert]
  do
    ListAdj:=Adjacency(TheGRA, i);
    AppendTo(output, Length(ListAdj));
    for eAdj in ListAdj
    do
      AppendTo(output, " ", eAdj);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
  #
  output:=OutputTextFile(FileGamma, true);
  nbElt:=Order(TheGamma);
  AppendTo(output, nbElt, "\n");
  AppendTo(output, nbVert, "\n");
  for eElt in TheGamma
  do
    eList:=List([1..nbVert], x->OnPoints(x, eElt));
    WriteVector(output, eList);
  od;
  CloseStream(output);
  #
  return rec(FileGamma:=FileGamma, FileGRA:=FileGRA);
end;

GetOrbitPerfectMatching:=function(TheGRA, TheGamma)
  local eRec, FileOutput, TheCommand, TheReply;
  eRec:=MakeInputForPerfectMatching(TheGRA, TheGamma);
  FileOutput:=Filename(PLANGRAPH_tmpdir, "TheOut");
  RemoveFileIfExist(FileOutput);
  #
  TheCommand:=Concatenation(FilePerfectMatch, " ", eRec.FileGRA, " ", eRec.FileGamma, " ", FileOutput, " 1");
  Exec(TheCommand);
  TheReply:=ReadAsFunction(FileOutput)();
  #
  RemoveFileIfExist(eRec.FileGRA);
  RemoveFileIfExist(eRec.FileGamma);
  RemoveFileIfExist(FileOutput);
  return TheReply;
end;

GetNrPerfectMatching:=function(TheGRA, TheGamma)
  local eRes, eRec, FileOutput, TheCommand, TheReply;
  eRes:=TheGRA.order mod 2;
  if eRes=1 then
    return rec( NbOrbit := 0, NbPerf := 0 );
  fi;
  eRec:=MakeInputForPerfectMatching(TheGRA, TheGamma);
  FileOutput:=Filename(PLANGRAPH_tmpdir, "TheOut");
  RemoveFileIfExist(FileOutput);
  #
  TheCommand:=Concatenation(FilePerfectMatch, " ", eRec.FileGRA, " ", eRec.FileGamma, " ", FileOutput, " 3");
  Exec(TheCommand);
  TheReply:=ReadAsFunction(FileOutput)();
  #
  RemoveFileIfExist(eRec.FileGRA);
  RemoveFileIfExist(eRec.FileGamma);
  RemoveFileIfExist(FileOutput);
  return TheReply;
end;


RandomAntisymmetricMatrix:=function(p, Max)
  local H, i, j, v;
  H:=NullMat(2*p, 2*p);
  for i in [2..2*p]
  do
    for j in [1..i-1]
    do
      v:=Random([-Max..Max]);
      H[i][j]:=v;
      H[j][i]:=-v;
    od;
  od;
  return H;
end;


IsAntisymmetricMatrix:=function(TheMat)
  local n, i,j;
  n:=Length(TheMat);
  if n<>Length(TheMat[1]) then
    return false;
  fi;
  for i in [1..n]
  do
    if TheMat[i][i]<>0 then
      return false;
    fi;
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      if TheMat[i][j]+TheMat[j][i]<>0 then
        return false;
      fi;
    od;
  od;
  return true;

end;

RandomCanonicalizeAntisymmetric:=function(p, Max)
  local H, i, j, v;
  H:=NullMat(2*p, 2*p);
  for i in [1..p]
  do
    v:=Random([-Max..Max]);
    H[2*i-1][2*i]:=v;
    H[2*i][2*i-1]:=-v;
  od;
  return H;
end;


#
#
# PL should be a planar graph
FindPfaffianOrientation:=function(PL)
  local LVERT, VEF, EdgeSet, FaceSet, EdgeSetRed, ListChoice, u, SPE, Pos, eFac, iCol, jCol, ThePfaffMat, List1, List2, GR, fDE1, fDE2, eDE1, eDE2, iDE, IsFinished, LC1, LC2, ListZero, fDE, FindPos, eEdge, eDE;
  VEF:=PlanGraphToVEFsecond(PL);
  EdgeSet:=VEF[2];
  FaceSet:=VEF[3];
  EdgeSetRed:=[];
  LC1:=[];
  LC2:=[];
  ListChoice:=[];
  for u in EdgeSet
  do
    Add(EdgeSetRed, Set([u[1][1], u[2][1]]));
    Add(ListChoice, 0);
    Add(LC1, u[1]);
    Add(LC2, u[2]);
  od;
  FindPos:=function(eDE)
    local Pos1, Pos2, Pos;
    Pos1:=Position(LC1, eDE);
    Pos2:=Position(LC2, eDE);
    if Pos1<> fail then
      Pos:=Pos1;
    else
      Pos:=Pos2;
    fi;
    return Pos;
  end;
  GR:=PlanGraphToGRAPE(PL);
  SPE:=SpanningTreeGraph(GR, 1);
  for eEdge in SPE
  do
    Pos:=Position(EdgeSetRed, eEdge);
    ListChoice[Pos]:=1;
  od;
  while(true)
  do
    for eFac in FaceSet
    do
      List1:=[];
      List2:=[];
      ListZero:=[];
      for eDE in eFac
      do
        Pos:=FindPos(eDE);
        if ListChoice[Pos]=0 then
          Add(ListZero, Pos);
        else
          fDE:=EdgeSet[Pos][ListChoice[Pos]];
          if fDE=eDE then
            Add(List1, Pos);
          else
            Add(List2, Pos);
          fi;
        fi;
      od;
      if Length(ListZero)=1 then
        Pos:=ListZero[1];
        eDE1:=EdgeSet[Pos][1];
        eDE2:=EdgeSet[Pos][2];
        if Length(List1) mod 2=0 then
          if Position(eFac, eDE1)<>fail then
            ListChoice[Pos]:=1;
          else
            ListChoice[Pos]:=2;
          fi;
        else
          if Position(eFac, eDE1)<>fail then
            ListChoice[Pos]:=2;
          else
            ListChoice[Pos]:=1;
          fi;
        fi;
      fi;
    od;
    #
    IsFinished:=true;
    for iDE in [1..Length(ListChoice)]
    do
      if ListChoice[iDE]=0 then
        IsFinished:=false;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  List1:=[];
  List2:=[];
  for iDE in [1..Length(EdgeSet)]
  do
    if ListChoice[iDE]=1 then
      eDE1:=EdgeSet[iDE][1];
      eDE2:=EdgeSet[iDE][2];
    else
      eDE1:=EdgeSet[iDE][2];
      eDE2:=EdgeSet[iDE][1];
    fi;
    fDE1:=[eDE1[1], PL[eDE1[1]][eDE1[2]]];
    fDE2:=[eDE2[1], PL[eDE2[1]][eDE2[2]]];
    Add(List1, fDE1);
    Add(List2, fDE2);
  od;

  ThePfaffMat:=NullMat(Length(PL), Length(PL));
  for iCol in [1..Length(PL)]
  do
    for jCol in [1..Length(PL)]
    do
      if IsEdge(GR, [iCol, jCol])=true then
        if Position(List1, [iCol,jCol])<>fail then
          ThePfaffMat[iCol][jCol]:=1;
        else
          ThePfaffMat[iCol][jCol]:=-1;
        fi;
      fi;      
    od;
  od;
  return ThePfaffMat;
end;




ExhaustiveSearchPerfectMatching:=function(GR)
  local nbV, ListCase, iter, ListNewCase, LStat, eCase, eEdge, NewCase, IsExtendible;
  nbV:=GR.order;
  IsExtendible:=function(PartialPL)
    local ListMatched, eDiff, U, Lowest, TheVert, Ladj, LPoss, LPSave, LZA, eVert;
    ListMatched:=[];
    for U in PartialPL
    do
      ListMatched:=Union(ListMatched, U);
    od;
    eDiff:=Difference([1..nbV], ListMatched);
    Lowest:=nbV;
    TheVert:=0;
    for eVert in eDiff
    do
      Ladj:=Set(Adjacency(GR, eVert));
      LPoss:=Difference(Ladj, ListMatched);
      if Length(LPoss)<Lowest then
        TheVert:=eVert;
        Lowest:=Length(LPoss);
        LPSave:=ShallowCopy(LPoss);
      fi;
      if Lowest=0 then
        return false;
      fi;
    od;
    LZA:=[];
    for eVert in LPSave
    do
      AddSet(LZA, Set([TheVert, eVert]));
    od;
    return LZA;
  end;

  ListCase:=[ [] ];
  for iter in [1..nbV/2]
  do
    ListNewCase:=[];
    for eCase in ListCase
    do
      LStat:=IsExtendible(eCase);
      if LStat<>false then
        for eEdge in LStat
        do
          NewCase:=Union(eCase, [ eEdge]);
          AddSet(ListNewCase, NewCase);
        od;
      fi;
    od;
    ListCase:=ShallowCopy(ListNewCase);
  od;
  return ListCase;
end;




IsPerfectMatchingPlangraph:=function(GR, ThePM)
  local nbV, u;
  for u in ThePM
  do
    if Length(u)<>2 then
      return false;
    fi;
  od;
  nbV:=GR.order;
  if Union(ThePM)<>[1..nbV] then
    return false;
  fi;
  if nbV<>2*Length(ThePM) then
    return false;
  fi;
  return true;
end;




FindOrbitPerfectMatching:=function(GR, LPM)
  local GRP, LORB, ListInfos, eRep, TehStab, eOrbit, TheStab;
  GRP:=AutGroupGraph(GR);
  LORB:=Orbits(GRP, LPM, OnSetsDisjointSets);
  ListInfos:=[];
  for eOrbit in LORB
  do
    eRep:=eOrbit[1];
    TheStab:=Stabilizer(GRP, eRep, OnSetsDisjointSets);
    Add(ListInfos, rec(eRep:=eRep, TheStab:=TheStab));
  od;
  return ListInfos;
end;

#
# operation Li <--> Lj and Ci <--> Cj if ThePerm=(i,j)
PermutationRowColumn:=function(TheMat, ThePerm)
  local NewMat, i;
  NewMat:=[];
  for i in [1..Length(TheMat)]
  do
    Add(NewMat, Permuted(TheMat[i], ThePerm));
  od;
  return Permuted(NewMat, ThePerm);
end;

#
# operations, Lj <- alpha*Lj and Cj<-alpha*Cj
RowColumnMultiplication:=function(TheMat, j, alpha)
  local NewMat, i;
  NewMat:=[];
  for i in [1..Length(TheMat)]
  do
    if i<>j then
      Add(NewMat, TheMat[i]);
    else
      Add(NewMat, alpha*TheMat[i]);
    fi;
  od;
  for i in [1..Length(TheMat)]
  do
    NewMat[i][j]:=alpha*NewMat[i][j];
  od;
  return NewMat;
end;

#
# operations, Li<- Li+alpha Lj
# operations, Ci<- Ci+alpha Ci
AdditionRowColumn:=function(TheMat, i, j, alpha)
  local NewMat, k;
  NewMat:=[];
  for k in [1..Length(TheMat)]
  do
    if k=i then
      Add(NewMat, TheMat[i]+alpha*TheMat[j]);
    else
      Add(NewMat, TheMat[k]);
    fi;
  od;
  for k in [1..Length(NewMat)]
  do
    NewMat[k][i]:=NewMat[k][i]+alpha*NewMat[k][j];
  od;
  return NewMat;
end;


#
# freely inspired from DeterminantMatDestructive
Pfaffian:=function(MatInput)
  local i, m, p, piv, zero, pfaff, j, k, sgn, row, row2, mult, mult2, result, AntiSymMat;
  AntiSymMat:=StructuralCopy(MatInput);
  m:=Length(AntiSymMat);
  if m mod 2=1 then
    return 0;
  fi;
  p:=m/2;
  zero:=Zero(AntiSymMat[1][1]);
  pfaff:=1;
  sgn:=1;
  for k in [1..p]
  do
    j:=2*k;
    while j<=m and AntiSymMat[2*k-1][j]=zero
    do
      j:=j+1;
    od;
    if j>m then
      return zero;
    fi;
    if j<> 2*k then
      AntiSymMat:=PermutationRowColumn(AntiSymMat, (j,2*k));
      sgn:=-sgn;
    fi;
    row:=AntiSymMat[2*k];
    piv:=row[2*k-1];
    for j in [2*k+1..m]
    do
      row2:=AntiSymMat[j];
      mult:=-row2[2*k-1];
      #  
      AntiSymMat:=RowColumnMultiplication(AntiSymMat, j, piv);
      #
      AntiSymMat:=AdditionRowColumn(AntiSymMat, j, 2*k, mult);
      #
      row2:=AntiSymMat[j];
      mult2:=row2[2*k]/piv;
      AntiSymMat:=AdditionRowColumn(AntiSymMat, j, 2*k-1, mult2);
      #
      AntiSymMat:=RowColumnMultiplication(AntiSymMat, j, Inverse(pfaff));
    od;
    pfaff:=-piv;
  od;
  result:=pfaff;
  for k in [1..p-1]
  do
    result:=result/AntiSymMat[2*k-1][2*k];
  od;
  return sgn*result;
end;




