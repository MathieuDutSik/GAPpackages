FileEquality:=Filename(DirectoriesPackagePrograms("polyhedral"),"Equality");
FileDetector:=Filename(DirectoriesPackagePrograms("polyhedral"),"Detector");
FileDetectorMinimal:=Filename(DirectoriesPackagePrograms("polyhedral"),"DetectorMinimal");
FileNudifyLRS_reduction:=Filename(DirectoriesPackagePrograms("polyhedral"),"NudifyLRS.reduction");
FileNudifyCDD_splitter:=Filename(DirectoriesPackagePrograms("polyhedral"),"NudifyLRS.splitter");
FileGet_Rays:=Filename(DirectoriesPackagePrograms("polyhedral"),"get_rays");
FileNudifyLRS_splitter:=Filename(DirectoriesPackagePrograms("polyhedral"),"NudifyLRS.splitter");
FileNudifyLRS_Canonicalize:=Filename(DirectoriesPackagePrograms("polyhedral"),"NudifyLRS.Canonicalize");
FilePD:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"pd");


Formal_CVPVallentinProgram:=function(GramMat, eV)
  return List(CVPVallentinProgram(GramMat, eV{[2..Length(eV)]}).ListVect, x->Concatenation([1], x));
end;





Pre__GetRays:=function(EXT, nb)
  local FileExt, FileIne, output, Ladj;
  FileExt:=Filename(POLYHEDRAL_tmpdir, "GET.ext");
  FileIne:=Filename(POLYHEDRAL_tmpdir, "GET.ine");
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, Length(EXT[1]), " ", Length(EXT), "\n");
  WriteMatrix(output, EXT);
  CloseStream(output);
  Print("getting some rays ", FileExt, "\n");
  Exec(FileGet_Rays, " -n ", String(nb), " < ", FileExt, " > ", FileIne);
  Ladj:=ReadVectorFile(FileIne);
  RemoveFile(FileExt);
  RemoveFile(FileIne);
  return Ladj;
end;



GetRAYS:=function(EXT, nb)
  local FileExt, FileIne, output, Ladj, eSub, EXTred, ListListInc, eFac;
  eSub:=__ProjectionFrame(EXT);
  EXTred:=List(EXT, x->x{eSub});
  Ladj:=SomeFacets(EXTred, nb);
  ListListInc:=[];
  for eFac in Ladj{[2..Length(Ladj)]}
  do
    Add(ListListInc, Filtered([1..Length(EXTred)], x->EXTred[x]*eFac=0));
  od;
  return ListListInc;
end;

Pre__DualDescriptionLRS:=function(EXT, ListOption)
  local FileExt, FileLog, FileIneNude, output, LPFAC, eOpt;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Project.ext");
  FileLog:=Filename(POLYHEDRAL_tmpdir,"Project.log");
  FileIneNude:=Filename(POLYHEDRAL_tmpdir,"Project.ine.Nude");
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", Length(EXT[1]), " integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  for eOpt in ListOption
  do
    AppendTo(output, eOpt[1], " ", eOpt[2], "\n");
  od;
  CloseStream(output);
  Exec(FileGLRS, " ", FileExt, " | grep -v '*' > ", FileLog);
  Exec(FileNudifyLRS, " ", FileLog, " > ", FileIneNude);
  LPFAC:=ReadVectorFile(FileIneNude);
  RemoveFile(FileExt);
  RemoveFile(FileLog);
  RemoveFile(FileIneNude);
  return LPFAC;
end;

SomeFacets:=function(EXT, nb)
  local KeyOpt;
  KeyOpt:=["maxoutput", nb];
  return Pre__DualDescriptionLRS(EXT, [KeyOpt]);
end;



ListFlagOrbitSigned:=function(GroupExt, EXT, FAC, GramMat)
  local O, ListOrbitPrec, i, dimension, ListOrbitNew, eOrbPrec, eface, WorkFlag, FlagNew, TheSign, FlagCan;
  if TestConicness(FAC)=true then
    dimension:=Length(FAC[1])-2;
  else
    dimension:=Length(FAC[1])-1;
  fi;
  O:=Orbits(GroupExt, [1..Length(EXT)]);
  ListOrbitPrec:=List(O, x->rec(TheFlag:=[  [x[1]]  ], TheSign:=1));
  Print("For i=1  one finds ", Length(ListOrbitPrec), " orbits\n");
  for i in [2..dimension]
  do
    ListOrbitNew:=[];
    for eOrbPrec in ListOrbitPrec
    do
      WorkFlag:=eOrbPrec.TheFlag;
      for eface in SPAN_face(WorkFlag[i-1], EXT, FAC)
      do
        FlagNew:=Concatenation(WorkFlag, [eface]);
        TheSign:=eOrbPrec.Sign;
        FlagCan:=CanonicalizationFlagAction(FlagNew, GroupExt);
        Add(ListOrbitNew, rec(TheFlag:=FlagCan, TheSign:=TheSign));
      od;
    od;
    ListOrbitPrec:=Set(ListOrbitNew);
    Print("For i=", i, "  one finds ", Length(ListOrbitPrec), " orbits\n");
  od;
  return ListOrbitNew;
end;


#
#
# Polytope is the list of vertices
# SubGraph is an affine basis of Polytope
# ListHypermetrics is the list of hypermetrics incident to the distance
# vector associated to SubGraph
ExtendSubGraph:=function(Polytope, SubGraph, ListHypermetrics)
  local L, eInc, S, iC;
  L:=ShallowCopy(SubGraph);
  for eInc in ListHypermetrics
  do
    S:=0;
    for iC in [1..Length(eInc)]
    do
      S:=S+eInc[iC]*Polytope[SubGraph[iC]];
    od;
    Add(L, Position(Polytope,S));
  od;
  Sort(L);
  return L;
end;

FindDelaunayPolytope:=function(GramMat)
  local n, FuncInequality, ListVectors, ListInequalities, VE, RandomVec, Optim, ListIncd, CP, Vcent, reply, i, u;
  n:=Length(GramMat);
  FuncInequality:=function(eVec)
    local IneqL, Sum, i, j;
    IneqL:=[];
    Sum:=0;
    for i in [1..n]
    do
      for j in [1..n]
      do
        Sum:=Sum+eVec[i]*eVec[j]*GramMat[i][j];
      od;
    od;
    Add(IneqL, Sum);
    for i in [1..n]
    do
      Sum:=0;
      for j in [1..n]
      do
        Sum:=Sum+GramMat[i][j]*eVec[j];
      od;
      Add(IneqL, -2*Sum);
    od;
    return IneqL;
  end;
  ListVectors:=[];
  ListInequalities:=[];
  VE:=NullZero(n);
  for i in [1..n]
  do
    VE[i]:=1;
    Add(ListVectors, ShallowCopy(VE));
    Add(ListInequalities, FuncInequality(VE));
    VE[i]:=-1;
    Add(ListVectors, ShallowCopy(VE));
    Add(ListInequalities, FuncInequality(VE));
    VE[i]:=0;
  od;
  RandomVec:=[0];
  for i in [1..n]
  do
    Add(RandomVec, Random([-20..20]));
  od;
  while(true)
  do
    Optim:=LinearProgrammingPolytopeVersion(ListInequalities, RandomVec);
#    Print("Optim=", Optim, "\n");
#    Print("Bonjour\n");
    ListIncd:=[];
    VE:=[1];
    for i in [1..n]
    do
      Add(VE, 0);
    od;
    Add(ListIncd, VE);
    for u in [1..Length(ListVectors)]
    do
      if Optim*ListInequalities[u]=0 then
        VE:=[1];
        Append(VE, ListVectors[u]);
        Add(ListIncd, VE);
      fi;
    od;
    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, ListIncd);
    Vcent:=[];
    for i in [1..n]
    do
      Add(Vcent, CP.Center[i+1]);
    od;
#    Print("Launching CVP computing\n");
    reply:=MinimalCVP(GramMat, Vcent);
#    Print("CVP computing finished\n");
    if reply[2]=CP.SquareRadius then
      break;
    else
      if Position(ListVectors, reply[1])<>fail then
        ListVectors:=NullMat(5);
      fi;
      Add(ListVectors, reply[1]);
      Add(ListInequalities, FuncInequality(reply[1]));
#      Print("Adding ", reply, " to the list\n");
    fi;
  od;
  return ListIncd;
end;


LinearProgrammingConeVersion:=function(InequalitySet, ToBeMinimized)
  local FileIne, FileLps, FileError, FileGap, FileDdl, FileLog, outputCdd, input, eLine, A;
  FileIne:=Filename(POLYHEDRAL_tmpdir, "LP.ine");
  FileLps:=Filename(POLYHEDRAL_tmpdir, "LP.lps");
  FileError:=Filename(POLYHEDRAL_tmpdir, "LP.error");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "LP.gap");
  FileDdl:=Filename(POLYHEDRAL_tmpdir, "LP.ddl");
  FileLog:=Filename(POLYHEDRAL_tmpdir, "LP.log");
  RemoveFileIfExist(FileIne);
  RemoveFileIfExist(FileLps);
  RemoveFileIfExist(FileError);
  RemoveFileIfExist(FileGap);
  RemoveFileIfExist(FileDdl);
  RemoveFileIfExist(FileLog);
  if Length(InequalitySet[1])<>Length(ToBeMinimized) then
    Print("Incoherence in dimensions, please be careful\n");
    Print(NullMat(5));
  fi;
  outputCdd:=OutputTextFile(FileIne, true);;
  AppendTo(outputCdd, "H-representation\n");
  AppendTo(outputCdd, "begin\n");
  AppendTo(outputCdd, " ", Length(InequalitySet), " ", Length(ToBeMinimized)+1, " integer\n");
  for eLine in InequalitySet
  do
    AppendTo(outputCdd, " 0");
    WriteVector(outputCdd, eLine);
  od;
  #
  AppendTo(outputCdd, "end\n");
  AppendTo(outputCdd, "minimize\n");
  #
  AppendTo(outputCdd, " 0");
  WriteVector(outputCdd, ToBeMinimized);
  CloseStream(outputCdd);

  Exec(FileTestlp2, " ", FileIne, " 2> ", FileError, " > ", FileLog);
#  Exec(FileCddrGmp, " ", FileIne, " 2> ", FileError, " > ", FileLog);
  Exec(Filelpcddcleaner, " < ", FileLog, " > ", FileGap);
#  Exec(Filelpcddcleaner, " < ", FileLps, " > ", FileGap);
#  input:=InputTextFile(FileGap);
#  if IsEmptyFile(FileError)=false then
#    Print("Nonempty error file in Linear Programming cone version\n");
#    Print(NullMat(5));
#  fi;
#  A:=ReadAll(input);
#  CloseStream(input);
  A:=ReadAsFunction(FileGap)();
#  Print(NullMat(5));
  RemoveFileIfExist(FileIne);
  RemoveFileIfExist(FileLps);
  RemoveFileIfExist(FileError);
  RemoveFileIfExist(FileGap);
  RemoveFileIfExist(FileDdl);
  RemoveFileIfExist(FileLog);
  return A;
end;



LinearProgrammingPolytopeVersion:=function(InequalitySet, ToBeMinimized)
  local FileIne, FileLps, FileGap, FileDdl, FileLog, outputCdd, eLine, TheResult, eRed;
  FileIne:=Filename(POLYHEDRAL_tmpdir, "LP.ine");
  FileLps:=Filename(POLYHEDRAL_tmpdir, "LP.lps");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "LP.gap");
  FileDdl:=Filename(POLYHEDRAL_tmpdir, "LP.ddl");
  FileLog:=Filename(POLYHEDRAL_tmpdir, "LP.log");
  outputCdd:=OutputTextFile(FileIne, true);;
  AppendTo(outputCdd, "H-representation\n");
  AppendTo(outputCdd, "begin\n");
  AppendTo(outputCdd, " ", Length(InequalitySet), " ", Length(ToBeMinimized), " integer\n");
  for eLine in InequalitySet
  do
    eRed:=RemoveFraction(eLine);
    WriteVector(outputCdd, eRed);
  od;
  #
  AppendTo(outputCdd, "end\n");
  AppendTo(outputCdd, "minimize\n");
  #
  eRed:=RemoveFraction(ToBeMinimized);
  WriteVector(outputCdd, eRed);
  CloseStream(outputCdd);
  Exec(FileCddrGmp, " ", FileIne, " > ", FileLog);
  Exec(Filelpcddcleaner, " ", FileLps, " > ", FileGap);
#  Exec(FilelpcddcleanerPol, " ", FileLps, " > ", FileGap);
#  Print(NullMat(5));
  TheResult:=ReadAsFunction(FileGap)();
  RemoveFile(FileIne);
  RemoveFile(FileLps);
  RemoveFile(FileGap);
  RemoveFile(FileDdl);
  RemoveFile(FileLog);
  return TheResult;
end;


#
#
# we consider here a fully recursive Adjacency decomposition
# method.
GroupToPerl:=function(FileName, GRP, nbelt)
  local output, eElt, eImg, i;
  output:=OutputTextFile(FileName, true);;
  for eElt in GRP
  do
    eImg:=OnTuples([1..nbelt], eElt);
    for i in [1..nbelt]
    do
      AppendTo(output, " ", eImg[i]);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;




#
# IMPORTANT FACT:
# this procedure does not work, since it is possible
# that by taking all possible simplices, we got
# 
#FindDelaunayPolytope:=function(GramMat)
#  local n, i, j, V, VSet, ListVert, CP, Vcent, reply, SelectedVertex, nb, NewMat, eV, CPprev, MinimalRadius, dist, ListRadius;
#  n:=Length(GramMat);
#  VSet:=[];
#  for i in [1..n+1]
#  do
#    V:=[1];
#    for j in [1..n]
#    do
#      if j<>i then
#        Add(V, 0);
#      else
#        Add(V, 1);
#      fi;
#    od;
#    AddSet(VSet, V);
#  od;
#  while(true)
#  do
#    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, VSet);
#    Print("Rsquare=", CP.SquareRadius, "\n");
#    Vcent:=[];
#    for i in [1..n]
#    do
#      Add(Vcent, CP.Center[i+1]);
#    od;
#    reply:=DetectorMinimalCVP(GramMat, Vcent, CP.SquareRadius);
#    if reply=true then
#      break;
#    else
#      dist:=0;
#      for i in [1..n]
#      do
#        for j in [1..n]
#        do
#          dist:=dist+(reply[i]-Vcent[i])*GramMat[i][j]*(reply[j]-Vcent[j]);
#        od;
#      od;
#      Print("dist-CP.squareRadius=", dist-CP.SquareRadius, "\n");
#      if dist>=CP.SquareRadius then
#        Print("Error\n");
#        CP:=NullMat(5);
#      fi;
#      SelectedVertex:=[1];
#      for i in [1..n]
#      do
#        Add(SelectedVertex, reply[i]);
#      od;
#      MinimalRadius:=CP.SquareRadius; # hook
#      ListRadius:=[];
#      for nb in [1..n+1]
#      do
#        NewMat:=Union(Difference(VSet, [VSet[nb]]), [SelectedVertex]);
#        if RankMat(NewMat)=n+1 then
#          CPprev:=CenterRadiusDelaunayPolytopeGeneral(GramMat, NewMat);
#          Add(ListRadius, CPprev.SquareRadius);
#          if CPprev.SquareRadius < MinimalRadius then
#            MinimalRadius:=CPprev.SquareRadius;
#            VSet:=ShallowCopy(NewMat);
#            Print("Assignation done\n");
#          fi;
#        fi;
#      od;
#      if MinimalRadius=CP.SquareRadius then
#        ListRadius:=NullMat(5);
#      fi;
#      Print("\n");
#    fi;
#  od;
#  ListVert:=[];
#  for eV in EqualityCVP(GramMat, Vcent, CP.SquareRadius)
#  do
#    V:=[1];
#    for i in [1..n]
#    do
#      Add(V, eV[i]);
#    od;
#    Add(ListVert, V);
#  od;
#  return ListVert;
#end;






# after doing LLL, one has 
# U*Gram*TransposedMat(U) = newGram;
CommonCVP:=function(FileDat, Gram, V, rsquare)
  local n, Den, iCol, iLin, output, res, U, newV, newGram, LineMat, CommonDenominator, newrsquare;
  n:=Length(V);
  if IsPositiveDefiniteSymmetricMatrix(Gram)=false then
    U:=[];
    for iCol in [1..n]
    do
      LineMat:=[];
      for iLin in [1..n]
      do
        if iCol=iLin then
          Add(LineMat, 1);
        else
          Add(LineMat, 0);
        fi;
      od;
      Add(U, LineMat);
    od;
    newGram:=Gram;
    newV:=V;
  else
    res:=LLLReducedGramMat(Gram);
    U:=res.transformation;
    newGram:=res.remainder;
    newV:=TransposedMat(Inverse(U))*V;
  fi;
  CommonDenominator:=1;
  for iCol in [1..n]
  do
    for iLin in [1..n]
    do
      CommonDenominator:=Lcm(CommonDenominator, DenominatorRat(newGram[iCol][iLin]));
    od;
  od;
  Den:=1;
  for iCol in [1..n]
  do
    Den:=LcmInt(Den, DenominatorRat(newV[iCol]));
  od;
  # 
  # creation of the file
  #
  newrsquare:=CommonDenominator*rsquare;
  output:=OutputTextFile(FileDat, true);;
  AppendTo(output, " ", n);
  AppendTo(output, " ", Den);
  AppendTo(output, " ", NumeratorRat(newrsquare));
  AppendTo(output, " ", DenominatorRat(newrsquare), "\n");
  #
  for iCol in [1..n]
  do
    AppendTo(output," ", newV[iCol]*Den);
  od;
  AppendTo(output,"\n");
  #
  for iCol in [1..n]
  do
    for iLin in [1..n]
    do
      AppendTo(output, " ", CommonDenominator*newGram[iCol][iLin]);
    od;
    AppendTo(output,"\n");
  od;
  CloseStream(output);
  return U;
end;






DetectorCVP:=function(Gram, V, rsquare)
  local FileDat, FileLog, FileLog2, FileReply, U, res;
  FileDat:=Filename(POLYHEDRAL_tmpdir, "CVP");
  FileLog:=Filename(POLYHEDRAL_tmpdir, "CVP.log");
  FileLog2:=Filename(POLYHEDRAL_tmpdir, "CVP.log2");
  FileReply:=Filename(POLYHEDRAL_tmpdir, "CVP.reply");

  U:=CommonCVP(FileDat, Gram, V, rsquare);
  Exec(FileDetector, " ", FileDat, " > ", FileLog2);
  res:=ReadAsFunction(FileReply)();
  RemoveFile(FileDat);
  RemoveFile(FileLog);
  RemoveFile(FileLog2);
  RemoveFile(FileReply);
  if res=true then
    return true;
  else
    return TransposedMat(U)*res;
  fi;
end;


DetectorCVP:=function(GramMat, V, rsquare)
  local LES;
  LES:=CVPVallentinProgram(GramMat, V);
  if LES.TheNorm<rsquare then
    return LES.ListVect[1];
  else
    return true;
  fi;
end;


EqualityCVP:=function(GramMat, V, rsquare)
  local LES;
  LES:=CVPVallentinProgram(GramMat, V);
  return LES.ListVect;
end;







FractionalPartInteger:=function(eFrac)
  local p, V1, V2;
  p:=NumeratorRat(eFrac) mod DenominatorRat(eFrac);
  V1:=p/DenominatorRat(eFrac);
  V2:=V1-1;
  if AbsInt(V1)>AbsInt(V2) then
    return V2;
  else
    return V1;
  fi;
end;



MinimalCVP:=function(GramMat, V)
  local FileDat, FileLog, FileLog2, FileReply, ResultSearch, U, res, VE, Sum, i, j, n, newV, newGram, Rsquare, Approx, Fre;
  FileDat:=Filename(POLYHEDRAL_tmpdir, "CVP");
  FileLog:=Filename(POLYHEDRAL_tmpdir, "CVP.log");
  FileLog2:=Filename(POLYHEDRAL_tmpdir, "CVP.log2");
  FileReply:=Filename(POLYHEDRAL_tmpdir, "CVP.reply");
  #
  n:=Length(GramMat);
  res:=LLLReducedGramMat(GramMat);
  U:=res.transformation;
  newGram:=res.remainder;
  newV:=TransposedMat(Inverse(U))*V;
  #
  VE:=[];
  Approx:=[];
  for i in [1..n]
  do
    Fre:=FractionalPartInteger(newV[i]);
    Add(VE, Fre);
    Add(Approx, newV[i]-Fre);
  od;
  Rsquare:=0;
  for i in [1..n]
  do
    for j in [1..n]
    do
      Rsquare:=Rsquare+VE[i]*VE[j]*newGram[i][j];
    od;
  od;
  U:=CommonCVP(FileDat, GramMat, V, Rsquare);
  Exec(FileDetectorMinimal, " ", FileDat, " > ", FileLog2);
  res:=ReadAsFunction(FileReply)();
  RemoveFile(FileDat);
  RemoveFile(FileLog);
  RemoveFile(FileLog2);
  RemoveFile(FileReply);
  if res=true then
    return [TransposedMat(U)*Approx, Rsquare];
  fi;
  ResultSearch:=TransposedMat(U)*res;
  Sum:=0;
  for i in [1..n]
  do
    for j in [1..n]
    do
      Sum:=Sum+ResultSearch[i]*ResultSearch[j]*GramMat[i][j];
    od;
  od;
  return [ResultSearch, Sum];
end;







EqualityCVP:=function(Gram, V, rsquare)
  local FileDat, FileLog, FileLog2, FileVector, ResultSearch, U, Xp;
  FileDat:=Filename(POLYHEDRAL_tmpdir, "CVP");
  FileLog:=Filename(POLYHEDRAL_tmpdir, "CVP.log");
  FileLog2:=Filename(POLYHEDRAL_tmpdir, "CVP.log2");
  FileVector:=Filename(POLYHEDRAL_tmpdir, "CVP.vector");

  U:=CommonCVP(FileDat, Gram, V, rsquare);
  Exec(FileEquality, " ", FileDat, " > ", FileLog2);
  ResultSearch:=[];
  for Xp in ReadVectorFile(FileVector)
  do
    Add(ResultSearch, TransposedMat(U)*Xp);
  od;
  RemoveFile(FileDat);
  RemoveFile(FileLog);
  RemoveFile(FileLog2);
  RemoveFile(FileVector);
  return ResultSearch;
end;









#
#
# From a raw list of orbit representatives, create a database
CreateDatabase:=function(FAC, ListOrb, ListGraph)
  local DatabaseWORK, iOrb;
  DatabaseWORK:=[];
  for iOrb in [1..Length(ListOrb)]
  do
    DatabaseWORK[iOrb]:=rec(Vector:=ListOrb[iOrb], 
            Incidence:=Length(ListIncidentFacet(ListOrb[iOrb], FAC)), 
            Status:="NO", 
            Graph:=ListGraph[iOrb]);
  od;
  return DatabaseWORK;
end;


ListAdjacent:=function(EXT, TheFacet)
  local RPLift, eSub, ListAdj, OneInc, eFac, eInc, fInc;
  OneInc:=Filtered([1..Length(EXT)], x->TheFacet*EXT[x]=0);
  RPLift:=__ProjectionLiftingFramework(EXT, OneInc);
  eSub:=__ProjectionFrame(EXT{OneInc});
  ListAdj:=[];
  for eFac in DualDescription(List(EXT{OneInc}, x->x{eSub}))
  do
    eInc:=Filtered(OneInc, x->eFac*EXT[x]{eSub} =0);
    fInc:=RPLift.FuncLift(eInc);
    Add(ListAdj, __FindFacetInequality(EXT, fInc));
  od;
  return ListAdj;
end;






#
#
# this is the general form of the Adjacency Decomposition Method
# assume the cone is defined by facets, and we give as input a 
# list of orbits of extreme rays presented in the form 
# List[iOrb]=[Repr, Incidence, treated(YES/NO), Size, RepresentationMatrix, Adjacency]
# MaxRuns is the maximal numbers of iterations allowed
# A->FuncInvariant(A) is a function (easy to compute) such that
#   A = B (mod Group)  ==> FuncInvariant(A)=FuncInvariant(B)
# A->FuncGraph(A) is a function such that
#   A = B (mod Group)  <==> FuncGraph(A) isomorphic to FuncGraph(B)
# Perhaps we should add an option to use canonical forms? (much like in the 
# perl program)
AdjacencyDecompositionMethod:=function(FAC, InitialDatabase, MaxRuns, MaxIncidence, FuncInvariant, FuncGraph)
  local DatabaseWORK, Incidence, UpdateDatabase, iteration, test, iOrb, INVA, nbTreated;
  DatabaseWORK:=ShallowCopy(InitialDatabase);
  nbTreated:=0;
  INVA:=[];
  for iOrb in [1..Length(DatabaseWORK)]
  do
    Add(INVA, FuncInvariant(DatabaseWORK[iOrb].Vector) );
    if DatabaseWORK[iOrb].Status="YES" then
      nbTreated:=nbTreated+1;
    fi;
  od;
  UpdateDatabase:=function(iO)
    local ELTFOUND, ORBFOUND, MatrixElt, SSIinv, SSIgraph, pos, u, nbOrb, i, VECT, nbNew, nbOld;
    Print("Nr. Treated=", nbTreated, "\n");
    ELTFOUND:=RemoveFractionList(ListAdjacent(FAC, DatabaseWORK[iO].Vector));
    DatabaseWORK[iO].Status:="YES";
    DatabaseWORK[iO].Adjacency:=Length(ELTFOUND);
    nbTreated:=nbTreated+1;
    Print("Orbit", iO, " has incidence ", DatabaseWORK[iO].Incidence," and adjacency ", DatabaseWORK[iO].Adjacency, "\n");
    SSIinv:=[];
    SSIgraph:=[];
    for i in [1..Length(ELTFOUND)]
    do
      SSIinv[i]:=FuncInvariant(ELTFOUND[i]);
      SSIgraph[i]:=FuncGraph(ELTFOUND[i]);
    od;
    ORBFOUND:=RemoveByIsomorphy(SSIgraph, SSIinv, IsIsomorphicGraph);
    MatrixElt:=[];
    nbNew:=0;
    nbOld:=0;
    for iOrb in [1..Length(ORBFOUND.IsomorphyClass)]
    do
      nbOrb:=1;
      pos:=0;
      while(nbOrb<=Length(DatabaseWORK))
      do
	if INVA[nbOrb]=ORBFOUND.ListInvariant[iOrb] then
	  if IsIsomorphicGraph(ORBFOUND.NonIsomorphRepresentant[iOrb], DatabaseWORK[nbOrb].Graph)=true then
	    pos:=nbOrb;
	    break;
	  fi;
	fi;
	nbOrb:=nbOrb+1;
      od;
      if pos=0 then
        nbNew:=nbNew+1;
	u:=Length(DatabaseWORK)+1; # find a new orbit!
	Add(MatrixElt, [u, Length(ORBFOUND.IsomorphyClass[iOrb])]);
        VECT:=ELTFOUND[ORBFOUND.ListSample[iOrb]];
        DatabaseWORK[u]:=rec(Vector:=VECT, 
           Incidence:=Length(ListIncidentFacet(VECT, FAC)), 
           Status:="NO", 
           Graph:=ORBFOUND.NonIsomorphRepresentant[iOrb]);
	INVA[u]:=ORBFOUND.ListInvariant[iOrb];
	Print("Orbit Nr. ", u, "  Incidence=", DatabaseWORK[u].Incidence, "\n");
      else
	Add(MatrixElt, [pos, Length(ORBFOUND.IsomorphyClass[iOrb])]);
        nbOld:=nbOld+1;
      fi;
    od;
    DatabaseWORK[iO].RepresentationMatrix:=MatrixElt;
    Print(Length(ORBFOUND.IsomorphyClass), " orbit", nbNew, " new and ", nbOld, " old\n");
  end;

  # the iteration looping
  iteration:=1;
  Incidence:=1;
  while((iteration<=MaxRuns) and (Incidence<=MaxIncidence))
  do
    for iOrb in [1..Length(DatabaseWORK)]
    do
      if DatabaseWORK[iOrb].Status="NO" and DatabaseWORK[iOrb].Incidence=Incidence then
	UpdateDatabase(iOrb);
	SaveDataToFile("DatabaseSave", DatabaseWORK);
        iteration:=iteration+1;
	Incidence:=1;
      fi;
    od;
    test:=1;
    for iOrb in [1..Length(DatabaseWORK)]
    do
      if DatabaseWORK[iOrb].Status="NO" and DatabaseWORK[iOrb].Incidence<=Incidence then
	test:=0;
      fi;
    od;
    if test=1 then
      Incidence:=Incidence+1;
    fi;
    test:=1;
    for iOrb in [1..Length(DatabaseWORK)]
    do
      if DatabaseWORK[iOrb].Status="NO" then
	test:=0;
      fi;
    od;
    if test=1 then
	break;
    fi;
  od;
  return DatabaseWORK;
end;




EnumerateOrbitFacets:=function(EXT, PermGRP)
  local FuncListIncidence, eFac, ListOrbit, FuncInsert, nbUndone, nbOrb, iOrb, ListFAC;
  FuncListIncidence:=function(eFac)
    local ELI, iExt;
    ELI:=[];
    for iExt in [1..Length(EXT)]
    do
      if EXT[iExt]*eFac=0 then
        Add(ELI, iExt);
      fi;
    od;
    return ELI;
  end;

  eFac:=RandomVertex(EXT);
  ListOrbit:=[rec(eFac:=eFac, Incd:=FuncListIncidence(eFac), Status:="NO")];
  FuncInsert:=function(eFac)
    local TheIncd, ORB, i;
    TheIncd:=FuncListIncidence(eFac);
    ORB:=Set(Orbit(PermGRP, TheIncd, OnSets));
    for iOrb in [1..Length(ListOrbit)]
    do
      if ListOrbit[iOrb].Incd in ORB then
        return;
      fi;
    od;
    Add(ListOrbit, rec(eFac:=eFac, Incd:=TheIncd, Status:="NO"));
  end;
  while(true)
  do
    nbUndone:=0;
    nbOrb:=Length(ListOrbit);
    for iOrb in [1..nbOrb]
    do
      if ListOrbit[iOrb].Status="NO" then
        nbUndone:=nbUndone+1;
        for eFac in ListAdjacent(EXT, ListOrbit[iOrb].eFac)
        do
          FuncInsert(eFac);
        od;
        ListOrbit[iOrb].Status:="YES";
      fi;
    od;
    if nbUndone=0 then
      break;
    fi;
  od;
  ListFAC:=[];
  for iOrb in [1..Length(ListOrbit)]
  do
    Add(ListFAC, ListOrbit[iOrb].eFac);
  od;
  return ListFAC;
end;

DelaunayDecomposition:=function(GramMat)
  local DistMat, DistVect, EXT, ListDelaunay, FuncInsert, nbNO, iDelaunay, FAC, iFac, eFac, RES, MaxSquareRadius, CP, SQR;
  DistMat:=GramMatrixToDistanceMatrix(GramMat);
  DistVect:=DistanceMatrixToDistanceVector(DistMat);
  EXT:=FindDelaunayPolytope(GramMat);
  Print("Find an initial Delaunay with ", Length(EXT), " vertices\n");
  ListDelaunay:=[rec(EXT:=EXT, Status:="NO", Linv:=ComputeInvariant(EXT, DistVect))];

  FuncInsert:=function(EXT)
    local TheInv, iDelaunay;
    TheInv:=ComputeInvariant(EXT, DistVect);
    for iDelaunay in [1..Length(ListDelaunay)]
    do
      if TheInv=ListDelaunay[iDelaunay].Linv then
        if IsIsomorphicExtremeDelaunay(ListDelaunay[iDelaunay].EXT, DistVect, EXT, DistVect)=true then
          return;
        fi;
      fi;
    od;
    Add(ListDelaunay, rec(EXT:=EXT, Status:="NO", Linv:=TheInv));
    Print("Find a new delaunay with ", Length(EXT), " vertices\n");
  end;
  #
  while(true)
  do
    nbNO:=0;
    for iDelaunay in [1..Length(ListDelaunay)]
    do
      if ListDelaunay[iDelaunay].Status="NO" then
        nbNO:=nbNO+1;
        ListDelaunay[iDelaunay].Status:="YES";
        EXT:=ListDelaunay[iDelaunay].EXT;
        FAC:=DualDescription(EXT);
        Print("Find ", Length(FAC), " facets for Delaunay ", iDelaunay, "\n");
        for iFac in [1..Length(FAC)]
        do
          eFac:=FAC[iFac];
          Print("Analysing facet ", iFac, " : ", eFac, "\n");
          RES:=FindAdjacentDelaunayPolytope(GramMat, EXT, eFac);
          FuncInsert(RES);
        od;
      fi;
    od;
    if nbNO=0 then
      break;
    fi;
  od;
  #
  MaxSquareRadius:=0;
  for iDelaunay in [1..Length(ListDelaunay)]
  do
    EXT:=ListDelaunay[iDelaunay].EXT;
    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
    SQR:=CP.SquareRadius;
    if SQR>MaxSquareRadius then
      MaxSquareRadius:=SQR;
    fi;
  od;
  return rec(ListDelaunay:=ListDelaunay, MaxSquareRadius:=MaxSquareRadius);
end;


OrbitGroupFormalismOnlySets:=function(nbelt, GroupExt, ListOrbit)
  local Odisc, O, FuncInvariant, FuncInsert;
  Odisc:=[];
  O:=Orbits(GroupExt, Combinations([1..nbelt], 1), OnSets);
  Append(Odisc, O);
  if Length(Odisc)<10 then
    O:=Orbits(GroupExt, Combinations([1..nbelt], 2), OnSets);
    Append(Odisc, O);
  fi;

  FuncInvariant:=function(ListInc)
    local eInv, eO, nb, eSet;
    eInv:=[];
    for eO in Odisc
    do
      nb:=0;
      for eSet in eO
      do
        if IsSubset(ListInc, eSet)=true then
          nb:=nb+1;
        fi;
      od;
      Add(eInv, nb);
    od;
    return eInv;
  end;
  

  FuncInsert:=function(Linc)
    local Stab, iOrb, TheInv, TheStab, iExt;
    TheInv:=FuncInvariant(Linc);
    for iOrb in [1..Length(ListOrbit)]
    do
      if TheInv=ListOrbit[iOrb].TheInv then
        if RepresentativeAction(GroupExt, Linc, ListOrbit[iOrb].Inc, OnSets)<>fail then
          return;
        fi;
      fi;
    od;
    Add(ListOrbit, rec(Inc:=Linc, TheInv:=TheInv));
  end;
  return rec(FuncInsert:=FuncInsert);
end;



ListOrbitRidges:=function(EXT, OrbitFacet, GroupExt, idxFacet)
  local rnk, ListOfIncidence, eInc, iExt, eExt, ListRidge, StabFacet, ORB, facetInc, ListMap, iElt, NewListGens, eGen, eList, eF, fF, RPL, iOrb, fInc, gInc, RNK, RevgInc, ReducedRevgInc, NewStab;
  rnk:=RankMat(EXT);
  ListOfIncidence:=[];
  for iOrb in [1..Length(OrbitFacet)]
  do
    eInc:=[];
    for iExt in [1..Length(EXT)]
    do
      eExt:=EXT[iExt];
      if eExt*OrbitFacet[iOrb]=0 then
        Add(eInc, iExt);
      fi;
    od;
    Add(ListOfIncidence, eInc);
  od;
  StabFacet:=Stabilizer(GroupExt, ListOfIncidence[idxFacet], OnSets);
  ORB:=Orbit(GroupExt, ListOfIncidence[idxFacet], OnSets);
  facetInc:=ListOfIncidence[idxFacet];
  ListMap:=List(ORB, x->RepresentativeAction(GroupExt, x, facetInc, OnSets));
  NewListGens:=[];
  for eGen in GeneratorsOfGroup(StabFacet)
  do
    eList:=[];
    for eF in facetInc
    do
      fF:=OnPoints(eF, eGen);
      Add(eList, Position(facetInc, fF));
    od;
    Add(NewListGens, PermList(eList));
  od;
  NewStab:=Group(NewListGens);


  Print("facetInc=", facetInc, "\n");
  ListRidge:=[];
  RPL:=OrbitGroupFormalismOnlySets(Length(facetInc), NewStab, ListRidge);
  for iOrb in [1..Length(OrbitFacet)]
  do
    Print("iOrb=", iOrb, "\n");
    eInc:=ListOfIncidence[iOrb];
    for iElt in [1..Length(ORB)]
    do
      fInc:=ORB[iElt];
      gInc:=Intersection(eInc, fInc);
      RNK:=RankMat(EXT{gInc});
      if RNK=rnk-2 then
        RevgInc:=OnSets(gInc, ListMap[iElt]^(-1));
        ReducedRevgInc:=List(RevgInc, x->Position(facetInc, x));
        Print("gInc=", gInc, "\n");
        Print("RevgInc=", RevgInc, "\n");
        Print("ReducedRevgInc=", ReducedRevgInc, "\n");
        RPL.FuncInsert(ReducedRevgInc);
      fi;
    od;
  od;
  return ListRidge;
end;


OutputToVallentinPackingCovering:=function(output, OneLtype, eCase)
  local n, eDelaunay, EXTred, iEXT, eEXT, i, iMat, eMat, iRow, iCol, FAC1, EXT2, FAC2, eFac, eList, ePerm, TheAction, GRPmat, ListVector, EXT, DDA, iExt, jExt, VE, ListOrbit, U, iU;
  n:=Length(eCase.Basis[1]);
  eList:=[n+1];
  for i in [2..n+1]
  do
    Add(eList, i-1);
  od;
  ePerm:=PermList(eList);
  #
  AppendTo(output, "list defining vectors\n");
  TheAction:=function(eVect, eMat)
    return eVect*eMat;
  end;
  GRPmat:=Group(eCase.ListGen);
  ListVector:=[];
  for eDelaunay in OneLtype
  do
    EXT:=eDelaunay.EXT;
    DDA:=DualDescriptionAdjacencies(EXT);
    for iExt in [1..Length(EXT)-1]
    do
      for jExt in Adjacency(DDA.SkeletonGraph, iExt)
      do
        if jExt>iExt then
          VE:=EXT[jExt]-EXT[iExt];
          Add(ListVector, VE{[2..n+1]});
        fi;
      od;
    od;
  od;
  ListVector:=Set(ListVector);
  ListOrbit:=[];
  while(Length(ListVector)>0)
  do
    U:=Orbit(GRPmat, ListVector[1], TheAction);
    ListVector:=Difference(ListVector, U);
    Add(ListOrbit, U[1]);
  od;
  for iU in [1..Length(U)]
  do
    WriteVector(output, U[iU]);
  od;
  #
  AppendTo(output, "list defining simplices\n");
  for eDelaunay in OneLtype
  do
    EXTred:=RowReduction(eDelaunay.EXT, n+1);
    for iEXT in [1..Length(EXTred)]
    do
      eEXT:=Permuted(EXTred[iEXT], ePerm);
      for i in [1..n+1]
      do
        if i>1 then
          AppendTo(output, " ", eEXT[i]);
        else
          AppendTo(output, eEXT[i]);
        fi;
      od;
      if iEXT<Length(EXTred) then
        AppendTo(output, ",");
      fi;
    od;
    AppendTo(output, "\n");
  od;
  #
  AppendTo(output, "list defining matrices\n");
  for iMat in [1..Length(eCase.Basis)]
  do
    eMat:=eCase.Basis[iMat];
    for iRow in [1..n]
    do
      for iCol in [1..iRow]
      do
        AppendTo(output, " ", eMat[iRow][iCol]);
      od;
    od;
    AppendTo(output, "\n");
  od;
  #
  AppendTo(output, "list defining inequalities\n");
  FAC1:=WriteFaceInequalities(OneLtype, eCase);
  EXT2:=DualDescription(FAC1.ListInequalities);
  FAC2:=EliminationByRedundancyCone(FAC1.ListInequalities, EXT2);
  for eFac in FAC2
  do
    WriteVector(output, eFac);
  od;
end;



OrbitGroupFormalism:=function(TheOperatingSet, GroupExt, ListOrbit, MaxSize)
  local Odisc, O, FuncInvariant, FuncInsert, iSize, iOrb, Maxi, Posi;
  Odisc:=[];
  for iSize in [1..3]
  do
    if Length(Odisc)<10 and iSize<=MaxSize then
      O:=Orbits(GroupExt, Combinations(TheOperatingSet, iSize), OnSets);
      Maxi:=0;
      for iOrb in [1..Length(O)]
      do
        if Length(O[iOrb])>Maxi then
          Maxi:=Length(O[iOrb]);
          Posi:=iOrb;
        fi;
      od;
      Append(Odisc, O{Difference([1..Length(O)], [Posi])});
    fi;
  od;
  FuncInvariant:=function(ListInc)
    local eInv, eO, nb, eSet;
    eInv:=[Length(ListInc)];
    for eO in Odisc
    do
      nb:=0;
      for eSet in eO
      do
        if IsSubset(ListInc, eSet)=true then
          nb:=nb+1;
        fi;
      od;
      Add(eInv, nb);
    od;
    return eInv;
  end;
  FuncInsert:=function(Linc)
    local Stab, iOrb, TheInv, TheStab, iExt;
    TheInv:=FuncInvariant(Linc);
    for iOrb in [1..Length(ListOrbit)]
    do
      if TheInv=ListOrbit[iOrb].TheInv then
        if RepresentativeAction(GroupExt, Linc, ListOrbit[iOrb].Inc, OnSets)<>fail then
          return;
        fi;
      fi;
    od;
    Stab:=Stabilizer(GroupExt, Linc, OnSets);
    Add(ListOrbit, rec(Inc:=Linc, TheInv:=TheInv, Status:="NO", OrdStab:=Order(Stab)));
  end;
  return rec(FuncInsert:=FuncInsert, FuncInvariant:=FuncInvariant);
end;





FindFacetRepartitionningComplex:=function(ListOrbitDelaunay, InteriorElement, SymmetryGroupRepartitionning, RepartInfo)
  local ListOrbitFacet, n, ListCenter, eRec, V, Gra, eMat, iCent, jCent, TotalListVertices,
eVert, eVertRed, fVert, HeightVert, eConn, Center, Linc, eV, FuncInsert,
PermVertGroup, IsFinished, nbOrb, iOrb, ListAdj, eFac, eAdj, FAC, Stab, EXT, MatrixGen,
PermGen, TheList, iVert, h1, h2, eGen, fGen, LEV, iInc, jInc, TheStab, GRPmat, GRPperm,
PhiPermMat, ListVertices, ListInformationCenter;
  ListVertices:=RepartInfo.ListVertices;
  ListInformationCenter:=RepartInfo.ListInformationCenter;
  n:=Length(InteriorElement);
  ListCenter:=List(ListInformationCenter, u->u.Center);
  Gra:=NullGraph(Group(()), Length(ListCenter));
  for eGen in GeneratorsOfGroup(SymmetryGroupRepartitionning.PermVertGroup)
  do
    eMat:=Image(SymmetryGroupRepartitionning.PhiPermMat, eGen);
    for iCent in [1..Length(ListCenter)]
    do
      jCent:=Position(ListCenter, ListCenter[iCent]*eMat);
      if iCent<>jCent then
        AddEdgeOrbit(Gra, [iCent, jCent]);
        AddEdgeOrbit(Gra, [jCent, iCent]);
      fi;
    od;
  od;
  TotalListVertices:=[];
  for eVert in ListVertices
  do
    eVertRed:=eVert{[2..n+1]};
    fVert:=ShallowCopy(eVert);
    HeightVert:=eVertRed*InteriorElement*eVertRed;
    Add(fVert, HeightVert);
    Add(TotalListVertices, fVert);
  od;
#  Print("TotalListVertices=\n");
#  PrintArray(TotalListVertices);
  if RankMat(TotalListVertices)<Length(TotalListVertices[1]) then
    Print("Error in the computation of the vertices\n");
    Print(NullMat(5));
  fi;
  ListOrbitFacet:=[];
  for eConn in ConnectedComponents(Gra)
  do
    eRec:=ListInformationCenter[eConn[1]];
    EXT:=List(ListOrbitDelaunay[eRec.iDelaunay].EXT, u->u*eRec.eBigMat);
    Linc:=List(EXT, u->Position(ListVertices, u));
    Add(ListOrbitFacet, rec(eFac:=__FindFacetInequality(TotalListVertices, Linc), EXT:=EXT, Linc:=Linc, Status:="NO", Position:="lower", Size:=Length(eConn),
iDelaunayOrigin:=eRec.iDelaunay, eBigMat:=eRec.eBigMat, Center:=eRec.Center));
  od;
  PermVertGroup:=SymmetryGroupRepartitionning.PermVertGroup;
  FuncInsert:=function(eFac)
    local Linc, EXT, iVert, iOrb, g, Stab, ThePos, CP, eEnr;
    Linc:=[];
    EXT:=[];
    for iVert in [1..Length(ListVertices)]
    do
      if TotalListVertices[iVert]*eFac=0 then
        Add(Linc, iVert);
        Add(EXT, ListVertices[iVert]);
      fi;
    od;
    for iOrb in [1..Length(ListOrbitFacet)]
    do
      g:=RepresentativeAction(PermVertGroup, ListOrbitFacet[iOrb].Linc, Linc, OnSets);
      if g<>fail then
        return rec(iOrb:=iOrb, eBigMat:=Image(SymmetryGroupRepartitionning.PhiPermMat, g));
      fi;
    od;
    Stab:=Stabilizer(PermVertGroup, Linc, OnSets);
    eEnr:=rec(eFac:=eFac, EXT:=EXT, Linc:=Linc, Status:="NO", Size:=Order(PermVertGroup)/Order(Stab));
    if eFac[Length(eFac)]=0 then
      ThePos:="barrel";
    else
      ThePos:="higher";
      CP:=CenterRadiusDelaunayPolytopeGeneral(InteriorElement, EXT);
      eEnr.Center:=CP.Center;
    fi;
    eEnr.Position:=ThePos;
    Add(ListOrbitFacet, eEnr);
    Print("New facet(Delaunay):  |V|=", Length(EXT), " |Sym|=", Order(Stab), "\n");
    return rec(iOrb:=Length(ListOrbitFacet), eBigMat:=IdentityMat(n+1));
  end;
  while(true)
  do
    IsFinished:=true;
    nbOrb:=Length(ListOrbitFacet);
    for iOrb in [1..nbOrb]
    do
      if ListOrbitFacet[iOrb].Status="NO" then
        Stab:=Stabilizer(PermVertGroup, ListOrbitFacet[iOrb].Linc, OnSets);
        PermGen:=[];
        MatrixGen:=[];
        for eGen in GeneratorsOfGroup(Stab)
        do
          TheList:=[];
          for iVert in [1..Length(ListOrbitFacet[iOrb].Linc)]
          do
            h1:=ListOrbitFacet[iOrb].Linc[iVert];
            h2:=OnPoints(h1, eGen);
            Add(TheList, Position(ListOrbitFacet[iOrb].Linc, h2));
          od;
          fGen:=PermList(TheList);
          Add(PermGen, fGen);
          eMat:=Image(SymmetryGroupRepartitionning.PhiPermMat, eGen);
          Add(MatrixGen, eMat);
        od;
        GRPperm:=PersoGroupPerm(PermGen);
        GRPmat:=PersoGroupMatrix(MatrixGen, n+1);
        PhiPermMat:=GroupHomomorphismByImagesNC(GRPperm, GRPmat, PermGen, MatrixGen);
        TheStab:=rec(PermutationStabilizer:=GRPperm, PhiPermMat:=PhiPermMat);
        ListOrbitFacet[iOrb].TheStab:=TheStab;
        ListAdj:=[];
        FAC:=ListAdjacent(TotalListVertices, ListOrbitFacet[iOrb].eFac);
        FAC:=OrbitListing(TotalListVertices, FAC, Stab);
        for eFac in FAC
        do
          eAdj:=FuncInsert(eFac);
          LEV:=[];
          for iInc in [1..Length(ListOrbitFacet[iOrb].Linc)]
          do
            jInc:=ListOrbitFacet[iOrb].Linc[iInc];
            if TotalListVertices[jInc]*eFac=0 then
              Add(LEV, iInc);
            fi;
          od;
          eAdj.eInc:=LEV;
          Add(ListAdj, eAdj);
        od;
        ListOrbitFacet[iOrb].ListAdj:=ListAdj;
        ListOrbitFacet[iOrb].Status:="YES";
        IsFinished:=false;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  for iOrb in [1..Length(ListOrbitFacet)]
  do
    Unbind(ListOrbitFacet[iOrb].eFac);
  od;
  return ListOrbitFacet;
end;



CreateRepartitionningSymmetryGroup:=function(ListOrbitDelaunay, RepartInfo)
  local ListGenerators, FuncInsertGenerator, ListiDelaunay, eRec, iDelaunay, ListReg, eMat, TheCenter, eBigMat, iComp, ListGenPermVertices, n, GRPperm, GRPmat, PhiPermMat, eGen, FuncCreatePermutation;
  Print("Entering CreateSymmetryGroup\n");
  n:=Length(RepartInfo.ListVertices[1])-1;
  ListGenerators:=[];
  ListGenPermVertices:=[];
  FuncCreatePermutation:=function(TheMat)
    local LE, iVert, eImg, pos;
    LE:=[];
    for iVert in [1..Length(RepartInfo.ListVertices)]
    do
      eImg:=RepartInfo.ListVertices[iVert]*TheMat;
      pos:=Position(RepartInfo.ListVertices, eImg);
      Add(LE, pos);
    od;
    return PermList(LE);
  end;



  FuncInsertGenerator:=function(TheMat)
    local test, ThePerm;
    ThePerm:=FuncCreatePermutation(TheMat);
    test:=ThePerm in PersoGroupPerm(ListGenPermVertices);
    if test=false then
      Add(ListGenerators, TheMat);
      Add(ListGenPermVertices, ThePerm);
    fi;
  end;
  ListiDelaunay:=Set(List(RepartInfo.ListInformationCenter, u->u.iDelaunay));
  for iDelaunay in ListiDelaunay
  do
    ListReg:=Filtered(RepartInfo.ListInformationCenter, x->x.iDelaunay=iDelaunay);
    eRec:=ListReg[1];
    for eGen in GeneratorsOfGroup(ListOrbitDelaunay[iDelaunay].TheStab.PermutationStabilizer)
    do
      eBigMat:=Image(ListOrbitDelaunay[iDelaunay].TheStab.PhiPermMat, eGen);
      FuncInsertGenerator(Inverse(eRec.eBigMat)*eBigMat*eRec.eBigMat);
    od;
    for iComp in [2..Length(ListReg)]
    do
      FuncInsertGenerator(Inverse(eRec.eBigMat)*ListReg[iComp].eBigMat);
    od;
  od;
  GRPperm:=PersoGroupPerm(ListGenPermVertices);
  GRPmat:=PersoGroupMatrix(ListGenerators, n+1);
  PhiPermMat:=GroupHomomorphismByImagesNC(GRPperm, GRPmat, ListGenPermVertices, ListGenerators);
  if PhiPermMat=fail then
    Print(NullMat(5));
  fi;
  Print("Order SymGRP(old)=", Order(GRPperm), "\n");
  Print("Leaving CreateSymmetryGroup\n");
  return rec(PermVertGroup:=GRPperm, PhiPermMat:=PhiPermMat);
end;





FindRepartitionningInfo:=function(eConnDelaunay, ListOrbitDelaunay, ListInformationsOneFlipping)
  local ListInformationCenter, eIdx, ListVertices, IsFinished, eEnr, nbCent, iCent, TheCenter, eCase, GRPperm, n, FuncInsert, NewMat, NewCenter, NewRec, test, eVert, TheVector, eCos, StabPerm, FuncAction;
  Print("We are entering FindRepartitionningInfo\n");
  n:=Length(ListOrbitDelaunay[1].EXT[1])-1;
  eIdx:=eConnDelaunay[1];
  ListInformationCenter:=[rec(iDelaunay:=eIdx, Status:="NO", Center:=ListOrbitDelaunay[eIdx].Center, eBigMat:=IdentityMat(n+1,0))];
  ListVertices:=Set(ListOrbitDelaunay[eIdx].EXT);
  FuncInsert:=function(TheRec)
    local eRec;
    for eRec in ListInformationCenter
    do
      if eRec.Center=TheRec.Center then
        return true;
      fi;
    od;
    Add(ListInformationCenter, ShallowCopy(TheRec));
    Print("We have now ", Length(ListInformationCenter), " centers\n");
    return false;
  end;
  while(true)
  do
    IsFinished:=true;
    nbCent:=Length(ListInformationCenter);
    for iCent in [1..nbCent]
    do
      eEnr:=ListInformationCenter[iCent];
      TheCenter:=eEnr.Center;
      if eEnr.Status="NO" then
        IsFinished:=false;
        eEnr.Status:="YES";
        for eCase in ListInformationsOneFlipping
        do
          if eEnr.iDelaunay=eCase.Input then
            GRPperm:=ListOrbitDelaunay[eCase.Input].TheStab.PermutationStabilizer;
            FuncAction:=function(eVect, ePerm)
              return eVect*Image(ListOrbitDelaunay[eCase.Input].TheStab.PhiPermMat, ePerm);
            end;
            TheVector:=ListOrbitDelaunay[eCase.iDelaunay].Center*eCase.eBigMat;
            StabPerm:=Stabilizer(GRPperm, TheVector, FuncAction);
            for eCos in RightCosetsNC(GRPperm, StabPerm)
            do
              NewMat:=eCase.eBigMat*Image(ListOrbitDelaunay[eCase.Input].TheStab.PhiPermMat, Representative(eCos))*eEnr.eBigMat;
              NewCenter:=ListOrbitDelaunay[eCase.iDelaunay].Center*NewMat;
              NewRec:=rec(iDelaunay:=eCase.iDelaunay, Status:="NO", Center:=NewCenter, eBigMat:=NewMat);
              test:=FuncInsert(NewRec);
              if test=false then
                for eVert in ListOrbitDelaunay[eCase.iDelaunay].EXT
                do
                  AddSet(ListVertices, eVert*NewMat);
                od;
              fi;
            od;
          fi;
        od;
        Print("Center ", iCent, " finished\n");
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  for iCent in [1..Length(ListInformationCenter)]
  do
    Unbind(ListInformationCenter[iCent].Status);
  od;
  if Length(ListInformationCenter)=1 then
    Print("Error in computation of centers\n");
    Print(NullMat(5));
  fi;
  Print("We are leaving FindRepartitionningInfo\n");
  return rec(ListVertices:=ListVertices, ListInformationCenter:=ListInformationCenter);
end;

#    RepartInfo:=FindRepartitionningInfo(eConn, ListOrbitDelaunay, ListInformationsOneFlipping);
#    SYMGRP:=CreateRepartitionningSymmetryGroup(ListOrbitDelaunay, RepartInfo);
#    LORB:=FindFacetRepartitionningComplex(ListOrbitDelaunay, InteriorElement, SYMGRP, RepartInfo);
#    ListCenterLow:=[];
#    ListCenterUpp:=[];
#    for eFacet in LORB
#    do
#      if eFacet.Position="lower" then
#        Add(ListCenterLow, eFacet.Size);
#      fi;
#      if eFacet.Position="higher" then
#        Add(ListCenterUpp, eFacet.Size);
#      fi;
#    od;
#    Print("Repart |V|=", Length(RepartInfo.ListVertices), "  low=", ListCenterLow, "  upp=", ListCenterUpp, "\n");

#    if Set(ListCenterLow2)<>Set(ListCenterLow) then
#      Print("We have a difference between the two computations\n");
#      Print(NullMat(5));
#    fi;



FindDelaunayDecompositionOnRay:=function(ListOrbitDelaunay, InteriorElement, FAC, eCase, TheExt)
  local LESmatch, iFac, TheBasis, eMat, fMat, Gra, ListMatched, i1, i2, eP, ListAdj, iOrb, ListConn, ListGroupMelt, ListGroupUnMelt, TheHistory, DataTheEquivariantLtypeDomain, NewListOrbitDelaunay, iInfo, TheDATA, eConn, ListInfo, CP, eInfo, SYMGRP, RepartInfo, iDelaunay, EXT2, FAC2, eFac, eInc, iExt, eMat1, eAdj, Pos, Pos2, iFacet, iDelaunayOld, iConn, eCent, iCase;
  TheBasis:=eCase.Basis;
  eMat:=FuncComputeMat(TheBasis, TheExt);
  fMat:=FuncComputeMat(TheBasis, InteriorElement);
  LESmatch:=[];
  for iFac in [1..Length(FAC.ListInequalities)]
  do
    if FAC.ListInequalities[iFac]*TheExt=0 then
      Append(LESmatch, FAC.ListInformations[iFac]);
    fi;
  od;
  Gra:=NullGraph(Group(()), Length(ListOrbitDelaunay));
  ListMatched:=[];
  for eP in LESmatch
  do
    i1:=eP.Input;
    i2:=eP.iDelaunay;
    ListMatched:=Union(ListMatched, Set([i1, i2]));
    if i1<>i2 then
      AddEdgeOrbit(Gra, [i1, i2]);
      AddEdgeOrbit(Gra, [i2, i1]);
    fi;
  od;
  ListConn:=ConnectedComponents(Gra);
  ListGroupMelt:=[];
  ListGroupUnMelt:=[];
  # this code take care of the cases of RepartitionningDelaunay
  # being composed of only one orbit of Delaunay.
  for eConn in ListConn
  do
    if Length(Intersection(eConn, ListMatched))>0 then
      Add(ListGroupMelt, eConn);
    else
      Add(ListGroupUnMelt, eConn);
    fi;
  od;

  ListInfo:=[];
  for eConn in ListGroupMelt
  do
    RepartInfo:=FindRepartitionningInfo(eConn, ListOrbitDelaunay, LESmatch);
    SYMGRP:=CreateRepartitionningSymmetryGroup(ListOrbitDelaunay, RepartInfo);
    EXT2:=RepartInfo.ListVertices;
    FAC2:=DualDescription(EXT2);
    FAC2:=OrbitListing(EXT2, FAC2, DataTheEquivariantLtypeDomain[iOrb].TheStab.PermVertGroup);
    ListAdj:=[];
    for eFac in FAC2
    do
      eInc:=[];
      for iExt in [1..Length(EXT2)]
      do
        if EXT2[iExt]*eFac=0 then
          Add(eInc, iExt);
        fi;
      od;
      Add(ListAdj, rec(eInc:=eInc));
    od;
    Add(ListInfo, [RepartInfo, SYMGRP, ListAdj]);
  od;
  NewListOrbitDelaunay:=[];
  for eConn in ListGroupUnMelt
  do
    Add(NewListOrbitDelaunay, ["old", eConn[1]]);
  od;
  for iInfo in [1..Length(ListInfo)]
  do
    Add(NewListOrbitDelaunay, ["new", iInfo]);
  od;

  DataTheEquivariantLtypeDomain:=[];
  for iOrb in [1..Length(NewListOrbitDelaunay)]
  do
    TheHistory:=NewListOrbitDelaunay[iOrb];
    if TheHistory[1]="old" then
      iDelaunay:=TheHistory[2];
      CP:=CenterRadiusDelaunayPolytopeGeneral(eMat, ListOrbitDelaunay[iDelaunay].EXT);
      TheDATA:=rec(EXT:=ListOrbitDelaunay[iDelaunay].EXT, TheStab:=ListOrbitDelaunay[iDelaunay].TheStab, Center:=CP.Center);
    else
      iInfo:=TheHistory[2];
      eInfo:=ListInfo[iInfo];
      CP:=CenterRadiusDelaunayPolytopeGeneral(eMat, eInfo[1].ListVertices);
      TheDATA:=rec(EXT:=eInfo[1].ListVertices, TheStab:=eInfo[2], Center:=CP.Center);
    fi;
    Add(DataTheEquivariantLtypeDomain, TheDATA);
  od;

  for iOrb in [1..Length(NewListOrbitDelaunay)]
  do
    TheHistory:=NewListOrbitDelaunay[iOrb];
    ListAdj:=[];
    if TheHistory[1]="old" then
      iDelaunay:=TheHistory[2];
      for eAdj in ListOrbitDelaunay[iDelaunay].Adjacencies
      do
        iDelaunayOld:=eAdj.iDelaunay;
        Pos:=Position(ListGroupUnMelt, [iDelaunayOld]);
        if Pos<>fail then
          Add(ListAdj, rec(eBigMat:=eAdj.eBigMat, iDelaunay:=Pos, eInc:=eAdj.eInc, Input:=iOrb));
          if Intersection(Set(List(DataTheEquivariantLtypeDomain[Pos].EXT, u->u*eAdj.eBigMat)), Set(DataTheEquivariantLtypeDomain[iOrb].EXT))<>Set(DataTheEquivariantLtypeDomain[iOrb].EXT{eAdj.eInc}) then
            Print("We have an error case 1\n");
            Print(NullMat(5));
          fi;
        else
          for iConn in [1..Length(ListGroupMelt)]
          do
            eConn:=ListGroupMelt[iConn];
            if Position(eConn, iDelaunayOld)<>fail then
              iInfo:=iConn;
            fi;
          od;
          for iFacet in [1..Length(ListInfo[iInfo][1].ListInformationCenter)]
          do
            eCent:=ListInfo[iInfo][1].ListInformationCenter[iFacet];
            if eCent.iDelaunay=iDelaunayOld then
              Pos2:=iFacet;
            fi;
          od;
          Pos:=Position(NewListOrbitDelaunay, ["new", iInfo]);
          eMat1:=Inverse(ListInfo[iInfo][1].ListInformationCenter[iFacet].eBigMat)*eAdj.eBigMat;
          Add(ListAdj, rec(eBigMat:=eMat1, iDelaunay:=Pos, eInc:=eAdj.eInc, Input:=iOrb));
          if Intersection(Set(List(DataTheEquivariantLtypeDomain[Pos].EXT, u->u*eMat1)), Set(DataTheEquivariantLtypeDomain[iOrb].EXT))<>Set(DataTheEquivariantLtypeDomain[iOrb].EXT{eAdj.eInc}) then
            Print("We have an error case 2\n");
            Print(NullMat(5));
          fi;
        fi;
      od;
    else
      iInfo:=TheHistory[2];
      for eAdj in ListInfo[iInfo][3]
      do
        
      od;
      Print(NullMat(5));
    fi;
    DataTheEquivariantLtypeDomain[iOrb].Adjacencies:=ListAdj;
  od;
  return DataTheEquivariantLtypeDomain;
end;




__GetRAYSaffine:=function(EXT, ListInc, nb)
  local EXTp, EXTnew;
  EXTp:=EXT{ListInc};
  EXTnew:=List([1..Length(EXTp)-1], x->EXTp[x]-EXTp[Length(EXTp)]);
  return List(__GetRAYSproj(EXTnew, [1..Length(EXTnew)], nb), x->ListInc{Concatenation(x, [Length(EXTp)])});
end;


GetRAYS:=function(EXT, ListInc, nb)
  local Lfirst;
  Lfirst:=List(EXT, x->x[1]);
  if Lfirst*Lfirst=0 then
    return __GetRAYSproj(EXT, ListInc, nb);
  fi;
  if Length(Set(Lfirst))=1 then
    return __GetRAYSaffine(EXT, ListInc, nb);
  fi;
  Print("first coordinate should be constant over EXT\n");
  Print(NullMat(5));
end;


#
# the action on SmallSet is left unchanged, while the action
# on the complement is trivialized.
ReduceGroupAction:=function(TheGroup, SmallSet)
  local nbV, ListGens, eGen, eList, iVert;
  nbV:=Maximum(SmallSet);
  ListGens:=[];
  for eGen in GeneratorsOfGroup(TheGroup)
  do
    eList:=[];
    for iVert in [1..nbV]
    do
      if Position(SmallSet, iVert)=fail then
        Add(eList, iVert);
      else
        Add(eList, OnPoints(iVert, eGen));
      fi;
    od;
    Add(ListGens, PermList(eList));
  od;
  return PersoGroupPerm(ListGens);
end;



MoveActionBetweenSet:=function(GroupExt, OldList, NewList)
  local eGen, NewListGens, eList, iNewVert, iOldVert, jOldVert, jNewVert, nbV;
  NewListGens:=[];
  nbV:=Maximum(NewList);
  for eGen in GeneratorsOfGroup(GroupExt)
  do
    eList:=[];
    for iNewVert in [1..nbV]
    do
      if Position(NewList, iNewVert)=fail then
        Add(eList, iNewVert);
      else
        iOldVert:=OldList[Position(NewList, iNewVert)];
        jOldVert:=OnPoints(iOldVert, eGen);
        jNewVert:=NewList[Position(OldList, jOldVert)];
        Add(eList, jNewVert);
      fi;
    od;
    Add(NewListGens, PermList(eList));
  od;
  return PersoGroupPerm(NewListGens);
end;



ListShortVectorCandidates:=function(Ltype)
  local nbDelaunay, iDelaunay, ListCand, ListCandByLtype, ListSizes, Gra, FuncFind, eAdj, jDelaunay, ieOrb, imgEXT, jeOrb, iStab, jStab, iStabNorm, jStabNorm, NewStab, FacORB, eOrb, LNst, FvWR, nb, CliqueVertices, LNstMapped, FvWR2, ListCandidateShortest, eVert, fVert, eEdge, eDiff, n, FuncInvFind, FuncFindInListCand, i, eConn;
  nbDelaunay:=Length(Ltype);
  ListCandByLtype:=[];
  ListSizes:=[];
  n:=Length(Ltype[1].EXT[1])-1;
  for iDelaunay in [1..nbDelaunay]
  do
    ListCand:=__ListOrbEdges(Ltype[iDelaunay].EXT, Ltype[iDelaunay].TheStab.PermutationStabilizer);
    Add(ListCandByLtype, ListCand);
    Add(ListSizes, Length(ListCand));
  od;
  Gra:=NullGraph(Group(()), Sum(ListSizes));
  FuncFind:=function(eList)
    return Sum(ListSizes{[1..eList[1]-1]})+eList[2];
  end;
  FuncInvFind:=function(BigeVert)
    local iDelaunay, eDiff;
    iDelaunay:=1;
    while(true)
    do
      eDiff:=BigeVert-Sum(ListSizes{[1..iDelaunay-1]});
      if eDiff<=ListSizes[iDelaunay] then
        return [iDelaunay, eDiff];
      fi;
    od;
  end;
  FuncFindInListCand:=function(eEdge, iDelaunay)
    local iRep;
    for iRep in [1..Length(ListCandByLtype[iDelaunay])]
    do
      if RepresentativeAction(Ltype[iDelaunay].TheStab.PermutationStabilizer, eEdge, ListCandByLtype[iDelaunay][iRep], OnSets)<>fail then
        return iRep;
      fi;
    od;
    return false;
  end;


  for iDelaunay in [1..nbDelaunay]
  do
    for eAdj in Ltype[iDelaunay].Adjacencies
    do
      jDelaunay:=eAdj.iDelaunay;
      if jDelaunay>iDelaunay then
        ieOrb:=eAdj.eInc;
        imgEXT:=List(Ltype[jDelaunay].EXT, x->x*eAdj.eBigMat);
        jeOrb:=List(Ltype[iDelaunay].EXT{ieOrb}, x->Position(imgEXT, x));
        iStab:=Stabilizer(Ltype[iDelaunay].TheStab.PermutationStabilizer, ieOrb, OnSets);
        jStab:=Stabilizer(Ltype[jDelaunay].TheStab.PermutationStabilizer, Set(jeOrb), OnSets);
        iStabNorm:=ReduceGroupAction(iStab, Set(ieOrb));
        jStabNorm:=MoveActionBetweenSet(ReduceGroupAction(jStab, Set(jeOrb)), jeOrb, ieOrb);
        NewStab:=Group(Union(GeneratorsOfGroup(iStabNorm), GeneratorsOfGroup(jStabNorm)));
        FacORB:=__RepresentativeOrbitTwoSet(NewStab, Set(ieOrb));
        for eOrb in FacORB
        do
          LNst:=__IndividualListing(eOrb, iStabNorm, NewStab);
          FvWR:=List(LNst, x->FuncFindInListCand(x, iDelaunay));
          nb:=Length(Filtered(FvWR, x->x=false));
          if nb>0 and nb<Length(LNst) then
            Print("illogism on first test for EdgeSet\n");
            Print(NullMat(5));
          fi;
          if nb>0 then
            CliqueVertices:=List(FvWR, x->[iDelaunay, x]);
            LNst:=__IndividualListing(eOrb, jStabNorm, NewStab);
            LNstMapped:=List(LNst, x->Set(List(x, y->jeOrb[Position(ieOrb, y)])));
            FvWR2:=List(LNstMapped, x->FuncFindInListCand(x, jDelaunay));
            nb:=Length(Filtered(FvWR, x->x=false));
            if nb>0 then
              Print("illogism on second test for EdgeSet\n");
              Print(NullMat(5));
            fi;
            Append(CliqueVertices, List(FvWR2, x->[jDelaunay, x]));
            for i in [2..Length(CliqueVertices)]
            do
              eVert:=FuncFind(CliqueVertices[i-1]);
              fVert:=FuncFind(CliqueVertices[i]);
              AddEdgeOrbit(Gra, [eVert, fVert]);
              AddEdgeOrbit(Gra, [fVert, eVert]);
            od;
          fi;
        od;
      fi;
    od;
  od;
  ListCandidateShortest:=[];
  for eConn in ConnectedComponents(Gra)
  do
    eVert:=FuncInvFind(eConn[1]);
    iDelaunay:=eVert[1];
    eEdge:=ListCandByLtype[eVert[2]];
    eDiff:=Ltype[iDelaunay].EXT[eEdge[1]]-
    Add(ListCandidateShortest, eDiff{[2..n+1]});
  od;
  return ListCandidateShortest;
end;





#UpDateCenterProcedure:=function(EquivariantLtypeDomain, GramMat)
#  local UpdatedLtype, iOrb, eRec, CP;
#  UpdatedLtype:=[];
#  for iOrb in [1..Length(EquivariantLtypeDomain)]
#  do
#    eRec:=EquivariantLtypeDomain[iOrb];
#    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, eRec.EXT);
#    Add(UpdatedLtype, rec(EXT:=eRec.EXT, Center:=CP.Center, TheStab:=eRec.TheStab, Adjacencies:=eRec.Adjacencies));
#  od;
#  return UpdatedLtype;
#end;






#
# NON WORKING AT PRESENT
__DualDescriptionLRS_PerlCanonicalize:=function(EXT, GroupExt)
  local FileExt, FileExt2, FileGrp, FileLog, FileCan, FileRed, output, LER, test, eRepr, eE, TheList, TheOrb, NLS;
  FileExt2:=Filename(POLYHEDRAL_tmpdir, "Projlrs3.ext2");
  FileGrp:=Filename(POLYHEDRAL_tmpdir, "Projlrs3.grp");
  FileLog:=Filename(POLYHEDRAL_tmpdir, "Projlrs3.log");
  FileCan:=Filename(POLYHEDRAL_tmpdir, "Projlrs3.can");
  FileRed:=Filename(POLYHEDRAL_tmpdir, "Projlrs3.red");
  Print("Working on ", FileExt, "\n");
  #
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", Length(EXT[1]), " integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  output:=OutputTextFile(FileExt2, true);;
  WriteMatrix(output, EXT);
  CloseStream(output);
  #
  GroupToPerl(FileGrp, GroupExt, Length(EXT));
  #
  Exec(FileGLRS, " ", FileExt, " | grep -v '*' > ", FileLog);
  #
  Exec(FileNudifyLRS_Canonicalize, " ", FileGrp, " ", FileExt2, " < ", FileLog, " > ", FileCan);
  #
  Exec("cat ", FileCan, " | sort | uniq > ", FileRed);
  #
  LER:=ReadVectorFile(FileRed);
  test:=TestConicness(EXT);
  TheOrb:=[];
  for eRepr in LER
  do
    TheList:=[];
    if test=true then
      Add(TheList, FacetOfInfinity(Length(EXT[1])));
    fi;
    for eE in eRepr
    do
      Add(TheList, EXT[eE]);
    od;
    NLS:=NullspaceMat(TheList);
#    Print("nb=", Length(NLS), "\n");
    Add(TheOrb, NLS[1]);
  od;
#  RemoveFile(FileExt);
#  RemoveFile(FileExt2);
#  RemoveFile(FileGrp);
#  RemoveFile(FileLog);
#  RemoveFile(FileCan);
  return TheOrb;
end;




SaveMatrixToFile:=function(FileName, TheMat)
  local output, nbCol, nbLine, iLine, iCol, eLine;
  nbLine:=Length(TheMat); 
  RemoveFile(FileName);
  output:=OutputTextFile(FileName, true);
  AppendTo(output, "return [");
  for iLine in [1..nbLine]
  do
    eLine:=TheMat[iLine];
    nbCol:=Length(eLine);
    AppendTo(output, "[");
    for iCol in [1..nbCol]
    do
      AppendTo(output, eLine[iCol]);
      if iCol < nbCol then
        AppendTo(output, ",");
      fi;
    od;
    AppendTo(output, "]");
    if iLine< nbLine then
      AppendTo(output, ",\n");
    fi;
  od;
  AppendTo(output, "];\n");
  CloseStream(output);
end;


OrbitListing:=function(EXT, FAC, GroupEXT)
  local Lset, iFac, Linc, O, eO, ListOrbFAC, pos;
  Lset:=[];
  for iFac in [1..Length(FAC)]
  do
    Linc:=Filtered([1..Length(EXT)], x->EXT[x]*FAC[iFac]=0);
    Add(Lset, Linc);
  od;
  O:=Orbits(GroupEXT, Lset, OnSets);
  ListOrbFAC:=[];
  for eO in O
  do
    pos:=Position(Lset, eO[1]);
    Add(ListOrbFAC, FAC[pos]);
  od;
  return ListOrbFAC;
end;


TakeHalfVector:=function(ListVect)
  local nbVect, Lstatus, Lreturn, iVect, eVect, pos1, pos2;
  nbVect:=Length(ListVect);
  Lstatus:=ListWithIdenticalEntries(nbVect, 0);
  Lreturn:=[];
  for iVect in [1..nbVect]
  do
    if Lstatus[iVect]=0 then
      eVect:=ListVect[iVect];
      pos1:=Position(ListVect, eVect);
      pos2:=Position(ListVect, -eVect);
      Lstatus[pos1]:=1;
      Lstatus[pos2]:=1;
      Add(Lreturn, eVect);
    fi;
  od;
  return Lreturn;
end;


__PermutationGroupFromFiniteMatrixGroup:=function(n, MatrixGRP, ListPermGens)
  local MatrGens, eMat, PermGRP, phi, FuncActionMod1, SmallyGenerated;
  MatrGens:=GeneratorsOfGroup(MatrixGRP);
  PermGRP:=Group(ListPermGens);
  phi:=GroupHomomorphismByImagesNC(PermGRP, MatrixGRP, ListPermGens, MatrGens);
  SmallyGenerated:=function()
    local RedGRP;
    RedGRP:=Group(SmallGeneratingSet(PermGRP));
    return PersoGroupMatrix(List(RedGRP, x->Image(phi, x)), n);
  end;
  return rec(PermGRP:=PermGRP, phi:=phi, SmallyGenerated:=SmallyGenerated);
end;


NormalizedSecondMomentForSimplex:=function(GramMat, ThePoint, ListVert)
  local n, TheBarycenter, TheSum, eVert, eDiff;
  n:=Length(ThePoint)-1;
  TheBarycenter:=Sum(ListVert)/Length(ListVert);
  TheSum:=0;
  for eVert in ListVert
  do
    eDiff:=eVert{[2..n+1]}-TheBarycenter{[2..n+1]};
    TheSum:=TheSum+eDiff*GramMat*eDiff;
  od;
  eDiff:=ThePoint{[2..n+1]}-TheBarycenter{[2..n+1]};
  return eDiff*GramMat*eDiff+TheSum/((n+1)*(n+2));
end;


QuantizationConstant:=function(DataLattice, DelaunayDatabase)
  local nbDelaunay, TheOrd, QuantizationSum, iOrb, TheRecord, TotalCent, GroupEXT, FAC, eAdj, fInc, eFac, FlagOrbs, eOrb, ListVert, SimplexVol, SecondMoment, EXT, TotalVolume;
  nbDelaunay:=DelaunayDatabase.FuncDelaunayGetNumber();
  TheOrd:=Size(DataLattice.MatrixGRP)/Factorial(DataLattice.n);
  QuantizationSum:=0;
  TotalVolume:=0;
  for iOrb in [1..nbDelaunay]
  do
    TheRecord:=DelaunayDatabase.FuncDelaunayGetRecord(iOrb);
    EXT:=TheRecord.EXT;
    TotalCent:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT).Center;
    GroupEXT:=TheRecord.TheStab.PermutationStabilizer;
    FAC:=[];
    for eAdj in TheRecord.Adjacencies
    do
      for fInc in Orbit(GroupEXT, eAdj.eInc, OnSets)
      do
        eFac:=NullspaceMat(TransposedMat(EXT{fInc}))[1];
        Add(FAC, eFac);
      od;
    od;
    FlagOrbs:=ListFlagOrbitSigned(GroupEXT, EXT, FAC, DataLattice.GramMat);
    for eOrb in FlagOrbs
    do
      ListVert:=List(eOrb.TheFlag, x->CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT{x}).Center);
      Add(ListVert, TotalCent);
      SimplexVol:=AbsInt(DeterminantMat(ListVert));
      SecondMoment:=NormalizedSecondMomentForSimplex(DataLattice.GramMat, ListVert[1], ListVert);
      QuantizationSum:=QuantizationSum+TheOrd*SimplexVol*SecondMoment*eOrb.TheSign;
      TotalVolume:=TotalVolume+TheOrd*SimplexVol*eOrb.TheSign;
    od;
  od;
  Print("TotalVolume=", TotalVolume, "\n");
  return QuantizationSum;
end;



#
# This is a beautiful code for computing homologies.
# But the use of determinant is simply so much faster
# 
FuncSignature:=function(ListOrbitByRank, TheRank, iOrbit, eEltTest)
  local TheEXT, eList, ePerm, eCenter, eSign, eElt, fCenter, fPos, fSign, fElt, eEltStab, test, iFaceSel;
  test:=eEltTest in ListOrbitByRank[TheRank][iOrbit].StabEXT;
  if test=false then
    Print("Inconsistency in stabilizer elements, first check\n");
    Print(NullMat(5));
  fi;
  if TheRank=3 then
    TheEXT:=ListOrbitByRank[TheRank][iOrbit].EXT;
    eList:=List(TheEXT, x->Position(TheEXT, x*eEltTest));
    ePerm:=PermList(eList);
    return SignPerm(ePerm);
  else
    iFaceSel:=ListOrbitByRank[TheRank][iOrbit].TheLookup.iFaceSel;
    eCenter:=ListOrbitByRank[TheRank][iOrbit].TheLookup.LookupCenter[1];
    eSign:=ListOrbitByRank[TheRank][iOrbit].TheLookup.LookupSign[1];
    eElt:=ListOrbitByRank[TheRank][iOrbit].TheLookup.LookupElt[1];
    fCenter:=eCenter*eEltTest;
    fPos:=Position(ListOrbitByRank[TheRank][iOrbit].TheLookup.LookupCenter, fCenter);
    fSign:=ListOrbitByRank[TheRank][iOrbit].TheLookup.LookupSign[fPos];
    fElt:=ListOrbitByRank[TheRank][iOrbit].TheLookup.LookupElt[fPos];
    eEltStab:=fElt*Inverse(eEltTest)*Inverse(eElt);
    test:=eEltStab in ListOrbitByRank[TheRank-1][iFaceSel].StabEXT;
    if test=false then
      Print("Inconsistency in stabilizer elements\n");
      Print(NullMat(5));
    fi;
    return eSign*fSign*FuncSignature(ListOrbitByRank, TheRank-1, iFaceSel, eEltStab);
  fi;
end;
#      # now computing Lookup data
#      if iRank=1 then
#        TheLookup:="irrelevant";
#      else
#        TheCollect:=Collected(ListIFace);
#        TheListOccur:=List(TheCollect, x->x[2]);
#        ThePossiblePos:=Filtered([1..Length(TheListOccur)], x->TheListOccur[x]=Minimum(TheListOccur));
#        iFaceSelect:=TheCollect[ThePossiblePos[1]][1];
#        IdxSel:=Filtered([1..Length(ListIFace)], x->ListIFace[x]=iFaceSelect);
#        LookupSign:=ListSign{IdxSel};
#        LookupElt:=ListElt{IdxSel};
#        LookupCenter:=ListCentersM1{IdxSel};
#        TheLookup:=rec(iFaceSel:=iFaceSelect, LookupSign:=LookupSign, LookupElt:=LookupElt, LookupCenter:=LookupCenter);
#      fi;




#
#
#
# This program solve overdeterminate Linearsystems
#
OverDeterminateLinearSystem:=function(ListEquations, RightTerms)
  local MinimalSubset, MinimalRightTerms, rnk, EVRL, B;
  MinimalSubset:=[];
  MinimalRightTerms:=[];
  rnk:=Length(ListEquations[1]);
  if RankMat(ListEquations)<rnk then
    Print("The system is underdeterminated\n");
    return false;
  fi;
  EVRL:=RowReduction(ListEquations);
  MinimalSubset:=ListEquations{EVRL.Select};
  MinimalRightTerms:=RightTerms{EVRL.Select};
  B:=SolutionMat(TransposedMat(MinimalSubset), MinimalRightTerms);
  if ListEquations*B<>RightTerms then
    Print("The system has no solution\n");
    return false;
  fi;
  return B;
end;



# last ListFuncMapping should be the identity and
# last ListFuncAction should be free (the "true" action)
FormalismIterationStabilizer:=function(ListFuncMapping, ListFuncAction)
  local nbAct, FuncStabilizer, FuncRepresentative;
  nbAct:=Length(ListFuncAction);
  FuncStabilizer:=function(GRP, eElt)
    local iAct, GrpStab;
    GrpStab:=ShallowCopy(GRP);
    for iAct in [1..nbAct]
    do
      GrpStab:=Stabilizer(GrpStab, ListFuncMapping[iAct], ListFuncAction[iAct]);
    od;
    return GrpStab;
  end;
  FuncRepresentative:=function(GRP, eElt1, eElt2)
    local GroupElement, fImg1, GrpStab, iAct, FCT, g;
    GroupElement:=Identity(GRP);
    fImg1:=ShallowCopy(eElt1);
    GrpStab:=ShallowCopy(GRP);
    for iAct in [1..nbAct]
    do
      FCT:=ListFuncMapping[iAct];
      g:=RepresentativeAction(GrpStab, FCT(fImg1), FCT(eElt2), ListFuncAction[iAct]);
      if g=fail then
        return fail;
      fi;
      fImg1:=ListFuncMapping[nbAct](fImg1);
      GroupElement:=GroupElement*g;
      if fImg1=eElt2 then
        return GroupElement;
      fi;
      GrpStab:=Stabilizer(GrpStab, fImg1, FCT);
    od;
  end;
  return rec(FuncStabilizer:=FuncStabilizer, FuncRepresentative:=FuncRepresentative);
end;




EliminationByRedundancyDirectCDD:=function(FAC)
  local FileINE, FileFIS, FileDDL, FileLOG, FileGAP, eFac, output, DataRedund;
  FileINE:=Filename(POLYHEDRAL_tmpdir, "redund.ine");
  FileFIS:=Filename(POLYHEDRAL_tmpdir, "redund.fis");
  FileDDL:=Filename(POLYHEDRAL_tmpdir, "redund.ddl");
  FileLOG:=Filename(POLYHEDRAL_tmpdir, "redund.log");
  FileGAP:=Filename(POLYHEDRAL_tmpdir, "redund.gap");
  output:=OutputTextFile(FileINE, true);
  AppendTo(output, "H-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(FAC), " ", Length(FAC[1]), " rational\n");
  for eFac in FAC
  do
    WriteVector(output, eFac);
  od;
  AppendTo(output, "end\n");
  AppendTo(output, "facet_listing\n");
  CloseStream(output);
  Exec(FileCddrGmp, " ", FileINE, " > ", FileLOG);
  Exec(FileVIStoGAP, " ", FileFIS, " > ", FileGAP);
  DataRedund:=ReadAsFunction(FileGAP)();
#  Print(NullMat(5), "\n");
  RemoveFile(FileINE);
  RemoveFile(FileFIS);
  RemoveFile(FileDDL);
  RemoveFile(FileGAP);
  return FAC{DataRedund};
end;

GroupHomologyByCellDecomposition:=function(PolyhedralInformation)
  local ListOrbitByRank, kSought, MatrixOfDim, ListResolutionsByRank, iRank, ListResol, LevSearch, iFace, eFace, TheStab, jRank, SpaceCoHomotopyFunction, TheDoperators, iK, dimSource, dimImg, TheMat, PrevVal1, PrevVal2, TheDim1, TheDim2, TheImage, iCol, eSign, eElt, pos, iOrbit, iEnt, TheBoundary, ListDimensions, ListMatrixDoperators, NewMat, iRankSource, jRankSource, iRankImage, jRankImage, iH2, TheD, iH1, iD, TheProd, TheOpp, SumOfProds, iH, TheResol, nbLine, nbCol, MatrixBegin, PrevVal, TheMatRES, TheDim, FuncSignatureOperation, FuncSignedMatrix, RightCosetVectorExpression, IsInKernel, iLine, TheHomotopy, SumMat;
  ListOrbitByRank:=PolyhedralInformation.ListOrbitByRank;
  kSought:=Length(ListOrbitByRank)-3;
  ListResolutionsByRank:=[];
  MatrixOfDim:=NullMat(kSought+2, kSought+2);
  Print("Computing the resolutions\n");
  for iRank in [0..kSought+1]
  do
    Print("  iRank=", iRank, "\n");
    ListResol:=[];
    LevSearch:=kSought+1-iRank;
    for iFace in [1..Length(ListOrbitByRank[iRank+2])]
    do
      eFace:=ListOrbitByRank[iRank+2][iFace];
      TheStab:=eFace.TheStab;
      Print("    iFace=", iFace, "  |G|=", Order(TheStab), "\n");
      TheResol:=ResolutionFiniteGroup(TheStab, LevSearch);
      for jRank in [0..LevSearch]
      do
        TheDim:=TheResol!.dimension(jRank);
        MatrixOfDim[iRank+1][jRank+1]:=MatrixOfDim[iRank+1][jRank+1]+TheDim;
      od;
      Add(ListResol, TheResol);
    od;
    Add(ListResolutionsByRank, ListResol);
  od;
  for iRank in [0..kSought+1]
  do
    LevSearch:=kSought+1-iRank;
    for jRank in [0..LevSearch]
    do
      Print(" ", MatrixOfDim[iRank+1][jRank+1]);
    od;
    Print("\n");
  od;
  FuncSignatureOperation:=function(iRank, iFace, eGmod)
    local NewListVal, iVal;
    NewListVal:=[];
    for iVal in [1..Length(eGmod.ListVal)]
    do
      Add(NewListVal, eGmod.ListVal[iVal]*PolyhedralInformation.FuncSignatureDet(iRank, iFace, eGmod.ListElt[iVal]));
    od;
    return rec(ListVal:=NewListVal, ListElt:=eGmod.ListElt);
  end;
  FuncSignedMatrix:=function(TheResol, iRank, jRank, iFace)
    local TheMatRES, iLine, iCol, TheDim1, TheDim2, RetMat, eLine;
    TheMatRES:=HAPmadeCorrect(TheResol).GetMatrix(jRank);
    TheDim1:=TheResol!.dimension(jRank);
    TheDim2:=TheResol!.dimension(jRank-1);
    RetMat:=[];
    for iLine in [1..TheDim1]
    do
      eLine:=[];
      for iCol in [1..TheDim2]
      do
        Add(eLine, FuncSignatureOperation(iRank, iFace, TheMatRES.TheMat[iLine][iCol]));
      od;
      Add(RetMat, eLine);
    od;
    return rec(nbLine:=TheDim1, nbCol:=TheDim2, TheMat:=RetMat);
  end;
  RightCosetVectorExpression:=function(TheStab, eVectSel)
    local ListRightCoset, TheDimInput, FuncInsertValue, iCol, iVal;
    ListRightCoset:=[];
    TheDimInput:=Length(eVectSel);
    FuncInsertValue:=function(eVal, iCol, eElt)
      local iCos, eQuot, TheVect;
      for iCos in [1..Length(ListRightCoset)]
      do
        eQuot:=eElt*ListRightCoset[iCos].eCos^(-1);
        if eQuot in TheStab then
          Add(ListRightCoset[iCos].TheVect[iCol].ListVal, eVal);
          Add(ListRightCoset[iCos].TheVect[iCol].ListElt, eQuot);
          return;
        fi;
      od;
      TheVect:=GetZeroVector(TheDimInput);
      Add(TheVect[iCol].ListVal, eVal);
      Add(TheVect[iCol].ListElt, ());
      Add(ListRightCoset, rec(eCos:=eElt, TheVect:=TheVect));
    end;
    for iCol in [1..TheDimInput]
    do
      for iVal in [1..Length(eVectSel[iCol].ListElt)]
      do
        FuncInsertValue(eVectSel[iCol].ListVal[iVal], iCol, eVectSel[iCol].ListElt[iVal]);
      od;
    od;
    return ListRightCoset;
  end;
  IsInKernel:=function(iRank, jRank, eVect)
    local PrevVal, iFace, TheResol, TheStab, TheDimInput, TheDimOutput, eVectSel, ListRightCoset, iCos, TheVect1, TheVect2, test;
    PrevVal:=0;
    for iFace in [1..Length(ListOrbitByRank[iRank+2])]
    do
      TheResol:=ListResolutionsByRank[iRank+1][iFace];
      TheStab:=ListOrbitByRank[iRank+2][iFace].TheStab;
      TheDimInput:=TheResol!.dimension(jRank);
      TheDimOutput:=TheResol!.dimension(jRank+1);
      eVectSel:=ReducedGmoduleVector(eVect{[1+PrevVal..PrevVal+TheDimInput]});
      ListRightCoset:=RightCosetVectorExpression(TheStab, eVectSel);
      for iCos in [1..Length(ListRightCoset)]
      do
        TheVect1:=ListRightCoset[iCos].TheVect;
        TheVect2:=List(TheVect1, x->FuncSignatureOperation(iRank, iFace, x));
        test:=HAPmadeCorrect(TheResol).IsInKernel(TheVect2, jRank);
        if test=false then
          return false;
        fi;
      od;
      PrevVal:=PrevVal+TheDimInput;
    od;
    return true;
  end;
  SpaceCoHomotopyFunction:=function(iRank, jRank, eVect)
    local TheReturn, PrevVal, iFace, TheResol, TheStab, TheDimInput, TheDimOutput, eVectSel, ListRightCoset, iCol, iVal, ListPreImage, iCos, PreImage1, PreImage2, TheReturn2, TheProd, test, TheVect1, TheVect2, TotalDimOutput;
    test:=IsInKernel(iRank, jRank, eVect);
    if test=false then
      Print("Sorry, the contracting homotopy is only defined in the kernel\n");
      Print("We are aware it is a limitation, but it is in aggreement with\n");
      Print("Our non-respect of Z-linearity\n");
      Print(NullMat(5));
    fi;
    TheReturn:=[];
    PrevVal:=0;
    TotalDimOutput:=MatrixOfDim[iRank+1][jRank+2];
    for iFace in [1..Length(ListOrbitByRank[iRank+2])]
    do
      TheResol:=ListResolutionsByRank[iRank+1][iFace];
      TheStab:=ListOrbitByRank[iRank+2][iFace].TheStab;
      TheDimInput:=TheResol!.dimension(jRank);
      TheDimOutput:=TheResol!.dimension(jRank+1);
      eVectSel:=ReducedGmoduleVector(eVect{[1+PrevVal..PrevVal+TheDimInput]});
      ListRightCoset:=RightCosetVectorExpression(TheStab, eVectSel);
      ListPreImage:=GetZeroVector(TheDimOutput);
      for iCos in [1..Length(ListRightCoset)]
      do
        TheVect1:=ListRightCoset[iCos].TheVect;
        TheVect2:=List(TheVect1, x->FuncSignatureOperation(iRank, iFace, x));
        PreImage2:=HAPmadeCorrect(TheResol).TheHomotopy(TheVect2, jRank);
        PreImage1:=List(PreImage2, x->FuncSignatureOperation(iRank, iFace, x));
        for iCol in [1..TheDimOutput]
        do
          for iVal in [1..Length(PreImage1[iCol].ListElt)]
          do
            Add(ListPreImage[iCol].ListVal, PreImage1[iCol].ListVal[iVal]);
            Add(ListPreImage[iCol].ListElt, PreImage1[iCol].ListElt[iVal]*ListRightCoset[iCos].eCos);
          od;
        od;
      od;
      TheProd:=VectorMatrixGmoduleMultiplication(ListPreImage, FuncSignedMatrix(TheResol, iRank, jRank+1, iFace));;
      test:=IsEqualGmoduleVector(TheProd, eVectSel);
      if test=false then
        Print("Non correct homotopy computation, please panic 2\n");
        Print(NullMat(5));
      fi;
      Append(TheReturn, ListPreImage);
      PrevVal:=PrevVal+TheDimInput;
    od;
    TheReturn2:=ReducedGmoduleVector(TheReturn);
    TheProd:=VectorMatrixGmoduleMultiplication(TheReturn2, TheDoperators[1][iRank+1][jRank+2]);
    test:=IsEqualGmoduleVector(TheProd, eVect);
    if test=false then
      Print("Non correct homotopy computation, please panic 3\n");
      Print(NullMat(5));
    fi;
    return TheReturn2;
  end;
  TheDoperators:=[];
  for iK in [1..kSought+2]
  do
    Add(TheDoperators, NullMat(kSought+2, kSought+2));
  od;
  Print("Computing the d0 operators\n");
  for iRank in [0..kSought]
  do
    Print("  iRank=", iRank, "\n");
    LevSearch:=kSought+1-iRank;
    for jRank in [1..LevSearch]
    do
      dimSource:=MatrixOfDim[iRank+1][jRank+1];
      dimImg:=MatrixOfDim[iRank+1][jRank];
      PrevVal1:=0;
      PrevVal2:=0;
      TheMat:=GetZeroMatrix(dimSource, dimImg);
      for iFace in [1..Length(ListOrbitByRank[iRank+2])]
      do
        TheResol:=ListResolutionsByRank[iRank+1][iFace];
        TheDim1:=TheResol!.dimension(jRank);
        TheDim2:=TheResol!.dimension(jRank-1);
        TheMatRES:=FuncSignedMatrix(TheResol, iRank, jRank, iFace);
        for iLine in [1..TheDim1]
        do
          TheMat.TheMat[PrevVal1+iLine]{[PrevVal2+1..PrevVal2+TheDim2]}:=TheMatRES.TheMat[iLine];
#          for iCol in [1..TheDim2]
#          do
#            TheMat.TheMat[PrevVal1+iLine][PrevVal2+iCol]:=TheMatRES.TheMat[iLine][iCol];
#          od;
        od;
        PrevVal1:=PrevVal1+TheDim1;
        PrevVal2:=PrevVal2+TheDim2;
      od;
      TheDoperators[1][iRank+1][jRank+1]:=TheMat;
    od;
  od;
  Print("Computing the d1 operator, first line\n");
  for iRank in [1..kSought+1]
  do
    dimSource:=Length(ListOrbitByRank[iRank+2]);
    dimImg:=Length(ListOrbitByRank[iRank+1]);
    TheMat:=[];
    for iOrbit in [1..dimSource]
    do
      TheImage:=GetZeroVector(dimImg);
      TheBoundary:=ListOrbitByRank[iRank+2][iOrbit].BoundaryImage;
      for iEnt in [1..Length(TheBoundary.ListSign)]
      do
        iFace:=TheBoundary.ListIFace[iEnt];
        eSign:=TheBoundary.ListSign[iEnt];
        eElt:=TheBoundary.ListElt[iEnt];
        Add(TheImage[iFace].ListVal, eSign);
        Add(TheImage[iFace].ListElt, eElt);
      od;
      Add(TheMat, TheImage);
    od;
    TheDoperators[2][iRank+1][1]:=rec(nbLine:=dimSource, nbCol:=dimImg, TheMat:=TheMat);
  od;
  Print("Computing the d1 operator, all lines\n");
  for iRank in [1..kSought+1]
  do
    Print("  iRank=", iRank, "\n");
    LevSearch:=kSought+1-iRank;
    for jRank in [1..LevSearch]
    do
      Print("    jRank=", jRank, "\n");
      TheProd:=MatrixMatrixGmoduleMultiplication(TheDoperators[1][iRank+1][jRank+1], TheDoperators[2][iRank+1][jRank]);
      TheOpp:=MatrixGmoduleOpposite(TheProd);
      NewMat:=List(TheOpp.TheMat, x->SpaceCoHomotopyFunction(iRank-1, jRank-1, x));
      TheDoperators[2][iRank+1][jRank+1]:=rec(nbLine:=MatrixOfDim[iRank+1][jRank+1], nbCol:=MatrixOfDim[iRank][jRank+1], TheMat:=NewMat);
    od;
  od;
  Print("Now checking the relation d_0 d_1 + d_1 d_0=0\n");
  for iRank in [1..kSought]
  do
    for jRank in [1..kSought]
    do
      if iRank+jRank<=kSought+1 then
        dimSource:=MatrixOfDim[iRank+1][jRank+1];
        dimImg:=MatrixOfDim[iRank][jRank];
        SumMat:=GetZeroMatrix(dimSource, dimImg);
        TheProd:=MatrixMatrixGmoduleMultiplication(TheDoperators[1][iRank+1][jRank+1], TheDoperators[2][iRank+1][jRank]);
        SumMat:=MatrixGmoduleAddition(SumMat, TheProd);
        TheProd:=MatrixMatrixGmoduleMultiplication(TheDoperators[2][iRank+1][jRank+1], TheDoperators[1][iRank][jRank+1]);
        SumMat:=MatrixGmoduleAddition(SumMat, TheProd);
        if IsZeroGmoduleMatrix(SumMat)=false then
          Print("We have a nonzero element!!!!\n");
          Print(NullMat(5));
        fi;
      fi;
    od;
  od;
  Print("Now computing the others di\n");
  for iD in [2..kSought+1]
  do
    Print("  iD=", iD, "\n");
    for iRank in [iD..kSought+1]
    do
      Print("    iRank=", iRank, "\n");
      LevSearch:=kSought+1-iRank;
      for jRank in [0..LevSearch]
      do
        Print("      jRank=", jRank, "\n");
        dimSource:=MatrixOfDim[iRank+1][jRank+1];
        dimImg:=MatrixOfDim[iRank+1-iD][jRank-1+iD];
        SumOfProds:=GetZeroMatrix(dimSource, dimImg);
        for iH in [0..iD-1]
        do
          if jRank+iH-1 >= 0 then
            TheProd:=MatrixMatrixGmoduleMultiplication(TheDoperators[1+iH][iRank+1][jRank+1], TheDoperators[1+iD-iH][iRank+1-iH][jRank+iH]);
            SumOfProds:=MatrixGmoduleAddition(SumOfProds, TheProd);
          fi;
        od;
        TheOpp:=MatrixGmoduleOpposite(SumOfProds);
        NewMat:=List(TheOpp.TheMat, x->SpaceCoHomotopyFunction(iRank-iD, jRank-2+iD, x));
        TheDoperators[1+iD][iRank+1][jRank+1]:=rec(nbLine:=MatrixOfDim[iRank+1][jRank+1], nbCol:=MatrixOfDim[iRank-iD+1][jRank+iD], TheMat:=NewMat);
      od;
    od;
  od;
  Print("Now computing dimensions\n");
  ListDimensions:=ListWithIdenticalEntries(kSought+3,0);
  ListDimensions[1]:=1;
  for iRank in [0..kSought+1]
  do
    LevSearch:=kSought+1-iRank;
    for jRank in [0..LevSearch]
    do
      ListDimensions[iRank+jRank+2]:=ListDimensions[iRank+jRank+2]+MatrixOfDim[iRank+1][jRank+1];
    od;
  od;
  MatrixBegin:=NullMat(kSought+2, kSought+2);
  for iRank in [0..kSought+1]
  do
    PrevVal:=0;
    for iH1 in [0..iRank]
    do
      iRankImage:=iRank-iH1;
      jRankImage:=iH1;
      MatrixBegin[iRankImage+1][jRankImage+1]:=PrevVal;
      PrevVal:=PrevVal+MatrixOfDim[iRankImage+1][jRankImage+1];
    od;
  od;
  ListMatrixDoperators:=[];
  Add(ListMatrixDoperators, GetZeroMatrix(MatrixOfDim[1][1], 1));
  Print("Summations, Di = d0 + d1 + d2 + ...\n");
  for iRank in [1..kSought+1]
  do
    Print("Computing the D", iRank, " operator\n");
    NewMat:=GetZeroMatrix(ListDimensions[iRank+2],ListDimensions[iRank+1]);
    PrevVal1:=0;
    for iH1 in [0..iRank]
    do
      iRankSource:=iRank-iH1;
      jRankSource:=iH1;
      for iH2 in [0..iRank]
      do
        iRankImage:=iRankSource-iH2;
        jRankImage:=jRankSource-1+iH2;
        if iRankImage>=0 and jRankImage>=0 then
          TheD:=TheDoperators[1+iH2][iRankSource+1][jRankSource+1];
          dimSource:=MatrixOfDim[iRankSource+1][jRankSource+1];
          dimImg:=MatrixOfDim[iRankImage+1][jRankImage+1];
          if TheD.nbLine<>dimSource or TheD.nbCol<>dimImg then
            Print("We are calling wrong matrix, please panic\n");
            Print(NullMat(5));
          fi;
          PrevVal2:=MatrixBegin[iRankImage+1][jRankImage+1];
          for iLine in [1..dimSource]
          do
            for iCol in [1..dimImg]
            do
              NewMat.TheMat[PrevVal1+iLine][PrevVal2+iCol]:=TheD.TheMat[iLine][iCol];
            od;
          od;
        fi;
      od;
      PrevVal1:=PrevVal1+MatrixOfDim[iRankSource+1][jRankSource+1];
    od;
    Add(ListMatrixDoperators, NewMat);
  od;
  # the obtained resolution is NOT twisted, the
  # kernel is the set $S$
  # x=sum alpha_g g    with   sum alpha_g=0
  IsInKernel:=function(TheVector,jRank)
    local eVal, TheProd;
    if jRank=0 then
      eVal:=TheVector[1];
      return Sum(eVal.ListVal)=0;
    else
      TheProd:=VectorMatrixGmoduleMultiplication(TheVector, ListMatrixDoperators[jRank+1]);
      return IsZeroGmoduleVector(TheProd);
    fi;
  end;
  TheHomotopy:=function(TheVector,iRank)
    local ThePreImage, ListVectorComponents, iH, iRankSource, jRankSource, TheDim, TheBegin, TheReturn, iRankPre, jRankPre, iH2, TheImg, TheProd, test;
    ListVectorComponents:=[];
    for iH in [0..iRank]
    do
      iRankSource:=iRank-iH;
      jRankSource:=iH;
      TheDim:=MatrixOfDim[iRankSource+1][jRankSource+1];
      TheBegin:=MatrixBegin[iRankSource+1][jRankSource+1];
      Add(ListVectorComponents, TheVector{[TheBegin+1..TheBegin+TheDim+1]});
    od;
    TheReturn:=[];
    for iH in [0..iRank+1]
    do
      iRankPre:=iRank+1-iH;
      jRankPre:=iH;
      if iH=0 then
        ThePreImage:=PolyhedralInformation.TheHomotopy(ListVectorComponents[1], iRank);
      else
        ThePreImage:=SpaceCoHomotopyFunction(iRank-(iH-1), iH-1, ListVectorComponents[iH]);
      fi;
      Append(TheReturn, ThePreImage);
      for iH2 in [0..iRank+1]
      do
        iRankImage:=iRank+1-iH2;
        jRankImage:=iH2-1;
        if iRankImage>=0 and jRankImage>=0 then
          TheImg:=VectorMatrixGmoduleMultiplication(ThePreImage, TheDoperators[iH2+1][iRankPre+1][jRankPre+1]);
          ListVectorComponents[jRankImage+1]:=VectorGmoduleAddition(ListVectorComponents[jRankImage+1], VectorGmoduleOpposite(TheImg));
        fi;
      od;
    od;
    TheProd:=VectorMatrixGmoduleMultiplication(TheReturn, ListMatrixDoperators[iRank+1]);
    test:=IsEqualGmoduleVector(TheProd, TheVector);
    if test=false then
      Print("Non correct homotopy computation CTC wall, please panic\n");
      Print(NullMat(5));
    fi;
    return TheReturn;
  end;
  return ListMatrixDoperators;
end;



Method1AutomGroupEdgeColoredGraph:=function(DistMatrix, SetV)
  local nbV, Grp, iDist, eDist, Gra, iExt, jExt, IsAnAuto\morphismGroup, ListRank, ListOrdered, SetRank, Pos, i, j, u;
  nbV:=Length(DistMatrix);
  SetV:=__SetValue(DistMatrix);
  IsAnAutomorphismGroup:=function(GRP)
    local eGen, i, j, d1, d2;
    for eGen in GeneratorsOfGroup(GRP)
    do
      for i in [1..nbV-1]
      do
        for j in [i+1..nbV]
        do
          d1:=DistMatrix[i][j];
          d2:=DistMatrix[OnPoints(i, eGen)][OnPoints(j, eGen)];
          if d1<>d2 then
            return false;
          fi;
        od;
      od;
    od;
    return true;
  end;
  ListRank:=ListWithIdenticalEntries(Length(SetV), 0);
  for i in [1..nbV-1]
  do
   for j in [i+1..nbV]
    do
      Pos:=Position(SetV, DistMatrix[i][j]);
      ListRank[Pos]:=ListRank[Pos]+1;
    od;
  od;
  SetRank:=Reversed(Set(ListRank));
  ListOrdered:=[];
  for u in SetRank
  do
    for i in [1..Length(SetV)]
    do
      if ListRank[i]=u then
        Add(ListOrdered, i);
      fi;
    od;
  od;
  for iDist in [1..Length(ListOrdered)]
  do
    eDist:=SetV[ListOrdered[iDist]];
    if iDist>1 then
      if IsAnAutomorphismGroup(Grp)=true then
        return Grp;
      fi;
    fi;
    Gra:=NullGraph(Group(()), nbV);
    for iExt in [1..nbV-1]
    do
      for jExt in [iExt+1..nbV]
      do
        if DistMatrix[iExt][jExt]=eDist then
          AddEdgeOrbit(Gra, [iExt, jExt]);
          AddEdgeOrbit(Gra, [jExt, iExt]);
        fi;
      od;
    od;
    if iDist=1 then
      Grp:=AutGroupGraph(Gra);
    else
      Grp:=Intersection(Grp, AutGroupGraph(Gra));
    fi;
  od;
  return Grp;
end;


#
#
# The API of this function has changed.
# the function is now simpler and takes as argument
# two distance matrices.
# if they are not isomorphic, it return false.
# otherwise, it returns a list [....]
# where the element in i-th position is the position of
# the i-th vertex of DM1 in DM2.
Method1EquivalenceEdgeColoredGraph:=function(DistMatrix1, DistMatrix2, SetV)
  local GRP, nbV, IsGeneratorOk, IsThereAnIsomorphism, IsAnAutomorphismGroup, iDist, eDist, i, j, Gra, test, Isom;
  if Length(DistMatrix1)<>Length(DistMatrix2) then
    return false;
  fi;
  nbV:=Length(DistMatrix1);
  IsGeneratorOk:=function(eGen)
    local i, j, d1, d2, Val1, Val2, nbChg;
    for i in [1..nbV-1]
    do
      for j in [i+1..nbV]
      do
        d1:=DistMatrix1[i][j];
        Val1:=OnPoints(i, eGen);
        nbChg:=0;
        if Val1>nbV then
          Val1:=Val1-nbV;
          nbChg:=nbChg+1;
        fi;
        Val2:=OnPoints(j, eGen);
        if Val2>nbV then
          nbChg:=nbChg+1;
          Val2:=Val2-nbV;
        fi;
        if nbChg=1 then
          return false;
        fi;
        if nbChg=0 then
          d2:=DistMatrix1[Val1][Val2];
        else
          d2:=DistMatrix2[Val1][Val2];
        fi;
        if d1<>d2 then
          return false;
        fi;
      od;
    od;
    return true;
  end;
  IsThereAnIsomorphism:=function(GRP)
    local eGen, test, i;
    for eGen in GeneratorsOfGroup(GRP)
    do
      test:=true;
      for i in [1..nbV]
      do
        if OnPoints(i, eGen)<=nbV then
          test:=false;
        fi;
      od;
      if test=true then
        if IsGeneratorOk(eGen)=true then
          return eGen;
        fi;
      fi;
    od;
    return false;
  end;
  IsAnAutomorphismGroup:=function(GRP)
    local eGen, i;
    for eGen in GeneratorsOfGroup(GRP)
    do
      if IsGeneratorOk(eGen)=false then
        return false;
      fi;
    od;
    return true;
  end;
  for iDist in [1..Length(SetV)]
  do
    Gra:=NullGraph(Group(()), 2*nbV);
    eDist:=SetV[iDist];
    for i in [1..nbV-1]
    do
      for j in [i+1..nbV]
      do
        if DistMatrix1[i][j]=eDist then
          AddEdgeOrbit(Gra, [i,j]);
          AddEdgeOrbit(Gra, [j,i]);
        fi;
        if DistMatrix2[i][j]=eDist then
          AddEdgeOrbit(Gra, [nbV+i, nbV+j]);
          AddEdgeOrbit(Gra, [nbV+j, nbV+i]);
        fi;
      od;
    od;
    if iDist=1 then
      GRP:=AutGroupGraph(Gra);
    else
      GRP:=Intersection(GRP, AutGroupGraph(Gra));
    fi;
    test:=IsThereAnIsomorphism(GRP);
    if test<>false then
      Isom:=[];
      for i in [1..nbV]
      do
        Isom[i]:=OnPoints(i, test)-nbV;
      od;
      return Isom;
    fi;
    if IsAnAutomorphismGroup(GRP)=true then
      return false;
    fi;
  od;
  Print("Should never reach that stage\n");
  Print(NullMat(5));
  return false;
end;



Method2partition:=function(k,n)
  local ThePartition, i;
  ThePartition:=[];
  for i in [1..k]
  do
    Add(ThePartition, [n*(i-1)+1..n*(i-1)+n]);
  od;
  return ThePartition;
end;



Method2modelEdgeColoredGraph:=function(DistMat, SetV)
  local k, n, iVert, jVert, i, j, eVal, GR;
  k:=Length(SetV);
  n:=Length(DistMat);
  GR:=NullGraph(Group(()), k*n);
  for iVert in [1..n]
  do
    for i in [1..k-1]
    do
      for j in [i+1..k]
      do
        AddEdgeOrbit(GR, [n*(i-1)+iVert, n*(j-1)+iVert]);
        AddEdgeOrbit(GR, [n*(j-1)+iVert, n*(i-1)+iVert]);
      od;
    od;
  od;
  for i in [1..Length(SetV)]
  do
    eVal:=SetV[i];
    for iVert in [1..n-1]
    do
      for jVert in [iVert+1..n]
      do
        if DistMat[iVert][jVert]=eVal then
          AddEdgeOrbit(GR, [n*(i-1)+iVert, n*(i-1)+jVert]);
          AddEdgeOrbit(GR, [n*(i-1)+jVert, n*(i-1)+iVert]);
        fi;
      od;
    od;
  od;
  return GR;
end;



Method2AutomGroupEdgeColoredGraph:=function(DistMat, SetV)
  local TheGraph, ThePartition, k, n, GRP;
  k:=Length(SetV);
  n:=Length(DistMat);
  TheGraph:=Method2modelEdgeColoredGraph(DistMat, SetV);
  ThePartition:=Method2partition(k,n);
  GRP:=SymmetryGroupVertexColoredGraph(TheGraph, ThePartition);
  return SecondReduceGroupAction(GRP, [1..n]);
end;





Method2EquivalenceEdgeColoredGraph:=function(DistMat1, DistMat2, SetV)
  local k, n, TheGraph1, TheGraph2, ThePartition, TheEquiv;
  k:=Length(SetV);
  n:=Length(DistMat1);
  TheGraph1:=Method2modelEdgeColoredGraph(DistMat1, SetV);
  TheGraph2:=Method2modelEdgeColoredGraph(DistMat2, SetV);
  ThePartition:=Method2partition(k,n);
  TheEquiv:=EquivalenceVertexColoredGraph(TheGraph1, TheGraph2, ThePartition);
  if TheEquiv=false then
    return false;
  fi;
  return TheEquiv{[1..n]};
end;



Method2CanonicalStringEdgeColoredGraph:=function(DistMat, SetV)
  local k, n, TheGraph, ThePartition, CanonDesc;
  k:=Length(SetV);
  n:=Length(DistMat);
  TheGraph:=Method2modelEdgeColoredGraph(DistMat, SetV);
  ThePartition:=Method2partition(k,n);
  CanonDesc:=CanonicalRepresentativeVertexColoredGraph(TheGraph, ThePartition);
  return __GetGraph6Expression(CanonDesc);
end;



Method3partition:=function(k,n)
  local ThePartition, i, NBV;
  NBV:=n*(n-1)/2;
  ThePartition:=[[1..NBV]];
  for i in [1..k]
  do
    Add(ThePartition, [NBV+i]);
  od;
  return ThePartition;
end;


Method3modelEdgeColoredGraph:=function(DistMat, SetV)
  local k, n, NBV, i, j, GR, LSET, Pos1, Pos2, eVal;
  k:=Length(SetV);
  n:=Length(DistMat);
  NBV:=n*(n-1)/2;
  GR:=NullGraph(Group(()), NBV+k);
  LSET:=[];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(LSET, [i,j]);
    od;
  od;
  for i in [1..NBV-1]
  do
    for j in [i+1..NBV]
    do
      if Length(Intersection(LSET[i], LSET[j]))=1 then
        AddEdgeOrbit(GR, [i,j]);
        AddEdgeOrbit(GR, [j,i]);
      fi;
    od;
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      eVal:=DistMat[i][j];
      Pos1:=Position(SetV, eVal);
      Pos2:=Position(LSET, [i,j]);
      AddEdgeOrbit(GR, [Pos2, NBV+Pos1]);
      AddEdgeOrbit(GR, [NBV+Pos1, Pos2]);
    od;
  od;
  return GR;
end;




Method3AutomGroupEdgeColoredGraph:=function(DistMat, SetV)
  local TheGraph, ThePartition, k, n, GRP;
  k:=Length(SetV);
  n:=Length(DistMat);
  TheGraph:=Method3modelEdgeColoredGraph(DistMat, SetV);
  ThePartition:=Method3partition(k,n);
  GRP:=SymmetryGroupVertexColoredGraph(TheGraph, ThePartition);
  return TranslateGroup(GRP, Method3EnumerationListSet(n), OnSets);
end;

Method3CanonicalStringEdgeColoredGraph:=function(DistMat, SetV)
  local k, n, TheGraph, ThePartition, CanonDesc;
  k:=Length(SetV);
  n:=Length(DistMat);
  TheGraph:=Method3modelEdgeColoredGraph(DistMat, SetV);
  ThePartition:=Method3partition(k,n);
  CanonDesc:=CanonicalRepresentativeVertexColoredGraph(TheGraph, ThePartition);
  return __GetGraph6Expression(CanonDesc);
end;

Method3EquivalenceEdgeColoredGraph:=function(DistMat1, DistMat2, SetV)
  local k, n, TheGraph1, TheGraph2, ThePartition, TheEquiv;
  k:=Length(SetV);
  n:=Length(DistMat1);
  TheGraph1:=Method3modelEdgeColoredGraph(DistMat1, SetV);
  TheGraph2:=Method3modelEdgeColoredGraph(DistMat2, SetV);
  ThePartition:=Method3partition(k,n);
  TheEquiv:=EquivalenceVertexColoredGraph(TheGraph1, TheGraph2, ThePartition);
  if TheEquiv=false then
    return false;
  fi;
  return TranslateElement(PermList(TheEquiv), Method3EnumerationListSet(n), OnSets);
end;






#EnumerateMatroidsFromFreeVectors:=function(DataLattice, BeltFreeInformations)
#  local n, GRPanti, O, ListVectVoronoiRep, nbRep, ListVoronoiGensAnti, eGen, eList, ListTotalSixBelt, PermGRPvoronoiAnti, eOrbit, TheOrb, ListQuasi4belt, pos, ListIneq, ListIneqRep, ListIneqRepB, EXT, eRep1, eRep2, eRep1b, ListEXTselect1, ListEXTselect2, TestCorrectness, eSetFree1, eSetFree2, eFreeVect, ListFreeVector, TheVectSpace2, TheVectSpace1, GramMat, ListVectVoronoi, FreeInformations;
#  n:=DataLattice.n;
#  GramMat:=DataLattice.GramMat;
#  FreeInformations:=BeltFreeInformations.FuncGetAllFreeVectors();
#  ListQuasi4belt:=[];
#  for eOrbit in __RepresentativeOrbitTwoSet(BeltFreeInformations.VectorPres.GRPperm, [1..Length(BeltFreeInformations.VectorPres.ListVectRed)])
#  do
#    pos:=First(BeltFreeInformations.ListBelt, x->IsSubset(x, eOrbit)=true);
#    if pos=fail then
#      Add(ListQuasi4belt, eOrbit);
#    fi;
#  od;
#  ListVectVoronoiRep:=BeltFreeInformations.VectorPres.ListVectRed;
#  ListVectVoronoi:=Concatenation(ListVectVoronoiRep, -ListVectVoronoiRep);
#  ListIneq:=List(ListVectVoronoi, x->Concatenation([1], -2*x*GramMat));
#  ListIneqRep:=List(ListVectVoronoiRep, x->Concatenation([1], -2*x*GramMat));
#  ListIneqRepB:=List(ListVectVoronoiRep, x->Concatenation([1], 2*x*GramMat));
#  EXT:=DualDescription(ListIneq);
#  for eOrbit in ListQuasi4belt
#  do
#    eRep1:=ListIneqRep[eOrbit[1]];
#    eRep1b:=ListIneqRepB[eOrbit[1]];
#    eRep2:=ListIneqRep[eOrbit[2]];
#    ListEXTselect1:=Filtered(EXT, x->x*(eRep1+eRep2)=0);
#    ListEXTselect2:=Filtered(EXT, x->x*(eRep1b+eRep2)=0);
#    TestCorrectness:=function(ListEXTselect, eFreeVect)
#      local eVect, TheSubspace, NSP, EXTselection, ListIncd, pos;
#      eVect:=ListEXTselect[1]+Concatenation([0], eFreeVect);
#      TheSubspace:=Concatenation(ListEXTselect, eVect);
#      if SolutionMat(TheSubspace, eVect)<>fail then
#        return false;
#      fi;
#      NSP:=NullspaceMat(TransposedMat(TheSubspace));
#      EXTselection:=Filtered(EXT, x->First(NSP, y->y*x<>0)=fail);
#      if IsSubset(Set(ListEXTselect), Set(EXTselection))=false then
#        Print("Please solve the bug\n");
#        Print(NullMat(5));
#      fi;
#      if Set(ListEXTselect)<>Set(EXTselection) then
#        return false;
#      fi;
#      ListIncd:=Filtered(ListIneq, x->First(ListEXTselect, y->y*x<>0)=fail);
#      pos:=First(ListIncd, x->x*eVect<0);
#      if pos<>fail then
#        return true;
#      fi;
#      return false;
#    end;
#    eSetFree1:=[];
#    eSetFree2:=[];
#    TheVectSpace1:=RowReduction(List(ListEXTselect1, x->x{[2..n+1]}-ListEXTselect1[1]{[2..n+1]})).EXT;
#    TheVectSpace2:=RowReduction(List(ListEXTselect2, x->x{[2..n+1]}-ListEXTselect2[1]{[2..n+1]})).EXT;
#    for eFreeVect in ListFreeVector
#    do
#      if TestCorrectness(ListEXTselect1, eFreeVect)=true then
#        Add(eSetFree1, eFreeVect);
#      fi;
#      if TestCorrectness(ListEXTselect2, eFreeVect)=true then
#        Add(eSetFree2, eFreeVect);
#      fi;
#    od;
#  od;
#end;



DoFlipping_V1:=function(SHVgroups, TheSubset)
  local SHV, eGroup, n, TheGramPerf, MinPerf, ListSymm, eSol, FacetMat, i, lambdaPar, TheLowVect, SHVwork, val1, val2, GramMatNew, SHVnew;
  SHV:=[];
  for eGroup in SHVgroups
  do
    Append(SHV, eGroup);
  od;
  n:=Length(SHV[1]);
  TheGramPerf:=GetCorrespondingPerfectForm(SHV);
  MinPerf:=SHV[1]*TheGramPerf*SHV[1];
  ListSymm:=List(SHVgroups, x->SymmetricMatrixToVector(TransposedMat([x[1]])*[x[1]]));
  eSol:=__FindFacetInequality(ListSymm, TheSubset);
  FacetMat:=VectorToSymmetricMatrix(eSol, n);
  for i in [1..n]
  do
    FacetMat[i][i]:=2*FacetMat[i][i];
  od;
  lambdaPar:=1;
  while(true)
  do
    GramMatNew:=TheGramPerf+lambdaPar*FacetMat;
    if IsPositiveDefiniteSymmetricMatrix(GramMatNew)=false then
      break;
    fi;
    SHVnew:=ShortestVectorDutourVersion(GramMatNew);
    if IsSubset(Set(SHV), Set(SHVnew))=false then
      break;
    fi;
    lambdaPar:=lambdaPar*2;
  od;
  while(true)
  do
    TheLowVect:=GRAM_GetALowVector(GramMatNew);
    if TheLowVect*GramMatNew*TheLowVect=MinPerf then
      return RemoveFractionMatrix(GramMatNew);
    fi;
    val1:=TheLowVect*TheGramPerf*TheLowVect;
    val2:=TheLowVect*FacetMat*TheLowVect;
    lambdaPar:=(MinPerf-val1)/val2;
    Print("lambdaPar=", lambdaPar, "\n");
    GramMatNew:=TheGramPerf+lambdaPar*FacetMat;
  od;
end;



OrthogonalProjectionOnTspace:=function(TheBasis, TheQuadForm)
  local DimSpace, TheScalMat, i, j, eScal, ListScal, ListCoef;
  DimSpace:=Length(TheBasis);
  TheScalMat:=NullMat(DimSpace, DimSpace);
  for i in [1..DimSpace]
  do
    for j in [1..DimSpace]
    do
      eScal:=Trace(TheBasis[i]*TheBasis[j]);
      TheScalMat[i][j]:=eScal;
    od;
  od;
  ListScal:=List(TheBasis, x->Trace(x*TheQuadForm));
  ListCoef:=ListScal*Inverse(TheScalMat);
  return ListCoef;
end;





#
#
DoDualizationOperation:=function(TheBound)
  local NewFuncSignatureDet, NewListOrbitByRank, len, iRank, nbOrb, NewListOrbit, iOrbit, eRec, nbOrbP1, iOrbP1, iFace, pos, lenBound, ListStatus, ListStatusAdjacency, TheStabFace, TheConjStab, TheStabTot, IsFinished, ListStatusOrbit, vElt, eGen, jBound, eElt, iBound, TheStab;
  NewFuncSignatureDet:=function(iRank, iOrbit, eElt)
    return TheBound.FuncSignatureTotal(eElt)*TheBound.FuncSignatureDet(iRank, iOrbit, eElt);
  end;
  NewListOrbitByRank:=[];
  len:=Length(TheBound.ListOrbitByRank)-2;
  for iRank in [1..len]
  do
    nbOrb:=Length(TheBound.ListOrbitByRank[iRank+1]);
    NewListOrbit:=[];
    for iOrbit in [1..nbOrb]
    do
      eRec:=rec(TheStab:=TheBound.ListOrbitByRank[iRank+1][iOrbit], BoundaryImage:=rec(ListIFace:=[], ListSign:=[], ListElement:=[]));
      Add(NewListOrbit, eRec);
    od;
    nbOrbP1:=Length(TheBound.ListOrbitByRank[iRank+2]);
    ListOrbits:=[];
    for iOrbP1 in [1..nbOrbP1]
    do
      lenBound:=Length(TheBound.ListOrbitByRank[iRank+2][iOrbP1].BoundaryImage.ListIFace);
      ListStatus:=ListWithIdenticalEntries(lenBound,1);
      ListStatusAdjacency:=ListWithIdenticalEntries(lenBound,1);
      for iBound in [1..lenBound]
      do
        if ListStatus[iBound]=1 then
          ListStatusOrbit:=ListWithIdenticalEntries(lenBound,1);
          iFace:=TheBound.ListOrbitByRank[iRank+2][iOrbP1].BoundaryImage.ListIFace[iBound];
          TheStabFace:=TheBound.ListOrbitByRank[iRank+1][iFace].TheStab;
          eElt:=TheBound.ListOrbitByRank[iRank+2][iOrbP1].BoundaryImage.ListElement[iBound];
          TheConjStab:=ConjugateGroup(TheStabFace, eElt);
          TheStabTot:=TheBound.ListOrbitByRank[iRank+2][iOrbP1].TheStab;
          TheStab:=Intersection(TheStabTot, TheConjStab);
          Add(ListOrbits, rec(iOrbP1:=iOrbP1, iBound:=iBound, iFace:=iFace));
          ListStatusOrbit[iBound]:=1;
          FindPosition:=function(iFace, vElt)
            local iBound, eElt, eQuot;
            for iBound in [1..lenBound]
            do
              if TheBound.ListOrbitByRank[iRank+2][iOrbP1].BoundaryImage.ListIFace[iBound]=iFace then
                eElt:=TheBound.ListOrbitByRank[iRank+2][iOrbP1].BoundaryImage.ListElement[iBound];
                eQuot:=vElt*Inverse(eElt);
                if eQuot in TheBound.ListOrbitByRank[iRank+1][iFace].MatrixStab then
                  return iBound;
                fi;
              fi;
            od;
          end;
          while(true)
          do
            IsFinished:=true;
            for jBound in [1..lenBound]
            do
              if ListStatusOrbit[jBound]=1 and ListStatusAdjacency[jBound]=0 then
                IsFinished:=false;
                ListStatusAdjacency[jBound]:=1;
                for eGen in GeneratorsOfGroup(TheStabTot)
                do
                  vElt:=TheBound.ListOrbitByRank[iRank+2][iOrbP1].BoundaryImage.ListElement[jBound]*eGen;
                  pos:=FindPosition(iFace, vElt);
                  ListStatus[pos]:=1;
                  ListStatusOrbit[pos]:=1;
                od;
              fi;
            od;
            if IsFinished=true then
              break;
            fi;
          od;
        fi;
      od;
    od;
    Add(NewListOrbitByRank, NewListOrbit);
  od;
  return rec(ListOrbitByRank:=NewListOrbitByRank, FuncSignatureDet:=NewFuncSignatureDet);
end;




RandomVertex:=function(FAC)
  local n, nMax, IneqV, i, LinProg, Lincd, eFAC;
  n:=Length(FAC[1]);
  nMax:=10;
  while(true)
  do
    IneqV:=[];
    for i in [1..n]
    do
      Add(IneqV, Random([-nMax..nMax]));
    od;
    LinProg:=LinearProgramming(FAC, IneqV);
    Lincd:=[];
    for eFAC in FAC
    do
      if eFAC*LinProg.Vector=0 then
        Add(Lincd, eFAC);
      fi;
    od;
    if RankMat(Lincd)=n-1 then
      return LinProg.Vector;
    fi;
  od;
end;


# thank for the help of F. Vallentin!
RandomFacet:=function(EXT)
  local BaryEXT, NewEXT, n, nMax, iExt, eNewEXT, eEXT, IneqV, i, LinProg, Lincd, NewLincd, NSP, NewNSP, IsNeg, H, eV;
  n:=Length(EXT[1]);
  BaryEXT:=Sum(EXT)/Length(EXT);
  NewEXT:=[];
  nMax:=10;
  for eEXT in EXT
  do
    H:=[1];
    eV:=eEXT-BaryEXT;
    Append(H, eV{[2..n]});
    Add(NewEXT, H);
  od;
  while(true)
  do
    IneqV:=[];
    for i in [1..n]
    do
      Add(IneqV, Random([-nMax..nMax]));
    od;
    LinProg:=LinearProgramming(NewEXT, IneqV);
    NewLincd:=[];
    Lincd:=[];
    for iExt in [1..Length(NewEXT)]
    do
      eNewEXT:=NewEXT[iExt];
      eEXT:=EXT[iExt];
      if eNewEXT*LinProg.Vector=0 then
        Add(NewLincd, eNewEXT);
        Add(Lincd, eEXT);
      fi;
    od;
    if RankMat(NewLincd)=n-1 then
      NSP:=NullspaceMat(TransposedMat(Lincd))[1];
      NewNSP:=RemoveFraction(NSP);
      IsNeg:=false;
      for eEXT in EXT
      do
        if NewNSP*eEXT<0 then
          IsNeg:=true;
        fi;
      od;
      if IsNeg=true then
        return -NewNSP;
      else
        return NewNSP;
      fi;
    fi;
  od;
end;




FileGetList:=Filename(DirectoriesPackagePrograms("polyhedral"),"GetLists.prog");

GetListPermGens:=function(ListVectRat, ListGens)
  local ListVect, FileMeta, FileVect, FileMatrix, FileOutput, output, NewListGens, eGen, eList;
  FileMeta:=Filename(POLYHEDRAL_tmpdir,"GetList.meta");
  FileVect:=Filename(POLYHEDRAL_tmpdir,"GetList.vect");
  FileMatrix:=Filename(POLYHEDRAL_tmpdir,"GetList.mat");
  FileOutput:=Filename(POLYHEDRAL_tmpdir,"GetList.out");
  RemoveFileIfExist(FileMeta);
  RemoveFileIfExist(FileVect);
  RemoveFileIfExist(FileMatrix);
  RemoveFileIfExist(FileOutput);
  #
  ListVect:=RemoveFractionMatrix(ListVectRat);
  #
  output:=OutputTextFile(FileMeta, true);
  AppendTo(output, Length(ListVect[1]), " ", Length(ListVect), "\n");
  CloseStream(output);
  #
  output:=OutputTextFile(FileVect, true);
  WriteMatrix(output, ListVect);
  CloseStream(output);
  Print("nbGen=", Length(ListGens), "  nbVector=", Length(ListVect), "\n");
  Print("Vector and meta files created\n");
  #
  NewListGens:=[];
  for eGen in ListGens
  do
    output:=OutputTextFile(FileMatrix, true);
    WriteMatrix(output, eGen);
    CloseStream(output);
    Exec(FileGetList, " ", FileMeta, " ", FileVect, " ", FileMatrix, " ", FileOutput);
    eList:=ReadAsFunction(FileOutput)();
    Add(NewListGens, PermList(eList));
    RemoveFile(FileMatrix);
  od;
  RemoveFile(FileMeta);
  RemoveFile(FileVect);
  RemoveFile(FileMatrix);
  RemoveFile(FileOutput);
  return NewListGens;
end;



__DualDescriptionLRS_splitter:=function(EXT, GroupExt, ThePath)
  local eSub, EXT2, FileExt, FileName, LRE, FilePrefix, FileLog, output, LPFAC, eFac, RPL, idxfile, DimEXT, test, EXTnew, FileInfo;
#  Print("Entering polyhedral function LRS_splitter |GRP|=", Order(GroupExt), "\n");
  FileExt:=Concatenation(ThePath, "Project.ext");
  FileLog:=Concatenation(ThePath, "Project.log");
  RemoveFileIfExist(FileExt);
  RemoveFileIfExist(FileLog);
  output:=OutputTextFile(FileExt, true);;
  eSub:=__ProjectionFrame(EXT);
  EXT2:=List(EXT, x->x{eSub});
  if TestConicness(EXT2) then
    EXTnew:=ShallowCopy(EXT2);
  else
    EXTnew:=List(EXT2, x->Concatenation([0], x));
  fi;
  DimEXT:=Length(EXTnew[1]);
  #
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", DimEXT, " integer\n");
  WriteMatrix(output, EXTnew);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  FilePrefix:=Concatenation(ThePath, "SSplit");
  Exec(FileGLRS, " ", FileExt, " | grep -v '*' > ", FileLog);
  Exec(FileNudifyLRS_splitter, " ", FilePrefix, " 100000 < ", FileLog);
  RemoveFile(FileExt);
  RemoveFile(FileLog);
  #
  FileInfo:=Concatenation(FilePrefix, "0");
  LRE:=ReadAsFunction(FileInfo)();
  RemoveFile(FileInfo);
#  Print("Found ", LRE[3], " objects (extreme ray, vertices, or facet)\n");

  RPL:=OnSetsGroupFormalism().OrbitGroupFormalism(EXT, GroupExt, "/irrelevant/", false);
  for idxfile in [1..LRE[1]]
  do
    FileName:=Concatenation(FilePrefix, String(idxfile));
    LPFAC:=ReadAsFunction(FileName)();
    for eFac in LPFAC
    do
      RPL.FuncInsert(Filtered([1..Length(EXTnew)], x->EXTnew[x]*eFac=0));
    od;
    RemoveFile(FileName);
#    Print("Block ", idxfile, " done\n");
  od;
#  Print(" Exiting the polyhedral computation\n");
  return RPL.FuncListOrbitIncidence();
end;




__DualDescriptionPD_splitter:=function(EXT, GroupExt, ThePath)
  local FileExt, FileLog, FilePrefix, output, LRE, RPL, idxfile, FileName, LPFAC, eFac, FileInfo, DimEXT, EXT2, EXTnew, eSub;
  Print("Entering polyhedral function PD_splitter |GRP|=", Order(GroupExt), "\n");
  FileExt:=Filename(ThePath, "PDrun.ext");
  FileLog:=Filename(ThePath, "PDrun.log");
  RemoveFileIfExist(FileExt);
  RemoveFileIfExist(FileLog);
  #
  eSub:=__ProjectionFrame(EXT);
  EXT2:=List(EXT, x->x{eSub});
  if TestConicness(EXT2) then
    EXTnew:=ShallowCopy(EXT2);
  else
    EXTnew:=List(EXT2, x->Concatenation([0], x));
  fi;
  DimEXT:=Length(EXTnew[1]);
  #
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXTnew), " ", DimEXT, " integer\n");
  WriteMatrix(output, EXTnew);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  FilePrefix:=Concatenation(ThePath, "SSplit");
  Exec(FilePD, " ", FileExt, " | grep -v '*' > ", FileLog);
  Exec(FileNudifyLRS_splitter, " ", FilePrefix, " 100000 < ", FileLog);
  RemoveFile(FileExt);
  RemoveFile(FileLog);
  #
  FileInfo:=Concatenation(FilePrefix, "0");
  LRE:=ReadAsFunction(FileInfo)();
  RemoveFile(FileInfo);
  Print("Found ", LRE[3], " objects (extreme ray, vertices, or facet)\n");
  #
  RPL:=OnSetsGroupFormalism().OrbitGroupFormalism(EXT, GroupExt, "/irrelevant/", false);
  for idxfile in [1..LRE[1]]
  do
    FileName:=Concatenation(FilePrefix, String(idxfile));
    LPFAC:=ReadAsFunction(FileName)();
    for eFac in LPFAC
    do
      RPL.FuncInsert(Filtered([1..Length(EXTnew)], x->EXTnew[x]*eFac=0));
    od;
    RemoveFile(FileName);
    Print("Block ", idxfile, " done\n");
  od;
  return RPL.FuncListOrbitIncidence();
end;










__DualDescriptionCDD_splitter:=function(EXT, GroupExt, ThePath)
  local FileExt, FileIne, FileLog, FileDdl, output, LPFAC, FileName, RPL, eFac, LRE, idxfile, FilePrefix, FileInfo, EXT2, EXTnew, eSub, DimEXT;
  Print("Entering polyhedral function CDD_splitter |GRP|=", Order(GroupExt), "\n");
  FileExt:=Concatenation(ThePath, "Project.ext");
  FileIne:=Concatenation(ThePath, "Project.ine");
  FileLog:=Concatenation(ThePath, "Project.log");
  FileDdl:=Concatenation(ThePath, "Project.ddl");
  FilePrefix:=Concatenation(ThePath, "SSplit");
  RemoveFileIfExist(FileExt);
  RemoveFileIfExist(FileIne);
  RemoveFileIfExist(FileLog);
  RemoveFileIfExist(FileDdl);
  #
  eSub:=__ProjectionFrame(EXT);
  EXT2:=List(EXT, x->x{eSub});
  if TestConicness(EXT2) then
    EXTnew:=ShallowCopy(EXT2);
  else
    EXTnew:=List(EXT2, x->Concatenation([0], x));
  fi;
  DimEXT:=Length(EXTnew[1]);
  #
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", DimEXT, " integer\n");
  WriteMatrix(output, EXTnew);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  Exec(FileLCDD, " ", FileExt, " 2> ", FileLog, " > ", FileIne);
  Exec(FileNudifyCDD_splitter, " ", FilePrefix, " 100000 ", FileIne);
  RemoveFile(FileExt);
  RemoveFile(FileIne);
  RemoveFile(FileLog);
  RemoveFile(FileDdl);
  #
  FileInfo:=Concatenation(FilePrefix, "0");
  LRE:=ReadAsFunction(FileInfo)();
  RemoveFile(FileInfo);
  Print("Found ", LRE[3], " objects\n");
  #
  RPL:=OnSetsGroupFormalism().OrbitGroupFormalism(EXT, GroupExt, "/irrelevant/", false);
  for idxfile in [1..LRE[1]]
  do
    FileName:=Concatenation(FilePrefix, String(idxfile));
    LPFAC:=ReadAsFunction(FileName)();
    for eFac in LPFAC
    do
      RPL.FuncInsert(Filtered([1..Length(EXTnew)], x->EXTnew[x]*eFac=0));
    od;
    RemoveFile(FileName);
    Print("Block ", idxfile, " done\n");
  od;
  return RPL.FuncListOrbitIncidence();
end;


__DualDescriptionCDD:=function(EXT, GroupExt)
  local FileExt, FileIne, FileLog, FileDdl, FileIneNude, output, LPFAC, RPL, eFac;
  Print("Entering polyhedral function CDD |GRP|=", Order(GroupExt), "\n");
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Project.ext");
  FileIne:=Filename(POLYHEDRAL_tmpdir,"Project.ine");
  FileLog:=Filename(POLYHEDRAL_tmpdir,"Project.log");
  FileDdl:=Filename(POLYHEDRAL_tmpdir,"Project.ddl");
  FileIneNude:=Filename(POLYHEDRAL_tmpdir,"Project.ine.Nude");
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", Length(EXT[1]), " integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  CloseStream(output);
  Exec(FileLCDD, " ", FileExt, " 2> ", FileLog, " > ", FileIne);
  Exec(FileNudify, " ", FileIne, " > ", FileIneNude);
  LPFAC:=ReadVectorFile(FileIneNude);
  RemoveFile(FileExt);
  RemoveFile(FileIne);
  RemoveFile(FileLog);
  RemoveFile(FileDdl);
  RemoveFile(FileIneNude);
  RPL:=OnSetsGroupFormalism().OrbitGroupFormalism(EXT, GroupExt, "/irrelevant/", false);
  for eFac in LPFAC
  do
    RPL.FuncInsert(Filtered([1..Length(EXT)], x->EXT[x]*eFac=0));
  od;
  return RPL.FuncListOrbitIncidence();
end;



__DualDescriptionLRS:=function(EXT, GroupExt)
  local LPFAC, RPL, eFac;
  Print("Entering polyhedral function LRS |GRP|=", Order(GroupExt), "\n");
  LPFAC:=Pre__DualDescriptionLRS(EXT, []);
  RPL:=OnSetsGroupFormalism().OrbitGroupFormalism(EXT, GroupExt, "/irrelevant/", false);
  for eFac in LPFAC
  do
    RPL.FuncInsert(Filtered([1..Length(EXT)], x->EXT[x]*eFac=0));
  od;
  return RPL.FuncListOrbitIncidence();
end;



FileFindDel:=Filename(DirectoriesPackagePrograms("polyhedral"),"finddel");
FileFindDelToGAP:=Filename(DirectoriesPackagePrograms("polyhedral"),"finddelToGAP");




#
# this procedure use a Frank Vallentin program 
# and returns one Delaunay polytope of a GramMatrix
# the program works only for integral forms.
# This is a dependency of lrs.
FindDelaunayPolytope_Rational:=function(GramMat)
  local FileIn, FileOut, FileGap, n, eLine, i, j, output, reply, replyB;
  n:=Length(GramMat);
  if IsIntegralMat(GramMat)=false then
    Print("FINDEL error: We have a non-integral matrix\n");
    Print(NullMat(5));
  fi;
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Print("FINDDEL error: matrix should be positive definite\n");
    Print(NullMat(5));
  fi;
  FileIn:=Filename(POLYHEDRAL_tmpdir, "FINDDEL.in");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "FINDDEL.out");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "FINDDEL.Gap");
  output:=OutputTextFile(FileIn, true);;
  AppendTo(output, n, "\n");
  for i in [1..n]
  do
    WriteVector(output, GramMat[i]{[1..i]});
  od;
  CloseStream(output);
  Print("GramMat=", GramMat, "\n");
  Print("beginning the finddel story\n");
  Exec(FileFindDel, " < ", FileIn, " > ", FileOut);
  Exec(FileFindDelToGAP, " ", FileOut, " > ", FileGap);
  Print("ending the finddel story\n");
  reply:=ReadAsFunction(FileGap)();
  replyB:=Filtered(reply, x->Length(x)=n);
  if Length(replyB)=0 then
    Print("BIG ERROR: We did not find any vertices\n");
    Print("FileIn=", FileIn, "\n");
    Print(NullMat(5));
  fi;
  RemoveFile(FileIn);
  RemoveFile(FileOut);
  RemoveFile(FileGap);
  return List(replyB, x->Concatenation([1], x));
end;


POLYDEC_IsReducedToOneLtype_V1:=function(eCase)
  local ThePath, PathLtype, PrimitiveElementFct, FileFacets, PathSave, dimspace, FACred, RML, FAC1, EXT2, FAC2, PathInitial;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  dimspace:=Length(eCase.Basis);
  PathSave:=Concatenation(ThePath, "/POLYDEC/");
  Exec("mkdir -p ", PathSave);
  PathInitial:=Concatenation(PathSave, "InitialLtype/");
  Exec("mkdir -p ", PathInitial);
  RML:=POLYDEC_RandomPrimitiveElement(eCase, PathInitial, false);
  FAC1:=WriteFaceInequalities(RML.DelCO, eCase);
  EXT2:=DualDescription(FAC1.ListInequalities);
  FAC2:=EliminationByRedundancyCone(FAC1.ListInequalities, EXT2);
  FACred:=List(FAC2, x->RemoveFraction(x{[2..dimspace+1]}));
#  Print("|FACred|=", Length(FACred), " |ListFacets|=", Length(eCase.ListFacets), "\n");
#  return rec(test:=test, FACred:=FACred, ListFacets:=eCase.ListFacets, GramMat:=RML.GramMat, DelCO:=RML.DelCO);
  return Set(FACred)=Set(eCase.ListFacets);
end;




FreedomStructure_TestConfiguration:=function(DataLattice, ListListStrongTrans, FreeInformations, eSet)
  local eMatrixGRP, n, ListFreeVect, FuncGetPermutation, ListPermGens, ListMatrGens, eBigGen, eGen, ePerm, PermGRPfree, phi, i, eOrbit, eCent, eRecO, len, ListFreeVectTot, phiTot, ListPermGensTot, ePermTot, PermGRPfreeTot, eElt, eEltImg1, eEltImg2, ListVectorTrans, iPos, eImg1, eImg2, EXTcomplete, ListFacetsEXT, nbOrbit, iOrbit, ListVectZon, ListVectZonAdd, eSetFace, ListFacetsInc, eFaceEXT, EXTsum, ListClusterFacet, ListEXT, eVect, eVectExt, EXTtot, ListPermGensEXT, eList, ListBelt, PermGRPext, eVectTrans, eVectTransSum, preEXTsum, eStab, eStabTot, eSetTot, nbFree, eEltRed, eStabMatr, ListMatrStabGens, iRank, preEXTsumDirect, ListPlanes, ListVectTransSum, ePlane, ListFaceIneq, ListListEXT, EXTface, eFacIneq, eVertRed, eVertOpp, ListEquaFace, rnk, GetListBelt;
  eMatrixGRP:=DataLattice.MatrixGRP;
  n:=DataLattice.n;
  ListFreeVect:=FreeInformations.ListFreeVect;
  nbFree:=Length(ListFreeVect);
  ListFreeVectTot:=Concatenation(ListFreeVect, -ListFreeVect);
  FuncGetPermutation:=function(eMat)
    local eList;
    eList:=List(ListFreeVect, x->GetPositionAntipodal(ListFreeVect, x*eMat));
    return PermList(eList);
  end;
  ListPermGens:=[];
  ListPermGensTot:=[];
  ListMatrGens:=GeneratorsOfGroup(eMatrixGRP);
  for eBigGen in ListMatrGens
  do
    eGen:=FuncExplodeBigMatrix(eBigGen).MatrixTransformation;
    ePerm:=FuncGetPermutation(eGen);
    ePermTot:=PermList(List(ListFreeVectTot, x->Position(ListFreeVectTot, x*eGen)));
    Add(ListPermGens, ePerm);
    Add(ListPermGensTot, ePermTot);
  od;
  PermGRPfree:=Group(ListPermGens);
  PermGRPfreeTot:=Group(ListPermGensTot);
  phi:=GroupHomomorphismByImagesNC(eMatrixGRP, PermGRPfree, ListMatrGens, ListPermGens);
  phiTot:=GroupHomomorphismByImagesNC(eMatrixGRP, PermGRPfreeTot, ListMatrGens, ListPermGensTot);
  EXTcomplete:=[];
  ListFacetsEXT:=[];
  ListVectTransSum:=[];
  ListClusterFacet:=[];
  ListListEXT:=[];
  ListFaceIneq:=[];
  for iRank in [0..n-1]
  do
    nbOrbit:=Length(ListListStrongTrans[iRank+1]);
    Print("iRank=", iRank, "/", n, "\n");
    for iOrbit in [1..nbOrbit]
    do
      eOrbit:=ListListStrongTrans[iRank+1][iOrbit];
      eCent:=eOrbit.EXTiso;
      Print("      rnk=", RankMat(eOrbit.EXTvoronoiFace), "\n");
      eRecO:=OrbitWithAction(eMatrixGRP, eCent, OnPoints);
      len:=Length(eRecO.ListElement);
      Print("iOrbit=", iOrbit, "/", nbOrbit, " |O|=", len, "\n");
      for i in [1..len]
      do
        eElt:=eRecO.ListElement[i];
        eEltRed:=FuncExplodeBigMatrix(eElt).MatrixTransformation;
        eEltImg1:=FuncGetPermutation(eEltRed);
        eEltImg2:=PermList(List(ListFreeVectTot, x->Position(ListFreeVectTot, x*eEltRed)));
        EXTface:=eOrbit.EXTvoronoiFace*eElt;
        ListVectorTrans:=[];
        eVectTransSum:=ListWithIdenticalEntries(n+1,0);
        for iPos in eOrbit.ListFoundPos
        do
          eImg1:=OnPoints(iPos, eEltImg1);
          if eImg1 in eSet then
            eImg2:=OnPoints(iPos, eEltImg2);
            eVectTrans:=ListFreeVectTot[eImg2];
            Add(ListVectorTrans, eVectTrans);
            eVectTransSum:=eVectTransSum+Concatenation([0],eVectTrans);
          fi;
        od;
        for iPos in eOrbit.ListFoundNeg
        do
          eImg1:=OnPoints(iPos, eEltImg1);
          if eImg1 in eSet then
            eImg2:=OnPoints(iPos, eEltImg2);
            eVectTrans:=-ListFreeVectTot[eImg2];
            Add(ListVectorTrans, eVectTrans);
            eVectTransSum:=eVectTransSum+Concatenation([0],eVectTrans);
          fi;
        od;
        ListVectZon:=[];
        ListVectZonAdd:=[];
        for iPos in eOrbit.ListStrongTrans
        do
          eImg1:=OnPoints(iPos, eEltImg1);
          if eImg1 in eSet then
            eVect:=ListFreeVect[eImg1];
            eVectExt:=Concatenation([0], eVect);
            if SolutionMat(EXTface, eVectExt)<>fail then
              Print("Inconsistency for strongly transversal vector\n");
              Print(NullMat(5));
            fi;
            Add(ListVectZon, eVect);
            Add(ListVectZonAdd, eVectExt);
          fi;
        od;
        for iPos in eOrbit.ListFoundZero
        do
          eImg1:=OnPoints(iPos, eEltImg1);
          if eImg1 in eSet then
            eVect:=ListFreeVect[eImg1];
            eVectExt:=Concatenation([0], eVect);
            if SolutionMat(EXTface, eVectExt)=fail then
              Print("Inconsistency for parallel vector\n");
              Print(NullMat(5));
            fi;
            Add(ListVectZon, eVect);
            Add(ListVectZonAdd, eVectExt);
          fi;
        od;
        EXTtot:=Concatenation(EXTface, ListVectZonAdd);
        if RankMat(EXTtot)=n+1 then
          Add(ListClusterFacet, rec(i:=i, iOrbit:=iOrbit, eElt:=eElt));
        fi;
        rnk:=RankMat(EXTtot);
        if rnk=n then
          ListEXT:=[];
          for eVect in ListVectZonAdd
          do
            Add(ListEXT, [eVect, -eVect]);
          od;
          Print("iRank=", iRank, " i=", i, "/", len, " |ListVectZon|=", Length(ListVectZonAdd), " |EXT|=", Length(EXTface), "\n");
          Add(ListEXT, EXTface);
          preEXTsum:=MINKSum_ByWeibelFukuda(ListEXT);
#          preEXTsumDirect:=MINKSum_Direct(ListEXT);
#          if Set(preEXTsum)<>Set(preEXTsumDirect) then
#            Print("No consistency in result of computation\n");
#            Print(NullMat(5));
#          fi;
          EXTsum:=List(preEXTsum, x->x+eVectTransSum);
          EXTcomplete:=Union(EXTcomplete, Set(EXTsum));
          Print("|EXTsum|=", Length(EXTsum), " rnk=", RankMat(EXTsum), " |EXTcomplete|=", Length(EXTcomplete), "\n");
          ListEquaFace:=NullspaceMat(TransposedMat(EXTsum));
          if Length(ListEquaFace)<>1 then
            Print("We have an inconsistency\n");
            Print(NullMat(5));
          fi;
          eFacIneq:=ListEquaFace[1];
          eVertRed:=EXTface[1]{[2..n+1]};
          eVertOpp:=Concatenation([1], -eVertRed);
          if eFacIneq*eVertOpp < 0 then
            eFacIneq:=-eFacIneq;
          fi;
          Add(ListFacetsEXT, EXTsum);
          Add(ListVectTransSum, eVectTransSum);
          Add(ListListEXT, ListEXT);
          Add(ListFaceIneq, eFacIneq);
        fi;
      od;
    od;
  od;
  Print("|EXTcomplete|=", Length(EXTcomplete), "\n");
  eSetTot:=Concatenation(eSet, List(eSet, x->x+nbFree));
  eStabTot:=Stabilizer(PermGRPfreeTot, eSetTot, OnSets);
  eStab:=Stabilizer(PermGRPfree, eSet, OnSets);
  eStabMatr:=PreImage(phi, eStab);
  ListFacetsInc:=[];
  ListPlanes:=[];
  for eFaceEXT in ListFacetsEXT
  do
    eSetFace:=Set(List(eFaceEXT, x->Position(EXTcomplete, x)));
    ePlane:=RemoveFraction(NullspaceMat(TransposedMat(eFaceEXT))[1]);
    Add(ListFacetsInc, eSetFace);
    Add(ListPlanes, ePlane);
  od;
  ListPermGensEXT:=[];
  ListMatrStabGens:=GeneratorsOfGroup(eStabMatr);
  for eGen in ListMatrStabGens
  do
    eList:=List(EXTcomplete, x->Position(EXTcomplete, x*eGen));
    ePerm:=PermList(eList);
    Add(ListPermGensEXT, ePerm);
  od;
  PermGRPext:=Group(ListPermGensEXT);
  GetListBelt:=function()
    return BeltComputationStandard(EXTcomplete, PermGRPext);
  end;
  return rec(EXTcomplete:=EXTcomplete,
             PermGRPext:=PermGRPext,
             GetListBelt:=GetListBelt, 
             ListClusterFacet:=ListClusterFacet, 
             ListPlanes:=ListPlanes,
             ListFacetsEXT:=ListFacetsEXT, 
             ListVectTransSum:=ListVectTransSum, 
             ListListEXT:=ListListEXT, 
             ListFaceIneq:=ListFaceIneq, 
             ListFacetsInc:=ListFacetsInc);
end;



IsIsomorphicGraphPerso:=function(gamma1, gamma2)
  local g,i,j,adj1,adj2,x,aut1,aut2,reps1;
  SetAutGroupCanonicalLabellingPerso(gamma1);
  SetAutGroupCanonicalLabellingPerso(gamma2);
  aut1:=gamma1.autGroup;
  aut2:=gamma2.autGroup;
  if Size(aut1) <> Size(aut2) then 
     return false; 
  fi;
  x:=gamma1.canonicalLabelling^-1*gamma2.canonicalLabelling;
  for g in GeneratorsOfGroup(aut1) do 
     if not g^x in aut2 then
        return false;
     fi;
  od; 
  reps1:=OrbitNumbers(aut1,gamma1.order).representatives;
  for i in reps1 do 
     adj1:=Adjacency(gamma1,i);
     adj2:=Adjacency(gamma2,i^x);
     if Length(adj1)<>Length(adj2) then 
        return false;
     fi;
     for j in adj1 do
        if not (j^x in adj2) then 
          return false; 
        fi;
     od;
  od;
  return true;
end;

#
# here we do implicitly a double coset computation among the orbits
# of Delaunay subpolytopes of TheDelaunay.
# That algorithm is BRAIN broken.
InfDel_OrbitSplitting_V1:=function(TheSuperDelaunay, TheDelaunay, ListOrbit)
  local n, NewListOrbit, eOrbit, PartialNewListOrbit, FuncInsert, IsFinished, nbOrbit, iOrbit, eRecDelaunay, eBigGen, eGen, TheImage, TheBigGroup, NewVectSpace, iOrbitMain, TheStab, testIsStab, ListStatus;
  Print("Begin InfDel_OrbitSplitting, |ListOrbit|=", Length(ListOrbit), "\n");
  n:=TheSuperDelaunay.n;
  NewListOrbit:=[];
  TheBigGroup:=InfDel_CompleteStabilizer(TheDelaunay);
  TheStab:=InfDel_PairStabilizer(TheSuperDelaunay, TheDelaunay);
  testIsStab:=InfDel_IsStabilizer(TheSuperDelaunay, TheBigGroup.GRPmatr);
  Print("|inner group|=", Order(TheBigGroup.GRPperm), " |stab|=", Order(TheStab.GRPperm), " testIsStab=", testIsStab, "\n");
  if testIsStab=true then
    return ListOrbit;
  fi;
  for iOrbitMain in [1..Length(ListOrbit)]
  do
    eOrbit:=ListOrbit[iOrbitMain];
    PartialNewListOrbit:=[];
    ListStatus:=[];
    FuncInsert:=function(eNewCand)
      local eOrbPartial, test, TheNewRecord;
      for eOrbPartial in PartialNewListOrbit
      do
        test:=InfDel_TripleEquivalence(TheSuperDelaunay, TheDelaunay, eOrbPartial, eNewCand);
        if test<>false then
          return;
        fi;
      od;
      Add(ListStatus, "NO");
      Add(PartialNewListOrbit, eNewCand);
    end;
    FuncInsert(eOrbit);
    while(true)
    do
      IsFinished:=true;
      nbOrbit:=Length(PartialNewListOrbit);
      for iOrbit in [1..nbOrbit]
      do
        if ListStatus[iOrbit]="NO" then
          eRecDelaunay:=PartialNewListOrbit[iOrbit];
          ListStatus[iOrbit]:="YES";
          IsFinished:=false;
          for eBigGen in GeneratorsOfGroup(TheBigGroup.GRPmatr)
          do
            TheImage:=InfDel_AffineTransformation(eRecDelaunay, eBigGen);
            if InfDel_IsSubset(TheImage, TheDelaunay)=false then
              Print("We do not have the expected inclusion, please debug\n");
              if InfDel_IsSubset(eRecDelaunay, TheDelaunay)=true then
                Print("althought eRecDelaunay is included\n");
              fi;
              Error("Please correct");
            fi;
            FuncInsert(TheImage);
          od;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    Print("iOrbitMain=", iOrbitMain, " nbOrbit=", nbOrbit, "\n");
    Append(NewListOrbit, PartialNewListOrbit);
  od;
  Print("End InfDel_OrbitSplitting, |NewListOrbit|=", Length(NewListOrbit), "\n");
  return NewListOrbit;
end;



DualDescriptionPD:=function(EXT, GroupExt)
  local FileExt, FileLog, FileIneNude, output, LPFAC, RPL, eFac, DimEXT, EXTnew;
#  Print("Entering polyhedral function PD |GRP|=", Order(GroupExt), "\n");
  FileExt:=Filename(POLYHEDRAL_tmpdir,"PDrun.ext");
  FileLog:=Filename(POLYHEDRAL_tmpdir,"PDrun.log");
  FileIneNude:=Filename(POLYHEDRAL_tmpdir,"PDrun.nude");
  if TestConicness(EXT)=true then
    DimEXT:=Length(EXT[1])-1;
    EXTnew:=List(EXT, x->x{[2..DimEXT+1]});
  else
    DimEXT:=Length(EXT[1]);
    EXTnew:=List(EXT, x->x);
  fi;
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXTnew), " ", DimEXT, " integer\n");
  WriteMatrix(output, EXTnew);
  AppendTo(output, "end\n");
  CloseStream(output);
  Exec(FilePD, " < ", FileExt, " | grep -v '*' > ", FileLog);
  Exec(FileNudifyLRS, " ", FileLog, " > ", FileIneNude);
  LPFAC:=ReadVectorFile(FileIneNude);
  if Length(LPFAC)=0 then
    Error("Error in DualDescriptionCDD_PD");
  fi;
#  RemoveFile(FileExt);
#  RemoveFile(FileLog);
#  RemoveFile(FileIneNude);
  RPL:=OnSetsGroupFormalism().OrbitGroupFormalism(EXT, GroupExt, "/irrelevant/", false);
  for eFac in LPFAC
  do
    RPL.FuncInsert(Filtered([1..Length(EXT)], x->EXTnew[x]*eFac=0));
  od;
  return RPL.FuncListOrbitIncidence();
end;



__DualDescriptionPD_Reduction:=function(EXT, GroupExt, ThePath)
  local FileExt, FileIne, FileIneNude, FileSupport, FileScratch, FileGroup, FileData, FileMetaData, FileOutput, FileError, output, LPFAC, RPL, eFac, DimEXT, EXTnew, ListInc;
  FileExt:=Concatenation(ThePath, "PD.ext");
  FileIne:=Concatenation(ThePath, "PD.ine");
  FileIneNude:=Concatenation(ThePath, "PD.inenude");
  FileSupport:=Concatenation(ThePath, "PD.support");
  FileScratch:=Concatenation(ThePath, "PD.scratch");
  FileGroup:=Concatenation(ThePath, "PD.group");
  FileData:=Concatenation(ThePath, "PD.data");
  FileMetaData:=Concatenation(ThePath, "PD.metadata");
  FileOutput:=Concatenation(ThePath, "PD.output");
  FileError:=Concatenation(ThePath, "PD.error");
  if TestConicness(EXT)=true then
    DimEXT:=Length(EXT[1])-1;
    EXTnew:=List(EXT, x->x{[2..DimEXT+1]});
  else
    DimEXT:=Length(EXT[1]);
    EXTnew:=List(EXT, x->x);
  fi;
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXTnew), " ", DimEXT, " integer\n");
  WriteMatrix(output, EXTnew);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  Exec(FilePD, " < ", FileExt, " | grep -v '*' > ", FileIne);
  Exec(FileNudifyLRS, " ", FileIne, " > ", FileIneNude);
  LPFAC:=ReadVectorFile(FileIneNude);
  if Length(LPFAC)=0 then
    Error("Error in DualDescriptionPD_Reduction");
  fi;
  #
  output:=OutputTextFile(FileSupport, true);
  WriteMatrix(output, EXTnew);
  CloseStream(output);
  #
  OutputGroup(GroupExt, Length(EXTnew), FileGroup);
  #
  Exec(FileIsoReduction, " ", FileData, " ", FileMetaData, " ", FileGroup, " ", FileSupport, " ", FileScratch, " ", FileOutput, "2>", FileError);
  ListInc:=ReadAsFunction(FileOutput)();
  if Length(ListInc)=0 then
    Error("Error in DualDescriptionLRS_Reduction");
  fi;
  RemoveFile(FileExt);
  RemoveFile(FileIne);
  RemoveFile(FileIneNude);
  RemoveFile(FileSupport);
  RemoveFile(FileScratch);
  RemoveFile(FileGroup);
  RemoveFile(FileData);
  RemoveFile(FileMetaData);
  RemoveFile(FileOutput);
  RemoveFile(FileError);
  return ListInc;
end;

