FileMoharSphere:=Filename(DirectoriesPackagePrograms("plangraph"),"CirclePackSphere");
FileMoharRenumber:=Filename(DirectoriesPackagePrograms("plangraph"), "RenumberingMoharOutput");
FileOrderFowler:=Filename(DirectoriesPackagePrograms("plangraph"), "OrderInFowlerFormat");
FileCPF:=Filename(DirectoriesPackagePrograms("plangraph"),"CPF");
FileCPF_nolimit:=Filename(DirectoriesPackagePrograms("plangraph"),"CPF_nolimit");
FileENU:=Filename(DirectoriesPackagePrograms("plangraph"),"ENU");
FileCGF:=Filename(DirectoriesPackagePrograms("plangraph"),"CGF");
FileConnect:=Filename(DirectoriesPackagePrograms("plangraph"),"Connect");
FileLESE:=Filename(DirectoriesPackagePrograms("plangraph"),"planarlese2.orig");
FileLESE2plangraph:=Filename(DirectoriesPackagePrograms("plangraph"),"planarlese_TO_PlanGraph");
FileLESE2connect:=Filename(DirectoriesPackagePrograms("plangraph"),"planarlese_TO_connect");
FileZOM:=Filename(DirectoriesPackagePrograms("plangraph"),"zombat");
FileZOFileSMSER:=Filename(DirectoriesPackagePrograms("plangraph"),"zombatSerial");
FileZOMSER:=Filename(DirectoriesPackagePrograms("plangraph"),"zombatSerial");
FileZOMSER_LUS:=Filename(DirectoriesPackagePrograms("plangraph"),"zombatSerialLUS");
FileScriptReadNr:=Filename(DirectoriesPackagePrograms("plangraph"),"ScriptReadNr");
FileLESE2zomser:=Filename(DirectoriesPackagePrograms("plangraph"),"planarlese_TO_zomser");
FilePlantri:=Filename(DirectoriesPackagePrograms("plangraph"),"plantri");
FileSplitLPL:=Filename(DirectoriesPackagePrograms("plangraph"),"SplitLPL");
FilePlanarlese2:=Filename(DirectoriesPackagePrograms("plangraph"),"planarlese2.orig");
FileLeseToPG:=Filename(DirectoriesPackagePrograms("plangraph"),"planarlese_TO_PlanGraph");



Get4valentPlaneGraphSpecifiedFaceSet:=function(nbV, ListFaceSize, FileSave)
  local TheSum, ePair, TmpDir, ThePrefix, TheComm, TheSize, n, FileLOG, FileOUT, TheCommand, nb, FileL, eSize, File4RE, FileErr;
  ThePrefix:=Concatenation("4reg_v", String(nbV));
  TheComm:=Concatenation(" v", String(nbV));
  for eSize in ListFaceSize
  do
    ThePrefix:=Concatenation(ThePrefix, "_f", String(eSize));
    TheComm:=Concatenation(TheComm, " f", String(eSize));
  od;
  FileErr:=Filename(PLANGRAPH_tmpdir, "ENU.log");
  TheComm:=Concatenation(TheComm, " 2> ", FileErr);
  TmpDir:=Filename(PLANGRAPH_tmpdir, "");
  File4RE:=Filename(PLANGRAPH_tmpdir, ThePrefix);
  FileLOG:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".log"));
  FileL:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".lese"));
  RemoveFileIfExist(File4RE);
  RemoveFileIfExist(FileLOG);
  TheCommand:=Concatenation("(cd ", TmpDir, " && ", FileENU, TheComm, ")");
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileLESE, " < ", File4RE, " > ", FileL);
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileLESE2plangraph, " < ", FileL, " > ", FileSave);
  Exec(TheCommand);
  #
  RemoveFile(File4RE);
  RemoveFile(FileLOG);
  RemoveFile(FileL);
end;

GetList4valentPlaneGraphSpecifiedFaceSet:=function(nbV, ListFaceSize)
  local FileReturn, LPL;
  FileReturn:=Filename(PLANGRAPH_tmpdir, "TheReturn");
  Get4valentPlaneGraphSpecifiedFaceSet(nbV, ListFaceSize, FileReturn);
  LPL:=ReadAsFunction(FileReturn)();
  RemoveFile(FileReturn);
  return LPL;
end;





Get3valentPlaneGraphSpecifiedFaces_PLC:=function(nbV, ListFaceDesc)
  local ePair, TmpDir, ThePrefix, TheComm, TheSize, n, FilePLC, FileLOG, FileOUT, TheCommand, nb, FileL, ListSiz, NewListFaceDesc, ePerm, eRec, FileERR, FileSTD;
  ListSiz:=List(ListFaceDesc, x->x[1]);
  if Length(ListSiz)<>Length(Set(ListSiz)) then
    Print("There are repetition in ListFaceDesc\n");
    Print("This is not allowed\n");
    Print(NullMat(5));
  fi;
  ePerm:=SortingPerm(ListSiz);
  NewListFaceDesc:=Permuted(ListFaceDesc, ePerm);
  ThePrefix:=Concatenation("3reg_n", String(nbV));
  TheComm:=Concatenation(" n ", String(nbV));
  for ePair in NewListFaceDesc
  do
    TheSize:=ePair[1];
    if TheSize < 3 then
      Print("TheSize=", TheSize, "\n");
      Error("Minimum face size is 3");
    fi;
    eRec:=ePair[2];
    if eRec.eNature="plus" then
      nb:=eRec.nb;
      if nb>0 then
        ThePrefix:=Concatenation(ThePrefix, "_f", String(TheSize), "+", String(nb));
        TheComm:=Concatenation(TheComm, " f ", String(TheSize), " +", String(nb));
      else
        ThePrefix:=Concatenation(ThePrefix, "_f", String(TheSize) );
        TheComm:=Concatenation(TheComm, " f ", String(TheSize) );
      fi;
    elif eRec.eNature="minus" then
      nb:=eRec.nb;
      ThePrefix:=Concatenation(ThePrefix, "_f", String(TheSize), "-", String(nb));
      TheComm:=Concatenation(TheComm, " f ", String(TheSize), " -", String(nb));
    elif eRec.eNature="unspec" then
      ThePrefix:=Concatenation(ThePrefix, "_f", String(TheSize));
      TheComm:=Concatenation(TheComm, " f ", String(TheSize));
    else
      Print("Wrong specification\n");
      Print(NullMat(5));
    fi;
  od;
  TmpDir:=Filename(PLANGRAPH_tmpdir, "");
  FilePLC:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".plc"));
  FileLOG:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".log"));
  FileERR:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".err"));
  FileSTD:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".std"));
  RemoveFileIfExist(FilePLC);
  RemoveFileIfExist(FileLOG);
  if nbV<=250 then
    TheCommand:=Concatenation("(cd ", TmpDir, " && ", FileCPF, TheComm, " > ", FileSTD, " 2> ", FileERR, ")");
  else
    TheCommand:=Concatenation("(cd ", TmpDir, " && ", FileCPF_nolimit, TheComm, " > ", FileSTD, " 2> ", FileERR, ")");
  fi;
#  Print("TheCommand=", TheCommand, "\n");
  Exec(TheCommand);
#  Print("After run\n");
  if IsExistingFile(FileLOG)=false then
    Print("Debug from here\n");
    Print(NullMat(5));
  fi;
  RemoveFile(FileLOG);
  return FilePLC;
end;

Get3valentPlaneGraphSpecifiedFaces:=function(nbV, ListFaceDesc, FileSave)
  local FilePLC, FileL, TheCommand;
  FilePLC:=Get3valentPlaneGraphSpecifiedFaces_PLC(nbV, ListFaceDesc);
  FileL:=Filename(PLANGRAPH_tmpdir, "eSave.lese");
  RemoveFileIfExist(FileL);
  TheCommand:=Concatenation(FileLESE, " < ", FilePLC, " > ", FileL);
  Exec(TheCommand);
  if IsExistingFile(FilePLC)=false then
    SaveDataToFile(FileSave, []);
  fi;
  #
  TheCommand:=Concatenation(FileLESE2plangraph, " < ", FileL, " > ", FileSave);
  Exec(TheCommand);
  RemoveFile(FilePLC);
  RemoveFile(FileL);
end;


GetList3valentPlaneGraphSpecifiedFaces_2connect:=function(nbV, ListPair)
  local FilePLC, FileL, TheCommand, TheSum, ListFaceDesc, ePair, FileConnInp, FileConnOut, LPL;
  TheSum:=0;
  ListFaceDesc:=[];
  for ePair in ListPair
  do
    TheSum:=TheSum+ePair[2]*ePair[1];
    Add(ListFaceDesc, [ePair[1], rec(eNature:="plus", nb:=ePair[2])]);
  od;
  if 3*nbV<>TheSum then
    Print("nbV=", nbV, " TheSum=", TheSum, "\n");
    Print("Inconsistency between asked faces and Fvector\n");
    Print(NullMat(5));
  fi;
  FilePLC:=Get3valentPlaneGraphSpecifiedFaces_PLC(nbV, ListFaceDesc);
  FileL:=Filename(PLANGRAPH_tmpdir, "eSave.lese");
  FileConnInp:=Filename(PLANGRAPH_tmpdir, "eSave.connectINP");
  FileConnOut:=Filename(PLANGRAPH_tmpdir, "eSave.connectOUT");
  RemoveFileIfExist(FileL);
  TheCommand:=Concatenation(FileLESE, " < ", FilePLC, " > ", FileL);
  Exec(TheCommand);
  if IsExistingFile(FilePLC)=false then
    return [];
  fi;
  #
  Print("FileL=", FileL, "\n");
  Print("FileConnInp=", FileConnInp, "\n");
  Print("FileConnOut=", FileConnOut, "\n");
  TheCommand:=Concatenation(FileLESE2connect, " < ", FileL, " > ", FileConnInp);
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileConnect, " ", FileConnInp, " ", FileConnOut);
  Exec(TheCommand);
  #
  LPL:=ReadAsFunction(FileConnOut)();
  Print("|LPL|=", Length(LPL), "\n");
  RemoveFile(FilePLC);
  RemoveFile(FileL);
  RemoveFile(FileConnInp);
  RemoveFile(FileConnOut);
  return LPL;
end;



Get3valentPlaneGraphSpecifiedFvector:=function(nbV, ListPair, FileSave)
  local TheSum, ListFaceDesc, ePair;
  TheSum:=0;
  ListFaceDesc:=[];
  for ePair in ListPair
  do
    TheSum:=TheSum+ePair[2]*ePair[1];
    Add(ListFaceDesc, [ePair[1], rec(eNature:="plus", nb:=ePair[2])]);
  od;
  if 3*nbV<>TheSum then
    Print("nbV=", nbV, " TheSum=", TheSum, "\n");
    Print("Inconsistency between asked faces and Fvector\n");
    Print(NullMat(5));
  fi;
  Get3valentPlaneGraphSpecifiedFaces(nbV, ListFaceDesc, FileSave);
end;


GetList3valentPlaneGraphSpecifiedFvector:=function(nbV, ListPair)
  local FileReturn, LPL;
  FileReturn:=Filename(PLANGRAPH_tmpdir, "TheReturn");
  Get3valentPlaneGraphSpecifiedFvector(nbV, ListPair, FileReturn);
  LPL:=ReadAsFunction(FileReturn)();
  RemoveFile(FileReturn);
  return LPL;
end;

GetList3valentPlaneGraphSpecifiedFaces:=function(nbV, ListFaceDesc)
  local FileReturn, LPL;
  FileReturn:=Filename(PLANGRAPH_tmpdir, "TheReturn");
  Get3valentPlaneGraphSpecifiedFaces(nbV, ListFaceDesc, FileReturn);
  LPL:=ReadAsFunction(FileReturn)();
  RemoveFile(FileReturn);
  return LPL;
end;



Get3valentOrientedMapsSpecifiedFvector:=function(nbV, eGenus, ListPair, FileSave)
  local TheSum, ePair, TmpDir, ThePrefix, TheComm, TheSize, n, FileEC, FileLOG, FileDUMP, FileDUMPt, FileOUT, TheCommand, nb, FileL, ListSiz, ePerm, NewListPair;
  TheSum:=0;
  ListSiz:=List(ListPair, x->x[1]);
  if Length(ListSiz)<>Length(Set(ListSiz)) then
    Print("There are repetition in ListPair\n");
    Print("This is not allowed\n");
    Print(NullMat(5));
  fi;
  ePerm:=SortingPerm(ListSiz);
  NewListPair:=Permuted(ListPair, ePerm);
  for ePair in NewListPair
  do
    TheSum:=TheSum+ePair[2]*ePair[1];
  od;
  if 3*nbV<>TheSum then
    Print("nbV=", nbV, " TheSum=", TheSum, "\n");
    Print("Inconsistency between asked faces and Fvector\n");
    Print(NullMat(5));
  fi;
  ThePrefix:=Concatenation("3reg_g", String(eGenus), "_v", String(nbV));
  TheComm:=Concatenation(" -v ", String(nbV), " -g ", String(eGenus));
  for ePair in NewListPair
  do
    TheSize:=ePair[1];
    nb:=ePair[2];
    if nb>0 then
      ThePrefix:=Concatenation(ThePrefix, "_f", String(TheSize), "_", String(nb), "]");
      TheComm:=Concatenation(TheComm, " -f ", String(TheSize), " ", String(nb), "u");
    fi;
  od;
  TmpDir:=Filename(PLANGRAPH_tmpdir, "");
  FileEC:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".ec"));
  FileLOG:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".log"));
  FileDUMP:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".dump"));
  FileDUMPt:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".dump~"));
  FileOUT:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".out"));
  FileL:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".lese"));
  RemoveFileIfExist(FileEC);
  RemoveFileIfExist(FileLOG);
  RemoveFileIfExist(FileDUMP);
  RemoveFileIfExist(FileDUMPt);
  RemoveFileIfExist(FileOUT);
  TheCommand:=Concatenation("(cd ", TmpDir, " && ", FileCGF, TheComm, ")");
  Exec(TheCommand);
  #
  if IsExistingFile(FileEC)=false then
    SaveDataToFile(FileSave, []);
    RemoveFile(FileLOG);
  else
    TheCommand:=Concatenation(FileLESE, " < ", FileEC, " > ", FileL);
    Exec(TheCommand);
    #
    TheCommand:=Concatenation(FileLESE2plangraph, " < ", FileL, " > ", FileSave);
    Exec(TheCommand);
    #
    RemoveFile(FileEC);
    RemoveFile(FileLOG);
    RemoveFile(FileDUMP);
    RemoveFile(FileDUMPt);
    RemoveFile(FileOUT);
    RemoveFile(FileL);
  fi;
end;

GetList3valentOrientedMapsSpecifiedFvector:=function(nbV, eGenus, ListPair)
  local FileReturn, LPL;
  FileReturn:=Filename(PLANGRAPH_tmpdir, "TheReturn");
  Get3valentOrientedMapsSpecifiedFvector(nbV, eGenus, ListPair, FileReturn);
  LPL:=ReadAsFunction(FileReturn)();
  RemoveFile(FileReturn);
  return LPL;
end;




__OutputCaGe:=function(output, PlanGraph, InfoMult)
  local iVert, LADJ, jVert, TheColl, eEnt, eNb, eEdge, pos, iVal, ListValues, ListEdges;
  ListValues:=[];
  ListEdges:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    AppendTo(output, String(iVert));
    AppendTo(output, " 0 0 0");
    LADJ:=[];
    for jVert in PlanGraph[iVert]
    do
      if not(jVert in LADJ) and jVert<>iVert then
        Add(LADJ, jVert);
      fi;
    od;
    if InfoMult=true then
      TheColl:=Collected(PlanGraph[iVert]);
      for eEnt in TheColl
      do
        eNb:=eEnt[2];
        if eNb>1 then
          eEdge:=Set([iVert, eEnt[1]]);
          pos:=Position(ListValues, eNb);
          if pos<>fail then
            Add(ListEdges[pos], eEdge);
          else
            Add(ListValues, eNb);
            Add(ListEdges, [eEdge]);
          fi;
        fi;
      od;
    fi;
    for jVert in LADJ
    do
      AppendTo(output, " ", jVert);
    od;
    AppendTo(output, "\n");
  od;
  AppendTo(output, "0\n");
  for iVal in [1..Length(ListValues)]
  do
    Print("eValue=", ListValues[iVal], "\n");
    for eEdge in Set(ListEdges[iVal])
    do
      Print("  eEdge=", eEdge, "\n");
    od;
  od;
end;



PlanGraphToCaGeSeveral:=function(FileName, LPL)
  local output, ePL, InfoMult;
  Exec("rm -f ", FileName, "\n");
  InfoMult:=false;
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, ">>writegraph3d planar <<\n");
  for ePL in LPL
  do
    __OutputCaGe(output, ePL, InfoMult);
  od;
  CloseStream(output);
end;

PlanGraphToCaGe:=function(FileName, PlanGraph)
  local output, InfoMult;
  Exec("rm -f ", FileName, "\n");
  InfoMult:=false;
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, ">>writegraph3d planar <<\n");
  __OutputCaGe(output, PlanGraph, InfoMult);
  CloseStream(output);
end;


RemoveEdgeOverlined:=function(eRecPLover, eEdge)
  local eEdgeRed, PLnew, pos, ListOver, eDiff;
  eEdgeRed:=Set(List(eEdge, x->x[1]));
  PLnew:=RemoveEdge(eRecPLover.PL, eEdge);
  pos:=Position(eRecPLover.ListOverlinedEdge, eEdgeRed);
  if pos=fail then
    ListOver:=eRecPLover.ListOverlinedEdge;
  else
    eDiff:=Difference([1..Length(eRecPLover.ListOverlinedEdge)], [pos]);
    ListOver:=eRecPLover.ListOverlinedEdge{eDiff};
  fi;
  return rec(PL:=PLnew, ListOverlinedEdge:=ListOver);
end;

RemoveVertexOverlined:=function(eRecPLover, eVert)
  local nbVert, ListCorresp, ListCorrespRed, iVertRed, iVert, nbVertRed, LAdj, eAdj, eAdjRed, ListOver, eEdge, eEdgeRed, PL;
#  Print("eVert=", eVert, "\n");
  nbVert:=Length(eRecPLover.PL);
  ListCorresp:=ListWithIdenticalEntries(nbVert, 0);
  ListCorrespRed:=ListWithIdenticalEntries(nbVert, 0);
  iVertRed:=0;
  for iVert in [1..nbVert]
  do
    if iVert<>eVert then
      iVertRed:=iVertRed+1;
      ListCorresp[iVert]:=iVertRed;
      ListCorrespRed[iVertRed]:=iVert;
    fi;
  od;
  nbVertRed:=iVertRed;
#  Print("nbVertRed=", nbVertRed, "\n");
  PL:=[];
  for iVertRed in [1..nbVertRed]
  do
    iVert:=ListCorrespRed[iVertRed];
    LAdj:=[];
    for eAdj in eRecPLover.PL[iVert]
    do
      if eAdj<>eVert then
        eAdjRed:=ListCorresp[eAdj];
	Add(LAdj, eAdjRed);
      fi;
    od;
    Add(PL, LAdj);
  od;
  ListOver:=[];
  for eEdge in eRecPLover.ListOverlinedEdge
  do
    if Position(eEdge, eVert)=fail then
      eEdgeRed:=List(eEdge, x->ListCorresp[x]);
      Add(ListOver, eEdgeRed);
    fi;
  od;
  return rec(PL:=PL, ListOverlinedEdge:=ListOver);
end;






__OutputCaGeOverlined:=function(output, eRecPLover)
  local iVert, LADJ, jVert, TheColl, eEnt, eNb, eEdge, pos, iVal, ListValues, ListEdges;
  ListValues:=[];
  ListEdges:=[];
  for iVert in [1..Length(eRecPLover.PL)]
  do
    AppendTo(output, String(iVert));
    AppendTo(output, " 0 0 0");
    LADJ:=[];
    for jVert in eRecPLover.PL[iVert]
    do
      if not(jVert in LADJ) and jVert<>iVert then
        Add(LADJ, jVert);
      fi;
    od;
    for jVert in LADJ
    do
      if jVert > iVert then
        eEdge:=[iVert, jVert];
      else
        eEdge:=[jVert, iVert];
      fi;
      pos:=Position(eRecPLover.ListOverlinedEdge, eEdge);
      if pos=fail then
        AppendTo(output, " ", jVert);
      else
        AppendTo(output, " -", jVert);
      fi;
    od;
    AppendTo(output, "\n");
  od;
  AppendTo(output, "0\n");
end;



PlanGraphToCaGeOverlinedSeveral:=function(FileName, ListRecPLover)
  local output, eRecPLover;
  Exec("rm -f ", FileName, "\n");
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, ">>writegraph3d planar <<\n");
  for eRecPLover in ListRecPLover
  do
    __OutputCaGeOverlined(output, eRecPLover);
  od;
  CloseStream(output);
end;

PlanGraphToCaGeOverlined:=function(FileName, eRecPLover)
  local output, InfoMult;
  Exec("rm -f ", FileName, "\n");
  InfoMult:=false;
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, ">>writegraph3d planar <<\n");
  __OutputCaGeOverlined(output, eRecPLover);
  CloseStream(output);
end;
















PlanGraphToCaGeInfoMult:=function(FileName, PlanGraph)
  local output, InfoMult;
  Exec("rm -f ", FileName, "\n");
  InfoMult:=true;
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, ">>writegraph3d planar <<\n");
  __OutputCaGe(output, PlanGraph, InfoMult);
  CloseStream(output);
end;




__MoharSpherical:=function(FileName, BipartitionVector, PL)
  local output, LAdj, iVert, nbV, jVert;
  RemoveFileIfExist(FileName);
  output:=OutputTextFile(FileName, true);
  nbV:=Length(PL);
  AppendTo(output, nbV, "\n");
  for iVert in [1..nbV]
  do
    AppendTo(output, " ", BipartitionVector[iVert]);
    LAdj:=PL[iVert];
    AppendTo(output, " ", Length(LAdj));
    for jVert in LAdj
    do
      AppendTo(output, " ", jVert);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;

TestMoharSpherical:=function(FileName, PL)
  local PL1, PL2, GR2, BipartitionVector;
  PL1:=MedialGraph(PL).PlanGraph;
  PL2:=DualGraph(PL1).PlanGraph;
  GR2:=PlanGraphToGRAPE(PL2);
  BipartitionVector:=GetBipartition(GR2);
  __MoharSpherical(FileName, BipartitionVector, PL2);
end;


# this program is better than the preceding in that PL is 
# part of the first bipartition
OutputToMoharProgram:=function(FileName, PL)
  local ListFaces, FindInListFaces, ThePL, ListBipartition, nbV, ListAdj, LAdj, iAdj, iFace, eDE, i;
  ListFaces:=__FaceSet(PL);
  FindInListFaces:=function(eDE)
    local iFace;
    for iFace in [1..Length(ListFaces)]
    do
      if Position(ListFaces[iFace], eDE)<>fail then
        return iFace;
      fi;
    od;
  end;
  ThePL:=[];
  ListBipartition:=[];
  nbV:=Length(PL);
  for i in [1..nbV]
  do
    ListAdj:=PL[i];
    LAdj:=[];
    for iAdj in [1..Length(ListAdj)]
    do
      Add(LAdj, nbV+FindInListFaces([i,iAdj]));
    od;
    Add(ThePL, LAdj);
    Add(ListBipartition, 1);
  od;
  for iFace in [1..Length(ListFaces)]
  do
    LAdj:=[];
    for eDE in ListFaces[iFace]
    do
      Add(LAdj, eDE[1]);
    od;
    Add(ThePL, LAdj);
    Add(ListBipartition, 2);
  od;
#  return ThePL;
  __MoharSpherical(FileName, ListBipartition, ThePL);
end;

CreateSphericalPrimalCoordinates:=function(FileName, PL)
  local FileTMP1, FileTMP2, FileTMP3;
  FileTMP1:=Filename(PLANGRAPH_tmpdir,"FileMohar.tmp1");
  FileTMP2:=Filename(PLANGRAPH_tmpdir,"FileMohar.tmp2");
  FileTMP3:=Filename(PLANGRAPH_tmpdir,"FileMohar.tmp3");
  OutputToMoharProgram(FileTMP1, PL);
  Exec(FileMoharSphere, " ", FileTMP1, " ", FileTMP2, " vert1 edge1");
  Exec(FileMoharRenumber, " ", FileTMP2, " > ", FileTMP3);
  Exec(FileOrderFowler, " ", FileTMP3, " > ", FileName);
  RemoveFile(FileTMP1);
  RemoveFile(FileTMP2);
  RemoveFile(FileTMP3);
end;









PlanGraphToFOWLER:=function(FileName, PlanGraph)
  local output, iVert, jVert, LADJ;
  Exec("rm -f ", FileName, "\n");
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, Length(PlanGraph), "\n");
  for iVert in [1..Length(PlanGraph)]
  do
    LADJ:=[];
    for jVert in PlanGraph[iVert]
    do
      if not(jVert in LADJ) then
        Add(LADJ, jVert);
      fi;
    od;
    for jVert in LADJ
    do
      AppendTo(output, " ", jVert);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;







PlanGraphToGRAPE:=function(PlanGraph)
  local n, Gra, i, u;
  n:=Length(PlanGraph);
  Gra:=NullGraph(Group(()), n);
  for i in [1..n]
  do
    for u in PlanGraph[i]
    do
      if u<>i then
        AddEdgeOrbit(Gra, [i,u]);
      fi;
    od;
  od;
  return Gra;
end;



PlanGraphToFOWLER2:=function(FileName, PlanGraph)
  local output, iVert, jVert, LADJ, eFac, FaceSet, i;
  Exec("rm -f ", FileName, "\n");
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, Length(PlanGraph), "\n");
  for iVert in [1..Length(PlanGraph)]
  do
    LADJ:=[];
    for jVert in PlanGraph[iVert]
    do
      if not(jVert in LADJ) then
        Add(LADJ, jVert);
      fi;
    od;
    for jVert in LADJ
    do
      AppendTo(output, " ", jVert);
    od;
    AppendTo(output, "\n");
  od;
  FaceSet:=__FaceSet(PlanGraph);
  for eFac in FaceSet
  do
    for i in [1..Length(eFac)]
    do
      AppendTo(output, " ", eFac[i][1]);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;





PlanGraphTo2DT:=function(FileName, PlanGraph)
  local PLABC, ListSymb0, ListSymb1, ListSymb2, output, nbP, FuncListReducedByMissing, FuncPrint, ReducedListMIJ, ListRed;
  output:=OutputTextFile(FileName, true);
  PLABC:=__PlanGraphToABC(PlanGraph);
  nbP:=PLABC.nbP;
  ListSymb0:=OnTuples([1..nbP], PLABC.permA);
  ListSymb1:=OnTuples([1..nbP], PLABC.permB);
  ListSymb2:=OnTuples([1..nbP], PLABC.permC);

  FuncListReducedByMissing:=function(ListSymb)
    local a, b, eList;
    eList:=[];
    for a in [1..nbP]
    do
      b:=ListSymb[a];
      if b=a then
        Add(eList, a);
      fi;
      if b>a then
        Add(eList, b);
      fi;
    od;
    return eList;
  end;



  FuncPrint:=function(eList)
    local iFlag;
    for iFlag in [1..Length(eList)]
    do
      if iFlag>1 then
        AppendTo(output, " ");
      fi;
      AppendTo(output, eList[iFlag]);
    od;
  end;


  ReducedListMIJ:=function(ePermI, ePermJ)
    local GRP, O, NewList, eOrb, fOrb, ListRed;
    GRP:=Group([ePermI, ePermJ]);
    O:=Orbits(GRP, [1..nbP], OnPoints);
    NewList:=[];
    for eOrb in O
    do
      fOrb:=Set(ShallowCopy(eOrb));
      AddSet(NewList, fOrb);
    od;
    ListRed:=[];
    for eOrb in NewList
    do
      Add(ListRed, Length(eOrb)/2);
    od;
    return ListRed;
  end;



  AppendTo(output, "<");
  AppendTo(output, "1.1");
  AppendTo(output, ":");
  AppendTo(output, nbP, " 2");

  AppendTo(output, ":");

  ListRed:=FuncListReducedByMissing(ListSymb0);
  FuncPrint(ListRed);
  AppendTo(output, ",");
  ListRed:=FuncListReducedByMissing(ListSymb1);
  FuncPrint(ListRed);
  AppendTo(output, ",");
  ListRed:=FuncListReducedByMissing(ListSymb2);
  FuncPrint(ListRed);

  AppendTo(output, ":");

  ListRed:=ReducedListMIJ(PLABC.permA, PLABC.permB);
  FuncPrint(ListRed);
  AppendTo(output, ",");
  ListRed:=ReducedListMIJ(PLABC.permB, PLABC.permC);
  FuncPrint(ListRed);
  AppendTo(output, ">\n");
  CloseStream(output);
end;






PlanGraphToTorusDraw:=function(FileName, PL)
  local PL1, PL2, i, j, output, nb, MaxNB, FileGraph, FileSpa, FileBip, u, BCE, SPA, eInc, eVert, MaxSize, iVert;
  PL1:=MedialGraph(PL).PlanGraph;
  PL2:=DualGraph(PL1).PlanGraph;
  FileGraph:=Concatenation(FileName, ".plg");
  Exec("rm -f ", FileGraph,"\n");
  output:=OutputTextFile(FileGraph, true);
  MaxNB:=0;
  for i in [1..Length(PL2)]
  do
    nb:=Length(PL2[i]);
    if nb>MaxNB then
      MaxNB:=nb;
    fi;
  od;
  for i in [1..Length(PL2)]
  do
    nb:=Length(PL2[i]);
    for j in [1..nb]
    do
      AppendTo(output, " ", PL2[i][j]);
    od;
    for j in [1..MaxNB-nb]
    do
      AppendTo(output, " 0");
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);

  FileSpa:=Concatenation(FileName, ".spa");
  Exec("rm -f ", FileSpa,"\n");
  output:=OutputTextFile(FileSpa, true);
  SPA:=SpanningTreeGraph(PlanGraphToGRAPE(PL2), 1);
  for eInc in SPA
  do
    AppendTo(output, " ", eInc[1], " ", eInc[2], "\n");
  od;
  CloseStream(output);

  FileBip:=Concatenation(FileName, ".bip");
  Exec("rm -f ", FileBip,"\n");
  output:=OutputTextFile(FileBip, true);
  BCE:=Bicomponents(PlanGraphToGRAPE(PL2));
  MaxSize:=Maximum(Length(BCE[1]), Length(BCE[2]));
  for iVert in [1..Length(PL2)]
  do
    if Position(BCE[1], iVert)<>fail then
      AppendTo(output, " 1");
    else
      AppendTo(output, " 2");
    fi;
  od;
  AppendTo(output, "\n");
  CloseStream(output);
end;

DoConversionPlanGraphToPlanGraphOriented:=function(PL)
  local ListDE, nbVert, iVert, nbAdj, iAdj, nbDE, eListNext, ListIdxCrit, ListListCandPos, eListInvBasic, iDE, eDE, len, iNew, eDEnext, eVertAdj, ListCandPos, LPLori, ePLori, eListInv, pos, LCand, eCand, eDEinv, LCandPos;
  ListDE:=[];
  nbVert:=Length(PL);
  for iVert in [1..nbVert]
  do
    nbAdj:=Length(PL[iVert]);
    for iAdj in [1..nbAdj]
    do
      Add(ListDE, [iVert, iAdj]);
    od;
  od;
  nbDE:=Length(ListDE);
  eListNext:=[];
  ListIdxCrit:=[];
  ListListCandPos:=[];
  eListInvBasic:=[];
  for iDE in [1..nbDE]
  do
    eDE:=ListDE[iDE];
    len:=Length(PL[eDE[1]]);
    iNew:=NextIdx(len, eDE[2]);
    eDEnext:=[eDE[1], iNew];
    Add(eListNext, Position(ListDE, eDEnext));
    eVertAdj:=PL[eDE[1]][eDE[2]];
    ListCandPos:=Filtered([1..Length(PL[eVertAdj])], x->PL[eVertAdj][x]=eDE[1]);
    if Length(ListCandPos)=1 then
      eDEinv:=[eVertAdj, ListCandPos[1]];
      Add(eListInvBasic, Position(ListDE, eDEinv));
    else
      Add(eListInvBasic, "unk");
      LCandPos:=List(ListCandPos, x->Position(ListDE, [eVertAdj, x]));
      Add(ListListCandPos, LCandPos);
      Add(ListIdxCrit, iDE);
    fi;
  od;
  LPLori:=[];
  LCand:=BuildSetMultiple(ListListCandPos);
  for eCand in LCand
  do
    eListInv:=[];
    for iDE in [1..nbDE]
    do
      pos:=Position(ListIdxCrit, iDE);
      if pos=fail then
        eListInv[iDE]:=eListInvBasic[iDE];
      else
        eListInv[iDE]:=eCand[pos];
      fi;
    od;
    if Length(Set(eListInv))=Length(eListInv) then
      ePLori:=rec(nbP:=nbDE, invers:=PermList(eListInv), next:=PermList(eListNext));
      Add(LPLori, ePLori);
    fi;
  od;
  return LPLori;
end;



# We have the program CGF for enumerating 3-valent graphs on surfaces.
# We search foricosahedrites on tori.
# We will have p3 = 2p4
# The number ofvertices will satisfy
# 5 n =3 p3 + 4 p4 = 10 p4
# Hence n= 2 p4
# totalnumber of edgesis 2e =5n. So e = 5 p4.
#
# Suppose now that we take the dual andtransform the vertices of degree 4
# into 4-gons by truncation. Then the resultinggraph has m = 4 p4 + p3
# vertices
# This makes m = 4 p4 +2 p4 = 6 p4 = 3n.
# Faces would be 4, 5, 6, 7, 8,9 and 10-gons.
# and number of 4-gons would be p4. Other faces numbers are unset.
#
# Othertransformation.Take the leapfrog of the graph.
# i.e. on everyedge but two vertices that are adjacent.
# This makes a graph with m = 5 n vertices.
# The faces are 3, 4, and 10-gons.
# The number of  3-gons is 2p4
# The number of  4-gons is p4
# The number of 10-gons is 2p4
# check (6-10)2 + (6-4) + (6-3)2 = -8 + 2 + 6 = 0
GetTorusIcosahedrite_method1:=function(n)
  local p4, m, TheCommand, eStrP4, ThePrefix, FileEC, FileLOG, FileDUMP, FileDUMPt, FileOUT, FileL, TmpDir, FileSave, LPL, LPLret, ePL, ePLori, VEFori, nbFace, ListFace, eRecINV, PLoriFinal;
  p4:=n/2;
  if IsInt(p4)=false then
    Error("n should be even");
  fi;
  m:=3*n;
  eStrP4:=Concatenation(" -f 4 l", String(p4), "-", String(p4), "u");
  #
  ThePrefix:=Concatenation("3reg_g1_v", String(m), "_f4[", String(p4), ",", String(p4), "]_f5_f6_f7_f8_f9_f10");
  TmpDir:=Filename(PLANGRAPH_tmpdir, "");
  FileEC:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".ec"));
  FileLOG:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".log"));
  FileDUMP:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".dump"));
  FileDUMPt:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".dump~"));
  FileOUT:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".out"));
  FileL:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".lese"));
  FileSave:=Filename(PLANGRAPH_tmpdir, Concatenation(ThePrefix, ".final"));
  RemoveFileIfExist(FileEC);
  RemoveFileIfExist(FileLOG);
  RemoveFileIfExist(FileDUMP);
  RemoveFileIfExist(FileDUMPt);
  RemoveFileIfExist(FileOUT);
  RemoveFileIfExist(FileSave);
  #
  TheCommand:=Concatenation("(cd ", TmpDir, " && ", FileCGF, " -v ", String(m), " -g 1", eStrP4, " -f 5 -f 6 -f 7 -f 8 -f 9 -f 10)");
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileLESE, " < ", FileEC, " > ", FileL);
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileLESE2plangraph, " < ", FileL, " > ", FileSave);
  Exec(TheCommand);
  #
  LPL:=ReadAsFunction(FileSave)();
  RemoveFileIfExist(FileEC);
  RemoveFileIfExist(FileLOG);
  RemoveFileIfExist(FileDUMP);
  RemoveFileIfExist(FileDUMPt);
  RemoveFileIfExist(FileOUT);
  RemoveFileIfExist(FileSave);
  LPLret:=[];
  for ePL in LPL
  do
    ePLori:=PlanGraphToPlanGraphOriented(ePL);
    VEFori:=PlanGraphOrientedToVEF(ePLori);
    nbFace:=Length(VEFori.FaceSet);
    ListFace:=Filtered([1..nbFace], x->Length(VEFori.FaceSet[x])=4);
    eRecINV:=InverseTruncationOrientedSelect(ePLori, VEFori, ListFace);
    if eRecINV.success=true then
      PLoriFinal:=DualGraphOriented(eRecINV.PLori);
      Add(LPLret, rec(PLori:=PLoriFinal, PLoriD:=eRecINV.PLori, PLoriPrev:=ePLori));
    fi;
  od;
  return LPLret;
end;

# The second is ultra super slow. Not to be used.
GetTorusIcosahedrite_method2:=function(n)
  local p4, m, TheCommand, eStrP3, eStrP4, eStrP10;
  p4:=n/2;
  m:=5*n;
  eStrP3 :=Concatenation(" -f 3 l", String(2*p4), "-", String(2*p4), "u");
  eStrP4 :=Concatenation(" -f 4 l", String(p4), "-", String(p4), "u");
  eStrP10:=Concatenation(" -f 10 l", String(2*p4), "-", String(2*p4), "u");
  TheCommand:=Concatenation(FileCGF, " -v ", String(m), " -g 1", eStrP3, eStrP4, eStrP10);
  Exec(TheCommand);
end;



ExportPlantriFormat:=function(FileName, PL)
  local nbVert, output, i, eVert;
  nbVert:=Length(PL);
  RemoveFileIfExist(FileName);
  output:=OutputTextFile(FileName, true);
  AppendTo(output, nbVert, "\n");
  for i in [1..nbVert]
  do
    AppendTo(output, i-1, " :");
    for eVert in PL[i]
    do
      AppendTo(output, " ", eVert-1);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;

