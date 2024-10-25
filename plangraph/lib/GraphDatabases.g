#
# This is the overarching code that encompass every classes
# of graphs that has been computed or for which we have accessibility methods
#

GetIcosahedriteFixedNumberVertex:=function(nbV)
  local eDir, eFile;
  if nbV>32 then
    Error("Icosahedrites are only available up to 32 vertices");
  fi;
  eDir:=DirectoriesPackageLibrary("plangraph", "DATA")[1];
  eFile:=Filename(eDir,Concatenation("DATAicosahedrites/LPL", String(nbV)));
  return ReadAsFunction(eFile)();
end;



Get0123graphs:=function(iClass, nbV)
  local eDir, eFile;
  eDir:=DirectoriesPackageLibrary("plangraph", "DATA/Data0123")[1];
  eFile:=Filename(eDir,Concatenation("DATA_C", String(iClass), "_", String(nbV)));
  return ReadAsFunction(eFile)();
end;


GetMapDatabasePrefix:=function(k, g, nbV, ListPair)
  local eStr, nbPair, iPair, ePair, pStr;
  eStr:=Concatenation("LPL_g", String(g), "_k", String(k), "_p");
  nbPair:=Length(ListPair);
  for iPair in [1..nbPair]
  do
    ePair:=ListPair[iPair];
    pStr:=Concatenation(String(ePair[1]), "_", String(ePair[2]));
    if iPair > 1 then
      eStr:=Concatenation(eStr, "_-_");
    fi;
    eStr:=Concatenation(eStr, pStr);
  od;
  #
  eStr:=Concatenation(eStr, "_n", String(nbV));
  return eStr;
end;


Get5valentPlaneGraph:=function(n)
  local eDir, eFile;
  eDir:=DirectoriesPackageLibrary("plangraph", "DATA/5valentPlaneGraphs")[1];
  eFile:=Filename(eDir,Concatenation("LPLfilt", String(n)));
  if IsExistingFile(eFile)=false then
    Print("File eFile=", eFile, " is missing\n");
    Error("Probably missing computation\n");
  fi;
  return ReadAsFunction(eFile)();
end;




QueryKnownComputation:=function(k, g, nbV, ListPair)
  local eStr, eDir, eFile1, eFile2, LPL, eInfo;
  eStr:=GetMapDatabasePrefix(k, g, nbV, ListPair);
  eDir:=DirectoriesPackageLibrary("plangraph", "DATA/MapDatabase")[1];
  eFile1:=Filename(eDir,Concatenation(eStr, ".data"));
  eFile2:=Filename(eDir,Concatenation(eStr, ".info"));
  if IsExistingFile(eFile1)=false or IsExistingFile(eFile2)=false then
    Print("Missing file eFile1=", eFile1, "\n");
    Print("Missing file eFile2=", eFile2, "\n");
    return rec(success:=false);
  fi;
  LPL:=ReadAsFunction(eFile1)();
  eInfo:=ReadAsFunction(eFile2)();
  return rec(success:=true, 
             LPL:=LPL,
             IsPLori:=eInfo.IsPLori,
             IsFull:=eInfo.Complete);
end;


Get26GrunbaumZaksMaps:=function(n)
  local LPL, LPLret, PLori, VEFori, ListVertSize, ListFaceSize;
  LPL:=123_GetAdmissibleGraphs(n, "equality");
  LPLret:=[];
  for PLori in LPL
  do
    VEFori:=PlanGraphOrientedToVEF(PLori);
    ListVertSize:=List(VEFori.VertSet, Length);
    ListFaceSize:=List(VEFori.FaceSet, Length);
    if Set(ListVertSize)<>[3] then
      Error("Deep error in the enumeration");
    fi;
    if Set(ListFaceSize)=[2,6] then
      Add(LPLret, PLori);
    fi;
  od;
  return LPLret;
end;



GetSpecificClassOfGraph:=function(eCase)
  local kCodeg, g, ListPair, eSumIncd, iPair, eNb, eGon, nbV, ListFaceSize, nbPair, LPL, ListValence, eRequest;
  kCodeg:=eCase.kCodeg;
  g:=eCase.g;
  ListPair:=eCase.ListPair;
  eSumIncd:=0;
  nbPair:=Length(ListPair);
  ListFaceSize:=List(ListPair, x->x[1]);
  ListValence:=List(ListPair, x->x[1]);
  for iPair in [1..nbPair]
  do
    eNb:=ListPair[iPair][2];
    eGon:=ListPair[iPair][1];
    eSumIncd:=eSumIncd + eNb*eGon;
  od;
  nbV:=eSumIncd/kCodeg;
  eRequest:=QueryKnownComputation(kCodeg, g, nbV, ListPair);
  if eRequest.success=true then
    return eRequest;
  fi;
  if g=0 then
    if kCodeg=3 then
      if Set(ListFaceSize)=[2,6] then
        return rec(LPL:=Get26GrunbaumZaksMaps(nbV), IsPLori:=true, IsFull:=true);
      fi;
      LPL := GetList3valentPlaneGraphSpecifiedFvector(nbV, ListPair);
      return rec(LPL:=LPL, IsPLori:=false, IsFull:=true);
    fi;
    if kCodeg=4 then
      ListFaceSize:=List(ListPair, x->x[1]);
      LPL := GetList4valentPlaneGraphSpecifiedFaceSet(nbV, ListFaceSize);
      return rec(LPL:=LPL, IsPLori:=false, IsFull:=true);
    fi;
    if kCodeg=5 then
      Error("This needs to be programmed");
    fi;
    if kCodeg=6 then
      Error("This needs to be programmed");
    fi;
  else
    if kCodeg=3 then
      LPL:=GetList3valentOrientedMapsSpecifiedFvector(nbV, g, ListPair);
      return rec(LPL:=LPL, IsPLori:=false, IsFull:=true);
    else
      Error("Please program relevant program");
    fi;
  fi;
  Print("Request for list of graphs failed\n");
  Print("kCodeg=", kCodeg, "\n");
  Print("g=", g, "\n");
  Print("nbV=", nbV, "\n");
  Print("ListPair=", ListPair, "\n");
  Error("We did not match anything. You probably need to program accessibility routine yourself");
end;


SaveToStandardDatabaseName:=function(LPLori)
  local ListName, ePLori, VEFori, EulerChar, eGenus, CollVert, kCodeg, CollFace, eName, IsFirst, eEnt, eStr, nbVert;
  ListName:=[];
  for ePLori in LPLori
  do
    VEFori:=PlanGraphOrientedToVEF(ePLori);
    EulerChar:=Length(VEFori.VertSet) - Length(VEFori.EdgeSet) + Length(VEFori.FaceSet);
    eGenus:=(2 - EulerChar)/2;
    CollVert:=Collected(List(VEFori.VertSet,Length));
    if Length(CollVert)<>1 then
      Error("Inconsistency in degree of vertices");
    fi;
    kCodeg:=CollVert[1][1];
    CollFace:=Collected(List(VEFori.FaceSet,Length));
    eName:=Concatenation("LPL_g", String(eGenus), "_k", String(kCodeg), "_p");
    IsFirst:=true;
    for eEnt in CollFace
    do
      eStr:=Concatenation(String(eEnt[1]), "_", String(eEnt[2]));
      if IsFirst=false then
        eName:=Concatenation(eName, "_-_");
      fi;
      IsFirst:=false;
      eName:=Concatenation(eName, eStr);
    od;
    nbVert:=Length(VEFori.VertSet);
    eName:=Concatenation(eName, "_n", String(nbVert), ".data");
    Add(ListName, eName);
  od;
  if Length(Set(ListName))<>1 then
    Error("There is more than 1 name. Impossible");
  fi;
  SaveDataToFile(ListName[1], LPLori);
end;




CheckMatchingPlanGraphOriented:=function(PLori, eCase)
  local kCodeg, g, ListPair, nbV, VEFori, ListDeg, ListMult, nbPair, ListMultAtt, eFace, len, pos, nbVert, nbEdge, nbFace, Charac;
  kCodeg:=eCase.kCodeg;
  g:=eCase.g;
  ListPair:=eCase.ListPair;
  nbV:=eCase.nbV;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  if First(VEFori.VertSet, x->Length(x)<>kCodeg)<>fail then
    Print("Fail at vertex degree kCodeg=", kCodeg, " ListPair=", ListPair, " nbV=", nbV, " g=", g, "\n");
    return false;
  fi;
  ListDeg:=List(ListPair, x->x[1]);
  ListMult:=List(ListPair, x->x[2]);
  nbPair:=Length(ListMult);
  ListMultAtt:=ListWithIdenticalEntries(nbPair,0);
  for eFace in VEFori.FaceSet
  do
    len:=Length(eFace);
    pos:=Position(ListDeg, len);
    if pos=fail then
      Print("Fail at face size\n");
      return false;
    fi;
    ListMultAtt[pos]:=ListMultAtt[pos] + 1;
  od;
  if ListMultAtt<>ListMult then
    Print("Fail at multiplicities\n");
    return false;
  fi;
  nbVert:=Length(VEFori.VertSet);
  nbEdge:=Length(VEFori.EdgeSet);
  nbFace:=Length(VEFori.FaceSet);
  Charac:=nbVert - nbEdge + nbFace;
  if Charac <>2 - 2*g then
    Print("Fail at characteristic\n");
    return false;
  fi;
  return true;
end;





IteratorListPlanGraph:=function(PrefixSave, eCase)
  local InitialComputationLPL, RetrievePlanGraphOriented, ListIFile, ListIPL, iFileCurrent, GetAll, IsPLori, IsFull, PartLPL, nbG;
  InitialComputationLPL:=function()
    local iFile, LPLfile, PartLPL, nbPartG, iPart, RecFull, RecAnswerB, FileGlobInfo, LPL;
    FileGlobInfo:=Concatenation(PrefixSave, "FullStatus");
    iFile:=1;
    nbG:=0;
    ListIFile:=[];
    ListIPL:=[];
    while(true)
    do
      LPLfile:=Concatenation(PrefixSave, "LPL", String(iFile));
      if IsExistingFile(LPLfile)=false then
        break;
      fi;
      PartLPL:=ReadAsFunction(LPLfile)();
      nbPartG:=Length(PartLPL);
      for iPart in [1..nbPartG]
      do
        Add(ListIFile, iFile);
        Add(ListIPL, iPart);
      od;
      nbG:=nbG + nbPartG;
      iFile:=iFile+1;
    od;
    if nbG>0 then
      if IsExistingFile(FileGlobInfo)=false then
        Print("FileGlobInfo=", FileGlobInfo, " is missing\n");
        Error("Missing file");
      fi;
      RecFull:=ReadAsFunction(FileGlobInfo)();
      IsFull:=RecFull.IsFull;
      IsPLori:=RecFull.IsPLori;
    else
      RecAnswerB:=GetSpecificClassOfGraph(eCase);
      IsFull:=RecAnswerB.IsFull;
      IsPLori:=RecAnswerB.IsPLori;
      LPL:=RecAnswerB.LPL;
      #
      nbG:=Length(LPL);
      LPLfile:=Concatenation(PrefixSave, "LPL1");
      SaveDataToFile(LPLfile, LPL);
      iFile:=1;
      for iPart in [1..nbG]
      do
        Add(ListIFile, iFile);
        Add(ListIPL, iPart);
      od;
      RecFull:=rec(IsFull:=IsFull, IsPLori:=IsPLori);
      Print("Doing saving\n");
      SaveDataToFile(FileGlobInfo, RecFull);
    fi;
    Print("We have nbG=", nbG, "\n");
  end;
  PartLPL:="unset";
  RetrievePlanGraphOriented:=function(iPL)
    local iFile, iPos, LPLfile, ePL, PLori;
    iFile:=ListIFile[iPL];
    iPos:=ListIPL[iPL];
    if iFileCurrent<>iFile then
      LPLfile:=Concatenation(PrefixSave, "LPL", String(iFile));
      PartLPL:=ReadAsFunction(LPLfile)();
      iFileCurrent:=iFile;      
    fi;
    if IsPLori=false then
      ePL:=PartLPL[iPos];
      PLori:=PlanGraphToPlanGraphOriented(ePL);
    else
      PLori:=PartLPL[iPos];
    fi;
    return PLori;
  end;
  GetAll:=function()
    local LPLret, iPL;
    LPLret:=[];
    for iPL in [1..nbG]
    do
      Add(LPLret, RetrievePlanGraphOriented(iPL));
    od;
    return LPLret;
  end;
  InitialComputationLPL();
  #
  iFileCurrent:=-1;
  return rec(nbG:=nbG,
             IsFull:=IsFull,
             RetrievePlanGraphOriented:=RetrievePlanGraphOriented,
	     GetAll:=GetAll);
end;

