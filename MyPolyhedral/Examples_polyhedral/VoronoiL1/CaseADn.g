TheLatt:="A";
#TheLatt:="D";
TheNorm:="L1";
#TheNorm:="Li";
nMin:=2;
nMax:=6;

for n in [nMin..nMax]
do
  Print("n=", n, " TheLatt=", TheLatt, " TheNorm=", TheNorm, "\n");
  if TheLatt="A" then
    Print("Case A\n");
    eRecLatt:=Vor_Linfinity_L1_An(n);
  else
    Print("Case D\n");
    eRecLatt:=Vor_Linfinity_L1_Dn(n);
  fi;
  if TheNorm="L1" then
    eRecL1:=eRecLatt.eRec_L1;
  else
    eRecL1:=eRecLatt.eRec_Li;
  fi;
  FileSave:=Concatenation("DATA/B_ListRecCompCell", TheNorm, "_", TheLatt, String(n));
  if IsExistingFilePlusTouch(FileSave)=false then
    ListRecCompCell:=VOR_L1_FullEnumerationCell(eRecL1);
    SaveDataToFilePlusTouch(FileSave, rec(ListRecCompCell:=ListRecCompCell));
  else
    eRecSave:=ReadAsFunction(FileSave)();
    ListRecCompCell:=eRecSave.ListRecCompCell;
  fi;
  FileSave:=Concatenation("DATA/B_ListRecCompEquiPlane", TheNorm, "_", TheLatt, String(n));
  if IsExistingFilePlusTouch(FileSave)=false then
    ListEXTinc:=VOR_L1_FullEnumerationFacet(eRecL1, ListRecCompCell);
    SaveDataToFilePlusTouch(FileSave, ListEXTinc);
  else
    ListEXTinc:=ReadAsFunction(FileSave)();
  fi;
  #
  FileData:=Concatenation("DATA/B_ListRecCompData", TheNorm, "_", TheLatt, String(n));
  RemoveFileIfExist(FileData);
  output:=OutputTextFile(FileData, true);
  nbRecCompCell:=Length(ListRecCompCell);
  Print("nbRecCompCell=", nbRecCompCell, "\n");
  AppendTo(output, "nbRecCompCell=", nbRecCompCell, "\n");
  VolCheck:=false;
#  VolCheck:=true;
  if VolCheck then
    SumVol:=0;
    ListVol:=[];
    ListStabSize:=[];
    NbCell:=0;
    for iRecCompCell in [1..nbRecCompCell]
    do
      eRecCompCell:=ListRecCompCell[iRecCompCell];
      eR:=VOR_L1_GetVertices(eRecL1, eRecCompCell);
      TheVol:=VolumeComputationPolytope(eR.EXText);
      Add(ListVol, TheVol);
      eRstab:=VOR_L1_AutomorphismCompFacet(eRecL1, eRecCompCell);
      eStabSize:=Order(eRstab.GRPaff);
      Add(ListStabSize, eStabSize);
      OrbSize:=Order(eRecL1.PointGRP)/eStabSize;
      SumVol:=SumVol + TheVol* OrbSize;
      NbCell:=NbCell + OrbSize;
      Print("iRecCompCell=", iRecCompCell, " / ", nbRecCompCell, " |EXT|=", Length(eR.EXText), " |stab|=", eStabSize, "\n");
      AppendTo(output, "iRecCompCell=", iRecCompCell, " / ", nbRecCompCell, " |EXT|=", Length(eR.EXText), " |stab|=", eStabSize, "\n");
    od;
    Print("SumVol=", SumVol, " NbCell=", NbCell, "\n");
    AppendTo(output, "SumVol=", SumVol, " NbCell=", NbCell, "\n");
  fi;
  #
  # Now Voronoi vertices
  #
  FileSave:=Concatenation("DATA/B_ListRecVoronoi", TheNorm, "_", TheLatt, String(n));
  if IsExistingFilePlusTouch(FileSave)=false then
    eRecVoronoi:=VOR_L1_GetOrbitVertexVoronoi(eRecL1, ListRecCompCell);
    SaveDataToFilePlusTouch(FileSave, eRecVoronoi);
  else
    eRecVoronoi:=ReadAsFunction(FileSave)();
  fi;
  #
  nbOrb:=Length(eRecVoronoi.ListOrbitSize);
  AppendTo(output, "Representatives of orbits of Voronoi vertices\n");
  for iOrb in [1..nbOrb]
  do
    AppendTo(output, iOrb, "/", nbOrb, " |O|=", eRecVoronoi.ListOrbitSize[iOrb], " eRepr=");
    WriteVector(output, eRecVoronoi.ListOrbitRepr[iOrb]*eRecL1.ListVect);
  od;
  #
  #
  AppendTo(output, "Representatives of orbits of Equi planes\n");
  nbOrb:=Length(ListEXTinc);
  for iOrb in [1..nbOrb]
  do
    AppendTo(output, iOrb, "/", nbOrb, "\n");
    WriteMatrix(output, ListEXTinc[iOrb]);
  od;
  #
  CheckListEqui:=false;
  if CheckListEqui then
    Print("Before ChecListEqui\n");
    for eRecCompCell in ListRecCompCell
    do
      eRecEXT:=VOR_L1_GetVertices(eRecL1, eRecCompCell);
      eIso:=Isobarycenter(eRecEXT.EXT);
      ListClos:=VOR_L1_FindClosest(eRecL1, eIso);
      ListEquiPt:=List(eRecCompCell.ListEqui, x->x.ePt);
      if Set(ListClos)<>Set(ListEquiPt) then
        Print("We have a clear error\n");
        Print(NullMat(5));
      fi;
    od;
  fi;
  #
  FileSave:=Concatenation("DATA/B_ListDvertices", TheNorm, "_", TheLatt, String(n));
  if IsExistingFilePlusTouch(FileSave)=false then
    Drec:=VOR_L1_Get_Dvertices(eRecL1, ListRecCompCell);
    SaveDataToFilePlusTouch(FileSave, Drec);
  else
    Drec:=ReadAsFunction(FileSave)();
  fi;
  Print("|Drec|=", Length(Drec.ListVertices), "\n");
  #
  # Now the real Voronoi vertices
  #
  FileTex:=Concatenation("DATA/B_table", TheNorm, "_", TheLatt, String(n), ".tex");
  RemoveFileIfExist(FileTex);
  outputTex:=OutputTextFile(FileTex, true);
  AppendTo(outputTex, "LocalMaxDim=", Drec.LocalMaxDim, "\n");
  TheSel:=Filtered(Drec, x->x.IsTrueVertex=true);
  nbSel:=Length(TheSel);
  Print("|TheSel|=", nbSel, "\n");
  for iSel in [1..nbSel]
  do
    hRec:=TheSel[iSel];
    eVert1:=(hRec.eVert2 - hRec.eVert1)*eRecL1.ListVect;
    ePerm:=SortingPerm(eVert1);
    eVert:=Permuted(eVert1, ePerm);
    AppendTo(outputTex, "(");
    len:=Length(eVert);
    for iCol in [1..len]
    do
      if iCol>1 then
        AppendTo(outputTex, ",");
      fi;
      AppendTo(outputTex, eVert[iCol]);
    od;
    AppendTo(outputTex, ")");
    AppendTo(outputTex, " & ");
    AppendTo(outputTex, hRec.IsMax);
    AppendTo(outputTex, "\\\\\n");
  od;
  CloseStream(outputTex);
  #
  CloseStream(output);
od;

