FileGetFullRankFacetSet:=GetBinaryFilename("POLY_GetFullRankFacetSet");
FilePolyDualDescription:=GetBinaryFilename("POLY_dual_description");
FileLCDD:=GetBinaryFilename("lcdd_gmp");
FileSCDD:=GetBinaryFilename("scdd_gmp");
FilePPL_LCDD:=GetBinaryFilename("ppl_lcdd");
FileGRP_IsomorphismReduction:=GetBinaryFilename("GRP_IsomorphismReduction");
FileGLRS:=GetBinaryFilename("glrs");


ReadCDD_LRS_output:=function(FileName)
    local list_lines, FAC, IsInside, line, eFAC, LStr, eStr, eVal;
    list_lines:=ReadTextFile(FileName);
    FAC:=[];
    IsInside:=false;
    for line in list_lines
    do
        if ends_with(line, "rational")<>fail then
            IsInside:=true;
        else
            if line="end" then
                IsInside:=false;
            else
                if IsInside then
                    eFAC:=[];
                    LStr:=SplitString(line, " ");
                    for eStr in LStr
                    do
                        if Length(eStr) > 0 then
                            eVal:=Rat(eStr);
                            Add(eFAC, eVal);
                        fi;
                    od;
                    Add(FAC, eFAC);
                fi;
            fi;
        fi;
    od;
    return FAC;
end;




OutputGroup:=function(GroupExt, nbExt, FileGroup)
  local output, ListGens, nbGen, eGen, eList, i;
  ListGens:=GeneratorsOfGroup(GroupExt);
  nbGen:=Length(ListGens);
  output:=OutputTextFile(FileGroup, true);;
  AppendTo(output, nbExt, " ", nbGen, "\n");
  for eGen in ListGens
  do
    eList:=OnTuples([1..nbExt], eGen);
    for i in [1..nbExt]
    do
      AppendTo(output, " ", eList[i]);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;



#
#
# Pass from one description to the other using RAW cdd program
DualDescription_Rational:=function(EXT)
  local FileExt, FileIne, output, FAC, FileErr, EXTred;
  if Length(Set(List(EXT,Length)))<>1 then
    Error("DualDescription_Rational: Input should be vectors of the same length");
  fi;
  if RankMat(EXT)<>Length(EXT[1]) then
    Print("DualDescription_Rational: The rank is not correct\n");
    Print("| EXT[1] |=", Length(EXT[1]), "  rnk=", RankMat(EXT), "\n");
    Error("Please correct");
  fi;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"CDD_Desc.ext");
  FileErr:=Filename(POLYHEDRAL_tmpdir,"CDD_Desc.err");
  FileIne:=Filename(POLYHEDRAL_tmpdir,"CDD_Desc.ine");
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), "  ", Length(EXT[1]), "  integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  Exec(FileLCDD, " ", FileExt, " > ", FileIne, " 2> ", FileErr);
  FAC:=ReadCDD_LRS_output(FileIne);
  if Length(FAC)=0 then
    Error("FAC is empty");
  fi;
  RemoveFile(FileExt);
  RemoveFile(FileErr);
  RemoveFile(FileIne);
  return FAC;
end;


DualDescription_General_Code:=function(EXT)
  local Nval;
  if IsMatrixRational(EXT)=true then
    return DualDescription_Rational(EXT);
  fi;
  Error("You have to build your own arithmetic");
end;


DualDescription:=function(EXT)
  if IsMatrixRational(EXT)=true then
    return DualDescription_Rational(EXT);
  fi;
  Print("Need to put arithmetic or use DualDescriptionGeneralCode\n");
  Error("You have to build your own arithmetic");
end;


EliminationByRedundancyDualDescription:=function(FAC)
  local FACred, EXTred, TheRank, FACreturn, nbFac, iFac, eFac, eFacRed, LINC, eEXT;
  FACred:=ColumnReduction(FAC).EXT;
  EXTred:=DualDescription(FACred);
  TheRank:=Length(FACred[1]);
  FACreturn:=[];
  nbFac:=Length(FACred);
  for iFac in [1..nbFac]
  do
    eFac:=FAC[iFac];
    eFacRed:=FACred[iFac];
    LINC:=[];
    for eEXT in EXTred
    do
      if eEXT*eFacRed=0 then
        Add(LINC, eEXT);
      fi;
    od;
    if PersoRankMat(LINC)=TheRank-1 then
      Add(FACreturn, eFac);
    fi;
  od;
  return FACreturn;
end;




DualDescriptionSets:=function(EXT)
  local eSelect, EXTproj, FACproj;
  eSelect:=ColumnReduction(EXT).Select;
  EXTproj:=List(EXT, x->x{eSelect});
  FACproj:=DualDescription(EXTproj);
  return List(FACproj, x->Filtered([1..Length(EXTproj)], y->EXTproj[y]*x=0));
end;

RemoveRedundancyByDualDescription_Kernel:=function(EXT)
  local eSelect, EXTproj, FACproj, eSet, len, idx, FACinc;
  if Length(EXT)=1 then
    return EXT;
  fi;
  eSelect:=ColumnReduction(EXT).Select;
  EXTproj:=List(EXT, x->RemoveFraction(x{eSelect}));
  len:=Length(EXTproj[1]);
  FACproj:=DualDescription(EXTproj);
  eSet:=[];
  for idx in [1..Length(EXTproj)]
  do
    FACinc:=Filtered(FACproj, x->x*EXTproj[idx]=0);
    if Length(FACinc)>0 then
      if RankMat(FACinc)=len-1 then
        Add(eSet, idx);
      fi;
    fi;
  od;
  return Set(EXT{eSet});
end;

RemoveRedundancyByDualDescription:=function(EXT0)
  local EXT1, EXT2, EXT3;
  EXT1:=Filtered(EXT0, x->x*x>0);
  EXT2:=List(EXT1, RemoveFraction);
  EXT3:=Set(EXT2);
  return RemoveRedundancyByDualDescription_Kernel(EXT3);
end;


WriteCddInputVertices:=function(FileName, EXT)
  local output;
  output:=OutputTextFile(FileName, true);
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), "  ", Length(EXT[1]), "  integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  CloseStream(output);
end;

ReadCddGraph:=function(FileName)
    local list_lines, IsInside, list_lines_red, line, line_nb, LStr, n_vert, eStr, g, LAdj, LTot, LStrA, LStrB, i, eStrA, eStrB, eVal, eAdj;
    list_lines:=ReadTextFile(FileName);
    #
    IsInside:=false;
    list_lines_red:=[];
    for line in list_lines
    do
        if line="begin" then
            IsInside:=true;
        else
            if line="end" then
                IsInside:=false;
            else
                if IsInside then
                    Add(list_lines_red, line);
                fi;
            fi;
        fi;
    od;
    #
    line_nb:=list_lines_red[1];
    LStr:=SplitString(line_nb, " ");
    n_vert:=0;
    for eStr in LStr
    do
        if Length(eStr) > 0 then
            n_vert:=Int(eStr);
        fi;
    od;
    if n_vert=0 then
        Error("n_vert=0 is not allowed");
    fi;
    #
    g:=NullGraph(Group(()), n_vert);
    for i in [1..n_vert]
    do
        eStrA:=list_lines_red[i+1];
        LStrA:=SplitString(eStrA, ":");
        if Length(LStrA)<>2 then
            Error("LStrA should have length 2");
        fi;
        LStrB:=SplitString(LStrA[2], " ");
        LAdj:=[];
        for eStrB in LStrB
        do
            if Length(eStrB) > 0 then
                eVal:=Int(eStrB);
                Add(LAdj, eVal);
            fi;
        od;
        if Length(SplitString(LStrA[1], "-"))=2 then
            LTot:=Difference([1..n_vert], [i]);
            LAdj:=Difference(LTot, LAdj);
        fi;
        for eAdj in LAdj
        do
            AddEdgeOrbit(g, [i, eAdj]);
        od;
    od;
    return g;
end;






DualDescriptionAdjacencies:=function(EXT)
  local FileExt, FileIne, FileLog, FileErr, FileDdl, FileIad, FileEad, output, RidgeGraph, SkeletonGraph, FAC;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Desc.ext");
  FileIne:=Filename(POLYHEDRAL_tmpdir,"Desc.ine");
  FileLog:=Filename(POLYHEDRAL_tmpdir,"Desc.log");
  FileErr:=Filename(POLYHEDRAL_tmpdir,"Desc.err");
  FileIad:=Filename(POLYHEDRAL_tmpdir,"Desc.iad");
  FileEad:=Filename(POLYHEDRAL_tmpdir,"Desc.ead");
  FileDdl:=Filename(POLYHEDRAL_tmpdir,"Desc.ddl");
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), "  ", Length(EXT[1]), "  integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  AppendTo(output, "adjacency\n");
  AppendTo(output, "input_adjacency\n");
  CloseStream(output);
  Exec(FileSCDD, " ", FileExt, " > ", FileLog, " 2> ", FileErr);
  RidgeGraph:=ReadCddGraph(FileIad);
  SkeletonGraph:=ReadCddGraph(FileEad);
  FAC:=ReadCDD_LRS_output(FileIne);
  RemoveFile(FileExt);
  RemoveFile(FileIne);
  RemoveFile(FileLog);
  RemoveFile(FileErr);
  RemoveFile(FileDdl);
  RemoveFile(FileIad);
  RemoveFile(FileEad);
  if Length(FAC)=0 then
    Error("Error in DualDescriptionAdjacencies");
  fi;
  return rec(FAC:=FAC, SkeletonGraph:=SkeletonGraph, RidgeGraph:=RidgeGraph);
end;


__DualDescriptionPoly:=function(EXT, command, ThePath)
    local FileExt, FileError, FileOut, arith, choice, FAC;
    FileExt:=Concatenation(ThePath, "LRS_Project.ext");
    FileError:=Concatenation(ThePath, "LRS_Project.error");
    FileOut:=Concatenation(ThePath, "LRS_Project.out");
    RemoveFileIfExist(FileExt);
    RemoveFileIfExist(FileError);
    RemoveFileIfExist(FileOut);
    WriteMatrixFile(FileExt, EXT);
    arith:="rational";
    choice:="CPP";
    Exec(FilePolyDualDescription, " ", arith, " ", command, " ", choice, " ", FileExt, " ", FileOut, "2>", FileError);
    FAC:=ReadMatrixFile(FileOut);
    RemoveFileIfExist(FileExt);
    RemoveFileIfExist(FileError);
    RemoveFileIfExist(FileOut);
    return FAC;
end;



__DualDescriptionLRS_Reduction:=function(EXT, GroupExt, ThePath)
  local eSub, EXT2, EXT3, FileExt, FileOut, FileFAC, FAC, FileGroup, FileSupport, FileOutput, FileError, output, DimEXT, test, EXTnew, ListInc;
#  Print("Entering polyhedral function LRS_Reduction |GRP|=", Order(GroupExt), "\n");
  FileExt:=Concatenation(ThePath, "LRS_Project.ext");
  FileOut:=Concatenation(ThePath, "LRS_Project.out");
  FileFAC:=Concatenation(ThePath, "LRS_Project.fac");
  FileGroup:=Concatenation(ThePath, "LRS_Project.group");
  FileSupport:=Concatenation(ThePath, "LRS_Project.supo");
  FileOutput:=Concatenation(ThePath, "LRS_Project.output");
  FileError:=Concatenation(ThePath, "LRS_Project.error");
  #
  output:=OutputTextFile(FileExt, true);
  eSub:=__ProjectionFrame(EXT);
  EXT2:=List(EXT, x->x{eSub});
  EXT3:=List(EXT2, RemoveFraction);
  if TestConicness(EXT3) then
    EXTnew:=ShallowCopy(EXT3);
  else
    EXTnew:=List(EXT3, x->Concatenation([0], x));
  fi;
  DimEXT:=Length(EXTnew[1]);
  #
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXTnew), " ", DimEXT, " integer\n");
  WriteMatrix(output, EXTnew);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  Exec(FileGLRS, " ", FileExt, " > ", FileOut);
  FAC:=ReadCDD_LRS_output(FileOut);
  WriteMatrixFile(FileFAC, FAC);
  #
  WriteMatrixFile(FileSupport, EXTnew);
  #
  SYMPOL_PrintGroup(FileGroup, Length(EXTnew), GroupExt);
  #
  Exec(FileGRP_IsomorphismReduction, " ", FileSupport, " ", FileFAC, " ", FileGroup, " ", FileOutput, "2>", FileError);
  ListInc:=ReadAsFunction(FileOutput)();
  if Length(ListInc)=0 then
    Error("Error in DualDescriptionLRS_Reduction");
  fi;
  RemoveFile(FileExt);
  RemoveFile(FileOut);
  RemoveFile(FileFAC);
  RemoveFile(FileGroup);
  RemoveFile(FileSupport);
  RemoveFile(FileOutput);
  RemoveFile(FileError);
  return ListInc;
end;


DualDescriptionLRS:=function(EXT, GroupExt)
  local ThePath;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  return __DualDescriptionLRS_Reduction(EXT, GroupExt, ThePath);
end;


ReadCddRaysOutput:=function(FileOut)
    local list_lines, list_lines_red, IsInside, eLine, end_str, len_end_str, ends_rational, pos_start, len;
    list_lines:=ReadTextFile(FileOut);
    list_lines_red:=[];
    IsInside:=false;
    end_str:="rational";
    len_end_str:=Length(end_str);
    for eLine in list_lines
    do
        len:=Length(eLine);
        ends_rational:=false;
        if IsInside=false then
            if len > len_end_str then
                pos_start:=len - len_end_str + 1;
                if eLine{[pos_start..len]}=end_str then
                    ends_rational:=true;
                fi;
            fi;
        fi;
        if ends_rational then
            IsInside:=true;
        else
            if eLine="end" then
                IsInside:=false;
            else
                if IsInside then
                    Add(list_lines_red, eLine);
                fi;
            fi;
        fi;
    od;
    return ReadVector_list_lines(list_lines_red);
end;





__DualDescriptionDoubleDescMethod_Reduction:=function(EXT, GroupExt, ThePath, TheProg)
  local eSub, EXT2, FileExt, FileOut, FileFAC, FileGroup, FileSupport, FileOutput, output, DimEXT, test, EXTnew, ListInc, FileError, TheCommand, FACread;
#  Print("Entering polyhedral function CDD_Reduction |GRP|=", Order(GroupExt), "\n");
  FileExt:=Concatenation(ThePath, "DD_Project.ext");
  FileOut:=Concatenation(ThePath, "DD_Project.out");
  FileFAC:=Concatenation(ThePath, "DD_Project.data");
  FileGroup:=Concatenation(ThePath, "DD_Project.group");
  FileSupport:=Concatenation(ThePath, "DD_Project.supo");
  FileOutput:=Concatenation(ThePath, "DD_Project.output");
  FileError:=Concatenation(ThePath, "DD_Project.error");
  #
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
  if TheProg<>"CDD" and TheProg<>"PPL" then
    Error("TheProg should be CDD or PPL");
  fi;
  if TheProg="CDD" then
    TheCommand:=Concatenation(FileLCDD, " ", FileExt, " > ", FileOut, " 2> ", FileError);
  fi;
  if TheProg="PPL" then
    TheCommand:=Concatenation(FilePPL_LCDD, " ", FileExt, " > ", FileOut, " 2> ", FileError);
  fi;
  Exec(TheCommand);
#  Print("Double description computation finished\n");
  #
  FACread:=ReadCddRaysOutput(FileOut);
  WriteMatrixFile(FileFAC, FACread);
  #
  WriteMatrixFile(FileSupport, EXTnew);
  #
  SYMPOL_PrintGroup(FileGroup, Length(EXTnew), GroupExt);
  #
  TheCommand:=Concatenation(FileGRP_IsomorphismReduction, " ", FileSupport, " ", FileFAC, " ", FileGroup, " ", FileOutput, " 2>", FileError);
  Exec(TheCommand);
  ListInc:=ReadAsFunction(FileOutput)();
  if Length(ListInc)=0 then
    Error("Error in DualDescriptionCDD_Reduction");
  fi;
#  Print("Isomorphism reduction finished\n");
  RemoveFile(FileExt);
  RemoveFile(FileOut);
  RemoveFile(FileFAC);
  RemoveFile(FileGroup);
  RemoveFile(FileSupport);
  RemoveFile(FileOutput);
  RemoveFile(FileError);
  return ListInc;
end;





__DualDescriptionCDD_Reduction:=function(EXT, GroupExt, ThePath)
  return __DualDescriptionDoubleDescMethod_Reduction(EXT, GroupExt, ThePath, "CDD");
end;

__DualDescriptionPPL_Reduction:=function(EXT, GroupExt, ThePath)
  return __DualDescriptionDoubleDescMethod_Reduction(EXT, GroupExt, ThePath, "PPL");
end;



DualDescriptionCDD:=function(EXT, GroupExt)
  local ThePath;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  return __DualDescriptionCDD_Reduction(EXT, GroupExt, ThePath);
end;


DualDescriptionPPL:=function(EXT, GroupExt)
  local ThePath;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  return __DualDescriptionPPL_Reduction(EXT, GroupExt, ThePath);
end;



GetFullRankFacetSet_GAP:=function(EXT)
    local dim, nb, rnk, MinSiz, EXTred, EXTpoly, ListSets, FAC, eSet, EXTsel, ListRidge, RPLift, ListSetsB;
    # Heuristic first, should work in many cases
    EXTred:=ColumnReduction(EXT).EXT;
    dim:=Length(EXTred[1]);
    nb:=10 * dim;
    EXTpoly:=PolytopizationGeneralCone(EXTred);
    Print("We have EXTpoly\n");
    ListSets:=GetInitialRaysEXT(EXTpoly, nb);
    Print("We have ListSets\n");
    FAC:=Set(List(ListSets, x->__FindFacetInequality(EXTpoly, x)));
    rnk:=RankMat(FAC);
    Print("GetFullRankFacetSet |FAC|=", Length(FAC), " |EXT|=", Length(EXT), " rnk=", rnk, " dim=", dim, "\n");
    if rnk = dim then # The heuristic works
        return ListSets;
    fi;
    # Otherwise we call recursively
    Print("Failing, so calling the recursive algo\n");
    MinSiz:=Minimum(List(ListSets, Length));
    eSet:=First(ListSets, x->Length(x)=MinSiz);
    EXTsel:=EXTred{eSet};
    ListRidge:=GetFullRankFacetSet_GAP(EXTsel);
    RPLift:=__ProjectionLiftingFramework(EXTred, eSet);
    ListSetsB:=List(ListRidge, RPLift.FuncLift);
    return Concatenation([eSet], ListSetsB);
end;


GetFullRankFacetSet:=function(EXT)
    local FileEXT, FileFAC_part, eCommand, TheReply;
    FileEXT:=Filename(POLYHEDRAL_tmpdir,"GetFullRankFacetSet.input");
    FileFAC_part:=Filename(POLYHEDRAL_tmpdir,"GetFullRankFacetSet.output");
    SYMPOL_PrintMatrix(FileEXT, EXT);
    #
    eCommand:=Concatenation(FileGetFullRankFacetSet, " ", FileEXT, " ", FileFAC_part);
    Print("eCommand=", eCommand, "\n");
    Exec(eCommand);
    TheReply:=ReadAsFunction(FileFAC_part)();
    RemoveFile(FileEXT);
    RemoveFile(FileFAC_part);
    return TheReply;
end;





# Here we implement the enumeration by using the PD
# method equivariantly.
# That is, once we find a new facet, we add it systematically.
__DualDescriptionPD_Reduction:=function(EXT, GRP, ThePath)
    local EXTpoly, TheDim, nbVert, ListOrbit, FAC, FuncInsert, FuncInsertIfNew, nb, ListSets, eSet, EXTfind, EXTfindCan, EXTcall, eFAC, EXTpolySet, GetFACnew, ListWrong, iWrong, jWrong, nbWrong, eEXT, ListStatus, fEXT, FACnew;
    EXTpoly:=PolytopizationGeneralCone(EXT);
    Print("We have EXTpoly\n");
    EXTpolySet:=Set(EXTpoly);
    TheDim:=Length(EXTpoly[1]);
    nbVert:=Length(EXTpoly);
    ListOrbit:=[];
    FAC:=[];
    GetFACnew:=function(eOrb)
        local FACnew, O, eRepr, eFAC;
        FACnew:=[];
        O:=Orbit(GRP, eOrb, OnSets);
        for eRepr in O
        do
            eFAC:=__FindFacetInequality(EXTpoly, eRepr);
            Add(FACnew, eFAC);
        od;
        return FACnew;
    end;
    FuncInsert:=function(eOrb)
        Add(ListOrbit, eOrb);
        Append(FAC, GetFACnew(eOrb));
    end;
    FuncInsertIfNew:=function(eOrb)
        local fOrb, test;
        for fOrb in ListOrbit
        do
            test:=RepresentativeAction(GRP, eOrb, fOrb, OnSets);
            if test<>fail then
                return;
            fi;
        od;
        FuncInsert(eOrb);
    end;
    #
    # First part of the enumeration:
    # Finding sufficient inequality for a full dimensional polytope.
    #
    for eSet in GetFullRankFacetSet(EXT)
    do
        FuncInsertIfNew(eSet);
    od;
    Print("We have FAC\n");
    #
    # Second part of the enumeration:
    # Iterating with linear programs
    #
    while(true)
    do
        EXTfind:=DualDescription(FAC);
        ListWrong:=[];
        for eEXT in EXTfind
        do
            if eEXT[1] <= 0 then
                Add(ListWrong, eEXT);
            else
                fEXT:=eEXT/eEXT[1];
                if not(fEXT in EXTpolySet) then
                    Add(ListWrong, eEXT);
                fi;
            fi;
        od;
        nbWrong:=Length(ListWrong);
        if nbWrong=0 then
            break;
        fi;
        ListStatus:=ListWithIdenticalEntries(nbWrong,0);
        for iWrong in [1..nbWrong]
        do
            if ListStatus[iWrong]=0 then
                eSet:=GetViolatedFacet(EXTpoly, ListWrong[iWrong]);
                Add(ListOrbit, eSet);
                FACnew:=GetFACnew(eSet);
                Append(FAC, FACnew);
                for jWrong in [iWrong..nbWrong]
                do
                    if ListStatus[jWrong]=0 then
                        if First(FACnew, x->x*ListWrong[jWrong]<0)<>fail then
                            ListStatus[jWrong]:=1;
                        fi;
                    fi;
                od;
            fi;
        od;
    od;
    return ListOrbit;
end;

__DualDescriptionPD_Reduction_Equivariant:=function(EXT, GRP)
  local ThePath;
  ThePath:="/irrelevant";
  return __DualDescriptionPD_Reduction(EXT, GRP, ThePath);
end;
