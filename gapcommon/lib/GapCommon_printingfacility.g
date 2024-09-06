STRING_Split:=function(eStr, ePat)
  local lenStr, lenPat, lenTest, ListMatch, i, eStrPart, ListStrInter, iVal, eVal, FirstVal, nbMatch, eStrInter;
  lenStr:=Length(eStr);
  lenPat:=Length(ePat);
#  Print("lenStr=", lenStr, " lenPat=", lenPat, "\n");
  ListMatch:=[];
  lenTest:=lenStr - (lenPat-1);
  for i in [1..lenTest]
  do
    eStrPart:=eStr{[i..i+lenPat-1]};
#    Print("i=", i, " eStrPart=", eStrPart, "\n");
    if eStrPart=ePat then
      Add(ListMatch, i);
    fi;
  od;
  nbMatch:=Length(ListMatch);
  if nbMatch=0 then
    return rec(ListStrInter:=[eStr], ListMatch:=[]);
  fi;
  Print("nbMatch=", nbMatch, "\n");
  ListStrInter:=[];
  for iVal in [1..nbMatch]
  do
    eVal:=ListMatch[iVal];
    if eVal>1 then
      if iVal>1 then
        FirstVal:=ListMatch[iVal-1]+lenPat;
      else
        FirstVal:=1;
      fi;
      eStrInter:=eStr{[FirstVal..eVal-1]};
      Add(ListStrInter, eStrInter);
    fi;
    if iVal=nbMatch then
      if eVal+lenPat<lenStr then
        FirstVal:=eVal+lenPat;
        eStrInter:=eStr{[FirstVal..lenStr]};
        Add(ListStrInter, eStrInter);
      fi;
    fi;
  od;
  return rec(ListStrInter:=ListStrInter, ListMatch:=ListMatch);
end;


PrintStabChain:=function(eG)
  local eRec, iLev;
  eRec:=StabChain(eG);
  iLev:=0;
  while(true)
  do
    Print("iLev=", iLev, "\n");
    if IsBound(eRec.transversal)=false then
      break;
    fi;
    Print("  transversal=", eRec.transversal, "\n");
    Print("  orbit=", eRec.orbit, "\n");
    Print("  genlabels=", eRec.genlabels, "\n");
    if IsBound(eRec.stabilizer) then
      eRec:=eRec.stabilizer;
    else
      break;
    fi;
    iLev:=iLev+1;
  od;
end;


LocalUpperInteger:=function(eFrac)
  local a, b, r;
  if IsInt(eFrac)=true then
    return eFrac;
  fi;
  a:=NumeratorRat(eFrac);
  b:=DenominatorRat(eFrac);
  r:=a mod b;
  return (a+b-r)/b;
end;


STRING_SplittingByBlock:=function(ListStr, nbPerLine)
  local nbEnt, nbLine, ListStrBlock, iLine, eStrBlock, idx, iPos;
  nbEnt:=Length(ListStr);
  if nbEnt=0 then
    return [""];
  fi;
  nbLine:=LocalUpperInteger(nbEnt / nbPerLine);
  ListStrBlock:=[];
  for iLine in [1..nbLine]
  do
    eStrBlock:="";
    for idx in [1..nbPerLine]
    do
      iPos:=nbPerLine*(iLine-1) + idx;
      if iPos<=nbEnt then
        eStrBlock:=Concatenation(eStrBlock, ListStr[iPos]);
        if iPos < nbEnt then
          eStrBlock:=Concatenation(eStrBlock, ",");
        fi;
      fi;
    od;
    Add(ListStrBlock, eStrBlock);
  od;
  return ListStrBlock;
end;







# File must be of the form path/file_pre.tex
# The footer and header are added
# to form the path/file.tex
# and the compilation is done with latex/dvips/ps2pdf
LATEX_Compilation:=function(eFile)
  local FinalFileTex, FinalFileDVI, FinalFileTexB, FinalFileDVIB, FinalFilePSB, eDirTEX, eFileFoot, eFileHead, eSplit, LastStr, lenLast, eFileRed, eSuffix, posSlash, eDir;
  eSplit:=STRING_Split(eFile, "/");
  LastStr:=eSplit.ListStrInter[Length(eSplit.ListStrInter)];
  lenLast:=Length(LastStr);
  eFileRed:=LastStr{[1..lenLast-8]};
  eSuffix:=LastStr{[lenLast-7..lenLast]};
  if eSuffix<>"_pre.tex" then
    Print("eFile=", eFile, "\n");
    Print("LastStr=", LastStr, "\n");
    Error("Last characters of LastStr should be _pre.tex");
  fi;
  posSlash:=eSplit.ListMatch[Length(eSplit.ListMatch)];
  eDir:=eFile{[1..posSlash]};
  FinalFileTex:=Concatenation(eDir, "/", eFileRed, ".tex");
  FinalFileDVI:=Concatenation(eDir, "/", eFileRed, ".dvi");
  FinalFileTexB:=Concatenation(eFileRed, ".tex");
  FinalFileDVIB:=Concatenation(eFileRed, ".dvi");
  FinalFilePSB:=Concatenation(eFileRed, ".ps");
  eDirTEX:=DirectoriesPackageLibrary("gapcommon", "DATA/TEX")[1];
  eFileFoot:=Filename(eDirTEX, "Footer.tex");
  eFileHead:=Filename(eDirTEX, "Header.tex");
  Exec("cat ", eFileHead, " ", eFile, " ", eFileFoot, " > ", FinalFileTex);
  Exec("(cd ", eDir, " && latex ", FinalFileTexB, ")");
  Exec("(cd ", eDir, " && dvips ", FinalFileDVIB, " -o )");
  Exec("(cd ", eDir, " && ps2pdf ", FinalFilePSB, ")");
end;

