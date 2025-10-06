FileSV_exact:=GetBinaryFilename("sv_exact");
FileLATT_near:=GetBinaryFilename("LATT_near");

ReadSV_output:=function(FileName)
    local list_lines, list_vect, n_vect, i, LStrA, LStrB, eVect, eStr, eVal;
    list_lines:=ReadTextFile(FileName);
    n_vect:=Int(list_lines[1]);
    list_vect:=[];
    for i in [1..n_vect]
    do
        LStrA:=SplitString(list_lines[i+1], ":");
        if Length(LStrA)<>2 then
            Error("LStrA should have length 2");
        fi;
        LStrB:=SplitString(LStrA[2], " ");
        eVect:=[];
        for eStr in LStrB
        do
            if Length(eStr) > 0 then
                eVal:=Int(eStr);
                Add(eVect, eVal);
            fi;
        od;
        Add(list_vect, eVect);
    od;
    return list_vect;
end;

# This function should return the solutions of the equation
# (x - eV) G (x - eV) <= TheDist.
#
Kernel_ClosestAtDistanceVallentinProgram:=function(GramMat, eV, TheDist, recOption)
  local FileIn, FilePreIn, FileOut, FileGap, FileErr, test, n, output, i, j, reply, eVect, TheNorm, ListVect, eVwork, eInfoRed, TheOption, CommSV, TheComm, opt, fStr, eNorm, md5_in, md5_out, md5_gap, ListNorm, RealV;
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Error("Matrix should be positive definite");
  fi;
  FilePreIn:=Filename(POLYHEDRAL_tmpdir, "SVvallentin.prein");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "SVvallentin.out");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "SVvallentin.Gap");
  FileErr:=Filename(POLYHEDRAL_tmpdir, "SVvallentin.err");
  RemoveFileIfExist(FilePreIn);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileGap);
  RemoveFileIfExist(FileErr);
  n:=Length(GramMat);
  #
  eInfoRed:=RemoveFractionMatrixPlusCoef(GramMat);
  eNorm:=TheDist * eInfoRed.TheMult;
  #
  output:=OutputTextFile(FilePreIn, true);;
  AppendTo(output, n, "\n");
  if eV*eV=0 then
    eVwork:=ListWithIdenticalEntries(n, 0);
    eVwork[1]:=1;
  else
    eVwork:=eV;
  fi;
  for i in [1..n]
  do
    fStr:="";
    for j in [1..i]
    do
      fStr:=Concatenation(fStr, " ", String(eInfoRed.TheMat[i][j]));
    od;
    fStr:=Concatenation(fStr, "\n");
    WriteAll(output, fStr);
  od;
  fStr:="";
  for i in [1..n]
  do
    fStr:=Concatenation(fStr, " ", String(-eVwork[i]));
  od;
  fStr:=Concatenation(fStr, "\n");
  WriteAll(output, fStr);
  fStr:=Concatenation(String(eNorm), "\n");
  WriteAll(output, fStr);
  CloseStream(output);
  #
  #
  #
  TheOption:="Use gmp_read";
  CommSV:=FileSV_exact;
  FileIn:=FilePreIn;
  if IsBound(recOption.MaxVector) then
    CommSV:=Concatenation(CommSV, " -s", String(recOption.MaxVector));
  fi;
  TheComm:=Concatenation(CommSV, " -M -l < ", FileIn, " > ", FileOut, " 2> ", FileErr);
  Exec(TheComm);
  #
  #
  #
  reply:=ReadSV_output(FileOut);
  ListVect:=[];
  if eV*eV=0 then
    ListNorm:=[];
    for eVect in reply
    do
      RealV:=eVect - eVwork;
      TheNorm:=RealV*GramMat*RealV;
      Add(ListNorm, TheNorm);
      Add(ListVect, RealV);
      if TheNorm > TheDist then
          Print("TheNorm=", TheNorm, " TheDist=", TheDist, "\n");
          Print("We have it for eVect=", eVect, "\n");
          Error("Please debug");
      fi;
    od;
    Print("Collected(ListNorm)=", Collected(ListNorm), "\n");
  else
    Print("CVP Case 2\n");
    ListNorm:=[];
    for eVect in reply
    do
      TheNorm:=(eV-eVect)*GramMat*(eV-eVect);
      Add(ListNorm, TheNorm);
      if TheNorm<=TheDist then
        Add(ListVect, eVect);
      fi;
      if TheNorm > TheDist then
        Print("TheNorm=", TheNorm, " TheDist=", TheDist, "\n");
        Error("Please debug");
      fi;
    od;
  fi;
  RemoveFileIfExist(FilePreIn);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileGap);
  RemoveFileIfExist(FileErr);
  return ListVect;
end;


DualLLLReducedGramMat:=function(GramMat)
  local eInv, res, TheRemainder, eTrans, InvRemainder, bTrans;
  eInv:=Inverse(GramMat);
  res:=LLLReducedGramMat(eInv);
  TheRemainder:=res.remainder;
  eTrans:=res.transformation;
  if TheRemainder<>eTrans*eInv*TransposedMat(eTrans) then
    Error("Logical error 1");
  fi;
  InvRemainder:=Inverse(TheRemainder);
  bTrans:=TransposedMat(Inverse(eTrans));
  if InvRemainder<>bTrans*GramMat*TransposedMat(bTrans) then
    Error("Logical error 2");
  fi;
  return rec(remainder:=InvRemainder,
             transformation:=bTrans);
end;


General_ClosestAtDistanceVallentinProgram:=function(GramMat, eV, TheDist, recOption)
  local res, TheRemainder, TheTransform, InvTrans, eVP, TheSol, TheSolRet, eVPnear, eVPdiff;
  if IsIntegralMat(GramMat)=false then
    Error("The Gram Matrix should be integral");
  fi;
#  res:=LLLReducedGramMat(GramMat);
  res:=DualLLLReducedGramMat(GramMat);
  TheRemainder:=res.remainder;
  TheTransform:=res.transformation;
  InvTrans:=Inverse(TheTransform);
  if InvTrans*TheRemainder*TransposedMat(InvTrans)<>GramMat then
    Error("Error in LLL computation");
  fi;
  eVP:=eV*InvTrans;
  eVPnear:=List(eVP, NearestInteger);
  eVPdiff:=eVP - eVPnear;
  TheSol:=Kernel_ClosestAtDistanceVallentinProgram(TheRemainder, eVPdiff, TheDist, recOption);
  if Length(TheSol) = 0 then
    return [];
  fi;
  TheSolRet:=List(TheSol, x->(x+eVPnear)*TheTransform);
  if First(TheSolRet, x->(x-eV)*GramMat*(x-eV) > TheDist)<>fail then
    Error("Short neighbor computation failed\n");
  fi;
  return TheSolRet;
end;


CloseVectors:=function(GramMat, eV, TheDist)
    local FileGram, FileV, FileOut, FileErr, choice, command, result;
    FileGram:=Filename(POLYHEDRAL_tmpdir, "LATT_near.gram");
    FileV:=Filename(POLYHEDRAL_tmpdir, "LATT_near.vect");
    FileOut:=Filename(POLYHEDRAL_tmpdir, "LATT_near.out");
    FileErr:=Filename(POLYHEDRAL_tmpdir, "LATT_near.err");
    WriteMatrixFile(FileGram, GramMat);
    WriteVectorFile(FileV, eV);
    choice:=Concatenation("near=", String(TheDist));
    command:=Concatenation(FileLATT_near, " gmp ", choice, " ", FileGram, " ", FileV, " GAP ", FileOut, " 2> ", FileErr);
    Exec(command);
    result:=ReadAsFunction(FileOut)();
    RemoveFile(FileGram);
    RemoveFile(FileV);
    RemoveFile(FileOut);
    RemoveFile(FileErr);
    return result;
end;

NearestVectors:=function(GramMat, eV)
    local FileGram, FileV, FileOut, FileErr, command, ListVect, eDiff, TheNorm;
    FileGram:=Filename(POLYHEDRAL_tmpdir, "LATT_near.gram");
    FileV:=Filename(POLYHEDRAL_tmpdir, "LATT_near.vect");
    FileOut:=Filename(POLYHEDRAL_tmpdir, "LATT_near.out");
    FileErr:=Filename(POLYHEDRAL_tmpdir, "LATT_near.err");
    WriteMatrixFile(FileGram, GramMat);
    WriteVectorFile(FileV, eV);
    command:=Concatenation(FileLATT_near, " gmp nearest ", FileGram, " ", FileV, " GAP ", FileOut, " 2> ", FileErr);
    Exec(command);
    ListVect:=ReadAsFunction(FileOut)();
    RemoveFile(FileGram);
    RemoveFile(FileV);
    RemoveFile(FileOut);
    RemoveFile(FileErr);
    eDiff:=eV - ListVect[1];
    TheNorm:=eDiff * GramMat * eDiff;
    return rec(TheNorm:=TheNorm, ListVect:=ListVect);
end;
