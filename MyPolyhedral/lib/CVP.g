FileLATT_near:=GetBinaryFilename("LATT_near");


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
