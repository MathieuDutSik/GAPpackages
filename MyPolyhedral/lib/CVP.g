FileSV_exact:=GetBinaryFilename("sv_exact");


CVPdimension1_Integral:=function(GramMat, eV)
  local x, a, b, r, x1, x2, eNorm1, eNorm2, TheNorm, ListVect, alpha;
  x:=eV[1];
  a:=DenominatorRat(x);
  b:=NumeratorRat(x);
  r:=b mod a;
  x1:=(b-r)/a;
  x2:=(b-r+a)/a;
  alpha:=GramMat[1][1];
  eNorm1:=(x1-x)*alpha*(x1-x);
  eNorm2:=(x2-x)*alpha*(x2-x);
  TheNorm:=Minimum([eNorm1, eNorm2]);
  ListVect:=[];
  if TheNorm=eNorm1 then
    Add(ListVect, [x1]);
  fi;
  if TheNorm=eNorm2 then
    Add(ListVect, [x2]);
  fi;
  return rec(ListVect:=ListVect, TheNorm:=TheNorm);
end;

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




Kernel_CVPVallentinProgramIntegral:=function(GramMat, eV, recOption)
  local eFileIn, FilePreIn, FileOut, FileGap, FileErr, test, n, output, i, j, reply, iVect, eNorm, TheNorm, ListVect, TheReply, eReply, eVint, eVdiff, TheOption, CommSV, TheComm, TheReturn, opt, eStr, fStr;
  FilePreIn:=Filename(POLYHEDRAL_tmpdir, "SVvallentin.prein");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "SVvallentin.out");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "SVvallentin.Gap");
  FileErr:=Filename(POLYHEDRAL_tmpdir, "SVvallentin.err");
  RemoveFileIfExist(FilePreIn);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileGap);
  n:=Length(GramMat);
  output:=OutputTextFile(FilePreIn, true);;
  AppendTo(output, n , "\n");
  for i in [1..n]
  do
    fStr:="";
    for j in [1..i]
    do
      fStr:=Concatenation(fStr, " ", String(GramMat[i][j]));
    od;
    fStr:=Concatenation(fStr, "\n");
    WriteAll(output, fStr);
  od;
  fStr:="";
  for i in [1..n]
  do
    fStr:=Concatenation(fStr, " ", String(-eV[i]));
  od;
  fStr:=Concatenation(fStr, "\n");
  WriteAll(output, fStr);
  CloseStream(output);
  eFileIn:=FilePreIn;
  CommSV:=FileSV_exact;
  if IsBound(recOption.MaxVector) then
    CommSV:=Concatenation(CommSV, " -s", String(recOption.MaxVector));
  fi;
  TheComm:=Concatenation(CommSV, " -M -c < ", eFileIn, " > ", FileOut, " 2> ", FileErr);
  Exec(TheComm);
  reply:=ReadSV_output(FileOut);
  for iVect in [1..Length(reply)]
  do
    eReply:=reply[iVect];
    eNorm:=(eV-eReply)*GramMat*(eV-eReply);
    if iVect=1 then
      ListVect:=[eReply];
      TheNorm:=eNorm;
    else
      if TheNorm=eNorm then
        Add(ListVect, eReply);
      else
        if eNorm<TheNorm then
          ListVect:=[eReply];
          TheNorm:=eNorm;
        fi;
      fi;
    fi;
  od;
  TheReturn:=rec(ListVect:=ListVect, TheNorm:=TheNorm);
  RemoveFileIfExist(FilePreIn);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileGap);
  RemoveFileIfExist(FileErr);
  return TheReturn;
end;




General_CVPVallentinProgram_Rational:=function(GramMatIn, eV, recOption)
  local INF, GramMat, n, res, TheRemainder, TheTransform, InvTrans, eVP, eVPnear, eVPdiff, TheRecSol, ListVectRet, TheNorm;
  INF:=RemoveFractionMatrixPlusCoef(GramMatIn);
  GramMat:=INF.TheMat;
  if IsIntegralMat(GramMat)=false then
    Error("The input matrix should be integral");
  fi;
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Error("Matrix should be positive definite");
  fi;
  if Length(GramMat)<>Length(eV) then
    Error("Dimension error in the CVP program");
  fi;
  if First(eV, x->IsRat(x)=false)<>fail then
    Error("Calling with nonrational eV");
  fi;
  n:=Length(GramMat);
  if IsIntegralVector(eV) then
    return rec(ListVect:=[eV], TheNorm:=0);
  fi;
  if n=1 then
    return CVPdimension1_Integral(GramMatIn, eV);
  fi;
  res:=LLLReducedGramMat(GramMat);
  TheRemainder:=res.remainder;
  TheTransform:=res.transformation;
  InvTrans:=Inverse(TheTransform);
  if InvTrans*TheRemainder*TransposedMat(InvTrans)<>GramMat then
    Error("Error in LLL computation");
  fi;
  eVP:=eV*InvTrans;
  eVPnear:=List(eVP, NearestInteger);
  eVPdiff:=eVP - eVPnear;
  TheRecSol:=Kernel_CVPVallentinProgramIntegral(TheRemainder, eVPdiff, recOption);
  ListVectRet:=List(TheRecSol.ListVect, x->(x+eVPnear)*TheTransform);
  TheNorm:=TheRecSol.TheNorm;
  if First(ListVectRet, x->(x-eV)*GramMat*(x-eV) <> TheNorm)<>fail then
    Error("Closest neighbor computation failed\n");
  fi;
  return rec(ListVect:=ListVectRet, TheNorm:=TheNorm/INF.TheMult);
end;

CVPVallentinProgram_Rational:=function(GramMatIn, eV)
  local recOption;
  recOption:=rec();
  return General_CVPVallentinProgram_Rational(GramMatIn, eV, recOption);
end;




CVPVallentinProgram:=function(GramMat, eV)
  local Nval;
  if IsMatrixRational(GramMat) and IsVectorRational(eV) then
    return CVPVallentinProgram_Rational(GramMat, eV);
  fi;
  Error("You have to build your own arithmetic");
end;




# This function should return the solutions of the equation
# (x - eV) G (x - eV) <= TheDist.
#
Kernel_ClosestAtDistanceVallentinProgram:=function(GramMat, eV, TheDist, recOption)
  local FileIn, FilePreIn, FileOut, FileGap, FileErr, test, n, output, i, j, reply, eVect, TheNorm, ListVect, eVwork, eInfoRed, TheOption, CommSV, TheComm, opt, fStr, eNorm, md5_in, md5_out, md5_gap, ListNorm, RealV;
#  Print("------------------------------------------------------------\n");
#  SaveDebugInfo("Kernel_ClosestAtDistanceVallentinProgram", rec(GramMat:=GramMat, eV:=eV, TheDist:=TheDist));
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
  Print("eVwork=", eVwork, "\n");
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
  Print("TheComm=", TheComm, "\n");
  Exec(TheComm);
  #
  #
  #
  reply:=ReadSV_output(FileOut);
  Print("|reply|=", Length(reply), "\n");
  ListVect:=[];
  if eV*eV=0 then
    Print("CVP Case 1 eVwork=", eVwork, " TheDist=", TheDist, "\n");
    Print("Iso(reply)=", Isobarycenter(reply), "\n");
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
    Print("Collected(ListNorm)=", Collected(ListNorm), "\n");
  fi;
  Print("|ListVect|=", Length(ListVect), "\n");
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
#  Print("TheRemainder=\n");
#  PrintArray(TheRemainder);
  if InvTrans*TheRemainder*TransposedMat(InvTrans)<>GramMat then
    Error("Error in LLL computation");
  fi;
  eVP:=eV*InvTrans;
  eVPnear:=List(eVP, NearestInteger);
  eVPdiff:=eVP - eVPnear;
#  Print("TheRemainder=\n");
#  PrintArray(TheRemainder);
#  Print("eVPdiff=", eVPdiff, "\n");
  TheSol:=Kernel_ClosestAtDistanceVallentinProgram(TheRemainder, eVPdiff, TheDist, recOption);
  if Length(TheSol)=0 then
    return [];
  fi;
#  Print("TheTransform=\n");
#  PrintArray(TheTransform);
  TheSolRet:=List(TheSol, x->(x+eVPnear)*TheTransform);
  if First(TheSolRet, x->(x-eV)*GramMat*(x-eV) > TheDist)<>fail then
    Error("Short neighbor computation failed\n");
  fi;
  return TheSolRet;
end;


ClosestAtDistanceVallentinProgram:=function(GramMat, eV, TheDist)
  local recOption;
  recOption:=rec();
  return General_ClosestAtDistanceVallentinProgram(GramMat, eV, TheDist, recOption);
end;


