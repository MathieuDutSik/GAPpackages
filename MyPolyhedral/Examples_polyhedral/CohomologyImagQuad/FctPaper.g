GetFundamentalInfo:=function(d)
  local res, IsCorrect, eSum, eProd, Dval, eQuot;
  res:=d mod 4;
  IsCorrect:=false;
  eSum:=0;
  eProd:=0;
  if res=0 then
    eSum:=0;
    eProd:=-d/4;
    Dval:=-eProd;
    IsCorrect:=true;
    if IsInt((Dval-1)/4)=true or IsInt(Dval/4)=true then
      IsCorrect:=false;
    fi;
  fi;
  if res=1 then
    eQuot:=(1-d)/4;
    eSum:=1;
    eProd:=eQuot;
    IsCorrect:=true;
  fi;
  return rec(eSum:=eSum, eProd:=eProd, IsCorrect:=IsCorrect);
end;


TreatSingleCase:=function(eCase)
  local DoSL, n, d, eFundInfo, eSum, eProd, RecOption, PrintHeaderGroup, eStrGRP, SavePrefix, FileHomol, outputHomol, RecFct, eCaseGen2, outputTable, FileTable;
  DoSL:=eCase.DoSL;
  n:=eCase.n;
  d:=eCase.d;
  eFundInfo:=GetFundamentalInfo(d);
  if eFundInfo.IsCorrect=false then
    Error("The input is not correct for modulo reasons");
  fi;
  eSum:=eFundInfo.eSum;
  eProd:=eFundInfo.eProd;
  if CorrectnessImaginaryQuadratic(eSum, eProd)=false then
    Error("The ring is not imaginary quadratic");
  fi;
  RecOption:=rec(DoBound:=true,
                 DoSign:=true,
                 DoMat:=true,
                 DoElt:=true,
                 DoRotationSubgroup:=true);
  if DoSL then
    eStrGRP:="SL";
  else
    eStrGRP:="GL";
  fi;
  PrintHeaderGroup:=function(output, d, n, eSum, eProd)
    AppendTo(output, "d=", d, "\n");
    AppendTo(output, "eSum=", eSum, "  eProd=", eProd, "\n");
    AppendTo(output, "ring Z[alpha] with\n");
    AppendTo(output, "alpha^2");
    if eSum<>0 then
      if eSum=1 then
        AppendTo(output, " - alpha");
      elif eSum=-1 then
        AppendTo(output, " + alpha");
      elif eSum > 0 then
        AppendTo(output, " - ", eSum, "alpha");
      elif eSum < 0 then
        AppendTo(output, " + ", -eSum, "alpha");
      fi;
    fi;
    if eProd < 0 then
      AppendTo(output, " - ", -eProd);
    else
      AppendTo(output, " + ", eProd);
    fi;
    AppendTo(output, "=0\n");
    AppendTo(output, "Arithmetic group G=", eStrGRP, String(n), "(Z[alpha])\n");
  end;
  Exec("mkdir -p Result");
  SavePrefix:=Concatenation("Result/HomologyImagQuad", eStrGRP, String(n), "_", String(d), "_");
  Print("d=", d, " eSum=", eSum, " eProd=", eProd, "\n");
  eCaseGen2:=GetSpaceImaginaryQuadratic(n, eSum, eProd);
  if DoSL then
    eCaseGen2.TheFilter:=eCaseGen2.IsInSL;
  else
    eCaseGen2.TheFilter:=eCaseGen2.TrivialFilter;
  fi;
  RecFct:=DoAllComputations_Perf_Complex_Matrix_SNF(eCaseGen2, SavePrefix);
  #
  FileHomol:=Concatenation(SavePrefix, "homol");
  RemoveFileIfExist(FileHomol);
  outputHomol:=OutputTextFile(FileHomol, true);
  AppendTo(outputHomol, "n=", n, "\n");
  AppendTo(outputHomol, "\n\n\n");
  PrintHeaderGroup(outputHomol, d, n, eSum, eProd);
  RecFct.PrintResult(outputHomol);
  AppendTo(outputHomol, "\n");
  CloseStream(outputHomol);
  #
  FileTable:=Concatenation(SavePrefix, "table_pre.tex");
  RemoveFileIfExist(FileTable);
  outputTable:=OutputTextFile(FileTable, true);
  RecFct.PrintLatexResult(outputTable);
  CloseStream(outputTable);
  LATEX_Compilation(FileTable);
  #
end;
