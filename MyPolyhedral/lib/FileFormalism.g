BindGlobal("POLYHEDRAL_tmpdir", DirectoryTemporary());





ReadTextFile:=function(FileName)
    local file, list_lines, line, line_red, n_char;
    file:=InputTextFile(FileName);
    list_lines:=[];
    while(true)
    do
        line:=ReadLine(file);
        if line=fail then
            CloseStream(file);
            return list_lines;
        fi;
        n_char:=Length(line) - 1;
        line_red:=line{[1..n_char]};
        Add(list_lines, line_red);
    od;
end;



IsEmptyFile:=function(FileName)
    local file, line;
    file:=InputTextFile(FileName);
    line:=ReadLine(file);
    CloseStream(file);
    if line=fail then
        return true;
    fi;
    return false;
end;




GetBinaryFilename:=function(FileName)
    local file_name, TmpFile, file, list_lines;
    file_name:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),FileName);
    if file_name<>fail then
        return file_name;
    fi;
    TmpFile:=Filename(DirectoryTemporary(), "Test.in");
    Exec("which ", FileName, " > ", TmpFile);
    list_lines:=ReadTextFile(TmpFile);
    if Length(list_lines)=0 then
        return fail;
    fi;
    return list_lines[1];
end;




RemoveFileIfExist:=function(FileName)
    local eFile;
    if IsString(FileName) then
        if IsExistingFile(FileName) then
            RemoveFile(FileName);
        fi;
    else
        if IsList(FileName) then
            for eFile in FileName
            do
                RemoveFileIfExist(eFile);
            od;
        fi;
    fi;
end;





SaveDataToFile:=function(FileName, OBJ)
  local output;
  Exec("rm -f ", FileName,"\n");
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, "return ", OBJ, ";\n");
  CloseStream(output);
end;




GetFinalFile:=function(eFile)
  local LStr;
  LStr:=STRING_Split(eFile, "/").ListStrInter;
  return LStr[Length(LStr)];
end;


GetDirectoryFromFile:=function(eFile)
  local len, i, pos;
  len:=Length(eFile);
  pos:=-1;
  for i in [1..len]
  do
    if eFile[i]='/' then
      pos:=i;
    fi;
  od;
  if pos=-1 then
    Error("We did not find the / in the string");
  fi;
  return eFile{[1..pos]};
end;


CopyFileForAnalysis:=function(FileToSave, ePrefix)
    local iter, FileO;
    iter:=0;
    while(true)
    do
        FileO:=Concatenation(ePrefix, "save_", String(iter));
        if IsExistingFile(FileO)=false then
            Exec("cp ", FileToSave, FileO);
            break;
        fi;
        iter:=iter+1;
    od;
end;


SaveDataToFilePlusTouch:=function(FileName, OBJ)
  local FileTouch;
  FileTouch:=Concatenation(FileName, "_touch");
  RemoveFileIfExist(FileTouch);
  SaveDataToFile(FileName, OBJ);
  SaveDataToFile(FileTouch, 0);
end;

IsExistingFilePlusTouch:=function(FileName)
  local FileTouch;
  if IsExistingFile(FileName)=false then
    return false;
  fi;
  FileTouch:=Concatenation(FileName, "_touch");
  return IsExistingFile(FileTouch);
end;




ReadVector_list_lines:=function(list_lines)
    local TheMat, line, LStr, eLine, eStr, val;
    TheMat:=[];
    for line in list_lines
    do
        LStr:=SplitString(line, " ");
        eLine:=[];
        for eStr in LStr
        do
            if Length(eStr) > 0 then
                val:=Rat(eStr);
                Add(eLine, val);
            fi;
        od;
        Add(TheMat, eLine);
    od;
    return TheMat;
end;

ReadVectorFile:=function(FileName)
    local list_lines;
    list_lines:=ReadTextFile(FileName);
    return ReadVector_list_lines(list_lines);
end;





SaveStringToFile:=function(FileName, eStr)
  local output;
  Exec("rm -f ", FileName,"\n");
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, "return \"", eStr, "\";");
  CloseStream(output);
end;

SaveDataToFilePlusGzip:=function(FileName, OBJ)
  local output, FileNameGzip;
  FileNameGzip:=Concatenation(FileName, ".gz");
  Exec("rm -f ", FileName, "\n");
  Exec("rm -f ", FileNameGzip, "\n");
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, "return ", OBJ, ";\n");
  CloseStream(output);
  Exec("gzip ", FileName);
end;


RemoveFilePlusTouch:=function(FileName)
  local FileTouch;
  FileTouch:=Concatenation(FileName, "_touch");
  RemoveFile(FileName);
  RemoveFile(FileTouch);
end;




SaveDataToFilePlusTouchPlusTest:=function(FileName, OBJ, test)
  if test then
    SaveDataToFilePlusTouch(FileName, OBJ);
  fi;
end;

SaveDataToFilePlusGzipPlusTouch:=function(FileName, OBJ)
  local FileTouch;
  FileTouch:=Concatenation(FileName, "_touch");
  RemoveFileIfExist(FileTouch);
  SaveDataToFilePlusGzip(FileName, OBJ);
  SaveDataToFile(Concatenation(FileName, "_touch"), 0);
end;


SaveDataToFilePlusGzipPlusTouchPlusTest:=function(FileName, OBJ, test)
  if test then
    SaveDataToFilePlusGzipPlusTouch(FileName, OBJ);
  fi;
end;




ReadAsFunctionPlusGzip:=function(FileName)
  local FilePre, FileD, W, FileGziped;
  FileGziped:=Concatenation(FileName, ".gz");
  FileD:=Filename(POLYHEDRAL_tmpdir,"Uncompressed");
  Exec("gunzip -c ", FileName, " > ", FileD);
  W:=ReadAsFunction(FileD);
  RemoveFile(FileD);
  return W;
end;



ComputeAndSave:=function(FileName, FCT)
  local TheData;
  if IsExistingFile(FileName) then
    return ReadAsFunction(FileName)();
  else
    TheData:=FCT(1);
    SaveDataToFile(FileName, TheData);
    return TheData;
  fi;
end;






ComputeAndSaveIfTest:=function(FileName, TheTest, FCT)
  local TheData;
  if TheTest=true and IsExistingFile(FileName) then
    return ReadAsFunction(FileName)();
  else
    TheData:=FCT(1);
    if TheTest then
      SaveDataToFile(FileName, TheData);
    fi;
    return TheData;
  fi;
end;




RemoveDirectoryPlusTest:=function(FileDirectory, test)
  if test then
    Exec("rm -rf ", FileDirectory);
  fi;
end;

CreateDirectory:=function(FileDirectory)
  Exec("mkdir -p ", FileDirectory);
end;

CreateDirectoryPlusTest:=function(FileDirectory, test)
  if test then
    Exec("mkdir -p ", FileDirectory);
  fi;
end;



RemoveFileIfExistPlusTouch:=function(FileName)
  local FileTouch;
  RemoveFileIfExist(FileName);
  FileTouch:=Concatenation(FileName, "_touch");
  RemoveFileIfExist(FileTouch);
end;

RemoveFileIfExistPlusTouchPlusTest:=function(FileName, test)
  if test then
    RemoveFileIfExistPlusTouch(FileName);
  fi;
end;




IsExistingFilePlusGzipPlusTouchPlusTest:=function(FileName, test)
  local FileTouch, FileGziped;
  if test=false then
    return false;
  else
    FileTouch:=Concatenation(FileName, "_touch");
    FileGziped:=Concatenation(FileName, ".gz");
    return IsExistingFile(FileTouch) and IsExistingFile(FileGziped);
  fi;
end;



IsExistingFilePlusTouchPlusTest:=function(FileName, test)
  local FileTouch;
  if test=false then
    return false;
  else
    FileTouch:=Concatenation(FileName, "_touch");
    if IsExistingFile(FileName)=false then
      return false;
    fi;
    return IsExistingFile(FileTouch);
  fi;
end;



RecollectTest:=function(FileName, test)
  if test then
    if IsExistingFile(FileName) then
      Error("Forget to run a Recollect function");
    fi;
  fi;
end;



ReadAsFunctionPlusTouchPlusTest:=function(FileName, DefaultVal, test)
  if test=false then
    return DefaultVal;
  else
    if IsExistingFilePlusTouch(FileName)=false then
      SaveDataToFilePlusTouch(FileName, DefaultVal);
      return DefaultVal;
    fi;
    return ReadAsFunction(FileName)();
  fi;
end;



ComputeAndSave:=function(FileName, FCT)
  local TheData, FileTouch;
  FileTouch:=Concatenation(FileName, "_touch");
  if IsExistingFile(FileName) then
    return ReadAsFunction(FileName)();
  else
    TheData:=FCT(1);
    SaveDataToFilePlusTouch(FileName, TheData);
    return TheData;
  fi;
end;



ComputeAndSavePlusTouch:=function(FileName, FCT)
  local TheData;
  if IsExistingFilePlusTouch(FileName) then
    return ReadAsFunction(FileName)();
  else
    TheData:=FCT(1);
    SaveDataToFilePlusTouch(FileName, TheData);
    return TheData;
  fi;
end;



ComputeAndSavePlusTouchPlusTest:=function(FileName, FCT, test)
  if test=false then
    return FCT(1);
  else
    return ComputeAndSavePlusTouch(FileName, FCT);
  fi;
end;



SaveDataToFileRecoverablePrevState:=function(FileName, Data)
  local File1, File2, File1touch, File2touch;
  File1:=Concatenation(FileName, "_1");
  File2:=Concatenation(FileName, "_2");
  File1touch:=Concatenation(File1, "_touch");
  File2touch:=Concatenation(File2, "_touch");
  SaveDataToFile(File2, Data);
  SaveDataToFile(File2touch, 0);
  RemoveFileIfExist(File1touch);
  RemoveFileIfExist(File1);
  Exec("cp ", File2, " ", File1);
  Exec("cp ", File2touch, " ", File1touch);
end;



SaveDataToFileRecoverablePrevStatePlusTest:=function(FileName, Data, test)
  if test then
    SaveDataToFileRecoverablePrevState(FileName, Data);
  fi;
end;



ReadAsFunctionRecoverablePrevState:=function(FileName)
  local File1, File2, File1touch, File2touch;
  File1:=Concatenation(FileName, "_1");
  File2:=Concatenation(FileName, "_2");
  File1touch:=Concatenation(File1, "_touch");
  File2touch:=Concatenation(File2, "_touch");
  if IsExistingFile(File1touch) then
    return ReadAsFunction(File1)();
  fi;
  if IsExistingFile(File2touch) then
    return ReadAsFunction(File2)();
  fi;
end;



IsExistingFileRecoverablePrevState:=function(FileName)
  local File1, File2, File1touch, File2touch;
  File1:=Concatenation(FileName, "_1");
  File2:=Concatenation(FileName, "_2");
  File1touch:=Concatenation(File1, "_touch");
  File2touch:=Concatenation(File2, "_touch");
  if IsExistingFile(File2touch) then
    return true;
  fi;
  if IsExistingFile(File1touch) then
    return true;
  fi;
  return false;
end;


# TheComm can be something like
# "ssh r ls TheComputation/LEGO/DATAcase"
LSoperation:=function(TheComm)
  local FileList, TheCommFull, FileFinal, TheListFinal, TheCommand;
  FileList:=Filename(POLYHEDRAL_tmpdir, "ListFile");
  TheCommFull:=Concatenation(TheComm, " > ", FileList);
  Exec(TheCommFull);
  #
  TheListFinal:=ReadTextFile(FileList);
  RemoveFileIfExist(FileList);
  return TheListFinal;
end;

# Replace the / by _
FullFileAsString:=function(eFile)
  local LStr, eStr, i;
  LStr:=STRING_Split(eFile, "/").ListStrInter;
  eStr:=LStr[1];
  for i in [2..Length(LStr)]
  do
    eStr:=Concatenation(eStr, "_", LStr[i]);
  od;
  return eStr;
end;

SaveDebugInfo:=function(ePrefix, TheData)
    local n_index, FileSave;
    n_index:=0;
    while(true)
    do
        FileSave:=Concatenation(ePrefix, String(n_index));
	if IsExistingFile(FileSave)=false then
            SaveDataToFile(FileSave, TheData);
            return;
        fi;
        n_index:=n_index+1;
    od;
end;

