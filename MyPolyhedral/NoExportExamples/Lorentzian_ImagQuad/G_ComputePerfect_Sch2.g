Exec("mkdir -p DATAlor");
DoWork:=function(d)
  local FileSave, RecPerf;
  FileSave:=Concatenation("DATAlor/Perf_Sch2_", String(d));
  if IsExistingFilePlusTouch(FileSave)=false then
    RecPerf:=GetAll_Sch2(d);
    SaveDataToFilePlusTouch(FileSave, RecPerf);
  fi;
end;


for d in [2..500]
do
  DoWork(d);
od;

