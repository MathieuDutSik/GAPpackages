ListFile:=[
"SingleSHV_10_15",
"SingleSHV_12_13",
"SingleSHV_9_6",
"SingleSHV_dim9_rank12",
"SingleSHV_11_17",
"SingleSHV_12_23",
"SingleSHV_dim11_rnk11_det12"];


ListResult:=[];
for eFile in ListFile
do
  SHV:=ReadAsFunction(eFile)();
  RecTest:=SHORT_TestRealizabilityShortestFamily(SHV);
  eResult:=rec(SHV:=SHV, test:=RecTest.reply, testCone:=RecTest.replyCone);
  Add(ListResult, eResult);
od;
