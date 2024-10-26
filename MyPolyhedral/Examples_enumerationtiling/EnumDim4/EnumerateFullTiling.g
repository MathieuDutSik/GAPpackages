n:=4;

#eFile:=Concatenation("OrbitSimplices_", String(n));
#TheResult:=ReadAsFunction(eFile)();

MaxVal:=1;
TheResult:=TRIG_EnumeratePossiblePairsSimplicesVolumeOne(n, MaxVal);

ListOrbit:=TRIG_EnumerationFixedDimension(TheResult);

ListListTrig:=[];
for eOrbit in ListOrbit
do
  ListTrig:=List(eOrbit, x->x.EXT);
  Add(ListListTrig, ListTrig);
od;

eFile:=Concatenation("DATA/ListTriangulation_dim", String(n));
SaveDataToFile(eFile, ListListTrig);

ListRecPeriodicTriang:=List(ListListTrig, TRIG_GetAdjacencyInformationOfTriangulation);
