n:=3;
DoGroupHomologyComp:=true;
Imultiplication:=NullMat(2*n,2*n);
for i in [1..n]
do
  Imultiplication[2*i][2*i-1]:=1;
  Imultiplication[2*i-1][2*i]:=-1;
od;

ListGen:=[Imultiplication];
eCasePrev:=rec(TheGroup:=Group(ListGen), SuperMat:=IdentityMat(2*n));
TheINFO:=GetEnumerationPerfectFormGspace(eCasePrev);

Print("TheTessel1\n");
TheTessel1:=TheINFO.TheTesselation;
PrintOrbitwiseTesselationInformation(TheTessel1);
Print("\n\n");


Print("TheTessel2\n");
TheTessel2:=DomainSplitting(TheTessel1, [1]);
PrintOrbitwiseTesselationInformation(TheTessel2);
CheckTilingFaceToFace(TheTessel2);
Print("\n\n");


if DoGroupHomologyComp=true then
  #WorkingTesselation:=TheTessel1;
  WorkingTesselation:=TheTessel2;
  kLevel:=5;
  eRecIAI:="unset";
  RecOption:=rec(DoBound:=true, DoSign:=true, DoElt:=true, 
                 DoRotationSubgroup:=true);
  TheBound:=BoundaryOperatorsFromPolyhedralTesselation(WorkingTesselation, kLevel, TheINFO.FuncDoRetraction);
  ListFuncResolution:=GroupHomologyByCellDecomposition(TheBound);
  kCall:=kLevel+1;
  ListFuncResolution.Initialization(kCall);
  ListMatrices:=[];
  for i in [1..kCall]
  do
    Add(ListMatrices, ListFuncResolution.GetDifferentiation(i));
  od;
  HomologyPGL3:=GettingHomologies(ListMatrices);
fi;
