n:=3;
DoGroupHomologyComp:=true;

Imultiplication:=NullMat(2*n,2*n);
TheSuperMat:=NullMat(2*n,2*n);
for i in [1..n]
do
  Imultiplication[2*i-1][2*i]:=-1;
  Imultiplication[2*i][2*i-1]:=1;
  Imultiplication[2*i][2*i]:=1;
  #
  TheSuperMat[2*i-1][2*i-1]:=2;
  TheSuperMat[2*i-1][2*i]:=-1;
  TheSuperMat[2*i][2*i-1]:=-1;
  TheSuperMat[2*i][2*i]:=2;
od;

ListGen:=[Imultiplication];
eCasePrev:=rec(TheGroup:=Group(ListGen), SuperMat:=TheSuperMat);
TheRES:=GetEnumerationPerfectFormGspace(eCasePrev);

Print("TheTessel1\n");
TheTessel1:=TheRES.TheTesselation;
PrintOrbitwiseTesselationInformation(TheTessel1);
Print("\n\n");


Print("TheTessel2\n");
TheTessel2:=DomainSplitting(TheTessel1, [1,2]);
PrintOrbitwiseTesselationInformation(TheTessel2);
CheckTilingFaceToFace(TheTessel2);
Print("\n\n");


Print("TheTessel3\n");
TheRay1:=GetTotalInvariantRay(TheTessel2, 2);
TheTessel3:=DomainSplittingGeneralized(TheTessel2, 2, TheRay1);
PrintOrbitwiseTesselationInformation(TheTessel3);
CheckTilingFaceToFace(TheTessel3);
Print("\n\n");


if DoGroupHomologyComp=true then
  Print("Doing group homology computation\n");
  #WorkingTesselation:=TheTessel1;
  #WorkingTesselation:=TheTessel2;
  WorkingTesselation:=TheTessel3;
  kLevel:=5;
  eRecIAI:="unset";
  RecOption:=rec(DoBound:=true, DoSign:=true, DoElt:=true, 
                 DoRotationSubgroup:=true);
  TheBound:=BoundaryOperatorsFromPolyhedralTesselation(WorkingTesselation, kLevel, TheRES.FuncDoRetractionDual, eRecIAI, RecOption);
  ListFuncResolution:=GroupHomologyByCellDecomposition(TheBound);
  kCall:=kLevel+1;
  ListFuncResolution.Initialization(kCall);
  ListMatrices:=[];
  for i in [1..kCall]
  do
    eMatrix:=ListFuncResolution.GetDifferentiation(i);
    Add(ListMatrices, eMatrix);
    eFileSave:=Concatenation("DATA/PGL3_EisInt", String(i));
    SaveDataToFile(eFileSave, eMatrix);
  od;
  HomologyPGL3:=GettingHomologies(ListMatrices);
fi;
