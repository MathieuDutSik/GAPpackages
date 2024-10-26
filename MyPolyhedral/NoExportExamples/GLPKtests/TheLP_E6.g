EXT:=ClassicalExtremeDelaunayPolytopes("G6");

n:=Length(EXT[1]) - 1;
FAC:=DualDescription(EXT);

FACsing:=[];
for eFAC in FAC
do
  pos:=First([1..n+1], x->eFAC[x]<>0);
  eVal:=AbsInt(eFAC[pos]);
  eFACsing:=eFAC / eVal;
  Add(FACsing, eFACsing);
od;

ToBeMinimized:=[0];
for i in [1..n]
do
  Add(ToBeMinimized, Random([-4..4]) );
od;

ListVal:=[];
for eEXT in EXT
do
  eVal:=eEXT*ToBeMinimized;
  Add(ListVal, eVal);
od;
eMin:=Minimum(ListVal);
SizMin:=Length(Filtered(ListVal, x->x=eMin));
Print("SizMin=", SizMin, "\n");
pos:=Position(ListVal, eMin);

VertMin:=EXT[pos];
Print("VertMin=", VertMin, "\n");
ListIdx:=Filtered([1..Length(FACsing)], x->FACsing[x]*VertMin=0);
Print("|ListIdx|=", Length(ListIdx), "\n");
Print("ListIdx=", ListIdx, "\n");


TheLP1:=rec(ListIneq:=FACsing, ToBeMinimized:=ToBeMinimized);




TheLP:=TheLP1;

StrType:="rational";
TheReply:=GLPK_LinearProgramming_General(TheLP.ListIneq, TheLP.ToBeMinimized, StrType);
