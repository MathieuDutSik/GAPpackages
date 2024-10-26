TheChoice:=4;
if TheChoice=1 then
  g:=5;
  k:=3;
elif TheChoice=2 then
  g:=3;
  k:=1;
elif TheChoice=3 then
  g:=20;
  k:=10;
elif TheChoice=4 then
  g:=5;
  k:=5;
else
  Print("Please put here what you have in mind\n");
  Print(NullMat(5));
fi;

TheLagrangian:=[];
for i in [1..k]
do
  eVect:=ListWithIdenticalEntries(2*g, 0);
  eVect[i]:=1;
  Add(TheLagrangian, eVect);
od;


nbIter:=1000;
for iter in [1..nbIter]
do
  Print("iter=", iter, "/", nbIter, "\n");
  eMat:=SYMPL_RandomElement(g);
  TheLagrangianImg:=Set(TheLagrangian*eMat);
  RedMat:=SYMPL_LagrangianReductionMatrix(TheLagrangianImg);
  TheLagrangianRed:=Set(TheLagrangianImg*RedMat);
  if TheLagrangianRed<>Set(TheLagrangian) then
    Print("Error in reduction algorithm\n");
    Print(NullMat(5));
  fi;
od;
