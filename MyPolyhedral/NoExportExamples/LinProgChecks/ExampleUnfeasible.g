a:=2;

ListIneq:=[
[-1,1,0,0],
[-1,0,1,0],
[-1,0,0,1],
[a,-1,-1,-1]];

ToBeMinimized:=[1,3,4,5];
n:=Length(ToBeMinimized);

TheResult:=LinearProgramming_Rational(ListIneq, ToBeMinimized);


if IsBound(TheResult.dual_solution) then
  eSum:=ListWithIdenticalEntries(n,0);
  for eEnt in TheResult.dual_solution
  do
    eSum:=eSum+ListIneq[eEnt[1]]*eEnt[2];
  od;
  Print("eSum=", eSum, "\n");
  eSum:=eSum+ToBeMinimized;
  Print("eSumP=", eSum, "\n");
  Print("optimal_value=", TheResult.optimal, "\n");
fi;

if IsBound(TheResult.dual_direction) then
  eSum:=ListWithIdenticalEntries(n,0);
  for eEnt in TheResult.dual_direction
  do
    eSum:=eSum+ListIneq[eEnt[1]]*AbsInt(eEnt[2]);
  od;
  Print("eSum=", eSum, "\n");
fi;
