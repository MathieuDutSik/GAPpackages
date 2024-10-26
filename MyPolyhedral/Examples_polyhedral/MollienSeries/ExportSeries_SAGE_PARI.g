ListCases:=[
rec(name:="K4", ListVect:=[
[1,0,0],
[0,1,0],
[0,0,1],
[1,-1,0],
[1,0,-1],
[0,1,-1]],
TheSum:="(1+t^3 +t^4+t^5+t^6+t^9)/((1-t)*(1-t^2)^2*(1-t^3)^2*(1-t^4))"),
rec(name:="C222", ListVect:=[
[1,0,0,0],
[0,1,0,0],
[0,0,1,0],
[1,0,0,-1],
[0,1,0,-1],
[0,0,1,-1]],
TheSum:="(1+t^4+t^5-t^7-t^8-t^12)/((1-t)*(1-t^2)^2*(1-t^3)^2*(1-t^4)*(1-t^6))"),
rec(name:="C2221", ListVect:=[
[1,0,0,0],
[0,1,0,0],
[0,0,1,0],
[0,0,0,1],
[1,0,0,-1],
[0,1,0,-1],
[0,0,1,-1]],
TheSum:="(1+t^4+t^5-t^7-t^8-t^12)/((1-t)^2*(1-t^2)^2*(1-t^3)^2*(1-t^4)*(1-t^6))"),
rec(name:="C321", ListVect:=[
[1,0,0,0],
[0,1,0,0],
[0,0,0,1],
[1,0,0,-1],
[0,1,0,-1],
[0,0,1,-1]],
TheSum:="1/((1-t)^3*(1-t^2)^2*(1-t^3))"),
rec(name:="K5-3", ListVect:=[
[1,0,0,0],
[0,1,0,0],
[0,0,1,0],
[1,0,-1,0],
[1,0,0,-1],
[0,1,-1,0],
[0,1,0,-1]],
TheSum:="(1-t+2*t^2)/((1-t)^4 * (1-t^2)^2 * (1-t^4))"),
rec(name:="K5-2-1", ListVect:=[
[1,0,0,0],
[0,1,0,0],
[0,0,0,1],
[1,-1,0,0],
[1,0,0,-1],
[0,1,-1,0],
[0,0,1,-1]],
TheSum:="(1-t+2*t^2)/((1-t)^4 * (1-t^2)^2 * (1-t^4))"),
rec(name:="C421", ListVect:=[
[1,0,0,0,0],
[0,1,0,0,0],
[0,0,1,0,0],
[1,0,0,0,-1],
[0,1,-1,0,0],
[0,0,1,-1,0],
[0,0,0,1,-1]],
TheSum:="1/((1-t)^3 * (1-t^2)^2 * (1-t^3) * (1-t^4))"),
rec(name:="C331", ListVect:=[
[1,0,0,0,0],
[0,1,0,0,0],
[0,0,0,1,0],
[1,0,0,0,-1],
[0,1,-1,0,0],
[0,0,1,-1,0],
[0,0,0,1,-1]],
TheSum:="(1-t+t^2+t^4)/((1-t)^3 * (1-t^2) * (1-t^3) * (1-t^4) * (1-t^6))"),
rec(name:="K4-1", ListVect:=[
[1,0,0],
[0,1,0],
[0,0,1],
[1,0,-1],
[0,1,-1]],
TheSum:="(1-t+t^2)/((1-t)^3 * (1-t^2) * (1-t^4))")];


#ChoiceProg:="sage";
ChoiceProg:="pari";



for eCase in ListCases
do
  InputFile:=Concatenation("specificsum_", eCase.name, ".", ChoiceProg);
  RemoveFileIfExist(InputFile);
  eSHV:=eCase.ListVect;
  RecGRPcone:=SHORT_GetStabilizerCone(eSHV);
  #
  output:=OutputTextFile(InputFile, true);
  if ChoiceProg = "sage" then
    AppendTo(output, "t = var('t')\n");
    SHORT_SAGE_PrintPsigmaSum(output, eSHV, RecGRPcone);
  fi;
  if ChoiceProg = "pari" then
    SHORT_PARI_PrintPsigmaSum(output, eSHV, RecGRPcone);
  fi;
  AppendTo(output, "TheSum = ", eCase.TheSum, "\n");
  AppendTo(output, "control = PsigmaSum - TheSum\n");
  CloseStream(output);
od;

