TheChoice:=2;
if TheChoice=1 then
  GramMat:=LatticeDn(4).TheGram;
elif TheChoice=2 then
  GramMat:=ClassicalSporadicLattices("E6"); # that should be fast
elif TheChoice=3 then
  GramMat:=ClassicalSporadicLattices("L81"); # takes a few days
                                             # reserves 300M at least in /tmp
elif TheChoice=4 then
  GramMat:=ClassicalSporadicLattices("L99"); # takes about a week
                                             # reserves 2G at least in /tmp
fi;

n:=Length(GramMat);
SHV:=ShortestVectorDutourVersion(GramMat);
MatrGRP:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [GramMat], SHV);

LimitNbRepresentatives:=10;
TheRec:=IndepFam_GetAllSets(SHV, MatrGRP, LimitNbRepresentatives);

TheFileCases:=Concatenation("TheCases", String(n), "_", String(Length(SHV)), "_", String(Order(MatrGRP)));
Print("TheFileCases=", TheFileCases, "\n");
IndepFam_PrintResult(TheFileCases, TheRec);
