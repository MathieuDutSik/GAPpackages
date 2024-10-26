for n in [3..24]
do
  Print("n=", n, "\n");
  LNames:=ClassicalSporadicLattices(["names fixed dimension", n]);
  for eName in LNames
  do
    eG:=ClassicalSporadicLattices(eName);
    CheckLLL_cppImplementation(eG);
  od;

od;