TheChoice:=1;
if TheChoice=1 then
  GramMat:=LatticeDn(4).TheGram;
  TheDim:=2;
  TheDet:=4;
elif TheChoice=2 then
  GramMat:=ClassicalSporadicLattices("E6");
  TheDim:=2;
  TheDet:=3;
elif TheChoice=3 then
  GramMat:=ClassicalSporadicLattices("L81");
  TheDim:=2;
  TheDet:=4;
elif TheChoice=4 then
  Print("Please put what you have in mind\n");
  Print(NullMat(5));
fi;



ProcEnum:=ProcEnum_SublatticeEnumeration();
ListLatt:=ProcEnum.EnumerateSublattices(GramMat, TheDim, TheDet);

