TheChoice:=3;

if TheChoice=1 then
  GramMat:=ClassicalSporadicLattices("E8");
  FileSave:="DATA/SubLattE8";
elif TheChoice=2 then
  GramMat:=ClassicalSporadicLattices("BW16");
  FileSave:="DATA/SubLattBW16";
elif TheChoice=3 then
  GramMat:=LatticeDn(20).TheGram;
  FileSave:="DATA/SubLattD20";
elif TheChoice=4 then
  GramMat:=LatticeDn(21).TheGram;
  FileSave:="DATA/SubLattD21";
else
  Print("Please put what you have in mind here\n");
  Print(NullMat(5));
fi;

GRP:=ArithmeticAutomorphismGroup([GramMat]);
Print("We have the group\n");
TheMod:=3;
ListOrb:=GetSublattices(GramMat, GRP, TheMod);
SaveDataToFile(FileSave, ListOrb);
