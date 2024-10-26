GRP:=MathieuGroup(24);

eSetSet1:=[[1..8]];
eStab1:=OnSetsSetsStabilizer(GRP, eSetSet1);
#
#O:=Orbits(eStab1, [9..24], OnPoints);
#ListSet:=List(O, x->Set(x));
#eSetSet2:=Concatenation(eSetSet1, Set(ListSet));

eSetSet2:=[[1,2,3,4,5,6,7,8],[9,11,13,17,18,19,22,23],
[10,12,14,15,16,20,21,24]];
eStab2:=OnSetsSetsStabilizer(GRP, eSetSet2);


eSetSet3:=[[1..6]];
eStab3:=OnSetsSetsStabilizer(GRP, eSetSet3);

eSetSet4:=[[1..6], [7..12]];
eStab4:=OnSetsSetsStabilizer(GRP, eSetSet4);

eSetSet5:=[[1..5]];
eStab5:=OnSetsSetsStabilizer(GRP, eSetSet5);

eSetSet6:=[[1..5], [6,7,8,11,13]];
eStab6:=OnSetsSetsStabilizer(GRP, eSetSet6);


DoTests:=function(GRP, eSetSet)
  local g, fSetSet, g2;
  g:=Random(GRP);
  fSetSet:=OnSetsSets(eSetSet, g);
  Print("g=", g, "\n");
  g2:=OnSetsSetsRepresentativeAction(GRP, eSetSet, fSetSet);
  if OnSetsSets(eSetSet, g2)<>fSetSet then
    Print("We have a bug to find out\n");
    Print(NullMat(5));
  fi;
end;
DoTestsSec:=function(GRP, eSetSet)
  local g, eStab, fSetSet, fStab, phi, eStabConj;
  g:=Random(GRP);
  Print("g=", g, "\n");
  eStab:=OnSetsSetsStabilizer(GRP, eSetSet);
  fSetSet:=OnSetsSets(eSetSet, g);
  fStab:=OnSetsSetsStabilizer(GRP, fSetSet);
  phi:=ConjugatorIsomorphism(GRP, g);
  eStabConj:=Image(phi, eStab);
  if eStabConj<>fStab then
    Print("We have a bug to find out\n");
    Print(NullMat(5));
  fi;
end;



g:=(1,11,21,12,4,5,7,9,17,22)(2,18,6,8,16,23,10,14,19,20)(3,13)(15,24);
#g:=( 1,11, 2,20, 6, 7,19, 9,14, 5,23,18)( 3, 8,10,24, 4,17,21,16,15,12,22,13);
fSetSet6:=OnSetsSets(eSetSet6, g);
g2:=OnSetsSetsRepresentativeAction(GRP, eSetSet6, fSetSet6);
fSetSet6_2:=OnSetsSets(eSetSet6, g2);
if fSetSet6<>fSetSet6_2 then
  Print("We have debugging to do\n");
  Print(NullMat(5));
fi;