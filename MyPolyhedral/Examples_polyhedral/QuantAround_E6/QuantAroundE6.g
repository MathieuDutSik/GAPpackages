TheFile:="RESULT_QuantAround_E6";
RemoveFileIfExist(TheFile);
output:=OutputTextFile(TheFile, true);

eGram:=ClassicalSporadicLattices("E6");
n:=Length(eGram);

AppendTo(output, "E6 Gram matrix:\n");
for eLine in eGram
do
  AppendTo(output, POL_VectorString(eLine), "\n");
od;

Gmatr:=ArithmeticAutomorphismGroup([eGram]);
ListMatGen:=GeneratorsOfGroup(Gmatr);
AppendTo(output, "|Gmatr| = ", Order(Gmatr), "\n");

SHV:=ShortestVectorDutourVersion(eGram);
nSHV:=Length(SHV);
AppendTo(output, "|SHV| = ", nSHV, "\n");

ListPermGen:=[];
for eGen in ListMatGen
do
  ePerm:=PermList(List(SHV, v -> Position(SHV, v * eGen)));
  Add(ListPermGen, ePerm);
od;
Gperm:=Group(ListPermGen);
AppendTo(output, "|Gperm| = ", Order(Gperm), "\n");

PairIdx:=ListWithIdenticalEntries(nSHV, 0);
ListPairRep:=[];
for i in [1..nSHV]
do
  if PairIdx[i] = 0 then
    Add(ListPairRep, i);
    PairIdx[i]:=Length(ListPairRep);
    PairIdx[Position(SHV, -SHV[i])]:=Length(ListPairRep);
  fi;
od;
nPair:=Length(ListPairRep);

ListPermGenAntipod:=[];
for eGen in ListMatGen
do
  ePerm:=PermList(List(ListPairRep, p -> PairIdx[Position(SHV, SHV[p] * eGen)]));
  Add(ListPermGenAntipod, ePerm);
od;
Gperm_antipod:=Group(ListPermGenAntipod);
AppendTo(output, "|Gperm_antipod| = ", Order(Gperm_antipod), "\n");

phi:=GroupHomomorphismByImagesNC(Gperm, Gperm_antipod, ListPermGen, ListPermGenAntipod);
phi_matr:=GroupHomomorphismByImagesNC(Gperm, Gmatr, ListPermGen, ListMatGen);

CJ:=ConjugacyClassesSubgroups(Gperm_antipod);
AppendTo(output, "|CJ| = ", Length(CJ), "\n");

for iClass in [1..Length(CJ)]
do
  H_antipod:=Representative(CJ[iClass]);
  H_perm:=PreImage(phi, H_antipod);
  ListGen:=List(GeneratorsOfGroup(H_perm), x -> Image(phi_matr, x));
  TheOrd:=Order(H_perm);
  if TheOrd > 200 then
    SPA:=InvariantFormDutourVersion(ListGen);
    if Length(SPA) > 1 then
    AppendTo(output, "\n=== Class ", iClass, " |H_matr| = ", TheOrd, " dim SPA = ", Length(SPA), " ===\n");
    repeat
      S:=Sum(SPA, x -> Random([-3..3]) * x);
    until RankMat([Flat(S), Flat(eGram)]) > 1;
    AppendTo(output, "S:\n");
    for eLine in S
    do
      AppendTo(output, POL_VectorString(eLine), "\n");
    od;
    k0:=1;
    while IsPositiveDefiniteSymmetricMatrix(k0 * eGram + S) = false
    do
      k0:=k0 + 1;
    od;
    AppendTo(output, "k0 = ", k0, "\n");
    for k in [k0..k0+10]
    do
      eQuad:=k * eGram + S;
      ListFunc:=DelaunayComputationStandardFunctions(eQuad);
      Q:=ListFunc.GetQuantization();
      Qcs:=ListFunc.GetQuantization_ConwaySloane();
      AppendTo(output, "k = ", k, " Q = ", Q, " Qcs = ", Qcs, "\n");
    od;
    fi;
  fi;
od;

CloseStream(output);
