FuncCreateMagicHypercube:=function(n, pDim)
  local LES, LESres, ListEqua, iDim, SLR, eRes, TheEqua, ListM, iSet, fSet, VCE, eLine, TheIneq, eIneq, ListGen, eGen, NewListEqua, Pos, ListN, eSet, ListIneq, eV;
  LES:=BuildSet(pDim, [1..n]);
  LESres:=BuildSet(pDim-1, [1..n]);
  ListEqua:=[];
  for iDim in [1..pDim]
  do
    SLR:=Difference([1..pDim], [iDim]);
    for eRes in LESres
    do
      TheEqua:=ListWithIdenticalEntries(Length(LES)+1, 0);
      TheEqua[1]:=1;
      ListM:=[];
      for iSet in [1..Length(LES)]
      do
        fSet:=LES[iSet];
        if fSet{SLR}=eRes then
          Add(ListM, iSet);
          TheEqua[iSet+1]:=-1;
        fi;
      od;
      Add(ListEqua, TheEqua);
    od;
  od;
  ListGen:=[];
  for eGen in GeneratorsOfGroup(SymmetricGroup([1..n]))
  do
    ListN:=[];
    for iSet in [1..Length(LES)]
    do
      eSet:=LES[iSet];
      fSet:=[OnPoints(eSet[1], eGen)];
      Append(fSet, eSet{[2..pDim]});
      Pos:=Position(LES, fSet);
      Add(ListN, Pos);
    od;
    Add(ListGen, PermList(ListN));
  od;
  for eGen in GeneratorsOfGroup(SymmetricGroup([1..pDim]))
  do
    ListN:=[];
    for iSet in [1..Length(LES)]
    do
      eSet:=LES[iSet];
      fSet:=Permuted(eSet, eGen);
      Pos:=Position(LES, fSet);
      Add(ListN, Pos);
    od;
    Add(ListGen, PermList(ListN));
  od;
  ListIneq:=[];
  for iSet in [1..Length(LES)]
  do
    TheIneq:=ListWithIdenticalEntries(Length(LES)+1, 0);
    TheIneq[iSet+1]:=1;
    Add(ListIneq, TheIneq);
  od;
  VCE:=NullspaceMat(TransposedMat(ListEqua));
  NewListEqua:=[];
  for eIneq in ListIneq
  do
    eLine:=[];
    for eV in VCE
    do
      Add(eLine, eIneq*eV);
    od;
    Add(NewListEqua, eLine);
  od;
  return rec(ListIneq:=NewListEqua, GRP:=Group(ListGen));
end;


# Cases [n,2] have only one orbit apparently.

ListCases:=[[3,3],[4,3],[3,4],[3,5],[4,2],[5,2],[6,2],[7,2]];
for eCase in ListCases
do
  n:=eCase[1];
  pDim:=eCase[2];
  eRec:=FuncCreateMagicHypercube(n, pDim);
  nbIneq:=Length(eRec.ListIneq);
  RelDim:=RankMat(eRec.ListIneq);
  OrdGRP:=Order(eRec.GRP);
  Print("n=", n, " p=", pDim, " dim=", RelDim, " |FAC|=", nbIneq, " |GRP|=", OrdGRP, "\n");
od;

ListCases:=[[4,3]];
for eCase in ListCases
do
  n:=eCase[1];
  pDim:=eCase[2];
  ePre:=Concatenation("Magic", String(n), "_", String(pDim));
  eFileEXT:=Concatenation(ePre, ".ext");
  eFileGRP:=Concatenation(ePre, ".grp");
  eRec:=FuncCreateMagicHypercube(n, pDim);
  SYMPOL_PrintMatrix(eFileEXT, eRec.ListIneq);
  SYMPOL_PrintGroup(eFileGRP, Length(eRec.ListIneq), eRec.GRP);
od;
