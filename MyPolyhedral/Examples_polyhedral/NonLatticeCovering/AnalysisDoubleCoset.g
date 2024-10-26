n:=5;
ListCosetsRed:=[];
H:=ListWithIdenticalEntries(n,0);
Add(ListCosetsRed, ShallowCopy(H));

H[1]:=1/3;
Add(ListCosetsRed, ShallowCopy(H));

ListCosets:=List(ListCosetsRed, x->Concatenation([1], x));


ListMat:=[];
for i in [1..n]
do
  TheMat:=NullMat(n,n);
  TheMat[i][i]:=1;
  Add(ListMat, TheMat);
od;
for i in [1..n-1]
do
  for j in [i+1..n]
  do
    TheMat:=NullMat(n,n);
    TheMat[i][j]:=1;
    TheMat[j][i]:=1;
    Add(ListMat, TheMat);
  od;
od;
eCase:=rec(SuperMat:=IdentityMat(n),
           Basis:=ListMat,
           TheGroup:=Group([-IdentityMat(n)]), 
           IsBravaisSpace:=true, 
           ListCosets:=ListCosets);
LFC:=Periodic_EnumerationProcedureLtype(eCase);

ThePrefix:="./ListCOOP/";
Exec("mkdir -p ", ThePrefix);

Periodic_CheckCoherencyDelaunayDecomposition:=function(DelCO, GramMat)
  local n, eDelaunay, EXT, CP, Vcent, reply, ListEXT;
  n:=Length(GramMat);
  for eDelaunay in DelCO
  do
    EXT:=eDelaunay.EXT;
    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
    Vcent:=CP.Center{[2..n+1]};
    reply:=Periodic_ClosestVector(GramMat, ListCosetsRed, Vcent);
    if reply.TheNorm>CP.SquareRadius then
      Print("This code defies all expectation of errors,\n");
      Print("it is simply wonderfully wrong !! \n");
      Print(NullMat(5));
    fi;
    if reply.TheNorm<CP.SquareRadius then
      Print("We find a closest vector than the one supposed to be,\n");
      Print("i.e., a point inside of the empty sphere\n");
      Print(NullMat(5));
    fi;
    ListEXT:=List(reply.ListVect, x->Concatenation([1], x));
    if Set(ListEXT)<>Set(EXT) then
      Print("We find some more point on the empty sphere,\n");
      Print("this is not allowed\n");
      Print(NullMat(5));
    fi;
  od;
end;



MyOutputOfLtype:=function(FileName, OneLtype, eCase)
  local n, DimSpace, FAC1, EXT2, FAC2, FAC1red, EXT2red, TheSum, eExt, GramMat, output, nbDelaunay, iDelaunay, eDelaunay;
  n:=Length(eCase.Basis[1]);
  DimSpace:=Length(eCase.Basis);
#  Print("n=", n, " DimSpace=", DimSpace, "\n");
  FAC1:=WriteFaceInequalities(OneLtype, eCase);
  FAC2:=EliminationByRedundancyDualDescription(FAC1.ListInequalities);
  FAC1red:=List(FAC1.ListInequalities, x->x{[2..DimSpace+1]});
  EXT2red:=DualDescription(FAC1red);
  EXT2:=List(EXT2red, x->Concatenation([0],x));
  TheSum:=[];
  for eExt in EXT2
  do
    TheSum:=TheSum+eExt;
  od;
  GramMat:=FuncComputeMat(eCase.Basis, TheSum);
  #
  output:=OutputTextFile(FileName, true);
  AppendTo(output, n, "\n\n");
  #
  nbDelaunay:=Length(OneLtype);
  AppendTo(output, "Number of Delaunay polytopes=", nbDelaunay, "\n");
  for iDelaunay in [1..nbDelaunay]
  do
    eDelaunay:=OneLtype[iDelaunay];
    AppendTo(output, "Delaunay number ", iDelaunay, "\n");
    WriteMatrix(output, eDelaunay.EXT);
  od;
  #
  AppendTo(output, "Gram Matrix=\n");
  WriteMatrix(output, GramMat);
  #
  CloseStream(output);
end;




nbLtypes:=LFC.LtypeDatabase.FuncGetNumberLtype();
for iLtype in [1..nbLtypes]
do
  Print("iLtype=", iLtype, " / ", nbLtypes, "\n");
  eLtype:=LFC.LtypeDatabase.FuncGetLtype(iLtype);
  FileName:=Concatenation(ThePrefix, "Input", String(iLtype));
  TheGramMat:=LFC.LtypeDatabase.FuncGetDiscInfo(iLtype).GramMat;
  RemoveFileIfExist(FileName);
  OutputToCOOP_PACOOP(FileName, eLtype, eCase, 100, "1e-5", "coop", 1);
  Periodic_CheckCoherencyDelaunayDecomposition(eLtype, TheGramMat);
  #
  FileNameInfo:=Concatenation(ThePrefix, "MoreInfo", String(iLtype));
  RemoveFileIfExist(FileNameInfo);
  MyOutputOfLtype(FileNameInfo, eLtype, eCase);
od;
