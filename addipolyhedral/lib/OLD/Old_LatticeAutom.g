FileAut_Grp:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"Aut_grp");


# in argument a family F1, ...., Fm of square matrices
# the first being symmetric and positive definite.
#
# return the group of matrices P satisfying to 
# TransposedMat(P)*Fi*P=Fi for all Fi
CallToAut_Grp:=function(ListMat)
  local FileIn, FileOut, FileGap, reply, GRP, eGen, eMat;
  FileIn:=Filename(POLYHEDRAL_tmpdir, "ListMat.in");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "ListMat.out");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "ListMat.gap");
  __FunctionOutPutMatrix_TYP(FileIn, ListMat);
  Exec(FileAut_Grp, " ", FileIn, " > ", FileOut);
  Exec(FileMatrix_TYP_Aut_Grp, " < ", FileOut, " > ", FileGap);
  reply:=ReadAsFunction(FileGap)();
  RemoveFile(FileIn);
  RemoveFile(FileOut);
  RemoveFile(FileGap);
  GRP:=Group(reply.ListMat);
  SetSize(GRP, reply.order);
  for eGen in GeneratorsOfGroup(GRP)
  do
    for eMat in ListMat
    do
      if TransposedMat(eGen)*eMat*eGen<>eMat then
        Error("Error in CallToAut_Grp");
      fi;
    od;
  od;
  return GRP;
end;




#
#
# return the a generator of the group of matrices U
# satisfying to
# U*F*TransposedMat(U)=F
Method2AutomorphismLattice:=function(GramMat)
  local U, ListMatTrans, GRP, eGen;
  U:=CallToAut_Grp([GramMat]);
  ListMatTrans:=List(GeneratorsOfGroup(U), TransposedMat);
  GRP:=Group(ListMatTrans);
  SetSize(GRP, Size(U));
  for eGen in GeneratorsOfGroup(GRP)
  do
    if eGen*GramMat*TransposedMat(eGen)<>GramMat then
      Error("Error in Method2AutomorphismLattice. Invariance not satisfied");
    fi;
  od;
  return GRP;
end;

