GramMat:=[
[2,1],
[1,2]
];



MatrixGRP:=ArithmeticAutomorphismGroup([GramMat]);

AffineGroup:=Group(List(GeneratorsOfGroup(MatrixGRP), x->FuncCreateBigMatrix(ListWithIdenticalEntries(Length(GramMat),0), x)));


ListCosets:=List([[1, 1/3, 1/3], [1, -1/3, -1/3]], PeriodicVectorMod1);

eRecU:=rec(GramMat:=GramMat, ListCosets:=ListCosets);
ListFunc:=Periodic_DelaunayComputationStandardFunctions(eRecU);
TheDesc:=ListFunc.GetDelaunayDescription();
ListVoronoiVertices:=ListFunc.GetVoronoiVertices();
