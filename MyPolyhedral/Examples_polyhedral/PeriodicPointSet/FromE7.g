GramMat:=ClassicalSporadicLattices("E7");

MatrixGRP:=ArithmeticAutomorphismGroup([GramMat]);

ListFunc:=DelaunayComputationStandardFunctions(GramMat);
DelCO:=ListFunc.GetDelaunayDescription();

ListSiz:=List(DelCO, x->Length(x.EXT));
Pos:=Position(ListSiz, 8);

CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, DelCO[Pos].EXT);
TheCenter:=CP.Center;
TheCenterRed:=VectorMod1(TheCenter{[2..8]});
FuncActionMod1:=function(eClass, eElt)
  return VectorMod1(eClass*eElt);
end;
TheOrbit:=Orbit(MatrixGRP, TheCenterRed, FuncActionMod1);

ListCosets:=List(TheOrbit, x->Concatenation([1], x));

eRecU:=rec(GramMat:=GramMat, ListCosets:=ListCosets);
ListFunc:=Periodic_DelaunayComputationStandardFunctions(eRecU);
TheDesc:=ListFunc.GetDelaunayDescription();
ListVoronoiVertices:=ListFunc.GetVoronoiVertices();
