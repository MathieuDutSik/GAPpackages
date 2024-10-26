EXT:=ClassicalExtremeDelaunayPolytopes("G6");

EXTred:=List(EXT, x->x{[2..7]});
eCent:=Isobarycenter(EXTred);
EXTdiff:=RemoveFractionMatrix(List(EXTred, x->x-eCent));

GRPinf:=__VectorConfigurationFullDim_Automorphism(EXTdiff);
GRPmatr:=GRPinf.MatrixGroup;

EXTtotal:=ZONOTOP_GetVertices(EXTdiff, GRPmatr);
