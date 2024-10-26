EXT:=ClassicalExtremeDelaunayPolytopes("G6");

EXTred:=List(EXT, x->x{[2..7]});
eCent:=Isobarycenter(EXTred);
EXTdiff:=RemoveFractionMatrix(List(EXTred, x->x-eCent));

EXTtotal:=ZONOTOP_GetVerticesMinkSum(EXTdiff);
