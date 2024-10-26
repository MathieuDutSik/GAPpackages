eRecInfo:=Q5_GetPolyhedraH3();


eRec:=Q5_GetPolyhedraH3_H4();
ListVect:=eRec.RootSystemH4;
TheGRP:=eRec.PermGroup120;

EXT:=List(ListVect, x->Concatenation([1], x));


ListOrbInc:=DualDescriptionStandard_Q5(EXT, TheGRP);
