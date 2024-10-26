n:=4;

eRec:=LatticeDn(n);
TheGram:=eRec.GramMat;

SHV:=ShortestVectorDutourVersion(TheGram);
nbV:=Length(SHV)/2;
ListVect:=List([1..nbV], x->SHV[2*x]);


eCase:=SHORT_CreateECaseForPolyhedralDecomposition(ListVect);

eInfo:=POLYDEC_EnumerationLtype(eCase);

