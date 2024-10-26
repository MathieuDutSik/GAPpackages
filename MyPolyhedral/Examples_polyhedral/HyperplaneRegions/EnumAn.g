GetHyperplaneArrangement_An:=function(n)
    local ListVect, i, j, eVect, eBasis, ListVectRed;
    ListVect:=[];
    for i in [1..n+1]
    do
        for j in [i+1..n+1]
        do
            eVect:=ListWithIdenticalEntries(n+1,0);
            eVect[i]:=1;
            eVect[j]:=-1;
            Add(ListVect, eVect);
        od;
    od;
    #
    eBasis:=RowReduction(ListVect).EXT;
    ListVectRed:=List(ListVect, x->SolutionMat(eBasis, x));
    return ListVectRed;
end;


n:=7;
eComplex:=GetHyperplaneArrangement_An(n);
ListFace:=EnumerationHyperplaneRegion(eComplex);

    
