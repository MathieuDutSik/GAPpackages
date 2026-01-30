

ProcessTestCase:=function(input)
    local prefix, FileBoundDual, FileCoho, FileHomol, FilePerf, FileRecMatrix, BoundDual, ListDim, entry, eDim, ListRelation, eBnd, TheResult, dim_shortest, i, FileOut, eOrbit, OrbitShortest, eRelation, idx, SHV1, SHV2, n_idx, EXT1, EXT2, ListSHVmiss, ListEXTmiss, SHVmiss, EXTmiss;
    Print("ProcessTestCase, step 1, inpus=", input, "\n");
    prefix:=Concatenation("HomologyImagQuad", input);
    FileBoundDual:=Concatenation("Result/", prefix, "_BoundDual");
    FileCoho:=Concatenation("Result/", prefix, "_Coho");
    FileHomol:=Concatenation("Result/", prefix, "_homol");
    FilePerf:=Concatenation("Result/", prefix, "_Perf");
    FileRecMatrix:=Concatenation("Result/", prefix, "_RecMatrix");

    Print("ProcessTestCase, step 2\n");
    BoundDual:=ReadAsFunction(FileBoundDual)();
    Print("ProcessTestCase, step 3\n");
    ListDim:=[];
    for entry in BoundDual
    do
        eDim:=Length(entry);
        Add(ListDim, eDim);
    od;
    Print("input=", input, " ListDim=", ListDim, "\n");
    dim_shortest:=1;
    for i in [1..Length(ListDim)]
    do
        if ListDim[i] > 0 then
            dim_shortest:=i;
        fi;
    od;
    FileOut:=Concatenation("Biikovskii_", input, ".data");
    OrbitShortest:=[];
    for eOrbit in BoundDual[dim_shortest]
    do
        Add(OrbitShortest, eOrbit.BoundaryImage.RecTotal);
    od;
    Print("ProcessTestCase, step 4\n");
    ListRelation:=[];
    for eOrbit in BoundDual[dim_shortest - 1]
    do
        Print("Building the relation\n");
        eBnd:=eOrbit.BoundaryImage;
        eRelation:=rec(ListEltGRP:=eBnd.ListEltGRP, ListElt:=eBnd.ListElt, ListIFace:=eBnd.ListIFace, ListSign:=eBnd.ListSign, RecTotal:=eBnd.RecTotal);
        ListSHVmiss:=[];
        ListEXTmiss:=[];
        n_idx:=Length(eRelation.ListSign);
        for idx in [1..n_idx]
        do
            Print("idx=", idx, " / ", n_idx, "\n");
            SHV1:=OrbitShortest[eRelation.ListIFace[idx]].SHV;
            SHV2:=SHV1 * Inverse(eRelation.ListEltGRP[idx]);
            if IsSubset(Set(eRelation.RecTotal.SHV), Set(SHV2))=false then
                Error("The boundary is not mapped as expected A");
            fi;
            SHVmiss:=Filtered(eRelation.RecTotal.SHV, x->Position(SHV2, x)=fail);
            Add(ListSHVmiss, SHVmiss);
            #
            EXT1:=OrbitShortest[eRelation.ListIFace[idx]].EXT;
            EXT2:=EXT1 * eRelation.ListElt[idx];
            if IsSubset(Set(eRelation.RecTotal.EXT), Set(EXT2))=false then
                Error("The boundary is not mapped as expected B");
            fi;
            EXTmiss:=Filtered(eRelation.RecTotal.EXT, x->Position(EXT2, x)=fail);
            Print("|EXTmiss|=", Length(EXTmiss), " |RecTotal.EXT|=", Length(eRelation.RecTotal.EXT), " |EXT2|=", Length(EXT2), "\n");
            
            Add(ListEXTmiss, EXTmiss);
        od;
        eRelation.ListSHVmiss:=ListSHVmiss;
        eRelation.ListEXTmiss:=ListEXTmiss;
        Add(ListRelation, eRelation);
    od;
    Print("ProcessTestCase, step 5\n");
    TheResult:=rec(OrbitShortest:=OrbitShortest, ListRelation:=ListRelation);
    SaveDataToFile(FileOut, TheResult);
end;



#ListInput:=["GL3_-3", "GL3_-4"];
ListInput:=["GL3_-3", "GL3_-4", "GL4_-3", "GL4_-4"];
#ListInput:=["GL3_-3", "GL3_-4", "GL3_-15", "GL4_-3", "GL4_-4"];

for input in ListInput
do
    ProcessTestCase(input);
od;
