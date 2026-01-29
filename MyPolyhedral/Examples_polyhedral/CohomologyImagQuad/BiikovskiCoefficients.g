

ProcessTestCase:=function(input)
    local prefix, FileBoundDual, FileCoho, FileHomol, FilePerf, FileRecMatrix, BoundDual, ListDim, entry, eDim, ListRelation, eBnd, TheResult, dim_shortest, i, FileOut, eOrbit, ListShortest, eRelation;
    Print("ProcessTestCase, step 1\n");
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
    ListShortest:=[];
    for eOrbit in BoundDual[dim_shortest]
    do
        Add(ListShortest, eOrbit.BoundaryImage.SHVtotal);
    od;
    Print("ProcessTestCase, step 4\n");
    ListRelation:=[];
    for eOrbit in BoundDual[dim_shortest - 1]
    do
        eBnd:=eOrbit.BoundaryImage;
        eRelation:=rec(ListElt:=eBnd.ListEltGRP, ListIFace:=eBnd.ListIFace, ListSign:=eBnd.ListSign, SHVtotal:=eBnd.SHVtotal);
        Add(ListRelation, eRelation);
    od;
    Print("ProcessTestCase, step 5\n");
    TheResult:=rec(OrbitShortest:=ListShortest, ListRelation:=ListRelation);
    SaveDataToFile(FileOut, TheResult);
end;



#ListInput:=["GL3_-3", "GL3_-4"];
ListInput:=["GL3_-3", "GL3_-4", "GL4_-3", "GL4_-4"];
#ListInput:=["GL3_-3", "GL3_-4", "GL3_-15", "GL4_-3", "GL4_-4"];

for input in ListInput
do
    ProcessTestCase(input);
od;
