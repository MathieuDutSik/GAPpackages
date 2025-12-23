ListMat:=ReadAsFunction("RecMatrix_ListMat")();


nMat:=Length(ListMat);
for iMat in [1..nMat]
do
    Print("iMat=", iMat, " / ", nMat, "\n");
    eFile:=Concatenation("Matrix", String(iMat), "_", String(nMat));
    eDensMat:=GetDenseMat(ListMat[iMat]);
    WriteMatrixFile(eFile, eDensMat);
od;
