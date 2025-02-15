
ListNames:=["Lambda9", "Lambda10"];


f:=function(eRes)
    ComputeCoveringDensityFromDimDetCov(eRes.TheDim, eRes.TheDet, eRec.TheCov);
end;



ListRes:=[];
for eName in ListNames
do
    GramMat:=ClassicalSporadicLattices(eName);
    LFC:=DelaunayComputationStandardFunctions(GramMat);
    eRes:=LFC.GetCoveringDensity();
    Add(ListRes, eRes);
od;

