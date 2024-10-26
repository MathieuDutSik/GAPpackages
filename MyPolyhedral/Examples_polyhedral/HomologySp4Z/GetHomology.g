eInvMat:=[
[0 ,0 ,0 ,1],
[0 ,0 ,1 ,0],
[0 ,-1,0 ,0],
[-1, 0,0 ,0]];

TheChoice:=2;
if TheChoice=1 then
  # Sp4Z
  FuncTestBelong:=function(eMat)
    if eMat*eInvMat*TransposedMat(eMat)=eInvMat and IsIntegralMat(eMat)=true then
      return true;
    fi;
    return false;
  end;
elif TheChoice=2 then
  # GSp4Z
  FuncTestBelong:=function(eMat)
    if Position([eInvMat, -eInvMat], eMat*eInvMat*TransposedMat(eMat))<>fail and IsIntegralMat(eMat)=true then
      return true;
    fi;
    return false;
  end;
else
  Print("Please put what you have in mind\n");
  Print(NullMat(5));
fi;



eFace4:=IdentityMat(4);
eFace4stab:=SymplecticStabilizer(eFace4, FuncTestBelong);

eFace3_1:=Concatenation(IdentityMat(4), [[1,0,0,1]]);
eFace3_2:=Concatenation(IdentityMat(4), [[1,0,1,0],[0,1,0,1]]);
eFace3_3:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[0,1,0,1],[1,0,1,-1]]);

eFace2_1:=Concatenation(IdentityMat(4), 
[[1,0,0,1],[0,1,1,0]]);
eFace2_2:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[1,0,0,-1],[0,1,0,1],[1,0,1,-1]]);
eFace2_3:=Concatenation(IdentityMat(4),
[[1,1,0,0],[1,0,1,0],[0,1,0,1],[1,0,1,-1]]);

eFace1_1:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[1,0,1,0],[1,0,0,-1],[0,1,0,1],[1,0,1,-1]]);
eFace1_2:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[0,1,0,-1],[0,0,1,-1],[1,1,-1,0],[1,0,-1,1]]);

eFace0_1:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[1,0,1,0],[1,0,0,-1],[0,1,0,1],[1,1,1,0],[1,0,1,-1]]);
eFace0_2:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[1,0,-1,0],[0,1,0,-1],[0,0,1,-1],[1,1,-1,0],[1,1,0,-1],[1,0,-1,1],[0,1,1,-1]]);

ListListFaces:=[
[eFace0_1,eFace0_2],
[eFace1_1,eFace1_2],
[eFace2_1,eFace2_2,eFace2_3],
[eFace3_1,eFace3_2,eFace3_3],
[eFace4]];



TheBound:=GetComplexListSystems(ListListFaces, FuncTestBelong);
DoHomology:=true;
if DoHomology=true then
  kLevel:=3;
  for i in [1..kLevel]
  do
    Add(TheBound.ListOrbitByRank, []);
  od;
  ListFuncResolution:=GroupHomologyByCellDecomposition(TheBound);
  kCall:=kLevel+1;
  ListFuncResolution.Initialization(kCall);
  ListMatrices:=[];
  for i in [1..kCall]
  do
    Print("Getting differential Nr", i, "\n");
    Add(ListMatrices, ListFuncResolution.GetDifferentiation(i));
  od;
  TheHomologies:=GettingHomologies(ListMatrices);
fi;
GetTheCharLinSystem:=function(ListListFaces, iRank, iOrbit, eElt)
  local eSystSec;
  eSystSec:=ListListFaces[iRank][iOrbit]*eElt;
  return Set(Concatenation(eSystSec, -eSystSec));
end;
DoComplexTopDim:=true;
if DoComplexTopDim=true then
  MaxDim:=Length(TheBound.ListOrbitByRank)-1;
  nbTopDim:=Length(TheBound.ListOrbitByRank[MaxDim+1]);
  for iTop in [1..nbTopDim]
  do
    ListListCell:=[];
    ListListMat:=[];
    ListListIOrbit:=[];
    for i in [1..MaxDim]
    do
      Add(ListListCell, []);
      Add(ListListMat, []);
      Add(ListListIOrbit, []);
    od;
    
    ListListCell[MaxDim]:=[GetTheCharLinSystem(ListListFaces, MaxDim, iTop, IdentityMat(4))];
    ListListMat[MaxDim]:=[IdentityMat(4)];
    ListListIOrbit[MaxDim]:=[iTop];
    for jRank in Reversed([1..MaxDim-1])
    do
      nbCell:=Length(ListListCell[jRank+1]);
      for iCell in [1..nbCell]
      do
        iOrbitB:=ListListIOrbit[jRank+1][iCell];
        eMatB:=ListListMat[jRank+1][iCell];
        BoundImg:=TheBound.ListOrbitByRank[jRank+2][iOrbitB].BoundaryImage;
        len:=Length(BoundImg.ListSign);
        Print("len=", len, "\n");
        for i in [1..len]
        do
          iOrbit:=BoundImg.ListIFace[i];
          eElt:=BoundImg.ListElt[i];
          eProdElt:=eElt*eMatB;
          eSystSec:=ListListFaces[jRank][iOrbit]*eProdElt;
          eSystTot:=Set(Concatenation(eSystSec, -eSystSec));
          pos:=Position(ListListCell[jRank], eSystTot);
          if pos=fail then
            Add(ListListCell[jRank], eSystTot);
            Add(ListListMat[jRank], eProdElt);
            Add(ListListIOrbit[jRank], iOrbit);
          fi;
        od;
      od;
      Print("|ListListCell[", jRank, "]|=", Length(ListListCell[jRank]), "\n");
    od;
    nbVert:=Length(ListListCell[1]);
    ListListSets:=[];
    for jRank in [1..MaxDim]
    do
      nbCell:=Length(ListListCell[jRank]);
      ListSets:=[];
      for iCell in [1..nbCell]
      do
        eSet:=[];
        for iVert in [1..nbVert]
        do
          if IsSubset(ListListCell[1][iVert], ListListCell[jRank][iCell])=true then
            Add(eSet, iVert);
          fi;
        od;
        Add(ListSets, eSet);
      od;
      Add(ListListSets, ListSets);
    od;
  od;
fi;


