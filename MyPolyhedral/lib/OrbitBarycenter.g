SolutionMatRepetitive:=function(TheBasis)
  local HRL, SelMat, InvMat, MySolutionMat;
  if RankMat(TheBasis)<>Length(TheBasis) then
    Error("It is not ok for this procedure");
  fi;
  HRL:=ColumnReduction(TheBasis);
  SelMat:=List(TheBasis, x->x{HRL.Select});
  InvMat:=Inverse(SelMat);
  MySolutionMat:=function(eVect)
    local MySol;
    MySol:=eVect{HRL.Select}*InvMat;
    if MySol*TheBasis<>eVect then
      return fail;
    fi;
    return MySol;
  end;
  return MySolutionMat;
end;



DirectSpannEquivariantSpace:=function(TheBasis, TheMatGrp)
  local ListSpann, MSL, IsFinished, eVect, eGen;
  while(true)
  do
    ListSpann:=ShallowCopy(TheBasis);
    MSL:=SolutionMatRepetitive(TheBasis);
    IsFinished:=true;
    for eVect in TheBasis
    do
      for eGen in GeneratorsOfGroup(TheMatGrp)
      do
        if MSL(eVect*eGen)=fail then
          Add(ListSpann, eVect*eGen);
          IsFinished:=false;
        fi;
      od;
    od;
    if IsFinished=true then
      break;
    fi;
    TheBasis:=RowReduction(ListSpann).EXT;
  od;
  return TheBasis;
end;

OrbitBarycenter:=function(TheExt, TheMatGrp)
  local ListSpann, TheBasis, IsFinished, eVect, ListEqua, ListB, eGen, Alpha, RelPointSet, IsInvariant, MSL;
  ListSpann:=List(GeneratorsOfGroup(TheMatGrp), x->RemoveFraction(TheExt*x-TheExt));
  TheBasis:=RowReduction(ListSpann).EXT;
  IsInvariant:=true;
  for eGen in GeneratorsOfGroup(TheMatGrp)
  do
    if TheExt*eGen<>TheExt then
      IsInvariant:=false;
    fi;
  od;
  if IsInvariant=true then
    return rec(TheBarycenter:=TheExt, RelPointSet:=[TheExt]);
  fi;
  TheBasis:=DirectSpannEquivariantSpace(TheBasis, TheMatGrp);
  ListEqua:=[];
  ListB:=[];
  for eGen in GeneratorsOfGroup(TheMatGrp)
  do
    Append(ListEqua, TransposedMat(TheBasis*eGen-TheBasis));
    Append(ListB, TheExt-TheExt*eGen);
  od;
  if RankMat(ListEqua)<>Length(TheBasis) then
    Error("We have a conception error here, please panic");
  fi;
  Alpha:=SolutionMat(TransposedMat(ListEqua), ListB);
  RelPointSet:=Concatenation([TheExt], List(TheBasis, x->TheExt+x));
  return rec(TheBarycenter:=TheExt+Alpha*TheBasis, RelPointSet:=RelPointSet);
end;





# Action of the group is M |---> t(P) M P
MatrixTransformationMappingToSymmetricMatrix:=function(eMat)
  local n, MatDim, eGenSymm, i, eVect, eSymmMat, eImgSymmMat;
  n:=Length(eMat);
  MatDim:=n*(n+1)/2;
  eGenSymm:=[];
  for i in [1..MatDim]
  do
    eVect:=ListWithIdenticalEntries(MatDim,0);
    eVect[i]:=1;
    eSymmMat:=VectorToSymmetricMatrix(eVect, n);
    eImgSymmMat:=TransposedMat(eMat)*eSymmMat*eMat;
    Add(eGenSymm, SymmetricMatrixToVector(eImgSymmMat));
  od;
  return eGenSymm;
end;


#
#
# Action of the group is M |---> t(P) M P
OrbitBarycenterSymmetricMatrix:=function(TheSymMat, TheMatGrp)
  local n, MatDim, NewListGens, eGen, eGenNew, i, eVect, eSymmMat, eImgSymmMat, GRPnew, TheVector, TheSingle;
  n:=Length(TheSymMat);
  MatDim:=n*(n+1)/2;
  NewListGens:=List(GeneratorsOfGroup(TheMatGrp), MatrixTransformationMappingToSymmetricMatrix);
  GRPnew:=Group(NewListGens);
  TheVector:=SymmetricMatrixToVector(TheSymMat);
  TheSingle:=OrbitBarycenter(TheVector, GRPnew);
  return VectorToSymmetricMatrix(TheSingle.TheBarycenter, n);
end;
