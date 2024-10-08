RemoveFractionPlusCoef:=function(TheList)
  local Den, List1, L, iCol, eVal, TheMult;
  if TheList*TheList=0 then
    return rec(TheVect:=TheList, TheMult:=1);
  fi;
  Den:=1;
  for eVal in TheList
  do
    Den:=LcmInt(Den, DenominatorRat(eVal));
  od;
  List1:=TheList*Den;
  L:=AbsInt(List1[1]);
  for iCol in [2..Length(TheList)]
  do
    L:=GcdInt(L, List1[iCol]);
  od;
  TheMult:=Den/L;
  if TheMult<0 then
    Error("Deep incoherence");
  fi;
  return rec(TheVect:=List1/L, TheMult:=TheMult);
end;

RemoveFraction:=function(TheList)
  return RemoveFractionPlusCoef(TheList).TheVect;
end;


RemoveFractionCanonic:=function(TheList)
  local eVect, pos, eSign;
  eVect:=RemoveFraction(TheList);
  pos:=First([1..Length(eVect)], x->eVect[x]<>0);
  if pos=fail then
    return TheList;
  fi;
  if eVect[pos]>0 then
    eSign:=1;
  else
    eSign:=-1;
  fi;
  return eVect*eSign;
end;

RemoveFractionMatrixPlusCoef:=function(OneMat)
  local Den, OneMat1, L, eLine, eCol;
  Den:=1;
  for eLine in OneMat
  do
    for eCol in eLine
    do
      Den:=LcmInt(Den, DenominatorRat(eCol));
    od;
  od;
  OneMat1:=Den*OneMat;
  L:=AbsInt(OneMat1[1][1]);
  for eLine in OneMat1
  do
    for eCol in eLine
    do
      L:=GcdInt(L, eCol);
    od;
  od;
  if L=0 then
    return rec(TheMat:=OneMat, TheMult:=1);
  fi;
  if Den/L <0 then
    Error("Deep incoherence");
  fi;
  return rec(TheMat:=(1/L)*OneMat1, TheMult:=Den/L);
end;

RemoveFractionMatrix:=function(OneMat)
  return RemoveFractionMatrixPlusCoef(OneMat).TheMat;
end;

