

GetHostName:=function()
  local FileD1, FileD2, reply;
  FileD1:="/tmp/HostName1";
  FileD2:="/tmp/HostName2";
  Exec("echo $HOSTNAME > ", FileD1);
  reply:=ReadAsFunction(FileD2)();
  RemoveFile(FileD1);
  RemoveFile(FileD2);
  return reply;
end;
PermListPlusFail:=function(eList)
  local h;
  h:=PermList(eList);
  if h=fail then
    Print("Error in computing PermList of ", eList, "\n");
    Print(NullMat(5));
  fi;
  return h;
end;



ProductList:=function(SetList1, SetList2)
  local eSet1, eSet2, ListR, S;
  ListR:=[];
  for eSet1 in SetList1
  do
    for eSet2 in SetList2
    do
      S:=ShallowCopy(eSet1);
      Append(S, eSet2);
      Add(ListR, S);
    od;
  od;
  return ListR;
end;



FromHypermetricVectorToHypermetricFace:=function(HypV)
  local HypDim, V, i, j, S, k, iCol;
  HypDim:=Length(HypV);
  S:=Sum(HypV);
  k:=(S-1)/2;
  V:=[k*(k+1)];
  #
  for i in [1..HypDim-1]
  do
    for j in [i+1..HypDim]
    do
      Add(V, -HypV[i]*HypV[j]);
    od;
  od;
  return V;
end;



