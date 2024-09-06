FileEnumerateSEmbedding:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"GRAPH_EnumerateDistanceSembedding");
#########################################################################
#                         l1emb.g                  D.V.Pasechnik 1996
#                                                    dima@win.tue.nl
# the functions to call are
# IsL1Emb(G), where G is a graph in GRAPE format.
# IsRigidL1(G)
#
#########################################################################
#                           and                    M.A.Dutour 2001
# 
#
#########################################################################

ShortestPathDistanceMatrix:=function(G)
  local M, iVert, jVert, n;
  n:=G.order;
  M:=NullMat(n,n);
#  Print("Begin ShortestPathDistanceMatrix, n=", n, "\n");
  for iVert in [1..n]
  do
    for jVert in [1..n]
    do
      M[iVert][jVert]:=Distance(G,iVert,jVert);
    od;
  od;
#  Print("End ShortestPathDistanceMatrix\n");
  return M;
end;

DistanceVector:=function(V1, V2)
  local S, iCol;
  S:=0;
  for iCol in [1..Length(V1)]
  do
    if V1[iCol]<>V2[iCol] then
      S:=S+1;
    fi;
  od;
  return S;
end;



EmbeddingToGraph:=function(Embedding)
  local n, dim, G, iVert, jVert;
  n:=Length(Embedding);
  dim:=Length(Embedding[1]);
  G:=NullGraph(Group(()), n);
  for iVert in [1..n-1]
  do
    for jVert in [iVert+1..n]
    do
      if DistanceVector(Embedding[iVert],Embedding[jVert])=2 then
        AddEdgeOrbit(G, [iVert, jVert]);
        AddEdgeOrbit(G, [jVert, iVert]);
      fi;
    od;
  od;
  return G;
end;

EmbeddingToDistMat:=function(Embedding)
  local n, dim, DM, iVert, jVert, S, iCol;
  n:=Length(Embedding);
  dim:=Length(Embedding[1]);
  DM:=NullMat(n,n);
  for iVert in [1..n]
  do
    for jVert in [1..n]
    do
      DM[iVert][jVert]:=DistanceVector(Embedding[iVert],Embedding[jVert])/2;
    od;
  od;
  return DM;
end;






#IsSpanningTree:=function(EdgeSet, n)
#  local iNode, jNode, Status;
#  for iNode in [1..n]
#  do
#    Status[iNode]:=iNode;
#  od;
#  for iNode in [1..n-1]
#  do
#    for jNode in [i+1..n]
#    do
#      if [iNode,jNode] in EdgeSet then
#        Status[jNode]:=Status[iNode];
#      fi;
#    od;
#  od;
#  for iNode in [1..n]
#  do
#    if Status[iNode]<>Status[1] then
#      return false;
#    fi;
#  od;
#  return true;
#end;





EmbeddingChange:=function(Embedding, VectorChange)
  local NewEmbedding, iVect;
  NewEmbedding:=[];
  for iVect in [1..Length(Embedding)]
  do
    NewEmbedding[iVect]:=(Embedding[iVect]+VectorChange) mod 2;
  od;
  return NewEmbedding;
end;





EquicutNess:=function(Embedding)
  local nbV, dimension, ListSum, i, iCol;
  nbV:=Length(Embedding);
  dimension:=Length(Embedding[1]);
  ListSum:=ListWithIdenticalEntries(dimension, 0);
  for i in [1..nbV]
  do
    ListSum:=ListSum+Embedding[i];
  od;
  for iCol in [1..dimension]
  do
    if 2*ListSum[iCol]<>nbV then
      return false;
    fi;
  od;
  return true;
end;



QbalancedNess:=function(Embedding)
  local nbV, dimension, ListSum, i, iCol, q, EmbedNew, iVert;
  nbV:=Length(Embedding);
  EmbedNew:=ShallowCopy(Embedding);
  dimension:=Length(Embedding[1]);
  ListSum:=ListWithIdenticalEntries(dimension, 0);
  for i in [1..nbV]
  do
    ListSum:=ListSum+Embedding[i];
  od;
  if Length(Set(ListSum))>2 then
    return false;
  fi;
  q:=ListSum[1];
  for iCol in [1..dimension]
  do
    if ListSum[iCol]<>q and ListSum[iCol]<>nbV-q then
      return false;
    fi;
    if ListSum[iCol]=nbV-q then
      for iVert in [1..nbV]
      do
        EmbedNew[iVert][iCol]:=1-Embedding[iVert][iCol];
      od;
    fi;
  od;
  return [q, EmbedNew];
end;



#
#
# We assume that the the first element of the given embedding
# has first element equal to zero
Johnson:=function(Embedding)
  local FuncSize, dimension, nbVert, LproperAtom, iVert, jVert, WanabeeEdge, Gra, eAtom, Pos1, Pos2, CMP, Seto, eCMP;
  FuncSize:=function(Line)
    local i, S;
    S:=0;
    for i in [1..Length(Line)]
    do
      S:=S+Line[i];
    od;
    return S;
  end;
  dimension:=Length(Embedding[1]);
  nbVert:=Length(Embedding);
  LproperAtom:=[];
  for iVert in [1..nbVert-1]
  do
    for jVert in [iVert+1..nbVert]
    do
      WanabeeEdge:=(Embedding[iVert]+Embedding[jVert]) mod 2;
      if FuncSize(Embedding[iVert])<>FuncSize(Embedding[jVert]) and FuncSize(WanabeeEdge)=2 then
        AddSet(LproperAtom, WanabeeEdge);
      fi;
    od;
  od;
  Gra:=NullGraph(Group(()), dimension);
  for eAtom in LproperAtom
  do
    Pos1:=Position(eAtom,1);
    Pos2:=Position(eAtom,1,Pos1);
    AddEdgeOrbit(Gra,[Pos1,Pos2]);
    AddEdgeOrbit(Gra,[Pos2,Pos1]);
  od;
  if IsBipartite(Gra)=true then
    CMP:=Bicomponents(Gra);
    Seto:=ListWithIdenticalEntries(dimension, 0);
    Seto{CMP[1]}:=ListWithIdenticalEntries(Length(CMP[1]), 1);
    return [Length(CMP[1]), EmbeddingChange(Embedding, Seto)];
  fi;
  return false;
end;


ExtractOccurence:=function(List)
  local H, i, nbOcc, S;
  H:=Set(List);
  S:=[];
  for i in [1..Length(H)]
  do
    nbOcc:=1;
    while(PositionNthOccurrence(List, H[i], nbOcc)<>fail)
    do
      nbOcc:=nbOcc+1;
    od;
    S[i]:=[H[i],nbOcc-1];
  od;
  return S;
end;





CheckSembedding:=function(DM, s, Embedding)
  local n, iVert, jVert;
  n:=Length(Embedding);
  for iVert in [1..n]
  do
    for jVert in [1..n]
    do
      if DM[iVert][jVert]<=s then
        if DistanceVector(Embedding[iVert],Embedding[jVert])<>2*DM[iVert][jVert] then
          return false;
        fi;
      fi;
    od;
  od;
  return true;
end;


#
#
# This function use 
# --a starting point x which will be labeled 0
# --a list of edges
# --a labeling of the edges
CreateEmbedding:=function(StartPoint, ListEdge, LabelingEdge)
  local nbV, nbVinvLineGraph, iEdge, Assigned, Embedding, eEdge, iVert, jVert, eLabel;
  nbV:=0;
  nbVinvLineGraph:=0;
  for iEdge in [1..Length(ListEdge)]
  do
    if ListEdge[iEdge][2]>nbV then
      nbV:=ListEdge[iEdge][2];
    fi;
    if LabelingEdge[iEdge][2]>nbVinvLineGraph then
      nbVinvLineGraph:=LabelingEdge[iEdge][2];
    fi;
  od;
  Assigned:=[StartPoint];
  Embedding:=[];
  Embedding[StartPoint]:=ListWithIdenticalEntries(nbVinvLineGraph, 0);
  while Length(Assigned)<nbV
  do
    for iEdge in [1..Length(ListEdge)]
    do
      eEdge:=ListEdge[iEdge];
      if Length(Intersection(Assigned, eEdge))=1 then
#        Print("Embedding=", Embedding, "\n");
        iVert:=Intersection(Assigned, eEdge)[1];
        jVert:=Difference(eEdge, [iVert])[1];
        Embedding[jVert]:=ShallowCopy(Embedding[iVert]);
        eLabel:=LabelingEdge[iEdge];
        Embedding[jVert][eLabel[1]]:=1-Embedding[jVert][eLabel[1]];
        Embedding[jVert][eLabel[2]]:=1-Embedding[jVert][eLabel[2]];
        AddSet(Assigned, jVert);
      fi;
    od;
  od;
  return Embedding;
end;



FindIsometricCycleEvenLength:=function(GraphCE, MaxD)
  local GRP, ListV, O, ListOrbit, eO, CircleDistance, FuncTestOK, NewListOrbit, NewCE, Lvert, FuncInsert, iter, eVert;
  GRP:=GraphCE.group;
  ListV:=[1..GraphCE.order];
  O:=Orbits(GRP, ListV, OnPoints);
  ListOrbit:=[];
  for eO in O
  do
    Add(ListOrbit, [eO[1]]);
  od;
  CircleDistance:=function(i, j)
    local eDiff, fDiff;
    eDiff:=AbsInt(i-j);
    fDiff:=MaxD-eDiff;
    return Minimum(eDiff, fDiff);
  end;
  FuncTestOK:=function(ePath)
    local i, j;
    for i in [1..Length(ePath)-1]
    do
      j:=Length(ePath);
      if CircleDistance(i,j)<>Distance(GraphCE, ePath[i], ePath[j]) then
        return false;
      fi;
    od;
    return true;
  end;
  for iter in [1..MaxD-1]
  do
    Print("iter=", iter, "  |ListOrbit|=", Length(ListOrbit), "\n");
    NewListOrbit:=[];
    FuncInsert:=function(ePath)
      local eOrb;
      for eOrb in NewListOrbit
      do
        if RepresentativeAction(GRP, Set(eOrb), Set(ePath), OnSets)<>fail then
          return;
        fi;
      od;
      Add(NewListOrbit, ePath);
    end;
    for eO in ListOrbit
    do
      Lvert:=eO[Length(eO)];
      for eVert in Adjacency(GraphCE, Lvert)
      do
        NewCE:=[];
        Append(NewCE, eO);
        Add(NewCE, eVert);
        if FuncTestOK(NewCE)=true then
#          Print("Inserting ", NewCE, "\n");
          FuncInsert(NewCE);
        fi;
      od;
    od;
    ListOrbit:=ShallowCopy(NewListOrbit);
  od;
  Print("|Cycles|=", Length(NewListOrbit), "\n");
  return NewListOrbit;
end;




EdgeDist:=function(GraphCE, eEdge, fEdge)
  local ptX, ptY, ptZ, ptT, u, d_uX, d_uY, d_uZ, d_uT, swp;
  ptX:=eEdge[1]; ptY:=eEdge[2];
  ptZ:=fEdge[1]; ptT:=fEdge[2];
  for u in [1..GraphCE.order]
  do
    d_uX:=Distance(GraphCE, u, ptX);
    d_uY:=Distance(GraphCE, u, ptY);
    if AbsInt(d_uX-d_uY)=1 then
      d_uZ:=Distance(GraphCE, u, ptZ);
      d_uT:=Distance(GraphCE, u, ptT);
      if AbsInt(d_uZ-d_uT)=1 then
        if d_uY=d_uX-1 then
          swp:=ptX;
          ptX:=ptY;
          ptY:=swp;
        fi;
        if d_uT=d_uZ-1 then
          swp:=ptZ;
          ptZ:=ptT;
          ptT:=swp;
        fi;
        return -Distance(GraphCE,ptY,ptT)+Distance(GraphCE,ptX,ptT)+Distance(GraphCE,ptY,ptZ)-Distance(GraphCE,ptX,ptZ);
      fi;
    fi;
  od;
  Print("unable to compute some distances between edges\n");
  Print(NullMat(5));
end;






DirectEmbeddingEquivariant:=function(GraphCE, ListOrbitIsometricCycles)
  local GRP, nbV, O, eO, eOrb, fOrb, eImg, OrbitEdgeRepresentative, ListEdge, GraphEdge, GroupEdge, eGen, NewGens, eList, iEdge, jEdge, eDist, FuncInsert, eVert, Stab, eV, ClassDist, GraphEdge2, iClass, jClass, ListClassFinal, ListClass1, NewGens2, GroupEdge2, eH1, eH2, fH1, fH2, eEdge, fEdge, FuncFindClass, len, TheHalf, GraphEdge1, eCycle, ListLabel, INVER, GraphClass3, GroupClass3, ListClass3, TheEmbed, NewGens3, fConn, eConn, fVert, ListClass2, dist1, dist2;
  GRP:=GraphCE.group;
  nbV:=GraphCE.order;
  Print("|Group|=", Order(GRP), "  |V(graph)|=", nbV, "\n");
  OrbitEdgeRepresentative:=[];
  ListEdge:=[];
  FuncInsert:=function(eEdge)
    local eSet, eOrb;
    eSet:=Set(eEdge);
    for eOrb in OrbitEdgeRepresentative
    do
      if RepresentativeAction(GRP, eOrb, eSet, OnSets)<>fail then
        return;
      fi;
    od;
    Add(OrbitEdgeRepresentative, eSet);
    Append(ListEdge, Orbit(GRP, eSet, OnSets));
  end;
  for eO in Orbits(GRP, [1..nbV], OnPoints)
  do
    eVert:=eO[1];
    for eV in Adjacency(GraphCE, eVert)
    do
      FuncInsert([eVert, eV]);
    od;
  od;
  Print("|Orb Edge|=", Length(OrbitEdgeRepresentative), " |Edge|=", Length(ListEdge), "\n");
  NewGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=[];
    for iEdge in [1..Length(ListEdge)]
    do
      eImg:=OnSets(ListEdge[iEdge], eGen);
      Add(eList, Position(ListEdge, eImg));
    od;
    Add(NewGens, PermList(eList));
  od;
  GroupEdge:=Group(NewGens);
  Print("GroupEdge computed\n");
  GraphEdge1:=NullGraph(GroupEdge, Length(ListEdge));
  for eCycle in ListOrbitIsometricCycles
  do
    len:=Length(eCycle);
    TheHalf:=len/2;
    for eH1 in [1..Length(eCycle)]
    do
      eH2:=NextIdx(len, eH1);
      fH1:=NextKIdx(len, eH1, TheHalf);
      fH2:=NextIdx(len, fH1);
      eEdge:=Set([eCycle[eH1], eCycle[eH2]]);
      fEdge:=Set([eCycle[fH1], eCycle[fH2]]);
      iEdge:=Position(ListEdge, eEdge);
      jEdge:=Position(ListEdge, fEdge);
      AddEdgeOrbit(GraphEdge1, [iEdge, jEdge]);
    od;
  od;
  ListClass1:=ConnectedComponents(GraphEdge1);
  Print("Find ", Length(ListClass1), " classes using isometric cycles\n");
  #
  NewGens2:=[];
  for eGen in GeneratorsOfGroup(GroupEdge)
  do
    FuncFindClass:=function(iEdge)
      local iClass;
      for iClass in [1..Length(ListClass1)]
      do
        if Position(ListClass1[iClass], iEdge)<>fail then
          return iClass;
        fi;
      od;
    end;
    eList:=[];
    for iClass in [1..Length(ListClass1)]
    do
      iEdge:=ListClass1[iClass][1];
      jEdge:=OnPoints(iEdge, eGen);
      Add(eList, FuncFindClass(jEdge));
    od;
    Add(NewGens2, PermList(eList));
  od;
  GroupEdge2:=Group(NewGens2);
  #
  #
  ClassDist:=function(eClass, fClass)
    return EdgeDist(GraphCE, ListEdge[eClass[1]], ListEdge[fClass[1]]);
  end;
  GraphEdge2:=NullGraph(GroupEdge2, Length(ListClass1));
  for eOrb in Orbits(GroupEdge2, [1..Length(ListClass1)], OnPoints)
  do
    iClass:=eOrb[1];
    Stab:=Stabilizer(GroupEdge2, iClass, OnPoints);
    O:=Orbits(Stab, Difference([1..Length(ListClass1)], [iClass]), OnPoints);
    for fOrb in O
    do
      jClass:=fOrb[1];
      eDist:=ClassDist(ListClass1[iClass], ListClass1[jClass]);
      if eDist=false then
        return false;
      fi;
      if eDist<0 then
        Print("Error by breaking non-negativity\n");
        return false;
      fi;
      if eDist=2 then
        AddEdgeOrbit(GraphEdge2, [iClass, jClass]);
        AddEdgeOrbit(GraphEdge2, [jClass, iClass]);
      fi;
    od;
  od;
  Print("Graph of eDist=2 computed\n");
  ListClass2:=ConnectedComponents(GraphEdge2);
  Print("Find ", Length(ListClass2), " classes\n");
#  Print(NullMat(5));


  ListClass3:=[];
  for eConn in ListClass2
  do
    fConn:=[];
    for iClass in eConn
    do
      Append(fConn, ListClass1[iClass]);
    od;
    fConn:=Set(fConn);
    Add(ListClass3, fConn);
  od;
  Print("Merging of classes finished, find ", Length(ListClass3), " classes\n");


  NewGens3:=[];  
  for eGen in GeneratorsOfGroup(GroupEdge)
  do
    FuncFindClass:=function(iEdge)
      local iClass;
      for iClass in [1..Length(ListClass3)]
      do
        if Position(ListClass3[iClass], iEdge)<>fail then
          return iClass;
        fi;
      od;
    end;
    eList:=[];
    for iClass in [1..Length(ListClass3)]
    do
      iEdge:=ListClass3[iClass][1];
      jEdge:=OnPoints(iEdge, eGen);
      Add(eList, FuncFindClass(jEdge));
    od;
    Add(NewGens3, PermList(eList));
  od;
  GroupClass3:=Group(NewGens3);
  
  GraphClass3:=NullGraph(GroupClass3, Length(ListClass3));
  for eOrb in Orbits(GroupClass3, [1..Length(ListClass3)], OnPoints)
  do
    iClass:=eOrb[1];
    Stab:=Stabilizer(GroupClass3, iClass, OnPoints);
    O:=Orbits(Stab, Difference([1..Length(ListClass3)], [iClass]), OnPoints);
    for fOrb in O
    do
      jClass:=fOrb[1];
      eDist:=ClassDist(ListClass3[iClass], ListClass3[jClass]);
      if eDist=false then
        Print("Error by impossibility of computing distances\n");
        return false;
      fi;
      if eDist<0 then
        Print("Error by breaking non-negativity\n");
        return false;
      fi;
      if eDist=1 then
        AddEdgeOrbit(GraphClass3, [iClass, jClass]);
      fi;
    od;
  od;
  Print("line graph computed\n");


  INVER:=InverseLineGraph(GraphClass3);
  Print("Inverse line graph computed\n");
  if INVER=false then
    Print("Not a line graph\n");
    return false;
  fi;
  ListLabel:=[];
  for iClass in [1..Length(ListClass3)]
  do
    for iEdge in ListClass3[iClass]
    do
      ListLabel[iEdge]:=ShallowCopy(INVER[2][iClass]);
    od;
  od;
  Print("Label assignation finished\n");
  TheEmbed:=CreateEmbedding(1, ListEdge, ListLabel);
  Print("Embedding computed\n");
  #
  # the idea is that the preceding computation are all done under 
  # assumption that we have an embedding.
  # those hypothesis are finally checked here.
  # and no group can be used here (I did the error two times)
  #
  Print("Doing checks and embedding, it can be long\n");
  Print("   but it cannot be bypassed\n");
  for eVert in [1..nbV-1]
  do
    for fVert in [eVert+1..nbV]
    do
      dist1:=DistanceVector(TheEmbed[eVert], TheEmbed[fVert]);
      dist2:=Distance(GraphCE, eVert, fVert);
      if dist1<>2*dist2 then
        return false;
      fi;
    od;
  od;
  Print("Embedding has been checked\n");
  return TheEmbed;
end;





DirectEmbedding:=function(GraphCE)
  local EdgeDist, ET, Aspec, u, iEdge, jEdge, eDist, Cspec, eElt, Dspec, iVert, jVert, eEdge1, eEdge2, iElt, jElt, eDist2, ListLabel, iCspec, INVER;
  Print("****Start treating L1-embedding\n");
  EdgeDist:=function(eEdge,fEdge, u) # the function i(x,y)
    local a, b, c, d, swp;
    a:=eEdge[1]; b:=eEdge[2];
    c:=fEdge[1]; d:=fEdge[2];
    if Distance(GraphCE,u,b)=Distance(GraphCE,u,a)-1 then
      swp:=a;
      a:=b;
      b:=swp;
    fi;
    if Distance(GraphCE,u,d)=Distance(GraphCE,u,c)-1 then
      swp:=c;
      c:=d;
      d:=swp;
    fi;
    return -Distance(GraphCE,b,d)+Distance(GraphCE,a,d)+Distance(GraphCE,b,c)-Distance(GraphCE,a,c);
  end;


  ET:=SpanningTreeGraph(GraphCE, 1);
  Print("Spanning tree computed, ", Length(ET), "  edges\n");
  Aspec:=NullGraph(Group(()), Length(ET));
  for iEdge in [1..Length(ET)-1]
    do
    for jEdge in [iEdge+1..Length(ET)]
    do
      eDist:=EdgeDist(ET[iEdge], ET[jEdge], 1);
      if eDist=2 then
        AddEdgeOrbit(Aspec, [iEdge, jEdge]);
        AddEdgeOrbit(Aspec, [jEdge, iEdge]);
      fi;
    od;
  od;
  Print("Graph of eDist=2 computed\n");
  Cspec:=ConnectedComponents(Aspec);
  Print("Connected components computed\n");
  for eElt in Cspec
  do
    if IsCompleteGraph(InducedSubgraph(Aspec, eElt))=false then
      Print("Not complete graph\n");
      return false;
    fi;
  od;
  Print("Identification of connected components finished\n");
  Dspec:=NullGraph(Group(()), Length(Cspec));
  for iVert in [1..Length(Cspec)-1]
  do
    for jVert in [iVert+1..Length(Cspec)]
    do
      eEdge1:=ET[Cspec[iVert][1]];
      eEdge2:=ET[Cspec[jVert][1]];
      eDist:=EdgeDist(eEdge1, eEdge2, 1);
      for iElt in [1..Length(Cspec[iVert])]
      do
        for jElt in [1..Length(Cspec[jVert])]
        do
          eEdge1:=ET[Cspec[iVert][iElt]];
          eEdge2:=ET[Cspec[jVert][jElt]];
          eDist2:=EdgeDist(eEdge1, eEdge2, 1);
          if eDist2<>eDist then
            Print("No coherence in the values\n");
            return false;
          fi;
        od;
      od;
      if eDist=1 then
        AddEdgeOrbit(Dspec, [iVert, jVert]);
        AddEdgeOrbit(Dspec, [jVert, iVert]);
      fi;
    od;
  od;
  INVER:=InverseLineGraph(Dspec);
  Print("Inverse line graph computed\n");
#  Print("INVER=", INVER, "\n");
  if INVER=false then
    Print("Not a line graph\n");
    return false;
  fi;
  ListLabel:=[];
  for iCspec in [1..Length(Cspec)]
  do
    for eElt in Cspec[iCspec]
    do
      ListLabel[eElt]:=ShallowCopy(INVER[2][iCspec]);
    od;
  od;
  return CreateEmbedding(1, ET, ListLabel);
end;


CPP_S_Embedding:=function(GRA, s, MaxIter)
  local FileGraph, FileEmbed, FileErr, TheCommand, ListRecEmbed;
  FileGraph:=Filename(POLYHEDRAL_tmpdir,"GRAPH.cpp");
  FileEmbed:=Filename(POLYHEDRAL_tmpdir,"GRAPH.embed");
  FileErr:=Filename(POLYHEDRAL_tmpdir,"GRAPH.err");
  RemoveFileIfExist(FileGraph);
  RemoveFileIfExist(FileEmbed);
  RemoveFileIfExist(FileErr);
  PrintGraphCppPolyhedral(FileGraph, GRA);
  TheCommand:=Concatenation(FileEnumerateSEmbedding, " ", FileGraph, " ", String(s), " ", String(MaxIter), " ", FileEmbed, " 2> ", FileErr);
#  Print("TheCommand=", TheCommand);
  Exec(TheCommand);
  #
  ListRecEmbed:=ReadAsFunction(FileEmbed)();
  RemoveFileIfExist(FileGraph);
  RemoveFileIfExist(FileEmbed);
  RemoveFileIfExist(FileErr);
  return ListRecEmbed;
end;


S_Embedding:=function(GraphCE, s)
  local M, DiamGraph, test, iCon, jCon, iCS, jCS, iElt, jElt, iEdge, jEdge, Embed, dimension, U, iCol, n, Pair, Pos, ConSet, ConSetSec, ConSetMerge, Edge, iDia, Lay, INVER, ListEdge, MCEU, MCES, MCE, A, B, C,  DO2, iDO2, DO, iDO, BadTry, Choice, iChoice, rep, Admissible, iAdmissible, SelectedType, h, k, Embedding, d, EdgeDist, eConSet, nb, CP, CliqueS, Gra, S, eCliq, a, b, c, CliqueSearch, W, SUV, FourCliqueS, eVert, NbUnsolved, NbPrev, eC, GraNull, ThreeCliques, TU, Arr, CurrentInMCE, NewMCE, SEpos, PU, wVert, US, NewConSet, val, val2, iVert, jVert, eComb, PK, ListUnsettled, FuncSetting1, FuncSetting2, FuncSetting3, FuncNextInMCE, ET, iPos, jPos, Aspec, Cspec, Dspec, iCspec, eElt, VEC1, VEC2, eEdge1, eEdge2, ListLabel;
  if IsSimpleGraph(GraphCE)=false then
    Print("The graph should be simple");
    return false;
  fi;
  if IsConnectedGraph(GraphCE)=false then
    Print("The graph should be connected");
    return false;
  fi;
  Print("****Start treating ", s, "-embedding\n");
  ListEdge:=[];
  n:=GraphCE.order;
  for iElt in [1..n-1]
  do
    for jElt in [iElt+1..n]
    do
      if iElt<>jElt and IsEdge(GraphCE,[iElt,jElt])=true then
        Add(ListEdge, [iElt,jElt]);
      fi;
    od;
  od;
  M:=ShortestPathDistanceMatrix(GraphCE);
  EdgeDist:=function(x,y) # the function i(x,y)
    local a,b,c,d,u, swp;
    a:=x[1]; b:=x[2];
    c:=y[1]; d:=y[2];
# ADD CHECK OF PAIRWISE DISTANCE OF TWO PATHS
    if not(M[a][c]<=s and M[a][d]<=s and M[b][c]<=s and M[b][d]<=s) then
      Print("Error by distance\n");
      return fail;
    fi;
    for u in [1..n]
    do
      if AbsInt(M[a][u]-M[b][u])=1 and AbsInt(M[c][u]-M[d][u])=1 and M[a][u]<=s and M[b][u]<=s and M[c][u]<=s and M[d][u]<=s then
        if M[u][b]=M[u][a]-1 then
          swp:=a;
          a:=b;
          b:=swp;
        fi;
        if M[u][d]=M[u][c]-1 then
          swp:=c;
          c:=d;
          d:=swp;
        fi;
        return -M[b][d]+M[a][d]+M[b][c]-M[a][c];
      fi;
    od;
    return fail;
  end;
  ConSet:=[];
  for iEdge in [1..Length(ListEdge)]
  do
    ConSet[iEdge]:=[iEdge];
  od;
  # Build consistency sets
  MCE:=NullMat(Length(ListEdge), Length(ListEdge));
  NbPrev:=0;
  NbUnsolved:=0;
  for iEdge in [1..Length(ListEdge)-1]
  do
    for jEdge in [iEdge+1..Length(ListEdge)]
    do
      val:=EdgeDist(ListEdge[iEdge],ListEdge[jEdge]);
      if val=fail then 
        val:=[0,1,2];
        NbUnsolved:=NbUnsolved+2;
      else
        val:=[val];
      fi;
      MCE[iEdge][jEdge]:=val;
      MCE[jEdge][iEdge]:=val;
      NbPrev:=NbPrev+2;
    od;
  od;
  Print("NbUnsolved=", NbUnsolved, "\n");
  Print("NbPrev    =", NbPrev, "\n");
  if NbPrev=NbUnsolved then
    Print("Nothing computable\n");
    return false;
  fi;
  DiamGraph:=Diameter(GraphCE);
  if DiamGraph=s then
    ET:=SpanningTreeGraph(GraphCE, 1);
    Aspec:=NullGraph(Group(()), Length(ET));
    for iEdge in [1..Length(ET)-1]
    do
      for jEdge in [iEdge+1..Length(ET)]
      do
        iPos:=Position(ListEdge, ET[iEdge]);
        jPos:=Position(ListEdge, ET[jEdge]);
        if MCE[iPos][jPos]=[2] then
          AddEdgeOrbit(Aspec, [iEdge, jEdge]);
          AddEdgeOrbit(Aspec, [jEdge, iEdge]);
        fi;
      od;
    od;
    Cspec:=ConnectedComponents(Aspec);
    for eElt in Cspec
    do
      if IsCompleteGraph(InducedSubgraph(Aspec, eElt))=false then
        Print("Not complete graph\n");
        return false;
      fi;
    od;
    Dspec:=NullGraph(Group(()), Length(Cspec));
    for iVert in [1..Length(Cspec)-1]
    do
      for jVert in [iVert+1..Length(Cspec)]
      do
        eEdge1:=ET[Cspec[iVert][1]];
        eEdge2:=ET[Cspec[jVert][1]];
        val:=MCE[Position(ListEdge, eEdge1)][Position(ListEdge, eEdge2)];
        for iElt in [1..Length(Cspec[iVert])]
        do
          for jElt in [1..Length(Cspec[jVert])]
          do
            eEdge1:=ET[Cspec[iVert][iElt]];
            eEdge2:=ET[Cspec[jVert][jElt]];
            val2:=MCE[Position(ListEdge, eEdge1)][Position(ListEdge, eEdge2)];
            if val2<>val then
              Print("No coherence in the values\n");
              return false;
            fi;
          od;
        od;
        if val=[1] then
          AddEdgeOrbit(Dspec, [iVert, jVert]);
          AddEdgeOrbit(Dspec, [jVert, iVert]);
        fi;
      od;
    od;
    INVER:=InverseLineGraph(Dspec);
    if INVER=false then
      Print("Not a line graph\n");
      return false;
    fi;
    ListLabel:=[];
    for iCspec in [1..Length(Cspec)]
    do
      for eElt in Cspec[iCspec]
      do
        ListLabel[eElt]:=ShallowCopy(INVER[2][iCspec]);
      od;
    od;
    Embedding:=CreateEmbedding(1, ET, ListLabel);
    for iEdge in [1..Length(ListEdge)-1]
    do
      for jEdge in [iEdge+1..Length(ListEdge)]
      do
        VEC1:=(Embedding[ListEdge[iEdge][1]]-Embedding[ListEdge[iEdge][2]]) mod 2;
        VEC2:=(Embedding[ListEdge[jEdge][1]]-Embedding[ListEdge[jEdge][2]]) mod 2;
        
        MCE[iEdge][jEdge]:=[(4-DistanceVector(VEC1, VEC2))/2];
        MCE[jEdge][iEdge]:=MCE[iEdge][jEdge];
      od;
    od;
  fi;
  #
  # the while loop that remove possibilities
  while(NbUnsolved<NbPrev)
  do
    Gra:=NullGraph(Group(()), Length(ConSet));
    for iCon in [1..Length(ConSet)-1]
    do
      for jCon in [iCon+1..Length(ConSet)]
      do
        if MCE[iCon][jCon]=[1] then
          AddEdgeOrbit(Gra, [iCon,jCon]);
          AddEdgeOrbit(Gra, [jCon,iCon]);
        fi;
      od;
    od;
    #
    ListUnsettled:=[];
    for iVert in [1..Length(ConSet)]
    do
      ListUnsettled[iVert]:=[];
      for jVert in Difference([1..Length(ConSet)], [iVert])
      do
        if Length(MCE[iVert][jVert])>1 then
          Add(ListUnsettled[iVert], jVert);
        fi;
      od;
    od;
    # In FuncSetting1 we have
    # MCE[a,b]=[0], MCE[a,w]
    FuncSetting1:=function(a,wVert)
      local b;
      for b in Adjacency(Gra, wVert)
      do
        if MCE[a][b]=[0] then
          MCE[a][wVert]:=Difference(MCE[a][wVert], [2]);
          MCE[wVert][a]:=MCE[a][wVert];
          return;
        fi;
      od;
    end;
    FuncSetting2:=function(a,wVert)
      local S, b, c;
      for S in Combinations(Adjacency(Gra, wVert), 2)
      do
        b:=S[1];
        c:=S[2];
        if MCE[b][c]=[0] and MCE[a][c]=[0] and MCE[b][c]=[0] then
          MCE[a][wVert]:=[0];
          MCE[wVert][a]:=[0];
          return;
        fi;
      od;
    end;
    FuncSetting3:=function(a, wVert)
      local S, TU, b, c, d;
      for S in Combinations(Adjacency(Gra, a), 3)
      do
        if MCE[S[1]][S[2]]=[1] and MCE[S[1]][S[3]]=[1] and MCE[S[2]][S[3]]=[1] then
          for TU in [[1,2,3],[2,3,1],[3,1,2]]
          do
            b:=S[TU[1]];
            c:=S[TU[2]];
            d:=S[TU[3]];
            if MCE[b][wVert]=[1] and MCE[b][wVert]=[1] and MCE[b][wVert]=[1] then
              MCE[a][wVert]:=Difference(MCE[a][wVert], [0]);
              MCE[wVert][a]:=MCE[a][wVert];
            fi;
            if MCE[b][wVert]=[0] and MCE[b][wVert]=[1] and MCE[b][wVert]=[1] then
              MCE[a][wVert]:=[0];
              MCE[wVert][a]:=MCE[a][wVert];
              return;
            fi;
          od;
        fi;
      od;
    end;
    for a in [1..Length(ConSet)]
    do
      for wVert in ListUnsettled[a]
      do
        FuncSetting1(a, wVert);
        FuncSetting2(a, wVert);
        FuncSetting3(a, wVert);
      od;
    od;

    CliqueSearch:=false;
    if CliqueSearch=true then
      ThreeCliques:=CompleteSubgraphsOfGivenSize(Gra, 3);
      Print("NBR ThreeCliques=", Length(ThreeCliques), "\n");
      for eCliq in ThreeCliques
      do
        for TU in [[1,2,3],[2,3,1],[3,1,2]]
        do
            a:=eCliq[TU[1]];
            b:=eCliq[TU[2]];
            c:=eCliq[TU[3]];
            for d in Difference([1..Length(ConSet)],eCliq)
            do
              if MCE[a][d]=[1] and MCE[b][d]=[1] and MCE[c][d]=[0] then
                for wVert in Difference([1..Length(ConSet)],Union(eCliq, [d]))
                do
                  if MCE[a][wVert]=[1] and MCE[b][wVert]=[1] and MCE[c][wVert]=[0] then
                    MCE[d][wVert]:=Difference(MCE[d][wVert], [0]);
                    MCE[wVert][d]:=MCE[d][wVert];
                  fi;
                  if MCE[c][wVert]=[0] and MCE[d][wVert]=[0] then
                    MCE[a][wVert]:=[0];
                    MCE[b][wVert]:=[0];
                    MCE[wVert][a]:=[0];
                    MCE[wVert][b]:=[0];
                  fi;
                od;
              fi;
            od;
        od;
      od;
    fi;
    #
    #
    A := Graph(Group(()), [1..Length(ConSet)], OnPoints, function(x,y) return MCE[x][y]=[2]; end, true);
    ConSetSec:=ConnectedComponents(A);
    NewMCE:=NullMat(Length(ConSetSec), Length(ConSetSec));
    NewConSet:=[];
    for iCon in [1..Length(ConSetSec)]
    do
      NewConSet[iCon]:=[];
      for iCS in ConSetSec[iCon]
      do
        NewConSet[iCon]:=Union(NewConSet[iCon], ConSet[iCS]);
      od;
    od;
    for iCon in [1..Length(ConSetSec)-1]
    do
      for jCon in [iCon+1..Length(ConSetSec)]
      do
        US:=[0,1,2];
        for iCS in ConSetSec[iCon]
        do
            for jCS in ConSetSec[jCon]
            do
              US:=Intersection(US, MCE[iCS][jCS]);
            od;
        od;
        if US=[] then
          Print("The distance has to assume incoherent different values\n");
          return false;
        fi;
        NewMCE[iCon][jCon]:=US;
        NewMCE[jCon][iCon]:=US;
      od;
    od;
    ConSet:=NewConSet;
    MCE:=NewMCE;

    # set things for a new run
    NbPrev:=NbUnsolved;
    NbUnsolved:=0;
    for iCon in [1..Length(ConSet)-1]
    do
      for jCon in [iCon+1..Length(ConSet)]
      do
        if Length(MCE[iCon][jCon])>1 then
          NbUnsolved:=NbUnsolved+Length(MCE[iCon][jCon])-1;
        fi;
      od;
    od;
  od;
  # brutal enumeration of remaining cases
  #
  #

  CurrentInMCE:=NullMat(Length(ConSet),Length(ConSet));
  for iCon in [1..Length(ConSet)-1]
  do
    for jCon in [iCon+1..Length(ConSet)]
    do
      CurrentInMCE[iCon][jCon]:=MCE[iCon][jCon][1];
      CurrentInMCE[jCon][iCon]:=CurrentInMCE[iCon][jCon];
    od;
  od;


  FuncNextInMCE:=function(Mat)
    local Wor, LPW, eLPW, iConSP, jConSP, Pos;
    Wor:=Mat;
    LPW:=[];
    for iConSP in [1..Length(ConSet)-1]
    do
      for jConSP in [iConSP+1..Length(ConSet)]
      do
        Pos:=Position(MCE[iConSP][jConSP], Wor[iConSP][jConSP]);
        if Pos<Length(MCE[iConSP][jConSP]) then
          for eLPW in LPW
          do
            Wor[eLPW[1]][eLPW[2]]:=MCE[eLPW[1]][eLPW[2]][1];
            Wor[eLPW[2]][eLPW[1]]:=MCE[eLPW[2]][eLPW[1]][1];
          od;
          Wor[iConSP][jConSP]:=MCE[iConSP][jConSP][Pos+1];
          Wor[jConSP][iConSP]:=MCE[iConSP][jConSP][Pos+1];
          return Wor;
        fi;
        LPW[Length(LPW)+1]:=[iConSP,jConSP];
      od;
    od;
    return "last";
  end;
  #
  Embedding:=[];
  while(true)
  do
    B := Graph(Group(()), [1..Length(ConSet)], OnPoints, function(x,y) return CurrentInMCE[x][y]=2; end, true);
    ConSetSec:=ConnectedComponents(B);
    # recomputation of the matrix
    MCES:=NullMat(Length(ConSetSec), Length(ConSetSec));
    BadTry:=0;
    for iCon in [1..Length(ConSetSec)-1]
    do
      for jCon in [iCon+1..Length(ConSetSec)]
      do
        SEpos:=[];
        for iCS in [1..Length(ConSetSec[iCon])]
        do
          for jCS in [1..Length(ConSetSec[jCon])]
          do
            AddSet(SEpos, CurrentInMCE[ConSetSec[iCon][iCS]][ConSetSec[jCon][jCS]]);
          od;
        od;
        if Length(SEpos)>1 then
          BadTry:=1;
        fi;
        MCES[iCon][jCon]:=SEpos[1];
        MCES[jCon][iCon]:=SEpos[1];
      od;
    od;
    #  reconstruction of edge set
    ConSetMerge:=[];
    for iCon in [1..Length(ConSetSec)]
    do
      ConSetMerge[iCon]:=Set([]);
      for jCon in ConSetSec[iCon]
      do
        ConSetMerge[iCon]:=Union(ConSetMerge[iCon], ConSet[jCon]);
      od;
    od;
#    Print("Number Connected Components=",Length(ConSetMerge),"\n");


    if BadTry=0 then
      C := Graph(Group(()), [1..Length(ConSetSec)], OnPoints, function(x,y) return MCES[x][y]=1; end, true);
      INVER:=InverseLineGraph(C);
#      Print("LineGraph=", C, "\n");
#      Print("Inverseline graph=", INVER, "\n");
      if INVER<>false then
        # embedding building
        ListLabel:=[];
        for iCon in [1..Length(ConSetMerge)]
        do
          for eElt in ConSetMerge[iCon]
          do
            ListLabel[eElt]:=INVER[2][iCon];
          od;
        od;
        Embed:=CreateEmbedding(1, ListEdge, ListLabel);
        if CheckSembedding(M, s, Embed)=true then
          Add(Embedding, Embed);
        fi;
      fi;
    fi;
    PU:=FuncNextInMCE(CurrentInMCE);
    if PU="last" then
      break;
    else
      CurrentInMCE:=PU;
    fi;
  od;
  if Length(Embedding)=0 then
    Print("No embedding found\n");
    return false;
  else
    return Embedding;
  fi;
end;





       
# checking whether the graph G is a subgraph of a cocktail
# party graph
#
IsSubCocktail:=function(G)
  local degs;
  degs:=VertexDegrees(G);
  if Minimum(degs)<G.order-2 then
    return false;
  fi;
  return true;
end;


# every conn. component of A - complete graph
#                            - ind. subgraph of a cocktail party graph
#                            - the edge graph of a graph            
DetComps:=function(A)
  local C, c, X, t, r;
  r:=[];
  C:=ConnectedComponents(A);
  for c in C
  do
    X:=InducedSubgraph(A,c);
    t:=0;
    if IsCompleteGraph(X) then
      t:=1;
    elif IsSubCocktail(X) then 
      t:=2;
    elif false<>InverseLineGraph(X) then 
      t:=3;
    fi;
    if t=0 then
      return false;
    fi;
    Add(r,[c,t]);
  od;
  return r;
end;

           
#######################################################################    
    
#IsL1Emb:=function(G)
#    local A,T,Comp;
#    
#    if not IsSimpleGraph(G) then 
#        Print("\n Error: G must be a simple graph\n");
#        return false;
#    fi;
#    
#    if not IsConnectedGraph(G) then 
#      return false; 
#    fi;
#    A:=AtomGraph(G);
#    if false=A then # suceeded in constructing A?
#      Print("Unable to construct atom graph\n");
#      return false; 
#    fi;  
#    T:=A.tree;
#    A:=A.atomgraph;
#    Comp:=DetComps(A);
#    if false=Comp then # wrong components of A
#      Print("Wrong components of atom graph\n");
#      return false; 
#    fi; 
#    
#    return true;
#    
#end;
















# every conn. component of A - complete graph
#                            - ind. subgraph of a cocktail party graph
#                            - the edge graph of a graph            
RigidComps:=function(A)
  local C,c,X,t,r;
  r:=[];
  C:=ConnectedComponents(A);
  for c in C
  do
    X:=InducedSubgraph(A,c);
    t:=0;
    if IsCompleteGraph(X) then 
      t:=1; 
      if X.order>2 then
        return false;
      fi;
    elif IsSubCocktail(X) then 
      t:=2;
      if X.order-EdgeGraph(ComplementGraph(X)).order>2 then
        return false;
      fi;
    elif false<>InverseLineGraph(X) then 
      t:=3;
    fi;
    if t=0 then
      return false;
    fi;
    Add(r,[c,t]);
  od;
  return r;
end;

           
#######################################################################    
    
#IsRigidL1:=function(G)
#    local A,T,Comp;
#    if not IsSimpleGraph(G) then 
#        Print("\n Error: G must be a simple graph\n");
#        return false;
#    fi;
#    
#    if not IsConnectedGraph(G) then return false; fi;
#    A:=AtomGraph(G);
#    if false=A then return false; fi;  # suceeded in constructing A?
#    T:=A.tree;
#    A:=A.atomgraph;
#    Comp:=RigidComps(A);
#    if false=Comp then return false; fi; # wrong components of A
#    return true;
#end;



Shelling5gonal:=function(GRA, nbite)
  local iter, VSET, ListVert, h, DistMat, i, j, d, Sum, eSet, fSet;
  for iter in [1..nbite]
  do
    VSET:=[1..GRA.order];
    ListVert:=[];
    for i in [1..5]
    do
      h:=Random(VSET);
      Add(ListVert, h);
      RemoveSet(VSET, h);
    od;
    DistMat:=NullMat(5,5);
    for i in [1..4]
    do
      for j in [i+1..5]
      do
        d:=Distance(GRA, ListVert[i], ListVert[j]);
        DistMat[i][j]:=d;
        DistMat[j][i]:=d;
      od;
    od;
    for eSet in Combinations([1..5],2)
    do
      Sum:=0;
      fSet:=Difference([1..5],eSet);
      Sum:=Sum+DistMat[eSet[1]][eSet[2]];

      Sum:=Sum+DistMat[fSet[1]][fSet[2]];
      Sum:=Sum+DistMat[fSet[1]][fSet[3]];
      Sum:=Sum+DistMat[fSet[2]][fSet[3]];

      Sum:=Sum-DistMat[fSet[1]][eSet[1]];
      Sum:=Sum-DistMat[fSet[2]][eSet[1]];
      Sum:=Sum-DistMat[fSet[3]][eSet[1]];
      Sum:=Sum-DistMat[fSet[1]][eSet[2]];
      Sum:=Sum-DistMat[fSet[2]][eSet[2]];
      Sum:=Sum-DistMat[fSet[3]][eSet[2]];
      if Sum > 0 then
        return [ListVert{eSet}, ListVert{fSet}];
      fi;
    od;
  od;
  return "unknown";
end;


Check5gonalInequalityOnSet:=function(DistMat, TestSet)
  local rSetE, Sum, rSetF, eSet, fSet;
  for rSetE in Combinations([1..5],2)
  do
    Sum:=0;
    rSetF:=Difference([1..5],rSetE);
    eSet:=TestSet{rSetE};
    fSet:=TestSet{rSetF};
    #
    Sum:=Sum+DistMat[eSet[1]][eSet[2]];
    #
    Sum:=Sum+DistMat[fSet[1]][fSet[2]];
    Sum:=Sum+DistMat[fSet[1]][fSet[3]];
    Sum:=Sum+DistMat[fSet[2]][fSet[3]];
    #
    Sum:=Sum-DistMat[fSet[1]][eSet[1]];
    Sum:=Sum-DistMat[fSet[2]][eSet[1]];
    Sum:=Sum-DistMat[fSet[3]][eSet[1]];
    Sum:=Sum-DistMat[fSet[1]][eSet[2]];
    Sum:=Sum-DistMat[fSet[2]][eSet[2]];
    Sum:=Sum-DistMat[fSet[3]][eSet[2]];
    if Sum > 0 then
      return rec(answer:=false, eSet:=eSet, fSet:=fSet);
    fi;
  od;
  return rec(answer:=true);
end;




CheckAll5gonalInequalities:=function(DistMat, GRP)
  local n, k, ListKset, TestSet, eRecTest;
  n:=Length(DistMat);
  k:=5;
  ListKset:=Enumerate_Ksets(n, GRP, k);
  for TestSet in ListKset
  do
    eRecTest:=Check5gonalInequalityOnSet(DistMat, TestSet);
    if eRecTest.answer=false then
      return eRecTest;
    fi;
  od;
  return rec(answer:=true);
end;
