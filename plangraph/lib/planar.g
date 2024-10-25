# this procedure will create the list of faces with an orientation
# 
# a planar graph is represented as a sequence
# A:=[[1,2,3], [....], ...]
# with A[i] being the list of adjacent vertex in direct order 
# (multiple occurence are autorized, and a change of order is possible)
# to work with adjacencies, faces and the like, we use the notion of directed
# edge: a beginning and an end
# three operations are possible for a directed edge:
# Reverse: exchange begin and end
# Next: go to the next directed edge with same beginning
# Prev: go to the previous directed edge with same beginning
# 
# We assume no edge is multiply connected to just one edge 
# 
# 

# the procedure here written works only for graphs with one edge
# but can be completed to handle multiple edges.
ReverseDE:=function(PlanGraph, DirEdge)
  local Ladj, Ladj2, AdjacentVertex, pos, pos2, nbpc, i;
  Ladj:=PlanGraph[DirEdge[1]];
  AdjacentVertex:=Ladj[DirEdge[2]];
  pos:=DirEdge[2];
  nbpc:=0;
  while(Ladj[PrevIdx(Length(Ladj), pos)]=AdjacentVertex)
  do
    pos:=PrevIdx(Length(Ladj), pos);
    nbpc:=nbpc+1;
  od;
  Ladj2:=PlanGraph[AdjacentVertex];
  pos2:=Position(Ladj2, DirEdge[1]);
  while (Ladj2[NextIdx(Length(Ladj2), pos2)]=DirEdge[1])
  do
    pos2:=NextIdx(Length(Ladj2), pos2);
  od;
  for i in [1..nbpc]
  do
    pos2:=PrevIdx(Length(Ladj2), pos2);
  od;
  return [AdjacentVertex, pos2];
end;



NextDE:=function(PlanGraph, DirEdge)
   local U;
   U:=PlanGraph[DirEdge[1]];
   if Length(U)=DirEdge[2] then
     return [DirEdge[1],1];
   else
     return [DirEdge[1],DirEdge[2]+1];
   fi;
end;


PrevDE:=function(PlanGraph, DirEdge)
   local U;
   U:=PlanGraph[DirEdge[1]];
   if 1=DirEdge[2] then
     return [DirEdge[1],Length(U)];
   else
     return [DirEdge[1],DirEdge[2]-1];
   fi;
end;

ListEdgeVertex:=function(PlanGraph, Vertex)
  local La, iVert;
  La:=[];
  for iVert in [1..Length(PlanGraph[Vertex])]
  do
    Add(La, [Vertex, iVert]);
  od;
  return La;
end;


ListDirectedEdges:=function(PlanGraph)
  local La, iVert;
  La:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    La:=Union(La, ListEdgeVertex(PlanGraph, iVert));
  od;
  return La;
end;


EdgeToDirEdge:=function(PlanGraph, Edge)
  return [Edge[1],Position(PlanGraph[Edge[1]],Edge[2])];
end;


CheckPlanGraph:=function(PlanGraph)
  local i, j, nb1, nb2;
  for i in [1..Length(PlanGraph)]
  do
    for j in Set(PlanGraph[i])
    do
      if j>i then
        nb1:=Length(Filtered(PlanGraph[i], x->x=j));
        nb2:=Length(Filtered(PlanGraph[j], x->x=i));
        if nb1<>nb2 then
          Print(" j=", j, " is ", nb1, "times in PlanGraph[", i, "]  but\n");
          Print("     i=", i, " is ", nb2, "times in PlanGraph[", j, "]\n");
        fi;
      fi;
    od;
  od;
end;


DoubleEdge:=function(PlanGraph)
  local DoubleEdges, DoubleString, iDou, iVert, jVert, n, DD;
  n:=Length(PlanGraph);
  DoubleEdges:=[];
  for iVert in [1..n-1]
  do
    for jVert in [iVert+1..n]
    do
      if PositionNthOccurrence(PlanGraph[iVert], jVert, 2)<>fail then
        Add(DoubleEdges, [iVert, jVert]);
      fi;
    od;
  od;
  DoubleString:="";
  for iDou in [1..Length(DoubleEdges)]
  do
    DD:=DoubleEdges[iDou];
    DoubleString:=Concatenation(DoubleString, "(",String(DD[1]),",",String(DD[2]),")");
    if iDou< Length(DoubleEdges) then
      DoubleString:=Concatenation(DoubleString, ", ");
    fi;
  od;
  return [DoubleEdges, DoubleString];
end;


PlanGraphToGRAPE:=function(PlanGraph)
  local n, Gra, i, u;
  n:=Length(PlanGraph);
  Gra:=NullGraph(Group(()), n);
  for i in [1..n]
  do
    for u in PlanGraph[i]
    do
      if u<>i then
        AddEdgeOrbit(Gra, [i,u]);
      fi;
    od;
  od;
  return Gra;
end;


#
#
# after some chirurgy on a PlanGraph, we return it to a normal form
Renormalisation:=function(PlanGraph)
  local VertexSet, i, NewPlanGraph, nbV, iV, NEWADJ, OLDADJ, iadj;
  VertexSet:=[];
  for i in [1..Length(PlanGraph)]
  do
    VertexSet:=Union(VertexSet, PlanGraph[i]);
  od;
  NewPlanGraph:=[];
  nbV:=Length(VertexSet);
  for iV in [1..nbV]
  do
    NEWADJ:=ShallowCopy([]);
    OLDADJ:=PlanGraph[VertexSet[iV]];
    for iadj in [1..Length(OLDADJ)]
    do
      NEWADJ[iadj]:=Position(VertexSet, OLDADJ[iadj]);
    od;
    NewPlanGraph[iV]:=NEWADJ;
  od;
  return NewPlanGraph;
end;


#
#
CreateOrderedListAdj:=function(ListOrd)
  local adjness, ListOrdAdj, iadj, PrevAdj, u;
  adjness:=Length(ListOrd);
  ListOrdAdj:=[ListOrd[1][1],ListOrd[1][2]];
  for iadj in [3..adjness]
  do
    PrevAdj:=ListOrdAdj[iadj-1];
    for u in ListOrd
    do
      if u[1]=PrevAdj then
        ListOrdAdj[iadj]:=u[2];
      fi;
    od;
  od;
  return ListOrdAdj;
end;




# Here we follow the book 
# "Introduction to Graph Theory"
# Prentice Hall, Douglas B.West p.253
Planar:=function(Ggraph)
  local iElt, eElt, iEltAdd, ListAdj, Ladj, ListFaces, TreatedVertices, i, j, iPos, Cyc1, Cyc2, Ridge, RidgeH, RidgeN, First, Second, swp, test, LFB, Fragment, Frag, Boundary, Cont, iFac, H, Bound, Unsaturated, S, d, beginning, ending, IndexSet, iB, Hcon, Matrix, SSet, eFac, LordAdj, pos, iVert, PlanGraph, eS, eCon, ipos;
  ListAdj:=[];
  for iElt in [1..Ggraph.order]
  do
    Ladj:=Adjacency(Ggraph, iElt);
    ListAdj[iElt]:=Ladj;
  od;
  # creation of the initial cycle
  Matrix:=NullMat(Ggraph.order, Ggraph.order);
  for i in [1..Ggraph.order]
  do
    for j in [1..Ggraph.order]
    do
      if IsEdge(Ggraph, [i,j])=true then
        Matrix[i][j]:=1;
      fi;
    od;
  od;
  beginning:=1;
  ending:=Adjacency(Ggraph, beginning)[1];
  Matrix[beginning][ending]:=0;
  Matrix[ending][beginning]:=0;
  H:=Graph(Group(()), [1..Ggraph.order], OnPoints, function(x,y) return Matrix[x][y]=1; end, true);
  Ridge:=ShallowCopy([]);
  Ridge[1]:=beginning;
  d:=Distance(H, beginning, ending);
  for i in [1..d]
  do
    Ridge[i+1]:=Intersection(Adjacency(H, Ridge[i]), Layers(H,ending)[d+1-i])[1];
  od;

  for i in [2..Length(Ridge)-1]
  do
    ListAdj[Ridge[i]]:=Difference(ListAdj[Ridge[i]], [Ridge[i+1], Ridge[i-1]]);
  od;
  ListAdj[Ridge[1]]:=Difference(ListAdj[Ridge[1]], [Ridge[2], Ridge[Length(Ridge)]]);
  ListAdj[Ridge[Length(Ridge)]]:=Difference(ListAdj[Ridge[Length(Ridge)]], [Ridge[1], Ridge[Length(Ridge)-1]]);
  ListFaces:=[Ridge, Reversed(Ridge)];
  TreatedVertices:=Set(Ridge);

  # adding fragment by fragment
  while(true)
  do
    test:=0;
    Unsaturated:=[];
    for iElt in [1..Ggraph.order]
    do
      if (Length(ListAdj[iElt])>0) and (iElt in TreatedVertices) then
    	test:=1;
        Add(Unsaturated, iElt);
      fi;
    od;
    if test=0 then
      break;
    fi;
    # search of ridge
    # search for the fragments of the graph
    Fragment:=[];
    LFB:=[];
    Boundary:=[];
    for eElt in Unsaturated  # first kind of Fragment
    do
      Ladj:=Intersection(ListAdj[eElt], TreatedVertices);
      for i in Ladj
      do
        Frag:=[eElt, i];
        Add(Fragment, Frag);
        Cont:=[];
        Add(Boundary, Frag); #boundary is equal to the Fragment
        # finding the set F(B) of faces containing the given Fragment
        for iFac in [1..Length(ListFaces)]
        do
          if IsSubset(Set(ListFaces[iFac]), Frag)=true then
            Add(Cont, iFac);
          fi;
        od;
        if Length(Cont)=0 then
          return false;
        fi;
        Add(LFB, Cont);
      od;
    od;
    H:=InducedSubgraph(Ggraph, Difference([1..Ggraph.order], TreatedVertices));
    Hcon:=ConnectedComponents(H);
    for eCon in Hcon
    do
      S:=[];
      for eElt in eCon
      do
        Add(S, VertexName(H, eElt));
      od;
      Add(Fragment, S);
      Bound:=[];
      for eS in S
      do
        Bound:=Union(Bound, Intersection(Adjacency(Ggraph, eS), TreatedVertices));
      od;
      Cont:=[];
      for iFac in [1..Length(ListFaces)]
      do
        if IsSubset(Set(ListFaces[iFac]), Bound)=true then
          Add(Cont, iFac);
        fi;
      od;
      if Length(Cont)=0 then
        return false;
      fi;
      Add(Boundary, ListFaces[Cont[1]]);
      Add(LFB, Cont);
    od;
    test:=0;
    for iElt in [1..Length(LFB)]
    do
      if Length(LFB[iElt])=1 and test=0 then
        test:=1;
        First:=iElt;
        iPos:=LFB[iElt][1];
      fi;
    od;
    # this case when we have several possible faces for each of the remaining
    if test=0 then
      First:=1;
      iPos:=LFB[1][1];
    fi;
    # searching the ridge

    if Boundary[First]=Fragment[First] then
      Ridge:=ShallowCopy(Boundary[First]);
    else
      SSet:=Union(Fragment[First], Boundary[First]);
      Matrix:=NullMat(Ggraph.order, Ggraph.order);
      for i in [1..Length(SSet)]
      do
        for j in [1..Length(SSet)]
        do
          if IsEdge(Ggraph, [SSet[i], SSet[j]])=true then
            Matrix[SSet[i]][SSet[j]]:=1;
          fi;
        od;
      od;
      for i in [1..Length(Boundary[First])]
      do
        for j in [1..Length(Boundary[First])]
        do
          Matrix[Boundary[First][i]][Boundary[First][j]]:=0;
        od;
      od;
      H:=Graph(Group(()), [1..Ggraph.order], OnPoints, function(x,y) return Matrix[x][y]=1; end, true);
      Ridge:=ShallowCopy([]);
      ipos:=1;
      while(true)
      do
        beginning:=Boundary[First][ipos];
        if (beginning in Unsaturated) and Intersection(Adjacency(H, beginning), Fragment[First])<>[] then
          break;
        fi;
        ipos:=ipos+1;
      od;
      ipos:=NextIdx(Length(Boundary[First]), ipos);
      while(true)
      do
        ending:=Boundary[First][ipos];
        if (ending in Unsaturated) and Intersection(Adjacency(H, ending), Fragment[First])<>[] then
          break;
        fi;
        ipos:=NextIdx(Length(Boundary[First]), ipos);
      od;
      Ridge[1]:=beginning;
      d:=Distance(H, beginning, ending);
      for i in [1..d]
      do
        Ridge[i+1]:=Intersection(Adjacency(H, Ridge[i]), Layers(H,ending)[d+1-i])[1];
      od;
    fi;
    
    TreatedVertices:=Union(TreatedVertices, Ridge);
    for iElt in [2..Length(Ridge)-1]
    do
      ListAdj[Ridge[iElt]]:=Difference(ListAdj[Ridge[iElt]], [Ridge[iElt-1], Ridge[iElt+1]]);
    od;
    ListAdj[Ridge[1]]:=Difference(ListAdj[Ridge[1]], [Ridge[2]]);
    ListAdj[Ridge[Length(Ridge)]]:=Difference(ListAdj[Ridge[Length(Ridge)]], [Ridge[Length(Ridge)-1]]);



    # updating the list of faces
    First:=Position(ListFaces[iPos], Ridge[1]);
    Second:=Position(ListFaces[iPos], Ridge[Length(Ridge)]);
    if Second<First then
      swp:=Second;
      Second:=First;
      First:=swp;
      Ridge:=ShallowCopy(Reversed(Ridge));
    fi;

    Cyc1:=ListFaces[iPos]{[First..Second-1]};
    Append(Cyc1, Reversed(Ridge{[2..Length(Ridge)]}));
    Cyc2:=Ridge{[2..Length(Ridge)-1]};
    Append(Cyc2, ListFaces[iPos]{[Second..Length(ListFaces[iPos])]});
    Append(Cyc2, ListFaces[iPos]{[1..First]});
    ListFaces:=Concatenation([Cyc1, Cyc2], ListFaces{Difference([1..Length(ListFaces)], [iPos])});
  od;
  # creation of ordered list of adjacency, using faces
  PlanGraph:=[];
  for iVert in [1..Ggraph.order]
  do
    LordAdj:=[];
    for eFac in ListFaces
    do
      if Position(eFac, iVert)<>fail then
        pos:=Position(eFac, iVert);
        Add(LordAdj, [eFac[NextIdx(Length(eFac), pos)], eFac[PrevIdx(Length(eFac), pos)]]);
      fi;
    od;
    PlanGraph[iVert]:=CreateOrderedListAdj(LordAdj);
  od;
  return rec(ListFaces:=ListFaces, PlanGraph:=PlanGraph);
end;





#
#
# this procedure handles multiple edges
#
PlanGraphToVEF:=function(PlanGraph)
  local n, EdgeSet, iV, eAdj, FaceSet, ListTot, z, Sequence, v, Face, iElt;
  n:=Length(PlanGraph);
  EdgeSet:=[];
  for iV in [1..n]
  do
    for eAdj in PlanGraph[iV]
    do
      EdgeSet:=Union(EdgeSet, [Set([iV, eAdj])] );
    od;
  od;
  FaceSet:=[];
  ListTot:=ListDirectedEdges(PlanGraph);
  while (Length(ListTot)>0)
  do
    z:=ListTot[1];
    Sequence:=ShallowCopy([z]);
    v:=PrevDE(PlanGraph, ReverseDE(PlanGraph,z));
    while (v<>z)
    do
      Add(Sequence, v);
      v:=PrevDE(PlanGraph, ReverseDE(PlanGraph,v));
    od;
    ListTot:=Difference(ListTot, Set(Sequence));
    Face:=ShallowCopy([]);
    for iElt in [1..Length(Sequence)]
    do
      Face[iElt]:=Sequence[iElt][1];
    od;
    Add(FaceSet, Face);
  od;
  return [n, EdgeSet, FaceSet];
end;






__EdgeSet:=function(PlanGraph)
  local EdgeSet, ListTot, z, Sequence;
  EdgeSet:=[];
  ListTot:=ListDirectedEdges(PlanGraph);
  while (Length(ListTot)>0)
  do
    z:=ListTot[1];
    Sequence:=Set([z, ReverseDE(PlanGraph, z)]);
    AddSet(EdgeSet, Sequence);
    ListTot:=Difference(ListTot, Set(Sequence));
  od;
  return EdgeSet;
end;



__FaceSet:=function(PlanGraph)
  local FaceSet, ListTot, z, Sequence, v;
  FaceSet:=[];
  ListTot:=ListDirectedEdges(PlanGraph);
  while (Length(ListTot)>0)
  do
    z:=ListTot[1];
    Sequence:=ShallowCopy([z]);
    v:=PrevDE(PlanGraph, ReverseDE(PlanGraph,z));
    while (v<>z)
    do
      Add(Sequence, v);
      v:=PrevDE(PlanGraph, ReverseDE(PlanGraph,v));
    od;
    ListTot:=Difference(ListTot, Set(Sequence));
    AddSet(FaceSet, Sequence);
  od;
  return FaceSet;
end;






PlanGraphToVEFsecond:=function(PlanGraph)
  return [Length(PlanGraph), __EdgeSet(PlanGraph), __FaceSet(PlanGraph)];
end;







#
#
# PlanGraph format is [invers, next, prev]
PlanGraphToVEFthird:=function(PlanGraph)
  local nbE, VertexSET, EdgeSET, FaceSET, z, v, ListTot, Sequence, eEdge;
  nbE:=Length(PlanGraph.Struct);
  VertexSET:=[];
  ListTot:=[1..nbE];
  while (Length(ListTot)>0)
  do
    z:=ListTot[1];
    Sequence:=ShallowCopy([z]);
    v:=PlanGraph.Struct[z][2];
    while (v<>z)
    do
      Add(Sequence, v);
      v:=PlanGraph.Struct[v][2];
    od;
    ListTot:=Difference(ListTot, Set(Sequence));
    AddSet(VertexSET, Sequence);
  od;
  EdgeSET:=[];
  ListTot:=[1..nbE];
  while (Length(ListTot)>0)
  do
    z:=ListTot[1];
    eEdge:=[z, PlanGraph.Struct[z][1]];
    ListTot:=Difference(ListTot, Set(eEdge));
    AddSet(EdgeSET, eEdge);
  od;
  FaceSET:=[];
  ListTot:=[1..nbE];
  while (Length(ListTot)>0)
  do
    z:=ListTot[1];
    Sequence:=ShallowCopy([z]);
    v:=PlanGraph.Struct[PlanGraph.Struct[z][1]][3];
    while (v<>z)
    do
      Add(Sequence, v);
      v:=PlanGraph.Struct[PlanGraph.Struct[v][1]][3];
    od;
    ListTot:=Difference(ListTot, Set(Sequence));
    AddSet(FaceSET, Sequence);
  od;
  return rec(VertexSet:=VertexSET, EdgeSet:=EdgeSET, FaceSet:=FaceSET);
end;


VEFtoPlanGraph:=function(VEF)
  local nbV, Edges, Faces, ListCyclic, i, Ladj, eEdge, ListPair, eFace, fFace, Cyc, u, fo, ePair, ListOrd, j, ESL, testF, isec, jsec, pos1, pos2, INTU;
  nbV:=VEF[1];
  Edges:=VEF[2];
  Faces:=VEF[3];
  ListCyclic:=[];
  for i in [1..nbV]
  do
    Ladj:=[];
    for eEdge in Edges
    do
      if i in eEdge then
        AddSet(Ladj, Difference(eEdge, [i])[1]);
      fi;
    od;
    ListPair:=[];
    for eFace in Faces
    do
      fFace:=Set(eFace);
      if i in fFace then
        AddSet(ListPair, Intersection(fFace, Ladj));
      fi;
    od;
    if Length(ListPair)=1 then
      Add(ListCyclic, ListPair[1]);
    else
      Cyc:=[ListPair[1][1]];
      RemoveSet(ListPair, ListPair[1]);
      for u in [1..Length(Ladj)-1]
      do
        fo:=-1;
        for ePair in ListPair
        do
          if Cyc[u] in ePair then
           fo:=ePair;
          fi;
        od;
        RemoveSet(ListPair, fo);
        Add(Cyc, Difference(ePair, [Cyc[u]])[1]);
      od;
      Add(ListCyclic, Cyc);
    fi;
  od;
  ListOrd:=[1];
  while(Length(ListOrd)<nbV)
  do
    for i in Difference([1..nbV], ListOrd)
    do
      INTU:=Intersection(Set(ListCyclic[i]), ListOrd);
      if Length(INTU)>0 then
        j:=INTU[1];
        pos1:=Position(ListCyclic[i], j);
        pos2:=Position(ListCyclic[j], i);
        jsec:=ListCyclic[i][PrevIdx(Length(ListCyclic[i]), pos1)];
        isec:=ListCyclic[j][NextIdx(Length(ListCyclic[j]), pos2)];
        ESL:=Set([i, j, isec, jsec]);
        testF:=false;
        for eFace in Faces
        do
          if IsSubset(Set(eFace), ESL)=true then
            testF:=true;
          fi;
        od;
        if testF=false then
          ListCyclic[i]:=Reversed(ListCyclic[i]);
        fi;
        AddSet(ListOrd, i);
      fi;
    od;
  od;
  return ListCyclic;
end;




Pvector:=function(VEF)
  local Faces, VEC, Occ, Pvec, eFac, i, eOcc, VV, eV;
  Faces:=VEF[3];
  VEC:=[];
  for eFac in Faces
  do
    Add(VEC, Length(eFac));
  od;
  Occ:=Collected(VEC);
  eV:=Set(VEC);
  VV:=[];
  for i in [1..Maximum(eV)]
  do
    VV[i]:=0;
  od;
  for eOcc in Occ
  do
    VV[eOcc[1]]:=eOcc[2];
  od;
#  Pvec:="";
#  for i in [1..Maximum(eV)]
#  do
#    Pvec:=Concatenation(Pvec,String(VV[i]));
#    if i<Maximum(eV) then
#      Pvec:=Concatenation(Pvec,",");
#    fi;
#  od;
  return rec(SString:=SyncTextOccurrence(Occ), Pvector:=VV);
end;

InvariantOfPlanGraph:=function(PlanGraph)
  local VEF, PV, VV, VEC, eVert, Occ, eV, eOcc, i;
  VEF:=PlanGraphToVEFsecond(PlanGraph);
  PV:=Pvector(VEF).Pvector;
  VEC:=[];
  for eVert in PlanGraph
  do
    Add(VEC, Length(eVert));
  od;
  Occ:=Collected(VEC);
  eV:=Set(VEC);
  VV:=[];
  for i in [1..Maximum(eV)]
  do
    VV[i]:=0;
  od;
  for eOcc in Occ
  do
    VV[eOcc[1]]:=eOcc[2];
  od;
  return [PV, VV];
end;











#
# SymGrp should be fixpoint free
PlanGraphQuotientedToHasseList:=function(PlanGraph, SymGrp)
  local VEF, ListVert, i, NewListVert, nbV, NewListEdge, nbE, ListFace, eFace, NewListFace, HasseList, iVert, iEdge, testF, eV, iFace, nbF;
  VEF:=PlanGraphToVEF(PlanGraph);
  ListVert:=[];
  for i in [1..VEF[1]]
  do
    Add(ListVert, [i]);
  od;
  NewListVert:=Orbits(SymGrp, ListVert, OnSets);
  nbV:=Length(NewListVert);
  NewListEdge:=Orbits(SymGrp, VEF[2], OnSets);
  nbE:=Length(NewListEdge);
  ListFace:=[];
  for eFace in VEF[3]
  do
    AddSet(ListFace, Set(eFace));
  od;
  NewListFace:=Orbits(SymGrp, ListFace, OnSets);
  nbF:=Length(NewListFace);
  HasseList:=[];
  for iVert in [1..nbV]
  do
    for iEdge in [1..nbE]
    do
      testF:=false;
      for eV in NewListEdge[iEdge]
      do
        if IsSubset(eV, NewListVert[iVert][1])=true then
          testF:=true;
        fi;
      od;
      if testF=true then
        Add(HasseList, [iVert, nbV+iEdge]);
      fi;
    od;
  od;
  for iEdge in [1..nbE]
  do
    for iFace in [1..nbF]
    do
      testF:=false;
      for eV in NewListFace[iFace]
      do
        if IsSubset(eV, NewListEdge[iEdge][1])=true then
          testF:=true;
        fi;
      od;
      if testF=true then
        Add(HasseList, [iEdge+nbV, iFace+nbV+nbE]);
      fi;
    od;
  od;
  return rec(ReducedHasseList:=HasseList, Fvector:=[nbV, nbE, nbF]);
end;







#
#
# maps formats: 
# --VEF: Vertex, Edge, Faces. A sequence [n, EDGE, FACE]
# with n the number of vertices, EDGE the list of edges in format [x,y]
# and faces the list of faces in format [x1, ..., xp] with xi adjacent to 
# xi+1 works for oriented or nonoriented maps.
# --GEM: Graph Encoded Maps a la S.Lins, a edge colored graph suited for Zig
# Zag and duality. Works for oriented or nonoriented maps.
# Every colored edge is given as [[x,y],col] where col can be either 
# "v", "f", "a" or "z".
# --PlanGraph: every vertex is given with the list of adjacent vertices 
# in clockwise order. Works only for oriented maps and it autorize multiple
# edges.




#
#
# a graph in oriented (directed edge formalism) is formed by
# two permutation "invers" and "next" acting on "nbP" directed edges
DualGraphOriented:=function(PLori)
  return rec(invers:=PLori.invers, next:=PLori.next*PLori.invers, nbP:=PLori.nbP);
end;


PlanGraphToPlanGraphOriented:=function(PlanGraph)
  local LDE, ListInvers, ListNext, iDE, IDE, NDE, MapDEvert, MapVertDE, iVert, iAdj, nb, nbAdj, eSet;
  LDE:=[];
  MapDEvert:=[];
  MapVertDE:=[];
  nb:=0;
  for iVert in [1..Length(PlanGraph)]
  do
    nbAdj:=Length(PlanGraph[iVert]);
    for iAdj in [1..nbAdj]
    do
      Add(LDE, [iVert, iAdj]);
      Add(MapDEvert, iVert);
    od;
    eSet:=[nb+1..nb+nbAdj];
    Add(MapVertDE, eSet);
    nb:=nb+nbAdj;
  od;
  ListInvers:=[];
  ListNext:=[];
  for iDE in [1..Length(LDE)]
  do
    IDE:=ReverseDE(PlanGraph, LDE[iDE]);
    NDE:=NextDE(PlanGraph, LDE[iDE]);
    ListInvers[iDE]:=Position(LDE, IDE);
    ListNext[iDE]:=Position(LDE, NDE);
  od;
  return rec(invers:=PermList(ListInvers),
             next:=PermList(ListNext),
             nbP:=Length(LDE),
             MapDEvert:=MapDEvert,
             MapVertDE:=MapVertDE);
end;


PrintNbVertNbEdge:=function(ePL)
  local nbVert, nbDoubl, eLAdj;
  nbVert:=Length(ePL);
  nbDoubl:=0;
  for eLAdj in ePL
  do
    nbDoubl:=nbDoubl + Length(eLAdj);
  od;
  return rec(nbVert:=nbVert, nbEdge:=nbDoubl/2);
end;


PLori_VEFori_toPlanGraph:=function(PLori,VEFori)
  local PL, nbVert, eVert, Ladj, iDE, rDE, fVert;
  PL:=[];
  for eVert in VEFori.VertSet
  do
    Ladj:=[];
    for iDE in eVert
    do
      rDE:=OnPoints(iDE, PLori.invers);
      fVert:=VEFori.ListOriginVert[rDE];
      Add(Ladj, fVert);
    od;
    Add(PL, Ladj);
  od;
  return PL;
end;



PlanGraphOrientedToPlanGraph:=function(PLori)
  local LDE, O, NewPlanGraph, iVert, Ladj, iAdj, rDE, pos, jOrb;
  LDE:=[1..PLori.nbP];
  O:=Orbits(Group([PLori.next]), LDE, OnPoints);
  NewPlanGraph:=[];
  for iVert in [1..Length(O)]
  do
    Ladj:=[];
    for iAdj in [1..Length(O[iVert])]
    do
      rDE:=OnPoints(O[iVert][iAdj], PLori.invers);
      pos:=-1;
      for jOrb in [1..Length(O)]
      do
        if rDE in O[jOrb] then
          pos:=jOrb;
        fi;
      od;
      Add(Ladj, pos);
    od;
    Add(NewPlanGraph, Ladj);
  od;
  return NewPlanGraph;
end;

PlanGraphOrientedToGRAPE:=function(PLori)
  local PL;
  PL:=PlanGraphOrientedToPlanGraph(PLori);
  return PlanGraphToGRAPE(PL);
end;


GetPlanGraphMultipleEdges:=function(PL)
  local nbVert, ListMultipleEdges, iVert, len, i, j, jVert, jVert2, eEdgeMultiple;
  nbVert:=Length(PL);
  ListMultipleEdges:=[];
  for iVert in [1..nbVert]
  do
    len:=Length(PL[iVert]);
    for i in [1..len]
    do
      j:=NextIdx(len, i);
      jVert:=PL[iVert][i];
      if jVert>=iVert then
        jVert2:=PL[iVert][j];
        if jVert2=jVert then
          eEdgeMultiple:=[iVert, jVert];
          Add(ListMultipleEdges, eEdgeMultiple);
        fi;
      fi;
    od;
  od;
  return ListMultipleEdges;
end;


PlanGraphOrientedToVEF:=function(PLori)
  local nbDE, LDE, GroupVert, GroupEdge, GroupFace, VertSet, EdgeSet, FaceSet, ListOriginVert, ListOriginEdge, ListOriginFace, iVert, iEdge, iFace, eS;
  nbDE:=PLori.nbP;
  LDE:=[1..PLori.nbP];
  GroupVert:=Group([PLori.next]);
  GroupEdge:=Group([PLori.invers]);
  GroupFace:=Group([PLori.next*PLori.invers]);
  VertSet:=Orbits(GroupVert, LDE, OnPoints);
  EdgeSet:=List(Orbits(GroupEdge, LDE, OnPoints), Set);
  FaceSet:=Orbits(GroupFace, LDE, OnPoints);
  ListOriginVert:=ListWithIdenticalEntries(nbDE, 0);
  ListOriginEdge:=ListWithIdenticalEntries(nbDE, 0);
  ListOriginFace:=ListWithIdenticalEntries(nbDE, 0);
  for iVert in [1..Length(VertSet)]
  do
    eS:=VertSet[iVert];
    ListOriginVert{eS}:=ListWithIdenticalEntries(Length(eS), iVert);
  od;
  for iEdge in [1..Length(EdgeSet)]
  do
    eS:=EdgeSet[iEdge];
    ListOriginEdge{eS}:=ListWithIdenticalEntries(Length(eS), iEdge);
  od;
  for iFace in [1..Length(FaceSet)]
  do
    eS:=FaceSet[iFace];
    ListOriginFace{eS}:=ListWithIdenticalEntries(Length(eS), iFace);
  od;
  return rec(eNextF:=PLori.next*PLori.invers,
             VertSet:=VertSet, EdgeSet:=EdgeSet, FaceSet:=FaceSet,
             ListOriginVert:=ListOriginVert,
             ListOriginEdge:=ListOriginEdge,
             ListOriginFace:=ListOriginFace,
             nbVert:=Length(VertSet),
             nbEdge:=Length(EdgeSet),
             nbFace:=Length(FaceSet));
end;







#
#
# add option for computing the planar graph corresponding to it.
CellComplex:=function(PlanGraph)
  local VEF, VertexSet, NbVert, NbEdge, NbFac, NbU, iVert, iEdge, iFac, GraphHasse, Edge, ListFace, ListEdge, GraphAutomorphismToCellComplexAutomorphism, evFace, evEdge, iCol, eEdge, eFace, MappingSymmetryGroup, GraphPoset, ThePartition, VertexSetVert, VertexSetEdge, VertexSetFace, graEdge1, graEdge2;
  VEF:=PlanGraphToVEFsecond(PlanGraph);
  VertexSet:=[];
  VertexSetVert:=[];
  VertexSetEdge:=[];
  VertexSetFace:=[];
  NbVert:=VEF[1];
  NbEdge:=Length(VEF[2]);
  NbFac:=Length(VEF[3]);
  for iVert in [1..VEF[1]]
  do
    Add(VertexSetVert, iVert);
    Add(VertexSet, iVert);
  od;
  ListEdge:=[];
  for iEdge in [1..Length(VEF[2])]
  do
    eEdge:=VEF[2][iEdge];
    Add(VertexSet, eEdge);
    Add(VertexSetEdge, Set(eEdge));
    evEdge:=List(eEdge, x->x[1]);
    Add(ListEdge, evEdge);
  od;
  ListFace:=[];
  for iFac in [1..Length(VEF[3])]
  do
    eFace:=VEF[3][iFac];
    Add(VertexSet, eFace);
    Add(VertexSetFace, eFace);
    evFace:=List(eFace, x->x[1]);
    Add(ListFace, evFace);
  od;
  NbU:=NbVert+NbEdge+NbFac;
  GraphHasse:=NullGraph(Group(()), NbU);
  GraphPoset:=NullGraph(Group(()), NbU);
  #
  # Computation of the automorphism group
  #
  for iVert in [1..NbVert]
  do
    for iEdge in [1..NbEdge]
    do
      Edge:=VertexSetEdge[iEdge];
      if Edge[1][1]=iVert or Edge[2][1]=iVert then
        AddEdgeOrbit(GraphHasse, [iVert, NbVert+iEdge]);
        AddEdgeOrbit(GraphHasse, [NbVert+iEdge, iVert]);
        AddEdgeOrbit(GraphPoset, [iVert, NbVert+iEdge]);
      fi;
    od;
  od;
  for iEdge in [1..NbEdge]
  do
    for iFac in [1..NbFac]
    do
      if Length(Intersection(VertexSetEdge[iEdge],VertexSetFace[iFac]))=1 then
        graEdge1:=[NbVert+iEdge, NbVert+NbEdge+iFac];
        AddEdgeOrbit(GraphHasse, graEdge1);
        AddEdgeOrbit(GraphPoset, graEdge1);
        graEdge2:=[NbVert+NbEdge+iFac, NbVert+iEdge];
        AddEdgeOrbit(GraphHasse, graEdge2);
      fi;
    od;
  od;
  ThePartition:=[[1..NbVert], [NbVert+1..NbVert+NbEdge], [NbVert+NbEdge+1..NbVert+NbEdge+NbFac]];
  for iVert in [1..NbVert]
  do
    for iFac in [1..NbFac]
    do
      if Position(ListFace[iFac], iVert)<>fail then
        AddEdgeOrbit(GraphPoset, [iVert,NbVert+NbEdge+iFac]);
      fi;
    od;
  od;
  #
  # the following function maps an automorphism
  # of a planar graph (defined on vertices) to an automorphism
  # on the cell complex.
  # It is possible that this is not defined.
  GraphAutomorphismToCellComplexAutomorphism:=function(Perm)
    local ListImage;
    ListImage:=[];
    for iVert in [1..VEF[1]]
    do
      ListImage[iVert]:=OnPoints(iVert, Perm);
    od;
    for iEdge in [1..Length(ListEdge)]
    do
      ListImage[NbVert+iEdge]:=NbVert+Position(ListEdge, OnSets(ListEdge[iEdge],Perm));
    od;
    for iFac in [1..Length(ListFace)]
    do
      ListImage[NbVert+NbEdge+iFac]:=NbVert+NbEdge+Position(ListFace, OnSets(ListFace[iFac], Perm));
    od;
    return PermList(ListImage);
  end;
  # 
  # 
  # 
  # 
  MappingSymmetryGroup:=function(GrpMap)
    local Gens, GenNew, eGen;
    Gens:=GeneratorsOfGroup(GrpMap);
    GenNew:=[];
    for eGen in Gens
    do
      Add(GenNew, GraphAutomorphismToCellComplexAutomorphism(eGen));
    od;
    return PersoGroupPerm(GenNew);
  end;
  return rec(ListCells:=VertexSet,
             VertexSetEdge:=VertexSetEdge, 
             VertexSetFace:=VertexSetFace, 
             ThePartition:=ThePartition, 
             GraphHasse:=GraphHasse, 
             GraphPoset:=GraphPoset,
             MappingSymmetryGroup:=MappingSymmetryGroup,
             GraphAutomorphismToCellComplexAutomorphism:=GraphAutomorphismToCellComplexAutomorphism);
end;






PlanGraphOrientedToCellComplex:=function(PLori, VEFori)
  local VertexSet, iVert, NbVert, NbEdge, NbFace, iEdge, eEdge, iFace, eFace, NbU, GraphHasse, GraphPoset, ThePartition, nbDE, eDE, VectStat;
  VertexSet:=Concatenation(VEFori.VertSet, VEFori.EdgeSet, VEFori.FaceSet);
  NbVert:=Length(VEFori.VertSet);
  NbEdge:=Length(VEFori.EdgeSet);
  NbFace:=Length(VEFori.FaceSet);
  NbU:=NbVert + NbEdge + NbFace;
  nbDE:=PLori.nbP;
  #
  #
  # Computation of the incidence structure
  #
  #
  GraphHasse:=NullGraph(Group(()), NbU);
  GraphPoset:=NullGraph(Group(()), NbU);
  for iVert in [1..NbVert]
  do
    for eDE in VEFori.VertSet[iVert]
    do
      iEdge:=VEFori.ListOriginEdge[eDE];
      AddEdgeOrbit(GraphHasse, [iVert,NbVert+iEdge]);
      AddEdgeOrbit(GraphHasse, [NbVert+iEdge,iVert]);
      AddEdgeOrbit(GraphPoset, [iVert,NbVert+iEdge]);
    od; 
  od;
  for iEdge in [1..NbEdge]
  do
    for eDE in VEFori.EdgeSet[iEdge]
    do
      iFace:=VEFori.ListOriginFace[eDE];
      AddEdgeOrbit(GraphHasse, [NbVert+iEdge,NbVert+NbEdge+iFace]);
      AddEdgeOrbit(GraphHasse, [NbVert+NbEdge+iFace,NbVert+iEdge]);
      AddEdgeOrbit(GraphPoset, [NbVert+iEdge,NbVert+NbEdge+iFace]);
    od;
  od;
  for iVert in [1..NbVert]
  do
    for eDE in VEFori.VertSet[iVert]
    do
      iFace:=VEFori.ListOriginFace[eDE];
      AddEdgeOrbit(GraphPoset, [iVert,NbVert+NbEdge+iFace]);
    od;
  od;
  ThePartition:=[[1..NbVert], [NbVert+1..NbVert+NbEdge], [NbVert+NbEdge+1..NbVert+NbEdge+NbFace]];
  VectStat:=ListWithIdenticalEntries(NbU,0);
  VectStat{[1..NbVert]}:=ListWithIdenticalEntries(NbVert,1);
  VectStat{[NbVert+1..NbVert+NbEdge]}:=ListWithIdenticalEntries(NbEdge,2);
  VectStat{[NbVert+NbEdge+1..NbVert+NbEdge+NbFace]}:=ListWithIdenticalEntries(NbFace,3);
  # 
  return rec(ListCells:=VertexSet,
             VEF:=VEFori,
             VectStat:=VectStat, 
             ThePartition:=ThePartition,
             GraphHasse:=GraphHasse,
             GraphPoset:=GraphPoset);
end;




PlanGraphOrientedToLatticeDescription:=function(PLori)
  local LES, GRP, VEF, VertSet, ListNewGen, eGen, eLE, GroupEXT, ListFace, eFace, ListInc, iVert, eVert, INTS, len, VEFori;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  LES:=PlanGraphOrientedToCellComplex(PLori, VEFori);
  GRP:=SymmetryGroupVertexColoredGraph(LES.GraphHasse, LES.ThePartition);
  VEF:=LES.VEF;
  VertSet:=VEF.VertSet;
  ListNewGen:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eLE:=OnTuples([1..Length(VertSet)], eGen);
    Add(ListNewGen, PermList(eLE));
  od;
  GroupEXT:=PersoGroupPerm(ListNewGen);
  ListFace:=[];
  for eFace in VEF.FaceSet
  do
    ListInc:=[];
    for iVert in [1..Length(VertSet)]
    do
      eVert:=VertSet[iVert];
      INTS:=Intersection(eVert, eFace);
      len:=Length(INTS);
      if len<>0 and len<>1 then
        return false;
      fi;
      if len=1 then
        Add(ListInc, iVert);
      fi;
    od;
    Add(ListFace, ListInc);
  od;
  return rec(ListSimplexes:=ListFace, GroupEXT:=GroupEXT);
end;



IsIsomorphicPlanGraph:=function(PlanGraph1, PlanGraph2)
  local CC1, CC2, test;
  CC1:=CellComplex(PlanGraph1);
  CC2:=CellComplex(PlanGraph2);
  if CC1.ThePartition<>CC2.ThePartition then
    return false;
  fi;
  test:=EquivalenceVertexColoredGraph(CC1.GraphHasse, CC2.GraphHasse, CC1.ThePartition);
  if test=false then
    return false;
  else
    return true;
  fi;
end;





GetAllFlagsFromCellComplex_V1:=function(CC, ePL)
  local nbVert, nbEdge, nbFace, PreListFlag, iVert, LAdj, eAdj, iEdge, LAdj2, fAdj, iFac, ListFlag, nbFlag, GRAadj, iFlag, eFlag, fFlag, gFlag, hFlag, ListOthVert, ListOthEdge, ListOthFace, jVert, jEdge, jFace, TheBipartitionVect, VectorNumber1, VectorNumber2, LVectorNumber, IsGraphSymmetryRotation, iFace, pos, LAdj1, LAdj3, GetPermFlag, eListA, eListB, eListC, IsGraphSymmetryReflection, LFaces;
  nbVert:=Length(CC.ThePartition[1]);
  nbEdge:=Length(CC.ThePartition[2]);
  nbFace:=Length(CC.ThePartition[2]);
  LFaces:=__FaceSet(ePL);
  PreListFlag:=[];
  for iVert in [1..nbVert]
  do
    LAdj:=Adjacency(CC.GraphHasse, iVert);
    for eAdj in LAdj
    do
      iEdge:=eAdj - nbVert;
      LAdj2:=Adjacency(CC.GraphPoset, eAdj);
      for fAdj in LAdj2
      do
        iFac:=fAdj - nbVert - nbFace;
        Add(PreListFlag, [iVert, iEdge, iFac]);
      od;
    od;
  od;
  ListFlag:=Set(PreListFlag);
  nbFlag:=Length(ListFlag);
  GRAadj:=NullGraph(Group(()), nbFlag);
  eListA:=[];
  eListB:=[];
  eListC:=[];
  for iFlag in [1..nbFlag]
  do
    eFlag:=ListFlag[iFlag];
    iVert:=eFlag[1];
    iEdge:=eFlag[2];
    iFace:=eFlag[3];
    #
    LAdj1:=Adjacency(CC.GraphHasse, nbVert+iEdge);
    ListOthVert:=Filtered(LAdj1, x->x<=nbVert and x<>iVert);
    if Length(ListOthVert)<>1 then
      Error("Thinness breakdown 1");
    fi;
    jVert:=ListOthVert[1];
    fFlag:=[jVert, iEdge, iFace];
    pos:=Position(ListFlag, fFlag);
    AddEdgeOrbit(GRAadj, [iFlag, pos]);
    Add(eListA, pos);
    #
    LAdj2:=Intersection(Set(Adjacency(CC.GraphHasse, iVert)), Set(Adjacency(CC.GraphHasse, iFace+nbVert+nbEdge)));
    ListOthEdge:=Filtered(LAdj2, x->x<>iEdge+nbVert);
    if Length(ListOthEdge)<>1 then
      Error("Thinness breakdown 2");
    fi;
    jEdge:=ListOthEdge[1] - nbVert;
    gFlag:=[iVert, jEdge, iFace];
    pos:=Position(ListFlag, gFlag);
    AddEdgeOrbit(GRAadj, [iFlag, pos]);
    Add(eListB, pos);
    #
    LAdj3:=Adjacency(CC.GraphHasse, nbVert+iEdge);
    ListOthFace:=Filtered(LAdj3, x->x>nbVert+nbEdge and x<>iFace+nbVert+nbEdge);
    if Length(ListOthFace)<>1 then
      Error("Thinness breakdown 3");
    fi;
    jFace:=ListOthFace[1] - nbVert - nbEdge;
    hFlag:=[iVert, iEdge, jFace];
    pos:=Position(ListFlag, hFlag);
    AddEdgeOrbit(GRAadj, [iFlag, pos]);
    Add(eListC, pos);
  od;
  TheBipartitionVect:=GetBipartition(GRAadj);
  VectorNumber1:=Filtered([1..nbFlag], x->TheBipartitionVect[x]=1);
  VectorNumber2:=Filtered([1..nbFlag], x->TheBipartitionVect[x]=2);
  LVectorNumber:=[VectorNumber1, VectorNumber2];
  GetPermFlag:=function(ePerm)
    local eListImg, eFlag, iVert, iEdge, iFace, jVert, jEdge, jFace, fFlag, pos, ePermFlag, ImagePart1, posImage;
    eListImg:=[];
    for eFlag in ListFlag
    do
      iVert:=eFlag[1];
      iEdge:=eFlag[2];
      iFace:=eFlag[3];
      jVert:=OnPoints(iVert, ePerm);
      jEdge:=OnPoints(iEdge + nbVert, ePerm) - nbVert;
      jFace:=OnPoints(iFace + nbEdge + nbVert, ePerm) - nbVert - nbEdge;
      fFlag:=[jVert, jEdge, jFace];
      pos:=Position(ListFlag, fFlag);
      Add(eListImg, pos);
    od;
    ePermFlag:=PermList(eListImg);
    return ePermFlag;
  end;
  IsGraphSymmetryRotation:=function(ePerm)
    local ePermFlag, ImagePart1, posImage;
    ePermFlag:=GetPermFlag(ePerm);
    ImagePart1:=OnSets(VectorNumber1, ePermFlag);
    posImage:=Position(LVectorNumber, ImagePart1);
    if posImage=1 then
      return true;
    fi;
    if posImage=2 then
      return false;
    fi;
    Error("Logical error, correct");
  end;
  IsGraphSymmetryReflection:=function(ePerm)
    local ePermFlag, iFlag, jFlag;
    ePermFlag:=GetPermFlag(ePerm);
    for iFlag in [1..nbFlag]
    do
      jFlag:=OnPoints(iFlag, ePermFlag);
      if jFlag=eListA[iFlag] then
        return true;
      fi;
      if jFlag=eListB[iFlag] then
        return true;
      fi;
      if jFlag=eListC[iFlag] then
        return true;
      fi;
    od;
    return false;
  end;
  return rec(ListFlag:=ListFlag,
             TheBipartitionVect:=TheBipartitionVect, 
             IsGraphSymmetryRotation:=IsGraphSymmetryRotation, 
             IsGraphSymmetryReflection:=IsGraphSymmetryReflection);
end;





#
# This is for the plangraph case.
# 
#
GetAllFlagsFromCellComplex:=function(CC, ePL)
  local nbVert, nbFace, ListDE, iVert, len, pos, eDE, nbDE, nbEdge, VectFaceStat, iFace, eFace, VectFaceEdge, iEdge, PreListFlagDir, PreListFlagUndir, rDE, jDE, eFlagDir, eFlagUndir, ListFlagDir, ListFlagUndir, ListFlagBothDir, nbDirFlag, ListFlag, GetPermDE, GetPermFlag, IsGraphSymmetryRotation, IsGraphSymmetryReflection, NbU, iDE, eFlag;
  nbVert:=Length(ePL);
  nbFace:=Length(CC.VertexSetFace);
  ListDE:=[];
  for iVert in [1..nbVert]
  do
    len:=Length(ePL[iVert]);
    for pos in [1..len]
    do
      eDE:=[iVert, pos];
      Add(ListDE, eDE);
    od;
  od;
  nbDE:=Length(ListDE);
  nbEdge:=nbDE/2;
  VectFaceStat:=ListWithIdenticalEntries(nbDE, 0);
  for iFace in [1..nbFace]
  do
    eFace:=CC.VertexSetFace[iFace];
    for eDE in eFace
    do
      pos:=Position(ListDE, eDE);
      VectFaceStat[pos]:=iFace;
    od;
  od;
  #
  VectFaceEdge:=ListWithIdenticalEntries(nbDE, 0);
  for iEdge in [1..nbEdge]
  do
    for eDE in CC.VertexSetEdge[iEdge]
    do
      pos:=Position(ListDE, eDE);
      VectFaceEdge[pos]:=iEdge;
    od;
  od;
  #
  PreListFlagDir:=[];
  PreListFlagUndir:=[];
  for iDE in [1..nbDE]
  do
    eDE:=ListDE[iDE];
    rDE:=ReverseDE(ePL, eDE);
    jDE:=Position(ListDE, rDE);
    iFace:=VectFaceStat[iDE];
    eFlagDir:=[iDE, iFace];
    eFlagUndir:=[jDE, iFace];
    Add(PreListFlagDir, eFlagDir);
    Add(PreListFlagUndir, eFlagUndir);
  od;
  #
  # In the case of 1-connected graphs, we can have graphs
  # with flags that are oriented in both directions.
  #
  ListFlagDir:=[];
  ListFlagUndir:=[];
  ListFlagBothDir:=[];
  for eFlag in PreListFlagDir
  do
    pos:=Position(PreListFlagUndir, eFlag);
    if pos<>fail then
      Add(ListFlagBothDir, eFlag);
    else
      Add(ListFlagDir, eFlag);
    fi;
  od;
  for eFlag in PreListFlagUndir
  do
    pos:=Position(PreListFlagDir, eFlag);
    if pos=fail then
      Add(ListFlagUndir, eFlag);
    fi;
  od;
  nbDirFlag:=Length(ListFlagDir);
  if Length(ListFlagUndir)<>nbDirFlag then
    Error("Inconsistency in Dir and Undir flags");
  fi;
  ListFlag:=Concatenation(ListFlagDir, ListFlagUndir, ListFlagBothDir);
  GetPermDE:=function(ePermCC)
    local eListDE, iDE, eDE, eVert, eVertImg, rDE, eEdge, iEdge, iEdgeImg, eEdgeImg, LVertImg, pos, eDEimg, posImg;
    eListDE:=[];
    for iDE in [1..nbDE]
    do
      eDE:=ListDE[iDE];
      eVert:=eDE[1];
      eVertImg:=OnPoints(eVert, ePermCC);
      rDE:=ReverseDE(ePL, eDE);
      eEdge:=Set([eDE, rDE]);
      iEdge:=Position(CC.VertexSetEdge, eEdge);
      iEdgeImg:=OnPoints(iEdge+nbVert, ePermCC) - nbVert;
      eEdgeImg:=CC.VertexSetEdge[iEdgeImg];
      LVertImg:=List(eEdgeImg, x->x[1]);
      if LVertImg[1]=LVertImg[2] then
        Error("Error on the edge");
      fi;
      pos:=First([1..2], x->LVertImg[x]=eVertImg);
      if pos=fail then
        Error("Error on the vertex");
      fi;
      eDEimg:=eEdgeImg[pos];
      posImg:=Position(ListDE, eDEimg);
      Add(eListDE, posImg);
    od;
    return PermList(eListDE);
  end;
  GetPermFlag:=function(ePermCC)
    local ePermDE, eListFlag, eFlag, iDE, iDEimg, iFace, iFaceImg, eFlagImg, iFlagImg;
    ePermDE:=GetPermDE(ePermCC);
    eListFlag:=[];
    for eFlag in ListFlag
    do
      iDE:=eFlag[1];
      iDEimg:=OnPoints(iDE, ePermDE);
      iFace:=eFlag[2];
      iFaceImg:=OnPoints(iFace + nbVert + nbEdge, ePermCC) - nbVert - nbEdge;
      eFlagImg:=[iDEimg, iFaceImg];
      iFlagImg:=Position(ListFlag, eFlagImg);
      Add(eListFlag, iFlagImg);
    od;
    return PermList(eListFlag);
  end;
  IsGraphSymmetryRotation:=function(ePermCC)
    local ePermFlag, eSet1, eSet2, eSet1img, eSet2img;
    ePermFlag:=GetPermFlag(ePermCC);
    eSet1:=[1..nbDirFlag];
    eSet2:=[nbDirFlag+1..2*nbDirFlag];
    eSet1img:=OnSets(eSet1, ePermFlag);
    if eSet1img=eSet1 then
      return true;
    fi;
    if eSet1img=eSet2 then
      return false;
    fi;
    Error("We did not find the right image of flag");
  end;
  NbU:=nbVert + nbEdge + nbFace;
  IsGraphSymmetryReflection:=function(ePermCC)
    local ListStab, ListVertStab, ListEdgeStab, ListFaceStab, ePermDE, ePermFlag, nbVertInvers, eVert, len, ePerm1, ePerm2, DihGRP, CycGRP, eList, i, eDEred, iDE, iDEimg, pos, ePerm, nbEdgeInvers, eEdge, eVert1, eVert2, eVert1img, eVert2img, IsDone, IsInv, LDE1, LDE2, LDE1img, LDE2img, nbFaceInvers, iFace, eFace, rFace;
    ListStab:=Filtered([1..NbU], x->OnPoints(x, ePermCC)=x);
    ListVertStab:=Intersection([1..nbVert], ListStab);
    ListEdgeStab:=List(Intersection([nbVert+1..nbVert+nbEdge], ListStab), x->x - nbVert);
    ListFaceStab:=List(Intersection([nbVert+nbEdge+1..nbVert+nbEdge+nbFace], ListStab), x->x - nbVert - nbEdge);
    ePermDE:=GetPermDE(ePermCC);
    ePermFlag:=GetPermFlag(ePermCC);
    nbVertInvers:=0;
    for eVert in ListVertStab
    do
      len:=Length(ePL[eVert]);
      ePerm1:=PermList(List([1..len], x->NextIdx(len, x)));
      ePerm2:=PermList(Reversed([1..len]));
      DihGRP:=Group([ePerm1, ePerm2]);
      CycGRP:=Group([ePerm1]);
      eList:=[];
      for i in [1..len]
      do
        eDEred:=[eVert, i];
        iDE:=Position(ListDE, eDEred);
        iDEimg:=OnPoints(iDE, ePermDE);
        pos:=ListDE[iDEimg][2];
        Add(eList, pos);
      od;
      ePerm:=PermList(eList);
      if not(ePerm in DihGRP) then
        Error("The element should be in the dihedral group");
      fi;
      if not(ePerm in CycGRP) then
        nbVertInvers:=nbVertInvers+1;
      fi;
    od;
    nbFaceInvers:=0;
    for iFace in ListFaceStab
    do
      eFace:=CC.VertexSetFace[iFace];
      rFace:=List(eFace, x->ReverseDE(ePL, x));
      LDE1:=Set(List(eFace, x->Position(ListDE, x)));
      LDE2:=Set(List(rFace, x->Position(ListDE, x)));
      LDE1img:=OnSets(LDE1, ePermDE);
      LDE2img:=OnSets(LDE2, ePermDE);
      IsDone:=false;
      if LDE1=LDE1img and LDE2=LDE2img then
        IsDone:=true;
        IsInv:=false;
      fi;
      if LDE2=LDE1img and LDE1=LDE2img then
        IsDone:=true;
        IsInv:=true;
      fi;
      if IsDone=false then
        Error("We could not conclude");
      fi;
      if IsInv then
        nbFaceInvers:=nbFaceInvers+1;
      fi;
    od;
    if nbVertInvers=0 and nbFaceInvers=0 then
      return false;
    fi;
    if nbVertInvers=Length(ListVertStab) and nbFaceInvers=Length(ListFaceStab) then
      return true;
    fi;
    Error("We did not reach conclusion in determination of inversion characteristic");
  end;
  return rec(ListFlag:=ListFlag,
             IsGraphSymmetryRotation:=IsGraphSymmetryRotation, 
             IsGraphSymmetryReflection:=IsGraphSymmetryReflection);
end;



#
#
# The method of using the cell complex for computing the automorphism group
# does not work when we have to deal with 
PlanarInformationSymmetryGroup:=function(CellComplex, AutomorphismGroup, RecFlag)
  local ListStable, iVert, eElt, InversionSymmetry, ListReflexionPlane, ListReflexionPlaneNormalized, ListAngleRotation, ListRotAxis, ListAngleSymmetryRotation, ListFoldingNumbers, FoldingNumber, test, MaxAxisOrder, SchoenflieSymbol, SchoenflieSymbolLatex, ListRotData, nbFoldTwo, CC, eRot, FuncOrderPerm, ePlane, fPlane, GrpSize, NbStable, SecFoldingNbr, NbCells, NbStable2, IsRotationGroup, iCell, IsElementRotation, ListIdentity, eProd, IsDone, IsElementReflection, RotationSubgroup, ListRotationGens, FuncInsertRotation, nbVert, nbEdge, nbFace, GetSymbolName, aStab, bStab;
  NbCells:=Length(CellComplex.ListCells);
  nbVert:=Length(CellComplex.ThePartition[1]);
  nbEdge:=Length(CellComplex.ThePartition[2]);
  nbFace:=Length(CellComplex.ThePartition[3]);
  GetSymbolName:=function(i)
    if i<=nbVert then
      return "vert";
    fi;
    if nbVert<i and i<=nbVert+nbEdge then
      return "edge";
    fi;
    if nbVert+nbEdge<i and i<=nbVert+nbEdge+nbFace then
      return "face";
    fi;
    Error("No point find");
  end;
  #
  #
  ListReflexionPlane:=[];
  ListAngleSymmetryRotation:=[];
  ListFoldingNumbers:=[];
  ListRotData:=[];
  InversionSymmetry:=false;
  IsRotationGroup:=true;
  #
  RotationSubgroup:=Group(());
  ListRotationGens:=[];
  FuncInsertRotation:=function(eElt)
    if eElt in RotationSubgroup then
      return;
    fi;
    Add(ListRotationGens, eElt);
    RotationSubgroup:=Group(ListRotationGens);
  end;
  #
  # finding the group elements
  FuncOrderPerm:=function(Perm)
    local Cyc, eLCM, u;
    Cyc:=CycleStructurePerm(Perm);
    eLCM:=1;
    for u in [1..Length(Cyc)]
    do
      if IsBound(Cyc[u])=true then
        eLCM:=Lcm(eLCM, u+1);
      fi;
    od;
    return eLCM;
  end;
  ListIdentity:=[];
  for eElt in AutomorphismGroup
  do
    ListStable:=Difference([1..NbCells], MovedPoints([eElt]));
    IsElementRotation:=RecFlag.IsGraphSymmetryRotation(eElt);
    IsElementReflection:=RecFlag.IsGraphSymmetryReflection(eElt);
    NbStable:=Length(ListStable);
    IsDone:=false;
    if eElt=() then
      IsDone:=true;
      Add(ListIdentity, eElt);
    fi;
    if NbStable=2 and IsElementRotation=true then
      # rotation
      FoldingNumber:=FuncOrderPerm(eElt);
      AddSet(ListFoldingNumbers, FoldingNumber);
      test:=0;
      for eRot in ListRotData
      do
        if eRot[1]=ListStable then
          test:=1;
          if FoldingNumber>eRot[2] then
            eRot[2]:=FoldingNumber;
          fi;
          AddSet(eRot[3], eElt);
        fi;
      od;
      if test=0 then
        Add(ListRotData, [ListStable, FoldingNumber, [eElt]]);
      fi;
      FuncInsertRotation(eElt);
      IsDone:=true;
    fi;
    if NbStable=0 and IsElementRotation=false and IsElementReflection=false then
      # rotation composed with reflection
      NbStable2:=NbCells - NrMovedPoints(eElt*eElt);
      SecFoldingNbr:=FuncOrderPerm(eElt*eElt);
      AddSet(ListAngleSymmetryRotation, SecFoldingNbr);
      if SecFoldingNbr=1 then
        InversionSymmetry:=eElt;
      fi;
      if IsElementRotation=true then
        Error("Logical error in our program 2");
      fi;
      IsRotationGroup:=false;
      IsDone:=true;
    fi;
    if NbStable<NbCells and IsElementRotation=false and IsElementReflection=true then
      # reflection
      eProd:=eElt*eElt;
      if eProd<>() then
        Error("Element is not a reflection");
      fi;
      AddSet(ListReflexionPlane, ListStable);
      if IsElementRotation=true then
        Error("Logical error in our program 3");
      fi;
      IsRotationGroup:=false;
      IsDone:=true;
    fi;
    if IsDone=false then
      Print("NbStable=", NbStable, "\n");
      Print("IsElementRotation=", IsElementRotation, "\n");
      Print("IsElementReflection=", IsElementReflection, "\n");
      Error("Failed to find right class");
    fi;
  od;
  #
  #
  # Build the rotation group
  GrpSize:=Order(AutomorphismGroup);
  #
  #
  #
  # Group analysis (see "Polyhedra", Peter R.Cromwell, p.313)
  nbFoldTwo:=0;
  for eRot in ListRotData
  do
    if eRot[2]=2 then
      nbFoldTwo:=nbFoldTwo+1;
    fi;
  od;
  if Length(ListRotData)=0 then
    if Length(ListReflexionPlane)=1 then
       SchoenflieSymbol:="Cs";
       SchoenflieSymbolLatex:="C_s";
    else
      if GrpSize>1 then
        SchoenflieSymbol:="Ci";
        SchoenflieSymbolLatex:="C_i";
      else
        SchoenflieSymbol:="C1";
        SchoenflieSymbolLatex:="C_1";
      fi;
    fi;
  elif Length(ListRotData)=1 then
    MaxAxisOrder:=Maximum(ListFoldingNumbers);
    if ListReflexionPlane=[] then
      if Length(ListAngleSymmetryRotation)>0 then
        SchoenflieSymbol:=Concatenation("S",String(2*MaxAxisOrder));
        SchoenflieSymbolLatex:=Concatenation("S_{",StringLatex(2*MaxAxisOrder),"}");
      else
        SchoenflieSymbol:=Concatenation("C",String(MaxAxisOrder));
        SchoenflieSymbolLatex:=Concatenation("C_{",StringLatex(MaxAxisOrder), "}");
      fi;
    else
      if Length(ListReflexionPlane)=1 then 
        SchoenflieSymbol:=Concatenation("C",String(MaxAxisOrder),"h");
        SchoenflieSymbolLatex:=Concatenation("C_{",String(MaxAxisOrder),"h}");
      else
        SchoenflieSymbol:=Concatenation("C",String(MaxAxisOrder),"v");
        SchoenflieSymbolLatex:=Concatenation("C_{",String(MaxAxisOrder),"v}");
      fi;
    fi;
  elif nbFoldTwo>=Length(ListRotData)-1 then
    MaxAxisOrder:=Maximum(ListFoldingNumbers);
    if ListReflexionPlane=[] then
      SchoenflieSymbol:=Concatenation("D",String(MaxAxisOrder));
      SchoenflieSymbolLatex:=Concatenation("D_{",StringLatex(MaxAxisOrder),"}");
    else
      if Length(ListReflexionPlane)=MaxAxisOrder then 
        SchoenflieSymbol:=Concatenation("D",String(MaxAxisOrder),"d");
        SchoenflieSymbolLatex:=Concatenation("D_{",String(MaxAxisOrder),"d}");
      else
        SchoenflieSymbol:=Concatenation("D",String(MaxAxisOrder),"h");
        SchoenflieSymbolLatex:=Concatenation("D_{",String(MaxAxisOrder),"h}");
      fi;
    fi;
  elif 5 in ListFoldingNumbers then
    if Length(ListReflexionPlane)=0 then
      SchoenflieSymbol:="I";
      SchoenflieSymbolLatex:="I";
    else
      SchoenflieSymbol:="Ih";
      SchoenflieSymbolLatex:="I_h";
    fi;
  elif 4 in ListFoldingNumbers then
    if Length(ListReflexionPlane)=0 then
      SchoenflieSymbol:="O";
      SchoenflieSymbolLatex:="O";
    else
      SchoenflieSymbol:="Oh";
      SchoenflieSymbolLatex:="O_h";
    fi;
  elif GrpSize=12 then
    SchoenflieSymbol:="T";
    SchoenflieSymbolLatex:="T";
  elif InversionSymmetry<>false then
    SchoenflieSymbol:="Th";
    SchoenflieSymbolLatex:="T_h";
  else
    SchoenflieSymbol:="Td";
    SchoenflieSymbolLatex:="T_d";
  fi;
  ListReflexionPlaneNormalized:=[];
  for ePlane in ListReflexionPlane
  do
    fPlane:=[];
    for iCell in ePlane
    do
      Add(fPlane, CellComplex.ListCells[iCell]);
    od;
    Add(ListReflexionPlaneNormalized, fPlane);
  od;
  ListRotAxis:=[];
  for eRot in ListRotData
  do
    aStab:=eRot[1][1];
    bStab:=eRot[1][2];
    Add(ListRotAxis, rec(ListStable:=[aStab,bStab],
                         type:=[GetSymbolName(aStab),GetSymbolName(bStab)],
                         axis:=[CellComplex.ListCells[aStab], CellComplex.ListCells[bStab]],
                         folding:=eRot[2]));
  od;
  return rec(SymmetryPlane:=ListReflexionPlaneNormalized,
             RotationAxis:=ListRotAxis,
	     RotationSubgroup:=RotationSubgroup, 
             SchoenfliesSymbol:=SchoenflieSymbol,
             SchoenfliesSymbolLatex:=SchoenflieSymbolLatex,
             GenSymbol:=SchoenflieSymbol,
             GenSymbolLatex:=SchoenflieSymbolLatex,
             Inversion:=InversionSymmetry,
             IsRotationGroup:=IsRotationGroup);
end;



GetRotationSubgroup_General:=function(AutomorphismGroup, RecFlag)
  local ListGEN, GrpGEN, FuncInsert, eElt, IsElementRotation;
  ListGEN:=[];
  GrpGEN:=Group(());
  FuncInsert:=function(eElt)
    if eElt in GrpGEN then
      return;
    fi;
    Add(ListGEN, eElt);
    GrpGEN:=Group(ListGEN);
  end;
  for eElt in AutomorphismGroup
  do
    IsElementRotation:=RecFlag.IsGraphSymmetryRotation(eElt);
    if IsElementRotation then
      FuncInsert(eElt);
    fi;
  od;
  return GrpGEN;
end;



TorusTranslationSubgroup_General:=function(CellComplex, GRProt, RecFlag)
  local NbCells, FuncIsTranslation, ListGen, GRPtrans, FuncInsert, eElt;
  NbCells:=Length(CellComplex.ListCells);
  FuncIsTranslation:=function(TheRot)
    local ListStable;
    ListStable:=Difference([1..NbCells], MovedPoints([eElt]));
    if Length(ListStable)>0 then
      return false;
    fi;
    return true;
  end;
  ListGen:=[];
  GRPtrans:=Group(());
  FuncInsert:=function(OneTrans)
    if OneTrans in GRPtrans then
      return;
    fi;
    Add(ListGen, OneTrans);
    GRPtrans:=Group(ListGen);
  end;
  for eElt in GRProt
  do
    if eElt<>() then
      if FuncIsTranslation(eElt)=true then
        FuncInsert(eElt);
      fi;
    fi;
  od;
  return GRPtrans;
end;








TorusInformationSymmetryGroupIrreducible:=function(CellComplex, GRPinput, RecFlag)
  local TransGroup, SpaceSymbol, TheSym, NbCells, GRProt, ListNumbersSeparatrixLines, ListStab2, ListStab3, ListStab4, AllIncluded, IsIncluded, eListStab, Stab, i, j, ListListStab, ListStab, ListCompReflectionTranslation, ListReflection, ListConn, IND, SIZ, u, GRA, IsRotationGroup, testRef, nbConn, ListConnCell;
#  Print("test(GraphPoset, GRP)=", IsGroupAutomorphism(CellComplex.GraphPoset, GRPinput), "\n");
  GRProt:=GetRotationSubgroup_General(GRPinput, RecFlag);
#  Print("  |GRPinput|=", Order(GRPinput), "  |GRProt|=", Order(GRProt), "\n");
  IsRotationGroup:=GRProt=GRPinput;
  TransGroup:=TorusTranslationSubgroup_General(CellComplex, GRProt, RecFlag);
  if Order(TransGroup)>1 then
    Error("The torus should be irreducible");
  fi;
  NbCells:=Length(CellComplex.ListCells);
#  Print("NbCells=", NbCells, "\n");
  ListStab2:=[];
  ListStab3:=[];
  ListStab4:=[];
  for i in [1..NbCells]
  do
    Stab:=Stabilizer(GRProt, i, OnPoints);
    if Order(Stab)=2 then
      Add(ListStab2, i);
    fi;
    if Order(Stab)=3 then
      Add(ListStab3, i);
    fi;
    if Order(Stab)=4 then
      Add(ListStab4, i);
    fi;
  od;
  #
  #
  #
  TheSym:=SymmetrizedVersionOfGraph(CellComplex.GraphPoset);
  ListReflection:=[];
  ListCompReflectionTranslation:=[];
  ListListStab:=[];
  ListNumbersSeparatrixLines:=[];
  for u in Difference(GRPinput, GRProt)
  do
#    Print("Before determination of nbConn\n");
    testRef:=RecFlag.IsGraphSymmetryReflection(u);
    if testRef then
      ListConnCell:=RecFlag.ComponentsStabilizedReflection(u).ListConnCell;
      ListStab:=Concatenation(ListConnCell);
      nbConn:=Length(ListConnCell);
      Add(ListReflection, u);
      AddSet(ListListStab, ListStab);
    else
      nbConn:=0;
      Add(ListCompReflectionTranslation, u);
    fi;
    Add(ListNumbersSeparatrixLines, nbConn);
  od;
#  Print(" ListNumbersSeparatrixLines=", ListNumbersSeparatrixLines, "\n");
  #
  # Now determining the groups
  #
  if Order(GRProt)=6 then
    if GRProt = GRPinput then
      SpaceSymbol:="p6";
    else
      SpaceSymbol:="p6mm";
    fi;
  elif Length(ListStab4)>0 then
    if GRProt = GRPinput then
      SpaceSymbol:="p4";
    else
      IsIncluded:=false;
      for eListStab in ListListStab
      do
        SIZ:=Length(Intersection(eListStab, ListStab4));
        if SIZ>0 then
          IsIncluded:=true;
        fi;
      od;
      if IsIncluded=false then
        SpaceSymbol:="p4gm";
      else
        SpaceSymbol:="p4mm";
      fi;
    fi;
  elif Length(ListStab3)>0 then
    if GRProt = GRPinput then
      SpaceSymbol:="p3";
    else
      AllIncluded:=true;
      for eListStab in ListListStab
      do
        if IsSubset(eListStab, ListStab3)=false then
          AllIncluded:=false;
        fi;
      od;
      if AllIncluded=true then
        SpaceSymbol:="p3m1";
      else
        SpaceSymbol:="p31m";
      fi;
    fi;
  elif Length(ListStab2)>0 then
    if GRPinput = GRProt then
      SpaceSymbol:="p2";
    else
      if ListNumbersSeparatrixLines=[2,2] then
        SpaceSymbol:="p2mm";
      elif ListNumbersSeparatrixLines=[1,1] then
        SpaceSymbol:="c2mm";
      elif ListNumbersSeparatrixLines=[0,0] then
        SpaceSymbol:="p2gg";
      elif Set(ListNumbersSeparatrixLines)=[0,2] then
        SpaceSymbol:="p2mg";
      else
        Error("We have an error HERE_1");
      fi;
    fi;
  elif Order(GRProt)=1 then
    if GRPinput = GRProt then
      SpaceSymbol:="p1";
    else
      if ListNumbersSeparatrixLines=[2] then
        SpaceSymbol:="pm";
      elif ListNumbersSeparatrixLines=[1] then
        SpaceSymbol:="cm";
      elif ListNumbersSeparatrixLines=[0] then
        SpaceSymbol:="pg";
      else
        Error("We have an error HERE_2");
      fi;
    fi;
  else
    Error("We have an error HERE_3");
  fi;
  return rec(ListStab2:=ListStab2,
             ListStab3:=ListStab3,
             ListStab4:=ListStab4,
             IsRotationGroup:=IsRotationGroup,
             SpaceSymbol:=SpaceSymbol,
             GenSymbol:=SpaceSymbol, 
             GenSymbolLatex:=SpaceSymbol);
end;

TorusInformationSymmetryGroup:=function(CellComplexIn, GRPin, RecFlag)
  local GRProt, TransGroup, NbCells, O, IsEdgeAdd, NbCellRed, GraphPoset, i, j, CellComplexRed, ListOriginCell, iO, NewListGen, ListGenIN, eGen, eList, iCellRed, iCell, jCell, jCellRed, GRPmapped, phi, IsGraphSymmetryRotation, IsGraphSymmetryReflection, RecFlagRed, TheRes, u, ListStab, ComponentsStabilizedReflection, testRef;
  GRProt:=GetRotationSubgroup_General(GRPin, RecFlag);
  TransGroup:=TorusTranslationSubgroup_General(CellComplexIn, GRProt, RecFlag);
  NbCells:=Length(CellComplexIn.ListCells);
  O:=Orbits(TransGroup, [1..NbCells], OnPoints);
  #
  # Creating the GraphPoset
  #
  IsEdgeAdd:=function(iPt,jPt)
    local v, ePt;
    ePt:=O[iPt][1];
    for v in O[jPt]
    do
      if IsEdge(CellComplexIn.GraphPoset, [ePt,v]) then
        return true;
      fi;
    od;
    return false;
  end;
  NbCellRed:=Length(O);
  GraphPoset:=NullGraph(Group(()), NbCellRed);
  for i in [1..NbCellRed]
  do
    for j in [1..NbCellRed]
    do
      if i<>j then
        if IsEdgeAdd(i,j) then
	  AddEdgeOrbit(GraphPoset, [i,j]);
	fi;
      fi;
    od;
  od;
  CellComplexRed:=rec(ListCells:=O,
                      GraphPoset:=GraphPoset);
  #
  # Mapping the group
  #
  ListOriginCell:=[];
  for iO in [1..NbCellRed]
  do
    ListOriginCell{O[iO]}:=ListWithIdenticalEntries(Length(O[iO]), iO);
  od;
  NewListGen:=[];
  ListGenIN:=GeneratorsOfGroup(GRPin);
  for eGen in ListGenIN
  do
    eList:=[];
    for iCellRed in [1..NbCellRed]
    do
      iCell:=O[iCellRed][1];
      jCell:=OnPoints(iCell, eGen);
      jCellRed:=ListOriginCell[jCell];
      Add(eList, jCellRed);
    od;
    Add(NewListGen, PermList(eList));
  od;
  GRPmapped:=PersoGroupPerm(NewListGen);
  #
  # Mapping the RecFlag
  #
  phi:=GroupHomomorphismByImages(GRPin, GRPmapped, ListGenIN, NewListGen);
  IsGraphSymmetryRotation:=function(eEltRed)
    local eElt;
    eElt:=PreImagesRepresentative(phi, eEltRed);
    return RecFlag.IsGraphSymmetryRotation(eElt);
  end;
  IsGraphSymmetryReflection:=function(eEltRed)
    local eElt, fElt, gElt, testResult;
    eElt:=PreImagesRepresentative(phi, eEltRed);
    for fElt in TransGroup
    do
      gElt:=eElt*fElt;
      testResult:=RecFlag.IsGraphSymmetryReflection(gElt);
      if testResult then
        return true;
      fi;
    od;
    return false;
  end;
  ComponentsStabilizedReflection:=function(eEltRed)
    local eElt, fElt, gElt, testResult, ListConnCell, ListConnCellSet, eConnCell, setConnCell, pos, nConnCell, eVal, iOrb;
    eElt:=PreImagesRepresentative(phi, eEltRed);
    ListConnCell:=[];
    for fElt in TransGroup
    do
      gElt:=eElt*fElt;
      testResult:=RecFlag.IsGraphSymmetryReflection(gElt);
      if testResult then
        for eConnCell in RecFlag.ComponentsStabilizedReflection(gElt).ListConnCell
        do
	  nConnCell:=[];
	  for eVal in eConnCell
	  do
	    iOrb:=ListOriginCell[eVal];
	    Add(nConnCell, iOrb);
	  od;
          AddSet(ListConnCell, DihedralCanonicalization(nConnCell));
        od;
      fi;
    od;
    if Length(ListConnCell)=0 then
      Error("We have ListConnCell being empty");
    fi;
    return rec(ListConnCell:=ListConnCell);
  end;
  RecFlagRed:=rec(IsGraphSymmetryRotation:=IsGraphSymmetryRotation, 
                  IsGraphSymmetryReflection:=IsGraphSymmetryReflection,
		  ComponentsStabilizedReflection:=ComponentsStabilizedReflection);
  return TorusInformationSymmetryGroupIrreducible(CellComplexRed, GRPmapped, RecFlagRed);
end;



MapInformationSymmetryGroup:=function(CellComplex, GRPin, RecFlag)
  local nbVert, nbEdge, nbFace, Charac;
  nbVert:=Length(CellComplex.ThePartition[1]);
  nbEdge:=Length(CellComplex.ThePartition[2]);
  nbFace:=Length(CellComplex.ThePartition[3]);
  Charac:=nbVert - nbEdge + nbFace;
  if Charac=2 then
    return PlanarInformationSymmetryGroup(CellComplex, GRPin, RecFlag);
  fi;
  if Charac=0 then
    return TorusInformationSymmetryGroup(CellComplex, GRPin, RecFlag);
  fi;
  Print("Charac=", Charac, "\n");
  Error("The Characteristic has no matched. Only 2 and 0 are possible, i.e. torus or plane graph");
end;

ReduceActionToEdge:=function(CellComplex, GRPin)
  local NewListGen, nbVert, nbEdge, eGen, eList, ePerm;
  NewListGen:=[];
  nbVert:=Length(CellComplex.ThePartition[1]);
  nbEdge:=Length(CellComplex.ThePartition[2]);
  for eGen in GeneratorsOfGroup(GRPin)
  do
    eList:=List([1..nbEdge], x->OnPoints(x+nbVert,eGen)-nbVert);
    ePerm:=PermList(eList);
    Add(NewListGen, ePerm);
  od;
  return PersoGroupPerm(NewListGen);
end;


GetOrderGroupPlanSize:=function(eString)
  local i, ListCasesTorus, eEnt;
  ListCasesTorus:=[
    rec(name:="p6", ord:=6),
    rec(name:="p6mm", ord:=12),
    
    rec(name:="p4", ord:=4),
    rec(name:="p4gm", ord:=8),
    rec(name:="p4mm", ord:=8),
    
    rec(name:="p3", ord:=3),
    rec(name:="p3m1", ord:=6),
    rec(name:="p31m", ord:=6),
    
    rec(name:="p2", ord:=2),
    rec(name:="p2mm", ord:=4),
    rec(name:="c2mm", ord:=4),
    rec(name:="p2gg", ord:=4),
    rec(name:="p2mg", ord:=4),

    rec(name:="p1", ord:=1),
    rec(name:="pm", ord:=2),
    rec(name:="cm", ord:=2),
    rec(name:="pg", ord:=2)];
  for eEnt in ListCasesTorus
  do
    if eEnt.name=eString then
      return eEnt.ord;
    fi;
  od;

  if eString="I" then
    return 60;
  fi;
  if eString="Ih" then
    return 60;
  fi;
  #
  if eString="O" then
    return 24;
  fi;
  if eString="Oh" then
    return 48;
  fi;
  #
  if eString="T" then
    return 12;
  fi;
  if eString="Th" then
    return 24;
  fi;
  if eString="Td" then
    return 24;
  fi;
  #
  if eString="C1" then
    return 1;
  fi;
  if eString="Ci" then
    return 2;
  fi;
  if eString="Cs" then
    return 2;
  fi;
  #
  for i in [2..100]
  do
    if eString=Concatenation("C", String(i)) then
      return i;
    fi;
    if eString=Concatenation("C", String(i), "v") then
      return 2*i;
    fi;
    if eString=Concatenation("C", String(i), "h") then
      return 2*i;
    fi;
    if eString=Concatenation("D", String(i)) then
      return 2*i;
    fi;
    if eString=Concatenation("D", String(i), "d") then
      return 4*i;
    fi;
    if eString=Concatenation("D", String(i), "h") then
      return 4*i;
    fi;
    if eString=Concatenation("S", String(i)) then
      return i;
    fi;
  od;
  Error("Did not match anything");
end;






#
# The flags are unfortunately not sufficient for distinguishing symmetries.
# But with the orientation we have a way to recover things.
#
ReduceToAdmissibleSymmetries:=function(ePL, CC, GRP)
  local LFaces, RedFaces, eFace, rFace, IsCycleEquivalent, IsInListReducedFaces, TestCorrectnessCCperm, IsCorrectGroup, ListCorrElt, eEltCC, GRPret, LGen;
  LFaces:=__FaceSet(ePL);
  RedFaces:=[];
  for eFace in LFaces
  do
    rFace:=List(eFace, x->x[1]);
    Add(RedFaces, rFace);
  od;
  IsCycleEquivalent:=function(rFace1, rFace2)
    local len, revFace2, i, j, rotFace1, u;
    len:=Length(rFace1);
    revFace2:=Reversed(rFace2);
    for i in [1..len]
    do
      j:=i;
      rotFace1:=[];
      for u in [1..len]
      do
        Add(rotFace1, rFace1[j]);
        j:=NextIdx(len, j);
      od;
      if rotFace1=rFace2 or rotFace1=revFace2 then
        return true;
      fi;
    od;
    return false;
  end;
  IsInListReducedFaces:=function(rFace)
    local rFaceB;
    for rFaceB in RedFaces
    do
      if IsCycleEquivalent(rFace, rFaceB)=true then
        return true;
      fi;
    od;
    return false;
  end;
  TestCorrectnessCCperm:=function(ePermCC)
    local rFace, rFaceImg;
    for rFace in RedFaces
    do
      rFaceImg:=OnTuples(rFace, ePermCC);
      if IsInListReducedFaces(rFaceImg)=false then
        return false;
      fi;
    od;
    return true;
  end;
  IsCorrectGroup:=function(GRP)
    local eGenCC;
    for eGenCC in GeneratorsOfGroup(GRP)
    do
      if TestCorrectnessCCperm(eGenCC)=false then
        return false;
      fi;
    od;
    return true;
  end;
  if IsCorrectGroup(GRP) then
    return GRP;
  fi;
  ListCorrElt:=[];
  for eEltCC in GRP
  do
    if TestCorrectnessCCperm(eEltCC)=true then
      Add(ListCorrElt, eEltCC);
    fi;
  od;
  GRPret:=PersoGroupPerm(ListCorrElt);
  LGen:=SmallGeneratingSet(GRPret);
  return PersoGroupPerm(LGen);
end;


GroupPlan:=function(ePL)
  local CC, PreSymmetryGroup, SymmetryGroup, SymmetryGroupEdge, GPU, FunctionSymmetry, RecFlag;
  CC:=CellComplex(ePL);
  PreSymmetryGroup:=SymmetryGroupVertexColoredGraph(CC.GraphHasse, CC.ThePartition);
  SymmetryGroup:=ReduceToAdmissibleSymmetries(ePL, CC, PreSymmetryGroup);
  RecFlag:=GetAllFlagsFromCellComplex(CC, ePL);
  FunctionSymmetry:=function(GRP)
    return MapInformationSymmetryGroup(CC, GRP, RecFlag);
  end;
  GPU:=FunctionSymmetry(SymmetryGroup);
  SymmetryGroupEdge:=ReduceActionToEdge(CC, SymmetryGroup);
  return rec(CC:=CC,
             SymmetryGroup:=SymmetryGroup,
             SymmetryGroupEdge:=SymmetryGroupEdge,
             GenSymbol:=GPU.GenSymbol,
             GenSymbolLatex:=GPU.GenSymbolLatex,
             TotalGroup:=GPU,
             FunctionSymmetry:=FunctionSymmetry);
end;


PlanGraphOrientedPreparationParametrization:=function(PlanGraphOriented)
  local DualPGO, CC, VEF, GRP, VertSet, EdgeSet, FaceSet, ListFlags1, ListFlags, ListCorrespondingDE, eVert, eEdge, fEdge, INTS, V1, V2, eFace, StabilizedSet, FlagMapping, eFlag, ListGenOrig, ListGenMapped, iGen, eGen, phi, LER, RotationGroup, ListGen, iFlag, GrpFlag, GrpStab, MorphismFaceFlag, MorphismFlagFlag1, GroupFlag1, GroupCentralizer;
  DualPGO:=DualGraphOriented(PlanGraphOriented);
  CC:=PlanGraphOrientedToCellComplex(DualPGO);
  VEF:=CC.VEF;
  GRP:=AutGroupGraph(CC.GraphHasse);
  
  VertSet:=CC.VEF.VertSet;
  EdgeSet:=CC.VEF.EdgeSet;
  FaceSet:=CC.VEF.FaceSet;
  ListFlags1:=[];
  ListFlags:=[];
  ListCorrespondingDE:=[];
  for eVert in VertSet
  do
    for eEdge in EdgeSet
    do
      INTS:=Intersection(Set(eEdge), Set(eVert));
      if Length(INTS)=1 then
        V1:=INTS[1];
        V2:=Difference(Set(eEdge), INTS)[1];
        for eFace in FaceSet
        do
          if Position(eFace, V1)<>fail then
            Add(ListFlags1, [eVert, eEdge, eFace]);
            Add(ListCorrespondingDE, V1);
            Add(ListFlags, [eVert, eEdge, eFace]);
          fi;
          if Position(eFace, V2)<>fail then
            Add(ListFlags, [eVert, eEdge, eFace]);
          fi;
        od;
      fi;
    od;
  od;
  if Length(FaceSet)=1 then
    return rec(CC:=CC,
             ListCorrespondingDE:=ListCorrespondingDE,
             ListFlags1:=ListFlags1,
             PlanGraphOriented:=DualPGO,
             VEF:=VEF,
             RotationGroupFlag1:=Group(()) );
  fi;

  StabilizedSet:=[];
  for eFlag in ListFlags1
  do
    AddSet(StabilizedSet, Position(ListFlags, eFlag));
  od;
  FlagMapping:=function(eFlag, eGen)
    local pos1, pos2, pos3, pos1b, pos2b, pos3b;
    pos1:=Position(CC.ListCells, eFlag[1]);
    pos2:=Position(CC.ListCells, eFlag[2]);
    pos3:=Position(CC.ListCells, eFlag[3]);
    pos1b:=OnPoints(pos1, eGen);
    pos2b:=OnPoints(pos2, eGen);
    pos3b:=OnPoints(pos3, eGen);
    return [CC.ListCells[pos1b], CC.ListCells[pos2b], CC.ListCells[pos3b]];
  end;
  ListGenOrig:=GeneratorsOfGroup(GRP);
  ListGenMapped:=[];
  for iGen in [1..Length(ListGenOrig)]
  do
    eGen:=ListGenOrig[iGen];
    LER:=[];
    for iFlag in [1..Length(ListFlags)]
    do
      eFlag:=ListFlags[iFlag];
      Add(LER, Position(ListFlags, FlagMapping(eFlag, eGen)));
    od;
    Add(ListGenMapped, PermList(LER));
  od;
  GrpFlag:=PersoGroupPerm(ListGenMapped);
  GrpStab:=Stabilizer(GrpFlag, StabilizedSet, OnSets);
  ListGen:=[];
  MorphismFaceFlag:=GroupHomomorphismByImages(GRP, GrpFlag, ListGenOrig, ListGenMapped);
  RotationGroup:=PreImage(MorphismFaceFlag, GrpStab);
  for eGen in GeneratorsOfGroup(RotationGroup)
  do
    LER:=[];
    for iFlag in [1..Length(ListFlags1)]
    do
      eFlag:=ListFlags1[iFlag];
      Add(LER, Position(ListFlags1, FlagMapping(eFlag, eGen)));
    od;
    Add(ListGen, PermList(LER));
  od;
  GroupFlag1:=PersoGroupPerm(ListGen);
#  Print("Computing Centralizer\n");
#  GroupCentralizer:=Centralizer(SymmetricGroup(Length(ListFlags1)), Group([DualPGO.invers, DualPGO.next]));
#  Print("Centralizer computed\n");
#  Print("Iso=", IsomorphismGroups(GroupCentralizer, GroupFlag1), "\n");
#  Print("Order=", Order(GroupCentralizer), "\n");


  MorphismFlagFlag1:=GroupHomomorphismByImages(RotationGroup, GroupFlag1, GeneratorsOfGroup(RotationGroup), ListGen);
  return rec(CC:=CC, GRP:=GRP, RotationGroup:=RotationGroup,
             ListFlags:=ListFlags,
             ListCorrespondingDE:=ListCorrespondingDE,
             ListFlags1:=ListFlags1,
             PlanGraphOriented:=DualPGO,
             VEF:=VEF,
             FlagMapping:=FlagMapping,
             RotationGroupFlag:=GrpStab, 
             RotationGroupFlag1:=GroupFlag1,
             MorphismFaceFlag:=MorphismFaceFlag,
             MorphismFlagFlag1:=MorphismFlagFlag1);
end;

TorusTranslationSubgroup:=function(PLE)
  local GrpRot, CC, nbO, FuncIsTranslation, FuncGroup, ListGen, GrpSize, FuncInsert, eElt;
  GrpRot:=PLE.RotationGroup;
  CC:=PLE.CC;
  nbO:=CC.GraphHasse.order;
  FuncIsTranslation:=function(TheRot)
    local iFace;
    for iFace in [1..nbO]
    do
      if OnPoints(iFace, TheRot)=iFace then
        return false;
      fi;
    od;
    return true;
  end;
  ListGen:=[()];
  GrpSize:=1;
  FuncInsert:=function(OneTrans)
    local nbS, ListNew;
    ListNew:=Union(ListGen, [OneTrans]);
    nbS:=Order(PersoGroupPerm(ListNew));
    if nbS>GrpSize then
      ListGen:=ShallowCopy(ListNew);
      GrpSize:=nbS;
    fi;
  end;
  for eElt in GrpRot
  do
    if eElt<>() then
      if FuncIsTranslation(eElt)=true then
        FuncInsert(eElt);
      fi;
    fi;
  od;
  return PersoGroupPerm(ListGen);
end;




OrdAdjToPlanGraph:=function(OrdAdj)
  local LDE, PL, iDE, DE1, DE2, DE3, pos1, pos2, pos3;
  LDE:=ListDirectedEdges(OrdAdj);
  PL:=[];
  for iDE in [1..Length(LDE)]
  do
    DE1:=ReverseDE(OrdAdj, LDE[iDE]);
    DE2:=NextDE(OrdAdj, LDE[iDE]);
    DE3:=PrevDE(OrdAdj, LDE[iDE]);
    pos1:=Position(LDE, DE1);
    pos2:=Position(LDE, DE2);
    pos3:=Position(LDE, DE3);
    PL[iDE]:=[pos1, pos2, pos3];
  od;
  return rec(Struct:=PL);
end;


__PlanGraphToABC:=function(PlanGraph)
  local VEF, EdgeSet, FaceSet, ListFlag, iVert, jVert, LSfac, fFac, PosA, PosB, PosC, ListA, ListB, ListC, iPath, jPath, fPath, ePath, eEdge;
  VEF:=PlanGraphToVEFsecond(PlanGraph);
  EdgeSet:=VEF[2];
  FaceSet:=VEF[3];
  ListFlag:=[];
  for eEdge in EdgeSet
  do
    iVert:=eEdge[1][1];
    jVert:=eEdge[2][1];
    LSfac:=[];
    for fFac in FaceSet
    do
      if Length(Intersection(Set(fFac), Set(eEdge)))>0 then
        Add(LSfac, fFac);
      fi;
    od;
    Add(ListFlag, [iVert, eEdge, LSfac[1]]);
    Add(ListFlag, [jVert, eEdge, LSfac[1]]);
    Add(ListFlag, [iVert, eEdge, LSfac[2]]);
    Add(ListFlag, [jVert, eEdge, LSfac[2]]);
  od;
  ListA:=[];
  ListB:=[];
  ListC:=[];
  for iPath in [1..Length(ListFlag)]
  do
    ePath:=ListFlag[iPath];
    PosA:=[];
    PosB:=[];
    PosC:=[];
    for jPath in [1..Length(ListFlag)]
    do
      fPath:=ListFlag[jPath];
      if fPath[2]=ePath[2] and fPath[3]=ePath[3] then
        Add(PosA, jPath);
      fi;
      if fPath[1]=ePath[1] and fPath[3]=ePath[3] then
        Add(PosB, jPath);
      fi;
      if fPath[1]=ePath[1] and fPath[2]=ePath[2] then
        Add(PosC, jPath);
      fi;
    od;
    if Length(PosA)<>2 or Length(PosB)<>2 or Length(PosC)<>2 then
      Print("Error, Poset not Eulerian\n");
      return false;
    fi;
    ListA[iPath]:=Difference(PosA, [iPath])[1];
    ListB[iPath]:=Difference(PosB, [iPath])[1];
    ListC[iPath]:=Difference(PosC, [iPath])[1];
  od;
  return rec(permA:=PermList(ListA), permB:=PermList(ListB), permC:=PermList(ListC), nbP:=Length(ListFlag), ListFlag:=ListFlag);
end;








__IsOrientedABC:=function(ABC)
  local ListStatus, ListMatched, NbMatched, iP, ListOdd, ListEven, ListAdj, iAdj, i;
  ListStatus:=[];
  ListMatched:=[];
  for i in [1..ABC.nbP]
  do
    Add(ListStatus, -1);
    Add(ListMatched, 0);
  od;  
  NbMatched:=0;
  ListStatus[1]:=1;
  while(NbMatched<ABC.nbP)
  do
    for iP in [1..ABC.nbP]
    do
      if ListMatched[iP]=0 and ListStatus[iP]<>-1 then
        ListAdj:=[OnPoints(iP, ABC.permA), OnPoints(iP, ABC.permB), OnPoints(iP, ABC.permC)];
        ListMatched[iP]:=1;
        NbMatched:=NbMatched+1;
        for i in [1..3]
        do
          iAdj:=ListAdj[i];
          if ListStatus[iP]=ListStatus[iAdj] then
            return false;
          fi;
          ListStatus[iAdj]:=1-ListStatus[iP];
        od;
      fi;
    od;
  od;
  ListOdd:=[];
  ListEven:=[];
  for iP in [1..ABC.nbP]
  do
    if ListStatus[iP]=1 then
      Add(ListOdd, iP);
    fi;
    if ListStatus[iP]=0 then
      Add(ListEven, iP);
    fi;
  od;
  return rec(ListOdd:=ListOdd, ListEven:=ListEven);
end;




__ABCToVEF:=function(ABC)
  local SetPath, GroupVert, GroupEdge, GroupFace, VertSet, EdgeSet, FaceSet;
  SetPath:=[1..ABC.nbP];
  GroupVert:=Group([ABC.permB, ABC.permC]);
  GroupEdge:=Group([ABC.permA, ABC.permC]);
  GroupFace:=Group([ABC.permA, ABC.permB]);
  VertSet:=Orbits(GroupVert, SetPath, OnPoints);
  EdgeSet:=Orbits(GroupEdge, SetPath, OnPoints);
  FaceSet:=Orbits(GroupFace, SetPath, OnPoints);
  return rec(VertSet:=VertSet, EdgeSet:=EdgeSet, FaceSet:=FaceSet);
end;



__ABCtoCellComplex:=function(ABC)
  local VEF, VertSet, EdgeSet, FaceSet, NbVert, NbEdge, NbFace, NbU, Gra, i, j, eVert, eEdge, eFace;
  VEF:=__ABCToVEF(ABC);
  VertSet:=VEF.VertSet;
  EdgeSet:=VEF.EdgeSet;
  FaceSet:=VEF.FaceSet;
  NbVert:=Length(VertSet);
  NbEdge:=Length(EdgeSet);
  NbFace:=Length(FaceSet);
  NbU:=NbVert+NbEdge+NbFace;
  Gra:=NullGraph(Group(()), NbU+3);
  #
  #
  # Computation of the automorphism group
  #
  #
  #
  for i in [1..NbVert]
  do
    for j in [NbVert+1..NbVert+NbEdge]
    do
      eVert:=VertSet[i];
      eEdge:=EdgeSet[j-NbVert];
      if Length(Intersection(eVert, eEdge))=2 then
        AddEdgeOrbit(Gra, [i,j]);
      fi;
    od;
  od;
  for i in [NbVert+1..NbVert+NbEdge]
  do
    for j in [NbVert+NbEdge+1..NbVert+NbEdge+NbFace]
    do
      eEdge:=EdgeSet[i-NbVert];
      eFace:=FaceSet[j-NbVert-NbEdge];
      if Length(Intersection(eEdge, eFace))=2 then
        AddEdgeOrbit(Gra, [i,j]);
      fi;
    od;
  od;
  AddEdgeOrbit(Gra, [NbU+2, NbU+3]);
  for i in [NbVert+1..NbVert+NbEdge]
  do
    AddEdgeOrbit(Gra, [i, NbU+1]);
  od;
  for i in [NbVert+NbEdge+1..NbVert+NbEdge+NbFace]
  do
    AddEdgeOrbit(Gra, [i,NbU+2]);
  od;    
  return Gra;
end;





__IsIsomorphicABC:=function(ABC1, ABC2)
  return IsIsomorphicGraph(__ABCtoCellComplex(ABC1), __ABCtoCellComplex(ABC2));
end;




__TopologicalTypeABC:=function(ABC)
  local Ort, ABCort, nbVert, nbEdge, nbFace, VEF, EulerChar;
  Ort:=__IsOrientedABC(ABC);
  if Ort=false then
    ABCort:=false;
  else
    ABCort:=true;
  fi;
  VEF:=__ABCToVEF(ABC);
  nbVert:=Length(VEF.VertSet);
  nbEdge:=Length(VEF.EdgeSet);
  nbFace:=Length(VEF.FaceSet);
  EulerChar:=nbVert+nbFace-nbEdge;
  return rec(Orientation:=ABCort, EulerChar:=EulerChar);
end;






ABCsymmetries:=function(ABC, symmetry)
  if symmetry=0 then
    return ABC;
  fi;
  if symmetry=1 then
    return rec(permA:=ABC.permC, permB:=ABC.permB, permC:=ABC.permA, nbP:=ABC.nbP);
  fi;
  if symmetry=2 then
    return rec(permA:=ABC.permC*ABC.permA, permB:=ABC.permB, permC:=ABC.permC, nbP:=ABC.nbP);
  fi;
  if symmetry=3 then
    return rec(permA:=ABC.permC, permB:=ABC.permB, permC:=ABC.permC*ABC.permA, nbP:=ABC.nbP);
  fi;
  if symmetry=4 then
    return rec(permA:=ABC.permC*ABC.permA, permB:=ABC.permB, permC:=ABC.permA, nbP:=ABC.nbP);
  fi;
  if symmetry=5 then
    return rec(permA:=ABC.permA, permB:=ABC.permB, permC:=ABC.permC*ABC.permA, nbP:=ABC.nbP);
  fi;
  Error("symmetry should be 0,1,2,3,4, or 5");
end;








ABCToPlanGraph:=function(ABC)
  local Ort, SetPath, VertexSet, z, v, Sequence, NewPlanGraph, OrdAdj, jVert, iVert, iAdj, iElt, jElt;
  Ort:=__IsOrientedABC(ABC);
  if Ort=false then
    return false;
  fi;
  SetPath:=Ort.ListOdd;
  VertexSet:=[];
  while (Length(SetPath)>0)
  do
    z:=SetPath[1];
    Sequence:=ShallowCopy([z]);
    v:=OnPoints(z, ABC.permB*ABC.permC);
    while(v<>z) 
    do
      Add(Sequence, v);
      v:=OnPoints(v, ABC.permB*ABC.permC);
    od;
    Add(VertexSet, Sequence);
    SetPath:=Difference(SetPath, Sequence);
  od;
  NewPlanGraph:=[];
  for iVert in [1..Length(VertexSet)]
  do
    OrdAdj:=[];
    for iAdj in [1..Length(VertexSet[iVert])]
    do
      iElt:=VertexSet[iVert][iAdj];
      jElt:=OnPoints(iElt, ABC.permA*ABC.permC);
      for jVert in [1..Length(VertexSet)]
      do
        if jElt in VertexSet[jVert] then
          Add(OrdAdj, jVert);
        fi;
      od;
    od;
    NewPlanGraph[iVert]:=OrdAdj;
  od;
  return NewPlanGraph;
end;









PlanGraphToPoset:=function(PlanGraph)
  local VEF, ListInc, nb1, nb2, nb3, nb4, nbObj, iVert, iEdge, iFac, eEdge, FuncTestIncVertFac;
  VEF:=PlanGraphToVEFsecond(PlanGraph);
  ListInc:=[];
  nb1:=VEF[1];
  nb2:=Length(VEF[2]);
  nb3:=nb1+nb2;
  nb4:=Length(VEF[3]);
  nbObj:=nb3+nb4;
  for iVert in [1..nb1]
  do
    for iEdge in [1..nb2]
    do
      eEdge:=VEF[2][iEdge];
      if eEdge[1][1]=iVert or eEdge[2][1]=iVert then
        Add(ListInc, [iVert, nb1+iEdge]);
      fi;
    od;
  od;
  #
  FuncTestIncVertFac:=function(iV, eFac)
    local fEdge;
    for fEdge in eFac
    do
      if fEdge[1]=iV then
        return true;
      fi;
    od;
    return false;
  end;
  #
  for iEdge in [1..nb2]
  do
    for iFac in [1..nb4]
    do
      if Intersection(VEF[2][iEdge], VEF[3][iFac])<>[] then
        Add(ListInc, [iEdge+nb1, iFac+nb3]);
      fi;
    od;
  od;
  #
  for iVert in [1..nb1]
  do
    for iFac in [1..nb4]
    do
      if FuncTestIncVertFac(iVert, VEF[3][iFac])=true then
        Add(ListInc, [iVert, nb3+iFac]);
      fi;
    od;
  od;
  #
  for iVert in [1..nbObj]
  do
    Add(ListInc, [iVert, nbObj+1]);
    Add(ListInc, [nbObj+2, iVert]);
  od;
  #
  Add(ListInc, [nbObj+2, nbObj+1]);
  return ListInc;
end;












#
#
# reverse left-right orientation of the planar graph.
ReversePlanGraph:=function(PlanGraph)
  local iVert, PlanGraphNew;
  PlanGraphNew:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    PlanGraphNew[iVert]:=Reversed(PlanGraph[iVert]);
  od;
  return PlanGraphNew;
end;






DualGraph:=function(PlanGraph)
  local Faces, iFac, eFac, jFac, Rev, PlanGraphNew, LADJ, iVert;
  Faces:=PlanGraphToVEFsecond(PlanGraph)[3];
  PlanGraphNew:=[];
  for iFac in [1..Length(Faces)]
  do
    eFac:=Faces[iFac];
    LADJ:=ShallowCopy([]);
    for iVert in [1..Length(eFac)]
    do
      Rev:=ReverseDE(PlanGraph, eFac[iVert]);
      for jFac in [1..Length(Faces)]
      do
        if Rev in Faces[jFac] then
          LADJ[iVert]:=jFac;
        fi;
      od;
    od;
    PlanGraphNew[iFac]:=LADJ;
  od;
  return rec(VertexSet:=Faces, PlanGraph:=PlanGraphNew);
end;









ShiftByZigZag:=function(PlanGraph, ZZ, k)
  local LE, letter, SequenceOne, SequenceTwo, PositionOne, PositionTwo, iZZL, ZZL, DE, ShiftedSequenceOne, ShiftedPositionOne, PlanGraphNew, iVert;
  LE:=Length(ZZ)/2;
  letter:=ZZ[1][1];
  SequenceOne:=[];
  SequenceTwo:=[];
  # finding the lifted sequences
  for iZZL in [1..LE]
  do
    ZZL:=ZZ[2*iZZL-1][2];
    Add(SequenceOne, ZZL[1]);
    if letter="P" then
      DE:=NextDE(PlanGraph, ZZL);
    else
      DE:=PrevDE(PlanGraph, ZZL);
    fi;
    Add(SequenceTwo, PlanGraph[DE[1]][DE[2]]);
  od;
  # finding the sequences of positions
  Print(SequenceOne, "\n");
  Print(SequenceTwo, "\n");
  PositionOne:=[];
  PositionTwo:=[];
  for iZZL in [1..LE]
  do
    PositionOne[iZZL]:=Position(PlanGraph[SequenceOne[iZZL]],SequenceTwo[iZZL]);
    PositionTwo[iZZL]:=Position(PlanGraph[SequenceTwo[iZZL]],SequenceOne[iZZL]);
  od;
  ShiftedSequenceOne:=[];
  ShiftedPositionOne:=[];
  for iZZL in [1..LE]
  do
    ShiftedSequenceOne[iZZL]:=SequenceOne[NextKIdx(LE, iZZL, k)];
    ShiftedPositionOne[iZZL]:=PositionOne[NextKIdx(LE, iZZL, k)];
  od;
  PlanGraphNew:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    PlanGraphNew[iVert]:=ShallowCopy(PlanGraph[iVert]);
  od;
  for iZZL in [1..LE]
  do
    PlanGraphNew[SequenceTwo[iZZL]][PositionTwo[iZZL]]:=ShiftedSequenceOne[iZZL];
    PlanGraphNew[ShiftedSequenceOne[iZZL]][ShiftedPositionOne[iZZL]]:=SequenceTwo[iZZL];
  od;
  return PlanGraphNew;
end;



ReverseCCL:=function(PlanGraph, CCL)
  local JO, i;
  JO:=[];
  for i in [1..Length(CCL)]
  do
    JO[i]:=ReverseDE(PlanGraph, CCL[i]);
  od;
  return Reversed(JO);
end;



#
#
# Canonicalization assuming that three determines everything.
ThreeCanonicalization:=function(Sequence)
  local n, min, idx, ZZQ, i, iN, iNN, A;
  n:=Length(Sequence);
  min:=[Sequence[1], Sequence[2],Sequence[3]];
  idx:=1;
  for i in [1..n]
  do
    iN:=NextIdx(n,i);
    iNN:=NextIdx(n,iN);
    A:=[Sequence[i], Sequence[iN], Sequence[iNN]];
    if A<min then
      min:=A;
      idx:=i;
    fi;
  od;
  ZZQ:=[];
  for i in [idx..n]
  do
    Add(ZZQ, Sequence[i]);
  od;
  for i in [1..idx-1]
  do
    Add(ZZQ, Sequence[i]);
  od;
 return ZZQ;
end;



CCaction:=function(CCpair, g)
  local CC1, CC2, CCpu1, CCpu2, i;
  CC1:=CCpair[1];
  CC2:=CCpair[2];
  CCpu1:=[];
  CCpu2:=[];
  for i in [1..Length(CC1)]
  do
    CCpu1[i]:=OnPoints(CC1[i],g);
    CCpu2[i]:=OnPoints(CC2[i],g);
  od;
  return Set([ThreeCanonicalization(CCpu1), ThreeCanonicalization(CCpu2)]);
end;





CCtoCanonicSequence:=function(CC)
  local LU, j;
  LU:=[];
  for j in [1..Length(CC)]
  do
    LU[j]:=CC[j][1];
  od;
  return Set([ThreeCanonicalization(LU), ThreeCanonicalization(Reversed(LU))]);
end;


#
#
# LZZ is the output of the function ZigZag
# Group a subgroup of Aut(PlanGraph)
CCorbits:=function(ListCC, G)
  local CCelt, u, O, LSorbit, SizeO, iO;
  CCelt:=[];
  for u in ListCC
  do
    Add(CCelt, CCtoCanonicSequence(u));
  od;
  O:=Orbits(G, CCelt, CCaction);
  LSorbit:=[];
  SizeO:=[];
  for iO in [1..Length(O)]
  do
    LSorbit[iO]:=O[iO][1][1];
    SizeO[iO]:=Length(O[iO]);
  od;
  return rec(ListOrbits:=LSorbit, SizeOrbits:=SizeO);
end;





#
# PlanGraph must be 4-valent.
CentralCircuit:=function(PlanGraph)
  local ListTot, ListCircuit, z, Sequence, SequenceRev, v, LSreturn, Self, eCirc, Circ, SetCirc, u, iVert, LSstring, LSprovsimple, LSprovself, FuncSort, INCD, IncidenceVertexCC, iCC, jCC, ROW, MATRintersect, ListIntVector, SE, IntVector, String1, String2, LSself, 
  iSymbol, FuncReverseDE, DowkerChain, iPos, jPos, ListStand, DE, DErev, DEnext, ListSymbol, len, k, ksec, CircuitWork, SignStand, iCirc, FuncReverseCircuitDE, ListPossible, Ups, iter, iDE, ListSizes,
  ListFace, ListStatus, ListDone, ListOdd, ListEven, eFac, fFac, RevertedFac, i, j, nbZero, eEdge, test, DE1, DE2, rDE1, rDE2, p1, p2, eInt, MatrixIntersectionWithTypes, MatrixIntersectionWithTypesI, MatrixIntersectionWithTypesII, SetDE, depl, ListIntVectorWithType, SIG, ListInvariants, CCuniformity, CCbalancedness, CCset, SetINTV, INTV, Pair, iC, CCL, 
  IsTight, SelfIntRailroad, BoundingRailroad, ListRailroad, ListRailroadCanonicalized, ListMatchingCircuitRailroad, Bcan, PosCC, BRR, nbFace, eRR;

  ListTot:=ListDirectedEdges(PlanGraph);
  ListCircuit:=[];
  while (Length(ListTot)>0)
  do
    z:=ListTot[1];
    Sequence:=ShallowCopy([z]);
    SequenceRev:=ShallowCopy([ReverseDE(PlanGraph, z)]);
    v:=NextDE(PlanGraph, NextDE(PlanGraph, ReverseDE(PlanGraph, z)));
    while(v<>z)
    do
      Add(Sequence, v);
      Add(SequenceRev, ReverseDE(PlanGraph, v));
      v:=NextDE(PlanGraph, NextDE(PlanGraph, ReverseDE(PlanGraph, v)));
    od;
    Add(ListCircuit, Sequence);
    ListTot:=Difference(ListTot, Union(Sequence, SequenceRev));
  od;


  ListFace:=Set(PlanGraphToVEFsecond(PlanGraph)[3]);
  nbFace:=Length(ListFace);
  BoundingRailroad:=function(CCL)
    local ilPos, ListIncFace, FacPos, ListOppositeCentral, eDir, eFac, IsBoundaryRailroad, Pos;
    ilPos:=1;
    IsBoundaryRailroad:=true;
    ListIncFace:=[];
    ListOppositeCentral:=[];
    while(ilPos<=Length(CCL))
    do
      FacPos:=1;
      eDir:=CCL[ilPos];
      while(FacPos<=nbFace)
      do
        Pos:=Position(ListFace[FacPos], eDir);
        if Pos<>fail then
          eFac:=ListFace[FacPos];
          if Length(eFac)<>4 then
            IsBoundaryRailroad:=false;
          else
            Add(ListIncFace, eFac);
            Add(ListOppositeCentral, eFac[NextKIdx(4, Pos, 2)]);
          fi;
          break;
        fi;
        FacPos:=FacPos+1;
      od;
      if IsBoundaryRailroad=false then
        break;
      fi;
      ilPos:=ilPos+1;
    od;
    if IsBoundaryRailroad=false then
      return false;
    else
      return [ListIncFace, Reversed(ListOppositeCentral)];
    fi;
  end;


  ListRailroad:=[];
  ListRailroadCanonicalized:=[];
  ListMatchingCircuitRailroad:=[];
  for iCirc in [1..Length(ListCircuit)]
  do
    for CCL in [ListCircuit[iCirc], ReverseCCL(PlanGraph, ListCircuit[iCirc])]
    do
      BRR:=BoundingRailroad(CCL);
      if BRR<>false then
        Bcan:=Set([ThreeCanonicalization(BRR[1]), ThreeCanonicalization(Reversed(BRR[1]))]);
        PosCC:=Position(ListRailroadCanonicalized, Bcan);
        if PosCC=fail then
          Add(ListRailroadCanonicalized, Bcan);
          Add(ListRailroad, BRR[1]);
          Add(ListMatchingCircuitRailroad, [iCirc]);
        else
          Add(ListMatchingCircuitRailroad[PosCC], iCirc);
        fi;
      fi;
    od;
  od;



  #
  #
  # create the chess bipartition of faces
  ListStatus:=[];
  ListDone:=[];
  for i in [1..Length(ListFace)]
  do
    ListStatus[i]:=0;
    ListDone[i]:=0;
  od;
  ListStatus[1]:=1;
  while(true)
  do
    nbZero:=0;
    for i in [1..Length(ListFace)]
    do
      if ListStatus[i]=0 then
        nbZero:=nbZero+1;
      fi;
      if ListStatus[i]<>0 and ListDone[i]=0 then
        ListDone[i]:=1;
        eFac:=ListFace[i];
        RevertedFac:=[];
        for eEdge in eFac
        do
          AddSet(RevertedFac, ReverseDE(PlanGraph, eEdge));
        od;
        for j in [1..Length(ListFace)]
        do
          if ListStatus[j]=0 then
            if Length(Intersection(RevertedFac, ListFace[j]))>0 then
              ListStatus[j]:=3-ListStatus[i];
            fi;
          fi;
        od;
      fi;
    od;
    if nbZero=0 then
      break;
    fi;
  od;
  ListOdd:=[];
  ListEven:=[];
  for i in [1..Length(ListFace)]
  do
    if ListStatus[i]=1 then
      AddSet(ListOdd, ListFace[i]);
    else
      AddSet(ListEven, ListFace[i]);
    fi;
  od;

  #
  #
  # computation of Dowker-Thistlethwaite code of the corresponding 
  # alternating link.
  FuncReverseDE:=function(DE)
    return NextDE(PlanGraph, NextDE(PlanGraph, DE));
  end;
  FuncReverseCircuitDE:=function(ListDE)
    local U, jDE;
    U:=[];
    for jDE in [1..Length(ListDE)]
    do
      U[jDE]:=NextDE(PlanGraph, NextDE(PlanGraph, ListDE[jDE]));
    od;
    return Reversed(U);
  end;


  #
  # Dowker chains
  #
  if Length(ListCircuit)=1 then
    len:=Length(ListCircuit[1])/2;
    DowkerChain:=Concatenation(String(len), "  1");
    for iPos in [1..len]
    do
      DE:=ListCircuit[1][2*iPos-1];
      DEnext:=NextDE(PlanGraph, DE);
      jPos:=Position(ListCircuit[1], DEnext);
      if jPos=fail then
        jPos:=Position(ListCircuit[1], FuncReverseDE(DEnext));
      fi;
      DowkerChain:=Concatenation(DowkerChain, " ", String(jPos));
    od;
  else
    ListSymbol:=[];
    ListStand:=[];
    # 1 stand for overpass, 0 stands for underpass
    ListPossible:=[];
    ListSizes:=[Length(ListCircuit[1])];
    for iSymbol in [1..Length(ListCircuit[1])]
    do
      DE:=NextDE(PlanGraph, ListCircuit[1][iSymbol]);
      DErev:=FuncReverseDE(DE);
      if not(DE in Set(ListCircuit[1])) and not(DErev in Set(ListCircuit[1])) then
        AddSet(ListPossible, iSymbol);
      fi;
    od;
    k:=ListPossible[1];
    for iSymbol in [1..Length(ListCircuit[1])]
    do
      ListSymbol[iSymbol]:=ListCircuit[1][k];
      if (iSymbol mod 2)=1 then
        ListStand[iSymbol]:=1;
      else
        ListStand[iSymbol]:=0;
      fi;
      k:=NextIdx(Length(ListCircuit[1]), k);
    od;
    for iter in [2..Length(ListCircuit)]
    do
      ListPossible:=ShallowCopy([]);
      k:=-1;
      while(1=1)
      do
        k:=k+2;
        DE:=NextDE(PlanGraph, ListSymbol[k]);
        DErev:=FuncReverseDE(DE);
        if not(DE in Set(ListSymbol)) and not(DErev in Set(ListSymbol)) then
          break;
        fi;
      od;
      for iCirc in [2..Length(ListCircuit)]
      do
        if DE in Set(ListCircuit[iCirc]) then
          CircuitWork:=ListCircuit[iCirc];
          ListSizes[iter]:=Length(ListCircuit[iCirc]);
        fi;
        if DErev in Set(ListCircuit[iCirc]) then
          CircuitWork:=FuncReverseCircuitDE(ListCircuit[iCirc]);
          ListSizes[iter]:=Length(ListCircuit[iCirc]);
        fi;
      od;
      SignStand:=ListStand[k];
      ksec:=PrevIdx(Length(CircuitWork), Position(CircuitWork, DE));
      for iDE in [1..Length(CircuitWork)]
      do
        Add(ListSymbol, CircuitWork[ksec]);
        Add(ListStand, SignStand);
        ksec:=NextIdx(Length(CircuitWork), ksec);
        SignStand:=1-SignStand;
      od;
    od;
    len:=0;
    DowkerChain:="";
    for iCirc in [1..Length(ListCircuit)]
    do
      DowkerChain:=Concatenation(DowkerChain, "  ", String(ListSizes[iCirc]));
      len:=len+Length(ListCircuit[iCirc])/2;
    od;
    DowkerChain:=Concatenation(String(len), "  ", String(Length(ListCircuit)), DowkerChain);
    len:=Length(ListSymbol)/2;
    for iPos in [1..len]
    do
      DE:=NextDE(PlanGraph, ListSymbol[2*iPos-1]);
      jPos:=Position(ListSymbol, DE);
      if jPos=fail then
        jPos:=Position(ListSymbol, FuncReverseDE(DE));
      fi;
      if ListStand[2*iPos-1]=1 and ListStand[jPos]=0 then
        DowkerChain:=Concatenation(DowkerChain, "  ", String(jPos));
      else
        DowkerChain:=Concatenation(DowkerChain, "  ", String(-jPos));
      fi;
    od;
  fi;
  #
  #
  LSprovsimple:=[];
  LSprovself:=[];
  LSreturn:=[];
  LSself:=[];
  for eCirc in ListCircuit
  do
    Circ:=ShallowCopy([]);
    for iVert in [1..Length(eCirc)]
    do
      Circ[iVert]:=eCirc[iVert][1];
    od;
    SetCirc:=Set(Circ);
    Self:=ShallowCopy([]);
    for u in SetCirc
    do
      if PositionNthOccurrence(Circ, u,2)<>fail then
        Add(Self, u);
      fi;
    od;
    if Length(Self)=0 then
      Add(LSprovsimple, String(Length(Circ)));
    else
      Add(LSprovself, Concatenation(String(Length(Circ)),"_{", String(Length(Self)), "}"));
    fi;
    Add(LSself, Self);
    Add(LSreturn, Circ);
  od;
  #
  #
  IncidenceVertexCC:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    INCD:=[];
    for iCC in [1..Length(LSreturn)]
    do
      if iVert in LSreturn[iCC] then
        AddSet(INCD, iCC);
      fi;
    od;
    IncidenceVertexCC[iVert]:=INCD;
  od;
  #
  #
  MATRintersect:=[];
  for iCC in [1..Length(ListCircuit)]
  do
    ROW:=[];
    for jCC in [1..Length(ListCircuit)]
    do
      if iCC=jCC then
        ROW[jCC]:=Length(LSself[iCC]);
      else
        ROW[jCC]:=Length(Intersection(LSreturn[iCC],LSreturn[jCC]));
      fi;
    od;
    MATRintersect[iCC]:=ROW;
  od;
  #
  #
  #
  # intersection matrix with type
  MatrixIntersectionWithTypes:=[];
  MatrixIntersectionWithTypesI:=NullMat(Length(ListCircuit), Length(ListCircuit));
  MatrixIntersectionWithTypesII:=NullMat(Length(ListCircuit), Length(ListCircuit));
  for iVert in [1..Length(PlanGraph)]
  do
    SetDE:=Set([[iVert, 1], ReverseDE(PlanGraph, [iVert, 2])]);
    test:=0;
    for fFac in ListOdd
    do
      if IsSubset(Set(fFac), SetDE)=true then
        test:=1;
      fi;
    od;
#    Print("test=", test,"\n");
    if test=1 then
      DE1:=[iVert, 1];
      DE2:=[iVert, 2];
    else
      DE1:=[iVert, 2];
      DE2:=[iVert, 3];
    fi;
    rDE1:=ReverseDE(PlanGraph, DE1);
    rDE2:=ReverseDE(PlanGraph, DE2);
    SignStand:=1;
    p1:=0; p2:=0;
    for iCC in [1..Length(ListCircuit)]
    do
      if DE1 in ListCircuit[iCC] or rDE1 in ListCircuit[iCC] then
        p1:=iCC;
      fi;
      if DE2 in ListCircuit[iCC] or rDE2 in ListCircuit[iCC] then
        p2:=iCC;
      fi;
    od;
    if rDE1 in ListCircuit[p1] then
      SignStand:=-SignStand;
    fi;
    if rDE2 in ListCircuit[p2] then
      SignStand:=-SignStand;
    fi;
#    Print("SG=", SignStand, "\n");
    if SignStand=1 then
      MatrixIntersectionWithTypesI[p1][p2]:=MatrixIntersectionWithTypesI[p1][p2]+1;
      MatrixIntersectionWithTypesI[p2][p1]:=MatrixIntersectionWithTypesI[p2][p1]+1;
    else
      MatrixIntersectionWithTypesII[p1][p2]:=MatrixIntersectionWithTypesII[p1][p2]+1;
      MatrixIntersectionWithTypesII[p2][p1]:=MatrixIntersectionWithTypesII[p2][p1]+1;
    fi;
  od;
  ROW:=[];
  for iCC in [1..Length(ListCircuit)]
  do
    ROW:=[];
    for jCC in [1..Length(ListCircuit)]
    do
      Add(ROW, [MatrixIntersectionWithTypesI[iCC][jCC], MatrixIntersectionWithTypesII[iCC][jCC]]);
    od;
    Add(MatrixIntersectionWithTypes, ROW);
  od;


  if Length(ListRailroad)>0 then
    IsTight:=false;
  else
    IsTight:=true;
  fi;
  SelfIntRailroad:=false;
  for eRR in ListMatchingCircuitRailroad
  do
    for u in eRR
    do
      if MatrixIntersectionWithTypes[u][u]<>[0,0] then
        SelfIntRailroad:=true;
      fi;
    od;
  od;

  for iCC in [1..Length(ListCircuit)]
  do
    eInt:=ShallowCopy(MatrixIntersectionWithTypes[iCC][iCC]);
    eInt:=[eInt[1]/2, eInt[2]/2];
    MatrixIntersectionWithTypes[iCC][iCC]:=eInt;
  od;
  #
  #
  # intersection vectors
  ListIntVector:=[];
  ListIntVectorWithType:=[];
  for iCC in [1..Length(ListCircuit)]
  do
    SE:=[];
    for jCC in [1..Length(ListCircuit)]
    do
      if iCC<>jCC then
        Add(SE, MATRintersect[iCC][jCC]);
      fi;
    od;
    IntVector:=SyncTextOccurrence(Collected(SE));
    Add(ListIntVector, IntVector);
    SIG:=Concatenation("(", String(MatrixIntersectionWithTypes[iCC][iCC][1]),",",String(MatrixIntersectionWithTypes[iCC][iCC][2]),"); ");
    Add(ListIntVectorWithType, Concatenation(SIG, IntVector));
  od;  


  # CCuniformity and CCbalancedness
  ListInvariants:=[];
  for iCC in [1..Length(ListCircuit)]
  do
    SIG:=MatrixIntersectionWithTypes[iCC][iCC];
    Add(ListInvariants, [Length(ListCircuit[iCC]), SIG[1],SIG[2]]);
  od;
  if Length(Set(ListInvariants))=1 then
    CCuniformity:=true;
  else
    CCuniformity:=false;
  fi;
  CCset:=Set(ListInvariants);
  CCbalancedness:=true;
  for iC in [1..Length(CCset)]
  do
    SetINTV:=[];
    for iCC in [1..Length(ListCircuit)]
    do
      if ListInvariants[iCC]=CCset[iC] then
        INTV:=ShallowCopy([]);
        for jCC in [1..Length(ListCircuit)]
        do
          Pair:=MatrixIntersectionWithTypes[iCC][jCC];
          Add(INTV, Pair[1]+Pair[2]);
        od;
        Sort(INTV);
        Add(SetINTV, ShallowCopy(INTV));
      fi;
    od;
    if Length(Set(SetINTV))>1 then
      CCbalancedness:=false;
    fi;
  od;
  #
  #
  FuncSort:=function(A,B)
    if A[1]<B[1] then
      return true;
    else
      return false;
    fi;
  end;
  Sort(LSprovsimple, FuncSort);
  Sort(LSprovself, FuncSort);
  LSstring:="";
  String1:=SyncTextOccurrence(Collected(LSprovsimple));
  String2:=SyncTextOccurrence(Collected(LSprovself));
  if String1="" then
    LSstring:=String2;
  elif String2="" then
    LSstring:=String1;
  else
    LSstring:=Concatenation(String1, "; ", String2);
  fi;
  #
  #
  return rec(ListCircuit:=ListCircuit, ListOdd:=ListOdd, ListEven:=ListEven, MatrixIntersection:=MATRintersect, MatrixIntersectionWithTypes:=MatrixIntersectionWithTypes, ListIntersectionVector:=ListIntVector, IncidenceVertexCC:=IncidenceVertexCC, CCvector:=LSstring, Dowker:=DowkerChain, ListIntVectorWithType:=ListIntVectorWithType, CCuniformity:=CCuniformity, CCbalancedness:=CCbalancedness, ListRailRoad:=ListRailroad, ListMatchingCircuitRailroad:=ListMatchingCircuitRailroad, Tightness:=IsTight, SelfIntRailroad:=SelfIntRailroad);
end;




#
#
# this relies on a criterion of Michel Deza
# it works only for eSet of length 2.
TestSeparabilityCorrespondingLink:=function(PlanGraph, CC, eSet)
  local ListListVert, LV, eC, iCC, FuncIsMatching, iVert;
  ListListVert:=[];
  for iCC in eSet
  do
    LV:=[];
    for eC in CC.ListCircuit[iCC]
    do
      Add(LV, eC[1]);
    od;
    Add(ListListVert, LV);
  od;
  FuncIsMatching:=function(u, v)
    local ListModPos, eVert, pos;
    ListModPos:=[];
    for eVert in ListListVert[u]
    do
      pos:=Position(ListListVert[v], eVert);
      if pos<>fail then
        AddSet(ListModPos, pos mod 2);
      fi;
    od;
    if Length(ListModPos)=1 then
      return true;
    else
      return false;
    fi;
  end;
  if FuncIsMatching(1, 2)=false then
    return false;
  elif FuncIsMatching(2, 1)=false then
    return false;
  else
    return true;
  fi;    
end;




IsBorromean:=function(PlanGraph, CC)
  local eSet;
  for eSet in Combinations([1..Length(CC.ListCircuit)], 2)
  do
    if TestSeparabilityCorrespondingLink(PlanGraph, CC, eSet)=false then
      return false;
    fi;
  od;
  return true;
end;




#IsBruniann:=function(PlanGraph, CC)
#  local eSet, nbCC;
#  nbCC:=Length(CC.ListCircuit);
#  for eSet in Combinations([1..nbCC])
#  do
#    if Length(eSet)>0 and Length(eSet)<nbCC then
#      if TestTrivialityCorrespondingLink(PlanGraph, CC, eSet)=false then
#        return false;
#      fi;
#    fi;
#  od;
#  return true;
#end;


# procedure used for generating $i$-hedrite out of fundamental
# $5$-hedrite and octahedrites.
AddDigon:=function(PlanGraph, eDE1)
  local TheVert, eDE2, eDE3, eDE4, Vert1, Vert2, Vert3, Vert4, NewPlanGraph, nbV, iVert, LADJ, i, ListDE, ListVert, fDE, Pos;
  TheVert:=eDE1[1];
  eDE2:=NextDE(PlanGraph, eDE1);
  eDE3:=NextDE(PlanGraph, eDE2);
  eDE4:=NextDE(PlanGraph, eDE3);
  Vert1:=PlanGraph[TheVert][eDE1[2]];
  Vert2:=PlanGraph[TheVert][eDE2[2]];
  Vert3:=PlanGraph[TheVert][eDE3[2]];
  Vert4:=PlanGraph[TheVert][eDE4[2]];
  NewPlanGraph:=[];
  nbV:=Length(PlanGraph);
  ListDE:=[eDE1, eDE2, eDE3, eDE4];
  ListVert:=[TheVert, nbV+1, nbV+1, TheVert];
  for iVert in [1..nbV+1]
  do
    if iVert=TheVert then
      LADJ:=[nbV+1, nbV+1, Vert4, Vert1];
    elif iVert=nbV+1 then
      LADJ:=[TheVert, TheVert, Vert2, Vert3];
    elif iVert in [Vert1, Vert2, Vert3, Vert4] then
      LADJ:=[];
      for i in [1..4]
      do
        fDE:=ReverseDE(PlanGraph, [iVert, i]);
        Pos:=Position(ListDE, fDE);
        if Pos<>fail then
          Add(LADJ, ListVert[Pos]);
        else
          Add(LADJ, PlanGraph[iVert][i]);
        fi;
      od;
    else
      LADJ:=PlanGraph[iVert];
    fi;
    Add(NewPlanGraph, LADJ);
  od;
  return NewPlanGraph;
end;


GenerateAllDigonSplitting:=function(PlanGraph, MaxNbVert)
  local ListFinished, ListToBeWorkedNew, ListPlan, ListInv, ePlan, ListFaces, ListPos, ListGonality, iFac, ePair, eFac, fFac, ListRev, u, fPlan, i;
  ListFinished:=[];
  ListToBeWorkedNew:=[PlanGraph];
  while(Length(ListToBeWorkedNew)>0)
  do
    ListPlan:=[];
    ListInv:=[];
    for ePlan in ListToBeWorkedNew
    do
      ListFaces:=PlanGraphToVEFsecond(ePlan)[3];
      ListPos:=[];
      ListGonality:=[];
      for iFac in [1..Length(ListFaces)]
      do
        if Length(ListFaces[iFac])<4 then
          Add(ListPos, iFac);
          Add(ListGonality, Length(ListFaces[iFac]));
        fi;
      od;
      for ePair in Combinations(ListPos, 2)
      do
        eFac:=ListFaces[ePair[1]];
        fFac:=ListFaces[ePair[2]];
        ListRev:=[];
        for i in [1..Length(eFac)]
        do
          Add(ListRev, NextDE(ePlan, NextDE(ePlan, eFac[i])));
        od;
        for u in Intersection(ListRev, fFac)
        do
          fPlan:=AddDigon(ePlan, u);
          if Length(fPlan) <= MaxNbVert then
            if Is3connected(PlanGraphToGRAPE(fPlan))=true then
              Add(ListPlan, fPlan);
              Add(ListInv, 0);
            fi;
          fi;
        od;
      od;
      Add(ListFinished, ePlan);
    od;
    ListToBeWorkedNew:=RemoveByIsomorphy(ListPlan, ListInv, IsIsomorphicPlanGraph).NonIsomorphRepresentant;
#    Print("ListToBeWorkedNew=", ListToBeWorkedNew, "\n");
#    Print("ListFinished=", ListFinished, "\n");
#    Print("NbWorkNew=", Length(ListToBeWorkedNew), "\n");
#    Print("NbFinished=", Length(ListFinished), "\n");
#    Print("\n");
  od;
  return ListFinished;
end;





CyclicRotate:=function(LIST, k)
  local LISTnew, i;
  LISTnew:=[];
  for i in [k+1..Length(LIST)]
  do
    Add(LISTnew, LIST[i]);
  od;
  for i in [1..k]
  do
    Add(LISTnew, LIST[i]);
  od;
  return LISTnew;
end;



#
# PlanGraph must be 4-valent, CC its central circuit info
# and ListFoldingNumbers the list of multiplications of central circuits.
SimultaneousInflation:=function(PlanGraph, CC, ListFoldingNumbers)
  local ListDE, ListStatus, ListFoldingStatus, iDE, iCC, CCL, iPos, DE1, DE2, DE3, DE4, Pos1, Pos2, Pos3, Pos4, NewPlanGraph, ListVertex, iVert, ListAdj, Fold1, Fold2, Fold3, EltAdj, eVert, fVert, VAdj, AdjStatus, rDE, nrDE, PlanGraph2, ListDE2, iCol, iLin, Ladj, DEold, DEnew, ListVal, pos, iColNew, xPos, yPos;

  ListDE:=ListDirectedEdges(PlanGraph);
  ListStatus:=[];
  ListFoldingStatus:=[];
  for iDE in [1..Length(ListDE)]
  do
    ListStatus[iDE]:=-1;
    ListFoldingStatus[iDE]:=-1;
  od;


  for iCC in [1..Length(CC.ListCircuit)]
  do
    CCL:=CC.ListCircuit[iCC];
    for iPos in [1..Length(CCL)]
    do
      DE1:=CCL[iPos];
      DE2:=NextDE(PlanGraph, DE1);
      DE3:=NextDE(PlanGraph, DE2);
      DE4:=NextDE(PlanGraph, DE3);
      Pos1:=Position(ListDE, DE1);
      Pos2:=Position(ListDE, DE2);
      Pos3:=Position(ListDE, DE3);
      Pos4:=Position(ListDE, DE4);
      if ListStatus[Pos1]=-1 then
        ListStatus[Pos1]:=1;
        ListStatus[Pos2]:=2;
        ListStatus[Pos3]:=3;
        ListStatus[Pos4]:=4;
      fi;
      ListFoldingStatus[Pos1]:=ListFoldingNumbers[iCC];
      ListFoldingStatus[Pos3]:=ListFoldingNumbers[iCC];
    od;
  od;
  PlanGraph2:=ShallowCopy(PlanGraph);
  ListDE2:=ShallowCopy(ListDE);
  for iVert in [1..Length(PlanGraph)]
  do
    ListVal:=[];
    for iCol in [1..4]
    do
      ListVal[iCol]:=ListStatus[Position(ListDE, [iVert,iCol])];
    od;
    Ladj:=[];
    for iCol in [1..4]
    do
      DEold:=[iVert,iCol];
      iColNew:=Position(ListVal, 5-iCol);
      DEnew:=[iVert, 5-iColNew];
      pos:=Position(ListDE, DEold);
      ListDE2[pos]:=DEnew;
      Ladj[iCol]:=PlanGraph[DEnew[1]][DEnew[2]];
    od;
    PlanGraph2[iVert]:=Ladj;
  od;
  ListVertex:=[];
  for iVert in [1..Length(PlanGraph2)]
  do
    Fold1:=ListFoldingStatus[Position(ListDE2, [iVert,1])];
    Fold2:=ListFoldingStatus[Position(ListDE2, [iVert,2])];
    for iCol in [1..Fold2]
    do
      for iLin in [1..Fold1]
      do
        Add(ListVertex, [iVert, iCol, iLin]);
      od;
    od;
  od;

  NewPlanGraph:=[];
  for iVert in [1..Length(ListVertex)]
  do
    eVert:=ListVertex[iVert];
    fVert:=eVert[1];
    xPos:=eVert[2];
    yPos:=eVert[3];
    Fold1:=ListFoldingStatus[Position(ListDE2, [fVert,1])];
    Fold2:=ListFoldingStatus[Position(ListDE2, [fVert,2])];
    ListAdj:=[];


    # case 1
    if xPos<Fold2 then
      EltAdj:=[fVert, xPos+1, yPos];
    else
      rDE:=ReverseDE(PlanGraph2, [fVert,1]);
      VAdj:=rDE[1];
      AdjStatus:=ListStatus[Position(ListDE2, rDE)];
      nrDE:=NextDE(PlanGraph2, rDE);
      Fold3:=ListFoldingStatus[Position(ListDE2, nrDE)];
      if AdjStatus=3 then
        EltAdj:=[VAdj, 1,yPos];
      elif AdjStatus=4 then
        EltAdj:=[VAdj, Fold1+1-yPos,1];
      elif AdjStatus=1 then
        EltAdj:=[VAdj, Fold3, Fold1+1-yPos];
      elif AdjStatus=2 then
        EltAdj:=[VAdj, yPos, Fold3];
      fi;
    fi;
    ListAdj[1]:=Position(ListVertex, EltAdj);
    if ListAdj[1]=fail then
      Error("We should not reach that stage");
    fi;

    # case 2
    if yPos<Fold1 then
      EltAdj:=[fVert, xPos, yPos+1];
    else
      rDE:=ReverseDE(PlanGraph2, [fVert, 2]);
      VAdj:=rDE[1];
      AdjStatus:=ListStatus[Position(ListDE2, rDE)];
      nrDE:=NextDE(PlanGraph2, rDE);
      Fold3:=ListFoldingStatus[Position(ListDE2, nrDE)];
      if AdjStatus=4 then
        EltAdj:=[VAdj, xPos,1];
      elif AdjStatus=1 then
        EltAdj:=[VAdj, Fold3, xPos];
      elif AdjStatus=2 then
        EltAdj:=[VAdj, Fold2+1-xPos, Fold3];
      elif AdjStatus=3 then
        EltAdj:=[VAdj, 1, Fold2+1-xPos];
      fi;
    fi;
    ListAdj[2]:=Position(ListVertex, EltAdj);
    if ListAdj[2]=fail then
      Error("We should not reach that stage 2");
    fi;

    # case 3
    if xPos>1 then
      EltAdj:=[fVert, xPos-1, yPos];
    else
      rDE:=ReverseDE(PlanGraph2, [fVert, 3]);
      VAdj:=rDE[1];
      AdjStatus:=ListStatus[Position(ListDE2, rDE)];
      nrDE:=NextDE(PlanGraph2, rDE);
      Fold3:=ListFoldingStatus[Position(ListDE2, nrDE)];
      if AdjStatus=1 then
        EltAdj:=[VAdj, Fold3, yPos];
      elif AdjStatus=2 then
        EltAdj:=[VAdj, Fold1+1-yPos, Fold3];
      elif AdjStatus=3 then
        EltAdj:=[VAdj, 1, Fold1+1-yPos];
      elif AdjStatus=4 then
        EltAdj:=[VAdj, yPos, 1];
      fi;
    fi;
    ListAdj[3]:=Position(ListVertex, EltAdj);
    if ListAdj[3]=fail then
      Error("ListAdj wrong set");
    fi;

    # case 4
    if yPos>1 then
      EltAdj:=[fVert, xPos, yPos-1];
    else
      rDE:=ReverseDE(PlanGraph2, [fVert,4]);
      VAdj:=rDE[1];
      AdjStatus:=ListStatus[Position(ListDE2, rDE)];
      nrDE:=NextDE(PlanGraph2, rDE);
      Fold3:=ListFoldingStatus[Position(ListDE2, nrDE)];
      if AdjStatus=2 then
        EltAdj:=[VAdj, xPos, Fold3];
      elif AdjStatus=3 then
        EltAdj:=[VAdj, 1, xPos];
      elif AdjStatus=4 then
        EltAdj:=[VAdj, Fold2+1-xPos, 1];
      elif AdjStatus=1 then
        EltAdj:=[VAdj, Fold3, Fold2+1-xPos];
      fi;
    fi;
    ListAdj[4]:=Position(ListVertex, EltAdj);
    if ListAdj[4]=fail then
      Error("ListAdj wrongly set");
    fi;
    #
    NewPlanGraph[iVert]:=ListAdj;
  od;
  return NewPlanGraph;
end;







#
#
# PlanGraph is either a 3-valent graph or a 4-valent graph
# in 3-valent case, the flat elements are the hexagons while in 
# 4-valent case, the flat elements are the squares
GraphOfCurvatures:=function(PlanGraph)
  local GS, Faces, DualG, Valency, FollowDirEdge, FlatNess, CurvatureElt, eFac, NbCurvy, GraphCur, iCurv, LADJ, iPos, OldAdj, adjness, iAdj, DE, FaceArrow;
  GS:=DualGraph(PlanGraph);
  Faces:=GS.Vertices;
  DualG:=GS.PlanGraph;
  Valency:=Length(PlanGraph[1]);
  if Valency=3 then
    FollowDirEdge:=function(DE)
      return NextDE(DualG, NextDE(DualG, NextDE(DualG, ReverseDE(DualG, DE))));
    end;
    FlatNess:=6;
  else
    FollowDirEdge:=function(DE)
      return NextDE(DualG, NextDE(DualG, ReverseDE(DualG, DE)));
    end;
    FlatNess:=4;
  fi;
  CurvatureElt:=[];
  for eFac in Faces
  do
    if Length(eFac)<>FlatNess then
      AddSet(CurvatureElt, eFac);
    fi;
  od;
  NbCurvy:=Length(CurvatureElt);
  GraphCur:=[];
  for iCurv in [1..NbCurvy]
  do
    LADJ:=[];
    iPos:=Position(Faces, CurvatureElt[iCurv]);
    OldAdj:=DualG[iPos];
    adjness:=Length(OldAdj);
    for iAdj in [1..adjness]
    do
      DE:=[iPos, iAdj];
      FaceArrow:=Faces[DualG[DE[1]][DE[2]]];
      while Length(FaceArrow)=FlatNess
      do
        DE:=FollowDirEdge(DE);
        FaceArrow:=Faces[DualG[DE[1]][DE[2]]];
      od;
      LADJ[iAdj]:=Position(CurvatureElt, FaceArrow);
    od;
    GraphCur[iCurv]:=LADJ;
  od;
  return [CurvatureElt, GraphCur];
end;






CentralCircuitDeletionHedrite:=function(PlanGraph, CC, ListDelete)
  local KeepVert, NewPlanGraph, iVert, FollowEdge, iV, OldAdj, NewAdj, DE, VertexArrow, u;
  KeepVert:=[];
  NewPlanGraph:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    if Intersection(CC.IncidenceVertexCC[iVert], ListDelete)=[] then
      Add(KeepVert, iVert);
    fi;
    NewPlanGraph[iVert]:=[];
  od;
  FollowEdge:=function(DE)
    return NextDE(PlanGraph, NextDE(PlanGraph, ReverseDE(PlanGraph, DE)));
  end;
  for iV in [1..Length(KeepVert)]
  do
    OldAdj:=PlanGraph[KeepVert[iV]];
    NewAdj:=[];
    for u in [1..Length(OldAdj)]
    do
      DE:=[KeepVert[iV], u];
      VertexArrow:=PlanGraph[DE[1]][DE[2]];
      while not (VertexArrow in KeepVert)
      do
        DE:=FollowEdge(DE);
        VertexArrow:=PlanGraph[DE[1]][DE[2]];
      od;
      NewAdj[u]:=VertexArrow;
    od;
    NewPlanGraph[KeepVert[iV]]:=NewAdj;
  od;
  return Renormalisation(NewPlanGraph);
end;












SwitchZZL:=function(ZZL)
  if ZZL[1]="N" then
    return ["P", ZZL[2]];
  else
    return ["N", ZZL[2]];
  fi;
end;


ReverseZZ:=function(PlanGraph, ZZ)
  local L, iZZ, ZZL;
  L:=[];
  for iZZ in [1..Length(ZZ)]
  do
    ZZL:=ZZ[iZZ];
    L[iZZ]:=[ZZL[1], ReverseDE(PlanGraph, ZZL[2])];
  od;
  return Reversed(L);
end;



#
#
#
# Matching stuff


#
#
# ZZ1 and ZZ2 are Zig Zag of the form 
# [ ["P" , [deb, idx]], ....]
MatchingDirEdge:=function(PlanGraph, ZZ1, ZZ2)
  local ZZseq, iZZ, MatchFirstType, MatchSecondType, pos1, pos2, eDE;
  ZZseq:=[];
  for iZZ in [1..Length(ZZ2)]
  do
    ZZseq[iZZ]:=ZZ2[iZZ][2];
  od;
  MatchFirstType:=[];
  MatchSecondType:=[];
  for eDE in ZZ1
  do
    pos1:=Position(ZZseq, eDE[2]);
    pos2:=Position(ZZseq, ReverseDE(PlanGraph, eDE[2]));
    if pos1<>fail then
      Add(MatchSecondType, eDE[2]);
    fi;
    if pos2<>fail then
      Add(MatchFirstType, eDE[2]);
    fi;
  od;
  return [MatchFirstType, MatchSecondType];
end;

#
#
#
# the self intersection is obviously treated differently!
SelfMatchingDirEdge:=function(PlanGraph, ZZ)
  local LL, ListDirectedEdge, Treated, FirstType, SecondType, iElt, pos1, pos2;
  #
  LL:=[];
  ListDirectedEdge:=[];
  Treated:=[];
  FirstType:=[]; # according to Motzkin-Grunbaum
  SecondType:=[];
  #
  for iElt in [1..Length(ZZ)]
  do
    LL[iElt]:=ZZ[iElt][2][1];
    ListDirectedEdge[iElt]:=ZZ[iElt][2];
    Treated[iElt]:=0;
  od;
  for iElt in [1..Length(ListDirectedEdge)]
  do
    if Treated[iElt]=0 then
      Treated[iElt]:=1;
      pos1:=PositionNthOccurrence(ListDirectedEdge, ListDirectedEdge[iElt], 2);
      pos2:=PositionNthOccurrence(ListDirectedEdge, ReverseDE(PlanGraph, ListDirectedEdge[iElt]), 1);
      if pos1<>fail then
        Add(SecondType, ListDirectedEdge[iElt]);
        Treated[pos1]:=1;
      else
        if pos2<>fail then
          Add(FirstType, ListDirectedEdge[iElt]);
          Treated[pos2]:=1;
        fi;
      fi;
    fi;
  od;
  return [LL, FirstType, SecondType];
end;




ChangeOrientation:=function(PlanGraph, LZZ, VECT)
  local ZZnew, nbZZ, i;
  ZZnew:=[];
  nbZZ:=Length(LZZ);
  for i in [1..nbZZ]
  do
    if VECT[i]=0 then
      ZZnew[i]:=LZZ[i];
    else
      ZZnew[i]:=ReverseZZ(PlanGraph, LZZ[i]);
    fi;
  od;
  return ZZnew;
end;







#
#
# ZZ is a sequence of n Zig Zag paths
# VECT is a 0-1 vector of length n with first coordinate
# equal to zero by convention
DirEdgeStructure:=function(PlanGraph, LZZ, VECT)
  local ZZnew, nbZZ, i, j, ListDirEdge;
  ZZnew:=[];
  nbZZ:=Length(LZZ);
  for i in [1..nbZZ]
  do
    if VECT[i]=0 then
      ZZnew[i]:=LZZ[i];
    else
      ZZnew[i]:=ReverseZZ(PlanGraph, LZZ[i]);
    fi;
  od;
  ListDirEdge:=[];
  for i in [1..nbZZ]
  do
    ListDirEdge:=Union(ListDirEdge, SelfMatchingDirEdge(PlanGraph, ZZnew[i])[2]);
  od;
  for i in [1..nbZZ-1]
  do
    for j in [i+1..nbZZ]
    do
      ListDirEdge:=Union(ListDirEdge, MatchingDirEdge(PlanGraph, ZZnew[i], ZZnew[j]));
    od;
  od;
  return ListDirEdge;
end;





MatrixOfIntersectionsWithTypes:=function(PlanGraph, LZZ)
  local Matri, nbZZ, ROW, iZZ, jZZ, TT;
  nbZZ:=Length(LZZ);
  Matri:=[];
  for iZZ in [1..nbZZ]
  do
    ROW:=[];
    for jZZ in [1..nbZZ]
    do
      ROW[jZZ]:=[];
    od;
    Matri[iZZ]:=ROW;
  od;
  for iZZ in [1..nbZZ]
  do
    for jZZ in [1..nbZZ]
    do
      if iZZ=jZZ then
        TT:=SelfMatchingDirEdge(PlanGraph, LZZ[iZZ]);
        Matri[iZZ][jZZ]:=[Length(TT[2]), Length(TT[3])];
      else
        TT:=MatchingDirEdge(PlanGraph, LZZ[iZZ], LZZ[jZZ]);
        Matri[iZZ][jZZ]:=[Length(TT[1]), Length(TT[2])];
      fi;
    od;
  od;
  return Matri;
end;




ResearchPerfectMatching:=function(PlanGraph, LZZ)
  local nbZZ, iZZ, jZZ, ROW, Matri, TT, FirstType, SecondType, eDO, DO, PossiblePairs, Appearance, iAp;
  nbZZ:=Length(LZZ);
  Matri:=MatrixOfIntersectionsWithTypes(PlanGraph, LZZ);
  DO:=ProductList([[0]],BuildSet(nbZZ-1,[0,1]));
  #
  PossiblePairs:=[];
  Appearance:=[];
  #
  for eDO in DO
  do
    FirstType:=0;
    SecondType:=0;
    for iZZ in [1..nbZZ]
    do
      for jZZ in [iZZ..nbZZ]
      do
        if eDO[iZZ]=eDO[jZZ] then
          FirstType:=FirstType+Matri[iZZ][jZZ][1];
          SecondType:=SecondType+Matri[iZZ][jZZ][2];
        else
          FirstType:=FirstType+Matri[iZZ][jZZ][2];
          SecondType:=SecondType+Matri[iZZ][jZZ][1];
        fi;
      od;
    od;
    if Position(PossiblePairs,[FirstType,SecondType])=fail then
      AddSet(PossiblePairs, [FirstType,SecondType]);
      AddSet(Appearance, [[FirstType,SecondType],[eDO]]);
    else
      for iAp in [1..Length(Appearance)]
      do
        if Appearance[iAp][1]=[FirstType,SecondType] then
          AddSet(Appearance[iAp][2],eDO);
        fi;
      od;
    fi;
  od;
  return rec(Matri:=Matri, PossiblePairs:=PossiblePairs, Appearance:=Appearance);
end;


#
#
# PlanGraph must be for example the dual of a planar bipartite graph
# we assume there exist an orientation such that no edge is of type I
SecondaryPartition:=function(PlanGraph, ZZ)
  local RPM, iSol, FirstType, SecondType, eSet, ZZnew, DirEdge, eZZ, eZZL, DE;
  RPM:=ResearchPerfectMatching(PlanGraph, ZZ.ListZigZag).Appearance;
  for iSol in [1..Length(RPM)]
  do
    FirstType:=RPM[iSol][1][1];
    SecondType:=RPM[iSol][1][2];
    if FirstType=0 then
      eSet:=RPM[iSol][2][1];
    fi;
  od;  
  ZZnew:=ChangeOrientation(PlanGraph, ZZ.ListZigZag, eSet);
  DirEdge:=[];
  for eZZ in ZZnew
  do
    for eZZL in eZZ
    do
      DE:=eZZL[2];
      AddSet(DirEdge, [DE[1],PlanGraph[DE[1]][DE[2]]]);
    od;
  od;
  return DirEdge;
end;




SetDirEdgeToSetEdge:=function(PlanGraph, SetDirEdge)
  local SetEdge, a, b, u;
  SetEdge:=[];
  for u in [1..Length(SetDirEdge)]
  do
    a:=SetDirEdge[u][1];
    b:=SetDirEdge[u][2];
    Add(SetEdge, [a,PlanGraph[a][b]]);
  od;
  return SetEdge;
end;






ReverseZZL:=function(PlanGraph, ZZL)
  return [ZZL[1], ReverseDE(PlanGraph, ZZL[2])];
end;

#
#
# return true if the sequence is a Road of hexagons
TestHexagon:=function(PlanGraph, ZZ)
  local NextInFace, iZZ, DE;
  NextInFace:=function(DirEdge)
    return NextDE(PlanGraph, ReverseDE(PlanGraph, DirEdge));
  end;
  for iZZ in [1..Length(ZZ)]
  do
    DE:=ZZ[iZZ][2];
    if NextInFace(NextInFace(NextInFace(NextInFace(NextInFace(NextInFace(DE))))))<>DE then
      return false;
    fi;
  od;
  return true;
end;



TestIrreducibility:=function(PlanGraph, LZZ)
  local U;
  for U in LZZ
  do
    if TestHexagon(PlanGraph, U)=true then
      return false;
    fi;
    if TestHexagon(PlanGraph, ReverseZZ(PlanGraph, U))=true then
      return false;
    fi;
  od;
  return true;
end;




# Zig-Zag path are made of little pieces put together
# these little pieces are called ZZL or Zig Zag Lego
# structure of Zig-Zag-Lego:
# ["N", [i,j]] with N or P standing for Next
# or Previous
ZigZag:=function(PlanGraph)
  local ListZigZag, ListZZL, iVert, iadj, FollowZZL, z, v, Sequence, SequenceRev, ListRaw, ListInvariants, Zmatrix, ROW, iZZ, jZZ, eZZ, ZZstring, i, ZZsimple, ZZself, ZZS, UNIQsimple, UNIQself, mult, obj, Sstring, SelfResult, INTV, Zuniformity, Zset, eZig, SetINTV, Zbalancedness, Pair, iElt, ListInt, ListIntersectionVectors, ListStrings, nbZZ, Occ, VCE, nbSimple, IsIrred, TotalListZigZag;
  ListZigZag:=[];
  ListZZL:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    for iadj in [1..Length(PlanGraph[iVert])]
    do
      Add(ListZZL, ["N", [iVert, iadj]]);
      Add(ListZZL, ["P", [iVert, iadj]]);
    od;
  od;
  FollowZZL:=function(ZZL)
    if ZZL[1]="P" then
      return ["N", PrevDE(PlanGraph, ReverseDE(PlanGraph, ZZL[2]))];
    else
      return ["P", NextDE(PlanGraph, ReverseDE(PlanGraph, ZZL[2]))];
    fi;
  end;
  TotalListZigZag:=[];
  while (Length(ListZZL)>0)
  do
    z:=ListZZL[1];
    Sequence:=ShallowCopy([z]);
    SequenceRev:=ShallowCopy([ReverseZZL(PlanGraph, z)]);
    v:=FollowZZL(z);
    while(v<>z) 
    do
      Add(Sequence, v);
      Add(SequenceRev, ReverseZZL(PlanGraph, v));
      v:=FollowZZL(v);
    od;
    Add(ListZigZag, Sequence);
    Add(TotalListZigZag, [Sequence, SequenceRev]);
    ListZZL:=Difference(ListZZL, Union(Sequence, SequenceRev));
  od;
  #
  ListRaw:=[];
  ListInvariants:=[];
  nbZZ:=Length(ListZigZag);
  for iZZ in [1..nbZZ]
  do
    eZZ:=ListZigZag[iZZ];
    SelfResult:=SelfMatchingDirEdge(PlanGraph, eZZ);
    ListRaw[iZZ]:=SelfResult[1];
    ListInvariants[iZZ]:=[Length(SelfResult[1]), Length(SelfResult[2]), Length(SelfResult[3])];
  od;
  Zmatrix:=MatrixOfIntersectionsWithTypes(PlanGraph, ListZigZag);
  ZZstring:="";
  ZZsimple:=[];
  ZZself:=[];
  for ZZS in ListInvariants
  do
    if ZZS[2]=0 and ZZS[3]=0 then
      Add(ZZsimple, ZZS);
    else
      Add(ZZself, ZZS);
    fi;
  od;
  UNIQsimple:=Collected(ZZsimple);
  UNIQself:=Collected(ZZself);
  for i in [1..Length(UNIQsimple)]
  do
    obj:=UNIQsimple[i][1];
    mult:=UNIQsimple[i][2];
    if mult=1 then
      ZZstring:=Concatenation(ZZstring, String(obj[1]));
    else
      ZZstring:=Concatenation(ZZstring, String(obj[1]),"^",StringLatex(mult));
    fi;
    if i<Length(UNIQsimple) then
      ZZstring:=Concatenation(ZZstring, ", ");
    fi;
  od;
  if Length(ZZsimple)>0 and Length(ZZself)>0 then
    ZZstring:=Concatenation(ZZstring, "; ");
  fi;
  for i in [1..Length(UNIQself)]
  do
    obj:=UNIQself[i][1];
    mult:=UNIQself[i][2];
    Sstring:=Concatenation(String(obj[1]),"_{",String(obj[2]),",",String(obj[3]),"}");
    if mult=1 then
      ZZstring:=Concatenation(ZZstring, Sstring);
    else
      ZZstring:=Concatenation(ZZstring, Sstring,"^",StringLatex(mult));
    fi;
    if i<Length(UNIQself) then
      ZZstring:=Concatenation(ZZstring, ", ");
    fi;
  od;
  if Length(Set(ListInvariants))=1 then
    Zuniformity:=true;
  else
    Zuniformity:=false;
  fi;
  # intersection vectors
  ListIntersectionVectors:=[];
  ListStrings:=[];
  for iZZ in [1..nbZZ]
  do
    ListInt:=[];
    for jZZ in [1..nbZZ]
    do
      VCE:=ShallowCopy(Zmatrix[iZZ][jZZ]);
      Sort(VCE);
      if iZZ<>jZZ then
        Sstring:=Concatenation("(", String(VCE[1]), ",",String(VCE[2]), ")");
        Add(ListInt, Sstring);
      fi;
    od;
    Occ:=Collected(ListInt);
    Add(ListIntersectionVectors, Occ);
    Add(ListStrings, SyncTextOccurrence(Occ));
  od;


  # Z-balancedness
  Zset:=Set(ListInvariants);
  Zbalancedness:=true;
  for iZZ in [1..Length(Zset)]
  do
    SetINTV:=[];
    for iElt in [1..Length(ListInvariants)]
    do
      if ListInvariants[iElt]=Zset[iZZ] then
        INTV:=ShallowCopy([]);
        for eZig in ListZigZag
        do
          Pair:=MatchingDirEdge(PlanGraph, ListZigZag[iElt], eZig);
          Add(INTV, Length(Pair[1])+Length(Pair[2]));
        od;
        Sort(INTV);
        Add(SetINTV, ShallowCopy(INTV));
      fi;
    od;
    if Length(Set(SetINTV))>1 then
      Zbalancedness:=false;
    fi;
  od;
  nbSimple:=Length(Filtered([1..Length(Zmatrix)], x->Zmatrix[x][x]=[0,0]));
  IsIrred:=TestIrreducibility(PlanGraph, ListZigZag);
  return rec(ListZigZag:=ListZigZag,
             TotalListZigZag:=TotalListZigZag,
             ListRaw:=ListRaw,
             Zmatrix:=Zmatrix,
             Invariants:=ListInvariants,
             Zvector:=ZZstring,
             Zuniformity:=Zuniformity,
             Zbalancedness:=Zbalancedness,
             ListIntersectionVectors:=ListStrings,
             nbSimple:=nbSimple,
             IsIrred:=IsIrred);
end;


ZigZagIcosahedrite:=function(ePL)
  local ZZinfo, ListTot, nbDE, LFace, nbFace, ListIFace, iFace, eFace, eDE, pos, IsThereRailroadSeq, IsThereRailroadPair, IsItTightIcosahedrite;
  ZZinfo:=ZigZag(ePL);
  ListTot:=ListDirectedEdges(ePL);
  nbDE:=Length(ListTot);
  LFace:=__FaceSet(ePL);
  nbFace:=Length(LFace);
  ListIFace:=ListWithIdenticalEntries(nbDE, 0);
  for iFace in [1..nbFace]
  do
    eFace:=LFace[iFace];
    for eDE in eFace
    do
      pos:=Position(ListTot, eDE);
      ListIFace[pos]:=iFace;
    od;
  od;
  IsThereRailroadSeq:=function(eSeq)
    local eZZL, eDE1, eDE2, eDE3, nDE1, nDE2, posDE1, posDE2, posDE3, iFace1, iFace2, iFace3, len1, len2, len3;
#    Print("|eSeq|=", Length(eSeq), "\n");
    for eZZL in eSeq
    do
      eDE1:=eZZL[2];
      posDE1:=Position(ListTot, eDE1);
      iFace1:=ListIFace[posDE1];
      len1:=Length(LFace[iFace]);
      if len1<>3 then
#        Print("Return false 1\n");
        return false;
      fi;
      if eZZL[1]="P" then
        eDE2:=NextDE(ePL, eDE1);
        posDE2:=Position(ListTot, eDE2);
        iFace2:=ListIFace[posDE2];
        len2:=Length(LFace[iFace2]);
        if len2<>4 then
#          Print("Return false 2\n");
          return false;
        fi;
        nDE1:=NextDE(ePL, eDE2);
        nDE2:=ReverseDE(ePL, nDE1);
        eDE3:=NextDE(ePL, nDE2);
        posDE3:=Position(ListTot, eDE3);
        iFace3:=ListIFace[posDE3];
        len3:=Length(LFace[iFace3]);
        if len3<>3 then
#          Print("Return false 3\n");
          return false;
        fi;
      fi;      
    od;
    return true;
  end;
  IsThereRailroadPair:=function(ePairZZ)
    local eSeq, test;
    for eSeq in ePairZZ
    do
      test:=IsThereRailroadSeq(eSeq);
#      Print("Seq, test=", test, "\n");
      if test=true then
        return true;
      fi;
    od;
    return false;
  end;
  IsItTightIcosahedrite:=function(ZZinfo)
    local ePairZZ;
    for ePairZZ in ZZinfo.TotalListZigZag
    do
      if IsThereRailroadPair(ePairZZ)=true then
        return false;
      fi;
    od;
    return true;
  end;
  ZZinfo.IsTightIcosahedrite:=IsItTightIcosahedrite(ZZinfo);
  return ZZinfo;
end;

SelfMatchingDirEdgeOriented:=function(PLori, ListVertStatus, ZZ)
  local LL, ListDirectedEdge, Treated, FirstType, SecondType, iElt, pos1, pos2, iVert, iDE;
  #
  LL:=[];
  ListDirectedEdge:=[];
  Treated:=[];
  FirstType:=[]; # according to Motzkin-Grunbaum
  SecondType:=[];
  #
  for iElt in [1..Length(ZZ)]
  do
    iDE:=ZZ[iElt][2];
    iVert:=ListVertStatus[iDE];
    LL[iElt]:=iVert;
    ListDirectedEdge[iElt]:=iDE;
    Treated[iElt]:=0;
  od;
  for iElt in [1..Length(ListDirectedEdge)]
  do
    if Treated[iElt]=0 then
      Treated[iElt]:=1;
      pos1:=PositionNthOccurrence(ListDirectedEdge, ListDirectedEdge[iElt], 2);
      pos2:=PositionNthOccurrence(ListDirectedEdge, OnPoints(PLori.invers, ListDirectedEdge[iElt]), 1);
      if pos1<>fail then
        Add(SecondType, ListDirectedEdge[iElt]);
        Treated[pos1]:=1;
      else
        if pos2<>fail then
          Add(FirstType, ListDirectedEdge[iElt]);
          Treated[pos2]:=1;
        fi;
      fi;
    fi;
  od;
  return [LL, FirstType, SecondType];
end;


MatchingDirEdgeOriented:=function(PLori, ZZ1, ZZ2)
  local ZZseq, iZZ, MatchFirstType, MatchSecondType, pos1, pos2, eDE;
  ZZseq:=[];
  for iZZ in [1..Length(ZZ2)]
  do
    ZZseq[iZZ]:=ZZ2[iZZ][2];
  od;
  MatchFirstType:=[];
  MatchSecondType:=[];
  for eDE in ZZ1
  do
    pos1:=Position(ZZseq, eDE[2]);
    pos2:=Position(ZZseq, OnPoints(PLori.invers, eDE[2]));
    if pos1<>fail then
      Add(MatchSecondType, eDE[2]);
    fi;
    if pos2<>fail then
      Add(MatchFirstType, eDE[2]);
    fi;
  od;
  return [MatchFirstType, MatchSecondType];
end;

MatrixOfIntersectionsWithTypesOriented:=function(PLori, ListVertStatus, LZZ)
  local Matri, nbZZ, ROW, iZZ, jZZ, TT;
  nbZZ:=Length(LZZ);
  Matri:=[];
  for iZZ in [1..nbZZ]
  do
    ROW:=[];
    for jZZ in [1..nbZZ]
    do
      ROW[jZZ]:=[];
    od;
    Matri[iZZ]:=ROW;
  od;
  for iZZ in [1..nbZZ]
  do
    for jZZ in [1..nbZZ]
    do
      if iZZ=jZZ then
        TT:=SelfMatchingDirEdgeOriented(PLori, ListVertStatus, LZZ[iZZ]);
        Matri[iZZ][jZZ]:=[Length(TT[2]), Length(TT[3])];
      else
        TT:=MatchingDirEdgeOriented(PLori, LZZ[iZZ], LZZ[jZZ]);
        Matri[iZZ][jZZ]:=[Length(TT[1]), Length(TT[2])];
      fi;
    od;
  od;
  return Matri;
end;










ZigZagOriented:=function(PLori)
  local ListZigZag, iVert, iadj, FollowZZL, z, v, Sequence, SequenceRev, ListRaw, ListInvariants, Zmatrix, ROW, iZZ, jZZ, eZZ, ZZstring, i, ZZsimple, ZZself, ZZS, UNIQsimple, UNIQself, mult, obj, Sstring, SelfResult, INTV, Zuniformity, Zset, eZig, SetINTV, Zbalancedness, Pair, iElt, ListInt, ListIntersectionVectors, ListStrings, nbZZ, Occ, VCE, ReverseZZL, eNext, ePrev, eInv, ListVertStatus, iP, VEFori, nbP, eSetVert, nbVert, GetSequence, ListStatusZZL, nbZZL, ListZZL, FuncPosZZL, TotalListZigZag, ReverseNP, IsSimple;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  nbP:=PLori.nbP;
  ListVertStatus:=ListWithIdenticalEntries(nbP, 0);
  nbVert:=Length(VEFori.VertSet);
  for iVert in [1..nbVert]
  do
    eSetVert:=VEFori.VertSet[iVert];
    ListVertStatus{eSetVert}:=ListWithIdenticalEntries(Length(eSetVert), iVert);
  od;
  ePrev:=Inverse(PLori.next);
  eNext:=PLori.next;
  eInv:=PLori.invers;
  ListZZL:=[];
  for iP in [1..nbP]
  do
    Add(ListZZL, ["N", iP]);
    Add(ListZZL, ["P", iP]);
  od;
  FuncPosZZL:=function(eZZL)
    if eZZL[1]="P" then
      return 2*eZZL[2];
    else
      return 2*eZZL[2]-1;
    fi;
  end;
  nbZZL:=Length(ListZZL);
  ListStatusZZL:=ListWithIdenticalEntries(nbZZL,1);
  ReverseNP:=function(eChar)
    if eChar="N" then
      return "P";
    else
      return "N";
    fi;
  end;
  ReverseZZL:=function(ZZL)
    return [ZZL[1], OnPoints(ZZL[2], eInv)];
  end;
  FollowZZL:=function(ZZL)
    if ZZL[1]="P" then
      return ["N", OnPoints(ZZL[2], eInv*ePrev)];
    else
      return ["P", OnPoints(ZZL[2], eInv*eNext)];
    fi;
  end;
  TotalListZigZag:=[];
  GetSequence:=function(z)
    local pos1, pos2, v, vRev, zRev, Sequence, SequenceRev, SequenceB, SequenceRevB;
    zRev:=ReverseZZL(z);
    pos1:=FuncPosZZL(z);
    pos2:=FuncPosZZL(zRev);
    ListStatusZZL[pos1]:=0;
    ListStatusZZL[pos2]:=0;
    Sequence:=[pos1];
    SequenceRev:=[pos2];
    SequenceB:=[z];
    SequenceRevB:=[zRev];
    v:=FollowZZL(z);
    while(v<>z)
    do
      vRev:=ReverseZZL(v);
      pos1:=FuncPosZZL(v);
      pos2:=FuncPosZZL(vRev);
      Add(Sequence, pos1);
      Add(SequenceRev, pos2);
      Add(SequenceB, v);
      Add(SequenceRevB, vRev);
      ListStatusZZL[pos1]:=0;
      ListStatusZZL[pos2]:=0;
      v:=FollowZZL(v);
    od;
    Add(TotalListZigZag, [SequenceB, SequenceRevB]);
    return ListZZL{Sequence};
  end;
  ListZigZag:=[];
  for i in [1..nbZZL]
  do
    if ListStatusZZL[i]=1 then
      Add(ListZigZag, GetSequence(ListZZL[i]));
    fi;
  od;
  #
  ListRaw:=[];
  ListInvariants:=[];
  nbZZ:=Length(ListZigZag);
  for iZZ in [1..nbZZ]
  do
    eZZ:=ListZigZag[iZZ];
    SelfResult:=SelfMatchingDirEdgeOriented(PLori, ListVertStatus, eZZ);
    ListRaw[iZZ]:=SelfResult[1];
    ListInvariants[iZZ]:=[Length(SelfResult[1]), Length(SelfResult[2]), Length(SelfResult[3])];
  od;
  Zmatrix:=MatrixOfIntersectionsWithTypesOriented(PLori, ListVertStatus, ListZigZag);
  ZZstring:="";
  ZZsimple:=[];
  ZZself:=[];
  for ZZS in ListInvariants
  do
    if ZZS[2]=0 and ZZS[3]=0 then
      Add(ZZsimple, ZZS);
    else
      Add(ZZself, ZZS);
    fi;
  od;
  IsSimple:=Length(ZZself)=0;
  UNIQsimple:=Collected(ZZsimple);
  UNIQself:=Collected(ZZself);
  for i in [1..Length(UNIQsimple)]
  do
    obj:=UNIQsimple[i][1];
    mult:=UNIQsimple[i][2];
    if mult=1 then
      ZZstring:=Concatenation(ZZstring, String(obj[1]));
    else
      ZZstring:=Concatenation(ZZstring, String(obj[1]),"^",StringLatex(mult));
    fi;
    if i<Length(UNIQsimple) then
      ZZstring:=Concatenation(ZZstring, ", ");
    fi;
  od;
  if Length(ZZsimple)>0 and Length(ZZself)>0 then
    ZZstring:=Concatenation(ZZstring, "; ");
  fi;
  for i in [1..Length(UNIQself)]
  do
    obj:=UNIQself[i][1];
    mult:=UNIQself[i][2];
    Sstring:=Concatenation(String(obj[1]),"_{",String(obj[2]),",",String(obj[3]),"}");
    if mult=1 then
      ZZstring:=Concatenation(ZZstring, Sstring);
    else
      ZZstring:=Concatenation(ZZstring, Sstring,"^",StringLatex(mult));
    fi;
    if i<Length(UNIQself) then
      ZZstring:=Concatenation(ZZstring, ", ");
    fi;
  od;
  if Length(Set(ListInvariants))=1 then
    Zuniformity:=true;
  else
    Zuniformity:=false;
  fi;
  # intersection vectors
  ListIntersectionVectors:=[];
  ListStrings:=[];
  for iZZ in [1..nbZZ]
  do
    ListInt:=[];
    for jZZ in [1..nbZZ]
    do
      ListInt:=[];
      for jZZ in [1..nbZZ]
      do
        VCE:=ShallowCopy(Zmatrix[iZZ][jZZ]);
        Sort(VCE);
        if iZZ<>jZZ then
          Sstring:=Concatenation("(", String(VCE[1]), ",",String(VCE[2]), ")");
          Add(ListInt, Sstring);
        fi;
      od;
      Occ:=Collected(ListInt);
      Add(ListIntersectionVectors, Occ);
      Add(ListStrings, SyncTextOccurrence(Occ));
    od;
  od;
  # Z-balancedness
  Zset:=Set(ListInvariants);
  Zbalancedness:=true;
  for iZZ in [1..Length(Zset)]
  do
    SetINTV:=[];
    for iElt in [1..Length(ListInvariants)]
    do
      if ListInvariants[iElt]=Zset[iZZ] then
        INTV:=ShallowCopy([]);
        for eZig in ListZigZag
        do
          Pair:=MatchingDirEdgeOriented(PLori, ListZigZag[iElt], eZig);
          Add(INTV, Length(Pair[1])+Length(Pair[2]));
        od;
        Sort(INTV);
        Add(SetINTV, ShallowCopy(INTV));
      fi;
    od;
    if Length(Set(SetINTV))>1 then
      Zbalancedness:=false;
    fi;
  od;
  return rec(ListZigZag:=ListZigZag,
             TotalListZigZag:=TotalListZigZag,
             IsSimple:=IsSimple,
             ListRaw:=ListRaw,
             Zmatrix:=Zmatrix,
             Invariants:=ListInvariants,
             Zvector:=ZZstring,
             Zuniformity:=Zuniformity,
             Zbalancedness:=Zbalancedness,
             ListIntersectionVectors:=ListStrings);
end;


# Search for a face of signature (2,2,2) and of second type
# See the manuscript of Pankov on z-knotted graph.
SearchCriticalGraph:=function(PLori, ZZori)
  local nbP, ListSignatureEdges, eZZ, i, eZZL1, eZZL2, pos1, pos2, iInv, VEFori, nb222trig, eFaceOri, TheSum, eDE, nbPlus, nbMinus, len, eList1, GrpCyc, ListPos, pos, SetPos, eList, ePerm;
  nbP:=PLori.nbP;
  ListSignatureEdges:=ListWithIdenticalEntries(nbP, 1);
  eZZ:=ZZori.ListZigZag[1];
  for i in [1..nbP]
  do
    eZZL1:=["P", i];
    eZZL2:=["N", i];
    pos1:=Position(eZZ, eZZL1);
    pos2:=Position(eZZ, eZZL2);
    if pos1<>fail and pos2<>fail then
      ListSignatureEdges[i]:=2;
      iInv:=OnPoints(i, PLori.invers);
      ListSignatureEdges[iInv]:=2;
    fi;
  od;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  nb222trig:=0;
  nbPlus:=0;
  nbMinus:=0;
  for eFaceOri in VEFori.FaceSet
  do
    TheSum:=0;
    len:=Length(eFaceOri);
    for eDE in eFaceOri
    do
      TheSum:=TheSum + ListSignatureEdges[eDE];
    od;
    if TheSum = 2*len then
      nb222trig:=nb222trig+1;
      eList1:=Concatenation([2..len], [1]);
      GrpCyc:=Group([PermList(eList1)]);
      ListPos:=[];
      for eDE in eFaceOri
      do
        pos:=Position(eZZ, ["P", eDE]);
	Add(ListPos, pos);
      od;
      SetPos:=Set(ListPos);
      eList:=[];
      for pos in ListPos
      do
        Add(eList, Position(SetPos, pos));
      od;
      ePerm:=PermList(eList);
      if ePerm in GrpCyc then
        nbPlus:=nbPlus+1;
      else
        nbMinus:=nbMinus+1;
      fi;
    fi;
  od;
  Print("nb222trig=", nb222trig, " nbPlus=", nbPlus, " nbMinus=", nbMinus, "\n");
  if nbPlus>0 and nbMinus> 0 then
    return true;
  fi;
  return false;
end;





ZigZagOriented_SelfDualMaps:=function(PLori)
  local ZZinfo, VEFori, IsThereRailroadSeq, IsThereRailroad, IsTight;
  ZZinfo:=ZigZagOriented(PLori);
  VEFori:=PlanGraphOrientedToVEF(PLori);
  IsThereRailroadSeq:=function(eSeq)
    local eZZL, eDE, iVert, rDE, iFace;
    for eZZL in eSeq
    do
      if eZZL[1]="N" then
        eDE:=eZZL[2];
        iVert:=VEFori.ListOriginVert[eDE];
        if Length(VEFori.VertSet[iVert])<>4 then
          return false;
        fi;
        rDE:=OnPoints(eDE, PLori.invers);
        iFace:=VEFori.ListOriginFace[rDE];
        if Length(VEFori.FaceSet[iFace])<>4 then
          return false;
        fi;
      fi;
    od;
    return true;
  end;
  IsThereRailroad:=function(ePair)
    local eSeq;
    for eSeq in ePair
    do
      if IsThereRailroadSeq(eSeq)=true then
        return true;
      fi;
    od;
    return false;
  end;
  IsTight:=function()
    local ePair;
    for ePair in ZZinfo.TotalListZigZag
    do
      if IsThereRailroad(ePair)=true then
        return false;
      fi;
    od;
    return true;
  end;
  ZZinfo.IsTightSelfMap:=IsTight();
  return ZZinfo;
end;






ZigZagAlt:=function(PlanGraph)
  local ListZigZag, ListZZL, iVert, iadj, FollowZZL, z, v, Sequence, SequenceRev, ListRaw, ListInvariants, Zmatrix, ROW, iZZ, jZZ, eZZ, ZZstring, i, ZZsimple, ZZself, ZZS, UNIQsimple, UNIQself, mult, obj, Sstring, SelfResult, INTV, Zuniformity, Zset, eZig, SetINTV, Zbalancedness, Pair, iElt, ListInt, ListIntersectionVectors, ListStrings, nbZZ, Occ, VCE, TotalListZigZag, ListTot, nbDE, LFace, ListIFace, pos, IsThereRailroadPair, IsTight, nbFace, iFace, eFace, eDE, IsThereRailroadSeq, IsItTightIcosahedrite;
  ListZigZag:=[];
  ListZZL:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    for iadj in [1..Length(PlanGraph[iVert])]
    do
      Add(ListZZL, ["N", [iVert, iadj]]);
      Add(ListZZL, ["P", [iVert, iadj]]);
    od;
  od;
  FollowZZL:=function(ZZL)
    if ZZL[1]="P" then
      return ["N", PrevDE(PlanGraph, PrevDE(PlanGraph, ReverseDE(PlanGraph, ZZL[2])))];
    else
      return ["P", NextDE(PlanGraph, NextDE(PlanGraph, ReverseDE(PlanGraph, ZZL[2])))];
    fi;
  end;
  TotalListZigZag:=[];
  while (Length(ListZZL)>0)
  do
    z:=ListZZL[1];
    Sequence:=ShallowCopy([z]);
    SequenceRev:=ShallowCopy([ReverseZZL(PlanGraph, z)]);
    v:=FollowZZL(z);
    while(v<>z) 
    do
      Add(Sequence, v);
      Add(SequenceRev, ReverseZZL(PlanGraph, v));
      v:=FollowZZL(v);
    od;
    Add(ListZigZag, Sequence);
    Add(TotalListZigZag, [Sequence, SequenceRev]);
    ListZZL:=Difference(ListZZL, Union(Sequence, SequenceRev));
  od;
  #
  ListRaw:=[];
  ListInvariants:=[];
  nbZZ:=Length(ListZigZag);
  for iZZ in [1..nbZZ]
  do
    eZZ:=ListZigZag[iZZ];
    SelfResult:=SelfMatchingDirEdge(PlanGraph, eZZ);
    ListRaw[iZZ]:=SelfResult[1];
    ListInvariants[iZZ]:=[Length(SelfResult[1]), Length(SelfResult[2]), Length(SelfResult[3])];
  od;
  Zmatrix:=MatrixOfIntersectionsWithTypes(PlanGraph, ListZigZag);

  ZZstring:="";
  ZZsimple:=[];
  ZZself:=[];
  for ZZS in ListInvariants
  do
    if ZZS[2]=0 and ZZS[3]=0 then
      Add(ZZsimple, ZZS);
    else
      Add(ZZself, ZZS);
    fi;
  od;
  UNIQsimple:=Collected(ZZsimple);
  UNIQself:=Collected(ZZself);
  for i in [1..Length(UNIQsimple)]
  do
    obj:=UNIQsimple[i][1];
    mult:=UNIQsimple[i][2];
    if mult=1 then
      ZZstring:=Concatenation(ZZstring, String(obj[1]));
    else
      ZZstring:=Concatenation(ZZstring, String(obj[1]),"^",StringLatex(mult));
    fi;
    if i<Length(UNIQsimple) then
      ZZstring:=Concatenation(ZZstring, ", ");
    fi;
  od;
  if Length(ZZsimple)>0 and Length(ZZself)>0 then
    ZZstring:=Concatenation(ZZstring, "; ");
  fi;
  for i in [1..Length(UNIQself)]
  do
    obj:=UNIQself[i][1];
    mult:=UNIQself[i][2];
    Sstring:=Concatenation(String(obj[1]),"_{",String(obj[2]),",",String(obj[3]),"}");
    if mult=1 then
      ZZstring:=Concatenation(ZZstring, Sstring);
    else
      ZZstring:=Concatenation(ZZstring, Sstring,"^",StringLatex(mult));
    fi;
    if i<Length(UNIQself) then
      ZZstring:=Concatenation(ZZstring, ", ");
    fi;
  od;
  if Length(Set(ListInvariants))=1 then
    Zuniformity:=true;
  else
    Zuniformity:=false;
  fi;


  # intersection vectors
  ListIntersectionVectors:=[];
  ListStrings:=[];
  for iZZ in [1..nbZZ]
  do
    ListInt:=[];
    for jZZ in [1..nbZZ]
    do
      VCE:=ShallowCopy(Zmatrix[iZZ][jZZ]);
      Sort(VCE);
      if iZZ<>jZZ then
        Sstring:=Concatenation("(", String(VCE[1]), ",",String(VCE[2]), ")");
        Add(ListInt, Sstring);
      fi;
    od;
    Occ:=Collected(ListInt);
    Add(ListIntersectionVectors, Occ);
    Add(ListStrings, SyncTextOccurrence(Occ));
  od;


  # Z-balancedness
  Zset:=Set(ListInvariants);
  Zbalancedness:=true;
  for iZZ in [1..Length(Zset)]
  do
    SetINTV:=[];
    for iElt in [1..Length(ListInvariants)]
    do
      if ListInvariants[iElt]=Zset[iZZ] then
        INTV:=ShallowCopy([]);
        for eZig in ListZigZag
        do
          Pair:=MatchingDirEdge(PlanGraph, ListZigZag[iElt], eZig);
          Add(INTV, Length(Pair[1])+Length(Pair[2]));
        od;
        Sort(INTV);
        Add(SetINTV, ShallowCopy(INTV));
      fi;
    od;
    if Length(Set(SetINTV))>1 then
      Zbalancedness:=false;
    fi;
  od;

  #
  # Tightness from icosahedrite viewpoint
  #
  ListTot:=ListDirectedEdges(PlanGraph);
  nbDE:=Length(ListTot);
  LFace:=__FaceSet(PlanGraph);
  nbFace:=Length(LFace);
  ListIFace:=ListWithIdenticalEntries(nbDE, 0);
  for iFace in [1..nbFace]
  do
    eFace:=LFace[iFace];
    for eDE in eFace
    do
      pos:=Position(ListTot, eDE);
      ListIFace[pos]:=iFace;
    od;
  od;
  IsThereRailroadSeq:=function(eSeq)
    local eZZL, eDE, eDE1, eDE2, eDE3, posDE1, posDE2, posDE3, iFace1, iFace2, iFace3, len1, len2, len3;
    for eZZL in eSeq
    do
      if eZZL[1]="P" then
        eDE:=eZZL[2];
        eDE1:=PrevDE(PlanGraph, eDE);
        eDE2:=PrevDE(PlanGraph, eDE1);
        eDE3:=PrevDE(PlanGraph, eDE2);
        posDE1:=Position(ListTot, eDE1);
        posDE2:=Position(ListTot, eDE2);
        posDE3:=Position(ListTot, eDE3);
        iFace1:=ListIFace[posDE1];
        iFace2:=ListIFace[posDE2];
        iFace3:=ListIFace[posDE3];
        len1:=Length(LFace[iFace1]);
        len2:=Length(LFace[iFace2]);
        len3:=Length(LFace[iFace3]);
        if len1<>3 or len2<>3 or len3<>4 then
          return false;
        fi;
      fi;
    od;
    return true;
  end;
  IsThereRailroadPair:=function(ePairZZ)
    local eSeq, test;
    for eSeq in ePairZZ
    do
      test:=IsThereRailroadSeq(eSeq);
#      Print("Seq: test=", test, "\n");
      if test=true then
        return true;
      fi;
    od;
    return false;
  end;
  IsItTightIcosahedrite:=function()
    local ePairZZ;
    for ePairZZ in TotalListZigZag
    do
      if IsThereRailroadPair(ePairZZ)=true then
        return false;
      fi;
    od;
    return true;
  end;
  IsTight:=IsItTightIcosahedrite();
  return rec(ListZigZag:=ListZigZag,
             ListRaw:=ListRaw,
             Zmatrix:=Zmatrix,
             Invariants:=ListInvariants,
             Zvector:=ZZstring,
             Zuniformity:=Zuniformity,
             Zbalancedness:=Zbalancedness,
             ListIntersectionVectors:=ListStrings,
             IsTightIcosahedrite:=IsTight,
             nbSimpleAlt:=Length(ZZsimple));
end;











NeighborhoodSequence:=function(PlanGraph, LZZ)
  local NextInFace, NextInLeftFace, NextInRightFace, ListFaceSignature, iZZ, ZZPATH, Left, Right, iP, DE, DEL, DER, LenLeft, LenRight, TxtL, TxtR, ListFaceS, FacOnLeft, FacOnRight, LenPath, FacLeft, FacRight;
  NextInLeftFace:=function(DirEdge)
    return NextDE(PlanGraph, ReverseDE(PlanGraph, DirEdge));
  end;
  NextInRightFace:=function(DirEdge)
    return PrevDE(PlanGraph, ReverseDE(PlanGraph, DirEdge));
  end;
  #
  ListFaceSignature:=[];
  ListFaceS:=[];
  
  for iZZ in [1..Length(LZZ)]
  do
    ZZPATH:=LZZ[iZZ];
    Left:=[];
    Right:=[];
    FacOnLeft:=[];
    FacOnRight:=[];

    LenPath:=Length(ZZPATH)/2;
    for iP in [1..LenPath]
    do
      DE:=ZZPATH[2*iP][2];
      DEL:=NextInLeftFace(DE);
      DER:=NextInRightFace(DE);
      LenLeft:=1;
      FacLeft:=[DEL[1]];
      LenRight:=1;
      FacRight:=[DER[1]];
      while (DEL<>DE)
      do
        DEL:=NextInLeftFace(DEL);
        Add(FacLeft, DEL[1]);
        LenLeft:=LenLeft+1;
      od;
      while (DER<>DE)
      do
        DER:=NextInRightFace(DER);
        Add(FacRight, DER[1]);
        LenRight:=LenRight+1;
      od;
      Left[iP]:=LenLeft;
      Right[iP]:=LenRight;
      FacOnLeft[iP]:=FacLeft;
      FacOnRight[iP]:=FacRight;
    od;
    TxtL:=SyncTextOccurrence(Collected(Left));
    TxtR:=SyncTextOccurrence(Collected(Right));
    #
    ListFaceS[iZZ]:=[FacOnLeft,FacOnRight];
    ListFaceSignature[iZZ]:=[TxtL, TxtR];
  od;
  return [ListFaceSignature, ListFaceS];
end;




#
#
# 3_n(F36) specific stuff


#
#
# PlanGraph is assumed to be a 3_n planar graph
F36_TestHexagon:=function(PlanGraph, ZZ)
  local NextInFace, iZZ, DE;
  NextInFace:=function(DirEdge)
    return NextDE(PlanGraph, ReverseDE(PlanGraph, DirEdge));
  end;
  for iZZ in [1..Length(ZZ)]
  do
    DE:=ZZ[iZZ][2];
    if NextInFace(NextInFace(NextInFace(DE)))=DE then
      return false;
    fi;
  od;
  return true;
end;




F36_MatrixIntersections:=function(PlanGraph,ZZ)
  local nbZZ, l1, l2, l3, L1, L2, L3, w1, w2, w3, iZZ, jZZ, InTS, Gra, symb, L, i, Con, MatriOrd, RowOrd;
  nbZZ:=Length(ZZ[4]);
  Gra:=NullGraph(Group(()), nbZZ);
  for iZZ in [1..nbZZ-1]
  do
    for jZZ in [iZZ+1..nbZZ]
    do
      InTS:=ZZ[3][iZZ][jZZ];
      if InTS[1]+InTS[2]=0 then
	AddEdgeOrbit(Gra, [iZZ, jZZ]);
	AddEdgeOrbit(Gra, [jZZ, iZZ]);
      fi;
    od;
  od;
  Con:=ConnectedComponents(Gra);
  #
  w1:=Length(Con[1])-1;
  w2:=Length(Con[2])-1;
  w3:=Length(Con[3])-1;
  #
  L1:=Length(ZZ[2][Con[1][1]]);
  l1:=(L1-4)/4;
  L2:=Length(ZZ[2][Con[2][1]]);
  l2:=(L2-4)/4;
  L3:=Length(ZZ[2][Con[3][1]]);
  l3:=(L3-4)/4;
  symb:=[[l1,w1],[l2,w2],[l3,w3]];
  L:=[];
  for i in [1..Length(Con[1])]
  do
    Add(L, Con[1][i]);
  od;
  for i in [1..Length(Con[2])]
  do
    Add(L, Con[2][i]);
  od;
  for i in [1..Length(Con[3])]
  do
    Add(L, Con[3][i]);
  od;
  MatriOrd:=[];
  for iZZ in [1..nbZZ]
  do
    RowOrd:=[];
    for jZZ in [1..nbZZ]
    do
      InTS:=ZZ[3][L[iZZ]][L[jZZ]];
      RowOrd[jZZ]:=InTS[1]+InTS[2];
    od;
    MatriOrd[iZZ]:=RowOrd;
  od;
  return [symb, MatriOrd];
end;




#
#
# ZZ is a zigzag,
# Trig is a triangle, this test if ZZ is incident to ZZ and if
# so returns the opposite triangle
F36_TestIncidence:=function(PlanGraph, eTrig, ZZ)
  local DElist, LenZZ, kL, DE, DEnext, pos, IdX, IdXm1, IdXp1, fTrig;
  DElist:=[];
  DElist[1]:=EdgeToDirEdge(PlanGraph, [eTrig[1],eTrig[2]]);
  DElist[2]:=EdgeToDirEdge(PlanGraph, [eTrig[2],eTrig[3]]);
  DElist[3]:=EdgeToDirEdge(PlanGraph, [eTrig[3],eTrig[1]]);
  LenZZ:=Length(ZZ);
  for kL in [1..LenZZ]
  do
    DE:=ZZ[PrevIdx(LenZZ,kL)][2];
    DEnext:=ZZ[kL][2];
    for pos in [1..3]
    do
      if Set([DE, DEnext])=Set([DElist[pos], DElist[NextIdx(3,pos)]]) or Set([DE, DEnext])=Set([ReverseDE(PlanGraph, DElist[pos]), ReverseDE(PlanGraph, DElist[NextIdx(3,pos)])]) then
        IdX:=NextKIdx(LenZZ, kL,LenZZ/2);
        IdXm1:=NextIdx(LenZZ, IdX);
        IdXp1:=PrevIdx(LenZZ, IdX);
        fTrig:=[ZZ[IdXm1][2][1],ZZ[IdX][2][1],ZZ[IdXp1][2][1]];
        return [pos, fTrig];
      fi;
    od;
  od;
  return false;
end;





F36_SpecZigZag:=function(PlanGraph, ZZ)
  local Faces, TrigS, eFac, nbZZ, IncTrigZZ, iTrig, eTrig, LCK, iZZ, eZZ, PoSD, Pair, PairSet, Matri, ePair, Trig1, Trig2, Pos1, Pos2, TrigSet, i;
  Faces:=PlanGraphToVEF(PlanGraph)[3];
  TrigS:=[];
  TrigSet:=[];
  for eFac in Faces
  do
    if Length(eFac)=3 then
      AddSet(TrigS,eFac);
      AddSet(TrigSet,Set(eFac));
    fi;
  od;
  nbZZ:=Length(ZZ[4]);
  IncTrigZZ:=[];
  PairSet:=[];
  for iTrig in [1..4]
  do
    eTrig:=TrigS[iTrig];
    LCK:=[0,0,0];
    for iZZ in [1..nbZZ]
    do
      eZZ:=ZZ[1][iZZ];
      PoSD:=F36_TestIncidence(PlanGraph, eTrig, eZZ);
      if PoSD<>false then
        Pair:=[Set([Set(eTrig),Set(PoSD[2])]), iZZ];
        AddSet(PairSet, Pair);
        LCK[PoSD[1]]:=iZZ;
      fi;
    od;
    IncTrigZZ[iTrig]:=LCK;
  od;
  Matri:=[];
  for i in [1..4]
  do
    Matri[i]:=[[],[],[],[]];
  od;
  for ePair in PairSet
  do
    Trig1:=ePair[1][1];
    Trig2:=ePair[1][2];
    Pos1:=Position(TrigSet,Trig1);
    Pos2:=Position(TrigSet,Trig2);
    AddSet(Matri[Pos1][Pos2], ePair[2]);
    AddSet(Matri[Pos2][Pos1], ePair[2]);
  od;
  return [TrigS, IncTrigZZ, PairSet, Matri];
end;








F36_TestIrreducibility:=function(PlanGraph, LZZ)
  local U;
  for U in LZZ
  do
    if F36_TestHexagon(PlanGraph, U)=true then
      return false;
    fi;
    if F36_TestHexagon(PlanGraph, ReverseZZ(PlanGraph, U))=true then
      return false;
    fi;
  od;
  return true;
end;




F36_IsTwoConnected:=function(PlanGraph)
  local Faces, Trig, iFac, i, j;
  Faces:=PlanGraphToVEF(PlanGraph)[3];
  Trig:=[];
  for iFac in [1..Length(Faces)]
  do
    if Length(Faces[iFac])=3 then
      AddSet(Trig, Faces[iFac]);
    fi;
  od;
  for i in [1..Length(Trig)-1]
  do
    for j in [i+1..Length(Trig)]
    do
      if Intersection(Trig[i],Trig[j])<>[] then
        return false;
      fi;
    od;
  od;
  return true;
end;


#
#
# return a vector containing the number of hexagon having
# one adjacent triangle, two adjacent triangles, three adjacent ...
F36_MatchingHexagon:=function(PlanGraph)
  local InFo, DG, Faces, Trig, Hex, iFac, MatchingVector, iHex, Matched, match, PS, iM;
  InFo:=DualGraph(PlanGraph);
  DG:=InFo.PlanGraph;
  Faces:=InFo.Vertices;
  Trig:=[];
  Hex:=[];
  for iFac in [1..Length(Faces)]
  do
    if Length(Faces[iFac])=3 then
      AddSet(Trig, iFac);
    else
      AddSet(Hex, iFac);
    fi;
  od;
  MatchingVector:=[0,0,0,0,0];
  for iHex in Hex
  do
    Matched:=Intersection(Trig, DG[iHex]);
    match:=Length(Matched);
    PS:=[];
    for iM in [1..Length(Matched)]
    do
      PS[iM]:=Position(DG[iHex], Matched[iM]);
    od;
    if Length(PS)=2 then
      if NextKIdx(6,PS[1],3)=PS[2] then
        MatchingVector[5]:=MatchingVector[5]+1;
      fi;
    fi;
    MatchingVector[match+1]:=MatchingVector[match+1]+1;
  od;
  return MatchingVector;
end;



#
#
# PlanGraph is assumed to be an hexagon monogam 3n planar graph
F36_3nToFullerene:=function(PlanGraph)
  local Faces, Trig, iFac, NewPlanGraph, eTrig, a, b, c, aAdj, bAdj, cAdj, Posb, Posc;
  Faces:=PlanGraphToVEF(PlanGraph)[3];
  Trig:=[];
  for iFac in [1..Length(Faces)]
  do
    if Length(Faces[iFac])=3 then
      AddSet(Trig, Faces[iFac]);
    fi;
  od;
  NewPlanGraph:=ShallowCopy(PlanGraph);
  for eTrig in Trig
  do
    a:=eTrig[1];
    b:=eTrig[2];
    c:=eTrig[3];
    aAdj:=Difference(eTrig, PlanGraph[a])[1];
    bAdj:=Difference(eTrig, PlanGraph[b])[1];
    cAdj:=Difference(eTrig, PlanGraph[c])[1];
    Posb:=Position(PlanGraph[bAdj],b);
    Posc:=Position(PlanGraph[bAdj],b);
    #
    NewPlanGraph[b]:=ShallowCopy([]);
    NewPlanGraph[c]:=ShallowCopy([]);
    NewPlanGraph[bAdj][Posb]:=a;
    NewPlanGraph[cAdj][Posc]:=a;
    NewPlanGraph[a]:=[aAdj,bAdj,cAdj]; # NEED TO CHECK ORIENTATION
  od;
  return Renormalisation(NewPlanGraph);
end;




#
#
#
# 4n specific stuff

F46_ListSignature:=function(PlanGraph, LZZ)
  local Faces, NG, eFac, Lsquare, nbSq, nbZZ, MatrixOcc, iZZ, LeftOcc, RightOcc, Left, Right, iFac, Pos;
  Faces:=PlanGraphToVEF(PlanGraph)[3];
  NG:=NeighborhoodSequence(PlanGraph, LZZ);
  Lsquare:=[];
  for eFac in Faces
  do
    if Length(eFac)=4 then
      AddSet(Lsquare, Set(eFac));
    fi;
  od; 
  nbSq:=Length(Lsquare);
  nbZZ:=Length(LZZ);
  MatrixOcc:=[];
  for iZZ in [1..nbZZ]
  do
    LeftOcc:=ListWithIdenticalEntries(nbSq, 0);
    RightOcc:=ListWithIdenticalEntries(nbSq, 0);
    Left:=NG[2][iZZ][1];
    Right:=NG[2][iZZ][2];
    for iFac in [1..Length(Left)]
    do
      eFac:=Left[iFac];
      if Length(eFac)=4 then
        Pos:=Position(Lsquare, Set(eFac));
        LeftOcc[Pos]:=LeftOcc[Pos]+1;
      fi;
    od;
    for iFac in [1..Length(Right)]
    do
      eFac:=Right[iFac];
      if Length(eFac)=4 then
        Pos:=Position(Lsquare, Set(eFac));
        RightOcc[Pos]:=RightOcc[Pos]+1;
      fi;
    od;
    MatrixOcc[iZZ]:=[LeftOcc, RightOcc];
  od;
  return [Lsquare, MatrixOcc];
end;





#
#
# Fullerene specific stuff



#
#
# return true if the PlanGraph is a fullerene
F56_IsFullerene:=function(PlanGraph)
  local LE, eFac, VEF, i;
  for i in [1..Length(PlanGraph)]
  do
    if Length(PlanGraph[i])<>3 then
      return false;
    fi;
  od;
  VEF:=PlanGraphToVEF(PlanGraph);
  #
  for eFac in VEF[3]
  do
    LE:=Length(eFac);
    if LE<>5 and LE<>6 then
      return false;
    fi;
  od;
  return true;
end;


#
#
# return true if the (assumed to be) fullerene has isolated pentagons
F56_IsIPFullerene:=function(PlanGraph)
  local VEF, Faces, Pent, eFac, nbPent, i, j;
  VEF:=PlanGraphToVEF(PlanGraph);
  Faces:=VEF[3];
  Pent:=[];
  for eFac in Faces
  do
    if Length(eFac)=5 then
      Add(Pent, eFac);
    fi;
  od;
  nbPent:=Length(Pent);
  for i in [1..nbPent-1]
  do
    for j in [i+1..nbPent]
    do
      if Intersection(Pent[i], Pent[j])<>[] then
        return false;
      fi;
    od;
  od;
  return true;
end;



#
#
# IPT stands for Isolated Pentagon Triples
F56_IPTfullereneTo3n:=function(PlanGraph)
  local Faces, Pent, eFac, nbV, VertexSelect, iVert, match, iPent, Comb, SolSet, eComb, v1,v2,v3,v4, SolGraph, Oadj, a, b, c, AN, BN, CN, PosAi, PosBi, PosCi, NewPlanGraph;
  Faces:=PlanGraphToVEF(PlanGraph)[3];
  Pent:=[];
  for eFac in Faces
  do
    if Length(eFac)=5 then
      AddSet(Pent, eFac);
    fi;
  od;
  nbV:=Length(PlanGraph);
  VertexSelect:=[];
  for iVert in [1..nbV]
  do
    match:=ShallowCopy([]);
    for iPent in [1..Length(Pent)]
    do
      if iVert in Pent[iPent] then
        AddSet(match, iPent);
      fi;
    od;
    if Length(match)=3 then
      AddSet(VertexSelect, [iVert, match]);
    fi;
  od;
  Comb:=Combinations([1..Length(VertexSelect)],4);
  SolSet:=[];
  for eComb in Comb
  do
    v1:=eComb[1];
    v2:=eComb[2];
    v3:=eComb[3];
    v4:=eComb[4];
    if Length(Union(VertexSelect[v1][2],VertexSelect[v1][2],VertexSelect[v1][2],VertexSelect[v1][2]))=12 then
      AddSet(SolSet,eComb);
    fi;
  od;
  if Length(SolSet)=0 then
    return false;
  fi;
  SolGraph:=[];
  for eComb in SolSet
  do
    NewPlanGraph:=ShallowCopy(PlanGraph);
    nbV:=Length(NewPlanGraph);
    for iVert in eComb
    do
      Oadj:=PlanGraph[iVert];
      a:=Oadj[1];
      b:=Oadj[2];
      c:=Oadj[3];
      AN:=nbV+1;
      BN:=nbV+2;
      CN:=nbV+3;
      PosAi:=Position(PlanGraph[a],iVert);
      PosBi:=Position(PlanGraph[b],iVert);
      PosCi:=Position(PlanGraph[c],iVert);
      #
      NewPlanGraph[a][PosAi]:=AN;
      NewPlanGraph[b][PosBi]:=BN;
      NewPlanGraph[c][PosCi]:=CN;
      NewPlanGraph[AN]:=[a,BN,CN];
      NewPlanGraph[BN]:=[AN,b,CN];
      NewPlanGraph[CN]:=[AN,BN,c];
      #
      nbV:=nbV+3;
    od;
    AddSet(SolGraph, Renormalisation(NewPlanGraph));
  od;
  return SolGraph;
end;




#
#
# this simple function can distinguish many noninvariant
# fullerenes
F56_FuncInvariantOfFullerene:=function(PlanGraph)
  local VEF, Faces, iP, iFac, jFac, ZZ;
  VEF:=PlanGraphToVEF(PlanGraph);
  ZZ:=ZigZag(PlanGraph);
  Faces:=VEF[3];
  iP:=0;
  for iFac in [1..Length(Faces)-1]
  do
    for jFac in [iFac+1..Length(Faces)]
    do
      if Intersection(Faces[iFac],Faces[jFac])<>[] then
        iP:=iP+1;
      fi;
    od;
  od;
  return [iP, ZZ[5]];
end;





#
#
#
# Groupism Stuff


#
# ZZaction works on pairs of zig zag in form:
# Set([[x1, ...., xn], [xn, ...., x1]])
ZZaction:=function(ZZpair, g)
  local ZZ1, ZZ2, ZZpu1, ZZpu2, i, n;
  ZZ1:=ZZpair[1];
  ZZ2:=ZZpair[2];
  ZZpu1:=[];
  ZZpu2:=[];
  n:=Length(ZZ1);
  for i in [1..n]
  do
    ZZpu1[i]:=OnPoints(ZZ1[i],g);
    ZZpu2[i]:=OnPoints(ZZ2[i],g);
  od;
  return Set([ThreeCanonicalization(ZZpu1), ThreeCanonicalization(ZZpu2)]);
end;



ZZtoCanonicSequence:=function(ZZ)
  local LU, j;
  LU:=ShallowCopy([]);
  for j in [1..Length(ZZ)]
  do
    LU[j]:=ZZ[j][2][1];
  od;
  return Set([ThreeCanonicalization(LU), ThreeCanonicalization(Reversed(LU))]);
end;


#
#
# LZZ is the output of the function ZigZag
# Group a subgroup of Aut(PlanGraph)
ZZorbits:=function(LZZ, G)
  local LZZelt, u, O, LSorbit, SizeO, iO;
  LZZelt:=[];
  for u in LZZ
  do
    Add(LZZelt, ZZtoCanonicSequence(u));
  od;
  O:=Orbits(G, LZZelt, ZZaction);
  LSorbit:=[];
  SizeO:=[];
  for iO in [1..Length(O)]
  do
    LSorbit[iO]:=O[iO][1][1];
    SizeO[iO]:=Length(O[iO]);
  od;
  return rec(ListOrbits:=LSorbit, SizeOrbits:=SizeO);
end;







RRaction:=function(RRpair, g)
  local RR1, RR2, RRpu1, RRpu2, i, n;
  RR1:=RRpair[1];
  RR2:=RRpair[2];
  RRpu1:=[];
  RRpu2:=[];
  n:=Length(RR1);
  for i in [1..n]
  do
    RRpu1[i]:=OnSets(RR1[i],g);
    RRpu2[i]:=OnSets(RR2[i],g);
  od;
  return Set([ThreeCanonicalization(RRpu1), ThreeCanonicalization(RRpu2)]);
end;



RRorbits:=function(RRS, G)
  local RRSelt, eRRS, LU, j, O, LSorbit, SizeO, iO;
  RRSelt:=[];
  for eRRS in RRS[2]
  do
    LU:=ShallowCopy([]);
    for j in [1..Length(eRRS)]
    do
      LU[j]:=Set(eRRS[j]);
    od;
    Add(RRSelt, Set([ThreeCanonicalization(LU), ThreeCanonicalization(Reversed(LU))]));
  od;
  O:=Orbits(G, RRSelt, RRaction);
  LSorbit:=[];
  SizeO:=[];
  for iO in [1..Length(O)]
  do
    LSorbit[iO]:=O[iO][1][1];
    SizeO[iO]:=Length(O[iO]);
  od;
  return [LSorbit, SizeO];
end;





#
#
# output the list of RailRoads (possibly self intersecting)
RailRoadSequence:=function(PlanGraph, LZZ)
  local LZZdouble, U, LZZRR, iZZ, nbDoubl, Treated, i, Kept, ZZL, NewZZL, pos, CellS, ListRailRoad, DE1, DE2, DE3, DE4, DE5, DE6, iHex, nbHex, iElt, eKept;
  LZZdouble:=[];
  for U in LZZ
  do
    Add(LZZdouble, U);
    Add(LZZdouble, ReverseZZ(PlanGraph,U));
  od;
  LZZRR:=[];
  for iZZ in [1..Length(LZZdouble)]
  do
    if TestHexagon(PlanGraph, LZZdouble[iZZ])=true then
      Add(LZZRR, LZZdouble[iZZ]);
    fi;
  od;
  nbDoubl:=Length(LZZRR);
  Treated:=[];
  for i in [1..nbDoubl]
  do
    Treated[i]:=0;
  od;
  Kept:=[];
  for i in [1..nbDoubl]
  do
    if Treated[i]=0 then
      if LZZRR[i][1][1]="N" then 
        ZZL:=LZZRR[i][1];
      else
        ZZL:=LZZRR[i][2];
      fi;
      NewZZL:=["N", NextDE(PlanGraph, ReverseDE(PlanGraph, PrevDE(PlanGraph, ZZL[2])))];
      pos:=1;
      while(Position(LZZRR[pos], NewZZL)=fail)
      do
        pos:=pos+1;
      od;
      Treated[i]:=1;
      Treated[pos]:=1;
      Add(Kept, LZZRR[i]);
    fi;
  od;
  ListRailRoad:=[];
  for iElt in [1..Length(Kept)]
  do
    eKept:=Kept[iElt];
    CellS:=ShallowCopy([]);
    nbHex:=Length(eKept)/2;
    for iHex in [1..nbHex]
    do
      DE1:=eKept[2*iHex-1][2];
      DE2:=NextDE(PlanGraph, ReverseDE(PlanGraph, DE1));
      DE3:=NextDE(PlanGraph, ReverseDE(PlanGraph, DE2));
      DE4:=NextDE(PlanGraph, ReverseDE(PlanGraph, DE3));
      DE5:=NextDE(PlanGraph, ReverseDE(PlanGraph, DE4));
      DE6:=NextDE(PlanGraph, ReverseDE(PlanGraph, DE5));
      CellS[iHex]:=[DE1[1],DE2[1],DE3[1],DE4[1],DE5[1],DE6[1]];
    od;
    ListRailRoad[iElt]:=CellS;
  od;
  return [Kept, ListRailRoad];
end;


#
#
# This procedure returns the list of hexagons that are intersected
# by several railroads
IntersectingRailRoads:=function(PlanGraph, RRS)
  local NewRRS, NewERRS, eRRS, eHex, HexagonSelfTwo, HexagonSelfTwoOtherOne, HexagonSelfThree, iRRS, SCT, h, jRRS, test, HexagonIntersectTwoDiff, HexagonIntersectThreeDiff, kRRS;

  NewRRS:=[];
  for eRRS in RRS[2]
  do
    NewERRS:=ShallowCopy([]);
    for eHex in eRRS
    do
      Add(NewERRS, Set(eHex));
    od;
    Add(NewRRS, NewERRS);
  od;
  # Search for railroads intersecting in an hexagon
  HexagonSelfTwo:=[];
  HexagonSelfTwoOtherOne:=[];
  HexagonSelfThree:=[];
  for iRRS in [1..Length(NewRRS)]
  do
    eRRS:=NewRRS[iRRS];
    SCT:=Set(eRRS);
    for h in SCT
    do
      if PositionNthOccurrence(eRRS,h,2)<>fail then
        if PositionNthOccurrence(eRRS,h,3)<>fail then
          Add(HexagonSelfThree, h);
        else
          test:=0;
          for jRRS in Difference([1..Length(NewRRS)],[iRRS])
          do
            if Position(NewRRS[jRRS], h)<>fail then
              test:=1;
            fi;
          od;
          if test=1 then
            Add(HexagonSelfTwoOtherOne, h);
          else
            Add(HexagonSelfTwo, h);
          fi;
        fi;
      fi;
    od;
  od;
  HexagonIntersectTwoDiff:=[];
  HexagonIntersectThreeDiff:=[];
  for iRRS in [1..Length(NewRRS)-1]
  do
    eRRS:=NewRRS[iRRS];
    SCT:=Set(eRRS);
    for h in SCT
    do
      for jRRS in [iRRS+1..Length(NewRRS)]
      do
        if Position(NewRRS[jRRS], h)<>fail then
          test:=0;
          for kRRS in [jRRS+1..Length(NewRRS)]
          do
            if Position(NewRRS[kRRS], h)<>fail then
              test:=1;
            fi;
          od;
          if test=1 then
            Add(HexagonIntersectThreeDiff, h);
          else
            Add(HexagonIntersectTwoDiff, h);
          fi;
        fi;
      od;
    od;
  od;
  return [HexagonSelfTwo, HexagonSelfTwoOtherOne, HexagonSelfThree, HexagonIntersectTwoDiff, HexagonIntersectThreeDiff];
end;





TestDoubleRailRoad:=function(PlanGraph, ZZ)
  if TestHexagon(PlanGraph, ZZ)=true and TestHexagon(PlanGraph, ReverseZZ(PlanGraph, ZZ))=true then
    return true;
  fi;
  return false;
end;



RemoveVertex:=function(PlanGraph, Vertex)
  local NewPlanGraph, iVert, Ladj, NewLadj, iCol;
  NewPlanGraph:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    if iVert <> Vertex then
      Ladj:=PlanGraph[iVert];
      NewLadj:=[];
      for iCol in [1..Length(Ladj)]
      do
        if Ladj[iCol] <> Vertex then
          Add(NewLadj, Ladj[iCol]);
        fi;
      od;
      Add(NewPlanGraph, NewLadj);
    else
      Add(NewPlanGraph, []);
    fi;
  od;
  return Renormalisation(NewPlanGraph);
end;



RemoveVertices:=function(PlanGraph, ListVertex)
  local NewPlanGraph, iVert, Ladj, NewLadj, iCol;
  NewPlanGraph:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    if Position(ListVertex, iVert)=fail then
      Ladj:=PlanGraph[iVert];
      NewLadj:=[];
      for iCol in [1..Length(Ladj)]
      do
        if Position(ListVertex, Ladj[iCol])=fail then
          Add(NewLadj, Ladj[iCol]);
        fi;
      od;
      Add(NewPlanGraph, NewLadj);
    else
      Add(NewPlanGraph, []);
    fi;
  od;
  return Renormalisation(NewPlanGraph);
end;


RemoveDegreeTwoVertices:=function(PL)
  local ListNewVert, NewPL, iVert, eDeg, Ladj, i, eDE, NextVert;
  ListNewVert:=Filtered([1..Length(PL)], x->Length(PL[x])>2);
  NewPL:=[];
  for iVert in ListNewVert
  do
    eDeg:=Length(PL[iVert]);
    Ladj:=[];
    for i in [1..eDeg]
    do
      eDE:=[iVert, i];
      while(true)
      do
        NextVert:=PL[eDE[1]][eDE[2]];
        if Length(PL[NextVert])>2 then
          break;
        fi;
        eDE:=NextDE(PL, ReverseDE(PL, eDE));
      od;
      Add(Ladj, Position(ListNewVert, NextVert));
    od;
    Add(NewPL, Ladj);
  od;
  return NewPL;
end;




Remove2valentVertices:=function(PlanGraph)
  local List2valent, iVert, NewPlanGraph, jVert, Ladj, eV, SE;
  List2valent:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    if Length(PlanGraph[iVert])=2 then
      Add(List2valent, iVert);
    fi;
  od;
  NewPlanGraph:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    if iVert in List2valent then
      Add(NewPlanGraph, []);
    else
      Ladj:=[];
      for jVert in [1..Length(PlanGraph[iVert])]
      do
        eV:=PlanGraph[iVert][jVert];
        if eV in List2valent then
          SE:=Difference(Set(PlanGraph[eV]), [iVert]);
          Add(Ladj, SE[1]);
        else
          Add(Ladj, eV);
        fi;
      od;
      Add(NewPlanGraph, Ladj);
    fi;
  od;
  return Renormalisation(NewPlanGraph);
end;



Duplicate2valentVertices:=function(PlanGraph)
  local List2valent, iVert, NewPlanGraph, NB, PosO, NewLadj, iAdj, eDE, rDE, Pos, jVert;
  List2valent:=[];
  for iVert in [1..Length(PlanGraph)]
  do
    if Length(PlanGraph[iVert])=2 then
      Add(List2valent, iVert);
    fi;
  od;
  NewPlanGraph:=[];
  NB:=Length(PlanGraph)+Length(List2valent);
  for iVert in [1..NB]
  do
    PosO:=Position(List2valent, iVert);
    if PosO=fail and iVert<=Length(PlanGraph) then
      NewLadj:=[];
      for iAdj in [1..3]
      do
        eDE:=[iVert, iAdj];
        rDE:=ReverseDE(PlanGraph, eDE);
        Pos:=Position(List2valent, rDE[1]);
        if Pos=fail then
          Add(NewLadj, rDE[1]);
        else
          if rDE[2]=1 then
            Add(NewLadj, rDE[1]);
          else
            Add(NewLadj, Length(PlanGraph)+Pos);
          fi;
        fi;
      od;
    elif PosO<>fail then
      NewLadj:=[PlanGraph[iVert][1], Length(PlanGraph)+PosO];
    else
      jVert:=List2valent[iVert-Length(PlanGraph)];
      NewLadj:=[PlanGraph[jVert][2], jVert];
    fi;
    Add(NewPlanGraph, NewLadj);
  od;
  return NewPlanGraph;
end;






RemoveEdge:=function(PlanGraph, Edge)
  local NewPlanGraph, eVert, Ladj, iAdj;
  NewPlanGraph:=[];
  for eVert in [1..Length(PlanGraph)]
  do
    if eVert=Edge[1][1] then
      Ladj:=[];
      for iAdj in [1..Length(PlanGraph[eVert])]
      do
        if iAdj<>Edge[1][2] then
          Add(Ladj, PlanGraph[eVert][iAdj]);
        fi;
      od;
    elif eVert=Edge[2][1] then
      Ladj:=[];
      for iAdj in [1..Length(PlanGraph[eVert])]
      do
        if iAdj<>Edge[2][2] then
          Add(Ladj, PlanGraph[eVert][iAdj]);
        fi;
      od;
    else
      Ladj:=PlanGraph[eVert];
    fi;
    Add(NewPlanGraph, Ladj);
  od;
  return Renormalisation(NewPlanGraph);
end;





#
#
# return true if the fullerene is not irreducible by sequences of
# hexagons
SearchRoadSelf:=function(PlanGraph, ZZ)
  local LZZ, U, iZZ, SelfS;
  LZZ:=ZZ.ListZigZag;
  for iZZ in [1..Length(LZZ)]
  do
    SelfS:=ZZ.ListRaw[iZZ];
    if SelfS[2]+SelfS[3]>0 then
      if TestHexagon(PlanGraph, LZZ[iZZ])=true then
        return iZZ;
      fi;
      if TestHexagon(PlanGraph, ReverseZZ(PlanGraph, LZZ[iZZ]))=true then
        return iZZ;
      fi;
    fi;
  od;
  return false;
end;






PlanGraphOrientedToABC:=function(PLori)
  local ePrev, ListFlags, nbDE, iDE, jDE, SetFlags, eListA, eListB, eListC, eFlag, eFlagA, nDE1, nDE2, eFlagB, eFlagC, val;
  ePrev:=Inverse(PLori.next);
  ListFlags:=[];
  nbDE:=PLori.nbP;
  for iDE in [1..nbDE]
  do
    jDE:=OnPoints(iDE, PLori.invers);
    Add(ListFlags, [iDE, 1]);
    Add(ListFlags, [iDE, 2]);
  od;
  SetFlags:=Set(ListFlags);
  if Length(SetFlags)<>Length(ListFlags) then
    Error("There are repetition in ListFlags. Not allowed");
  fi;
  eListA:=[];
  eListB:=[];
  eListC:=[];
  for eFlag in SetFlags
  do
    iDE:=eFlag[1];
    val:=eFlag[2];
    jDE:=OnPoints(iDE, PLori.invers);
    nDE1:=OnPoints(iDE, PLori.next);
    nDE2:=OnPoints(iDE, ePrev);
    eFlagA:=[jDE, 3-val];
    if val=1 then
      eFlagB:=[nDE1, 3-val];
    else
      eFlagB:=[nDE2, 3-val];
    fi;
    eFlagC:=[iDE, 3-val];
    Add(eListA, eFlagA);
    Add(eListB, eFlagB);
    Add(eListC, eFlagC);
  od;
  return rec(nbP:=Length(SetFlags),
             permA:=SortingPerm(eListA),
             permB:=SortingPerm(eListB),
             permC:=SortingPerm(eListC),
             ListFlags:=SetFlags);
end;


AutomorphismGroupPlanGraphOriented:=function(PLori)
  local nbDE, FuncCompletion, ListPerm, i, eList;
  nbDE:=PLori.nbP;
  FuncCompletion:=function(iDE)
    local IsFinished, ListValue, ListDone, i, j, iNext, jNext, iInv, jInv;
    ListValue:=ListWithIdenticalEntries(nbDE,0);
    ListDone:=ListWithIdenticalEntries(nbDE,0);
    ListValue[1]:=iDE;
    while(true)
    do
      IsFinished:=true;
      for i in [1..nbDE]
      do
        j:=ListValue[i];
        if j>0 and ListDone[i]=0 then
          ListDone[i]:=1;
          IsFinished:=false;
          iNext:=OnPoints(i, PLori.next);
          jNext:=OnPoints(j, PLori.next);
          iInv:=OnPoints(i, PLori.invers);
          jInv:=OnPoints(j, PLori.invers);
          if ListValue[iNext]>0 then
            if ListValue[iNext]<>jNext then
              return false;
            fi;
          fi;
          ListValue[iNext]:=jNext;
          if ListValue[iInv]>0 then
            if ListValue[iInv]<>jInv then
              return false;
            fi;
          fi;
          ListValue[iInv]:=jInv;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    return ListValue;
  end;
  ListPerm:=[];
  for i in [1..nbDE]
  do
    eList:=FuncCompletion(i);
    if eList<>false then
      Add(ListPerm, PermList(eList));
    fi;
  od;
  return Group(SmallGeneratingSet(PersoGroupPerm(ListPerm)));
end;



AutomorphismGroupABC:=function(PLabc)
  local nbDE, FuncCompletion, ListPerm, i, eList, ListGen;
  nbDE:=PLabc.nbP;
  FuncCompletion:=function(iDE)
    local IsFinished, ListValue, ListDone, i, j, iA, iB, iC, jA, jB, jC;
    ListValue:=ListWithIdenticalEntries(nbDE,0);
    ListDone:=ListWithIdenticalEntries(nbDE,0);
    ListValue[1]:=iDE;
    while(true)
    do
      IsFinished:=true;
      for i in [1..nbDE]
      do
        j:=ListValue[i];
        if j>0 and ListDone[i]=0 then
          ListDone[i]:=1;
          IsFinished:=false;
          iA:=OnPoints(i, PLabc.permA);
          jA:=OnPoints(j, PLabc.permA);
          iB:=OnPoints(i, PLabc.permB);
          jB:=OnPoints(j, PLabc.permB);
          iC:=OnPoints(i, PLabc.permC);
          jC:=OnPoints(j, PLabc.permC);
          if ListValue[iA]>0 then
            if ListValue[iA]<>jA then
              return false;
            fi;
          fi;
          ListValue[iA]:=jA;
          if ListValue[iB]>0 then
            if ListValue[iB]<>jB then
              return false;
            fi;
          fi;
          ListValue[iB]:=jB;
          if ListValue[iC]>0 then
            if ListValue[iC]<>jC then
              return false;
            fi;
          fi;
          ListValue[iC]:=jC;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    return ListValue;
  end;
  ListPerm:=[];
  for i in [1..nbDE]
  do
    eList:=FuncCompletion(i);
    if eList<>false then
      Add(ListPerm, PermList(eList));
    fi;
  od;
  ListGen:=SmallGeneratingSet(PersoGroupPerm(ListPerm));
  return PersoGroupPerm(ListGen);
end;


# return true or false
IsEquivalentABC:=function(PLabc1, PLabc2)
  local nbFlag, FuncCompletion, i, eList;
  if PLabc1.nbP<>PLabc2.nbP then
    return false;
  fi;
  nbFlag:=PLabc1.nbP;
  FuncCompletion:=function(iFlag)
    local IsFinished, ListValue, ListDone, i, j, iA, iB, iC, jA, jB, jC;
    ListValue:=ListWithIdenticalEntries(nbFlag,0);
    ListDone:=ListWithIdenticalEntries(nbFlag,0);
    ListValue[1]:=iFlag;
    while(true)
    do
      IsFinished:=true;
      for i in [1..nbFlag]
      do
        j:=ListValue[i];
        if j>0 and ListDone[i]=0 then
          ListDone[i]:=1;
          IsFinished:=false;
          iA:=OnPoints(i, PLabc1.permA);
          jA:=OnPoints(j, PLabc2.permA);
          iB:=OnPoints(i, PLabc1.permB);
          jB:=OnPoints(j, PLabc2.permB);
          iC:=OnPoints(i, PLabc1.permC);
          jC:=OnPoints(j, PLabc2.permC);
          if ListValue[iA]>0 then
            if ListValue[iA]<>jA then
              return false;
            fi;
          fi;
          ListValue[iA]:=jA;
          if ListValue[iB]>0 then
            if ListValue[iB]<>jB then
              return false;
            fi;
          fi;
          ListValue[iB]:=jB;
          if ListValue[iC]>0 then
            if ListValue[iC]<>jC then
              return false;
            fi;
          fi;
          ListValue[iC]:=jC;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    return ListValue;
  end;
  for i in [1..nbFlag]
  do
    eList:=FuncCompletion(i);
    if eList<>false then
      return true;
    fi;
  od;
  return false;
end;





GetAutomorphismGroupOriented:=function(PLori, VEFori)
  local nbDE, PLabc, GRPabc, ListSets, ListOriginDE, ListOriginIFace, i, eSet, nbVert, nbEdge, nbFace, iDE, iFlag, jFlag, jDE, jVert, jEdge, jFace, eList, eGen, ListGens, eS, nbFlag, ListSetFace, iFace, RecReturn, ListGenABC, jFlagA, jFlagB, jFlagC, GRAflag, TheBipartitionVect, LVectorNumber, VectorNumber1, VectorNumber2, SymGRP, phi, RecFlag, IsGraphSymmetryRotationABC, IsGraphSymmetryRotation, IsGraphSymmetryReflection, IsGraphSymmetryReflectionABC, GetPermutationDirectedEdge, SignatureInformation, IsPermutationCorrect, IsCorrectGroup, GetGRPabc, CycleOrd, ListVert_asSet, ListFace_asSet, ListVert_orCyc, ListFace_orCyc, ListFaceRev_asSet, ListFaceRev_orCyc, CCori, TheAdj, TheAdjImg, iVertImg, iVert, ComponentsStabilizedReflection, ComponentsStabilizedReflectionABC, LPerm, NaturePairFlag, ExpressIFlagAsVEF, GetPairCellsFromPairFlag, SwitchPairFlag, GetAllSwitching, GetIFaceFromFlag;
  nbDE:=PLori.nbP;
  nbVert:=Length(VEFori.VertSet);
  nbEdge:=Length(VEFori.EdgeSet);
  nbFace:=Length(VEFori.FaceSet);
  PLabc:=PlanGraphOrientedToABC(PLori);
  LPerm:=[PLabc.permA, PLabc.permB, PLabc.permC];
  nbFlag:=Length(PLabc.ListFlags);
  CycleOrd:=function(ePt, ePerm)
    local eCycle, fPt;
    eCycle:=[ePt];
    fPt:=ePt;
    while(true)
    do
      fPt:=OnPoints(fPt, ePerm);
      if fPt=ePt then
        return eCycle;
      fi;
      Add(eCycle, fPt);
    od;
  end;
  ListVert_asSet:=List(VEFori.VertSet, Set);
  ListVert_orCyc:=List(VEFori.VertSet, x->CycleOrd(x[1], PLori.next));
  ListFace_asSet:=List(VEFori.FaceSet, Set);
  ListFace_orCyc:=List(VEFori.FaceSet, x->CycleOrd(x[1], PLori.next*PLori.invers));
  ListFaceRev_asSet:=List(VEFori.FaceSet, x->Set(OnTuples(x, PLori.invers)));
  ListFaceRev_orCyc:=List(ListFaceRev_asSet, x->CycleOrd(x[1], PLori.invers*PLori.next));
  GetPermutationDirectedEdge:=function(ePermABC)
    local eList, iDE, iFlag, iFlagImg, eFlagImg, jDE;
    eList:=ListWithIdenticalEntries(nbDE,0);
    for iDE in [1..nbDE]
    do
      iFlag:=First([1..nbFlag], x->PLabc.ListFlags[x][1]=iDE);
      iFlagImg:=OnPoints(iFlag, ePermABC);
      eFlagImg:=PLabc.ListFlags[iFlagImg];
      jDE:=eFlagImg[1];
      eList[iDE]:=jDE;
    od;
    return PermList(eList);
  end;
  SignatureInformation:=function(eList1, eList2)
    local len, eList, grp1, test, ePerm2, eList2img;
    if Set(eList1)<>Set(eList2) then
      Error("It is likely to be inconsistent");
    fi;
    if Length(eList1)=2 then
      return rec(success:=true, vect:=[0,0]);
    fi;
    len:=Length(eList1);
    eList:=Concatenation([2..len],[1]);
    grp1:=Group([PermList(eList)]);
    test:=RepresentativeAction(grp1, eList1, eList2, Permuted);
    if test<>fail then
      return rec(success:=true, vect:=[1,0]);
    fi;
    ePerm2:=PermList(Reversed([1..len]));
    eList2img:=Permuted(eList2, ePerm2);
    test:=RepresentativeAction(grp1, eList1, eList2img, Permuted);
    if test<>fail then
      return rec(success:=true, vect:=[0,1]);
    fi;
    return rec(success:=false);
  end;
  IsPermutationCorrect:=function(ePermDE)
    local VectSign, eVert, eVertImg, eSign, eFace, eFaceImg, pos, eVertPrior, eFacePrior, fSign, uSign;
    VectSign:=[0,0];
    for eVert in ListVert_orCyc
    do
      eVertImg:=List(eVert, x->OnPoints(x,ePermDE));
      pos:=Position(ListVert_asSet, Set(eVertImg));
      if pos=fail then
        return false;
      fi;
      eVertPrior:=ListVert_orCyc[pos];
      eSign:=SignatureInformation(eVertPrior, eVertImg);
      if eSign.success=false then
        return false;
      fi;
      VectSign:=VectSign + eSign.vect;
    od;
    if VectSign[1] > 0 and VectSign[2]>0 then
      return false;
    fi;
    if VectSign[1]>0 then
      fSign:=1;
    else
      fSign:=-1;
    fi;
    for eFace in ListFace_orCyc
    do
      if fSign=1 then
        eFaceImg:=OnTuples(eFace, ePermDE);
      else
        eFaceImg:=OnTuples(eFace, ePermDE*PLori.invers);
      fi;
      pos:=Position(ListFace_asSet, Set(eFaceImg));
      if pos=fail then
        return false;
      fi;
      eFacePrior:=ListFace_orCyc[pos];
      uSign:=SignatureInformation(eFacePrior, eFaceImg);
      if uSign.success=false then
        return false;
      fi;
      VectSign:=VectSign + uSign.vect;
    od;
    if VectSign[1] > 0 and VectSign[2]>0 then
      return false;
    fi;
    return true;
  end;
  IsCorrectGroup:=function(grpABC)
    local eGenABC, eGenDE;
    for eGenABC in GeneratorsOfGroup(grpABC)
    do
      eGenDE:=GetPermutationDirectedEdge(eGenABC);
      if IsPermutationCorrect(eGenDE)=false then
        return false;
      fi;
    od;
    return true;
  end;
  GetGRPabc:=function()
    local TestGRP, ListCorrElt, eEltABC, eEltDE, GRPret, LGen, FinalGRP;
    TestGRP:=AutomorphismGroupABC(PLabc);
    if IsCorrectGroup(TestGRP) then
      return TestGRP;
    fi;
    ListCorrElt:=[];
    for eEltABC in TestGRP
    do
      eEltDE:=GetPermutationDirectedEdge(eEltABC);
      if IsPermutationCorrect(eEltDE)=true then
        Add(ListCorrElt, eEltABC);
      fi;
    od;
    GRPret:=PersoGroupPerm(ListCorrElt);
    LGen:=SmallGeneratingSet(GRPret);
    FinalGRP:=PersoGroupPerm(LGen);
    return FinalGRP;
  end;
  GRPabc:=GetGRPabc();
  ListSets:=[];
  ListOriginDE:=ListWithIdenticalEntries(nbFlag, 0);
  for i in [1..nbDE]
  do
    eSet:=Filtered([1..Length(PLabc.ListFlags)], x->PLabc.ListFlags[x][1]=i);
    Add(ListSets, eSet);
    ListOriginDE{eSet}:=ListWithIdenticalEntries(Length(eSet), i);
  od;
  GetIFaceFromFlag:=function(iFlag)
    local iDE, val, rDE;
    iDE:=PLabc.ListFlags[iFlag][1];
    val:=PLabc.ListFlags[iFlag][2];
    if val = 1 then
      return VEFori.ListOriginFace[iDE];
    else
      rDE:=OnPoints(iDE, PLori.invers);
      return VEFori.ListOriginFace[rDE];
    fi;
  end;
  ListSetFace:=[];
  ListOriginIFace:=ListWithIdenticalEntries(nbFlag, 0);
  for iFace in [1..nbFace]
  do
    Add(ListSetFace, []);
  od;
  for iFlag in [1..nbFlag]
  do
    iFace:=GetIFaceFromFlag(iFlag);
    Add(ListSetFace[iFace], iFlag);
    ListOriginIFace[iFlag]:=iFace;
  od;
  GRAflag:=NullGraph(Group(()), nbFlag);
  for iFlag in [1..nbFlag]
  do
    jFlagA:=OnPoints(iFlag, PLabc.permA);
    AddEdgeOrbit(GRAflag, [iFlag, jFlagA]);
    jFlagB:=OnPoints(iFlag, PLabc.permB);
    AddEdgeOrbit(GRAflag, [iFlag, jFlagB]);
    jFlagC:=OnPoints(iFlag, PLabc.permC);
    AddEdgeOrbit(GRAflag, [iFlag, jFlagC]);
  od;
  TheBipartitionVect:=GetBipartition(GRAflag);
  VectorNumber1:=Filtered([1..nbFlag], x->TheBipartitionVect[x]=1);
  VectorNumber2:=Filtered([1..nbFlag], x->TheBipartitionVect[x]=2);
  LVectorNumber:=[VectorNumber1, VectorNumber2];
  IsGraphSymmetryRotationABC:=function(eSymABC)
    local ImagePart1, posImage;
    ImagePart1:=OnSets(VectorNumber1, eSymABC);
    posImage:=Position(LVectorNumber, ImagePart1);
    if posImage=1 then
      return true;
    fi;
    if posImage=2 then
      return false;
    fi;
    Error("Logical error, correct");
  end;
  NaturePairFlag:=function(SetFlag)
    local iFlag, jFlag, i, iFlagImg;
    iFlag:=SetFlag[1];
    jFlag:=SetFlag[2];
    for i in [1..3]
    do
      iFlagImg:=OnPoints(iFlag, LPerm[i]);
      if iFlagImg=jFlag then
        return i;
      fi;
    od;
    return -1;
  end;
  ExpressIFlagAsVEF:=function(iFlag)
    local iDE, iFace, iVert, iEdge;
    iDE:=PLabc.ListFlags[iFlag][1];
    iFace:=GetIFaceFromFlag(iFlag);
    iVert:=VEFori.ListOriginVert[iDE];
    iEdge:=VEFori.ListOriginEdge[iDE];
    return Set([iVert, iEdge+nbVert, iFace+nbVert+nbEdge]);
  end;
  GetPairCellsFromPairFlag:=function(ePairFlag)
    local eVEF1, eVEF2;
    eVEF1:=ExpressIFlagAsVEF(ePairFlag.SetFlag[1]);
    eVEF2:=ExpressIFlagAsVEF(ePairFlag.SetFlag[2]);
    return Intersection([eVEF1, eVEF2]);
  end;
  IsGraphSymmetryReflectionABC:=function(eSymABC)
    local iFlag, iPerm;
    for iFlag in [1..nbFlag]
    do
      jFlag:=OnPoints(iFlag, eSymABC);
      iPerm:=NaturePairFlag([iFlag, jFlag]);
      if iPerm > 0 then
        return true;
      fi;
    od;
    return false;
  end;
  SwitchPairFlag:=function(ePairFlag, ListParPerm)
    local PartGRP, O, siz, eFlipPerm, pos, i, fSetFlag, iPerm, eProd;
    PartGRP:=Group(ListParPerm);
    O:=Orbit(PartGRP, ePairFlag.SetFlag[1], OnPoints);
    siz:=Length(O)/2;
    eFlipPerm:=();
    pos:=1;
    for i in [1..siz]
    do
      eFlipPerm:=eFlipPerm*ListParPerm[pos];
      pos:=3-pos;
    od;
    eProd:=eFlipPerm*eFlipPerm;
    if First(O, x->OnPoints(x, eProd)<>x)<>fail then
      Error("Logical problem in construction of the Coxeter group");
    fi;
    fSetFlag:=OnSets(ePairFlag.SetFlag, eFlipPerm);
    iPerm:=NaturePairFlag(fSetFlag);
    if iPerm=-1 then
      Error("We have iPerm=-1 which is not allowed here");
    fi;
    return rec(iPerm:=iPerm, SetFlag:=fSetFlag);
  end;
  GetAllSwitching:=function(ePairFlag)
    local RetListPairFlag, jPerm, eSetAllow, ListParPerm, fPairFlag;
    RetListPairFlag:=[];
    for jPerm in [1..3]
    do
      if jPerm<>ePairFlag.iPerm then
        eSetAllow:=Set([jPerm, ePairFlag.iPerm]);
        ListParPerm:=LPerm{eSetAllow};
        fPairFlag:=SwitchPairFlag(ePairFlag, ListParPerm);
	Add(RetListPairFlag, fPairFlag);
      fi;
    od;
    return RetListPairFlag;
  end;
  ComponentsStabilizedReflectionABC:=function(eSymABC)
    local ListStatusFlag, ListPairFlagStab, iFlag, jFlag, iPerm, iFlagImg, nbPairFlag, GRA, iPairFlag, ePairFlag, jPerm, eSetAllow, ListParPerm, fPairFlag, posPair, ListConnFlag, eConnFlag, ListCycles, eCycle, eVal, ListConnCell, eConnCell, lenCycle, ListConnWork, TheList, j, iCell;
    ListStatusFlag:=ListWithIdenticalEntries(nbFlag,1);
    ListPairFlagStab:=[];
    for iFlag in [1..nbFlag]
    do
      jFlag:=OnPoints(iFlag, eSymABC);
      if jFlag>iFlag then
        for iPerm in [1..3]
        do
          iFlagImg:=OnPoints(iFlag, LPerm[iPerm]);
          if iFlagImg=jFlag then
            Add(ListPairFlagStab, rec(iPerm:=iPerm, SetFlag:=Set([iFlag, jFlag])));
          fi;
        od;
      fi;
    od;
    nbPairFlag:=Length(ListPairFlagStab);
    GRA:=NullGraph(Group(()), nbPairFlag);
    for iPairFlag in [1..nbPairFlag]
    do
      ePairFlag:=ListPairFlagStab[iPairFlag];
      for fPairFlag in GetAllSwitching(ePairFlag)
      do
        posPair:=Position(ListPairFlagStab, fPairFlag);
	if posPair=fail then
	  Error("We did not find fPairFlag");
	fi;
	AddEdgeOrbit(GRA, [iPairFlag, posPair]);
	AddEdgeOrbit(GRA, [posPair, iPairFlag]);
      od;
    od;
    if IsUnionOfCycle(GRA)=false then
      Error("The graph should be an union of cycles");
    fi;
    ListConnWork:=ConnectedComponents(GRA);
    ListCycles:=FindAllShortestCycles(GRA);
    ListConnFlag:=[];
    ListConnCell:=[];
    for eCycle in ListCycles
    do
      eConnFlag:=[];
      TheList:=[];
      for eVal in eCycle
      do
        ePairFlag:=ListPairFlagStab[eVal];
        Add(TheList, GetPairCellsFromPairFlag(ePairFlag));
        Add(eConnFlag, ePairFlag);
      od;
      Add(ListConnFlag, eConnFlag);
      #
      lenCycle:=Length(eCycle);
      eConnCell:=[];
      for i in [1..lenCycle]
      do
        j:=NextIdx(lenCycle, i);
        iCell:=Intersection(TheList[i], TheList[j])[1];
	Add(eConnCell, iCell);
      od;
      Add(ListConnCell, eConnCell);
    od;
    return rec(ListConnFlag:=ListConnFlag, ListConnCell:=ListConnCell);
  end;
  ListGenABC:=GeneratorsOfGroup(GRPabc);
  ListGens:=[];
  for eGen in ListGenABC
  do
    eList:=[];
    for eS in VEFori.VertSet
    do
      iDE:=eS[1];
      iFlag:=ListSets[iDE][1];
      jFlag:=OnPoints(iFlag, eGen);
      jDE:=ListOriginDE[jFlag];
      jVert:=VEFori.ListOriginVert[jDE];
      Add(eList, jVert);
    od;
    for eS in VEFori.EdgeSet
    do
      iDE:=eS[1];
      iFlag:=ListSets[iDE][1];
      jFlag:=OnPoints(iFlag, eGen);
      jDE:=ListOriginDE[jFlag];
      jEdge:=VEFori.ListOriginEdge[jDE];
      Add(eList, jEdge + nbVert);
    od;
    for eS in ListSetFace
    do
      iFlag:=eS[1];
      jFlag:=OnPoints(iFlag, eGen);
      jFace:=ListOriginIFace[jFlag];
      Add(eList, jFace + nbVert + nbEdge);
    od;
    Add(ListGens, PermList(eList));
  od;
  SymGRP:=PersoGroupPerm(ListGens);
  phi:=GroupHomomorphismByImagesNC(SymGRP, GRPabc, ListGens, ListGenABC);
  IsGraphSymmetryRotation:=function(eSym)
    local eSymABC;
    eSymABC:=Image(phi, eSym);
    return IsGraphSymmetryRotationABC(eSymABC);
  end;
  IsGraphSymmetryReflection:=function(eSym)
    local eSymABC;
    eSymABC:=Image(phi, eSym);
    return IsGraphSymmetryReflectionABC(eSymABC);
  end;
  ComponentsStabilizedReflection:=function(eSym)
    local eSymABC;
    eSymABC:=Image(phi, eSym);
    return ComponentsStabilizedReflectionABC(eSymABC);
  end;
  CCori:=PlanGraphOrientedToCellComplex(PLori, VEFori);
  for eGen in GeneratorsOfGroup(SymGRP)
  do
    for iVert in [1..Length(CCori.ListCells)]
    do
      iVertImg:=OnPoints(iVert, eGen);
      TheAdj:=Adjacency(CCori.GraphHasse, iVert);
      TheAdjImg:=OnSets(TheAdj, eGen);
      if TheAdjImg<>Adjacency(CCori.GraphHasse, iVertImg) then
        Error("Inconsistency error in the generator");
      fi;
    od;
  od;
  RecFlag:=rec(IsGraphSymmetryRotation:=IsGraphSymmetryRotation, 
               IsGraphSymmetryReflection:=IsGraphSymmetryReflection,
               ComponentsStabilizedReflection:=ComponentsStabilizedReflection);
  RecReturn:=rec(RecFlag:=RecFlag, SymGRP:=SymGRP);
  return RecReturn;
end;

#return true or false
IsIsomorphicPlanGraphOriented:=function(PLori1, PLori2)
  local PLabc1, PLabc2;
  PLabc1:=PlanGraphOrientedToABC(PLori1);
  PLabc2:=PlanGraphOrientedToABC(PLori2);
  return IsEquivalentABC(PLabc1, PLabc2);
end;


GroupPlanOriented:=function(PLori)
  local CCori, SymmetryGroupEdge, FunctionSymmetry, GPU, VEFori, RecSymm;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  CCori:=PlanGraphOrientedToCellComplex(PLori, VEFori);
  RecSymm:=GetAutomorphismGroupOriented(PLori, VEFori);
  FunctionSymmetry:=function(GRP)
    return MapInformationSymmetryGroup(CCori, GRP, RecSymm.RecFlag);
  end;
  GPU:=FunctionSymmetry(RecSymm.SymGRP);
  SymmetryGroupEdge:=ReduceActionToEdge(CCori, RecSymm.SymGRP);
  return rec(CC:=CCori,
             SymmetryGroup:=RecSymm.SymGRP,
             SymmetryGroupEdge:=SymmetryGroupEdge,
             GenSymbol:=GPU.GenSymbol,
             GenSymbolLatex:=GPU.GenSymbolLatex,
             TotalGroup:=GPU,
             FunctionSymmetry:=FunctionSymmetry);
end;



ComputeAllFlips:=function(PLori)
    local nbP, invers, next, prev, IsCorrect, ListPLori, iP, iP_rev, iP1, iP2, iP3, iP4, iP5, iP6, iP7, iP8, iP9, iP10, eList, NewPLori;
    nbP:=PLori.nbP;
    invers:=PLori.invers;
    next:=PLori.next;
    prev:=Inverse(next);
    IsCorrect:=function(ePLori)
        local GRP, n_orb, ListFace, ListLen;
        GRP:=Group([ePLori.next, ePLori.invers]);
        n_orb:=Length(Orbits(GRP, [1..nbP], OnPoints));
        if n_orb>1 then
            return false;
        fi;
        ListFace:=Orbits(Group([ePLori.next * ePLori.invers]), [1..nbP], OnPoints);
        ListLen:=List(ListFace, Length);
        if Set(ListLen)<>[3] then
            Error("Some faces do not have size 3");
        fi;
        return true;
    end;
    ListPLori:=[];
    for iP in [1..nbP]
    do
        iP_rev:=OnPoints(iP, invers);
        if iP < iP_rev then
            iP2 :=iP;
            iP5 :=iP_rev;
            iP3 :=OnPoints(iP2, next);
            iP1 :=OnPoints(iP2, prev);
            iP6 :=OnPoints(iP5, next);
            iP4 :=OnPoints(iP5, prev);
            iP7 :=OnPoints(iP3, invers);
            iP8 :=OnPoints(iP4, invers);
            iP9 :=OnPoints(iP6, invers);
            iP10:=OnPoints(iP1, invers);
            eList:=List([1..nbP], x->OnPoints(x,next));
            eList[iP2]:=iP10;
            eList[iP9]:=iP2;

            eList[iP1]:=iP3;

            eList[iP5]:=iP8;
            eList[iP7]:=iP5;

            eList[iP4]:=iP6;
            if PermList(eList)=fail then
                Error("Debug from here");
            fi;
            NewPLori:=rec(invers:=invers, next:=PermList(eList), nbP:=nbP);
            if IsCorrect(NewPLori) then
                Add(ListPLori, NewPLori);
            fi;
        fi;
    od;
    return ListPLori;
end;


GenerateFlipClass:=function(PLori)
    local ListPLori, InsertCand, pos, pos_prev, idx, ListSpann, eSpann;
    ListPLori:=[];
    InsertCand:=function(ePLori)
        local fPLori;
        for fPLori in ListPLori
        do
            if IsIsomorphicPlanGraphOriented(ePLori, fPLori) then
                return;
            fi;
        od;
        Add(ListPLori, ePLori);
        Print("Now |ListPLori|=", Length(ListPLori), "\n");
    end;
    InsertCand(PLori);
    pos:=1;
    while(true)
    do
        pos_prev:=Length(ListPLori);
        for idx in [pos..Length(ListPLori)]
        do
            ListSpann:=ComputeAllFlips(ListPLori[idx]);
            Print("|ListSpann|=", Length(ListSpann), "\n");
            for eSpann in ListSpann
            do
                InsertCand(eSpann);
            od;
        od;
        if pos_prev=Length(ListPLori) then
            break;
        fi;
        pos:=Length(ListPLori);
    od;
    Print("GenerateAllFlips |ListPLori|=", Length(ListPLori), "\n");
    return ListPLori;
end;









GetGroupsDirectedEdgePlanGraphOriented:=function(PLori)
  local GRPori, CCori, VEFori, nbP, ListDE, nbVert, iDE, iVert, iEdge, GetGroupDirectedEdge, GRPtot, GRProt;
  GRPori:=GroupPlanOriented(PLori);
  CCori:=GRPori.CC;
  VEFori:=CCori.VEF;
  nbP:=PLori.nbP;
  ListDE:=[];
  nbVert:=Length(VEFori.VertSet);
  for iDE in [1..nbP]
  do
    iVert:=VEFori.ListOriginVert[iDE];
    iEdge:=VEFori.ListOriginEdge[iDE];
    Add(ListDE, rec(iVert:=iVert, iEdge:=iEdge));
  od;
  GetGroupDirectedEdge:=function(TheGRP)
    local ListPermGenDE, eGRP, eGen, eList, eRecDE, iVert, iEdge, iVertImg, iEdgeImg, eRecDEimg, pos, GRPde;
    ListPermGenDE:=[];
    for eGen in GeneratorsOfGroup(TheGRP)
    do
      eList:=[];
      for iDE in [1..nbP]
      do
        eRecDE:=ListDE[iDE];
        iVert:=eRecDE.iVert;
        iEdge:=eRecDE.iEdge;
        iVertImg:=OnPoints(iVert, eGen);
        iEdgeImg:=OnPoints(iEdge + nbVert, eGen) - nbVert;
        eRecDEimg:=rec(iVert:=iVertImg, iEdge:=iEdgeImg);
        pos:=Position(ListDE, eRecDEimg);
        if pos=fail then
          Error("Please correct from that point");
        fi;
        Add(eList, pos);
      od;
      Add(ListPermGenDE, PermList(eList));
    od;
    GRPde:=PersoGroupPerm(ListPermGenDE);
    return GRPde;
  end;
  GRPtot:=GetGroupDirectedEdge(GRPori.SymmetryGroup);
  GRProt:=GetGroupDirectedEdge(GRPori.TotalGroup.RotationSubgroup);
  return rec(GRPtot:=GRPtot, GRProt:=GRProt);
end;





ProjectivePlaneFromCentrallySymmetric:=function(PL)
  local GRPinfo, eInv, nbV, O, VectStat, iO, eO, GRA, i, iVert, eAdj, j;
  GRPinfo:=GroupPlan(PL);
  eInv:=GRPinfo.TotalGroup.Inversion;
  nbV:=Length(PL)/2;
  O:=Orbits(Group([eInv]), [1..2*nbV], OnPoints);
  VectStat:=ListWithIdenticalEntries(2*nbV, 0);
  for iO in [1..nbV]
  do
    eO:=O[iO];
    VectStat{eO}:=ListWithIdenticalEntries(2, iO);
  od;
  GRA:=NullGraph(Group(()), nbV);
  for i in [1..nbV]
  do
    iVert:=O[i][1];
    for eAdj in PL[iVert]
    do
      j:=VectStat[eAdj];
      AddEdgeOrbit(GRA, [i, j]);
      AddEdgeOrbit(GRA, [j, i]);
    od;
  od;
  return GRA;
end;


CANONIC_PL_DoReordering:=function(PL, eDE)
  local nbVert, ListVerticesAssignment, ListVerticesAssignmentRev, eVert, eDE1, idx, iAdj, eAdj, ListStatus, PLnew, LAdj, LAdjB, pos, nbAdj, TheMin, eAdjNew, iVert, IsFinished, relAdj, jAdj, SelectedAdj, ListChange01, ListChange10, fAdj, SelectedVert, iVertNew;
  nbVert:=Length(PL);
  ListVerticesAssignment:=ListWithIdenticalEntries(nbVert,0);
  ListStatus:=ListWithIdenticalEntries(nbVert,0);
  ListVerticesAssignmentRev:=ListWithIdenticalEntries(nbVert,0);
  eVert:=eDE[1];
  ListVerticesAssignment[1]:=eVert;
  ListVerticesAssignmentRev[eVert]:=1;
  nbAdj:=Length(PL[eVert]);
  eDE1:=[eDE[1],eDE[2]];
  idx:=1;
  for iAdj in [1..nbAdj]
  do
    eAdj:=PL[eDE1[1]][eDE1[2]];
    idx:=idx+1;
    ListVerticesAssignment[idx]:=eAdj;
    ListVerticesAssignmentRev[eAdj]:=idx;
    eDE1:=NextDE(PL, eDE1);
  od;
  ListStatus[1]:=1;
  while(true)
  do
    IsFinished:=true;
    for iVertNew in [1..nbVert]
    do
      iVert:=ListVerticesAssignment[iVertNew];
      if ListStatus[iVertNew] = 0 and iVert > 0 then
        ListStatus[iVertNew]:=1;
        nbAdj:=Length(PL[iVert]);
        ListChange01:=[];
        ListChange10:=[];
        SelectedVert:=nbVert+1;
        SelectedAdj:=-1;
        for iAdj in [1..nbAdj]
        do
          jAdj:=NextIdx(nbAdj, iAdj);
          eAdj:=PL[iVert][iAdj];
          fAdj:=PL[iVert][jAdj];
          if ListVerticesAssignmentRev[eAdj] > 0 and ListVerticesAssignmentRev[fAdj] = 0 then
            Add(ListChange01, iAdj);
            if eAdj < SelectedVert then
              SelectedVert:=eAdj;
              SelectedAdj:=iAdj;
            fi;
          fi;
          if ListVerticesAssignmentRev[eAdj] = 0 and ListVerticesAssignmentRev[fAdj] > 0 then
            Add(ListChange10, jAdj);
          fi;
        od;
        if Length(ListChange01) <>Length(ListChange10) then
          Error("We have an inconsistency in ListChange01 and ListChange10\n");
        fi;
        if Length(ListChange01) > 0 then
          IsFinished:=false;
          relAdj:=SelectedAdj;
          for jAdj in [1..nbAdj]
          do
            relAdj:=NextIdx(nbAdj, relAdj);
            eAdj:=PL[iVert][relAdj];
            if ListVerticesAssignmentRev[eAdj] = 0 then
              idx:=idx+1;
              ListVerticesAssignment[idx]:=eAdj;
              ListVerticesAssignmentRev[eAdj]:=idx;
            fi;
          od;
        fi;
      fi;
    od;
    if IsFinished=false then
      break;
    fi;
  od;
  PLnew:=[];
  for iVertNew in [1..nbVert]
  do
    iVert:=ListVerticesAssignment[iVertNew];
    nbAdj:=Length(PL[iVert]);
    LAdj:=[];
    for iAdj in [1..nbAdj]
    do
      eAdj:=PL[iVert][iAdj];
      eAdjNew:=ListVerticesAssignmentRev[eAdj];
      Add(LAdj, eAdjNew);
    od;
    TheMin:=Minimum(LAdj);
    pos:=Position(LAdj, TheMin);
    LAdjB:=[];
    for iAdj in [1..nbAdj]
    do
      Add(LAdjB, LAdj[pos]);
      pos:=NextIdx(nbAdj, pos);
    od;
    Add(PLnew, LAdjB);
  od;
  return PLnew;
end;

CANONIC_PL_SetReordering:=function(PL)
  local LPL, nbVert, iVert, len, ipos, eDE, PLreord;
  LPL:=[];
  nbVert:=Length(PL);
  for iVert in [1..nbVert]
  do
    len:=Length(PL[iVert]);
    for ipos in [1..len]
    do
      eDE:=[iVert, ipos];
      PLreord:=CANONIC_PL_DoReordering(PL, eDE);
      Add(LPL, PLreord);
    od;
  od;
  return Collected(LPL);
end;

CANONIC_PL_3valent_TestInequality:=function(PL1, PL2)
  local nbVert, iVert, len, iAdj;
  if Length(PL1)<>Length(PL2) then
    Error("The program is not designed for that");
  fi;
  nbVert:=Length(PL1);
  for iAdj in [1..3]
  do
    for iVert in [1..nbVert]
    do
      if PL1[iAdj] < PL2[iAdj] then
        return 1;
      fi;
      if PL2[iAdj] < PL1[iAdj] then
        return -1;
      fi;
    od;
  od;
  return 0;
end;

CANONIC_PL_MinimumInfo:=function(PL)
  local LPLreord, TheMinPL, test, nbClass, iClass, ePLcand, ListDE, ListStatus, nbVert, eDEfirst, iVert, len, iAdj, eDE, ePL, eStatus;
  LPLreord:=CANONIC_PL_SetReordering(PL);
  TheMinPL:=LPLreord[1][1];
  nbClass:=Length(LPLreord);
  for iClass in [2..nbClass]
  do
    ePLcand:=LPLreord[iClass][1];
    test:=CANONIC_PL_3valent_TestInequality(TheMinPL, ePLcand);
    if test=1 then
      TheMinPL:=ePLcand;
    fi;
  od;
  ListDE:=[];
  ListStatus:=[];
  nbVert:=Length(TheMinPL);
  eDEfirst:=[1,1];
  if TheMinPL<>CANONIC_PL_DoReordering(TheMinPL, eDEfirst) then
    Error("A piece of understanding is missing");
  fi;
  for iVert in [1..nbVert]
  do
    len:=Length(TheMinPL[iVert]);
    for iAdj in [1..len]
    do
      eDE:=[iVert, iAdj];
      ePL:=CANONIC_PL_DoReordering(TheMinPL, eDE);
      if ePL<>TheMinPL then
        eStatus:=0;
      else
        eStatus:=1;
      fi;
      Add(ListDE, eDE);
      Add(ListStatus, eStatus);
    od;
  od;
  return rec(TheMinPL:=TheMinPL,
             ListDE:=ListDE, ListStatus:=ListStatus);
end;



# A list of face to be collapsed
InverseTruncationOrientedSelect:=function(PLori, VEFori, ListFace)
  local nbVert, ListStatusVert, eDeg, ListVertSets, eFace, NSet, eDE, eVert, nbSet, iSet, jSet, eInt, ListDE, TotalVertSet, eRec, iFace, eRecDE, rDE, nDE, eNext, eInv, ListNext, ListInv, ePermNext, ePermInv, iVert, nbDE, fVert, PLoriRet;
  nbVert:=VEFori.nbVert;
  ListStatusVert:=ListWithIdenticalEntries(nbVert,1);
  ListVertSets:=[];
  for eFace in VEFori.FaceSet{ListFace}
  do
    NSet:=[];
    for eDE in eFace
    do
      eVert:=VEFori.ListOriginVert[eDE];
      eDeg:=Length(VEFori.VertSet[eVert]);
      if eDeg<>3 then
        return rec(success:=false, reason:="degrees should be 3 for vertices from truncated faces");
      fi;
      ListStatusVert[eVert]:=0;
      Add(NSet, eVert);
    od;
    Add(ListVertSets, Set(NSet));
  od;
  #
  nbSet:=Length(ListVertSets);
  for iSet in [1..nbSet-1]
  do
    for jSet in [iSet+1..nbSet]
    do
      eInt:=Intersection(ListVertSets[iSet], ListVertSets[jSet]);
      if Length(eInt)<>0 then
        return rec(success:=false, reason:="adjacent k-gons to be inverse truncated");
      fi;
    od;
  od;
  #
  ListDE:=[];
  TotalVertSet:=[];
  for iVert in [1..nbVert]
  do
    if ListStatusVert[iVert]=1 then
      eRec:=rec(eNat:=1, eVert:=iVert);
      Add(TotalVertSet, eRec);
      for eDE in VEFori.VertSet[iVert]
      do
        eRecDE:=rec(eNat:=1, eVert:=iVert, eDE:=eDE);
        Add(ListDE, eRecDE);
      od;
    fi;
  od;
  for iFace in ListFace
  do
    eRec:=rec(eNat:=0, iFace:=iFace);
    Add(TotalVertSet, eRec);
    for eDE in VEFori.FaceSet[iFace]
    do
      nDE:=OnPoints(eDE, PLori.next*PLori.next);
      eRecDE:=rec(eNat:=0, iFace:=iFace, eDE:=nDE);
      Add(ListDE, eRecDE);
    od;
  od;
  nbDE:=Length(ListDE);
  #
  ListNext:=[];
  ListInv:=[];
  for eRecDE in ListDE
  do
    if eRecDE.eNat=1 then
      nDE:=OnPoints(eRecDE.eDE, PLori.next);
      eNext:=First([1..nbDE], x->ListDE[x].eNat=1 and ListDE[x].eDE=nDE);
      #
      rDE:=OnPoints(eRecDE.eDE, PLori.invers);
      fVert:=VEFori.ListOriginVert[rDE];
      if ListStatusVert[fVert]=1 then
        eInv:=First([1..nbDE], x->ListDE[x].eNat=1 and ListDE[x].eDE=rDE);
      else
        eInv:=First([1..nbDE], x->ListDE[x].eNat=0 and ListDE[x].eDE=rDE);
      fi;
    else
      nDE:=OnPoints(eRecDE.eDE, PLori.next*PLori.invers*PLori.next);
      eNext:=Position(ListDE, rec(eNat:=0, iFace:=eRecDE.iFace, eDE:=nDE));
      #
      rDE:=OnPoints(eRecDE.eDE, PLori.invers);
      fVert:=VEFori.ListOriginVert[rDE];
      if ListStatusVert[fVert]=1 then
        eInv:=First([1..nbDE], x->ListDE[x].eNat=1 and ListDE[x].eDE=rDE);
      else
        eInv:=First([1..nbDE], x->ListDE[x].eNat=0 and ListDE[x].eDE=rDE);
      fi;
    fi;
    Add(ListNext, eNext);
    Add(ListInv, eInv);
  od;
  ePermNext:=PermList(ListNext);
  ePermInv:=PermList(ListInv);
  if ePermNext=fail or ePermInv=fail then
    Error("Inconsistency in the perm lists");
  fi;
  PLoriRet:=rec(nbP:=Length(ListDE), next:=ePermNext, invers:=ePermInv);
  return rec(success:=true, PLori:=PLoriRet);
end;

TruncationOrientedSelect:=function(PLori, VEFori, ListIVert)
  local nbVert, ListStatusVert, NewListDE, nbDE, iVert, i, ePrev, ListNext, ListInv, eDEnew, eDEnewInv, eDEnewNext, iDE, rDE, nDE, pDE, fVert, pos, posNext, ePermNext, ePermInv;
  nbVert:=Length(VEFori.VertSet);
  ListStatusVert:=ListWithIdenticalEntries(nbVert,0);
  ListStatusVert{ListIVert}:=ListWithIdenticalEntries(Length(ListIVert),1);
  NewListDE:=[];
  nbDE:=PLori.nbP;
  for iDE in [1..nbDE]
  do
    iVert:=VEFori.ListOriginVert[iDE];
    if ListStatusVert[iVert]=0 then
      Add(NewListDE, [0,iDE]);
    else
      for i in [1..3]
      do
        Add(NewListDE, [1,iDE,i]);
      od;
    fi;
  od;
  ePrev:=Inverse(PLori.next);
  ListNext:=[];
  ListInv:=[];
  for eDEnew in NewListDE
  do
    iDE:=eDEnew[2];
    rDE:=OnPoints(iDE, PLori.invers);
    nDE:=OnPoints(iDE, PLori.next);
    pDE:=OnPoints(iDE, ePrev);
    if eDEnew[1]=0 then
      fVert:=VEFori.ListOriginVert[rDE];
      if ListStatusVert[fVert]=0 then
        eDEnewInv:=[0,rDE];
      else
        eDEnewInv:=[1,rDE,1];
      fi;
      eDEnewNext:=[0,nDE];
    else
      pos:=eDEnew[3];
      posNext:=NextIdx(3,pos);
      eDEnewNext:=[1,iDE,posNext];
      if pos=1 then
        fVert:=VEFori.ListOriginVert[rDE];
        if ListStatusVert[fVert]=0 then
          eDEnewInv:=[0,rDE];
        else
          eDEnewInv:=[1,rDE,1];
        fi;
      else
        if pos=2 then
          eDEnewInv:=[1,nDE,3];
        fi;
        if pos=3 then
          eDEnewInv:=[1,pDE,2];
        fi;
      fi;
    fi;
    Add(ListNext, Position(NewListDE, eDEnewNext));
    Add(ListInv, Position(NewListDE, eDEnewInv));
  od;
  ePermNext:=PermList(ListNext);
  ePermInv:=PermList(ListInv);
  if ePermNext=fail or ePermInv=fail then
    Error("Inconsistency in the perm lists");
  fi;
  return rec(nbP:=Length(NewListDE), next:=ePermNext, invers:=ePermInv);
end;


TruncationOriented:=function(PLori)
  local VEFori, nbVert, ListIVert;
  VEFori:=PlanGraphOrientedToVEF(PLori);
  nbVert:=Length(VEFori.VertSet);
  ListIVert:=[1..nbVert];
  return TruncationOrientedSelect(PLori, VEFori, ListIVert);
end;


DuplicationVertexOriented:=function(PLori)
  local NewListDE, nbP, i, j, eListNext, eListInv, eDE, eDEinv, eDEnext, posNext, posInv;
  nbP:=PLori.nbP;
  NewListDE:=[];
  for i in [1..nbP]
  do
    for j in [0..1]
    do
      Add(NewListDE, rec(side:=j, iDE:=i));
    od;
  od;
  #
  eListNext:=[];
  eListInv:=[];
  for eDE in NewListDE
  do
    eDEinv:=rec(side:=1-eDE.side, iDE:=eDE.iDE);
    if eDE.side=0 then
      eDEnext:=rec(side:=0, iDE:=OnPoints(eDE.iDE, PLori.next));
    else
      eDEnext:=rec(side:=1, iDE:=OnPoints(eDE.iDE, PLori.invers));
    fi;
    posNext:=Position(NewListDE, eDEnext);
    posInv :=Position(NewListDE, eDEinv);
    Add(eListNext, posNext);
    Add(eListInv, posInv);
  od;
  return rec(nbP:=Length(NewListDE), next:=PermList(eListNext), invers:=PermList(eListInv));
end;





ReducePlanGraphToSelectVertices:=function(PL, eConn)
  local NewPL, nbVert, iVert, eVert, LAdj, eAdj, pos;
  NewPL:=[];
  nbVert:=Length(eConn);
  for iVert in [1..nbVert]
  do
    eVert:=eConn[iVert];
    LAdj:=[];
    for eAdj in PL[eVert]
    do
      pos:=Position(eConn, eAdj);
      if pos<>fail then
        Add(LAdj, pos);
      fi;
    od;
    Add(NewPL, LAdj);
  od;
  return NewPL;
end;






DetectErrorInListForPermutation:=function(eList)
  local len, i, j, val;
  len:=Length(eList);
  Print("len=", len, "\n");
  for i in [1..len]
  do
    val:=eList[i];
    if val < 1 or val > len then
      Print("Error at entry ", i, " val=", val, "\n");
    fi;
  od;
  for i in [1..len-1]
  do
    for j in [i+1..len]
    do
      if eList[i]=eList[j] then
        Print("Entry ", i, " and ", j, " have same value\n");
      fi;
    od;
  od;
end;
