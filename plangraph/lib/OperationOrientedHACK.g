#
#
# this procedure is defined for regular graph, number k should be
# prime with the valency
ShiftGraph:=function(PlanGraph, k)
  local FuncShift, NewPlanGraph, i;
  FuncShift:=function(LIST, k)
    local pos, NList, i;
    pos:=1;
    NList:=[];
    for i in [1..Length(LIST)]
    do
      Add(NList, LIST[pos]);
      pos:=NextKIdx(Length(LIST), pos, k);
    od;
    return NList;
  end;
  NewPlanGraph:=[];
  for i in [1..Length(PlanGraph)]
  do
    NewPlanGraph[i]:=FuncShift(PlanGraph[i],k);
  od;
  return NewPlanGraph;
end;













#
#
# this procedure allow us to build "Snub Cube" and "Snub dodecahedron"
# and more generally any snub construction we may want
Snub:=function(PlanGraph)
  local Faces, eFac, u, fFac, Sprev, Snext, nextFac, prevFac, PlanGraphLeft, PlanGraphRight, PlanGraphMixed, Pos1, Pos2, Pos3, Pos4, Pos5, Pos6, Pos, iElt, len, eVert, NewVertexSet;
  Faces:=PlanGraphToVEF(PlanGraph)[3];
  NewVertexSet:=[];
  for eFac in Faces
  do
    for u in eFac
    do
      AddSet(NewVertexSet, [u,eFac]);
    od;
  od;
  PlanGraphLeft:=[];
  PlanGraphMixed:=[];
  PlanGraphRight:=[];
  for iElt in [1..Length(NewVertexSet)]
  do
    eVert:=NewVertexSet[iElt][1];
    eFac:=NewVertexSet[iElt][2];
    len:=Length(eFac);
    Pos:=Position(eFac,eVert);
    #
    Sprev:=Set([eFac[PrevIdx(len,Pos)],eVert]);
    Snext:=Set([eFac[NextIdx(len,Pos)],eVert]);
    for fFac in Difference(Faces,[eFac])
    do
      if IsSubset(fFac, Sprev) then
        prevFac:=fFac;
      fi;
      if IsSubset(fFac, Snext) then
        nextFac:=fFac;
      fi;
    od;
    #
    Pos1:=Position(NewVertexSet,[eFac[PrevIdx(len,Pos)],eFac]);
    Pos2:=Position(NewVertexSet,[eFac[PrevIdx(len,Pos)],prevFac]);
    Pos3:=Position(NewVertexSet,[eVert,prevFac]);
    Pos4:=Position(NewVertexSet,[eVert,nextFac]);
    Pos5:=Position(NewVertexSet,[eFac[NextIdx(len,Pos)],nextFac]);
    Pos6:=Position(NewVertexSet,[eFac[NextIdx(len,Pos)],eFac]);
    #
    PlanGraphLeft[iElt]:=[Pos1,Pos2,Pos3,Pos4,Pos6];
    PlanGraphMixed[iElt]:=[Pos1,Pos3,Pos4,Pos6];
    PlanGraphRight[iElt]:=[Pos1,Pos3,Pos4,Pos5,Pos6];
  od;
  return rec(VertexSet:=NewVertexSet, LeftIsomer:=PlanGraphLeft, StraightIsomer:=PlanGraphMixed, RightIsomer:=PlanGraphRight);
end;




#
#
# input must be a planar 3-valent graph
# i and j must be integers satisfying to -i <= j <= i
# (The case i=j=1 is LeapFrog)
GoldbergConstruction:=function(PlanGraph,i,j)
  local Triangulation, VEF, Triangles, Edges, ListStandardPosition, xpos, ypos, ListBeforeQuotient, eTrig, ePos, Rotation1, Rotation2, Rotation3, Rotation1rec, Rotation2rec, Rotation3rec, nbElt, Gra, iP, fTrig, NewPos1, NewPos2, NewPos3, Position1, Position2, Position3, eEdge1, eEdge2, eEdge3, eTrig1, eTrig2, eTrig3, nbVert, VertexSet, ListHexAdj, NewTriangulation, ListOrd,  iVert, jVert, nbadj, iHex, Pos1, Pos2, NewVert1, NewVert2, EltCons, iRepr, jv1, jv2;
  Triangulation:=DualGraph(PlanGraph).PlanGraph;
  Triangles:=PlanGraphToVEFsecond(Triangulation)[3];
  ListStandardPosition:=[];
  for xpos in [-j..i]
  do
    for ypos in [0..i+j]
    do
      if xpos+ypos>=0 and xpos+ypos<=i+j then
        AddSet(ListStandardPosition, [xpos,ypos]);
      fi;
    od;
  od;
  # OrdTrig:=[[0,0],[i,j],[-j,i+j]];
  # creation of the set
  ListBeforeQuotient:=[];
  for eTrig in Triangles
  do
    for ePos in ListStandardPosition
    do
      AddSet(ListBeforeQuotient, [eTrig, ePos]);
    od;
  od;
  #rotation of angle (pi/3) stabilizing (0,0)
  Rotation1:=function(k,l)
    return [-l,k+l];
  end;
  #rotation of angle (-pi/3) stabilizing (0,0)
  Rotation1rec:=function(k,l)
    return [l+k,-k];
  end;
  #
  #rotation of angle (pi/3) stabilizing (i,j)
  Rotation2:=function(k,l)
    return [i+j-l,-i+k+l];
  end;
  #rotation of angle (-pi/3) stabilizing (i,j)
  Rotation2rec:=function(k,l)
    return [-j+l+k, i+j-k];
  end;
  #
  #rotation of angle (pi/3) stabilizing (-j,i+j)
  Rotation3:=function(k,l)
    return [i-l,j+k+l];
  end;
  #rotation of angle (-pi/3) stabilizing (-j,i+j)
  Rotation3rec:=function(k,l)
    return [-j-i+l+k,i-k];
  end;



  # quotienting the set to get the vertices
  nbElt:=Length(ListBeforeQuotient);
  Gra:=NullGraph(Group(()),nbElt);
  
  for iP in [1..nbElt]
  do
    eTrig:=ListBeforeQuotient[iP][1];
    ePos:=ListBeforeQuotient[iP][2];
    #
    eEdge1:=ReverseDE(Triangulation, eTrig[1]);
    eEdge2:=ReverseDE(Triangulation, eTrig[2]);
    eEdge3:=ReverseDE(Triangulation, eTrig[3]);
    for fTrig in Triangles
    do
      if eEdge1 in fTrig then
        eTrig1:=fTrig;
      fi;
      if eEdge2 in fTrig then
        eTrig2:=fTrig;
      fi;
      if eEdge3 in fTrig then
        eTrig3:=fTrig;
      fi;
    od;
    if eEdge1=eTrig1[1] then
      NewPos1:=[i-ePos[1],j-ePos[2]];
    fi;
    if eEdge1=eTrig1[2] then
      NewPos1:=Rotation2rec(ePos[1],ePos[2]);
    fi;
    if eEdge1=eTrig1[3] then
      NewPos1:=Rotation1(ePos[1],ePos[2]);
    fi;
    #
    if eEdge2=eTrig2[1] then
      NewPos2:=Rotation2(ePos[1],ePos[2]);
    fi;
    if eEdge2=eTrig2[2] then
      NewPos2:=[i-j-ePos[1],i+2*j-ePos[2]];
    fi;
    if eEdge2=eTrig2[3] then
      NewPos2:=Rotation3rec(ePos[1],ePos[2]);
    fi;
    #
    if eEdge3=eTrig3[1] then
      NewPos3:=Rotation1rec(ePos[1],ePos[2]);
    fi;
    if eEdge3=eTrig3[2] then
      NewPos3:=Rotation3(ePos[1],ePos[2]);
    fi;
    if eEdge3=eTrig3[3] then
      NewPos3:=[-j-ePos[1],i+j-ePos[2]];
    fi;
    Position1:=Position(ListBeforeQuotient, [eTrig1,NewPos1]);
    Position2:=Position(ListBeforeQuotient, [eTrig2,NewPos2]);
    Position3:=Position(ListBeforeQuotient, [eTrig3,NewPos3]);
    if Position1<>fail then
      AddEdgeOrbit(Gra,[iP,Position1]);
      AddEdgeOrbit(Gra,[Position1,iP]);
    fi;
    if Position2<>fail then
      AddEdgeOrbit(Gra,[iP,Position2]);
      AddEdgeOrbit(Gra,[Position2,iP]);
    fi;
    if Position3<>fail then
      AddEdgeOrbit(Gra,[iP,Position3]);
      AddEdgeOrbit(Gra,[Position3,iP]);
    fi;
  od;
  VertexSet:=ConnectedComponents(Gra);
  nbVert:=Length(VertexSet);


  ListHexAdj:=[[1,0],[0,1],[-1,1],[-1,0],[0,-1],[1,-1]];
  NewTriangulation:=[];
  for iVert in [1..nbVert]
  do
    ListOrd:=[];
    for iRepr in [1..Length(VertexSet[iVert])]
    do
      EltCons:=ListBeforeQuotient[VertexSet[iVert][iRepr]];
      eTrig:=EltCons[1];
      ePos:=EltCons[2];
      for iHex in [1..6]
      do
        NewVert1:=[eTrig,ePos+ListHexAdj[iHex]];
        NewVert2:=[eTrig,ePos+ListHexAdj[NextIdx(6,iHex)]];
        Pos1:=Position(ListBeforeQuotient, NewVert1);
        Pos2:=Position(ListBeforeQuotient, NewVert2);
        if Pos1<>fail and Pos2<>fail then
          for jVert in [1..nbVert]
          do
            if Pos1 in VertexSet[jVert] then
              jv1:=jVert;
            fi;
            if Pos2 in VertexSet[jVert] then
              jv2:=jVert;
            fi;
          od;
          AddSet(ListOrd, [jv1,jv2]);
        fi;
      od;
    od;
    NewTriangulation[iVert]:=CreateOrderedListAdj(ListOrd);
  od;
  return DualGraph(NewTriangulation).PlanGraph;
end;





OctahedriteConstruction:=function(PlanGraph, i, j)
  local Quadrangulation, Quadrangles, ListStandardPosition, xpos, ypos, eSquare, ePos, ListBeforeQuotient, fSquare, ListEdgeSquare, iEdge, nbElt, InternalRotation, InternalRotationRec, iP, Gra, NewPos, ite, PositionTry, nbTurnRight, NSQ, SetEdge, ListSquare, eSquareEx, VertexSet, nbVert, NewQuadrangulation, ListSquareAdj, iVert, jVert, NewVert1, NewVert2, EltCons, jv1, jv2, Pos1, Pos2, iRepr, iSq, ListOrd, u;
  Quadrangulation:=DualGraph(PlanGraph).PlanGraph;
  Quadrangles:=PlanGraphToVEF(Quadrangulation)[3];
  ListStandardPosition:=[];
  for xpos in [-j..i]
  do
    for ypos in [0..i+j]
    do
      AddSet(ListStandardPosition, [xpos,ypos]);
    od;
  od;
  # OrdTrig:=[[0,0],[i,j],[i-j,i+j],[-j,i]]
  # creation of the set
  ListBeforeQuotient:=[];
  for eSquare in Quadrangles
  do
    for ePos in ListStandardPosition
    do
      AddSet(ListBeforeQuotient, [eSquare, ePos]);
    od;
  od;
  #rotation of angle (pi/2) with center ((i-j)/2, (i+j)/2)
  InternalRotation:=function(Pos)
    return [i-Pos[2],j+Pos[1]];
  end;
  #rotation of angle (-pi/2) with center ((i-j)/2, (i+j)/2)
  InternalRotationRec:=function(Pos)
    return [-j+Pos[2],i-Pos[1]];
  end;



  # quotienting the set to get the vertices
  nbElt:=Length(ListBeforeQuotient);
  Gra:=NullGraph(Group(()),nbElt);



  for iP in [1..nbElt]
  do
    eSquare:=ListBeforeQuotient[iP][1];
    ePos:=ListBeforeQuotient[iP][2];
    #
    ListEdgeSquare:=[[eSquare[1],eSquare[2]], [eSquare[2],eSquare[3]], [eSquare[3],eSquare[4]], [eSquare[4],eSquare[1]] ];
    ListSquare:=Difference(Quadrangles, [eSquare]);
    for iEdge in [1..4]
    do
      SetEdge:=Set(ListEdgeSquare[iEdge]);
      for fSquare in ListSquare
      do
        if IsSubset(fSquare, SetEdge) then
          eSquareEx:=fSquare;
        fi;
      od;
      NSQ:=eSquareEx;
      # change coordinates
      nbTurnRight:=0;
      while ([NSQ[4],NSQ[3]]<>ListEdgeSquare[iEdge])
      do
        NSQ:=[NSQ[2],NSQ[3],NSQ[4],NSQ[1]];
        nbTurnRight:=nbTurnRight+1;
      od;
      if iEdge=1 then
        NewPos:=[ePos[1]-j,ePos[2]+i];
        ite:=nbTurnRight;
        for u in [1..ite]
        do
          NewPos:=InternalRotation(NewPos);
        od;
      fi;
      if iEdge=2 then
        NewPos:=[ePos[1]-i,ePos[2]-j];
        ite:=(3+nbTurnRight) mod 4;
        for u in [1..ite]
        do
          NewPos:=InternalRotation(NewPos);
        od;
      fi;
      if iEdge=3 then
        NewPos:=[ePos[1]+j,ePos[2]-i];
        ite:=(2+nbTurnRight) mod 4;
        for u in [1..ite]
        do
          NewPos:=InternalRotation(NewPos);
        od;
      fi;
      if iEdge=4 then
        NewPos:=[ePos[1]+i,ePos[2]+j];
        ite:=(1+nbTurnRight) mod 4;
        for u in [1..ite]
        do
          NewPos:=InternalRotation(NewPos);
        od;
      fi;
      PositionTry:=Position(ListBeforeQuotient, [eSquareEx,NewPos]);
      if PositionTry<>fail then
        AddEdgeOrbit(Gra,[iP,PositionTry]);
        AddEdgeOrbit(Gra,[PositionTry,iP]);
      fi;
    od;
  od;
  VertexSet:=ConnectedComponents(Gra);
  nbVert:=Length(VertexSet);

  ListSquareAdj:=[[1,0],[0,1],[-1,0],[0,-1]];
  NewQuadrangulation:=[];
  for iVert in [1..nbVert]
  do
    ListOrd:=[];
    for iRepr in [1..Length(VertexSet[iVert])]
    do
      EltCons:=ListBeforeQuotient[VertexSet[iVert][iRepr]];
      eSquare:=EltCons[1];
      ePos:=EltCons[2];
      for iSq in [1..4]
      do
        NewVert1:=[eSquare,ePos+ListSquareAdj[iSq]];
        NewVert2:=[eSquare,ePos+ListSquareAdj[NextIdx(4,iSq)]];
        Pos1:=Position(ListBeforeQuotient, NewVert1);
        Pos2:=Position(ListBeforeQuotient, NewVert2);
        if Pos1<>fail and Pos2<>fail then
          for jVert in [1..nbVert]
          do
            if Pos1 in VertexSet[jVert] then
              jv1:=jVert;
            fi;
            if Pos2 in VertexSet[jVert] then
              jv2:=jVert;
            fi;
          od;
          AddSet(ListOrd, [jv1,jv2]);
        fi;
      od;
    od;
    NewQuadrangulation[iVert]:=CreateOrderedListAdj(ListOrd);
  od;
  return DualGraph(NewQuadrangulation).PlanGraph;
end;



SL2action:=function(G, MatrixM)
  local a, b, c, d, a1, b1, c1, d1, r, q, h1, h2, w, w1, w2, MatrixP, IdentityMat;
  h1:=G[1];
  h2:=G[2];
  MatrixP:=ShallowCopy(MatrixM);
  IdentityMat:=[[1,0],[0,1]];
  while(MatrixP<>IdentityMat)
  do
    a:=MatrixP[1][1];
    b:=MatrixP[1][2];
    c:=MatrixP[2][1];
    d:=MatrixP[2][2];
    if a=0 and d<>0 then
      q:=d/c;
      a1:=a;
      b1:=b;
      c1:=c;
      d1:=d-q*c;
      MatrixP:=[[a1, b1], [c1, d1]];
      h1:=h1*(h2^q);
    elif AbsInt(a)>=AbsInt(b) and AbsInt(b)>0 then
      r:=a mod b;
      q:=(a-r)/b;
      a1:=a-q*b;
      b1:=b;
      c1:=c-q*d;
      d1:=d;
      MatrixP:=[[a1, b1], [c1, d1]];
      h2:=(h1^q)*h2;
    elif AbsInt(b)>=AbsInt(a) and AbsInt(a)>0 then
      r:=b mod a;
      q:=(b-r)/a;
      a1:=a;
      b1:=b-q*a;
      c1:=c;
      d1:=d-q*c;
      MatrixP:=[[a1, b1], [c1, d1]];
      h1:=h1*(h2^q);
    elif AbsInt(c)>=AbsInt(d) and AbsInt(d)>0 then
      r:=c mod d;
      q:=(c-r)/d;
      a1:=a-q*b;
      b1:=b;
      c1:=c-q*d;
      d1:=d;
      MatrixP:=[[a1, b1], [c1, d1]];
      h2:=(h1^q)*h2;
    elif AbsInt(d)>=AbsInt(c) and AbsInt(c)>0 then
      r:=d mod c;
      q:=(d-r)/c;
      a1:=a;
      b1:=b-q*a;
      c1:=c;
      d1:=d-q*c;
      MatrixP:=[[a1, b1], [c1, d1]];
      h1:=h1*(h2^q);
    elif MatrixP=[[-1, 0], [0, -1]] then
      w:=h1^(-1)*h2;
      h1:=w^(-1)*h1^(-1)*w;
      h2:=w^(-1)*h2^(-1)*w;
      MatrixP:=[[1,0],[0,1]];
    elif MatrixP=[[0,-1], [1,0]] then
      w:=h2^(-1)*h1^(-1)*h2;
      w1:=h1;
      w2:=h2;
      h1:=w^(-1)*w2^(-1)*w;
      h2:=w^(-1)*w1*w;
      MatrixP:=[[1,0],[0,1]];
    elif MatrixP=[[0,1], [-1,0]] then
      w:=h2;
      h2:=h2^(-1)*h1^(-1)*h2;
      h1:=w;
      MatrixP:=[[1,0],[0,1]];
    fi;
  od;
  return [h1, h2];
end;





HalfCyclicStructure:=function(Perm, NBU)
  local GCyc, UC, ListCyc, i, O, eO, StringPart, iCol, pos, NbExpo;
  GCyc:=Group([Perm]);
  UC:=ListWithIdenticalEntries(NBU, -1);
  ListCyc:=ListWithIdenticalEntries(NBU, 0);
  NbExpo:=0;
  for i in [1..NBU]
  do
    if UC[i]=-1 then
      O:=Orbit(GCyc, i, OnPoints);
      for eO in O
      do
        UC[eO]:=Length(O);
      od;
      if ListCyc[Length(O)]=0 then
        NbExpo:=NbExpo+1;
      fi;
      ListCyc[Length(O)]:=ListCyc[Length(O)]+1;
    fi;
  od;
  pos:=0;
  StringPart:="";
  for iCol in [1..NBU]
  do
    if ListCyc[iCol]>0 then
      pos:=pos+1;
      if ListCyc[iCol]=2 then
        StringPart:=Concatenation(StringPart, String(iCol));
      else
        StringPart:=Concatenation(StringPart, String(iCol), "^", StringLatex(ListCyc[iCol]/2));
      fi;
      if pos<NbExpo then
        StringPart:=Concatenation(StringPart, ", ");
      fi;
    fi;
  od;
  return StringPart;
end;



KLproduct:=function(k,l, g1, g2)
  # k and l must be positive here.
  local DirEdge, pos, iMove, Perm;
  pos:=1;
  Perm:=();
  for iMove in [1..k+l]
  do
    if pos in [1..k] then
      pos:=pos+l;
      Perm:=Perm*g1;
    else
      pos:=pos-k;
      Perm:=Perm*g2;
    fi;
  od;
  return Perm;
end;


KLproductSecond:=function(k,l, g1, g2)
  local k1, l1, e1, e2, q, r, VE;
  e1:=g1;
  e2:=g2;
  if k<0 and l>0 then
    VE:=SL2action([e1,e2], [[0,1],[-1,0]]);
    e1:=VE[1]; e2:=VE[2];
    k1:=l;
    l1:=-k;
  elif k>0 and l<0 then
    VE:=SL2action([e1,e2], [[0,-1],[1,0]]);
    e1:=VE[1]; e2:=VE[2];
    k1:=-l;
    l1:=k;
  elif k<0 and l<0 then
    VE:=SL2action([e1,e2], [[-1,0],[0,-1]]);
    e1:=VE[1]; e2:=VE[2];
    k1:=-k;
    l1:=-l;
  else
    k1:=k;
    l1:=l;
  fi;
  while(k1 >0 and l1>0)
  do
    if k1>l1 then
      r:=k1 mod l1;
      q:=(k1-r)/l1;
      e2:=(e1)^q*e2;
      k1:=r;
    else
      r:=l1 mod k1;
      q:=(l1-r)/k1;
      e1:=e1*(e2)^q;
      l1:=r;
    fi;
  od;
  if (k1=1 and l1=0) then
    return e1;
  elif (k1=0 and l1=1) then
    return e2;
  fi;
end;




GoldbergFormalism:=function(PlanGraph)
  local FuncNext, FuncPrev, FuncRevers, VEF, 
  valency, DualPlan, ListDEsecond, ListDE, FirstMovePerm, SecondMovePerm, ThirdMovePerm, iEdge, eDir, fDir, gDir, hDir, 
  FMP, SMP, TMP, FC, SC, iVert, RotG, 
  Smapping, SmappingSecond, PartitionVectorFunction, GrpMoves, ListNormalNonTrivialSubgroup, PartitionVectorEnumeration, ListElementsByNormalSubgroup, PartitionVectorRepartition, CaseK1, CaseKK_1, HCS
  , MatrixEnumeration, PrintMatrixEnumeration, PairToPerm, CommGrp, CommGrpPair, Gens, GenNew, iGen, IndexNumber, FuncTestMembership, PowerOrder, SearchForGenerators;
  if IsRecord(PlanGraph)=true then
    DualPlan:=DualGraphOriented(PlanGraph);
    ListDEsecond:=[1..PlanGraph.nbP];
    ListDE:=[1..PlanGraph.nbP];
    VEF:=PlanGraphOrientedToVEF(PlanGraph);
    valency:=Length(VEF.VertSet[1]);
    for iVert in [1..Length(VEF.VertSet)]
    do
      if valency <> Length(VEF.VertSet[iVert]) then
        Print("Error, valency is not homogeneous\n");
        return false;
      fi;
    od;
    FuncNext:=function(Obj)
      return OnPoints(Obj, DualPlan.next);
    end;
    FuncPrev:=function(Obj)
      return OnPoints(Obj, (DualPlan.next)^(-1));
    end;
    FuncRevers:=function(Obj)
      return OnPoints(Obj, DualPlan.invers);
    end;
    RotG:=Group(());
  else
    DualPlan:=DualGraph(PlanGraph).PlanGraph;
    ListDEsecond:=ListDirectedEdges(DualPlan);
    ListDE:=[];
    valency:=Length(PlanGraph[1]);
    for iVert in [1..Length(PlanGraph)]
    do
      if valency <> Length(PlanGraph[iVert]) then
        Print("Error, valency is not homogeneous\n");
        return false;
      fi;
    od;
    FuncNext:=function(Obj)
      return NextDE(DualPlan, Obj);
    end;
    FuncPrev:=function(Obj)
      return PrevDE(DualPlan, Obj);
    end;
    FuncRevers:=function(Obj)
      return ReverseDE(DualPlan, Obj);
    end;
  fi;
  FirstMovePerm:=[];
  SecondMovePerm:=[];
  ThirdMovePerm:=[];
  for iEdge in [1..Length(ListDEsecond)]
  do
    eDir:=ListDEsecond[iEdge];
    if valency=4 then
      fDir:=FuncNext(FuncRevers(FuncNext(eDir)));
      gDir:=FuncRevers(FuncPrev(FuncRevers(eDir)));
      hDir:=FuncNext(eDir);
      FirstMovePerm[iEdge]:=Position(ListDEsecond, fDir);
      SecondMovePerm[iEdge]:=Position(ListDEsecond, gDir);
      ThirdMovePerm[iEdge]:=Position(ListDEsecond, hDir);
    else
      fDir:=FuncNext(FuncRevers(FuncNext(FuncNext(eDir))));
      gDir:=FuncNext(FuncNext(FuncRevers(FuncNext(eDir))));
      FirstMovePerm[iEdge]:=Position(ListDEsecond, fDir);
      SecondMovePerm[iEdge]:=Position(ListDEsecond, gDir);
    fi;
    if IsRecord(PlanGraph)=false then
      ListDE[iEdge]:=[eDir[1], DualPlan[eDir[1]][eDir[2]] ];
    fi;
  od;
  if IsRecord(PlanGraph)=false then
    RotG:=TranslateGroup(GroupPlan(DualPlan).RotationSubgroup, ListDE, OnPairs);
  fi;
  if valency = 4 then
    FMP:=PermList(FirstMovePerm);
    SMP:=PermList(SecondMovePerm);
    TMP:=PermList(ThirdMovePerm);
    FC:=FMP;
    SC:=(FMP^(-1))*SMP*TMP;
  elif valency = 3 then
    FMP:=PermList(FirstMovePerm);
    SMP:=PermList(SecondMovePerm);
    FC:=FMP;
    SC:=SMP;
  else
    Print("Error: valency of the graph should be 3 or 4\n");
    return false;
  fi;
  GrpMoves:=Group([FC, SC]);
  ListNormalNonTrivialSubgroup:=function()
    local UJ, LNTS, iClass;
    UJ:=NormalSubgroups(GrpMoves);
    LNTS:=[];
    for iClass in [1..Length(UJ)]
    do
      if Order(UJ[iClass])>1 and Order(UJ[iClass])<Order(GrpMoves) then
        Add(LNTS, UJ[iClass]);
      fi;
    od;
    return LNTS;
  end;
  # here and below, k and l must be coprime integers.
  Smapping:=function(k,l)
    return KLproduct(k, l, FC, SC);
  end;
  SmappingSecond:=function(k,l)
    return KLproductSecond(k, l, FC, SC);
  end;
  HCS:=function(Perm)
    return HalfCyclicStructure(Perm, Length(ListDEsecond));
  end;


  PartitionVectorFunction:=function(k,l)
    local Perm;
    Perm:=SmappingSecond(k,l);
    return rec(PartitionVector:=HCS(Perm), Perm:=Perm);
  end;
  #
  #
  # Use the normal subgroups of MovingGroup to derive
  # information on the possible z-vector and CC-vector
  PowerOrder:=function(eElt, SubGrp)
    local fElt, ord;
    fElt:=();
    ord:=1;
    while(not(fElt*eElt in SubGrp))
    do
      fElt:=fElt*eElt;
      ord:=ord+1;
    od;
    return ord;
  end;
  ListElementsByNormalSubgroup:=function()
    local ListInitialConjClas, ListConjClas,  P1, P2, ListInfoCongruence, IdxGrp, eComm, eNorm, iNorm, u, ListCommQuot, ListPossibility, TotalListPossibility, OrdFC, OrdSC, TotalList, ListExcludedNonCommutativeQuotient, ListExcludedSpecialCommutativeQuotient, ListComplementPossibility, NormalNonCommutativeExclusion, NormalCommutativeExclusion, LNTS, FE, FuncListPossibility, FuncExclusion;
    LNTS:=ListNormalNonTrivialSubgroup();
    Print("Found ", Length(LNTS), " normal subgroups\n");
    ListInitialConjClas:=Set(ConjugacyClasses(GrpMoves));
    Print("Found ", Length(ListInitialConjClas), " conjugacy classes\n");
    if IsCommutative(GrpMoves)=false then
      RemoveSet(ListInitialConjClas, ConjugacyClass(GrpMoves,()));
    fi;
    FuncListPossibility:=function(ListCC)
      local ListPoss, u;
      ListPoss:=[];
      for u in ListCC
      do
        AddSet(ListPoss, HCS(Representative(u)));
      od;
      return ListPoss;
    end;
    TotalList:=FuncListPossibility(ListInitialConjClas);
    P1:=FC*SC;
    P2:=SC*FC;
    eComm:=P1*(P2^(-1));
    FuncExclusion:=function(eNormal, ListConjClas)
      local ReducedListConjClas, u, IdxGrp, OrdFC, OrdSC;
      if not(eComm in eNormal) then
        ReducedListConjClas:=[];
        for u in ListConjClas
        do
          if not(Representative(u) in eNormal) then
            Add(ReducedListConjClas, u);
          fi;
        od;
        return rec(Status:="NonCommutative", ReducedListConjClas:=ReducedListConjClas);
      else
        IdxGrp:=Order(GrpMoves)/Order(eNormal);
        OrdFC:=PowerOrder(FC, eNormal);
        OrdSC:=PowerOrder(SC, eNormal);
        if OrdFC*OrdSC = IdxGrp and Gcd(OrdFC, OrdSC)<> 1 then
          ReducedListConjClas:=[];
          for u in ListConjClas
          do
            if not(Representative(u) in eNormal) then
              Add(ReducedListConjClas, u);
            fi;
          od;
          return rec(Status:="CommutativeSpecial", ReducedListConjClas:=ReducedListConjClas);
        else
          ReducedListConjClas:=ShallowCopy(ListConjClas);
          return rec(Status:="Commutative", ReducedListConjClas:=ReducedListConjClas);
        fi;
      fi;
    end;
    #
    #
    #
    #
    NormalCommutativeExclusion:=[];
    NormalNonCommutativeExclusion:=[];
    ListCommQuot:=[];
    ListConjClas:=ShallowCopy(ListInitialConjClas);
    for iNorm in [1..Length(LNTS)]
    do
      eNorm:=LNTS[iNorm];
      Print("Considering group ", iNorm, " of size ", Order(eNorm), "\n");
      FE:=FuncExclusion(eNorm, ListConjClas);
      ListConjClas:=FE.ReducedListConjClas;
      if FE.Status="NonCommutative" then
        Add(NormalNonCommutativeExclusion, iNorm);
      fi;
      if FE.Status="CommutativeSpecial" then
        Add(NormalCommutativeExclusion, iNorm);
      fi;
      if FE.Status="Commutative" then
        Add(ListCommQuot, iNorm);
      fi;
    od;
    TotalListPossibility:=FuncListPossibility(ListConjClas);
    ListInfoCongruence:=[];
    for iNorm in ListCommQuot
    do
      eNorm:=LNTS[iNorm];
      Print("Considering group ", iNorm, " of size ", Order(eNorm), "\n");
      IdxGrp:=Order(GrpMoves)/Order(eNorm);
      ListPossibility:=[];
      ListComplementPossibility:=[];
      for u in ListConjClas
      do
        if Representative(u) in eNorm then
          AddSet(ListPossibility, HCS(Representative(u)));
        else
          AddSet(ListComplementPossibility, HCS(Representative(u)));
        fi;
      od;
      if FC*SC in eNorm then
        Add(ListInfoCongruence, rec(PositionListNormal:=iNorm, ListPossibility:=ListPossibility, ListComplementPossibility:=ListComplementPossibility, Relation:=Concatenation("k-l mod ", String(IdxGrp))));
      else
        Add(ListInfoCongruence, rec(PositionListNormal:=iNorm, ListPossibility:=ListPossibility, ListComplementPossibility:=ListComplementPossibility, Relation:="unknown"));
      fi;
    od;
    return rec(ListInitialConjClas:=ListInitialConjClas, 
    ListConjClas:=ListConjClas, 
    LNTS:=LNTS, 
    TotalListPossibility:=TotalListPossibility, 
    TotalList:=TotalList, 
    NormalNonCommutativeExclusion:=NormalNonCommutativeExclusion, 
    NormalCommutativeExclusion:=NormalCommutativeExclusion, 
    FuncExclusion:=FuncExclusion, 
    FuncListPossibility:=FuncListPossibility, 
    ListInfoCongruence:=ListInfoCongruence);
  end;







  #
  #
  # Enumeration of Matrices
  # in stabilizer
  PairToPerm:=function(ePair)
    local FCH, iDE;
    FCH:=[];
    for iDE in [1..Length(ListDEsecond)]
    do
      FCH[iDE]:=iDE+Length(ListDEsecond);
    od;
    for iDE in [1..Length(ListDEsecond)]
    do
      FCH[iDE+Length(ListDEsecond)]:=iDE;
    od;
    return ePair[1]*PermList(FCH)*ePair[2]*PermList(FCH);
  end;
  CommGrp:=DerivedSubgroup(GrpMoves);
  Gens:=GeneratorsOfGroup(CommGrp);
  if Length(Gens)=0 then
    CommGrpPair:=Group(());
  else
    GenNew:=[];
    for iGen in [1..Length(Gens)]
    do
      Add(GenNew, PairToPerm([Gens[iGen], Gens[iGen]]));
    od;
    CommGrpPair:=Group(GenNew);
  fi;
  IndexNumber:=function(type)
    local nbP, ListPair, ListMatch, TotalMatch, iPair, ePair, fPair1, fPair2, FuncInsert, ListPermA, ListPossibility, StabilizerGroup;
    if type="null" then
      StabilizerGroup:=Group(());
    elif type="derived" then
      StabilizerGroup:=CommGrpPair;
    elif type="symmetric" then
      Gens:=GeneratorsOfGroup(SymmetricGroup(Length(ListDEsecond)));
      GenNew:=[];
      for iGen in [1..Length(Gens)]
      do
        Add(GenNew, PairToPerm([Gens[iGen], Gens[iGen]]));
      od;
      StabilizerGroup:=Group(GenNew);
    else
      Print("Error, type should be null, derived or symmetric\n");
      return false;
    fi;
    ListPair:=[[FC, SC]];
    ListPermA:=[PairToPerm([FC,SC])];
    ListMatch:=[0];
    TotalMatch:=0;
    FuncInsert:=function(fPair)
      local ePerm, jPair;
      ePerm:=PairToPerm(fPair);
      for jPair in [1..Length(ListPair)]
      do
        if IsConjugate(StabilizerGroup, ePerm, ListPermA[jPair]) then
          return;
        fi;
      od;
      Add(ListPair, fPair);
      Add(ListPermA, ePerm);
      Add(ListMatch, 0);
      TotalMatch:=0;
      return;
    end;
    while TotalMatch=0
    do
      nbP:=Length(ListPair);
      TotalMatch:=1;
      for iPair in [1..nbP]
      do
        ePair:=ListPair[iPair];
        if ListMatch[iPair]=0 then
          ListMatch[iPair]:=1;
          fPair1:=[ePair[1], ePair[1]*ePair[2]];
          fPair2:=[ePair[1]*ePair[2], ePair[2]];
          FuncInsert(fPair1);
          FuncInsert(fPair2);
        fi;
      od;
      Print("Number of Pairs=", Length(ListPair), "\n");
    od;
    ListPossibility:=[];
    for ePair in ListPair
    do
      AddSet(ListPossibility, HCS(ePair[1]));
      AddSet(ListPossibility, HCS(ePair[2]));
    od;
    return rec(ListPair:=ListPair, ListPossibility:=ListPossibility, IndexNumber:=Length(ListPair));
  end;
  FuncTestMembership:=function(Mat)
    local ePerm, ePair, fPerm;
    ePerm:=PairToPerm([FC,SC]);
    ePair:=SL2action([FC,SC], Mat);
    fPerm:=PairToPerm(ePair);
    return IsConjugate(CommGrpPair, ePerm, fPerm);
  end;
  MatrixEnumeration:=function(UpperBound, typeasked)
    local a, b, c, d, ListMatrix, U, Uinv, LM, iUpp, Nmax, LMinvRed, LStatus, LMnew, iElt, jElt;
    ListMatrix:=[];
    for a in [-UpperBound..UpperBound]
    do
      for b in [-UpperBound..UpperBound]
      do
        for c in [-UpperBound..UpperBound]
        do
          for d in [-UpperBound..UpperBound]
          do
            if a*d-b*c=1 then
              U:=[[a,b],[c,d]];
              if FuncTestMembership(U)=true then
                Add(ListMatrix, U);
              fi;
            fi;
          od;
        od;
      od;
    od;
    LM:=[];
    for iUpp in [1..UpperBound]
    do
      LM[iUpp]:=[];
    od;
    for U in ListMatrix
    do
      Nmax:=Maximum(AbsInt(U[1][1]),AbsInt(U[1][2]),AbsInt(U[2][1]),AbsInt(U[2][2]));
      if typeasked="simple" or U<>[[1,0],[0,1]] then
        AddSet(LM[Nmax], U);
      fi;
    od;
    if typeasked="simple" then
      return LM;
    fi;
    LMinvRed:=[];
    for iUpp in [1..UpperBound]
    do
      LStatus:=[];
      for iElt in [1..Length(LM[iUpp])]
      do
        LStatus[iElt]:=1;
      od;
      for iElt in [1..Length(LM[iUpp])]
      do
        U:=LM[iUpp][iElt];
        Uinv:=Inverse(U);
        jElt:=Position(LM[iUpp], Uinv);
        if LStatus[iElt]=1 and LStatus[jElt]=1 then
          LStatus[jElt]:=0;
        fi;
      od;
      LMnew:=[];
      for iElt in [1..Length(LM[iUpp])]
      do
        if LStatus[iElt]=1 then
          Add(LMnew, LM[iUpp][iElt]);
        fi;
      od;
      LMinvRed[iUpp]:=LMnew;
    od;
    return LMinvRed;
  end;
  SearchForGenerators:=function(UpperBoundTest, UpperBoundGens, nbite)
    local LM, ListGens, iUpp, eUP, ListTotal, ListWork, ListNew, ite, eGen, fGen, U, Nmax;
    LM:=MatrixEnumeration(UpperBoundTest, "simple");
    ListGens:=[];
    for iUpp in [1..UpperBoundGens]
    do
      for eUP in LM[iUpp]
      do
        Add(ListGens, eUP);
      od;
    od;
    Print("nbGens=", Length(ListGens), "\n");
    ListTotal:=[];
    for iUpp in [1..UpperBoundTest]
    do
      for eUP in LM[iUpp]
      do
        Add(ListTotal, eUP);
      od;
    od;
    Print("nb Total=", Length(ListTotal), "\n");

    ListWork:=Set(ListGens);
    for ite in [1..nbite]
    do
      Print("ite=", ite, "\n");
      ListNew:=Set(ListWork);
      for eGen in ListWork
      do
        for fGen in ListWork
        do
          U:=eGen*fGen;
          Nmax:=Maximum(AbsInt(U[1][1]),AbsInt(U[1][2]),AbsInt(U[2][1]),AbsInt(U[2][2]));
          if Nmax<=UpperBoundTest then
            AddSet(ListNew, U);
          fi;
        od;
      od;
      ListWork:=Set(ListNew);
      Print("nb elt=", Length(ListWork), "\n");
      if Set(ListTotal)=ListWork then
        return true;
      fi;
    od;
    if IsSubset(ListWork, Set(ListTotal))=true then
      return true;
    else
      return false;
    fi;
  end;


  PrintMatrixEnumeration:=function(output, UpperBound)
    local LM, iUpp, eMatrix;
    LM:=MatrixEnumeration(UpperBound, "inverseReduction");
    for iUpp in [1..UpperBound]
    do
      if Length(LM[iUpp])>0 then 
        AppendTo(output, "Matrices of Norm ", iUpp,"\n");
        AppendTo(output, "\\begin{multicols}{3}\n");
        for eMatrix in LM[iUpp]
        do
          LatexPrintMatrix(output, eMatrix);
        od;
        AppendTo(output, "\\end{multicols}\n");
      fi;
    od;
  end;
  #
  #
  #
  # enumeration of all possible cases of Partition Vector
  PartitionVectorEnumeration:=function(MAXK, Disc)
    local GrpPlan, k, l, Minl, STR, LPVSatisfyRelation, LPVNonSatisfyRelation, Residu, ImageSet, W;
    LPVSatisfyRelation:=[];
    LPVNonSatisfyRelation:=[];
    ImageSet:=[];

    GrpPlan:=GroupPlan(PlanGraph);
    for k in [1..MAXK]
    do
      if GrpPlan.IsRotationGroup=false then 
        Minl:=0;
      else
        Minl:=-k;
      fi;
      for l in [Minl..k]
      do
        if Gcd(k,l)=1 then
          W:=PartitionVectorFunction(k,l);
          AddSet(ImageSet, W.Perm);
          STR:=W.PartitionVector;
          Residu:=(k-l) mod Disc;
          if Residu=0 then
            AddSet(LPVSatisfyRelation, STR);
          else
            AddSet(LPVNonSatisfyRelation, STR);
          fi;
        fi;
      od;
    od;
    return rec(LPVSatisfyRelation:=LPVSatisfyRelation, LPVNonSatisfyRelation:=LPVNonSatisfyRelation, ImageSet:=ImageSet);
  end;
  #
  #
  # give in entrance a list of possible repartition vector
  # and output is the repartition in pairs $(k,l)$.
  PartitionVectorRepartition:=function(MAXK, ListPossibility)
    local k, l, GrpPlan, Minl, ListAppear, iPos, Pos, STR;
    ListAppear:=[];
    for iPos in [1..Length(ListPossibility)]
    do
      ListAppear[iPos]:=[];
    od;
    GrpPlan:=GroupPlan(PlanGraph);
    for k in [1..MAXK]
    do
      if GrpPlan.IsRotationGroup=false then 
        Minl:=0;
      else
        Minl:=-k;
      fi;
      for l in [Minl..k]
      do
        if Gcd(k,l)=1 then
          STR:=PartitionVectorFunction(k,l).PartitionVector;
          Pos:=Position(ListPossibility, STR);
          Add(ListAppear[Pos], [k,l]);
        fi;
      od;
    od;
    return ListAppear;
  end;
  CaseK1:=function()
    local Nord, ListCases, k;
    Nord:=PowerOrder(FC, Group(()));
    ListCases:=[];
    for k in [1..Nord]
    do
      Add(ListCases, Concatenation(String(k),",1: ", HCS((FC^k)*SC)));
    od;
    return ListCases;
  end;
  CaseKK_1:=function()
    local Nord, ListCases, k;
    Nord:=PowerOrder(FC*SC, Group(()));
    ListCases:=[];
    for k in [1..Nord]
    do
      Add(ListCases, Concatenation(String(k),",", String(k-1),": ", HCS(FC*((FC*SC)^(k-1)))));
    od;
    return ListCases;
  end;



  return rec(ListDE:=ListDE, ListDEsecond:=ListDEsecond, PlanGraph:=DualPlan, RotG:=RotG, MovingGroup:=GrpMoves, ListNormalNonTrivialSubgroup:=ListNormalNonTrivialSubgroup, FC:=FC, SC:=SC, PartitionVectorFunction:=PartitionVectorFunction, IndexNumber:=IndexNumber, Smapping:=Smapping, SmappingSecond:=SmappingSecond, FuncTestMembership:=FuncTestMembership, PartitionVectorEnumeration:=PartitionVectorEnumeration, MatrixEnumeration:=MatrixEnumeration, ListElementsByNormalSubgroup:=ListElementsByNormalSubgroup, PrintMatrixEnumeration:=PrintMatrixEnumeration, PartitionVectorRepartition:=PartitionVectorRepartition, CaseK1:=CaseK1, CaseKK_1:=CaseKK_1, PairToPerm:=PairToPerm, CommGrpPair:=CommGrpPair, SearchForGenerators:=SearchForGenerators);
end;









CreateOrientedMap:=function(Grp, RGen, SGen)
  local RSg, ListElt, u, ListPairing, ListStatus, i, eV, pos, ValencyP, ListVert, ListPos, NewPlanGraph, iVert, jVert, Ladj, h;
  RSg:=SGen*RGen;
  ListElt:=[];
  for u in Grp
  do
    Add(ListElt, u);
  od;
  #
  ListPairing:=[];
  ListStatus:=[];
  for i in [1..Length(ListElt)]
  do
    ListPairing[i]:=0;
    ListStatus[i]:=0;
  od;
  for i in [1..Length(ListElt)]
  do
    if ListPairing[i]=0 then
      eV:=ListElt[i]*RSg;
      pos:=Position(ListElt, eV);
      ListPairing[i]:=pos;
      ListPairing[pos]:=i;
    fi;
  od;
  #
  ValencyP:=Order(SGen);
  ListVert:=[];
  for i in [1..Length(ListElt)]
  do
    if ListStatus[i]=0 then
      ListPos:=[];
      u:=ListElt[i];
      for i in [1..ValencyP]
      do
        pos:=Position(ListElt, u);
        ListStatus[pos]:=1;
        Add(ListPos, pos);
        u:=u*SGen;
      od;
      Add(ListVert, ListPos);
    fi;
  od;
  NewPlanGraph:=[];
#  Print("ListVert=", ListVert, "\n");
#  Print("ListPairing=", ListPairing, "\n");
  for iVert in [1..Length(ListVert)]
  do
    Ladj:=[];
    for i in [1..Length(ListVert[iVert])]
    do
      h:=ListPairing[ListVert[iVert][i]];
#      Print("h=", h, "\n");
      pos:=0;
      for jVert in [1..Length(ListVert)]
      do
        if Position(ListVert[jVert], h)<>fail then
#          Print("Assigning pos, \n");
          pos:=jVert;
        fi;
      od;
      Add(Ladj, pos);
    od;
    Add(NewPlanGraph, Ladj);
  od;
  return NewPlanGraph;
end;



CreateOrientedMapSecond:=function(Grp, RGen, SGen)
  local LPinv, LPnext, O, i, u;
  O:=Orbit(Grp, (), OnRight);
  LPnext:=[];
  LPinv:=[];
  for i in [1..Length(O)]
  do
    u:=OnRight(O[i], SGen);
    Add(LPnext, Position(O, u));
    u:=OnRight(O[i], RGen*SGen);
    Add(LPinv, Position(O, u));
  od;
  return rec(next:=PermList(LPnext), invers:=PermList(LPinv), nbP:=Length(O));
end;





ListMatRotTrig:=function()
  local A;
  A:=[[0,-1],[1,1]];
  return [A^0, A, A^2, A^3, A^4, A^5];
end;

PlaneRotationTrig:=function(eDat, ePoint)
  return ListMatRotTrig()[eDat.ord+1]*ePoint+eDat.VTrans;
end;

ListMatRotQuad:=function()
  local A;
  A:=[[0,-1],[1,0]];
  return [A^0, A, A^2, A^3];
end;


PlaneRotationQuad:=function(eDat, ePoint)
  return ListMatRotQuad()[eDat.ord+1]*ePoint+eDat.VTrans;
end;




#
# Create the rotation mapping ePoint1 to fPoint1
# and ePoint2 to fPoint2
CreateRotationTrig:=function(ePoint1, ePoint2, fPoint1, fPoint2)
  local ListMat, ord, eV, fV;
  ListMat:=ListMatRotTrig();
  ord:=0;
  eV:=ePoint2-ePoint1;
  fV:=fPoint2-fPoint1;
  while(ord<=5)
  do
    if fV=ListMat[ord+1]*eV then
      break;
    fi;
    ord:=ord+1;
  od;
  if ord=6 then
    return false;
  fi;
  return rec(ord:=ord, VTrans:=fPoint2-ListMat[ord+1]*ePoint2);
end;




CreateRotationQuad:=function(ePoint1, ePoint2, fPoint1, fPoint2)
  local ListMat, ord, eV, fV;
  ListMat:=ListMatRotQuad();
  eV:=ePoint2-ePoint1;
  fV:=fPoint2-fPoint1;
  ord:=0;
  while(ord<=5)
  do
    if fV=ListMat[ord+1]*eV then
      break;
    fi;
    ord:=ord+1;
  od;
  if ord=4 then
    return false;
  fi;
  return rec(ord:=ord, VTrans:=fPoint2-ListMat[ord+1]*ePoint2);
end;












#
# return the list [a,b,c] such that the
# equation of the line between ePoint and fPoint is
# ax+by+c=0
LineEquation:=function(ePoint, fPoint)
  return [ePoint[2]-fPoint[2], fPoint[1]-ePoint[1], fPoint[2]*ePoint[1]-fPoint[1]*ePoint[2]];
end;


CreateListPoint:=function(ListThreePoints)
  local ePoint1, ePoint2, ePoint3, MinimalX, MinimalY, MaximalX, MaximalY, coordX, coordY, ListPoint, eEqua, Equa12, Equa23, Equa31, ApproxX, FindMatch, ListEqua, i, ListX, ListByYcoordinate, ListYcoordinate, vPoint;
  ePoint1:=ListThreePoints[1];
  Append(ePoint1, [1]);
  ePoint2:=ListThreePoints[2];
  Append(ePoint2, [1]);
  ePoint3:=ListThreePoints[3];
  Append(ePoint3, [1]);
  #
  MinimalX:=Minimum(ePoint1[1],ePoint2[1],ePoint3[1])-1;
  MaximalX:=Maximum(ePoint1[1],ePoint2[1],ePoint3[1])+1;
  MinimalY:=Minimum(ePoint1[2],ePoint2[2],ePoint3[2]);
  MaximalY:=Maximum(ePoint1[2],ePoint2[2],ePoint3[2]);
  Equa12:=LineEquation(ePoint1, ePoint2);
  Equa23:=LineEquation(ePoint2, ePoint3);
  Equa31:=LineEquation(ePoint3, ePoint1);
  if Equa12*ePoint3<0 then
    Equa12:=-Equa12;
  fi;
  if Equa23*ePoint1<0 then
    Equa23:=-Equa23;
  fi;
  if Equa31*ePoint2<0 then
    Equa31:=-Equa31;
  fi;
  #
  ListEqua:=[Equa12, Equa23, Equa31];
  ListByYcoordinate:=[];
  ListYcoordinate:=[];
  for coordY in [MinimalY..MaximalY]
  do
    ListX:=[];
    for coordX in [MinimalX..MaximalX]
    do
      FindMatch:=false;
      for i in [1..3]
      do
        eEqua:=ListEqua[i];
        if eEqua[1]<>0 then
          ApproxX:=(-eEqua[3]-eEqua[2]*coordY)/eEqua[1];
          if AbsInt(coordX-ApproxX)<1 then
            vPoint:=[ApproxX, coordY, 1];
            if Equa12*vPoint>=0 and Equa23*vPoint>=0 and Equa31*vPoint>=0 then
              FindMatch:=true;
            fi;
          fi;
        fi;
      od;
      if FindMatch=true then
        Add(ListX, coordX);
      fi;
    od;
    Add(ListByYcoordinate, ListX);
    Add(ListYcoordinate, coordY);
  od;
  ListPoint:=[];
  for i in [1..Length(ListYcoordinate)]
  do
    for coordX in [Minimum(ListByYcoordinate[i])..Maximum(ListByYcoordinate[i])]
    do
      Add(ListPoint, [coordX, ListYcoordinate[i]]);
    od;
  od;
  return ListPoint;
end;


CreateListPointQuadWithRotation:=function(ListFourPoints)
  local ePoint1, ePoint2, ePoint3, ePoint4, Equa13, Equa24, SGN24, SGN13, Trig1, Trig2, ListPoint, eTrig, i, eDat, eDatRev, u;
  ePoint1:=ShallowCopy(ListFourPoints[1]);
  Append(ePoint1, [1]);
  ePoint2:=ShallowCopy(ListFourPoints[2]);
  Append(ePoint2, [1]);
  ePoint3:=ShallowCopy(ListFourPoints[3]);
  Append(ePoint3, [1]);
  ePoint4:=ShallowCopy(ListFourPoints[4]);
  Append(ePoint4, [1]);
  Equa13:=LineEquation(ePoint1, ePoint3);
  Equa24:=LineEquation(ePoint2, ePoint4);
  SGN24:=(Equa13*ePoint2)*(Equa13*ePoint4);
  SGN13:=(Equa24*ePoint1)*(Equa24*ePoint3);
  if SGN13<=0 then
    Trig1:=[ListFourPoints[1],ListFourPoints[3],ListFourPoints[2]];
    Trig2:=[ListFourPoints[1],ListFourPoints[3],ListFourPoints[4]];
  else
    Trig1:=[ListFourPoints[2],ListFourPoints[4],ListFourPoints[1]];
    Trig2:=[ListFourPoints[2],ListFourPoints[4],ListFourPoints[3]];
  fi;

  ListPoint:=[];
  for eTrig in [Trig1, Trig2]
  do
    for i in [0..1]
    do
      eDat:=rec(ord:=i, VTrans:=[0,0]);
      if i=0 then
        eDatRev:=rec(ord:=0, VTrans:=[0,0]);
      else
        eDatRev:=rec(ord:=4-i, VTrans:=[0,0]);
      fi;
      for u in CreateListPoint([PlaneRotationQuad(eDat, eTrig[1]), PlaneRotationQuad(eDat, eTrig[2]), PlaneRotationQuad(eDat, eTrig[3])])
      do
        AddSet(ListPoint, PlaneRotationQuad(eDatRev, u));
      od;
    od;
  od;
  return ListPoint;
end;












CreateListPointTrigWithRotation:=function(ListThreePoints)
  local ListPoint, i, eDat, eDatRev, ePoint1, ePoint2, ePoint3, u;
  ePoint1:=ListThreePoints[1];
  ePoint2:=ListThreePoints[2];
  ePoint3:=ListThreePoints[3];
  ListPoint:=[];
  for i in [0..2]
  do
    eDat:=rec(ord:=i, VTrans:=[0,0]);
    if i=0 then
      eDatRev:=rec(ord:=0, VTrans:=[0,0]);
    else
      eDatRev:=rec(ord:=6-i, VTrans:=[0,0]);
    fi;
    for u in CreateListPoint([PlaneRotationTrig(eDat, ePoint1), PlaneRotationTrig(eDat, ePoint2), PlaneRotationTrig(eDat, ePoint3)])
    do
      AddSet(ListPoint, PlaneRotationTrig(eDatRev, u));
    od;
  od;
  return ListPoint;
end;





CreateGraphFromEisensteinTriangulation:=function(TheTriangulation)
  local ListBeforeQuotient, ListOfPos, nbTrig, iTrig, jTrig, ListOnTrig, ePoint, Gra, Ordi, ListjTrig, eTrig, ListRotation, List3points, ePoint1, ePoint2, fPoint1, fPoint2, pos, eOrdi2, i, fPoint, iPoint, VertexSet, nbVert, iHex, ListHexAdj, iVert, jVert, jv1, jv2, SPos1, SPos2, Pos1, Pos2, ListOrd, NewVert1, NewVert2, NewTriangulation, FuncFindTrig, eRepr;
  ListBeforeQuotient:=[];
  ListOfPos:=[0];
  nbTrig:=Length(TheTriangulation);
  for iTrig in [1..nbTrig]
  do
    ListOnTrig:=CreateListPointTrigWithRotation(TheTriangulation[iTrig][1]);
#    Print("ListOnTrig=", ListOnTrig, "\n");
    Add(ListBeforeQuotient, ListOnTrig);
    Add(ListOfPos, Length(ListOnTrig)+ListOfPos[iTrig]);
  od;
  Gra:=NullGraph(Group(()), ListOfPos[nbTrig+1]);
  Ordi:=[[1,2],[2,3],[3,1]];
  for iTrig in [1..nbTrig]
  do
    eTrig:=TheTriangulation[iTrig];
    ListjTrig:=[eTrig[2][1][1],eTrig[2][2][1],eTrig[2][3][1]];
    ListRotation:=[];
    for i in [1..3]
    do
      ePoint1:=eTrig[1][Ordi[i][1]];
      ePoint2:=eTrig[1][Ordi[i][2]];
      jTrig:=eTrig[2][i][1];
      List3points:=TheTriangulation[jTrig][1];
      eOrdi2:=Ordi[eTrig[2][i][2]];
      fPoint1:=List3points[eOrdi2[2]];
      fPoint2:=List3points[eOrdi2[1]];
      Add(ListRotation, CreateRotationTrig(ePoint1, ePoint2, fPoint1, fPoint2));
    od;
#    Print("iTrig       =", iTrig, "\n");
#    Print("ListjTrig   =", ListjTrig, "\n");
#    Print("ListRotation=", ListRotation, "\n");
    for iPoint in [1..Length(ListBeforeQuotient[iTrig])]
    do
      ePoint:=ListBeforeQuotient[iTrig][iPoint];
      for i in [1..3]
      do
        fPoint:=PlaneRotationTrig(ListRotation[i], ePoint);
        jTrig:=ListjTrig[i];
        pos:=Position(ListBeforeQuotient[jTrig], fPoint);
        if pos<>fail then
          AddEdgeOrbit(Gra, [ListOfPos[iTrig]+iPoint, ListOfPos[jTrig]+pos]);
        fi;
      od;
    od;
  od;
  VertexSet:=ConnectedComponents(Gra);
  nbVert:=Length(VertexSet);
  FuncFindTrig:=function(idx)
    local iTrig;
    iTrig:=1;
    while(true)
    do
      if ListOfPos[iTrig]<idx and ListOfPos[iTrig+1]>=idx then
        return iTrig;
      fi;
      iTrig:=iTrig+1;
    od;
  end;


  ListHexAdj:=[[1,0],[0,1],[-1,1],[-1,0],[0,-1],[1,-1]];
  NewTriangulation:=[];
  for iVert in [1..nbVert]
  do
    ListOrd:=[];
    for eRepr in VertexSet[iVert]
    do
      iTrig:=FuncFindTrig(eRepr);
      ePoint:=ListBeforeQuotient[iTrig][eRepr-ListOfPos[iTrig]];
      for iHex in [1..6]
      do
        NewVert1:=ePoint+ListHexAdj[iHex];
        NewVert2:=ePoint+ListHexAdj[NextIdx(6,iHex)];
        Pos1:=Position(ListBeforeQuotient[iTrig], NewVert1);
        Pos2:=Position(ListBeforeQuotient[iTrig], NewVert2);
        if Pos1<>fail and Pos2<>fail then
          SPos1:=ListOfPos[iTrig]+Pos1;
          SPos2:=ListOfPos[iTrig]+Pos2;
          for jVert in [1..nbVert]
          do
            if SPos1 in VertexSet[jVert] then
              jv1:=jVert;
            fi;
            if SPos2 in VertexSet[jVert] then
              jv2:=jVert;
            fi;
          od;
          AddSet(ListOrd, [jv1,jv2]);
        fi;
      od;
    od;
    NewTriangulation[iVert]:=CreateOrderedListAdj(ListOrd);
  od;
  return DualGraph(NewTriangulation).PlanGraph;
end;















CreateGraphFromGaussianQuadrangulation:=function(TheQuadrangulation)
  local ListBeforeQuotient, ListOfPos, nbQuad, ListOnQuad, Gra, Ordi, iQuad, eQuad, ListjQuad, ListRotation, i, ePoint1, ePoint2, jQuad, List4points, eOrdi2, fPoint1, fPoint2, iPoint, ePoint, fPoint, pos, VertexSet, nbVert, ListLocalRotation, FuncFindAnAdjacentVertex, FuncFindNextAdjacent, FuncFindSquare, ListQuadAdj, Pos, Pos2, TheNewQuadrangulation, Ladj, eVert, fVert;
  ListBeforeQuotient:=[];
  ListOfPos:=[0];
  nbQuad:=Length(TheQuadrangulation);
  for iQuad in [1..nbQuad]
  do
    ListOnQuad:=CreateListPointQuadWithRotation(TheQuadrangulation[iQuad][1]);
    Add(ListBeforeQuotient, ListOnQuad);
    Add(ListOfPos, Length(ListOnQuad)+ListOfPos[iQuad]);
  od;
  Gra:=NullGraph(Group(()), ListOfPos[nbQuad+1]);
  Ordi:=[[1,2],[2,3],[3,4], [4,1]];
  ListLocalRotation:=[];
  for iQuad in [1..nbQuad]
  do
    eQuad:=TheQuadrangulation[iQuad];
    ListjQuad:=[eQuad[2][1][1],eQuad[2][2][1],eQuad[2][3][1],eQuad[2][4][1]];
    ListRotation:=[];
    for i in [1..4]
    do
      ePoint1:=eQuad[1][Ordi[i][1]];
      ePoint2:=eQuad[1][Ordi[i][2]];
      jQuad:=eQuad[2][i][1];
      List4points:=TheQuadrangulation[jQuad][1];
      eOrdi2:=Ordi[eQuad[2][i][2]];
      fPoint1:=List4points[eOrdi2[2]];
      fPoint2:=List4points[eOrdi2[1]];
      Add(ListRotation, CreateRotationQuad(ePoint1, ePoint2, fPoint1, fPoint2));
    od;
    Add(ListLocalRotation, ListRotation);
    for iPoint in [1..Length(ListBeforeQuotient[iQuad])]
    do
      ePoint:=ListBeforeQuotient[iQuad][iPoint];
      for i in [1..4]
      do
        fPoint:=PlaneRotationQuad(ListRotation[i], ePoint);
        jQuad:=ListjQuad[i];
        pos:=Position(ListBeforeQuotient[jQuad], fPoint);
        if pos<>fail then
          AddEdgeOrbit(Gra, [ListOfPos[iQuad]+iPoint, ListOfPos[jQuad]+pos]);
        fi;
      od;
    od;
  od;
  VertexSet:=ConnectedComponents(Gra);
  nbVert:=Length(VertexSet);
  ListQuadAdj:=[[1,0],[0,1],[-1,0],[0,-1]];
  FuncFindSquare:=function(idx)
    local iQuad;
    iQuad:=1;
    while(true)
    do
      if ListOfPos[iQuad]<idx and ListOfPos[iQuad+1]>=idx then
        return iQuad;
      fi;
      iQuad:=iQuad+1;
    od;
  end;
  FuncFindAnAdjacentVertex:=function(eVert)
    local eRepr, iQuad, ePoint, eSQ, NewVert, Pos, SPos;
    for eRepr in VertexSet[eVert]
    do
      iQuad:=FuncFindSquare(eRepr);
      ePoint:=ListBeforeQuotient[iQuad][eRepr-ListOfPos[iQuad]];
      for eSQ in ListQuadAdj
      do
        NewVert:=ePoint+eSQ;
        Pos:=Position(ListBeforeQuotient[iQuad], NewVert);
        if Pos<>fail then
          SPos:=ListOfPos[iQuad]+Pos;
          for i in [1..nbVert]
          do
            if SPos in VertexSet[i] then
              return i;
            fi;
          od;
        fi;
      od;
    od;
    return fail;
  end;
  #
  # eVert is adjacent to fVert, what is
  # the next vertex in the cyclic ordering?
  FuncFindNextAdjacent:=function(eVert, fVert)
    local eListQuad, eRepr, fListQuad, fRepr, iRepr, jRepr, iQuad, ePoint, fPoint, eMove, iMove, gPoint, Pos, i, iAdj, fPointMV, iMoveMV, jQuad, SPos;
    eListQuad:=[];
    for iRepr in [1..Length(VertexSet[eVert])]
    do
      eRepr:=VertexSet[eVert][iRepr];
      Add(eListQuad, FuncFindSquare(eRepr));
    od;
    fListQuad:=[];
    for jRepr in [1..Length(VertexSet[fVert])]
    do
      fRepr:=VertexSet[fVert][jRepr];
      Add(fListQuad, FuncFindSquare(fRepr));
    od;
    iQuad:=Intersection(eListQuad, fListQuad)[1];
    eRepr:=VertexSet[eVert][Position(eListQuad, iQuad)];
    fRepr:=VertexSet[fVert][Position(fListQuad, iQuad)];
    ePoint:=ListBeforeQuotient[iQuad][eRepr-ListOfPos[iQuad]];
    fPoint:=ListBeforeQuotient[iQuad][fRepr-ListOfPos[iQuad]];
    eMove:=fPoint-ePoint;
    iMove:=Position(ListQuadAdj, eMove);
    gPoint:=ePoint+ListQuadAdj[NextIdx(4,iMove)];
    Pos:=Position(ListBeforeQuotient[iQuad], gPoint);
    if Pos<>fail then
      SPos:=Pos+ListOfPos[iQuad];
      for i in [1..nbVert]
      do
        if SPos in VertexSet[i] then
          return i;
        fi;
      od;
    fi;
    for i in [1..2]
    do
      iMove:=NextIdx(4, iMove);
      gPoint:=fPoint+ListQuadAdj[iMove];
      Pos:=Position(ListBeforeQuotient[iQuad], gPoint);
      if Pos<>fail then
        fPoint:=gPoint;
        SPos:=ListOfPos[iQuad]+Pos;
      else
        iAdj:=1;
        while(true)
        do
          jQuad:=TheQuadrangulation[iQuad][2][iAdj][1];
          fPointMV:=PlaneRotationQuad(ListLocalRotation[iQuad][iAdj],fPoint);
          iMoveMV:=NextKIdx(4, iMove, ListLocalRotation[iQuad][iAdj].ord);
          Pos:=Position(ListBeforeQuotient[jQuad], fPointMV);
          if Pos<>fail then
            gPoint:=fPointMV+ListQuadAdj[iMoveMV];
            Pos2:=Position(ListBeforeQuotient[jQuad], gPoint);
            if Pos2<>fail then
              iMove:=iMoveMV;
              iQuad:=jQuad;
              fPoint:=gPoint;
              SPos:=ListOfPos[iQuad]+Pos2;
              break;
            fi;
          fi;
          iAdj:=iAdj+1;
        od;
      fi;
    od;
    for i in [1..nbVert]
    do
      if SPos in VertexSet[i] then
        return i;
      fi;
    od;
  end;
  TheNewQuadrangulation:=[];
  for eVert in [1..nbVert]
  do
    fVert:=FuncFindAnAdjacentVertex(eVert);
    Ladj:=[fVert];
    while(true)
    do
      fVert:=FuncFindNextAdjacent(eVert, fVert);
      if fVert=Ladj[1] then
        break;
      fi;
      Add(Ladj, fVert);
    od;
    Add(TheNewQuadrangulation, Ladj);
  od;
  return DualGraph(TheNewQuadrangulation).PlanGraph;
end;




OctahedriteSymmetryO:=function(Z1)
  local iZ1, TheQuad, ListQuad;
  iZ1:=PlaneRotationQuad(rec(ord:=1, VTrans:=[0,0]), Z1);
  TheQuad:=[[0,0],Z1, Z1+iZ1, iZ1];
  ListQuad:=[];

  Add(ListQuad, [TheQuad, [[4,4],[5,1],[2,1],[3,1]]]);
  Add(ListQuad, [TheQuad, [[1,3],[5,4],[6,1],[3,2]]]);
  Add(ListQuad, [TheQuad, [[1,4],[2,4],[6,4],[4,1]]]);
  Add(ListQuad, [TheQuad, [[3,4],[6,3],[5,2],[1,1]]]);
  Add(ListQuad, [TheQuad, [[1,2],[4,3],[6,2],[2,2]]]);
  Add(ListQuad, [TheQuad, [[2,3],[5,3],[4,2],[3,3]]]);

  return CreateGraphFromGaussianQuadrangulation(ListQuad);
end;



OctahedriteSymmetryD4:=function(Z1, Z2)
  local iZ1, TheQuad1, TheQuad2, ListQuad;
  iZ1:=PlaneRotationQuad(rec(ord:=1, VTrans:=[0,0]), Z1);
  TheQuad1:=[[0,0],Z1, Z1+iZ1, iZ1];
  TheQuad2:=[[0,0],Z1, Z1+Z2, Z2];

  ListQuad:=[];
  Add(ListQuad, [TheQuad1, [[4,1],[5,1],[2,1],[3,1]]]);
  Add(ListQuad, [TheQuad2, [[1,3],[5,4],[6,1],[3,2]]]);
  Add(ListQuad, [TheQuad2, [[1,4],[2,4],[6,4],[4,2]]]);
  Add(ListQuad, [TheQuad2, [[1,1],[3,4],[6,3],[5,2]]]);
  Add(ListQuad, [TheQuad2, [[1,2],[4,4],[6,2],[2,2]]]);
  Add(ListQuad, [TheQuad1, [[2,3],[5,3],[4,3],[3,3]]]);

  return CreateGraphFromGaussianQuadrangulation(ListQuad);
end;



OctahedriteSymmetryD3:=function(Z1, Z2)
  local iZ1, TheQuad, ListQuad;
  iZ1:=PlaneRotationQuad(rec(ord:=1, VTrans:=[0,0]), Z1);
  TheQuad:=[[0,0],Z1, Z2, iZ1];

  ListQuad:=[];
  Add(ListQuad, [TheQuad, [[3,4],[6,2],[4,3],[2,1]]]);
  Add(ListQuad, [TheQuad, [[1,4],[4,2],[5,3],[3,1]]]);
  Add(ListQuad, [TheQuad, [[2,4],[5,2],[6,3],[1,1]]]);
  Add(ListQuad, [TheQuad, [[5,4],[2,2],[1,3],[6,1]]]);
  Add(ListQuad, [TheQuad, [[6,4],[3,2],[2,3],[4,1]]]);
  Add(ListQuad, [TheQuad, [[4,4],[1,2],[3,3],[5,1]]]);

  return CreateGraphFromGaussianQuadrangulation(ListQuad);
end;












#
# Eis1 and Eis2 are the two Eisenstein integer defining the graph
# of type 3n
Graph3n:=function(Eis1, Eis2)
  local TheTrig, ListTrig;
  ListTrig:=[];
  TheTrig:=[[0,0],Eis1, Eis2];
  Add(ListTrig, [TheTrig, [[2,1],[3,1],[4,1]]]);
  #
  TheTrig:=[Eis1, [0,0], Eis1-Eis2];
  Add(ListTrig, [TheTrig, [[1,1],[4,3],[3,2]]]);
  #
  TheTrig:=[Eis2, Eis1, Eis1+Eis2];
  Add(ListTrig, [TheTrig, [[1,2],[2,3],[4,2]]]);
  #
  TheTrig:=[[0,0], Eis2, Eis2-Eis1];
  Add(ListTrig, [TheTrig, [[1,3],[3,3],[2,2]]]);

  return CreateGraphFromEisensteinTriangulation(ListTrig);
end;




Graph4nSymmetryD3:=function(Eis1, Eis2)
  local OmegaEis1, TheTrig, ListTrig;
  OmegaEis1:=PlaneRotationTrig(rec(ord:=1, VTrans:=[0,0]), Eis1);
  ListTrig:=[];
  TheTrig:=[[0,0],Eis1,OmegaEis1];
  Add(ListTrig, [TheTrig, [[4,1],[2,1],[3,1]]]);
  #
  TheTrig:=[[0,0], Eis1, Eis2];
  Add(ListTrig, [TheTrig, [[1,2],[7,3],[5,1]]]);
  #
  Add(ListTrig, [TheTrig, [[1,3],[5,3],[6,1]]]);
  #
  Add(ListTrig, [TheTrig, [[1,1],[6,3],[7,1]]]);
  #
  TheTrig:=[[0,0],Eis2, Eis2-Eis1];
  Add(ListTrig, [TheTrig, [[2,3],[8,3],[3,2]]]);
  #
  Add(ListTrig, [TheTrig, [[3,3],[8,2],[4,2]]]);
  #
  Add(ListTrig, [TheTrig, [[4,3],[8,1],[2,2]]]);
  #
  TheTrig:=[[0,0],Eis1,OmegaEis1];
  Add(ListTrig, [TheTrig, [[7,2],[6,2],[5,2]]]);

  return CreateGraphFromEisensteinTriangulation(ListTrig);
end;



Graph5nSymmetryT:=function(Eis1, Eis2)
  local OmegaEis1, OmegaEis2, TheTrig1, TheTrig2, TheTrig3, ListTrig;
  OmegaEis1:=PlaneRotationTrig(rec(ord:=1, VTrans:=[0,0]), Eis1);
  OmegaEis2:=PlaneRotationTrig(rec(ord:=1, VTrans:=[0,0]), Eis2);
  ListTrig:=[];
  TheTrig1:=[[0,0],Eis1,OmegaEis1];
  TheTrig2:=[[0,0],Eis2,OmegaEis2];
  TheTrig3:=[[0,0],Eis1,Eis2];
  ListTrig[1]:=[TheTrig1,  [[4,1], [2,1], [3,1] ]];
  ListTrig[2]:=[TheTrig3,  [[1,2], [10,2],[5,1] ]];
  ListTrig[3]:=[TheTrig3,  [[1,3], [8,2], [6,3] ]];
  ListTrig[4]:=[TheTrig3,  [[1,1], [9,2], [7,3] ]];
  ListTrig[5]:=[TheTrig2,  [[2,3], [11,3],[8,3] ]];
  ListTrig[6]:=[TheTrig2,  [[12,3],[9,3], [3,3] ]];
  ListTrig[7]:=[TheTrig2,  [[13,3],[10,3],[4,3] ]];
  ListTrig[8]:=[TheTrig3,  [[15,1],[3,2], [5,3] ]];
  ListTrig[9]:=[TheTrig3,  [[16,3],[4,2], [6,2] ]];
  ListTrig[10]:=[TheTrig3, [[14,1],[2,2], [7,2] ]];
  ListTrig[11]:=[TheTrig3, [[14,3],[17,2],[5,2] ]];
  ListTrig[12]:=[TheTrig3, [[15,3],[18,2],[6,1] ]];
  ListTrig[13]:=[TheTrig3, [[16,2],[19,2],[7,1] ]];
  ListTrig[14]:=[TheTrig1, [[10,1],[19,1],[11,1]]];
  ListTrig[15]:=[TheTrig1, [[8,1], [17,1],[12,1]]];
  ListTrig[16]:=[TheTrig1, [[18,1],[13,1],[9,1] ]];
  ListTrig[17]:=[TheTrig3, [[15,2],[11,2],[20,1]]];
  ListTrig[18]:=[TheTrig3, [[16,1],[12,2],[20,3]]];
  ListTrig[19]:=[TheTrig3, [[14,2],[13,2],[20,2]]];
  ListTrig[20]:=[TheTrig2, [[17,3],[19,3],[18,3]]];
  return CreateGraphFromEisensteinTriangulation(ListTrig);
end;



Graph5nSymmetryDm:=function(Eis1, Eis2, m)
  local OmegaEis1, TheTrig1, TheTrig2, ListTrig, i, iNext, iPrev;
  OmegaEis1:=PlaneRotationTrig(rec(ord:=1, VTrans:=[0,0]), Eis1);
  TheTrig1:=[[0,0],Eis1, OmegaEis1];
  TheTrig2:=[[0,0],Eis1, Eis2];
  ListTrig:=[];
  for i in [1..m]
  do
    iNext:=NextIdx(m, i);
    iPrev:=PrevIdx(m, i);
    ListTrig[i]:=[TheTrig1, [[m+i, 1],[iNext, 3],[iPrev,2]]];
    ListTrig[m+i]:=[TheTrig2, [[i,1],[2*m+i,2],[2*m+iNext,3]]];
    ListTrig[2*m+i]:=[TheTrig2, [[3*m+i,1],[m+i,2],[m+iPrev,3]]];
    ListTrig[3*m+i]:=[TheTrig1, [[2*m+i,1],[3*m+iPrev,3],[3*m+iNext,2]]];
  od;
  return CreateGraphFromEisensteinTriangulation(ListTrig);
end;



Graph5nSymmetryD3:=function(Eis1, Eis2, Eis3)
  local Eis4, Eis5, TheTrig1, TheTrig2, TheTrig3, TheTrig4, ListTrig;
  Eis4:=Eis1+PlaneRotationTrig(rec(ord:=2, VTrans:=[0,0]), Eis2-Eis1);
  Eis5:=PlaneRotationTrig(rec(ord:=1, VTrans:=[0,0]), Eis3-Eis2);
  TheTrig1:=[Eis1, Eis2, [0,0]];
  TheTrig2:=[Eis2, Eis3, [0,0]];
  TheTrig3:=[Eis1, [0,0], Eis4];
  TheTrig4:=[[0,0], Eis5, Eis4];
  ListTrig:=[];
  ListTrig[1]:=[TheTrig1, [[6,3], [15,3], [2,1]]];
  ListTrig[2]:=[TheTrig3, [[1,3], [17,3], [3,1]]];
  ListTrig[3]:=[TheTrig1, [[2,3], [7,3], [4,1]]];
  ListTrig[4]:=[TheTrig3, [[3,3], [9,3], [5,1]]];
  ListTrig[5]:=[TheTrig1, [[4,3], [11,3], [6,1]]];
  ListTrig[6]:=[TheTrig3, [[5,3], [13,3], [1,1]]];
  ListTrig[7]:=[TheTrig2, [[18,1], [8,2], [3,2]]];
  ListTrig[8]:=[TheTrig2, [[9,1], [7,2], [20,2]]];
  ListTrig[9]:=[TheTrig4, [[8,1], [10,2], [4,2]]];
  ListTrig[10]:=[TheTrig4, [[11,1], [9,2], [21,2]]];
  ListTrig[11]:=[TheTrig2, [[10,1], [12,2], [5,2]]];
  ListTrig[12]:=[TheTrig2, [[13,1], [11,2], [22,2]]];
  ListTrig[13]:=[TheTrig4, [[12,1], [14,2], [6,2]]];
  ListTrig[14]:=[TheTrig4, [[15,1], [13,2], [23,2]]];
  ListTrig[15]:=[TheTrig2, [[14,1], [16,2], [1,2]]];
  ListTrig[16]:=[TheTrig2, [[17,1], [15,2], [24,2]]];
  ListTrig[17]:=[TheTrig4, [[16,1], [18,2], [2,2]]];
  ListTrig[18]:=[TheTrig4, [[7,1], [17,2], [19,2]]];
  ListTrig[19]:=[TheTrig3, [[20,3], [18,3], [24,1]]];
  ListTrig[20]:=[TheTrig1, [[21,3], [8,3], [19,1]]];
  ListTrig[21]:=[TheTrig3, [[22,3], [10,3], [20,1]]];
  ListTrig[22]:=[TheTrig1, [[23,3], [12,3], [21,1]]];
  ListTrig[23]:=[TheTrig3, [[24,3], [14,3], [22,1]]];
  ListTrig[24]:=[TheTrig1, [[19,3], [16,3], [23,1]]];
  return CreateGraphFromEisensteinTriangulation(ListTrig);
end;






HexTiling:=function(Eis1, Eis2)
  local ListTrig;
  ListTrig:=[];
  ListTrig[1]:=[ [[0,0], Eis1, Eis2], [[2,2],[2,3],[2,1]]];
  ListTrig[2]:=[ [Eis2, [0,0],Eis1], [[1,3],[1,1],[1,2]]];
  return CreateGraphFromEisensteinTriangulation(ListTrig);
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
  if Length(ListGenMapped)=0 then
    GrpFlag:=Group(());
  else
    GrpFlag:=Group(ListGenMapped);
  fi;
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
  if Length(ListGen)=0 then
    GroupFlag1:=Group(());
  else
    GroupFlag1:=Group(ListGen);
  fi;
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
  FuncGroup:=function(LGen)
    if Length(LGen)=0 then
      return Group(());
    else
      return Group(LGen);
    fi;
  end;
  ListGen:=[()];
  GrpSize:=1;
  FuncInsert:=function(OneTrans)
    local nbS, ListNew;
    ListNew:=Union(ListGen, [OneTrans]);
    nbS:=Order(FuncGroup(ListNew));
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
  if Length(ListGen)=0 then
    return Group(());
  else
    return Group(ListGen);
  fi;
end;


IsIrreducibleTorus:=function(PlanGraph)
  local PLori, PLE, TransGroup;
  PLori:=PlanGraphToPlanGraphOriented(PlanGraph);
  PLE:=PlanGraphOrientedPreparationParametrization(PLori);
  TransGroup:=TorusTranslationSubgroup(PLE);
  if Order(TransGroup)=1 then
    return true;
  fi;
  return false;
end;



#FindIrreducibleComponent:=function(PlanGraph)
#end;






GroupTorus:=function(PlanGraph)
  local PLori, PLE, TransGroup, SpaceSymbol, CC, TheSym, NbCells, GRP, GrpRot, ListNumbersSeparatrixLines, ListStab2, ListStab3, ListStab4, AllIncluded, IsIncluded, eLine, Stab, i, j, ListLines, ListStab, ListSymmetryTranslation, ListSymmetry, ListConn, IND, SIZ, u, GRA;
  PLori:=PlanGraphToPlanGraphOriented(PlanGraph);
  PLE:=PlanGraphOrientedPreparationParametrization(PLori);
  TransGroup:=TorusTranslationSubgroup(PLE);
  if Order(TransGroup)>1 then
    Print("The torus should be irreducible\n");
    return false;
  fi;
  CC:=PLE.CC;
  GRA:=CC.GraphPoset;
#  Print("ord Sym of GRA=", Order(AutGroupGraph(GRA)), "\n");
  TheSym:=NullGraph(Group(()), GRA.order);
  for i in [1..GRA.order]
  do
    for j in [1..GRA.order]
    do
      if IsEdge(GRA, [i,j]) then
        AddEdgeOrbit(TheSym, [i,j]);
        AddEdgeOrbit(TheSym, [j,i]);
      fi;
    od;
  od;
  #
  #
  NbCells:=Length(CC.ListCells);
  GRP:=PLE.GRP;
  GrpRot:=PLE.RotationGroup;
  if Order(GrpRot)=6 then
    if GrpRot=GRP then
       SpaceSymbol:="p6";
    else
       SpaceSymbol:="p6mm";
    fi;
    return rec(SpaceSymbol:=SpaceSymbol);
  fi;
  ListSymmetry:=[];
  ListSymmetryTranslation:=[];
  ListLines:=[];
  ListNumbersSeparatrixLines:=[];

  for u in Difference(GRP, GrpRot)
  do
    ListStab:=[];
    for i in [1..NbCells]
    do
      if OnPoints(i, u)=i then
        Add(ListStab, i);
      fi;
    od;
    IND:=InducedSubgraph(TheSym, ListStab);
    ListConn:=ConnectedComponents(IND);
    Add(ListNumbersSeparatrixLines, Length(ListConn));
    if Length(ListStab)=0 then
      Add(ListSymmetryTranslation, u);
    else
      Add(ListSymmetry, u);
      AddSet(ListLines, ListStab);
    fi;
  od;


  ListStab2:=[];
  ListStab3:=[];
  ListStab4:=[];
  for i in [1..NbCells]
  do
    Stab:=Stabilizer(GrpRot, i, OnPoints);
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
#  Print("ListStab2=", ListStab2, "\n");
#  Print("ListStab3=", ListStab3, "\n");
#  Print("ListStab4=", ListStab4, "\n");


  if Length(ListStab4)>0 then
    if GrpRot=GRP then
      SpaceSymbol:="p4";
    else
      IsIncluded:=false;
      for eLine in ListLines
      do
        SIZ:=Length(Intersection(eLine, ListStab4));
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
    if GrpRot=GRP then
      SpaceSymbol:="p3";
    else
      AllIncluded:=true;
      for eLine in ListLines
      do
        if IsSubset(eLine, ListStab3)=false then
          AllIncluded:=false;
        fi;
      od;
      if AllIncluded=true then
        SpaceSymbol:="p3m1";
      else
        SpaceSymbol:="p31m";
      fi;
    fi;
    return rec(SpaceSymbol:=SpaceSymbol);
  elif Length(ListStab2)>0 then
    if GRP=GrpRot then
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
        Print("We have an error HERE_1\n");
        Print(NullMat(5));
        return false;
      fi;
    fi;
  elif Order(GrpRot)=1 then
    if GRP=GrpRot then
      SpaceSymbol:="p1";
    else
      if ListNumbersSeparatrixLines=[2] then
        SpaceSymbol:="pm";
      elif ListNumbersSeparatrixLines=[1] then
        SpaceSymbol:="cm";
      elif ListNumbersSeparatrixLines=[0] then
        SpaceSymbol:="pg";
      else
        Print("We have an error HERE_2\n");
        return false;
        Print(NullMat(5));
      fi;
    fi;
  else
    Print("We have an error HERE_3\n");
    return false;
    Print(NullMat(5));
  fi;
  return rec(SpaceSymbol:=SpaceSymbol);
end;




RotationSubgroup:=function(PL, GRP)
  local nbV, ListDE, VEF, FaceSet, FaceSetRed, ListBelong, iFace, eFace, eDE, pos, ListFlag1, ListFlag2, iVert, Ladj, iAdj, eAdj, eDE1, pos1, eFace1, eDE2, pos2, eFace2, eEdge, FuncMapFlag, ListEltRot, eElt, nbInv, nbDir, eFlag1, eImgFlag, ListGen;
  nbV:=Length(PL);
  ListDE:=ListDirectedEdges(PL);
  VEF:=PlanGraphToVEFsecond(PL);
  FaceSet:=VEF[3];
  FaceSetRed:=List(FaceSet, x->Set(List(x, y->y[1])));
  ListBelong:=[];
  for iFace in [1..Length(FaceSet)]
  do
    eFace:=FaceSet[iFace];
    for eDE in eFace
    do
      pos:=Position(ListDE, eDE);
      ListBelong[pos]:=FaceSetRed[iFace];
    od;
  od;
  ListFlag1:=[];
  ListFlag2:=[];
  for iVert in [1..nbV]
  do
    Ladj:=PL[iVert];
    for iAdj in [1..Length(Ladj)]
    do
      eAdj:=Ladj[iAdj];
      eDE1:=[iVert, iAdj];
      pos1:=Position(ListDE, eDE1);
      eFace1:=ListBelong[pos1];
      eDE2:=ReverseDE(PL, eDE1);
      pos2:=Position(ListDE, eDE2);
      eFace2:=ListBelong[pos2];
      eEdge:=Set([eDE1[1], eDE2[1]]);
      Add(ListFlag1, [iVert, eEdge, eFace1]);
      Add(ListFlag2, [iVert, eEdge, eFace2]);
    od;
  od;
  FuncMapFlag:=function(eFlag, g)
    return [OnPoints(eFlag[1], g), OnSets(eFlag[2], g), OnSets(eFlag[3], g)];
  end;

  ListEltRot:=[];
  for eElt in GRP
  do
    nbDir:=0;
    nbInv:=0;
    for eFlag1 in ListFlag1
    do
      eImgFlag:=FuncMapFlag(eFlag1, eElt);
      if Position(ListFlag1, eImgFlag)<>fail then
        nbDir:=nbDir+1;
      fi;
      if Position(ListFlag2, eImgFlag)<>fail then
        nbInv:=nbInv+1;
      fi;
    od;
    if nbDir>0 and nbInv>0 then
      Print("We have an error in flag structure\n");
      Print(NullMat(5));
    fi;
    if nbInv=0 then
      Add(ListEltRot, eElt);
    fi;
  od;
  ListGen:=SmallGeneratingSet(Group(ListEltRot));
  return Group(ListGen);
end;


__ListOrbitDirectedEdges:=function(PL, GRP)
  local ListDE, iVert, LAdj, iAdj, MyAction, TheOrb;
  ListDE:=[];
  for iVert in [1..Length(PL)]
  do
    LAdj:=PL[iVert];
    for iAdj in [1..Length(LAdj)]
    do
      Add(ListDE, [iVert, iAdj]);
    od;
  od;
  MyAction:=function(eDE, eElt)
    local TheAdj, imgVert, imgAdj, ThePos;
    TheAdj:=PL[eDE[1]][eDE[2]];
    imgVert:=OnPoints(eDE[1], eElt);
    imgAdj:=OnPoints(TheAdj, eElt);
    ThePos:=Position(PL[imgVert], imgAdj);
    return [imgVert, ThePos];
  end;
  TheOrb:=Orbits(GRP, ListDE, MyAction);
  return TheOrb;
end;

ListOrbitRotationSubgroupDirectedEdges:=function(PL)
  local GRPinfo, TheGRP, TheRotSubgroup;
  GRPinfo:=GroupPlan(PL);
  TheGRP:=GRPinfo.SymmetryGroup;
  TheRotSubgroup:=RotationSubgroup(PL, TheGRP);
  return __ListOrbitDirectedEdges(PL, TheRotSubgroup);
end;

ListOrbitDirectedEdges:=function(PL)
  local GRPinfo, TheGRP;
  GRPinfo:=GroupPlan(PL);
  TheGRP:=GRPinfo.SymmetryGroup;
  return __ListOrbitDirectedEdges(PL, TheGRP);
end;



TranslationSubgroup:=function(PL, GRProt)
  local nbV, VEF, EdgeSet, FaceSet, IsTranslation, ListTranslationElement, ListGen;
  nbV:=Length(PL);
  VEF:=PlanGraphToVEF(PL);
  EdgeSet:=VEF[2];
  FaceSet:=List(VEF[3], x->Set(x));
  IsTranslation:=function(eElt)
    local iVert, eEdge, eFace;
    for iVert in [1..nbV]
    do
      if OnPoints(iVert, eElt)=iVert then
        return false;
      fi;
    od;
    for eEdge in EdgeSet
    do
      if OnSets(eEdge, eElt)=eEdge then
        return false;
      fi;
    od;
    for eFace in FaceSet
    do
      if OnSets(eFace, eElt)=eFace then
        return false;
      fi;
    od;
    return true;
  end;
  ListTranslationElement:=Filtered(GRProt, x->IsTranslation(x)=true);
  Add(ListTranslationElement, ());
  ListGen:=SmallGeneratingSet(Group(ListTranslationElement));
  return Group(ListGen);
end;


TorusTranslationSubgroupForPlanGraph:=function(PL)
  local CC, GRP, GRProt, GRPtrans;
  CC:=CellComplex(PL);
  GRP:=AutGroupGraph(CC.GraphPoset);
  GRProt:=RotationSubgroup(PL, GRP);
  GRPtrans:=TranslationSubgroup(PL, GRProt);
  return GRPtrans;
end;


TranslationQuotient:=function(PL, TranslationGroup)
  local nbV, O, ListBelong, iOrb, eElt, PLred, Ladj, eAdj;
  nbV:=Length(PL);
  O:=Orbits(TranslationGroup, [1..nbV], OnPoints);
  ListBelong:=ListWithIdenticalEntries(nbV, 0);
  for iOrb in [1..Length(O)]
  do
    for eElt in O[iOrb]
    do
      ListBelong[eElt]:=iOrb;
    od;
  od;
  PLred:=[];
  for iOrb in [1..Length(O)]
  do
    Ladj:=[];
    for eAdj in PL[O[iOrb][1]]
    do
      Add(Ladj, ListBelong[eAdj]);
    od;
    Add(PLred, Ladj);
  od;
  return PLred;
end;








#
# SymGRP should be a subgroup of RotationGroup on ListFlag1
PlanGraphOrientedExtractionParameter:=function(PLE, SymGRP)
  local ListFlagByFace, ListEquationsBasic, VEF, iFace, jFace, eFace, ListMatched, TheEqua, iFlag, eFlag, INVERS, NEXT, NbVert, NbFace, GRA, ListCurvature, NULLS, jFlag, TheDE, TheVert, OthDE, OthVert, ListGen, iGen, eGen, eCase, EquaSet, ListSeto, PowerOrder, iVert, jVert, nb, BSE, SME, u, INTS, IsFinished, testOK, iEdge, TheSpannProv, TheSpannEdges, ListListAdj, jEdge, Ladj, ListPos, eDE, rDE, ListEdgeDualGraph, FuncFindEdge, eEdge, fEdge, FaceSet, EdgeSet, VertSet, NewEdgeList, TheSpann2, ListM, ListSystem, ListStatus, 
  ListEdge, ListEdgeOriented, eSet, TheSpannEdges2, ListListMultiplier, ListMultiplier, ListCorrespondingFace, If, Jf, Ifp, Jfp, TheCoeff, eSol, iFaceFound, CreateListEqua, TheGoldbergParameterVector, TheGoldbergVectorSecond, TheGoldbergParameterVectorSecond, IsGoldbergIn, TheGoldbergVector,
  O, iOrb, ListCase;
  VertSet:=PLE.VEF.VertSet;
  EdgeSet:=PLE.VEF.EdgeSet;
  FaceSet:=PLE.VEF.FaceSet;
  ListEquationsBasic:=[];
  for eFace in FaceSet
  do
    TheEqua:=ListWithIdenticalEntries(Length(PLE.ListFlags1), 0);
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      eFlag:=PLE.ListFlags1[iFlag];
      if eFlag[3]=eFace then
        TheEqua[iFlag]:=1;
      fi;
    od;
    Add(ListEquationsBasic, TheEqua);
  od;
  INVERS:=PLE.PlanGraphOriented.invers;
  NEXT:=PLE.PlanGraphOriented.next;
  NbVert:=Length(VertSet);
  GRA:=NullGraph(Group(()), NbVert);
  ListCurvature:=[];
  for iVert in [1..NbVert]
  do
    for eDE in VertSet[iVert]
    do
      rDE:=OnPoints(eDE, INVERS);
      for jVert in [1..NbVert]
      do
        if Position(VertSet[jVert], rDE)<>fail then
          AddEdgeOrbit(GRA, [iVert, jVert]);
          AddEdgeOrbit(GRA, [jVert, iVert]);
        fi;
      od;
    od;
    Add(ListCurvature, 6-Length(VertSet[iVert]));
  od;
  ListEdgeDualGraph:=ShallowCopy(EdgeSet);
  FuncFindEdge:=function(eEdge, VSET)
    local fEdge, fSet, ListM, iVert, INTS;
    for fEdge in VSET
    do
      ListM:=[];
      for iVert in [1..NbVert]
      do
        INTS:=Intersection(Set(VertSet[iVert]), Set(fEdge));
        if Length(INTS)=1 then
          AddSet(ListM, iVert);
        fi;
      od;
      if ListM=eEdge then
        return fEdge;
      fi;
    od;
  end;

  TheSpannProv:=SpanningTreeGraph(GRA, 1);
  TheSpannEdges:=[];
  ListMatched:=[];
  for iEdge in [1..Length(TheSpannProv)]
  do
    eEdge:=TheSpannProv[iEdge];
    fEdge:=FuncFindEdge(eEdge, ListEdgeDualGraph);
    RemoveSet(ListEdgeDualGraph, fEdge);
    Add(TheSpannEdges, fEdge);
    Add(ListMatched, 0);
  od;

  ListSystem:=[];
  for eEdge in ListEdgeDualGraph
  do
    ListPos:=[];
    for eDE in eEdge
    do
      Add(ListPos, Position(PLE.ListCorrespondingDE, eDE));
    od;
    TheEqua:=ListWithIdenticalEntries(Length(PLE.ListFlags1), 0);
    TheEqua[ListPos[1]]:=1;
    TheEqua[ListPos[2]]:=1;
    Add(ListSystem, [ListPos[1], ListPos[2], 1]);
    Add(ListSystem, [ListPos[2], ListPos[1], 1]);
    Add(ListEquationsBasic, TheEqua);
  od;

  IsFinished:=false;
  while(IsFinished=false)
  do
    IsFinished:=true;
    for iEdge in [1..Length(TheSpannEdges)]
    do
      if ListMatched[iEdge]=0 then
        IsFinished:=false;
        Ladj:=[];
        SME:=[];
        for u in [1,2]
        do
          for iVert in [1..NbVert]
          do
            if Position(VertSet[iVert], TheSpannEdges[iEdge][u])<>fail then
              Add(SME, Set(VertSet[iVert]));
            fi;
          od;
        od;
        ListListAdj:=[[],[]];
        for jEdge in [1..Length(TheSpannEdges)]
        do
          if iEdge<>jEdge and ListMatched[jEdge]=0 then
            for u in [1,2]
            do
              INTS:=Intersection(Set(TheSpannEdges[jEdge]), SME[u]);
              if Length(INTS)=1 then
                Add(ListListAdj[u], jEdge);
              fi;
            od;
          fi;
        od;
        testOK:=false;
        u:=1;
        while(u<=2)
        do
          if Length(ListListAdj[u])=0 then
            TheDE:=TheSpannEdges[iEdge][u];
            OthDE:=TheSpannEdges[iEdge][3-u];
            testOK:=true;
            break;
          fi;
          u:=u+1;
        od;
        if testOK=true then
          ListMatched[iEdge]:=1;
          for iVert in [1..NbVert]
          do
            if Position(VertSet[iVert], TheDE)<>fail then
              TheVert:=iVert;
            fi;
            if Position(VertSet[iVert], OthDE)<>fail then
              OthVert:=iVert;
            fi;
          od;
          TheEqua:=[];
          for iFlag in [1..Length(PLE.ListFlags1)]
          do
            Add(TheEqua, 0);
          od;
          iFlag:=Position(PLE.ListCorrespondingDE, TheDE);
          jFlag:=Position(PLE.ListCorrespondingDE, OthDE);
          TheCoeff:=E(6)^(ListCurvature[TheVert]);
          TheEqua[iFlag]:=1;
          TheEqua[jFlag]:=TheCoeff;
          Add(ListSystem, [iFlag, jFlag, TheCoeff]);
          Add(ListSystem, [jFlag, iFlag, (TheCoeff)^(-1)]);
          Add(ListEquationsBasic, TheEqua);
          ListCurvature[OthVert]:=ListCurvature[OthVert]+ListCurvature[TheVert];
          ListCurvature[TheVert]:=0;
        fi;
      fi;
    od;
  od;

  #TheSpann Bis
  NbFace:=Length(FaceSet);
  GRA:=NullGraph(Group(()), NbFace);
  NewEdgeList:=Difference(Set(EdgeSet), Set(TheSpannEdges));
  ListEdge:=[];
  ListEdgeOriented:=[];
  for eEdge in NewEdgeList
  do
    ListMatched:=[];
    for iFace in [1..Length(FaceSet)]
    do
      INTS:=Intersection(Set(FaceSet[iFace]), Set(eEdge));
      if Length(INTS)=1 then
        Add(ListMatched, iFace);
      fi;
    od;
    eSet:=Set(ListMatched);
    Add(ListEdge, eSet);
    AddEdgeOrbit(GRA, [eSet[1], eSet[2]]);
    AddEdgeOrbit(GRA, [eSet[2], eSet[1]]);
    Add(ListEdgeOriented, eEdge);
  od;
  TheSpann2:=SpanningTreeGraph(GRA, 1);
  TheSpannEdges2:=[];
  ListMatched:=[];
  for iEdge in [1..Length(TheSpann2)]
  do
    eEdge:=TheSpann2[iEdge];
    Add(TheSpannEdges2, ListEdgeOriented[Position(ListEdge, eEdge)]);
    Add(ListMatched, 0);
  od;

  ListGen:=GeneratorsOfGroup(SymGRP);
  if Order(SymGRP)=1 then
    ListGen:=[];
  fi;




  # ListListMultiplier contains the list of listmultiplier
  # listmultiplier is a list of complex numbers satisfying to
  # value(ImageFlag1)=listmultiplier[iflag]*value(Flag1[iFlag])
  ListListMultiplier:=[];
  for iGen in [1..Length(ListGen)]
  do
    eGen:=ListGen[iGen];
    ListMultiplier:=[];
    ListCorrespondingFace:=[];
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      ListMultiplier[iFlag]:="unset";
      iFace:=Position(FaceSet, PLE.ListFlags1[iFlag][3]);
      ListCorrespondingFace[iFlag]:=iFace;
    od;
    ListStatus:=ListWithIdenticalEntries(Length(FaceSet), 0);
    ListStatus[1]:=1;
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      if ListCorrespondingFace[iFlag]=1 then
        ListMultiplier[iFlag]:=1;
      fi;
    od;
    IsFinished:=false;
    while(IsFinished=false)
    do
      IsFinished:=true;
      for iFace in [1..Length(FaceSet)]
      do
        if ListStatus[iFace]=0 then
          IsFinished:=false;
          iFaceFound:=0;
          for jFace in [1..Length(FaceSet)]
          do
            eEdge:=Set([iFace, jFace]);
            if ListStatus[jFace]=1 and eEdge in TheSpann2 then
              iFaceFound:=jFace;
              fEdge:=ListEdgeOriented[Position(ListEdge, eEdge)];
              If:=Position(PLE.ListCorrespondingDE, Intersection(Set(fEdge), Set(FaceSet[iFace]))[1]);
              Jf:=Position(PLE.ListCorrespondingDE, Intersection(Set(fEdge), Set(FaceSet[jFace]))[1]);
              Ifp:=OnPoints(If, eGen);
              Jfp:=OnPoints(Jf, eGen);
            fi;
          od;
          if iFaceFound<>0 then
            ListStatus[iFace]:=1;
            for eSol in ListSystem
            do
              if eSol[1]=Ifp and eSol[2]=Jfp then
                TheCoeff:=ListMultiplier[Jf]*eSol[3];
                for iFlag in [1..Length(PLE.ListFlags1)]
                do
                  if ListCorrespondingFace[iFlag]=iFace then
                    ListMultiplier[iFlag]:=TheCoeff;
                  fi;
                od;
              fi;
            od;
          fi;
        fi;
      od;
    od;
    Add(ListListMultiplier, ListMultiplier);
  od;

  
  TheGoldbergParameterVector:=function()
    local TheVector, iFlag, pos1, pos2, pos3, iFlag1, iFlag2, iFlag3, TheEqua, ListEquaGold;
    ListEquaGold:=[];
    for iFace in [1..Length(FaceSet)]
    do
      pos1:=FaceSet[iFace][1];
      pos2:=OnPoints(OnPoints(pos1, NEXT), INVERS);
      pos3:=OnPoints(OnPoints(pos2, NEXT), INVERS);
      iFlag1:=Position(PLE.ListCorrespondingDE, pos1);
      iFlag2:=Position(PLE.ListCorrespondingDE, pos2);
      iFlag3:=Position(PLE.ListCorrespondingDE, pos3);
      TheEqua:=ListWithIdenticalEntries(Length(PLE.ListFlags1), 0);
      TheEqua[iFlag1]:=1;
      TheEqua[iFlag3]:=E(6);
      Add(ListEquaGold, TheEqua);
      TheEqua:=ListWithIdenticalEntries(Length(PLE.ListFlags1), 0);
      TheEqua[iFlag3]:=1;
      TheEqua[iFlag2]:=E(6);
      Add(ListEquaGold, TheEqua);
      TheEqua:=ListWithIdenticalEntries(Length(PLE.ListFlags1), 0);
      TheEqua[iFlag2]:=1;
      TheEqua[iFlag1]:=E(6);
      Add(ListEquaGold, TheEqua);
    od;
    Append(ListEquaGold, ListEquationsBasic);
    TheVector:=NullspaceMat(TransposedMat(ListEquaGold));
#    Print("TheVector=", TheVector, "\n");
    if Length(TheVector)=1 then
      return TheVector[1];
    else
      return ListWithIdenticalEntries(Length(PLE.ListFlags1), 0);
    fi;
  end;


  TheGoldbergParameterVectorSecond:=function()
    local TheVector, iFlag, iFace, ListCorrespondingFace, Setted, ListStatus, iFlag1, iFlag2, iFlag3, pos1, pos2, pos3, eEdge, fEdge, IsFinished, jFlag;
    TheVector:=[];
    ListCorrespondingFace:=[];
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      TheVector[iFlag]:="unset";
      iFace:=Position(FaceSet, PLE.ListFlags1[iFlag][3]);
      ListCorrespondingFace[iFlag]:=iFace;
    od;
    ListStatus:=ListWithIdenticalEntries(Length(FaceSet), 0);
    ListStatus[1]:=1;
    Setted:=false;
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      if ListCorrespondingFace[iFlag]=1 and Setted=false then
        pos1:=PLE.ListCorrespondingDE[iFlag];
        pos2:=OnPoints(OnPoints(pos1, NEXT), INVERS);
        pos3:=OnPoints(OnPoints(pos2, NEXT), INVERS);
        iFlag1:=Position(PLE.ListCorrespondingDE, pos1);
        iFlag2:=Position(PLE.ListCorrespondingDE, pos2);
        iFlag3:=Position(PLE.ListCorrespondingDE, pos3);
        TheVector[iFlag1]:=1;
        TheVector[iFlag2]:=E(6)^2;
        TheVector[iFlag3]:=E(6)^4;
        Setted:=true;
      fi;
    od;
    IsFinished:=false;
    while(IsFinished=false)
    do
      IsFinished:=true;
      for iFace in [1..Length(FaceSet)]
      do
        if ListStatus[iFace]=0 then
          IsFinished:=false;
          for jFace in [1..Length(FaceSet)]
          do
            eEdge:=Set([iFace, jFace]);
            if ListStatus[jFace]=1 and eEdge in TheSpann2 then
              ListStatus[iFace]:=1;
              fEdge:=ListEdgeOriented[Position(ListEdge, eEdge)];
              pos1:=Intersection(Set(fEdge), Set(FaceSet[iFace]))[1];
              jFlag:=Position(PLE.ListCorrespondingDE, Intersection(Set(fEdge), Set(FaceSet[jFace]))[1]);
              pos2:=OnPoints(OnPoints(pos1, NEXT), INVERS);
              pos3:=OnPoints(OnPoints(pos2, NEXT), INVERS);
              iFlag1:=Position(PLE.ListCorrespondingDE, pos1);
              iFlag2:=Position(PLE.ListCorrespondingDE, pos2);
              iFlag3:=Position(PLE.ListCorrespondingDE, pos3);
              TheVector[iFlag1]:=-TheVector[jFlag];
              TheVector[iFlag2]:=TheVector[iFlag1]*E(6)^2;
              TheVector[iFlag3]:=TheVector[iFlag2]*E(6)^2;
            fi;
          od;
        fi;
      od;
    od;
    return TheVector;
  end;


  O:=Orbits(SymGRP, [1..Length(PLE.ListFlags1)], OnPoints);
  ListMatched:=[];
  ListCase:=[];
  for iFace in [1..Length(FaceSet)]
  do
    ListM:=[];
    for u in FaceSet[iFace]
    do
      for iOrb in [1..Length(O)]
      do
        if Position(O[iOrb], u)<>fail then
          Add(ListM, iOrb);
        fi;
      od;
    od;
    Print("ListM=", ListM, "\n");
    Add(ListMatched, ListM);
    Sort(ListM);
    AddSet(ListCase, ShallowCopy(ListM));
  od;
  Print("ListCase=", ListCase, "\n");






  Print("Computing the Goldberg Vector\n");
  TheGoldbergVector:=TheGoldbergParameterVector();
  TheGoldbergVectorSecond:=TheGoldbergParameterVectorSecond();
  Print("Computation Goldberg Vector finished\n");

  # now going for the groups
  PowerOrder:=function(eElt)
    local fElt, ord;
    fElt:=();
    ord:=1;
    while(not(fElt*eElt=()))
    do
      fElt:=fElt*eElt;
      ord:=ord+1;
    od;
    return ord;
  end;
  ListSeto:=[];
  CreateListEqua:=function(eGen, ListMultiplier, TheCoeff)
    local SomeEquations, iFlag, jFlag, TheEqua;
    SomeEquations:=[];
    for iFlag in [1..Length(PLE.ListFlags1)]
    do
      TheEqua:=ListWithIdenticalEntries(Length(PLE.ListFlags1), 0);
      jFlag:=OnPoints(iFlag, eGen);
      if jFlag<>iFlag then
        TheEqua[iFlag]:=TheCoeff*ListMultiplier[iFlag];
        TheEqua[jFlag]:=-1;
        Add(SomeEquations, TheEqua);
      fi;
    od;
#    Print("SomeEquations=", SomeEquations, "\n");
    return SomeEquations;
  end;

  for iGen in [1..Length(ListGen)]
  do
    nb:=PowerOrder(ListGen[iGen]);
    Add(ListSeto, [0..5]);
#    if nb=6 then
#      Add(ListSeto, [0..5]);
#    elif nb=3 then
#      Add(ListSeto, [0,2,4]);
#    elif nb=2 then
#      Add(ListSeto, [0,3]);
#    else
#      Add(ListSeto, [0]);
#    fi;
  od;
  BSE:=BuildSetMultiple(ListSeto);
  Print("dim=", Length(NullspaceMat(TransposedMat(ListEquationsBasic))), "\n");

  Print("TheGoldbergVector1=", TheGoldbergVector, "\n");
  Print("TheGoldbergVector2=", TheGoldbergVectorSecond, "\n");
  Print("Rank=", RankMat([TheGoldbergVector, TheGoldbergVectorSecond]), "\n");


  for eCase in BSE
  do
    EquaSet:=ShallowCopy(ListEquationsBasic);
    for iGen in [1..Length(ListGen)]
    do
      Append(EquaSet, CreateListEqua(ListGen[iGen], ListListMultiplier[iGen], E(6)^(eCase[iGen])));
    od;
    NULLS:=NullspaceMat(TransposedMat(EquaSet));
    if Length(NULLS)<>0 then
      IsGoldbergIn:=true;
      for u in EquaSet
      do
        if u*TheGoldbergVector<>0 then
          IsGoldbergIn:=false;
        fi;
      od;
      Print("eCase=", eCase, "\n");
      Print("number parameter=", Length(NULLS), "\n");
      Print("GoldbergVectorIn=", IsGoldbergIn, "\n");
    fi;
  od;
  return EquaSet;
end;



#
#
# if PL is a torus, then we build a k times
# bigger one with the same structure and k^2 of vertices, edges, 
# faces.
KuplingTorusMap:=function(PL, TheMult)
  local nbVert, ListEdges, eVert, fVert, nbEdge, MatrixEdge2, eEdge, TheNSPint, TheSign, IsFinished, pos, posEdge, iEdge, ListDone, TheBeginVert, ListEdgeExpression, TheSpanningTree, TheTotalBasis, TheHomologyBasis, DimZspace, TheFaceImageRed, TheFaceImageBasis, eDE, TheLine, eFace, MatrixEdge2Vert, MatrixFace2Edge, eLine, TheHomologyBasisRed, GRA, NewPL, ListAdj, eNewVert, fNewVert, iNewVert, jNewVert, NewListVert, eNewVectRed, ListEdgeVect, nbNewVert, eVect, eCycle, eSol, eNewVect, nbAdj, iAdj;
  nbVert:=Length(PL);
  ListEdges:=__EdgeSet(PL);
  ListEdgesDE:=List(ListEdges, x->x[1]);
  ListEdgesDErev:=List(ListEdges, x->x[2]);
  nbEdge:=Length(ListEdges);
  MatrixEdge2Vert:=[];
  for iEdge in [1..nbEdge]
  do
    fVert:=ListEdgesDE[iEdge][1];
    eVert:=ListEdgesDErev[iEdge][1];
    TheLine:=ListWithIdenticalEntries(nbVert, 0);
    TheLine[fVert]:=1;
    TheLine[eVert]:=-1;
    Add(MatrixEdge2Vert, TheLine);
  od;
  TheNSPint:=NullspaceIntMat(MatrixEdge2Vert);
  MatrixFace2Edge:=[];
  for eFace in __FaceSet(PL)
  do
    TheLine:=ListWithIdenticalEntries(nbEdge, 0);
    for eDE in eFace
    do
      pos:=Position(ListEdgesDE, eDE);
      if pos<>fail then
        TheSign:=1;
      else
        TheSign:=-1;
        pos:=Position(ListEdgesDErev, eDE);
      fi; 
      pos:=Position(ListEdges, eEdge);
      TheLine[pos]:=TheLine[pos]+TheSign;
    od;
    Add(MatrixFace2Edge, TheLine);
  od;
  DimZspace:=Length(TheNSPint);
  TheFaceImageBasis:=GetZbasis(MatrixFace2Edge);
  TheFaceImageRed:=List(TheFaceImageBasis, x->SolutionMat(TheNSPint, x));
  TheHomologyBasisRed:=SubspaceCompletion(TheFaceImageRed, DimZspace);
  TheHomologyBasis:=[];
  for eLine in TheHomologyBasisRed
  do
    Add(TheHomologyBasis, eLine*TheNSPint);
  od;
  TheTotalBasis:=Concatenation(TheHomologyBasis, TheFaceImageBasis);
  GRA:=PlanGraphToGRAPE(PL);
  TheBeginVert:=1;
  TheSpanningTree:=SpanningTreeGraph(GRA, TheBeginVert);
  ListEdgeExpression:=NullMat(nbVert, nbEdge);
  ListDone:=ListWithIdenticalEntries(nbVert, 0);
  ListDone[TheBeginVert]:=1;
  while(true)
  do
    IsFinished:=true;
    for eVert in [1..nbVert]
    do
      if ListDone[eVert]=1 then
        nbAdj:=Length(PL[eVert]);
        for iAdj in [1..nbAdj]
        do
          eDE:=[eVert, iAdj];
          pos:=Position(ListEdgesDE, eDE);
          if pos<>fail then
            TheSign:=1;
          else
            TheSign:=-1;
            pos:=Position(ListEdgesDErev, eDE);
          fi;
          fVert:=PL[eVert][iAdj];
          eEdge:=Set([eVert, fVert]);
          if ListDone[fVert]=0 and Position(TheSpanningTree, eEdge)<>fail then
            IsFinished:=false;
            ListDone[fVert]:=1;
            for iEdge in [1..nbEdge]
            do
              ListEdgeExpression[fVert][iEdge]:=ListEdgeExpression[eVert][iEdge];
            od;
            ListEdgeExpression[fVert][pos]:=ListEdgeExpression[fVert][pos]+TheSign;
          fi;
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  ListEdgeVect:=[];
  for iEdge in [1..nbEdge]
  do
    fVert:=ListEdgesDE[iEdge][1];
    eVert:=ListEdgesDErev[iEdge][1];
    eVect:=ListWithIdenticalEntries(nbEdge, 0);
    eVect[iEdge]:=1;
    eCycle:=eVect - ListEdgeExpression[fVert] + ListEdgeExpression[eVert];
    eSol:=SolutionMat(TheTotalBasis, eCycle);
    Add(ListEdgeVect, eSol{[1,2]});
  od;
  NewListVert:=[];
  for eVert in [1..nbVert]
  do
    for eVect in BuildSet(2, [0..TheMult-1])
    do
      eNewVert:=rec(eVert:=eVert, eVect:=eVect);
      Add(NewListVert, eNewVert);
    od;
  od;
  nbNewVert:=Length(NewListVert);
  NewPL:=[];
  for iNewVert in [1..nbNewVert]
  do
    ListAdj:=[];
    eNewVert:=NewListVert[iNewVert];
    nbAdj:=Length(PL[eNewVert.eVert]);
    for iAdj in [1..nbAdj]
    do
      eDE:=[eNewVert.eVert, iAdj];
      pos:=Position(ListEdgesDE, eDE);
      if pos<>fail then
        TheSign:=1;
      else
        TheSign:=-1;
        pos:=Position(ListEdgesDErev, eDE);
      fi;
      fVert:=PL[eNewVert.eVert][iAdj];
      eNewVect:=eNewVert.eVect + TheSign*ListEdgeVect[pos];
      eNewVectRed:=eNewVect mod TheMult;
      fNewVert:=rec(eVert:=fVert, eVect:=eNewVectRed);
      jNewVert:=Position(NewListVert, fNewVert);
      Add(ListAdj, jNewVert);
    od;
    Add(NewPL, ListAdj);
  od;
  return NewPL;
end;


#
#
# we shink some faces of a plane graph to a vertex
# this is an operation reverse to truncation
# we assume the graph to be 3-valent.
ShrinkPlaneGraph:=function(PL, SomeFaces)
  local nbVert, NewPL, ListAdj, NewListVert, eNewVert, nbNewVert, eFace, fVert, eDE, fDE, fNewVert, fFace, iFace, ListDone, eVert, pos, iNewVert;
  nbVert:=Length(PL);
  ListDone:=ListWithIdenticalEntries(nbVert, 0);
  for iFace in [1..Length(SomeFaces)]
  do
    eFace:=SomeFaces[iFace];
    for eDE in eFace
    do
      ListDone[eDE[1]]:=iFace;
    od;
  od;
  NewListVert:=[];
  for eVert in [1..nbVert]
  do
    if ListDone[eVert]=0 then
      eNewVert:=rec(IsOldVert:=1, eVert:=eVert, eFace:="irrelevant");
      Add(NewListVert, eNewVert);
    fi;
  od;
  for eFace in SomeFaces
  do
    eNewVert:=rec(IsOldVert:=0, eVert:="irrelevant", eFace:=eFace);
    Add(NewListVert, eNewVert);
  od;
  nbNewVert:=Length(NewListVert);
  NewPL:=[];
  for iNewVert in [1..nbNewVert]
  do
    ListAdj:=[];
    eNewVert:=NewListVert[iNewVert];
    if eNewVert.IsOldVert=1 then
      for fVert in PL[eNewVert.eVert]
      do
        if ListDone[fVert]=0 then
          fNewVert:=rec(IsOldVert:=1, eVert:=fVert, eFace:="irrelevant");
        else
          iFace:=ListDone[fVert];
          fFace:=SomeFaces[iFace];
          fNewVert:=rec(IsOldVert:=0, eVert:="irrelevant", eFace:=fFace);
        fi;
        pos:=Position(NewListVert, fNewVert);
        Add(ListAdj, pos);
      od;
    else
      for eDE in eNewVert.eFace
      do
        fDE:=PrevDE(PL, eDE);
        fVert:=PL[fDE[1]][fDE[2]];
        if ListDone[fVert]=0 then
          fNewVert:=rec(IsOldVert:=1, eVert:=fVert, eFace:="irrelevant");
        else
          iFace:=ListDone[fVert];
          fFace:=SomeFaces[iFace];
          fNewVert:=rec(IsOldVert:=0, eVert:="irrelevant", eFace:=fFace);
        fi;
        pos:=Position(NewListVert, fNewVert);
        Add(ListAdj, pos);
      od;
    fi;
    Add(NewPL, ListAdj);
  od;
  return NewPL;
end;
