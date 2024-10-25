#
#
# families of special planar graphs
Prism:=function(n)
  local PlanGraph, i;
  PlanGraph:=[];
  for i in [1..n]
  do
    PlanGraph[i]:=[NextIdx(n,i),PrevIdx(n,i),i+n];
  od;
  for i in [1..n]
  do
    PlanGraph[i+n]:=[NextIdx(n,i)+n,i, PrevIdx(n,i)+n];
  od;
  return PlanGraph;
end;


AntiPrism:=function(n)
  local PlanGraph, i;
  PlanGraph:=[];
  for i in [1..n]
  do
    PlanGraph[i]:=[NextIdx(n,i), PrevIdx(n,i), PrevIdx(n,i)+n, i+n];
  od;
  for i in [1..n]
  do
    PlanGraph[i+n]:=[NextIdx(n,i)+n, NextIdx(n,i), i, PrevIdx(n,i)+n];
  od;
  return PlanGraph;
end;


SnubAntiprism:=function(n)
  local PL, i, iP, iN;
  PL:=[];
  for i in [1..n]
  do
    iP:=PrevIdx(n, i);
    iN:=NextIdx(n, i);
    PL[4*(i-1)+1]:=[4*(iP-1)+1, 4*(iN-1)+1, 4*(i -1)+2, 4*(iP-1)+3, 4*(iP-1)+2];
    PL[4*(i-1)+2]:=[4*(i -1)+1, 4*(iN-1)+1, 4*(i -1)+3, 4*(iP-1)+4, 4*(iP-1)+3];
    PL[4*(i-1)+3]:=[4*(i -1)+2, 4*(iN-1)+1, 4*(iN-1)+2, 4*(i -1)+4, 4*(iP-1)+4];
    PL[4*(i-1)+4]:=[4*(iP-1)+4, 4*(i -1)+3, 4*(iN-1)+2, 4*(iN-1)+3, 4*(iN-1)+4];
  od;
  return PL;
end;

SnubPrism:=function(n)
  local PL, i, iP, iN;
  PL:=[];
  for i in [1..n]
  do
    iP:=PrevIdx(n, i);
    iN:=NextIdx(n, i);
    PL[4*(i-1)+1]:=[4*(iP-1)+1, 4*(i -1)+2, 4*(iN-1)+1];
    PL[4*(i-1)+2]:=[4*(i -1)+1, 4*(iP-1)+3, 4*(i -1)+3];
    PL[4*(i-1)+3]:=[4*(i -1)+2, 4*(i -1)+4, 4*(iN-1)+2];
    PL[4*(i-1)+4]:=[4*(iP-1)+4, 4*(iN-1)+4, 4*(i -1)+3];
  od;
  return PL;
end;


InfiniteSeries_b2_5valent:=function(n)
  local PL, i, iP, iN;
  PL:=[];
  for i in [1..n]
  do
    iP:=PrevIdx(n, i);
    iN:=NextIdx(n, i);
    PL[12*(i-1) + 1]:=[12*(i-1) + 5, 12*(iP-1)+11, 12*(iP-1) + 10, 12*(i-1)+2, 12*(i-1) + 3];
    PL[12*(i-1) + 2]:=[12*(i-1) + 1, 12*(iP-1)+10, 12*(iP-1) + 12, 12*(i-1)+6, 12*(i-1) + 3];
    PL[12*(i-1) + 3]:=[12*(i-1) + 1 , 12*(i-1) + 2 , 12*(i-1) + 6 , 12*(i-1) + 4 , 12*(i-1) + 5];
    PL[12*(i-1) + 4]:=[12*(i-1) + 3 , 12*(i-1) + 6 , 12*(i-1) + 8 , 12*(i-1) + 7 , 12*(i-1) + 5];
    PL[12*(i-1) + 5]:=[12*(i-1) + 1 , 12*(i-1) + 3 , 12*(i-1) + 4 , 12*(i-1) + 7 , 12*(i-1) + 11];
    PL[12*(i-1) + 6]:=[12*(i-1) + 12 , 12*(i-1) + 8 , 12*(i-1) + 4 , 12*(i-1) + 3 , 12*(i-1) + 2];
    PL[12*(i-1) + 7]:=[12*(i-1) + 4 , 12*(i-1) +  8, 12*(i-1) +  9, 12*(i-1) +  11, 12*(i-1) + 5];
    PL[12*(i-1) + 8]:=[12*(i-1) + 4 , 12*(i-1) +  6, 12*(i-1) +  12, 12*(i-1) +  9, 12*(i-1) + 7];
    PL[12*(i-1) + 9]:=[12*(i-1) + 7 , 12*(i-1) +  8, 12*(i-1) +  12, 12*(i-1) +  10, 12*(i-1) + 11];
    PL[12*(i-1) +10]:=[12*(i-1) + 11 , 12*(i-1) +  9, 12*(i-1) +  12, 12*(iN-1) + 2 , 12*(iN-1) + 1];
    PL[12*(i-1) +11]:=[12*(i-1) +  5, 12*(i-1) +  7, 12*(i-1) +  9, 12*(i-1) +  10, 12*(iN-1) + 1];
    PL[12*(i-1) +12]:=[12*(i-1) +  10, 12*(i-1) +  9, 12*(i-1) +  8, 12*(i-1) +  6, 12*(iN-1) + 2];
  od;
  return PL;
end;





Foil:=function(m)
  local iVert, PlanGraphNew, iPrev, iNext;
  PlanGraphNew:=[];
  for iVert in [1..m]
  do
    iPrev:=PrevIdx(m, iVert);
    iNext:=NextIdx(m, iVert);
    PlanGraphNew[iVert]:=[iPrev, iPrev, iNext, iNext];
  od;
  return PlanGraphNew;
end;



Mbundle:=function(m)
  local NewPlanGraph, i, Ladj, PlanGraphOriented;
  NewPlanGraph:=[];
  for i in [1..m]
  do
    Ladj:=[PrevIdx(m, i), NextIdx(m, i)];
    Add(NewPlanGraph, Ladj);
  od;
  PlanGraphOriented:=PlanGraphToPlanGraphOriented(NewPlanGraph);
  return DualGraphOriented(PlanGraphOriented);
end;

# Below the torus has one vertex, 3 edges and 2 triangular faces.
# 
PlanGraphOrientedTorus:=function()
  local INVERS, NEXT;
  INVERS:=(1,4)(2,5)(3,6);
  NEXT:=(1,2,3,4,5,6);
  return rec(invers:=INVERS, next:=NEXT, nbP:=6);
end;



SpecialFamily4hedrite:=function(n)
  local ListDE, iVert, i, eListNext, eListInvers, iDE, eDE, eNextDE, pos, idx, eInvDE;
  ListDE:=[];
  for iVert in [1..n]
  do
    for i in [1..4]
    do
      Add(ListDE, [iVert, i]);
    od;
  od;
  for iVert in [n+1..2*n]
  do
    for i in [1..4]
    do
      Add(ListDE, [iVert, i]);
    od;
  od;
  eListNext:=[];
  eListInvers:=[];
  for iDE in [1..Length(ListDE)]
  do
    eDE:=ListDE[iDE];
    eNextDE:=[eDE[1], NextIdx(4, eDE[2])];
    pos:=Position(ListDE, eNextDE);
    Add(eListNext, pos);
    iVert:=eDE[1];
    idx:=eDE[2];
    if iVert<=n then
      if iVert=1 and idx=1 then
        eInvDE:=[n+1, 1];
      elif iVert=n and idx=3 then
        eInvDE:=[2*n, 3];
      elif idx=2 then
        eInvDE:=[iVert+n, 4];
      elif idx=4 then
        eInvDE:=[iVert+n, 2];
      elif idx=1 then
        eInvDE:=[iVert-1, 3];
      elif idx=3 then
        eInvDE:=[iVert+1, 1];
      else
        Print("Please debug 1\n");
        Print(NullMat(5));
      fi;
    else
      if iVert=n+1 and idx=1 then
        eInvDE:=[1, 1];
      elif iVert=2*n and idx=3 then
        eInvDE:=[n, 3];
      elif idx=2 then
        eInvDE:=[iVert-n, 4];
      elif idx=4 then
        eInvDE:=[iVert-n, 2];
      elif idx=1 then
        eInvDE:=[iVert-1, 3];
      elif idx=3 then
        eInvDE:=[iVert+1, 1];
      else
        Print("Please debug 1\n");
        Print(NullMat(5));
      fi;
    fi;
    pos:=Position(ListDE, eInvDE);
    Add(eListInvers, pos);
  od;
  return rec(invers:=PermList(eListInvers), next:=PermList(eListNext), nbP:=Length(ListDE));
end;




FamilyIin:=function(i,n)
  local PlanGraph, kL;
  if not(i in [4,5,6]) then
    Print("i must be in [4,5,6]\n");
    return false;
  fi;
  PlanGraph:=[];
  for kL in [1..n+1]
  do
    if kL=1 then
      if i=6 then
        PlanGraph[1]:=[2,2,3,4];
        PlanGraph[2]:=[1,1,4,3];
      elif i=5 then
        PlanGraph[1]:=[2*(n+1)+1,2*(n+1)+1,3,4];
        PlanGraph[2]:=[2*(n+1)+1,2*(n+1)+1,4,3];
      else
        PlanGraph[1]:=[2*(n+1)+1,2*(n+1)+1,3,4];
        PlanGraph[2]:=[2*(n+1)+1,2*(n+1)+1,4,3];
      fi;
    elif kL=n+1 then
      if i=6 then
        PlanGraph[2*(n+1)-1]:=[2*(n+1)-3,2*(n+1)-2,2*(n+1),2*(n+1)];
        PlanGraph[2*(n+1)]:=[2*(n+1)-2, 2*(n+1)-3, 2*(n+1)-1,2*(n+1)-1];
      elif i=5 then
        PlanGraph[2*(n+1)-1]:=[2*(n+1)-3,2*(n+1)-2,2*(n+1),2*(n+1)];
        PlanGraph[2*(n+1)]:=[2*(n+1)-2, 2*(n+1)-3, 2*(n+1)-1,2*(n+1)-1];
      else
        PlanGraph[2*(n+1)-1]:=[2*(n+1)-3,2*(n+1)-2,2*(n+1)+2,2*(n+1)+2];
        PlanGraph[2*(n+1)]:=[2*(n+1)-2, 2*(n+1)-3, 2*(n+1)+2,2*(n+1)+2];
      fi;
    else
      PlanGraph[2*kL-1]:=[2*kL-3, 2*kL-2, 2*kL+1, 2*kL+2];
      PlanGraph[2*kL]:=[2*kL-2, 2*kL-3, 2*kL+2, 2*kL+1];
    fi;
  od;
  if i=5 then
    PlanGraph[2*(n+1)+1]:=[1,1,2,2];
  elif i=4 then
    PlanGraph[2*(n+1)+1]:=[1,1,2,2];
    PlanGraph[2*(n+1)+2]:=[2*(n+1), 2*(n+1), 2*(n+1)-1, 2*(n+1)-1];
  fi;
  return PlanGraph;
end;


#
#
# does not work due to failures in the planning of PlanGraph
# (multiple edges not handled correctly).
InflationFundamental4hedrite:=function(n)
  local PlanGraph, i;
  PlanGraph:=[];
  for i in [1..n]
  do
    if i=1 then
      PlanGraph[2*i]:=[1,1,1,4];
    elif i=n then
      PlanGraph[2*i]:=[2*i-1,2*(i-1),2*i-1,2*i-1];
    else
      PlanGraph[2*i]:=[2*i-1,2*(i-1),2*i-1,2*i+2];
    fi;
  od;
  for i in [1..n]
  do
    if i=1 then
      PlanGraph[2*i-1]:=[2,2,2,3];
    elif i=n then
      PlanGraph[2*i-1]:=[2*i,2*i-3,2*i,2*i];
    else
      PlanGraph[2*i-1]:=[2*i,2*i-3,2*i,2*i+1];
    fi;
  od;
  return PlanGraph;
end;





IsArchimedean:=function(PlanGraph)
  local Gra, GRP, O;
  Gra:=PlanGraphToGRAPE(PlanGraph);
  GRP:=AutGroupGraph(Gra);
  O:=Orbit(GRP, 1, OnPoints);
  if Length(O)=Length(PlanGraph) then
    return true;
  else
    return false;
  fi;
end;



ArchimedeanPolyhedra:=function(StringName)
  local ListNames, NameGraph;
  ListNames:=[];

  #Tetrahedron
  NameGraph:="Tetrahedron";
  if StringName=NameGraph then
    return [[2,3,4],[1,4,3],[1,2,4],[1,3,2]];
  fi;
  Add(ListNames, NameGraph);

  # cube
  NameGraph:="Cube";
  if StringName=NameGraph then
    return [[2,3,4],[1,5,6],[1,6,7],[1,7,5],[2,4,8],[2,8,3],[3,8,4],[5,7,6]];
  fi;
  Add(ListNames, NameGraph);

  # dodecahedron
  NameGraph:="Dodecahedron";
  if StringName=NameGraph then
    return [[4,2,7],[9,1,3],[2,5,11],[6,5,1],[3,4,13],[14,4,8],[8,1,10],[6,7,16],[12,10,2],[7,9,17],[12,3,15],[18,9,11],[15,5,14],[19,13,6],[11,13,20],[19,8,17],[16,10,18],[20,17,12],[20,14,16],[15,19,18]];
  fi;
  Add(ListNames, NameGraph);

  # cuboctahedron
  NameGraph:="Cuboctahedron";
  if StringName=NameGraph then
    return MedialGraph(ArchimedeanPolyhedra("Cube")).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  # icosidodecahedron
  NameGraph:="Icosidodecahedron";
  if StringName=NameGraph then
    return MedialGraph(ArchimedeanPolyhedra("Dodecahedron")).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  # truncated tetrahedron
  NameGraph:="TruncatedTetrahedron";
  if StringName=NameGraph then
    return TruncatedGraph(ArchimedeanPolyhedra("Tetrahedron"));
  fi;
  Add(ListNames, NameGraph);

  # octahedron
  NameGraph:="Octahedron";
  if StringName=NameGraph then
    return DualGraph(ArchimedeanPolyhedra("Cube")).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  # truncated octahedron
  NameGraph:="TruncatedOctahedron";
  if StringName=NameGraph then
    return TruncatedGraph(ArchimedeanPolyhedra("Octahedron"));
  fi;
  Add(ListNames, NameGraph);

  # icosahedron
  NameGraph:="Icosahedron";
  if StringName=NameGraph then
    return DualGraph(ArchimedeanPolyhedra("Dodecahedron")).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  # truncated cube
  NameGraph:="TruncatedCube";
  if StringName=NameGraph then
    return TruncatedGraph(ArchimedeanPolyhedra("Cube"));
  fi;
  Add(ListNames, NameGraph);

  # truncated icosahedron
  NameGraph:="TruncatedIcosahedron";
  if StringName=NameGraph then
    return TruncatedGraph(ArchimedeanPolyhedra("Icosahedron"));
  fi;
  Add(ListNames, NameGraph);

  # truncated dodecahedron
  NameGraph:="TruncatedDodecahedron";
  if StringName=NameGraph then
    return TruncatedGraph(ArchimedeanPolyhedra("Dodecahedron"));
  fi;
  Add(ListNames, NameGraph);

  # rhombicuboctahedron
  NameGraph:="RhombiCuboctahedron";
  if StringName=NameGraph then
    return MedialGraph(ArchimedeanPolyhedra("Cuboctahedron")).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  # rhombicosidodecahedron
  NameGraph:="Rhombicosidodecahedron";
  if StringName=NameGraph then
    return MedialGraph(ArchimedeanPolyhedra("Icosidodecahedron")).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  # truncated cuboctahedron
  NameGraph:="TruncatedCuboctahedron";
  if StringName=NameGraph then
    return TruncatedGraph(ArchimedeanPolyhedra("Cuboctahedron"));
  fi;
  Add(ListNames, NameGraph);

  # truncated icosidodecahedron
  NameGraph:="TruncatedIcosidodecahedron";
  if StringName=NameGraph then
    return TruncatedGraph(ArchimedeanPolyhedra("Icosidodecahedron"));
  fi;
  Add(ListNames, NameGraph);

  # snub cube
  NameGraph:="SnubCube";
  if StringName=NameGraph then
    return Snub(ArchimedeanPolyhedra("Cube")).RightIsomer;
  fi;
  Add(ListNames, NameGraph);

  # snub dodecahedron
  NameGraph:="SnubDodecahedron";
  if StringName=NameGraph then
    return Snub(ArchimedeanPolyhedra("Dodecahedron")).RightIsomer;
  fi;
  Add(ListNames, NameGraph);

  # icosahedron
  NameGraph:="RhombicDodecahedron";
  if StringName=NameGraph then
    return DualGraph(ArchimedeanPolyhedra("Cuboctahedron")).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="TwistedRhombicuboctahedron";
  if StringName=NameGraph then
    return [[4,5,13,2],[1,14,12,3],[2,12,10,4],[3,7,5,1],[4,6,15,1],[7,8,16,5],[4,10,8,6],[7,9,17,6],[10,11,18,8],[7,3,11,9],[10,12,19,9],[3,2,20,11],[1,15,21,14],[13,21,20,2],[5,16,22,13],[6,17,22,15],[8,18,23,16],[9,19,23,17],[11,20,24,18],[12,14,24,19],[13,22,24,14],[15,16,23,21],[17,18,24,22],[19,20,21,23]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="SmallStellatedDodecahedron";
  if StringName=NameGraph then
    return ShiftGraph(ArchimedeanPolyhedra("Icosahedron"), 2);
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="GreatDodecahedron";
  if StringName=NameGraph then
    return DualGraph(ArchimedeanPolyhedra("SmallStellatedDodecahedron")).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  if StringName="List" then
    return ListNames;
  fi;
  return fail;
end;







Deltahedra:=function(StringName)
  local ListNames, PlanGraph, NameGraph;
  ListNames:=[];


  #Prism5
  NameGraph:="DeltahedraVII";
  if StringName=NameGraph then
    return Prism(5);
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="DeltahedraVIII";
  if StringName=NameGraph then
    PlanGraph:=[[2,3,4,5,6],[1,6,7,3],[1,2,7,8,4],[1,3,8,5],[1,4,8,6],[1,5,8,7,2],[2,6,8,3],[3,7,6,5,4]];
    return DualGraph(PlanGraph).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="DeltahedraIX";
  if StringName=NameGraph then
    PlanGraph:=[[2,3,4,5],[1,5,8,9,3],[1,2,9,7,4],[1,3,7,6,5],[1,4,6,8,2],[4,7,9,8,5],[3,9,6,4],[2,5,6,9],[2,8,6,7,3]];
    return DualGraph(PlanGraph).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="DeltahedraX";
  if StringName=NameGraph then
    PlanGraph:=[[2,3,4,5],[1,5,8,10,3],[1,2,10,7,4],[1,3,7,6,5],[1,4,6,8,2],[4,7,9,8,5],[3,10,9,6,4],[2,5,6,9,10],[6,7,10,8],[2,8,9,7,3]];
    return DualGraph(PlanGraph).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="DurerTruncatedOctahedron";
  if StringName=NameGraph then
    PlanGraph:=[[2,3,4],[1,4,6,7,3],[1,2,7,5,4],[1,3,5,6,2],[3,7,8,6,4],[2,4,5,8,7],[2,6,8,5,3],[5,7,6]];
    return DualGraph(PlanGraph).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  if StringName="List" then
    return ListNames;
  fi;
  return fail;
end;









JohnsonSolid:=function(StringName)
  local ListNames, PlanGraph, NameGraph;
  ListNames:=[];

  #
  NameGraph:="Square pyramid";
  if StringName=NameGraph then
    return [[4,5,2],[1,5,3],[2,5,4],[3,5,1],[1,4,3,2]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Pentagonal pyramid";
  if StringName=NameGraph then
    return [[5,6,2],[1,6,3],[2,6,4],[3,6,5],[4,6,1],[1,5,4,3,2]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Triangular cupola";
  if StringName=NameGraph then
    return [[6,7,2],[1,9,3],[2,9,4],[3,8,5],[4,8,6],[5,7,1],[9,1,6,8],[7,5,4,9],[8,3,2,7]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Square cupola";
  if StringName=NameGraph then
    return [[8,9,2],[1,12,3],[2,12,4],[3,11,5],[4,11,6],[5,10,7],[6,10,8],[7,9,1],[12,1,8,10],[9,7,6,11],[10,5,4,12],[11,3,2,9]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Pentagonal cupola";
  if StringName=NameGraph then
    return [[10,11,2],[1,15,3],[2,15,4],[3,14,5],[4,14,6],[5,13,7],[6,13,8],[7,12,9],[8,12,10],[9,11,1],[15,1,10,12],[11,9,8,13],[12,7,6,14],[13,5,4,15],[14,3,2,11]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Pentagonal rotunda";
  if StringName=NameGraph then
    return [[10,20,2],[1,17,3],[2,17,4],[3,16,5],[4,16,6],[5,18,7],[6,18,8],[7,19,9],[8,19,10],[9,20,1],[15,17,20,12],[11,20,19,13],[12,19,18,14],[13,18,16,15],[14,16,17,11],[15,14,5,4],[3,2,11,15],[14,13,7,6],[13,12,9,8],[12,11,1,10]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated triangular pyramid";
  if StringName=NameGraph then
    return [[3,7,2],[1,4,3],[2,5,1],[2,7,6,5],[4,6,7,3],[4,7,5],[5,6,4,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated square pyramid";
  if StringName=NameGraph then
    return [[4,9,2],[1,5,3],[2,6,4],[3,8,1],[2,9,7,6],[5,7,8,3],[5,9,8,6],[6,7,9,4],[8,7,5,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal pyramid";
  if StringName=NameGraph then
    return [[5,10,2],[1,11,3],[2,6,4],[3,7,5],[4,9,1],[3,11,8,7],[6,8,9,4],[6,11,10,9,7],[7,8,10,5],[9,8,11,1],[10,8,6,2]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated square pyramid";
  if StringName=NameGraph then
    return [[3,9,5,4,2],[1,4,8,3],[2,8,7,9,1],[1,5,6,2],[1,9,7,6,4],[5,7,8,4],[5,9,3,8,6],[7,3,2,6],[3,7,5,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated pentagonal pyramid";
  if StringName=NameGraph then
    return [[3,11,5,4,2],[1,4,10,3],[2,10,9,11,1],[1,5,6,2],[1,11,7,6,4],[5,7,8,4],[5,11,9,8,6],[7,9,10,6],[7,11,3,10,8],[9,3,2,8],[3,9,7,5,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Triangular dipyramid";
  if StringName=NameGraph then
    return DualGraph(Prism(3)).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Pentagonal dipyramid";
  if StringName=NameGraph then
    return DualGraph(Prism(5)).PlanGraph;
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated triangular dipyramid";
  if StringName=NameGraph then
    return [[4,6,7,2],[1,8,5,3],[2,5,8,4],[3,7,6,1],[2,8,3],[4,7,1],[8,1,6,4],[3,5,2,7]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated square dipyramid";
  if StringName=NameGraph then
    return [[4,9,5,2],[1,5,7,3],[2,8,6,4],[3,6,10,1],[1,9,7,2],[3,8,10,4],[2,5,9,8],[7,10,6,3],[7,5,1,10],[9,4,6,8]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal dipyramid";
  if StringName=NameGraph then
    return [[4,11,5,2],[1,5,8,3],[2,7,6,4],[3,6,12,1],[1,11,10,8,2],[3,7,9,12,4],[8,9,6,3],[2,5,10,7],[10,12,6,7],[8,5,11,9],[10,5,1,12],[11,4,6,9]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated square dipyramid";
  if StringName=NameGraph then
    return [[3,9,5,4,2],[1,4,10,8,3],[2,8,7,9,1],[1,5,6,10,2],[1,9,7,6,4],[5,7,8,10,4],[5,9,3,8,6],[7,3,2,10,6],[3,7,5,1],[4,6,8,2]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated triangular cupola";
  if StringName=NameGraph then
    return [[6,10,2],[1,11,3],[2,12,4],[3,7,5],[4,8,6],[5,9,1],[4,12,13,8],[7,15,9,5],[8,15,10,6],[9,14,11,1],[10,14,12,2],[11,13,7,3],[15,7,12,14],[13,11,10,15],[14,9,8,13]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated square cupola";
  if StringName=NameGraph then
    return [[8,9,2],[1,10,3],[2,11,4],[3,12,5],[4,13,6],[5,14,7],[6,15,8],[7,16,1],[1,16,17,10],[9,17,11,2],[10,20,12,3],[11,20,13,4],[12,19,14,5],[13,19,15,6],[14,18,16,7],[15,18,9,8],[20,10,9,18],[17,16,15,19],[18,14,13,20],[19,12,11,17]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal cupola";
  if StringName=NameGraph then
    return [[10,14,2],[1,15,3],[2,16,4],[3,17,5],[4,18,6],[5,19,7],[6,20,8],[7,11,9],[8,12,10],[9,13,1],[8,20,21,12],[11,25,13,9],[12,25,14,10],[13,24,15,1],[14,24,16,2],[15,23,17,3],[16,23,18,4],[17,22,19,5],[18,22,20,6],[19,21,11,7],[25,11,20,22],[21,19,18,23],[22,17,16,24],[23,15,14,25],[24,13,12,21]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal rotunda";
  if StringName=NameGraph then
    return [[10,30,2],[1,19,3],[2,18,4],[3,20,5],[4,22,6],[5,23,7],[6,24,8],[7,26,9],[8,28,10],[9,29,1],[15,27,25,12],[11,25,21,13],[12,21,17,14],[13,17,16,15],[14,16,27,11],[19,30,15,14],[14,13,20,18],[17,20,3,19],[18,2,30,16],[17,22,4,18],[13,12,23,22],[21,23,5,20],[21,24,6,22],[25,26,7,23],[12,11,26,24],[25,28,8,24],[11,15,29,28],[27,29,9,26],[27,30,10,28],[16,19,1,29]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated triangular cupola";
  if StringName=NameGraph then
    return [[4,2,3,9],[3,1,5,6],[1,2,7,8],[1,9,15,10,5],[2,4,10,11,6],[2,5,11,12,7],[3,6,12,13,8],[3,7,13,14,9],[8,14,15,4,1],[5,4,15,11],[6,5,10,12],[7,6,11,13],[8,7,12,14],[9,8,13,15],[4,9,14,10]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated square cupola";
  if StringName=NameGraph then
    return [[5,2,4,12],[1,6,7,3],[2,8,9,4],[3,10,11,1],[1,12,20,13,6],[5,13,14,7,2],[2,6,14,15,8],[7,15,16,9,3],[3,8,16,17,10],[9,17,18,11,4],[4,10,18,19,12],[11,19,20,5,1],[5,20,14,6],[7,6,13,15],[8,7,14,16],[9,8,15,17],[10,9,16,18],[11,10,17,19],[12,11,18,20],[5,12,19,13]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated pentagonal cupola";
  if StringName=NameGraph then
    return [[6,7,2,5],[8,9,3,1],[10,11,4,2],[12,13,5,3],[14,15,1,4],[15,25,16,7,1],[1,6,16,17,8],[2,7,17,18,9],[2,8,18,19,10],[3,9,19,20,11],[3,10,20,21,12],[4,11,21,22,13],[4,12,22,23,14],[5,13,23,24,15],[5,14,24,25,6],[6,25,17,7],[7,16,18,8],[8,17,19,9],[9,18,20,10],[11,10,19,21],[12,11,20,22],[13,12,21,23],[14,13,22,24],[15,14,23,25],[6,15,24,16]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated pentagonal rotunda";
  if StringName=NameGraph then
    return [[6,2,5,10],[7,3,1,6],[8,4,2,7],[9,5,3,8],[10,1,4,9],[11,12,2,1],[13,14,3,2],[15,16,4,3],[17,18,5,4],[19,20,1,5],[20,30,21,12,6],[6,11,21,22,13],[7,12,22,23,14],[7,13,23,24,15],[8,14,24,25,16],[8,15,25,26,17],[9,16,26,27,18],[9,17,27,28,19],[10,18,28,29,20],[10,19,29,30,11],[11,30,22,12],[12,21,23,13],[13,22,24,14],[14,23,25,15],[16,15,24,26],[17,16,25,27],[18,17,26,28],[19,18,27,29],[20,19,28,30],[11,20,29,21]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyrobifastigium";
  if StringName=NameGraph then
    return [[4,2,3],[1,5,6],[4,1,6,8],[7,5,1,3],[6,2,4,7],[3,2,5,8],[5,4,8],[3,6,7]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Triangular orthobicupola";
  if StringName=NameGraph then
    return [[3,9,4,2],[1,5,6,3],[2,7,8,1],[1,9,10,5],[4,12,6,2],[5,12,7,2],[6,11,8,3],[7,11,9,3],[8,10,4,1],[12,4,9,11],[10,8,7,12],[11,6,5,10]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Square orthobicupola";
  if StringName=NameGraph then
    return [[4,10,11,2],[1,12,5,3],[2,6,7,4],[3,8,9,1],[2,12,16,6],[5,15,7,3],[6,15,8,3],[7,14,9,4],[8,14,10,4],[9,13,11,1],[10,13,12,1],[11,16,5,2],[16,11,10,14],[13,9,8,15],[14,7,6,16],[15,5,12,13]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Square gyrobicupola";
  if StringName=NameGraph then
    return [[4,10,11,2],[1,12,6,3],[2,5,7,4],[3,8,9,1],[6,14,7,3],[2,12,14,5],[5,13,8,3],[7,13,9,4],[8,16,10,4],[9,16,11,1],[10,15,12,1],[11,15,6,2],[16,8,7,14],[13,5,6,15],[14,12,11,16],[15,10,9,13]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Pentagonal orthobicupola";
  if StringName=NameGraph then
    return [[5,11,12,2],[1,13,14,3],[2,15,6,4],[3,7,8,5],[4,9,10,1],[3,15,19,7],[6,18,8,4],[7,18,9,4],[8,17,10,5],[9,17,11,5],[10,16,12,1],[11,16,13,1],[12,20,14,2],[13,20,15,2],[14,19,6,3],[20,12,11,17],[16,10,9,18],[17,8,7,19],[18,6,15,20],[19,14,13,16]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Pentagonal gyrobicupola";
  if StringName=NameGraph then
    return [[5,15,7,2],[1,6,8,3],[2,9,10,4],[3,11,12,5],[4,13,14,1],[7,16,8,2],[1,15,16,6],[6,20,9,2],[8,20,10,3],[9,19,11,3],[10,19,12,4],[11,18,13,4],[12,18,14,5],[13,17,15,5],[14,17,7,1],[20,6,7,17],[16,15,14,18],[17,13,12,19],[18,11,10,20],[19,9,8,16]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Pentagonal orthocupolarotunda";
  if StringName=NameGraph then
    return [[5,13,14,2],[1,15,7,3],[2,6,8,4],[3,9,10,5],[4,11,12,1],[7,25,8,3],[2,15,25,6],[6,24,9,3],[8,24,10,4],[9,23,11,4],[10,23,12,5],[11,21,13,5],[12,21,14,1],[13,22,15,1],[14,22,7,2],[20,23,24,17],[16,24,25,18],[17,25,22,19],[18,22,21,20],[19,21,23,16],[13,12,20,19],[19,18,15,14],[11,10,16,20],[9,8,17,16],[6,7,18,17]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Pentagonal gyrocupolarotunda";
  if StringName=NameGraph then
    return [[5,13,14,2],[1,15,6,3],[2,7,8,4],[3,9,10,5],[4,11,12,1],[2,15,25,7],[6,24,8,3],[7,24,9,3],[8,23,10,4],[9,23,11,4],[10,22,12,5],[11,22,13,5],[12,21,14,1],[13,21,15,1],[14,25,6,2],[20,21,22,17],[16,22,23,18],[17,23,24,19],[18,24,25,20],[19,25,21,16],[16,20,14,13],[12,11,17,16],[10,9,18,17],[8,7,19,18],[6,15,20,19]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Pentagonal orthobirotunda";
  if StringName=NameGraph then
    return [[5,6,9,2],[1,9,12,3],[2,12,15,4],[3,15,18,5],[4,18,6,1],[1,5,20,7],[6,20,27,8],[7,26,10,9],[8,10,2,1],[8,26,11,9],[10,30,13,12],[11,13,3,2],[11,30,14,12],[13,29,16,15],[14,16,4,3],[14,29,17,15],[16,28,19,18],[17,19,5,4],[17,28,20,18],[19,27,7,6],[25,26,27,22],[21,27,28,23],[22,28,29,24],[23,29,30,25],[24,30,26,21],[21,25,10,8],[7,20,22,21],[19,17,23,22],[16,14,24,23],[13,11,25,24]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated triangular orthobicupola";
  if StringName=NameGraph then
    return [[3,9,4,2],[1,5,6,3],[2,7,8,1],[1,9,14,5],[4,13,6,2],[5,18,7,2],[6,17,8,3],[7,16,9,3],[8,15,4,1],[12,14,15,11],[10,16,17,12],[11,18,13,10],[12,18,5,14],[13,4,15,10],[14,9,16,10],[15,8,17,11],[16,7,18,11],[17,6,13,12]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated triangular gyrobicupola";
  if StringName=NameGraph then
    return [[3,9,4,2],[1,5,6,3],[2,7,8,1],[1,9,15,5],[4,14,6,2],[5,13,7,2],[6,18,8,3],[7,17,9,3],[8,16,4,1],[12,18,13,11],[10,14,15,12],[11,16,17,10],[10,18,6,14],[13,5,15,11],[14,4,16,11],[15,9,17,12],[16,8,18,12],[17,7,13,10]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated square gyrobicupola";
  if StringName=NameGraph then
    return ArchimedeanPolyhedra("TwistedRhombicuboctahedron");
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal orthobicupola";
  if StringName=NameGraph then
    return [[5,13,14,2],[1,15,6,3],[2,7,8,4],[3,9,10,5],[4,11,12,1],[2,15,21,7],[6,22,8,3],[7,30,9,3],[8,29,10,4],[9,28,11,4],[10,27,12,5],[11,26,13,5],[12,25,14,1],[13,24,15,1],[14,23,6,2],[20,26,27,17],[16,28,29,18],[17,30,22,19],[18,21,23,20],[19,24,25,16],[22,6,23,19],[18,30,7,21],[21,15,24,19],[23,14,25,20],[24,13,26,20],[25,12,27,16],[26,11,28,16],[27,10,29,17],[28,9,30,17],[29,8,22,18]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal gyrobicupola";
  if StringName=NameGraph then
    return [[5,15,7,2],[1,6,8,3],[2,9,10,4],[3,11,12,5],[4,13,14,1],[7,22,8,2],[1,15,23,6],[6,21,9,2],[8,30,10,3],[9,29,11,3],[10,28,12,4],[11,27,13,4],[12,26,14,5],[13,25,15,5],[14,24,7,1],[20,22,23,17],[16,24,25,18],[17,26,27,19],[18,28,29,20],[19,30,21,16],[20,30,8,22],[21,6,23,16],[22,7,24,16],[23,15,25,17],[24,14,26,17],[25,13,27,18],[26,12,28,18],[27,11,29,19],[28,10,30,19],[29,9,21,20]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal orthocupolarotunda";
  if StringName=NameGraph then
    return [[5,13,14,2],[1,15,7,3],[2,6,8,4],[3,9,10,5],[4,11,12,1],[7,22,8,3],[2,15,25,6],[6,21,9,3],[8,35,10,4],[9,34,11,4],[10,32,12,5],[11,31,13,5],[12,30,14,1],[13,28,15,1],[14,26,7,2],[20,24,23,17],[16,23,27,18],[17,27,29,19],[18,29,33,20],[19,33,24,16],[24,35,8,22],[21,6,25,23],[22,25,17,16],[16,20,35,21],[22,7,26,23],[25,15,28,27],[26,28,18,17],[26,14,30,27],[30,31,19,18],[28,13,31,29],[30,12,32,29],[31,11,34,33],[32,34,20,19],[32,10,35,33],[34,9,21,24]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal gyrocupolarotunda";
  if StringName=NameGraph then
    return [[5,13,14,2],[1,15,7,3],[2,6,8,4],[3,9,10,5],[4,11,12,1],[7,22,8,3],[2,15,23,6],[6,35,9,3],[8,34,10,4],[9,32,11,4],[10,31,12,5],[11,30,13,5],[12,28,14,1],[13,26,15,1],[14,25,7,2],[20,24,27,17],[16,27,29,18],[17,29,33,19],[18,33,21,20],[19,21,24,16],[20,19,35,22],[21,35,6,23],[22,7,25,24],[23,25,16,20],[23,15,26,24],[25,14,28,27],[26,28,17,16],[26,13,30,27],[30,31,18,17],[28,12,31,29],[30,11,32,29],[31,10,34,33],[32,34,19,18],[32,9,35,33],[34,8,22,21]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal orthobirotunda";
  if StringName=NameGraph then
    return [[5,6,9,2],[1,9,12,3],[2,12,15,4],[3,15,18,5],[4,18,6,1],[1,5,20,7],[6,20,26,8],[7,29,10,9],[8,10,2,1],[8,40,11,9],[10,39,13,12],[11,13,3,2],[11,37,14,12],[13,36,16,15],[14,16,4,3],[14,34,17,15],[16,33,19,18],[17,19,5,4],[17,32,20,18],[19,30,7,6],[25,28,27,22],[21,27,31,23],[22,31,35,24],[23,35,38,25],[24,38,28,21],[29,7,30,27],[26,30,22,21],[21,25,40,29],[28,40,8,26],[26,20,32,27],[32,33,23,22],[30,19,33,31],[32,17,34,31],[33,16,36,35],[34,36,24,23],[34,14,37,35],[36,13,39,38],[37,39,25,24],[37,11,40,38],[39,10,29,28]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Elongated pentagonal gyrobirotunda";
  if StringName=NameGraph then
    return [[5,6,9,2],[1,9,11,3],[2,11,15,4],[3,15,18,5],[4,18,6,1],[1,5,20,7],[6,20,30,8],[7,28,10,9],[8,10,2,1],[8,27,12,9],[12,13,3,2],[10,40,13,11],[12,39,14,11],[13,38,16,15],[14,16,4,3],[14,36,17,15],[16,34,19,18],[17,19,5,4],[17,33,20,18],[19,32,7,6],[25,26,29,22],[21,29,31,23],[22,31,35,24],[23,35,37,25],[24,37,26,21],[21,25,40,27],[26,40,10,28],[27,8,30,29],[28,30,22,21],[28,7,32,29],[32,33,23,22],[30,20,33,31],[32,19,34,31],[33,17,36,35],[34,36,24,23],[34,16,38,35],[38,39,25,24],[36,14,39,37],[38,13,40,37],[39,12,27,26]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated triangular bicupola";
  if StringName=NameGraph then
    return [[3,9,5,2],[1,4,6,3],[2,7,8,1],[5,14,13,6,2],[1,9,15,14,4],[4,13,18,7,2],[6,18,17,8,3],[7,17,16,9,3],[8,16,15,5,1],[12,14,15,11],[10,16,17,12],[11,18,13,10],[12,18,6,4,14],[13,4,5,15,10],[14,5,9,16,10],[15,9,8,17,11],[16,8,7,18,11],[17,7,6,13,12]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated square bicupola";
  if StringName=NameGraph then
    return [[4,12,6,2],[1,5,7,3],[2,8,9,4],[3,10,11,1],[6,17,18,7,2],[1,12,19,17,5],[5,18,24,8,2],[7,24,23,9,3],[8,23,22,10,3],[9,22,21,11,4],[10,21,20,12,4],[11,20,19,6,1],[16,17,19,14],[13,20,21,15],[14,22,23,16],[15,24,18,13],[18,5,6,19,13],[16,24,7,5,17],[17,6,12,20,13],[19,12,11,21,14],[20,11,10,22,14],[21,10,9,23,15],[22,9,8,24,15],[23,8,7,18,16]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated pentagonal bicupola";
  if StringName=NameGraph then
    return [[5,15,7,2],[1,6,8,3],[2,9,10,4],[3,11,12,5],[4,13,14,1],[7,22,21,8,2],[1,15,23,22,6],[6,21,30,9,2],[8,30,29,10,3],[9,29,28,11,3],[10,28,27,12,4],[11,27,26,13,4],[12,26,25,14,5],[13,25,24,15,5],[14,24,23,7,1],[20,26,27,17],[16,28,29,18],[17,30,21,19],[18,22,23,20],[19,24,25,16],[18,30,8,6,22],[21,6,7,23,19],[22,7,15,24,19],[23,15,14,25,20],[24,14,13,26,20],[25,13,12,27,16],[26,12,11,28,16],[27,11,10,29,17],[28,10,9,30,17],[29,9,8,21,18]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated pentagonal cupolarotunda";
  if StringName=NameGraph then
    return [[5,15,7,2],[1,6,8,3],[2,9,10,4],[3,11,12,5],[4,13,14,1],[7,24,23,8,2],[1,15,25,24,6],[6,23,35,9,2],[8,35,34,10,3],[9,34,32,11,3],[10,32,31,12,4],[11,31,29,13,4],[12,29,28,14,5],[13,28,27,15,5],[14,27,25,7,1],[20,33,22,17],[16,22,21,18],[17,21,26,19],[18,26,30,20],[19,30,33,16],[24,25,18,17],[17,16,35,23],[22,35,8,6,24],[23,6,7,25,21],[24,7,15,27,21],[27,28,19,18],[25,15,14,28,26],[27,14,13,29,26],[28,13,12,31,30],[29,31,20,19],[29,12,11,32,30],[31,11,10,34,33],[32,34,16,20],[32,10,9,35,33],[34,9,8,23,22]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyroelongated pentagonal birotunda";
  if StringName=NameGraph then
    return [[5,6,9,2],[1,9,11,3],[2,11,15,4],[3,15,17,5],[4,17,6,1],[1,5,20,7],[6,20,30,29,8],[7,29,28,10,9],[8,10,2,1],[8,28,40,12,9],[12,13,3,2],[10,40,39,13,11],[12,39,37,14,11],[13,37,36,16,15],[14,16,4,3],[14,36,34,18,15],[18,19,5,4],[16,34,33,19,17],[18,33,31,20,17],[19,31,30,7,6],[25,35,38,22],[21,38,27,23],[22,27,26,24],[23,26,32,25],[24,32,35,21],[29,30,24,23],[23,22,40,28],[27,40,10,8,29],[28,8,7,30,26],[29,7,20,31,26],[30,20,19,33,32],[31,33,25,24],[31,19,18,34,32],[33,18,16,36,35],[34,36,21,25],[34,16,14,37,35],[36,14,13,39,38],[37,39,22,21],[37,13,12,40,38],[39,12,10,28,27]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Augmented triangular prism";
  if StringName=NameGraph then
    return [[4,7,5,2],[1,5,3],[2,6,4],[3,6,7,1],[2,1,7,6],[5,7,4,3],[6,5,1,4]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Biaugmented triangular prism";
  if StringName=NameGraph then
    return [[4,8,7,2],[1,7,6,3],[2,6,5,4],[3,5,8,1],[6,7,8,4,3],[3,2,7,5],[2,1,8,5,6],[5,7,1,4]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Triaugmented triangular prism";
  if StringName=NameGraph then
    return [[3,9,7,2],[1,7,4,5,3],[2,5,6,9,1],[2,7,8,6,5],[4,6,3,2],[5,4,8,9,3],[2,1,9,8,4],[7,9,6,4],[8,7,1,3,6]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Augmented pentagonal prism";
  if StringName=NameGraph then
    return [[5,11,6,2],[1,10,3],[2,9,4],[3,8,5],[4,7,11,1],[10,1,11,7],[6,11,5,8],[7,4,9],[8,3,10],[9,2,6],[5,7,6,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Biaugmented pentagonal prism";
  if StringName=NameGraph then
    return [[5,12,6,2],[1,10,3],[2,9,11,4],[3,11,8,5],[4,7,12,1],[10,1,12,7],[6,12,5,8],[7,4,11,9],[8,11,3,10],[9,2,6],[3,9,8,4],[5,7,6,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Augmented hexagonal prism";
  if StringName=NameGraph then
    return [[6,13,7,2],[1,12,3],[2,11,4],[3,10,5],[4,9,6],[5,8,13,1],[12,1,13,8],[7,13,6,9],[8,5,10],[9,4,11],[10,3,12],[11,2,7],[6,8,7,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Parabiaugmented hexagonal prism";
  if StringName=NameGraph then
    return [[6,14,7,2],[1,12,3],[2,11,13,4],[3,13,10,5],[4,9,6],[5,8,14,1],[12,1,14,8],[7,14,6,9],[8,5,10],[9,4,13,11],[10,13,3,12],[11,2,7],[3,11,10,4],[6,8,7,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Metabiaugmented hexagonal prism";
  if StringName=NameGraph then
    return [[6,14,7,2],[1,12,3],[2,11,4],[3,10,13,5],[4,13,9,6],[5,8,14,1],[12,1,14,8],[7,14,6,9],[8,5,13,10],[9,13,4,11],[10,3,12],[11,2,7],[4,10,9,5],[6,8,7,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Triaugmented hexagonal prism";
  if StringName=NameGraph then
    return [[6,15,7,2],[1,12,13,3],[2,13,11,4],[3,10,14,5],[4,14,9,6],[5,8,15,1],[12,1,15,8],[7,15,6,9],[8,5,14,10],[9,14,4,11],[10,3,13,12],[11,13,2,7],[2,12,11,3],[4,10,9,5],[6,8,7,1]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Augmented dodecahedron";
  if StringName=NameGraph then
    return [[5,11,2],[1,14,3],[2,7,4],[3,6,5],[4,10,1],[8,9,4],[3,15,8],[7,20,6],[6,19,21,10],[9,21,12,5],[12,13,1],[10,21,18,11],[11,16,14],[13,15,2],[14,17,7],[13,18,17],[16,20,15],[12,21,19,16],[20,18,21,9],[8,17,19],[18,12,10,9,19]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Parabiaugmented dodecahedron";
  if StringName=NameGraph then
    return [[5,11,2],[1,13,22,3],[2,22,7,4],[3,6,5],[4,10,1],[8,9,4],[3,22,19,8],[7,18,6],[6,17,21,10],[9,21,12,5],[12,14,1],[10,21,15,11],[14,19,22,2],[11,16,13],[12,21,17,16],[15,20,14],[18,15,21,9],[8,20,17],[7,22,13,20],[19,16,18],[15,12,10,9,17],[2,13,19,7,3]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Metabiaugmented dodecahedron";
  if StringName=NameGraph then
    return [[5,9,22,2],[1,22,8,3],[2,7,4],[3,12,5],[4,10,1],[8,20,7],[6,14,3],[2,22,19,6],[11,19,22,1],[5,13,21,11],[10,21,17,9],[4,14,13],[12,15,21,10],[7,16,12],[16,17,21,13],[14,20,15],[11,21,15,18],[17,20,19],[18,8,22,9],[18,16,6],[17,11,10,13,15],[1,9,19,8,2]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Triaugmented dodecahedron";
  if StringName=NameGraph then
    return [[5,9,22,2],[1,22,8,3],[2,7,4],[3,12,5],[4,10,1],[8,20,23,7],[6,23,14,3],[2,22,19,6],[11,19,22,1],[5,13,21,11],[10,21,17,9],[4,14,13],[12,15,21,10],[7,23,16,12],[16,17,21,13],[14,23,20,15],[11,21,15,18],[17,20,19],[18,8,22,9],[18,16,23,6],[17,11,10,13,15],[1,9,19,8,2],[16,14,7,6,20]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Metabidiminished icosahedron";
  if StringName=NameGraph then
    return [[5,10,9,2],[1,9,6,3],[2,6,4],[3,8,5],[4,8,10,1],[3,2,9,7],[6,9,10,8],[7,10,5,4],[10,7,6,2,1],[1,5,8,7,9]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Tridiminished icosahedron";
  if StringName=NameGraph then
    return [[5,6,2],[1,6,3],[2,8,4],[3,8,9,5],[4,9,1],[2,1,7],[6,9,8],[7,9,4,3],[8,7,5,4]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Augmented tridiminished icosahedron";
  if StringName=NameGraph then
    return [[2,3,4],[3,1,4,5],[1,2,6,4],[1,3,7,2],[8,2,9],[3,8,10],[4,10,9],[6,5,9,10],[5,7,10,8],[7,6,8,9]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Augmented truncated tetrahedron";
  if StringName=NameGraph then
    return [[4,11,5,2],[1,5,8,3],[2,8,15,4],[3,15,11,1],[1,10,9,2],[9,14,7],[6,14,8],[7,3,2],[5,10,6],[5,11,12,9],[1,4,12,10],[11,15,13,10],[12,15,14],[13,7,6],[12,4,3,13]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Augmented truncated cube";
  if StringName=NameGraph then
    return [[4,10,11,2],[1,12,5,3],[2,6,7,4],[3,8,9,1],[2,12,22,6],[5,22,7,3],[6,26,8,3],[7,26,9,4],[8,15,10,4],[9,15,11,1],[10,14,12,1],[11,14,5,2],[18,19,14],[13,12,11],[10,9,16],[15,28,17],[16,28,18],[17,19,13],[13,18,20],[19,23,21],[20,23,22],[21,6,5],[21,20,24],[23,27,25],[24,27,26],[25,8,7],[25,24,28],[27,17,16]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Biaugmented truncated cube";
  if StringName=NameGraph then
    return [[4,10,11,2],[1,12,5,3],[2,6,7,4],[3,8,9,1],[2,12,30,6],[5,30,7,3],[6,32,8,3],[7,32,9,4],[8,27,10,4],[9,27,11,1],[10,26,12,1],[11,26,5,2],[16,24,17,14],[13,18,19,15],[14,20,21,16],[15,22,23,13],[13,24,25,18],[17,25,19,14],[18,28,20,14],[19,28,21,15],[20,31,22,15],[21,31,23,16],[22,29,24,16],[23,29,17,13],[18,17,26],[25,12,11],[10,9,28],[27,20,19],[24,23,30],[29,6,5],[22,21,32],[31,8,7]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Augmented truncated dodecahedron";
  if StringName=NameGraph then
    return [[10,36,2],[1,36,3],[2,11,4],[3,11,5],[4,15,6],[5,15,7],[6,23,8],[7,23,9],[8,30,10],[9,30,1],[3,16,4],[18,54,64,13],[12,64,24,14],[13,24,15],[14,6,5],[11,19,17],[16,19,18],[17,54,12],[16,39,17],[25,59,21],[20,31,22],[21,31,23],[22,8,7],[14,13,63,25],[24,63,59,20],[31,57,27],[26,57,28],[27,37,29],[28,37,30],[29,10,9],[22,21,26],[37,55,33],[32,55,34],[33,40,35],[34,40,36],[35,2,1],[29,28,32],[40,52,39],[38,52,19],[35,34,38],[50,61,51,42],[41,51,43],[42,53,44],[43,53,45],[44,56,46],[45,56,47],[46,58,48],[47,58,49],[48,60,50],[49,60,61,41],[41,65,54,42],[39,38,53],[52,44,43],[51,65,12,18],[33,32,56],[55,46,45],[27,26,58],[57,48,47],[20,25,62,60],[59,62,50,49],[65,41,50,62],[61,60,59,63],[62,25,24,64],[63,13,12,65],[64,54,51,61]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Parabiaugmented truncated dodecahedron";
  if StringName=NameGraph then
    return [[10,30,68,2],[1,68,40,3],[2,40,4],[3,11,5],[4,11,6],[5,15,7],[6,15,8],[7,23,9],[8,23,10],[9,30,1],[4,16,5],[18,57,64,13],[12,64,24,14],[13,24,15],[14,7,6],[11,19,17],[16,19,18],[17,57,12],[16,42,17],[25,59,21],[20,31,22],[21,31,23],[22,9,8],[14,13,63,25],[24,63,59,20],[31,32,27],[26,32,28],[27,39,29],[28,39,69,30],[29,69,1,10],[22,21,26],[27,26,33],[32,51,34],[33,51,35],[34,50,36],[35,50,37],[36,58,38],[37,58,70,39],[38,70,29,28],[2,67,43,3],[44,55,42],[41,55,19],[40,67,45,44],[43,45,41],[43,66,58,44],[53,61,54,47],[46,54,48],[47,56,49],[48,56,50],[49,36,35],[34,33,52],[51,60,53],[52,60,61,46],[46,65,57,47],[42,41,56],[55,49,48],[54,65,12,18],[45,66,38,37],[20,25,62,60],[59,62,53,52],[65,46,53,62],[61,60,59,63],[62,25,24,64],[63,13,12,65],[64,57,54,61],[70,58,45,67],[66,43,40,68],[67,2,1,69],[68,30,29,70],[69,39,38,66]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Metabiaugmented truncated dodecahedron";
  if StringName=NameGraph then
    return [[10,33,2],[1,33,3],[2,11,4],[3,11,5],[4,15,6],[5,15,7],[6,23,8],[7,23,9],[8,29,10],[9,29,1],[3,16,4],[18,54,64,13],[12,64,24,14],[13,24,15],[14,6,5],[11,19,17],[16,19,18],[17,54,12],[16,39,17],[25,58,21],[20,30,22],[21,30,23],[22,8,7],[14,13,63,25],[24,63,58,20],[31,60,66,27],[26,66,34,28],[27,34,29],[28,10,9],[22,21,31],[30,60,26],[37,40,33],[32,2,1],[28,27,70,35],[34,70,55,36],[35,55,37],[36,40,32],[40,52,39],[38,52,19],[32,37,38],[50,61,51,42],[41,51,43],[42,53,44],[43,53,45],[44,56,46],[45,56,68,47],[46,68,57,48],[47,57,49],[48,59,50],[49,59,61,41],[41,65,54,42],[39,38,53],[52,44,43],[51,65,12,18],[36,35,69,56],[55,69,46,45],[47,67,60,48],[20,25,62,59],[58,62,50,49],[57,67,26,31],[65,41,50,62],[61,59,58,63],[62,25,24,64],[63,13,12,65],[64,54,51,61],[70,27,26,67],[66,60,57,68],[67,47,46,69],[68,56,55,70],[69,35,34,66]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Triaugmented truncated dodecahedron";
  if StringName=NameGraph then
    return [[10,37,71,2],[1,71,11,3],[2,11,4],[3,18,5],[4,18,6],[5,23,7],[6,23,8],[7,29,9],[8,29,10],[9,37,1],[2,75,12,3],[11,75,19,13],[12,19,68,14],[13,68,53,15],[14,53,16],[15,24,17],[16,24,18],[17,5,4],[12,74,60,69,13],[25,50,21],[20,30,22],[21,30,23],[22,7,6],[17,16,25],[24,50,20],[31,52,61,27],[26,61,32,28],[27,32,29],[28,9,8],[22,21,31],[30,52,26],[28,27,65,33],[32,65,56,34],[33,56,35],[34,38,36],[35,38,72,37],[36,72,1,10],[35,59,73,36],[48,66,55,40],[39,55,41],[40,57,42],[41,57,63,43],[42,63,49,44],[43,49,45],[44,51,46],[45,51,47],[46,54,48],[47,54,66,39],[43,62,52,44],[20,25,51],[50,46,45],[49,62,26,31],[15,14,67,54],[53,67,48,47],[39,70,58,40],[34,33,64,57],[56,64,42,41],[55,70,60,59],[58,60,73,38],[58,69,19,74,59],[65,27,26,62],[61,52,49,63],[62,43,42,64],[63,57,56,65],[64,33,32,61],[70,39,48,67],[66,54,53,68],[67,14,13,69],[68,19,60,70],[69,58,55,66],[75,2,1,72],[71,37,36,73],[72,38,59,74],[73,60,19,75],[74,12,11,71]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyrate rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,20,5,2],[1,5,7,3],[2,9,56,4],[3,56,44,1],[1,21,6,2],[5,25,11,7],[6,10,8,2],[7,10,12,9],[8,58,57,3],[7,11,13,8],[6,25,17,10],[13,14,58,8],[10,16,14,12],[13,15,60,12],[16,18,55,14],[13,17,18,15],[11,29,19,16],[16,19,31,15],[17,29,30,18],[1,32,22,21],[20,22,24,5],[20,33,23,21],[22,27,26,24],[23,26,25,21],[24,29,11,6],[23,28,29,24],[23,36,40,28],[27,40,30,26],[26,19,17,25],[28,41,31,19],[30,41,43,18],[20,44,34,33],[32,34,36,22],[32,45,35,33],[34,38,37,36],[35,37,27,33],[35,39,40,36],[35,48,52,39],[38,52,42,37],[37,41,28,27],[40,42,31,30],[39,53,43,41],[42,53,55,31],[32,4,46,45],[44,46,48,34],[44,56,47,45],[46,50,49,48],[47,49,38,45],[47,51,52,48],[47,57,59,51],[50,59,54,49],[49,53,39,38],[52,54,43,42],[51,60,55,53],[54,60,15,43],[4,3,57,46],[9,58,50,56],[9,12,59,57],[58,60,51,50],[59,14,55,54]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Parabigyrate rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,20,5,2],[1,5,7,3],[2,9,56,4],[3,56,46,1],[1,21,6,2],[5,25,11,7],[6,10,8,2],[7,10,13,9],[8,58,57,3],[7,11,12,8],[6,25,17,10],[10,15,14,13],[12,14,58,8],[12,16,60,13],[12,17,18,16],[15,18,55,14],[11,29,19,15],[15,19,31,16],[17,29,30,18],[1,32,22,21],[20,22,23,5],[20,33,24,21],[24,26,25,21],[22,27,26,23],[23,29,11,6],[24,28,29,23],[24,35,41,28],[27,41,30,26],[26,19,17,25],[28,42,31,19],[30,42,44,18],[20,46,45,33],[32,34,35,22],[33,45,37,35],[34,36,27,33],[37,38,41,35],[34,39,38,36],[37,40,43,36],[37,48,52,40],[39,52,53,38],[36,42,28,27],[41,43,31,30],[38,53,44,42],[43,53,55,31],[32,46,48,34],[32,4,47,45],[46,56,49,48],[47,49,39,45],[47,50,52,48],[49,57,59,51],[50,59,54,52],[51,40,39,49],[40,54,44,43],[51,60,55,53],[54,60,16,44],[4,3,57,47],[9,58,50,56],[9,13,59,57],[58,60,51,50],[59,14,55,54]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Metabigyrate rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,56,44,2],[1,20,5,3],[2,5,7,4],[3,8,56,1],[2,21,6,3],[5,26,11,7],[6,10,9,3],[9,58,57,4],[7,10,13,8],[7,11,12,9],[6,26,17,10],[10,16,14,13],[12,14,58,9],[12,15,60,13],[16,18,55,14],[12,17,18,15],[11,30,19,16],[16,19,32,15],[17,30,31,18],[2,34,33,21],[20,22,23,5],[21,33,24,23],[22,25,26,21],[22,28,27,25],[24,27,30,23],[23,30,11,6],[24,29,31,25],[24,36,39,29],[28,39,41,27],[25,19,17,26],[27,41,32,19],[31,41,43,18],[20,34,36,22],[20,44,35,33],[34,45,37,36],[35,37,28,33],[35,40,39,36],[40,52,42,39],[38,29,28,37],[37,47,52,38],[29,42,32,31],[38,53,43,41],[42,53,55,32],[34,1,46,45],[44,46,47,35],[44,56,48,45],[48,49,40,45],[46,50,49,47],[48,51,52,47],[48,57,59,51],[50,59,54,49],[49,53,38,40],[52,54,43,42],[51,60,55,53],[54,60,15,43],[1,4,57,46],[8,58,50,56],[8,13,59,57],[58,60,51,50],[59,14,55,54]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Trigyrate rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,56,44,2],[1,20,5,3],[2,5,7,4],[3,8,56,1],[2,21,6,3],[5,26,11,7],[6,10,9,3],[9,59,57,4],[7,10,13,8],[7,11,12,9],[6,26,17,10],[10,16,14,13],[12,14,59,9],[12,15,55,13],[16,18,54,14],[12,17,18,15],[11,30,19,16],[16,19,32,15],[17,30,31,18],[2,34,33,21],[20,22,23,5],[21,33,24,23],[22,25,26,21],[22,28,27,25],[24,27,30,23],[23,30,11,6],[24,29,31,25],[24,36,40,29],[28,40,41,27],[25,19,17,26],[27,41,32,19],[31,41,43,18],[20,34,36,22],[20,44,35,33],[34,45,37,36],[35,37,28,33],[35,38,40,36],[37,48,49,39],[38,51,42,40],[39,29,28,37],[29,42,32,31],[39,51,43,41],[42,52,54,32],[34,1,46,45],[44,46,48,35],[44,56,47,45],[46,58,50,48],[47,49,38,45],[48,50,51,38],[47,58,53,49],[49,52,42,39],[51,53,54,43],[50,60,55,52],[52,55,15,43],[53,60,14,54],[1,4,57,46],[8,59,58,56],[57,60,50,47],[8,13,60,57],[59,55,53,58]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Diminished rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,44,2],[1,20,5,3],[2,5,7,4],[3,9,1],[2,21,6,3],[5,11,10,7],[6,10,8,3],[7,13,14,9],[8,46,4],[6,12,13,7],[6,23,28,12],[11,28,17,10],[10,16,14,8],[13,15,46,8],[16,18,55,14],[13,17,18,15],[12,29,19,16],[16,19,54,15],[17,29,31,18],[2,32,22,21],[20,22,23,5],[20,33,24,21],[24,25,11,21],[22,26,25,23],[24,27,28,23],[24,35,40,27],[26,40,30,25],[25,29,12,11],[28,30,19,17],[27,41,31,29],[30,41,43,19],[20,44,34,33],[32,34,35,22],[32,45,36,33],[36,37,26,33],[34,38,37,35],[36,39,40,35],[36,50,51,39],[38,51,42,37],[37,41,27,26],[40,42,31,30],[39,52,43,41],[42,52,54,31],[32,1,45],[44,50,34],[9,14,47],[46,55,48],[47,53,49],[48,51,50],[49,38,45],[49,52,39,38],[51,53,43,42],[48,55,54,52],[53,55,18,43],[47,15,54,53]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Paragyrate diminished rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,45,2],[1,20,5,3],[2,5,6,4],[3,9,1],[2,21,7,3],[7,10,8,3],[5,12,10,6],[6,13,14,9],[8,50,4],[7,11,13,6],[12,27,17,10],[7,23,25,11],[10,16,14,8],[13,15,50,8],[16,18,55,14],[13,17,18,15],[11,27,19,16],[16,19,54,15],[17,28,30,18],[2,32,22,21],[20,22,23,5],[20,33,24,21],[24,25,12,21],[22,37,26,23],[23,26,27,12],[24,37,29,25],[25,28,17,11],[27,29,30,19],[26,41,31,28],[28,31,43,19],[29,41,42,30],[20,45,34,33],[32,34,36,22],[32,44,35,33],[34,39,38,36],[35,38,37,33],[36,41,26,24],[35,40,41,36],[35,49,51,40],[39,51,42,38],[38,31,29,37],[40,52,43,31],[42,52,54,30],[45,49,34],[32,1,44],[50,55,47],[46,53,48],[47,51,49],[48,39,44],[9,14,46],[48,52,40,39],[51,53,43,42],[47,55,54,52],[53,55,18,43],[46,15,54,53]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Metagyrate diminished rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,20,5,2],[1,5,6,3],[2,9,4],[3,44,1],[1,21,7,2],[7,10,8,2],[5,11,10,6],[6,13,14,9],[8,50,3],[7,12,13,6],[7,24,28,12],[11,28,17,10],[10,16,14,8],[13,15,50,8],[16,18,55,14],[13,17,18,15],[12,29,19,16],[16,19,54,15],[17,29,31,18],[1,33,22,21],[20,22,24,5],[20,32,23,21],[22,26,25,24],[23,25,11,21],[23,27,28,24],[23,35,37,27],[26,39,30,25],[25,29,12,11],[28,30,19,17],[27,39,31,29],[30,40,42,19],[33,34,35,22],[20,44,34,32],[33,45,36,32],[36,37,26,32],[34,51,38,35],[35,38,39,26],[36,51,41,37],[37,40,30,27],[39,41,42,31],[38,52,43,40],[40,43,54,31],[41,52,53,42],[33,4,45],[44,49,34],[50,55,47],[46,53,48],[47,52,49],[48,51,45],[9,14,46],[49,52,38,36],[48,43,41,51],[47,55,54,43],[53,55,18,42],[46,15,54,53]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Bigyrate diminished rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,22,21,2],[1,6,5,3],[2,10,4],[3,44,1],[6,7,9,2],[2,21,8,5],[8,11,14,5],[6,13,11,7],[5,14,15,10],[9,46,3],[8,12,18,7],[13,27,29,11],[8,24,27,12],[7,16,15,9],[14,17,46,9],[14,18,19,17],[16,19,55,15],[11,29,20,16],[16,20,54,17],[18,29,31,19],[1,22,24,6],[1,33,23,21],[22,32,25,24],[23,25,13,21],[23,28,27,24],[28,39,30,27],[26,12,13,25],[25,36,37,26],[12,30,20,18],[26,39,31,29],[30,40,42,20],[33,34,36,23],[22,44,34,32],[33,45,35,32],[34,51,38,36],[35,37,28,32],[36,38,39,28],[35,51,41,37],[37,40,30,26],[39,41,42,31],[38,52,43,40],[40,43,54,31],[41,52,53,42],[33,4,45],[44,50,34],[10,15,47],[46,55,48],[47,53,49],[48,52,50],[49,51,45],[50,52,38,35],[49,43,41,51],[48,55,54,43],[53,55,19,42],[47,17,54,53]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Parabidiminished rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,39,2],[1,20,5,3],[2,5,7,4],[3,9,1],[2,21,6,3],[5,11,10,7],[6,10,8,3],[7,13,14,9],[8,41,4],[6,12,13,7],[6,24,12],[11,17,10],[10,16,14,8],[13,15,41,8],[16,18,50,14],[13,17,18,15],[12,19,16],[16,19,49,15],[17,28,18],[2,29,22,21],[20,22,24,5],[20,30,23,21],[22,25,24],[23,11,21],[23,32,26],[25,34,27],[26,37,28],[27,38,19],[20,39,31,30],[29,31,32,22],[29,40,33,30],[33,34,25,30],[31,35,34,32],[33,36,26,32],[33,45,46,36],[35,46,37,34],[36,47,38,27],[37,47,49,28],[29,1,40],[39,45,31],[9,14,42],[41,50,43],[42,48,44],[43,46,45],[44,35,40],[44,47,36,35],[46,48,38,37],[43,50,49,47],[48,50,18,38],[42,15,49,48]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Metabidiminished rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,41,2],[1,20,5,3],[2,5,7,4],[3,9,1],[2,21,6,3],[5,11,10,7],[6,10,8,3],[7,13,14,9],[8,47,4],[6,12,13,7],[6,24,28,12],[11,28,17,10],[10,16,14,8],[13,15,47,8],[16,18,50,14],[13,17,18,15],[12,29,19,16],[16,19,49,15],[17,29,31,18],[2,33,22,21],[20,22,24,5],[20,32,23,21],[22,26,25,24],[23,25,11,21],[23,27,28,24],[23,36,27],[26,30,25],[25,29,12,11],[28,30,19,17],[27,31,29],[30,40,19],[33,34,36,22],[20,41,34,32],[33,42,35,32],[34,37,36],[35,26,32],[35,46,38],[37,45,39],[38,48,40],[39,49,31],[33,1,42],[41,46,34],[47,50,44],[43,48,45],[44,38,46],[45,37,42],[9,14,43],[44,50,49,39],[48,50,18,40],[43,15,49,48]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Gyrate bidiminished rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,41,2],[1,20,5,3],[2,5,7,4],[3,9,1],[2,21,6,3],[5,25,11,7],[6,10,8,3],[7,10,13,9],[8,43,4],[7,11,12,8],[6,25,17,10],[10,16,14,13],[12,14,43,8],[12,15,50,13],[16,18,49,14],[12,17,18,15],[11,29,19,16],[16,19,31,15],[17,29,30,18],[2,32,22,21],[20,22,24,5],[20,33,23,21],[22,27,26,24],[23,26,25,21],[24,29,11,6],[23,28,29,24],[23,36,28],[27,30,26],[26,19,17,25],[28,31,19],[30,38,18],[20,41,34,33],[32,34,36,22],[32,42,35,33],[34,39,36],[35,27,33],[40,48,38],[37,49,31],[35,47,40],[39,46,37],[32,1,42],[41,47,34],[9,13,44],[43,50,45],[44,48,46],[45,40,47],[46,39,42],[45,50,49,37],[48,50,15,38],[44,14,49,48]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Tridiminished rhombicosidodecahedron";
  if StringName=NameGraph then
    return [[4,36,2],[1,17,5,3],[2,5,7,4],[3,9,1],[2,18,6,3],[5,16,7],[6,8,3],[7,15,9],[8,38,4],[16,22,11],[10,25,12],[11,26,13],[12,44,14],[13,45,15],[14,38,8],[6,21,10],[2,27,19,18],[17,19,21,5],[17,28,20,18],[19,24,22,21],[20,22,16,18],[20,23,10,21],[24,25,22],[20,31,23],[23,26,11],[25,32,12],[17,36,29,28],[27,29,31,19],[27,37,30,28],[29,33,31],[30,24,28],[35,44,26],[30,42,34],[33,41,35],[34,43,32],[27,1,37],[36,42,29],[9,15,39],[38,45,40],[39,43,41],[40,34,42],[41,33,37],[40,45,44,35],[43,45,13,32],[39,14,44,43]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Snub disphenoid";
  if StringName=NameGraph then
    return [[3,8,5,4,2],[1,4,6,3],[2,6,7,8,1],[1,5,6,2],[1,8,7,6,4],[2,4,5,7,3],[5,8,3,6],[5,1,3,7]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Snub square antiprism";
  if StringName=NameGraph then
    return [[4,12,7,6,2],[1,6,5,8,3],[2,8,9,10,4],[3,10,11,12,1],[6,14,13,8,2],[2,1,7,14,5],[1,12,15,14,6],[3,2,5,13,9],[8,13,16,10,3],[4,3,9,16,11],[10,16,15,12,4],[1,4,11,15,7],[16,9,8,5,14],[13,5,6,7,15],[14,7,12,11,16],[15,11,10,9,13]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Sphenocorona";
  if StringName=NameGraph then
    return [[4,8,6,2],[1,5,10,3],[2,10,9,4],[3,9,8,1],[6,7,10,2],[1,8,7,5],[9,10,5,6,8],[7,6,1,4,9],[8,4,3,10,7],[3,2,5,7,9]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Augmented sphenocorona";
  if StringName=NameGraph then
    return [[3,11,8,5,2],[1,4,10,9,3],[2,9,11,1],[5,7,10,2],[1,8,7,4],[8,11,9,10,7],[6,10,4,5,8],[7,5,1,11,6],[6,11,3,2,10],[9,2,4,7,6],[8,1,3,9,6]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Sphenomegacorona";
  if StringName=NameGraph then
    return [[4,10,8,2],[1,8,9,5,3],[2,5,6,7,4],[3,7,11,1],[2,9,12,6,3],[3,5,12,11,7],[6,11,4,3],[2,1,10,9],[8,10,12,5,2],[11,12,9,8,1],[4,7,6,12,10],[11,6,5,9,10]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Hebesphenomegacorona";
  if StringName=NameGraph then
    return [[4,10,8,2],[1,8,9,5,3],[2,5,6,7,4],[3,7,11,1],[2,9,14,6,3],[3,5,14,13,7],[6,13,11,4,3],[2,1,10,12,9],[8,12,14,5,2],[11,12,8,1],[4,7,13,10],[13,14,9,8,10],[11,7,6,14,12],[13,6,5,9,12]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Disphenocingulum";
  if StringName=NameGraph then
    return [[3,13,14,4,2],[1,5,7,3],[2,7,10,13,1],[1,14,16,6,5],[4,6,8,2],[4,16,15,8,5],[2,8,9,10,3],[5,6,15,9,7],[8,15,11,10,7],[7,9,11,13,3],[9,15,12,10],[11,16,14,13],[12,14,1,3,10],[13,12,16,4,1],[11,9,8,6,16],[15,6,4,14,12]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Bilunabirotunda";
  if StringName=NameGraph then
    return [[4,7,8,2],[1,8,5,3],[2,5,6,4],[3,6,7,1],[2,10,3],[3,11,12,4],[4,13,1],[1,14,9,2],[8,14,11,10],[9,11,5],[10,9,12,6],[6,11,14,13],[12,14,7],[13,12,9,8]];
  fi;
  Add(ListNames, NameGraph);

  #
  NameGraph:="Triangular hebesphenorotunda";
  if StringName=NameGraph then
    return [[5,9,12,2],[1,12,17,3],[2,17,6,4],[3,6,7,5],[4,7,9,1],[3,18,7,4],[6,8,5,4],[7,13,10,9],[8,10,1,5],[9,8,13,11],[10,13,14,12],[11,14,2,1],[8,15,11,10],[11,15,16,12],[13,18,16,14],[14,15,18,17],[16,18,3,2],[15,6,17,16]];
  fi;
  Add(ListNames, NameGraph);


  if StringName="List" then
    return ListNames;
  fi;
  return fail;
end;

DyckMap:=function()
  return [[4,3,2,9,8,7,6,5],[9,1,3,11,5,10,7,12],[11,2,1,4,12,6,10,8],[12,3,1,5,11,7,10,9],[11,4,1,6,12,8,10,2],[5,1,7,11,9,10,3,12],[11,6,1,8,12,2,10,4],[12,7,1,9,11,3,10,5],[11,8,1,2,12,4,10,6],[9,4,7,2,5,8,3,6],[9,6,7,4,5,2,3,8],[6,3,4,9,2,7,8,5]];
end;

KleinMap:=function()
  return [[22,24,7,2,17,6,19],[17,1,7,20,3,13,18],[2,20,23,22,8,4,13],[5,15,14,13,3,8,21],[4,21,24,23,9,6,15],[16,15,5,9,19,1,17],[1,24,10,14,15,20,2],[3,22,11,16,17,21,4],[6,5,23,12,18,13,19],[24,21,18,12,11,14,7],[16,8,22,19,14,10,12],[9,23,20,16,11,10,18],[3,4,14,19,9,18,2],[7,10,11,19,13,4,15],[20,7,14,4,5,6,16],[8,11,12,20,15,6,17],[6,1,2,18,21,8,16],[12,10,21,17,2,13,9],[6,9,13,14,11,22,1],[3,2,7,15,16,12,23],[10,24,5,4,8,17,18],[3,23,24,1,19,11,8],[9,5,24,22,3,20,12],[1,22,23,5,21,10,7]];
end;


IsRegularPlanGraph:=function(PlanGraph)
  local ListVal, eAdj;
  ListVal:=[];
  for eAdj in PlanGraph
  do
    AddSet(ListVal, Length(eAdj));
    if Length(ListVal)<>1 then
      return false;
    fi;
  od;
  return true;
end;




IsFaceRegular:=function(PlanGraph)
  local DualG, ListGonality, eGon, ListOfMatch, i, ListMatch, u, jGon, pos, ListStatus, STR, test;
  if IsRegularPlanGraph(PlanGraph)<>true then
    return false;
  fi;
  DualG:=DualGraph(PlanGraph).PlanGraph;
  ListGonality:=[];
  for i in [1..Length(DualG)]
  do
    AddSet(ListGonality, Length(DualG[i]));
  od;
  ListStatus:=[];
  for eGon in ListGonality
  do
    ListOfMatch:=[];
    test:=true;
    for i in [1..Length(DualG)]
    do
      if Length(DualG[i])=eGon then
        ListMatch:=ListWithIdenticalEntries(Length(ListGonality), 0);
        for u in DualG[i]
        do
          jGon:=Length(DualG[u]);
          pos:=Position(ListGonality, jGon);
          ListMatch[pos]:=ListMatch[pos]+1;
        od;
        AddSet(ListOfMatch, ListMatch);
        if Length(ListOfMatch)<>1 then
          test:=false;
        fi;
      fi;
    od;
    if test=true then
      ListMatch:=ListOfMatch[1];
      STR:=Concatenation(String(eGon), "R(");
      for jGon in [1..Length(ListGonality)]
      do
        STR:=Concatenation(STR, String(ListGonality[jGon]), ":", String(ListMatch[jGon]));
        if jGon < Length(ListGonality) then
          STR:=Concatenation(STR, ",");
        fi;
      od;
      STR:=Concatenation(STR, ")");
      Add(ListStatus, STR);
    else
      Add(ListStatus, "void");
    fi;
  od;
  return ListStatus;
end;


TorusHexagon:=function()
  local eListInv, eListNext;
  eListInv:=[4,5,6,1,2,3];
  eListNext:=[6,4,5,3,1,2];
  return rec(next:=PermList(eListNext), invers:=PermList(eListInv), nbP:=6);
end;





