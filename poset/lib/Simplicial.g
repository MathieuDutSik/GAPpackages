#Simplicial poset are encoded as set of vertices.
#We keep only the facets of highest dimension
#example for octahedron:
#[[1,2,3],[4,2,3],[1,5,3],[4,5,3],[1,5,6],[4,5,6]]
#the point is to extend simplicial complexes by faces of
#dimension n-2


ListFacesDimK:=function(SimpPoset, k)
  local ListFaces, eFacet;
  ListFaces:=[];
  for eFacet in SimpPoset
  do
    ListFaces:=Union(ListFaces, Combinations(eFacet, k));
  od;
  return ListFaces;
end;

ListOfVertices:=function(SimpPoset)
  local LV, eFacet;
  LV:=[];
  for eFacet in SimpPoset
  do
    LV:=Union(LV, eFacet);
  od;
  return LV;
end;

ListCandidateForExtension:=function(SimpPoset)
  local SimpPosetDim, ListFaces, ListVertex, ListCand, eCand, Liststatus, iCol, eFacet, FE, pos, test, VertexNumber;
  SimpPosetDim:=Length(SimpPoset[1]);
  ListVertex:=ListOfVertices(SimpPoset);
  ListFaces:=ListFacesDimK(SimpPoset, SimpPosetDim-2);
  ListCand:=[];
  for eCand in ListFaces
  do
#    Print("Looking at ", eCand, "\n");
    Liststatus:=[];
    for iCol in [1..Length(ListVertex)]
    do
      Liststatus[iCol]:=0;
    od;
    for eFacet in SimpPoset
    do
      if IsSubset(eFacet, eCand) then
        FE:=Difference(eFacet, eCand);
        pos:=Position(ListVertex, FE[1]);
        Liststatus[pos]:=Liststatus[pos]+1;
        pos:=Position(ListVertex, FE[2]);
        Liststatus[pos]:=Liststatus[pos]+1;
      fi;
    od;
#    Print("Liststatus=", Liststatus, "\n");
    test:=false;
    VertexNumber:=0;
    for iCol in [1..Length(ListVertex)]
    do
      if Liststatus[iCol]=1 then
        test:=true;
      fi;
      if Liststatus[iCol]>0 then
        VertexNumber:=VertexNumber+1;
      fi;
    od;
    if test=true then
      Add(ListCand, [eCand,VertexNumber]);
#    else
#      Print("It is saturated\n");
    fi;
#    Print("\n");
  od;
  return ListCand;
end;


ExtensionByFace:=function(SimpPoset, eCand, FoldNumber)
  local ListVertex, Liststatus, eFacet, FE, NewSimpPoset, pos, EndS, VertexNumber, iCol, Diff, ListN, iDiff, fCand;
  ListVertex:=ListOfVertices(SimpPoset);
  Liststatus:=[];
  for iCol in [1..Length(ListVertex)]
  do
    Liststatus[iCol]:=0;
  od;
  for eFacet in SimpPoset
  do
    if IsSubset(eFacet, eCand) then
      FE:=Difference(eFacet, eCand);
      pos:=Position(ListVertex, FE[1]);
      Liststatus[pos]:=Liststatus[pos]+1;
      pos:=Position(ListVertex, FE[2]);
      Liststatus[pos]:=Liststatus[pos]+1;
    fi;
  od;
#  Print("Liststatus=", Liststatus, "\n");
  EndS:=[];
  VertexNumber:=0;
  for iCol in [1..Length(ListVertex)]
  do
    if Liststatus[iCol]=1 then
      Add(EndS, ListVertex[iCol]);
    fi;
    if Liststatus[iCol]>0 then
      VertexNumber:=VertexNumber+1;
    fi;
    if Liststatus[iCol]>2 then
      return false;
    fi;
  od;
#  Print("EndS=", EndS, "\n");
  if VertexNumber=FoldNumber then
#    Print("first case\n");
    fCand:=Union(eCand, EndS);
    NewSimpPoset:=Union(SimpPoset, [fCand]);
    return NewSimpPoset;
  else
#    Print("second case\n");
    Diff:=FoldNumber-VertexNumber;
    NewSimpPoset:=[];
    for fCand in SimpPoset
    do
      Add(NewSimpPoset, fCand);
    od;
    ListN:=[EndS[1]];
    for iDiff in [1..Diff]
    do
      Add(ListN, Maximum(ListVertex)+iDiff);
    od;
    Add(ListN, EndS[2]);
#    Print(ListN, "\n");
    for iCol in [1..Length(ListN)-1]
    do
      Add(NewSimpPoset, Union(eCand, Set([ListN[iCol], ListN[iCol+1]])) );
    od;
    return NewSimpPoset;
  fi;
end;

SimplicialPosetToHasseDiagram:=function(SimpPoset)
  local ListFaces, eFacet, NewPoset, iSet, jSet, SEi, SEj;
  ListFaces:=[];
  for eFacet in SimpPoset
  do
    ListFaces:=Union(ListFaces, Set(Combinations(eFacet)));
  od;
  NewPoset:=[];
  for iSet in [1..Length(ListFaces)]
  do
    for jSet in [1..Length(ListFaces)]
    do
      SEi:=ListFaces[iSet];
      SEj:=ListFaces[jSet];
      if iSet<>jSet and IsSubset(SEj, SEi)=true and Length(SEj)=1+Length(SEi) then
        Add(NewPoset, [iSet, jSet]);
      fi;
    od;
  od;
  return NewPoset;
end;



EliminationIsomorph:=function(ListSimpPoset)
  local ListGRAP, ListInvariant, iSP, LSE, eSamp, NewListSimpPoset;
  ListGRAP:=[];
  ListInvariant:=[];
  for iSP in [1..Length(ListSimpPoset)]
  do
    Add(ListGRAP, PosetToGRAPE(SimplicialPosetToHasseDiagram(ListSimpPoset[iSP])));
    Add(ListInvariant, Length(ListSimpPoset[iSP]));
  od;
  LSE:=RemoveByIsomorphy(ListGRAP, ListInvariant, IsIsomorphicGraph);
  NewListSimpPoset:=[];
  for eSamp in LSE.ListSample
  do
    Add(NewListSimpPoset, ListSimpPoset[eSamp]);
  od;
  return NewListSimpPoset;
end;



ClosureOperation:=function(SimpPoset, FoldNumber)
  local NewSimpPoset, eFacet, FCTbreak, VCE;
  NewSimpPoset:=[];
  for eFacet in SimpPoset
  do
    Add(NewSimpPoset, eFacet);
  od;
  FCTbreak:=function(SimpPoset)
    local eCand, VCE, TheStatus;
    VCE:=[];
    TheStatus:=true;
    for eCand in ListCandidateForExtension(SimpPoset)
    do
      if eCand[2]=FoldNumber then
        Add(VCE, eCand[1]);
      fi;
      if eCand[2]>FoldNumber then
        return false;
      fi;
    od;
    return VCE;
  end;
  while (true)
  do
    VCE:=FCTbreak(NewSimpPoset);
    if VCE=false then
      return false;
    else
      if VCE=[] then
        return NewSimpPoset;
      else
#        Print("Inserting face ", VCE[1], "\n");
#        Print("NewSimposet before=", NewSimpPoset, "\n");
        NewSimpPoset:=ExtensionByFace(NewSimpPoset, VCE[1], FoldNumber);
        if NewSimpPoset=false then
          return false;
        fi;
#        Print("NewSimposet after=", NewSimpPoset, "\n");
      fi;
    fi;
  od;
end;


SpanningFromOneElement:=function(SimpPoset, Lset)
  local ListSpanned, eCand, U, eVal, MaxLink, OneSimpPoset;
  MaxLink:=Maximum(Lset);
  ListSpanned:=[];
  for eCand in ListCandidateForExtension(SimpPoset)
  do
    for eVal in Lset
    do
      U:=ExtensionByFace(SimpPoset, eCand[1], eVal);
#      Print("U=", U, "\n");
      if U<>false then
        OneSimpPoset:=ClosureOperation(U, MaxLink);
        if OneSimpPoset<>false then
          AddSet(ListSpanned, OneSimpPoset);
        fi;
      fi;
    od;
  od;
  return ListSpanned;
end;



GenerationPoset:=function(Beginning, Lset)
  local ListUncompleted, ListSpanned, ListProv, eSimp, ListUnicized, ListCand;
  ListUncompleted:=[Beginning];
  ListSpanned:=[];
  while(Length(ListUncompleted)>0)
  do
    ListProv:=[];
    for eSimp in ListUncompleted
    do
#      Print("eSimp=", eSimp, "\n");
      ListProv:=Union(ListProv, SpanningFromOneElement(eSimp, Lset));
#      Print("Spanning finished\n");
    od;
    ListUnicized:=EliminationIsomorph(ListProv);
    ListUncompleted:=[];
    for eSimp in ListUnicized
    do
      ListCand:=ListCandidateForExtension(eSimp);
      if Length(ListCand)>0 then
        AddSet(ListUncompleted, eSimp);
      else
        AddSet(ListSpanned, eSimp);
      fi;
    od;
    Print("We have ", Length(ListSpanned), " generated complexes\n");
    Print("ListSpanned=", ListSpanned, "\n");
    Print("We have ", Length(ListUncompleted), " uncompleted complexes\n");
#    Print("ListUncompleted=", ListUncompleted, "\n");
  od;
  return EliminationIsomorph(ListSpanned);
end;





ListFacesSimpPoset:=function(SimpPoset)
  local PosDim, ListFacesByRank, iRank, eFacet, eSet;
  PosDim:=Length(SimpPoset[1]);
  ListFacesByRank:=[];
  for iRank in [1..PosDim]
  do
    ListFacesByRank[iRank]:=[];
  od;
  for eFacet in SimpPoset
  do
    for eSet in Combinations(eFacet)
    do
      if Length(eSet)>0 then
        AddSet(ListFacesByRank[Length(eSet)], eSet);
      fi;
    od;
  od;
  return ListFacesByRank;
end;









CreateSAUSimplicialPoset:=function(SimpPoset)
  local SEQE, nRank, ListAbove, iRank, ListAB, iElt, ListFound, jElt, ListUnder;
  SEQE:=ListFacesSimpPoset(SimpPoset);
  nRank:=Length(SimpPoset[1])+1;
  ListAbove:=[];
  for iRank in [1..nRank-2]
  do
    ListAB:=[];
    for iElt in [1..Length(SEQE[iRank])]
    do
      ListFound:=[];
      for jElt in [1..Length(SEQE[iRank+1])]
      do
        if IsSubset(SEQE[iRank+1][jElt], SEQE[iRank][iElt])=true then
          Add(ListFound, jElt);
        fi;
      od;
      Add(ListAB, ListFound);
    od;
    Add(ListAbove, ListAB);
  od;
  ListUnder:=[];
  for iRank in [1..nRank-2]
  do
    ListAB:=[];
    for iElt in [1..Length(SEQE[iRank+1])]
    do
      ListFound:=[];
      for jElt in [1..Length(SEQE[iRank])]
      do
        if IsSubset(SEQE[iRank+1][iElt], SEQE[iRank][jElt])=true then
          Add(ListFound, jElt);
        fi;
      od;
      Add(ListAB, ListFound);
    od;
    Add(ListUnder, ListAB);
  od;
  return rec(SEQE:=SEQE, ListAbove:=ListAbove, ListUnder:=ListUnder);
end;




SimplicialPosetToPoset:=function(SimpPoset)
  local ListFaces, eFacet, NewPoset, iSet, jSet, PosDim, iRank, eSet, ListFacesByRank;
  PosDim:=Length(SimpPoset[1])+2;
  ListFacesByRank:=[];
  for iRank in [1..PosDim]
  do
    ListFacesByRank[iRank]:=[];
  od;
  for eFacet in SimpPoset
  do
    for eSet in Combinations(eFacet)
    do
      if Length(eSet)>0 then
        AddSet(ListFacesByRank[Length(eSet)+1], eSet);
      fi;
    od;
  od;
  AddSet(ListFacesByRank[1], []);
  AddSet(ListFacesByRank[PosDim], ListOfVertices(SimpPoset));
  ListFaces:=[];
  for iRank in [1..PosDim]
  do
    for iSet in [1..Length(ListFacesByRank[iRank])]
    do
      Add(ListFaces, ListFacesByRank[iRank][iSet]);
    od;
  od;
  NewPoset:=[];
  for iSet in [1..Length(ListFaces)]
  do
    for jSet in [1..Length(ListFaces)]
    do
      if iSet<>jSet and IsSubset(ListFaces[jSet], ListFaces[iSet])=true then
        Add(NewPoset, [iSet, jSet]);
      fi;
    od;
  od;
  return rec(Poset:=NewPoset, ListFacesByRank:=ListFacesByRank, ListFaces:=ListFaces);
end;





AutGroupFacesDimk:=function(SimpPoset, kDim)
  local NPoset, Gra, eInc, SymGrp, NewGens,eGen, ListE, iVert, AddNbr, iRank;
  NPoset:=SimplicialPosetToPoset(SimpPoset);
  Gra:=NullGraph(Group(()), Length(NPoset.ListFaces));
  for eInc in NPoset.Poset
  do
    AddEdgeOrbit(Gra, eInc);
  od;
  SymGrp:=AutGroupGraph(Gra);
  NewGens:=[];
  AddNbr:=0;
  for iRank in [1..kDim-1]
  do
    AddNbr:=AddNbr+Length(NPoset.ListFacesByRank[iRank]);
  od;
  for eGen in GeneratorsOfGroup(SymGrp)
  do
    ListE:=[];
    for iVert in [1..Length(NPoset.ListFacesByRank[kDim])]
    do
      ListE[iVert]:=OnPoints(AddNbr+iVert, eGen)-AddNbr;
    od;
    Add(NewGens, PermList(ListE));
  od;
  return Group(NewGens);
end;


IsIsohedral:=function(SimpPoset)
  return IsTransitive(AutGroupFacesDimk(SimpPoset, Length(SimpPoset[1])));
end;









HyperOctahedron:=function(n)
  local ListFacet, eSet, eFac, i, Gra;
  ListFacet:=[];
  for eSet in Combinations([1..n])
  do
    eFac:=[];
    for i in [1..n]
    do
      if i in eSet then
        AddSet(eFac, i);
      else
        AddSet(eFac, n+i);
      fi;
    od;
    AddSet(ListFacet, eFac);
  od;
  Gra:=NullGraph(Group(()), 2*n);
  for i in [1..n]
  do
    AddEdgeOrbit(Gra, [i,n+i]);
    AddEdgeOrbit(Gra, [n+i,i]);
  od;
  return rec(ListSimplexes:=ListFacet, GroupEXT:=AutGroupGraph(Gra));
end;



CombinatorialGroupSize:=function(ePart)
  local SiZ, i, uSiz, m;
  SiZ:=1;
  for i in [1..Length(ePart)]
  do
    SiZ:=SiZ*Factorial(1+Length(ePart[i]));
  od;
  for uSiz in [1..Length(ePart)]
  do
    m:=0;
    for i in [1..Length(ePart)]
    do
      if Length(ePart[i])=uSiz then
        m:=m+1;
      fi;
    od;
    SiZ:=SiZ*Factorial(m);
  od;
  return SiZ;
end;


SymmetryGroupSimplicialComplex:=function(eSimp)
  local ListVert, Gra, iVert, iFacet, Gens, NewGens, eGen, Lval, iVal;  
  ListVert:=ListOfVertices(eSimp);
  Gra:=NullGraph(Group(()), Length(ListVert)+Length(eSimp));
  for iVert in [1..Length(ListVert)]
  do
    for iFacet in [1..Length(eSimp)]
    do
      if ListVert[iVert] in eSimp[iFacet] then
        AddEdgeOrbit(Gra, [iVert, Length(ListVert)+iFacet]);
      fi;
    od;
  od;
  Gens:=GeneratorsOfGroup(AutGroupGraph(Gra));
  if Length(Gens)=0 then
    return Group(());
  else
    NewGens:=[];
    for eGen in Gens
    do
      Lval:=[];
      for iVal in [1..Length(ListVert)]
      do
        Lval[iVal]:=OnPoints(iVal, eGen);
      od;
      Add(NewGens, PermList(Lval));
    od;
    return Group(NewGens);
  fi;
end;



CoxeterSubgroup:=function(eSimp)
  local n, ListVert, 2face, SymGrp, ListGen, iGen, Stab;
  n:=Length(eSimp[1]);
  ListVert:=ListOfVertices(eSimp);
  SymGrp:=SymmetryGroupSimplicialComplex(eSimp);
  ListGen:=[];
  for iGen in [1..n]
  do
    2face:=Difference([1..n], [iGen]);
    Stab:=Stabilizer(SymGrp, 2face, OnTuples);
    if Order(Stab)<>2 then
      Print("Error in generation of Coxeter groups\n");
    fi;
    Add(ListGen, GeneratorsOfGroup(Stab)[1]);
  od;
  return Group(ListGen);
end;


GenerationSimpPoset3or4PartitionMethod:=function(n)
  local ListCase, ListSimpPoset, HyperOct, LRamPart, eCase, NewPoset, eFacet, fFacet, iVert, iPart, jVert;
  ListSimpPoset:=[];
  HyperOct:=HyperOctahedron(n);
  LRamPart:=GenerationRamanujanPartitions(n);
  for eCase in LRamPart
  do
    NewPoset:=[];
    for eFacet in HyperOct.ListSimplexes
    do
      fFacet:=[];
      for iVert in eFacet
      do
        if iVert<=n then
          AddSet(fFacet, iVert);
        else
          jVert:=iVert-n;
          for iPart in [1..Length(eCase)]
          do
            if jVert in eCase[iPart] then
              AddSet(fFacet, iPart+n);
            fi;
          od;
        fi;
      od;
      if Length(fFacet)=n then
        AddSet(NewPoset, fFacet);
      fi;
    od;
    Add(ListSimpPoset, NewPoset);
  od;
  return rec(ListCases:=LRamPart, ListSimpPoset:=ListSimpPoset);
end;




SkelettonGraphSimpPoset:=function(SimpPoset)
  local ListVert, ListEdge, Gra, eEdge, a, b;
  ListVert:=ListOfVertices(SimpPoset);
  ListEdge:=ListFacesDimK(SimpPoset, 2);
  Gra:=NullGraph(Group(()), Length(ListVert));
  for eEdge in ListEdge
  do
    a:=eEdge[1];
    b:=eEdge[2];
    AddEdgeOrbit(Gra, [a,b]);
    AddEdgeOrbit(Gra, [b,a]);
  od;
  return Gra;
end;


RegularSimplex:=function(n)
  return rec(ListSimplexes:=Combinations([1..n+2], n+1), GroupEXT:=SymmetricGroup([1..n+2]));
end;



#
# if n is dimension of the complex, then
# type is a subset of 1, ...., n+1
WythoffConstruction:=function(ListSimplexesByVertexSet, eType, GroupEXT)
  local n, ListFlag, eSimp, ePerm, ListVert, ListFacesBySet, ListSimplexContainingFaceBySet, ListOfSet, eSet, ListFacesFixedRank, ListSimplexContainingFace, eface, eF, pos, nbClass, SetOfFace, SpecifiedFlag, ToolForRankingVertexSetsBySet, MaxFoundRankSubset, iPos, jPos, ListRank, iRank, Rankable, nbRanked, eSer, FacesAsVertexSetBySet, ListFaces, NewGens, Gens, eGen, eVert, iVert, NewGroupEXT, LPerm, ListPos, FuncExpression, nbIter;
  n:=Length(ListSimplexesByVertexSet[1])-1;
  ListFlag:=[];
  for eSimp in ListSimplexesByVertexSet
  do
    for ePerm in SymmetricGroup([1..n+1])
    do
      Add(ListFlag, Permuted(eSimp, ePerm));
    od;
  od;
#  Print("Find ", Length(ListFlag), "\n");
  FuncExpression:=function(eFlag, eT)
    local LSE, Prec, i;
    LSE:=[];
    Prec:=[];
    for i in [1..n+1]
    do
      AddSet(Prec, eFlag[i]);
      Add(LSE, ShallowCopy(Prec));
    od;
    return LSE{eT};
  end;
  ListFacesBySet:=[];
  ListSimplexContainingFaceBySet:=[];
  ListOfSet:=[];
  for eSet in Filtered(Combinations([1..n+1]), x->Length(x)>0)
  do
    ListFacesFixedRank:=[];
    ListSimplexContainingFace:=[];
    for eSimp in ListFlag
    do
      eface:=FuncExpression(eSimp, eSet);
      pos:=Position(ListFacesFixedRank, eface);
      if pos=fail then
        Add(ListFacesFixedRank, eface);
        Add(ListSimplexContainingFace, [eSimp]);
      else
        Add(ListSimplexContainingFace[pos], eSimp);
      fi;
    od;
    Add(ListOfSet, eSet);
    Add(ListFacesBySet, ListFacesFixedRank);
    Add(ListSimplexContainingFaceBySet, ListSimplexContainingFace);
  od;
  FacesAsVertexSetBySet:=[];
  ToolForRankingVertexSetsBySet:=[];
  SpecifiedFlag:=ListFlag[1];
  ListRank:=[];
  nbClass:=0;
  ListVert:=Set(List(ListFlag, x->FuncExpression(x, eType)));
  for iPos in [1..Length(ListOfSet)]
  do
    SetOfFace:=[];
    for eSer in ListSimplexContainingFaceBySet[iPos]
    do
      ListPos:=[];
      for eF in eSer
      do
        AddSet(ListPos, Position(ListVert, FuncExpression(eF, eType)));
      od;
      Add(SetOfFace, ListPos);
      if Position(eSer, SpecifiedFlag)<>fail then
        Add(ToolForRankingVertexSetsBySet, ListPos);
      fi;
    od;
    if Length(Set(SetOfFace))<Length(SetOfFace) then
      Add(ListRank, -2);
    else
      nbClass:=nbClass+1;
      if ListOfSet[iPos]=eType then
        Add(ListRank, 0);
      else
        Add(ListRank, -1);
      fi;
    fi;
    Add(FacesAsVertexSetBySet, SetOfFace);
  od;
  Print("nbClass=", nbClass, "\n");
  for iPos in [1..Length(ListOfSet)]
  do
    if ListRank[iPos]<>-2 then
      Print("eSet=", ListOfSet[iPos], " ToolRank=", ToolForRankingVertexSetsBySet[iPos], "\n");
    fi;
  od;
  Print("ToolForRanking=", ToolForRankingVertexSetsBySet, "\n");
  nbRanked:=1;
  nbIter:=1;
  while(nbRanked<nbClass)
  do
    nbIter:=nbIter+1;
    if nbIter > 100 then
      return false;
    fi;
    Print("nbRanked=", nbRanked, " nbClass=", nbClass, "\n");
    for iPos in [1..Length(ListOfSet)]
    do
      if ListRank[iPos]=-1 then
        MaxFoundRankSubset:=0;
        Rankable:=true;
        for jPos in Difference([1..Length(ListOfSet)], [iPos])
        do
          if IsSubset(ToolForRankingVertexSetsBySet[iPos], ToolForRankingVertexSetsBySet[jPos])=true and Rankable=true then
            if ListRank[jPos]=-1 then
              Rankable:=false;
            else
              if ListRank[jPos]>=0 then
                MaxFoundRankSubset:=Maximum(MaxFoundRankSubset, ListRank[jPos]);
              fi;
            fi;
          fi;
        od;
        if Rankable=true then
          ListRank[iPos]:=MaxFoundRankSubset+1;
          nbRanked:=nbRanked+1;
        fi;
      fi;
    od;
  od;
  ListFaces:=[];
  for iRank in [1..n+1]
  do
    Add(ListFaces, []);
  od;
  for iPos in [1..Length(ListOfSet)]
  do
    if ListRank[iPos]<>-2 then
      for eSet in FacesAsVertexSetBySet[iPos]
      do
        pos:=ListRank[iPos]+1;
        if pos > Length(ListFaces) then
          return false;
        fi;
        Add(ListFaces[pos], eSet);
      od;
    fi;
  od;
  Gens:=GeneratorsOfGroup(GroupEXT);
  NewGens:=[];
  for eGen in Gens
  do
    LPerm:=[];
    for iVert in [1..Length(ListVert)]
    do
      eVert:=OnTuplesSets(ListVert[iVert], eGen);
      Add(LPerm, Position(ListVert, eVert));
    od;
    Add(NewGens, PermList(LPerm));
  od;
  if Length(NewGens)=0 then
    NewGroupEXT:=Group(());
  else
    NewGroupEXT:=Group(NewGens);
  fi;
  return rec(ListFaces:=ListFaces, GroupEXT:=NewGroupEXT);
end;
