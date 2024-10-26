LoadPackage("hapcryst");
LoadPackage("polyhedral");

minetohis:=function(mat)
    local   rows,  cols,  hismat,  length;
    
    if IsMatrix(mat)
       then
        rows:=Size(mat);
        cols:=Size(mat[1]);
        if not (ForAll(mat{[1..rows-1]}[cols],x->x=0) and mat[rows][cols]=1)
           then
            Error("no affine matrix in my format");
        fi;
        hismat:=NullMat(rows,cols);
        hismat[1]{[2..cols]}:=mat[rows]{[1..cols-1]};
        hismat[1][1]:=1;
        hismat{[2..rows]}{[2..cols]}:=mat{[1..rows-1]}{[1..cols-1]};
    elif IsVector(mat)
      then
        length:=Size(mat);
        if not mat[length]=1
           then
            Error("vector not affine enough");
        fi;
        hismat:=NullMat(1,length);
        hismat[1]:=1;
        hismat{[2..length]}:=mat{[1..length-1]};
    fi;
    return hismat;
end;


histomine:=function(hismat)
    local   rows,  cols,  mymat,  length;
    
    if IsMatrix(hismat)
       then
        rows:=Size(hismat);
        cols:=Size(hismat[1]);
        if not (ForAll(hismat[1]{[2..cols]},x->x=0) and hismat[1][1]=1)
           then
            Error("no affine matrix in Mathieu's format");
        fi;
        mymat:=NullMat(rows,cols);
        mymat[rows]{[1..cols-1]}:=hismat[1]{[2..cols]};
        mymat[rows][cols]:=1;
        mymat{[1..rows-1]}{[1..cols-1]}:=hismat{[1..rows]}{[1..cols]};
    elif IsVector(hismat)
      then
        length:=Size(hismat);
        if not hismat[1]=1
           then
            Error("vector not affine enough");
        fi;
        mymat:=NullMat(1,length);
        mymat[1]:=1;
        mymat{[1..length-1]}:=hismat{[2..length]};
    fi;
    return mymat;
end;



FDmathieu:=function(vector,G)
    local   dim,  GramMat,  affvec,  cslist,  MatrixGRP,  AffineGroup,  
            ListCosets,  ListFunc,  verts;
    Print("==============\n");
    dim:=DimensionOfMatrixGroup(G);
      #find invariant scalar product:
    GramMat:=GramianOfAverageScalarProductFromFiniteMatrixGroup(PointGroup(G));
    
      #convert vector to (my) affine form
    affvec:=Concatenation(vector,[1]);
    
      #find a list of coset representatives:
    cslist:=List(PointGroupRepresentatives(G),i->minetohis(affvec*i));
          
      # now cut&paste from  Mathieu's code:
    #    MatrixGRP:=Method2AutomorphismLattice(GramMat);
    AffineGroup:=Group(List(GeneratorsOfGroup(G),minetohis));
#    AffineGroup:=Group(List(GeneratorsOfGroup(MatrixGRP),x->FuncCreateBigMatrix(ListWithIdenticalEntries(Length(GramMat),0), x)));
    ListCosets:=Set(cslist,PeriodicVectorMod1);
    Exec("date");
    ListFunc:=Periodic_NonirreducibleDelaunayComputationStandardFunctions(rec(GramMat:=GramMat, ListCosets:=ListCosets));
#    ListFunc:=Periodic_DelaunayComputationStandardFunctions(rec(GramMat:=GramMat, ListCosets:=ListCosets));
    Exec("date");
    Print("== Getting Voronoi vertices ==\n");
    verts:=ListFunc.GetVoronoiVertices();
    Print("Getting vertices for given vector\n");
    return rec(Vert:=verts.GetVoronoi(Concatenation([1],vector)), ListFunc:=ListFunc);
end;


testFundamentalDomains:=function(vector,G)
    local   dim,  Mathieusvertices,  FDhapcryst;
    dim:=Size(vector);
    Mathieusvertices:=List(FDmathieu(vector,G),v->v{[2..dim]});
    Print("now do the same using HAPcryst\n");
    Exec("date");
    FDhapcryst:=FundamentalDomainBieberbachGroup(vector,G);
    Exec("date");
    if Set(Polymake(FDhapcryst,"VERTICES"))=Set(Mathieusvertices)
       then
        Print("vertices are equal! ");
        return true;
    else
        Print("ALLES KAPUTT\n");
        return fail;
    fi;
end;
    
#Print("First, a simple example, dimension 3 and identity Gram matrix: \n");
#group:=SpaceGroup(3,4);
#FDmathieu([0,0,0],group);
#
#Print("Now a non-identity Gram matrix\n");
#G:=SpaceGroup(3,165);
#FDmathieu([0,0,0],G);
#FRS:=FDmathieu([1/3,1/2,1/7,8/9],SpaceGroup(4,4));
#FRS:=FDmathieu([1/3,1/2,1/7,8/9],SpaceGroup(4,4139));
FRS:=FDmathieu([0,0,0,0],SpaceGroup(4,3047));
