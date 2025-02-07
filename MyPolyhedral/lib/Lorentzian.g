FileVIN_ComputeDomain:=GetBinaryFilename("LORENTZ_FundDomain_Vinberg");
FileEDGEWALK_ComputeDomain:=GetBinaryFilename("LORENTZ_FundDomain_AllcockEdgewalk");
FileCOXDYN_ComputeSymbol:=GetBinaryFilename("COXDYN_ComputeSymbol");
FileCOXDYN_FindExtensionsCoxMat:=GetBinaryFilename("COXDYN_FindExtensionsCoxMat");
FileComputeRootsVertex:=GetBinaryFilename("LORENTZ_ComputeRoots_Vertex");


LORENTZ_TerminateIfNotLorentzian:=function(LorMat)
    local DiagInfo;
    DiagInfo:=DiagonalizeSymmetricMatrix(LorMat);
    if DiagInfo.nbZero<>0 or DiagInfo.nbMinus<>1 then
        Print("nbZero=", DiagInfo.nbZero, " nbMinus=", DiagInfo.nbMinus, " nbPlus=", DiagInfo.nbPlus, "\n");
        Error("We should have nbZero=0 and nbMinus=1 according to the convention of Lorentzian geometry");
    fi;
end;



LORENTZ_GetSymbolName:=function(LorMat, ListRoot)
    local FileLorMat, FileListRoot, FileOut, eCommand, TheReply;
    FileLorMat:=Filename(POLYHEDRAL_tmpdir,"symbol.lormat");
    FileListRoot:=Filename(POLYHEDRAL_tmpdir,"symbol.listroot");
    FileOut:=Filename(POLYHEDRAL_tmpdir,"symbol.out");
    SYMPOL_PrintMatrix(FileLorMat, LorMat);
    SYMPOL_PrintMatrix(FileListRoot, ListRoot);
    #
    eCommand:=Concatenation(FileCOXDYN_ComputeSymbol, " ", FileLorMat, " ", FileListRoot, " ", FileOut);
#    Print("eCommand=", eCommand, "\n");
    Exec(eCommand);
    #
    TheReply:=ReadAsFunction(FileOut)();
    RemoveFile(FileLorMat);
    RemoveFile(FileListRoot);
    RemoveFile(FileOut);
    return TheReply;
end;


LORENTZ_GetListExtensionsCoxMat:=function(CoxMat)
    local FileCoxMat, FileOut, eCommand, ListExtensions;
    FileCoxMat:=Filename(POLYHEDRAL_tmpdir,"ExtendCoxMat.coxmat");
    FileOut:=Filename(POLYHEDRAL_tmpdir,"ExtendCoxMat.out");
    SYMPOL_PrintMatrix(FileCoxMat, CoxMat);
    #
    eCommand:=Concatenation(FileCOXDYN_FindExtensionsCoxMat, " ", FileCoxMat, " euclidean lorentzian ", FileOut);
    Exec(eCommand);
    #
    ListExtensions:=ReadAsFunction(FileOut)();
    RemoveFile(FileCoxMat);
    RemoveFile(FileOut);
    return ListExtensions;
end;


LORENTZ_WriteInitialVertex:=function(eFile, TheRec)
    local len, output, i;
    RemoveFileIfExist(eFile);
    output:=OutputTextFile(eFile, true);
    SYMPOL_PrintVectorStream(output, TheRec.gen);
    SYMPOL_PrintMatrixStream(output, TheRec.l_roots);
    CloseStream(output);
end;


LORENTZ_ReadInitialVertex:=function(eFile)
    local eList, eVertex, dim, n_root, MatRoot;
    eList:=ReadVectorFile(eFile);
    eVertex:=eList[2];
    dim:=Length(eVertex);
    if eList[1][1] <>dim then
        Error("Inconsistency 1");
    fi;
    n_root:=eList[3][1];
    if eList[3][2] <>dim then
        Error("Inconsistency 2");
    fi;
    if Length(eList)<>n_root+3 then
        Error("Inconsistency 2");
    fi;
    MatRoot:=eList{[4..n_root+3]};
    return rec(gen:=eVertex, l_roots:=MatRoot);
end;

LORENTZ_WriteSingleEdgewalkInput:=function(FileSave, NewRec)
    local output, eNorm;
    RemoveFileIfExist(FileSave);
    output:=OutputTextFile(FileSave, true);
    SYMPOL_PrintMatrixStream(output, NewRec.G);
    AppendTo(output, Length(NewRec.l_norms));
    for eNorm in NewRec.l_norms
    do
        AppendTo(output, " ", eNorm);
    od;
    SYMPOL_PrintVectorStream(output, NewRec.k);
    SYMPOL_PrintVectorStream(output, NewRec.ad.v_disc);
    SYMPOL_PrintMatrixStream(output, NewRec.ad.l_ui);
    #
    SYMPOL_PrintVectorStream(output, NewRec.vert_expect.gen);
    SYMPOL_PrintMatrixStream(output, NewRec.vert_expect.l_roots);
    CloseStream(output);
end;

# This is for debugging of course
LORENTZ_FindAllCoxeterSubdiagrams:=function(CoxMat)
    local len, i, fc, ePerm, NewCoxMat, CoxMatRed, eLine, ListRec, eRec;
    len:=Length(CoxMat);
    ListRec:=[];
    for i in [1..len]
    do
        if i=len then
            ePerm:=();
        else
            ePerm:=(i,len);
        fi;
        fc:=function(eList)
            return Permuted(eList, ePerm);
        end;
        NewCoxMat:=fc(List(CoxMat, fc));
        CoxMatRed:=List(NewCoxMat{[1..len-1]}, x->x{[1..len-1]});
        eLine:=NewCoxMat[len]{[1..len-1]};
        eRec:=rec(CoxMat:=CoxMatRed, eLine:=eLine);
        Add(ListRec, eRec);
    od;
    return ListRec;
end;



LORENTZ_GetIsotropicGram_K3:=function(n)
    local TheMat, i, j;
    TheMat:=NullMat(n,n);
    for i in [1..n]
    do
        for j in [1..n]
        do
            if i<>j then
                TheMat[i][j]:=1;
            fi;
        od;
    od;
    if n=9 then
        TheMat[1][2]:=2;
        TheMat[2][1]:=2;
    fi;
    if n=10 then
        TheMat[1][2]:=2;
        TheMat[2][1]:=2;
        TheMat[1][3]:=2;
        TheMat[3][1]:=2;
    fi;
    return TheMat;
end;


LORENTZ_GetIsotropicGram_K3_bis:=function(n)
    local GramIso, i, j, ListVect, TheBasis, TheGram;
    GramIso:=NullMat(n,n);
    for i in [1..n]
    do
        for j in [1..n]
        do
            if i<>j then
                GramIso[i][j]:=1;
            fi;
        od;
    od;
    ListVect:=IdentityMat(n);
    Add(ListVect, ListWithIdenticalEntries(n,1/3));
    TheBasis:=GetZbasis(ListVect);
    TheGram:=TheBasis * GramIso * TransposedMat(TheBasis);
    return rec(TheGram:=TheGram, TheBasis:=TheBasis, TheBasisInv:=Inverse(TheBasis), GramIso:=GramIso);
end;


LORENTZ_GetReflection:=function(LorMat, eRoot)
    local n, eNorm, TheMat, eLine, eScal, fLine;
    n:=Length(eRoot);
    eNorm:=eRoot * LorMat * eRoot;
    TheMat:=[];
    for eLine in IdentityMat(n)
    do
        eScal:=eLine * LorMat * eRoot;
        fLine:=eLine - 2 * (eScal / eNorm) * eRoot;
        Add(TheMat, fLine);
    od;
    if eRoot*TheMat<>-eRoot then
        Error("TheMat does not reflect eRoot");
    fi;
    if IsIntegralMat(TheMat)=false then
        Error("TheMat should be integral");
    fi;
    if TheMat*TheMat<>IdentityMat(n) then
        Error("The matrix TheMat *TheMat is not the identity");
    fi;
    return TheMat;
end;



LORENTZ_FundamentalDomainReduction:=function(LorMat, ListRoot)
    local n, ListIneq, ListTransform, eRoot, eNorm, TheMatrix, EXT, CentVect, max_scal, min_scal;
    LORENTZ_TerminateIfNotLorentzian(LorMat);
    n:=Length(LorMat);
    ListIneq:= - ListRoot * LorMat;
    ListTransform:=[];
    for eRoot in ListRoot
    do
        eNorm:=eRoot * LorMat * eRoot;
        TheMatrix:=LORENTZ_GetReflection(LorMat, eRoot);
        Add(ListTransform, TheMatrix);
    od;
    EXT:=DualDescription(ListIneq);
    CentVect:=Sum(EXT);
    return function(eVect)
        local eVectWork, NewVectWork, DoSomething, i, eScal, Algo1, Algo2, Algo3, MainScal, NewScal, ListScal, MinScal, pos, eSol, eBasis;
        eVectWork:=StructuralCopy(eVect);
        while(true)
        do
#            Print("eVectWork=", eVectWork, "\n");
            Algo3:=true;
            if Algo3 then
                MainScal:=eVectWork * LorMat * CentVect;
#                Print("MainScal=", MainScal, "\n");
                DoSomething:=false;
                for i in [1..Length(ListRoot)]
                do
                    NewVectWork:=eVectWork * ListTransform[i];
                    NewScal:=NewVectWork * LorMat * CentVect;
                    if NewScal < MainScal then
                        eVectWork:=NewVectWork;
                        MainScal:=NewScal;
#                        Print("Now MainScal=", MainScal, "\n");
                        DoSomething:=true;
                    fi;
                od;
                if DoSomething=false then
                    ListScal:=List(ListIneq, x->x * eVectWork);
                    max_scal:=Maximum(ListScal);
                    min_scal:=Minimum(ListScal);
                    if max_scal=0 and min_scal<0 then
                        return -eVectWork;
                    fi;
                    if max_scal>0 and min_scal=0 then
                        return eVectWork;
                    fi;
                    Error("We cannot conclude because we cannot improve upon the scalar product");
                fi;
            fi;
            Algo2:=false;
            if Algo2 then
                ListScal:=List(ListIneq, x->x * eVectWork);
                MinScal:=Minimum(ListScal);
                if MinScal >= 0 then
                    return eVectWork;
                fi;
                pos:=Position(ListScal, MinScal);
                Print("pos=", pos, "\n");
                eVectWork:=eVectWork * ListTransform[pos];
            fi;
            Algo1:=false;
            if Algo1 then
                DoSomething:=false;
                for i in [1..Length(ListRoot)]
                do
                    if DoSomething=false then
                        eRoot:=ListRoot[i];
                        eScal:=eVectWork * ListIneq[i];
                        if eScal < 0 then
                            Print("i=", i, " eScal=", eScal, "\n");
                            eBasis:=Concatenation([eRoot], NullspaceIntMat(TransposedMat([eRoot*LorMat])));
                            eSol:=SolutionMat(eBasis, eVectWork);
#                        Print("  eSol=", eSol, "\n");
                            eVectWork:=eVectWork * ListTransform[i];
                            DoSomething:=true;
                        fi;
                    fi;
                od;
                if DoSomething=false then
                    return eVectWork;
                fi;
            fi;
        od;
    end;
end;




LORENTZ_ComputeRoots_Vertex:=function(LorMat, gen)
    local FileRootComputeLorMat, FileRootComputeOutput, FileRootComputeVertex, output, n, i, j, eVal, eCommand, TheReply, eVect, eProg;
    LORENTZ_TerminateIfNotLorentzian(LorMat);
    FileRootComputeLorMat:=Filename(POLYHEDRAL_tmpdir,"RootCompute.lormat");
    FileRootComputeVertex:=Filename(POLYHEDRAL_tmpdir,"RootCompute.vertex");
    FileRootComputeOutput:=Filename(POLYHEDRAL_tmpdir,"RootCompute.output");
    RemoveFileIfExist(FileRootComputeLorMat);
    RemoveFileIfExist(FileRootComputeVertex);
    RemoveFileIfExist(FileRootComputeOutput);
    #
    output:=OutputTextFile(FileRootComputeVertex, true);
    n:=Length(LorMat);
    AppendTo(output, n, "\n");
    for i in [1..n]
    do
        eVal:=gen[i];
        AppendTo(output, " ", eVal);
    od;
    AppendTo(output, "\n");
    CloseStream(output);
    #
    output:=OutputTextFile(FileRootComputeLorMat, true);
    n:=Length(LorMat);
    AppendTo(output, n, " ", n, "\n");
    for i in [1..n]
    do
        for j in [1..n]
        do
            eVal:=LorMat[i][j];
            AppendTo(output, " ", eVal);
        od;
        AppendTo(output, "\n");
    od;
    CloseStream(output);
    eCommand:=Concatenation(FileComputeRootsVertex, " ", FileRootComputeLorMat, " ", FileRootComputeVertex, " ", FileRootComputeOutput);
    Print("eCommand=", eCommand, "\n");
    Exec(eCommand);
    TheReply:=ReadAsFunction(FileRootComputeOutput)();
    RemoveFileIfExist(FileRootComputeLorMat);
    RemoveFileIfExist(FileRootComputeVertex);
    RemoveFileIfExist(FileRootComputeOutput);
    return TheReply;
end;


# This version works only if Subspace1 is a codimension 1 subspace.
LORENTZ_ExtendOrthogonalIsotropicIsomorphism_Dim1:=function(G1, Subspace1, G2, Subspace2)
    local dim, Compl1, eVect1, eNorm, eProd1, eProd2, Vscal, V0, NSP, V1, eNorm_V1, scal0, scal1, tVal, eVect2, Trans1, Trans2, eEquiv, eInv, G1_tr;
    dim:=Length(G1);
    Compl1:=SubspaceCompletionRational(Subspace1, dim);
    if Length(Compl1)<>1 then
        Error("Compl1 should be of length 1");
    fi;
    eVect1:=Compl1[1];
    eNorm:=eVect1 * G1 * eVect1;
    eProd1 := Subspace1 * G1;
    eProd2 := Subspace2 * G2;
    Vscal:=List(eProd1, x->x*eVect1);
    V0:=SolutionMat(TransposedMat(eProd2), Vscal);
    if V0=fail then
        Error("The solutionning failed");
    fi;
    NSP:=NullspaceMat(TransposedMat(eProd2));
    if Length(NSP)<>1 then
        Error("NSP should have length 1");
    fi;
    V1:=NSP[1];
    eNorm_V1 := V1 * G2 * V1;
    if eNorm_V1<>0 then
        Error("V1 should be an isotrop vector");
    fi;
    scal0 := eNorm - V0 * G2 * V0;
    scal1 := 2 * (V0 * G2 * V1);
    if scal1=0 then
        Error("scal1 should be non-zero");
    fi;
    tVal:=scal0 / scal1;
    eVect2:=V0 + tVal * V1;
    Trans1:=Concatenation(Subspace1, [eVect1]);
    Trans2:=Concatenation(Subspace2, [eVect2]);
    eEquiv:=Inverse(Trans1) * Trans2;
    eInv:=Inverse(eEquiv);
    G1_tr:=eInv * G1 * TransposedMat(eInv);
    if G1_tr<>G2 then
        Error("G1 was not mapped to G2");
    fi;
    if Subspace1*eEquiv <> Subspace2 then
        Error("Subspace1 is not mapped to Subspace2");
    fi;
    return eEquiv;
end;

# Resolution of B = X A + A^T X^T
# b_{ij} = sum_k x_{ik} a_{kj} + a_{ki} x_{jk}
SpecialEquationSolving:=function(Amat, Bmat)
    local dim, TheMat, Bvect, f, i, j, u, k, v1, v2, f_getmat, eSol_vect, eSol_mat, BasisKernel, NSP, eVect, eMat;
    dim:=Length(Bmat);
    TheMat:=NullMat(dim * dim, dim * dim);
    Bvect:=ListWithIdenticalEntries(dim * dim, 0);
    f:=function(i, j)
        return i + dim * (j-1);
    end;
    for i in [1..dim]
    do
        for j in [1..dim]
        do
            u:=f(i,j);
            Bvect[u] := Bmat[i][j];
            for k in [1..dim]
            do
                # contribudion x_{ik} a_{kj}
                v1:=f(i, k);
                TheMat[v1][u] := TheMat[v1][u] + Amat[k][j];
                # contribution a_{ki} x_{jk}
                v2:=f(j, k);
                TheMat[v2][u] := TheMat[v2][u] + Amat[k][i];
            od;
        od;
    od;
    f_getmat:=function(eVect)
        local eMat, i, j;
        eMat:=NullMat(dim, dim);
        for i in [1..dim]
        do
            for j in [1..dim]
            do
                eMat[i][j] := eVect[f(i,j)];
            od;
        od;
        return eMat;
    end;
    eSol_vect:=SolutionMat(TheMat, Bvect);
    eSol_mat:=f_getmat(eSol_vect);
    if Bmat<>eSol_mat * Amat + TransposedMat(Amat) * TransposedMat(eSol_mat) then
        Error("Failed to find the correct solution 1");
    fi;
    BasisKernel:=[];
    NSP:=NullspaceMat(TheMat);
    for eVect in NSP
    do
        eMat:=f_getmat(eVect);
        if NullMat(dim,dim)<>eMat * Amat + TransposedMat(Amat) * TransposedMat(eMat) then
            Error("Failed to find the correct solution 2");
        fi;
        Add(BasisKernel, eMat);
    od;
    return rec(BasisKernel:=BasisKernel, eSol_mat:=eSol_mat);
end;



# Resolution of B = X A + A^T X^T
# b_{ij} = sum_k x_{ik} a_{kj} + a_{ki} x_{jk}
# with the constraint that C + X D in M_n(Z)
SpecialEquationSolving_Integral:=function(Amat, Bmat, Cmat, Dmat)
    local dim, eRec, f, f_getmat, f_vect, Zmat_v, List_BasisKernel_v, eRecInt;
    dim:=Length(Amat);
    eRec:=SpecialEquationSolving(Amat, Bmat);
    #
    f:=function(i, j)
        return i + dim * (j-1);
    end;
    f_getmat:=function(eVect)
        local eMat, i, j;
        eMat:=NullMat(dim, dim);
        for i in [1..dim]
        do
            for j in [1..dim]
            do
                eMat[i][j] := eVect[f(i,j)];
            od;
        od;
        return eMat;
    end;
    f_vect:=function(eMat)
        local Bvect, i, j, u;
        Bvect:=ListWithIdenticalEntries(dim * dim, 0);
        for i in [1..dim]
        do
            for j in [1..dim]
            do
                u:=f(i,j);
                Bvect[u] := Bmat[i][j];
            od;
        od;
        return Bvect;
    end;
    # Write X = X0 + y1 X_1 + ..... y_p X_p
    # C + X D
    # Equation rewritten as Z + y Zb
    # The question is then to find the y such that Z + yZb is integral
    Zmat_v := f_vect(Cmat + eRec.eSol_mat * Dmat);
    List_BasisKernel_v:=List(eRec.BasisKernel, x->f_vect(x * Dmat));
    eRecInt:=IntegralLinearSpace(Zmat_v, List_BasisKernel_v);
    # CODE Needs to be written if it is needed
end;



# Define the matrix
# J(d1, ...., dK) with entries d1, ...., dK on the diagonal.
# The Gram matrices is expressed as
# | 0 J 0 |
# | J 0 0 |
# | 0 0 A |
#
# When restricting to space (dim1+1....n) the matrix is
# | 0 0 |
# | 0 A |
# Write the matrix is written as
# / P1  P2 \    / 0 0 \   / P1^T P3^T \
# \ P3  P4 /    \ 0 A /   \ P2^T P4^T /
# =  / 0 P2 A \  / P1^T P3^T \
#    \ 0 P4 A /  \ P2^T P4^T /
# =  / P2 A P2^T   P2 A P4^T \
#    \ P4 A P2^T   P4 A P4^T /
# Which should equal the original matrix 0, 0, 0, A.
# This implies P2 = 0
# When extending to a full matrix the partial transformation we get something like
# / Q1 Q5 Q6 \
# | Q2 P1 0  |
# \ Q3 P3 P4 /
# The vectors (0 X2 X3 ) has to be mapped to (0 * *)
# Therefore Q2 = 0, Q3 = 0
# The product is then expressed as
# / Q1 Q5 Q6 \   / 0 J 0 \   / Q1^T 0    0    \
# | 0  P1 0  |   | J 0 0 |   | Q5^T P1^T P3^T |
# \ 0  P3 P4 /   \ 0 0 A /   \ Q6^T 0    P4^T /
# This simplifies to
# / Q5 J  Q1 J  Q6 A  \   / Q1^T 0    0    \
# | P1 J  0     0     |   | Q5^T P1^T P3^T |
# \ P3 J  0     P4 A  /   \ Q6^T 0    P4^T /
# further it is:
# /  Q5 J Q1^T + Q1 J Q5^T + Q6 A Q6^T      Q1 J P1^T    Q1 J P3^T + Q6  A P4^T   \
# |  P1 J Q1^T                              0            0                        |
# \  P3 J Q1^T + P4 A Q6^T                  0            P4 A P4^T                /
# We therefore need to have
# Q1 J P1^T = J  <===>  P1 J Q1^T = J
# Q1 J P3^T + Q6  A P4^T = 0
# Q5 J Q1^T + Q1 J Q5^T + Q6 A Q6^T = 0
# Q5 P1^{-1} J + J P1^{-T} Q5^T + Q6 A Q6^T = 0
# If d is the denominator of J^{-1} then Q1 is in M_*(Z) / d
#    because of the formula Q1 = J P1^{-T} J^{-1}
# If d' is the denominator of A^{-1} then Q6 is in M_*(Z) / (d d')
#    because of the formula Q6 = - (Q1 J P3^T) P4^{-T} A^{-1}
# We then have Q6 A Q6^T is in M_*(Z) / (d d d')
#    The A J + J A matrix will get us denominators 1 / (2d)
#    So in the end we get 1 / (2 d d d d')
# Q5 is undefined by the equation
# Below P2 is undefined
# / P1 P2 P3 \   / Q1 Q2 Q3 \     / P1 Q1    P1 Q2 + P2 Q4 + P3 Q5     P1 Q3 + P3 Q6   \
# | 0  P4 0  |   | 0  Q4 0  |  =  | 0        P4 Q4                     0               |
# \ 0  P5 P6 /   \ 0  Q5 Q6 /     \ 0        P5 Q4 + P6 Q5             P6 Q6           /
# So, the coefficient P2 remains in the same quotient space.


# Subspace1 and Subspace2 are in the orthogonal of a K-space of isotropic vectors.
# Subspace1 is a list of vectors and Subspace2 another list of vectors.
# We build a full dimensional orthogonal mapping that maps 1 on 2.
# and that is an orthogonal transformation mapping G1 to G2.
#
# The returned extension is not unique if Subspace1 / Subspace2 have codimension > 1.
LORENTZ_ExtendOrthogonalIsotropicIsomorphism:=function(G1, Subspace1, G2, Subspace2)
    local dim, rnk, dimSpace, dimCompl, TheCompl1, TheCompl2, eVect1, eProd1, eProd2, Vscal, NSP1, NSP2, ProdMat1, ProdMat2, eVect2, Trans1, Trans1Inv, Trans2, eEquiv, eEquivInv, MatScal1, MatScal2, MatScalCand2, G1_tr, ListVectCand2, DiffScal, LambdaMat, LScal1, LScal2, eVectCand2, SMat1, SMat2, denomSol, test_transformation, check_transformation, get_one_transformation, get_kernel_generating_set;
    dim:=Length(G1);
    rnk:=RankMat(Subspace1);
#    Print("------------------------------\n");
#    Print("Subspace1:=", Subspace1, ";\n");
#    Print("Subspace2:=", Subspace2, ";\n");
    if Length(Subspace1)<>rnk then
        Error("Inconsistent input: We should have Subspace1 of full rank");
    fi;
    dimSpace:=rnk;
    dimCompl:=dim - dimSpace;
#    Print("dim:=", dim, ", dimSpace:=", dimSpace, ", dimCompl:=", dimCompl, ";\n");
    # Checking the input
    eProd1:=Subspace1 * G1;
    eProd2:=Subspace2 * G2;
    NSP1:=NullspaceMat(TransposedMat(eProd1));
    ProdMat1:=NSP1 * G1 * TransposedMat(NSP1);
    if ProdMat1<>NullMat(dimCompl,dimCompl) then
        Error("Inconsistent input: ProdMat1 should be equal to zero");
    fi;
    NSP2:=NullspaceMat(TransposedMat(eProd2));
    ProdMat2:=NSP2 * G2 * TransposedMat(NSP2);
    if ProdMat2<>NullMat(dimCompl,dimCompl) then
        Error("Inconsistent input: ProdMat2 should be equal to zero");
    fi;
    SMat1:=Subspace1 * G1 * TransposedMat(Subspace1);
    SMat2:=Subspace2 * G2 * TransposedMat(Subspace2);
    if SMat1<>SMat2 then
        Error("Inconsistent input: SMat1 should be equal to SMat2");
    fi;
    # Now doing the computation side of the job
    TheCompl1:=SubspaceCompletionRational(Subspace1, dim);
    Trans1:=Concatenation(Subspace1, TheCompl1);
    Trans1Inv:=Inverse(Trans1);
    MatScal1:=TheCompl1 * G1 * TransposedMat(TheCompl1);
    ListVectCand2:=[];
    for eVect1 in TheCompl1
    do
        Vscal:=List(eProd1, x->x*eVect1);
        eVectCand2:=SolutionMat(TransposedMat(eProd2), Vscal);
        if eVectCand2 = fail then
            Error("The solutionning failed");
        fi;
        LScal1:=List(Subspace1, x->x * G1 * eVect1);
        LScal2:=List(Subspace2, x->x * G2 * eVectCand2);
        if LScal1<>LScal2 then
            Error("Inconsistency for LScal1 = LScal2");
        fi;
        Add(ListVectCand2, eVectCand2);
    od;
    # The solutions are written as
    # eVect2 = eVectCand2 + c_vect * NSP2
    # Putting together this gets ListVect2 = TheCompl2 = ListVectCand2 + c_Mat * NSP2
    # MatScal2 = (ListVectCand2 + c_Mat * NSP2) * G2 * (NSP2^T * c_Mat^T + ListVectCand2^T)
    #          = ListVectCand2 * G2 * ListVectCand2^T + c_Mat * NSP2 * G2 * ListVectCand2^T + ListVectCand2 * G2 * NSP2^T * c_Mat^T
    # c_vect is a vector of length dimCompl which gets into
    # Put all together, this gets us c_Mat a matrix of size (dimCompl, dimCompl)
    # The equation that we get is thus of the form B = X A + A^T X^T
    # The equation is underdefined. This is because B is symmetric and so we have n(n+1)/2 equations
    # for n^2 unknowns.
    # The space NSP2 is uniquely defined as the set of isotropic vectors in the space. It is defined
    # as a Kernel.
    MatScalCand2:=ListVectCand2 * G2 * TransposedMat(ListVectCand2);
    LambdaMat := NSP2 * G2 * TransposedMat(ListVectCand2);
    denomSol:=GetDenominatorQuotientSolution(LambdaMat);
    DiffScal:=MatScal1 - MatScalCand2;
    test_transformation:=function(eEq)
        local eEqInv, G1_tr;
        eEqInv:=Inverse(eEq);
        G1_tr:=eEqInv * G1 * TransposedMat(eEqInv);
        if G1_tr<>G2 then
            Print("G1 was not mapped to G2\n");
            return false;
        fi;
        if Subspace1*eEq <> Subspace2 then
            Print("Subspace1 is not mapped to Subspace2\n");
            return false;
        fi;
        return true;
    end;
    check_transformation:=function(eEq)
        if test_transformation(eEq)=false then
            Error("Something wrong happened");
        fi;
    end;
    get_one_transformation:=function()
        local TheRec, f_get_equiv, eEquiv0, ListEquiv_terms, eEquiv0_v, ListEquiv_terms_v, TheSol, RetSol;
        TheRec:=SpecialEquationSolving(LambdaMat, DiffScal);
        f_get_equiv:=function(eSol)
            local TheCompl2, Trans2;
            TheCompl2:=ListVectCand2 + eSol * NSP2;
            Trans2:=Concatenation(Subspace2, TheCompl2);
            return Trans1Inv * Trans2;
        end;
        eEquiv0:=f_get_equiv(TheRec.eSol_mat);
        ListEquiv_terms:=List(TheRec.BasisKernel, x->Trans1Inv * Concatenation(NullMat(rnk, dim), x * NSP2));
        # The matrix is expressed as eEquiv0 + alpha1 ListEquiv_terms[1] + ..... + alphaN ListEquiv_terms[N]
        RetSol:=EliminateSuperfluousPrimeDenominators_Matrix(eEquiv0, ListEquiv_terms);
        check_transformation(RetSol);
        return RetSol;
    end;
    get_kernel_generating_set:=function(d)
        local TheRec, ListEquiv_terms1, ListEquiv_terms2, ListEquiv_terms3, ListEquiv_terms4, ListEquiv_terms5, eGen;
#        Print("Beginning of get_kernel_generating_set\n");
        if G1<>G2 or Subspace1<>Subspace2 then
            Error("We should have G1=G2 and Subspace1=Subspace2 in order for kernel to make sense");
        fi;
        TheRec:=SpecialEquationSolving(LambdaMat, DiffScal);
        ListEquiv_terms1:=List(TheRec.BasisKernel, x->Trans1Inv * Concatenation(NullMat(rnk, dim), x * NSP2));
        ListEquiv_terms2:=List(ListEquiv_terms1, MatrixToVector);
        ListEquiv_terms3:=IntegralSpaceSaturation(ListEquiv_terms2);
        ListEquiv_terms4:=List(ListEquiv_terms3, VectorToMatrix);
        ListEquiv_terms5:=List(ListEquiv_terms4, x->IdentityMat(dim) + x / d);
        for eGen in ListEquiv_terms5
        do
            check_transformation(eGen);
        od;
        return PersoGroupMatrix(ListEquiv_terms5, dim);
    end;
    return rec(denomSol:=denomSol,
               check_transformation:=check_transformation,
               get_one_transformation:=get_one_transformation,
               get_kernel_generating_set:=get_kernel_generating_set);
end;








LORENTZ_GetFundamentalDomain_Edgewalk_Kernel:=function(LorMat, RecOpt)
    local FileEdgewalkNML, FileEdgewalkLorMat, FileEdgewalkOutput, FileEdgewalkVertex, output, n, i, j, eVal, eCommand, TheReply, eVect, GetStringBool, eProg, FailAndContinue;
    LORENTZ_TerminateIfNotLorentzian(LorMat);
    FileEdgewalkNML:=Filename(POLYHEDRAL_tmpdir,"Edgewalk.nml");
    FileEdgewalkLorMat:=Filename(POLYHEDRAL_tmpdir,"Edgewalk.lormat");
    FileEdgewalkVertex:=Filename(POLYHEDRAL_tmpdir,"Edgewalk.vertex");
    FileEdgewalkOutput:=Filename(POLYHEDRAL_tmpdir,"Edgewalk.output");
    RemoveFileIfExist(FileEdgewalkNML);
    RemoveFileIfExist(FileEdgewalkLorMat);
    RemoveFileIfExist(FileEdgewalkVertex);
    RemoveFileIfExist(FileEdgewalkOutput);
    #
    FailAndContinue:=false;
    if IsBound(RecOpt.FailAndContinue) then
        FailAndContinue:=RecOpt.FailAndContinue;
    fi;
    #
    GetStringBool:=function(val)
        if val then
            return "T";
        else
            return "F";
        fi;
    end;
    output:=OutputTextFile(FileEdgewalkNML, true);
    AppendTo(output, "&PROC\n");
    AppendTo(output, " FileLorMat = \"", FileEdgewalkLorMat, "\"\n");
    if IsBound(RecOpt.InitialVertex) then
        AppendTo(output, " OptionInitialVertex = \"FileVertex\"\n");
        AppendTo(output, " FileInitialVertex = \"", FileEdgewalkVertex, "\"\n");
    else
        AppendTo(output, " OptionInitialVertex = \"vinberg\"\n");
    fi;
    AppendTo(output, " OutFormat = \"GAP\"\n");
    AppendTo(output, " FileOut = \"", FileEdgewalkOutput, "\"\n");
    if IsBound(RecOpt.OptionNorms) then
        AppendTo(output, " OptionNorms = \"", RecOpt.OptionNorms, "\"\n");
    else
        AppendTo(output, " OptionNorms = \"all\"\n");
    fi;
    if IsBound(RecOpt.EarlyTerminationIfNotReflective) then
        AppendTo(output, " EarlyTerminationIfNotReflective = ", GetStringBool(RecOpt.EarlyTerminationIfNotReflective), "\n");
    fi;
    if IsBound(RecOpt.ComputeAllSimpleRoots) then
        AppendTo(output, " ComputeAllSimpleRoots = ", GetStringBool(RecOpt.ComputeAllSimpleRoots), "\n");
    else
        AppendTo(output, " ComputeAllSimpleRoots = T\n");
    fi;
    AppendTo(output, "/\n");
    CloseStream(output);
    #
    if IsBound(RecOpt.InitialVertex) then
        output:=OutputTextFile(FileEdgewalkVertex, true);
        n:=Length(LorMat);
        AppendTo(output, n, "\n");
        for i in [1..n]
        do
            eVal:=RecOpt.InitialVertex[i];
            AppendTo(output, " ", eVal);
        od;
        AppendTo(output, "\n");
        CloseStream(output);
    fi;
    #
    output:=OutputTextFile(FileEdgewalkLorMat, true);
    n:=Length(LorMat);
    AppendTo(output, n, " ", n, "\n");
    for i in [1..n]
    do
        for j in [1..n]
        do
            eVal:=LorMat[i][j];
            AppendTo(output, " ", eVal);
        od;
        AppendTo(output, "\n");
    od;
    CloseStream(output);
    #
    if FailAndContinue then
        eProg:=Concatenation("ulimit -m 4194304 -v 4194304 && ", FileEDGEWALK_ComputeDomain);
    else
        eProg:=FileEDGEWALK_ComputeDomain;
    fi;
    eCommand:=Concatenation(FileEDGEWALK_ComputeDomain, " ", FileEdgewalkNML);
    Print("eCommand=", eCommand, "\n");
    Exec(eCommand);
    if IsExistingFile(FileEdgewalkOutput) then
        TheReply:=ReadAsFunction(FileEdgewalkOutput)();
        RemoveFile(FileEdgewalkNML);
        RemoveFile(FileEdgewalkLorMat);
        RemoveFile(FileEdgewalkOutput);
        return TheReply;
    fi;
    if FailAndContinue then
        return "fail";
    fi;
    Error("We have some bug to resolve");
end;

LORENTZ_GetFundamentalDomain_Edgewalk:=function(LorMat)
    local RecOpt;
    RecOpt:=rec();
    return LORENTZ_GetFundamentalDomain_Edgewalk_Kernel(LorMat, RecOpt);
end;



LORENTZ_NicePrinting:=function(FileSave, U)
    local output, nGen, iGen, eGen, eNorm, nVert, iVert, val;
    RemoveFileIfExist(FileSave);
    output:=OutputTextFile(FileSave, true);
    AppendTo(output, "LorMat=\n");
    WriteMatrix(output, U.LorMat);
    nGen:=Length(U.ListIsomCox);
    AppendTo(output, "Generators of Isom(L) / Cox(L). nGen=", nGen, "\n");
    for iGen in [1..nGen]
    do
        AppendTo(output, "iGen=", iGen, " / ", nGen, "\n");
        WriteMatrix(output, U.ListIsomCox[iGen]);
    od;
    nVert:=Length(U.ListVertices);
    AppendTo(output, "List of vertices nVert=", nVert, "\n");
    for iVert in [1..nVert]
    do
        AppendTo(output, "iVert=", iVert, " / ", nVert, "\n");
        AppendTo(output, "gen=");
        eGen:=U.ListVertices[iVert].gen;
        for val in eGen
        do
            AppendTo(output, " ", val);
        od;
        eNorm:=eGen * U.LorMat * eGen;
        AppendTo(output, "  norm=", eNorm, "\n");
        AppendTo(output, "List of incident roots=\n");
        WriteMatrix(output, U.ListVertices[iVert].l_roots);
    od;
    CloseStream(output);
end;







LORENTZ_GetFundamentalDomain:=function(LorMat)
    local FileVinNML, FileVinLorMat, FileVinOutput, output, n, i, j, eVal, eCommand, TheReply, eVect;
    LORENTZ_TerminateIfNotLorentzian(LorMat);
    FileVinNML:=Filename(POLYHEDRAL_tmpdir,"Vinberg.nml");
    FileVinLorMat:=Filename(POLYHEDRAL_tmpdir,"Vinberg.lormat");
    FileVinOutput:=Filename(POLYHEDRAL_tmpdir,"Vinberg.output");
    #
    output:=OutputTextFile(FileVinNML, true);
    AppendTo(output, "&PROC\n");
    AppendTo(output, " FileLorMat = \"", FileVinLorMat, "\"\n");
    AppendTo(output, " FileV0 = \"compute\"\n");
    AppendTo(output, " OptionNorms = \"all\"\n");
    AppendTo(output, " OutFormat = \"GAP\"\n");
    AppendTo(output, " FileOut = \"", FileVinOutput, "\"\n");
    AppendTo(output, "/\n");
    CloseStream(output);
    #
    output:=OutputTextFile(FileVinLorMat, true);
    n:=Length(LorMat);
    AppendTo(output, n, " ", n, "\n");
    for i in [1..n]
    do
        for j in [1..n]
        do
            eVal:=LorMat[i][j];
            AppendTo(output, " ", eVal);
        od;
        AppendTo(output, "\n");
    od;
    CloseStream(output);
    #
    eCommand:=Concatenation(FileVIN_ComputeDomain, " ", FileVinNML);
    Print("eCommand=", eCommand, "\n");
    Exec(eCommand);
    TheReply:=ReadAsFunction(FileVinOutput)();
    RemoveFile(FileVinNML);
    RemoveFile(FileVinLorMat);
    RemoveFile(FileVinOutput);
    return TheReply;
end;



LORENTZ_GetFundamentalDomain_V1:=function(LorMat)
    local FileGram, FileRoot, output, n, i, j, eVal, eCommand, ListRoot;
    FileGram:=Filename(POLYHEDRAL_tmpdir,"Vinberg.gram");
    FileRoot:=Filename(POLYHEDRAL_tmpdir,"Vinberg.roots");
    output:=OutputTextFile(FileGram, true);
    n:=Length(LorMat);
    AppendTo(output, Length(LorMat), "\n");
    for i in [1..n]
    do
        for j in [1..n]
        do
            eVal:= - LorMat[i][j]; # Different sign convention
            AppendTo(output, " ", eVal);
        od;
        AppendTo(output, "\n");
    od;
    CloseStream(output);
    #
    eCommand:=Concatenation("(cd /home/mathieu/TheComputation_Polyhedral/vinberg-algorithm && ./vinberg-algorithm_specrun.sage ", FileGram, " ", FileRoot, ")");

    Exec(eCommand);
    ListRoot:=ReadVectorFile(FileRoot);
    RemoveFile(FileGram);
    RemoveFile(FileRoot);
    return ListRoot;
end;





LORENTZ_IsIsotropic:=function(GramMat)
    local eDet;
    eDet:= - DeterminantMat(GramMat);
    return RatSqrt(eDet) <>fail;
end;

#
# this is a set of functions related to Lorentzian lattice computation
# in one way or another.
LORENTZ_IsLorentzian:=function(LorMat)
  local eRec;
  eRec:=DiagonalizeSymmetricMatrix(LorMat);
  if eRec.nbPlus<>1 then
    Print("Cannot be lorentzian. Plus space should be one-dimensional\n");
    return false;
  fi;
  if eRec.nbZero<>0 then
    Print("Cannot be lorentzian. Should be nondegenerate\n");
    return false;
  fi;
  return true;
end;


LORENTZ_AssembleDiagBlocks:=function(ListMat)
  local nbMat, ListDim, TotDim, RetMat, iMat, TheShift, jMat, eDim, i, j;
  nbMat:=Length(ListMat);
  ListDim:=List(ListMat, Length);
  TotDim:=Sum(ListDim);
  RetMat:=NullMat(TotDim, TotDim);
  for iMat in [1..nbMat]
  do
    TheShift:=0;
    for jMat in [1..iMat-1]
    do
      TheShift:=TheShift + ListDim[jMat];
    od;
    eDim:=ListDim[iMat];
    for i in [1..eDim]
    do
      for j in [1..eDim]
      do
        RetMat[i+TheShift][j+TheShift]:=ListMat[iMat][i][j];
      od;
    od;
  od;
  return RetMat;
end;


TestSpecificCase:=function(eRec)
    local LorMat, n_simple, dim, RecOpt, TheRec, LRoot, ListIneq, ListRay1, ListRay2, GRPmatr, LOrbRay, eOrb;
    LorMat:=eRec.LorMat;
    dim:=Length(LorMat);
#    TheRec:=LORENTZ_GetFundamentalDomain_Edgewalk(LorMat);
    RecOpt:=rec(EarlyTerminationIfNotReflective:=true);
    TheRec:=LORENTZ_GetFundamentalDomain_Edgewalk_Kernel(LorMat, RecOpt);
    if TheRec.is_reflective=false then
        Error("The lattice is found to be not-reflective, while it is");
    fi;
    #
    LRoot:=TheRec.ListSimpleRoots;
    if IsBound(eRec.n_simple) then
        if TheRec.n_simple<>eRec.n_simple then
            Print("We have TheRec.n_simple=", TheRec.n_simple, " n_simple=", eRec.n_simple, "\n");
            Error("There are some bugs to resolve yet");
        fi;
    fi;
    if RankMat(LinearDeterminedByInequalities(LRoot))<>dim then
        Error("Space determined by inequalities has wrong rank");
    fi;
    if Length(RedundancyCheck(LRoot))<>Length(LRoot) then
        Error("There are some redundant roots");
    fi;
    ListIneq:= - LRoot * LorMat;
    ListRay1:=DualDescription(ListIneq);
    ListRay2:=List(ListRay1, RemoveFraction);
    if Length(TheRec.ListIsomCox)=0 then
        GRPmatr:=Group([IdentityMat(dim)]);
    else
        GRPmatr:=Group(TheRec.ListIsomCox);
    fi;
    for eOrb in TheRec.ListVertices
    do
        if Position(ListRay2, eOrb.gen)=fail then
            Print("gen=", eOrb.gen, "\n");
            Error("The found ray is absent from the computed list");
        fi;
    od;
    LOrbRay:=Orbits(GRPmatr, ListRay2, OnPoints);
    if Length(LOrbRay)<>Length(TheRec.ListVertices) then
        Print("|LOrbRay|=", Length(LOrbRay), " |TheRec.ListVertices|=", Length(TheRec.ListVertices), "\n");
        Error("The number of orbits of rays is not matching");
    fi;
end;





LORENTZ_GetSquareFreeHyperbolic:=function(n)
    local ListDim, SqrDim, eDir, eFile, ListV, ListLorMat, eV, LorMat, idx, i, j;
    ListDim :=Concatenation([4..19], [21]);
    if Position(ListDim, n)=fail then
        Error("The allowed dimensions are 4 ... 19, 21");
    fi;
    SqrDim := (n+1) * (n+1);
    eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/SquareFreeHyperbolic")[1];
    eFile:=Filename(eDir,Concatenation("Gram", String(n)));
    ListV:=ReadAsFunction(eFile)();
    ListLorMat:=[];
    for eV in ListV
    do
        if Length(eV)<>SqrDim then
            Error("The vector eV does not have the right length");
        fi;
        LorMat:=NullMat(n+1,n+1);
        idx:=0;
        for i in [1..n+1]
        do
            for j in [1..n+1]
            do
                idx:=idx+1;
                LorMat[i][j]:=eV[idx];
            od;
        od;
        Add(ListLorMat, LorMat);
    od;
    return ListLorMat;
end;



LORENTZ_SymbolToLorMat:=function(eList)
    local GetGram, ListGram, eName, i;
    GetGram:=function(eStr)
        local dim, U, sFact;
        if eStr="E6" then
            return ClassicalSporadicLattices("E6");
        fi;
        if eStr="E7" then
            return ClassicalSporadicLattices("E7");
        fi;
        if eStr="E8" then
            return ClassicalSporadicLattices("E8");
        fi;
        if eStr[1]='D' then
            dim:=Int(eStr{[2..Length(eStr)]});
            return LatticeDn(dim).GramMat;
        fi;
        if eStr[1]='A' then
            dim:=Int(eStr{[2..Length(eStr)]});
            return LatticeAn(dim).GramMat;
        fi;
        U:=[[0,1],[1,0]];
        if eStr="U" then
            return U;
        fi;
        if eStr[1]='U' then
            sFact:=Int(eStr{[2..Length(eStr)]});
            return sFact*U;
        fi;
        return [[-Int(eStr)]];
    end;
    ListGram:=List(eList, GetGram);
    eName:=eList[1];
    for i in [2..Length(eList)]
    do
        eName:=Concatenation(eName, "_", eList[i]);
    od;
    return rec(LorMat:=LORENTZ_AssembleDiagBlocks(ListGram), name:=eName);
end;






LORENTZ_GetNikulinList:=function()
    local LS_05, LS_06, LS_07, LS_08, LS_09, LS_10, LS_11, LS_12, LS_13, LS_14, LS_15, LS_16, LS_17, LS_18, LS_19, GetGram, LSall, ListRec, eList, ListGram, LorMat, eRec;
    LS_05:=[ ["U", "A1", "A1", "A1"], ["U2", "A1", "A1", "A1"], ["U", "A1", "A2"], ["U", "A3"], ["U4", "A1", "A1", "A1"],
             ["6", "A2", "A2"], ["4", "D4"], ["8", "D4"], ["16", "D4"] ];
    LS_06:=[ ["U", "D4"], ["U2", "D4"], ["U", "A1", "A1", "A1", "A1"], ["U2", "A1", "A1", "A1", "A1"], ["U", "A1", "A1", "A2"],
             ["U", "A2", "A2"], ["U", "A1", "A3"], ["U", "A4"], ["U4", "D4"], ["U3", "A2", "A2"] ];
    LS_07:=[ ["U", "D4", "A1"], ["U2", "A1", "A1", "A1", "A1", "A1"], ["U", "A1", "A2", "A2"],
             ["U", "A1", "A1", "A3"], ["U", "A2", "A3"], ["U", "A1", "A4"], ["U", "A5"], ["U", "D5"] ];
    LS_08:=[ ["U", "D6"], ["U", "D4", "A1", "A1"], ["U", "A1", "A1", "A1", "A1", "A1", "A1"], ["U2", "A1", "A1", "A1", "A1", "A1", "A1"],
             ["U", "A2", "A2", "A2"], ["U", "A3", "A3"],
             ["U", "A2", "A4"], ["U", "A1", "A5"], ["U", "A6"], ["U", "A2", "D4"], ["U", "A1", "D5"], ["U", "E6"] ];
    LS_09:=[ ["U", "E7"], ["U", "D6", "A1"], ["U", "D4", "A1", "A1", "A1"], ["U", "A1", "A1", "A1", "A1", "A1", "A1", "A1"],
             ["U2", "A1", "A1", "A1", "A1", "A1", "A1", "A1"], ["U", "A7"], ["U", "A3", "D4"], ["U", "A2", "D5"], ["U", "D7"], ["U", "A1", "E6"] ];
    LS_10:=[ ["U", "E8"], ["U", "D8"], ["U", "E7", "A1"], ["U", "D4", "D4"], ["U", "D6", "A1", "A1"], ["U", "A2", "E6"],
             ["U2", "D4", "D4"], ["U", "D4", "A1", "A1", "A1", "A1"], ["U", "A1", "A1", "A1", "A1", "A1", "A1", "A1", "A1"] ];
    LS_11:=[ ["U", "E8", "A1"], ["U", "D8", "A1"], ["U", "D4", "D4", "A1"], ["U", "D4", "A1", "A1", "A1", "A1", "A1"] ];
    LS_12:=[ ["U", "E8", "A1", "A1"], ["U", "D8", "A1", "A1"], ["U", "D4", "D4", "A1", "A1"], ["U", "A2", "E8"] ];
    LS_13:=[ ["U", "E8", "A1", "A1", "A1"],["U", "D8", "A1", "A1", "A1"], ["U", "A3", "E8"] ];
    LS_14:=[ ["U", "E8", "D4"], ["U", "D8", "D4"], ["U", "E8", "A1", "A1", "A1", "A1"] ];
    LS_15:=[ ["U", "E8", "D4", "A1"] ];
    LS_16:=[ ["U", "E8", "D6"] ];
    LS_17:=[ ["U", "E8", "E7"] ];
    LS_18:=[ ["U", "E8", "E8"] ];
    LS_19:=[ ["U", "E8", "E8", "A1"] ];
    LSall:=Concatenation([LS_05, LS_06, LS_07, LS_08, LS_09, LS_10, LS_11, LS_12, LS_13, LS_14, LS_15, LS_16, LS_17, LS_18, LS_19]);
    ListRec:=[];
    for eList in LSall
    do
        LorMat:=LORENTZ_SymbolToLorMat(eList).LorMat;
        eRec:=rec(LorMat:=LorMat);
        Add(ListRec, eRec);
    od;
    return ListRec;
end;



LORENTZ_GetReflectiveDim3:=function()
    local Postfix, eDir, eFile, ListCases, GetLorMat_dim3, ListReturn, i;
    #Postfix:="RK3_implicit_gap";
    #Postfix:="RK3_explicit_gap";
    Postfix:="RK3_all_gap";
    eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/Lorentzian_Lattices")[1];
    eFile:=Filename(eDir,Postfix);
    Print("eFile=", eFile, "\n");
    ListCases:=ReadAsFunction(eFile)();
    GetLorMat_dim3:=function(eEnt)
        local vectLorMat, LorMat, idx, i, j, vectSimpleRoot, n_root, MatRoot, i_root, ListNormRoot, ListNormRay, ListIneq, ListRay;
        vectLorMat:=eEnt[1];
        LorMat:=NullMat(3,3);
        idx:=0;
        for i in [1..3]
        do
            for j in [1..3]
            do
                idx:=idx+1;
                LorMat[i][j]:=vectLorMat[idx];
            od;
        od;
        vectSimpleRoot:=eEnt[3];
        n_root:=Length(vectSimpleRoot) / 3;
        MatRoot:=NullMat(n_root,3);
        for i_root in [1..n_root]
        do
            for i in [1..3]
            do
                MatRoot[i_root][i]:=vectSimpleRoot[i_root + (i-1) * n_root];
            od;
        od;
        ListIneq:=-MatRoot * LorMat;
        ListRay:=DualDescription(ListIneq);
        ListNormRay:=List(ListRay, x->x*LorMat*x);
        ListNormRoot:=List(MatRoot, x->x*LorMat*x);
        return rec(LorMat:=LorMat, MatRoot:=MatRoot, n_simple:=n_root, ListNormRay:=ListNormRay, ListNormRoot:=ListNormRoot);
    end;
    ListReturn:=[];
    for i in [1..Length(ListCases)]
    do
        Print("i=", i, " / ", Length(ListCases), "\n");
        Add(ListReturn, GetLorMat_dim3(ListCases[i]));
    od;
    return ListReturn;
end;



LORENTZ_GetReflectiveDim4:=function()
    local ListCasesDim4, ListRec, GetLorMat_dim4;
    ListCasesDim4:=
    [
      [1,1,1, 4],
      [1,0,1, 4],
      [1,1,2, 6],
      [1,0,2, 5],
      [1,1,3, 6],
      [2,2,2, 4],
      [1,1,4, 8],
      [2,1,2, 6],
      [1,1,5, 7],
      [1,0,5, 6],
      [2,2,3, 6],
      [1,0,6, 6],
      [2,0,3, 6],
      [2,2,4, 8],
      [3,1,3, 8],
      [3,0,3, 5],
      [1,1,10, 10],
      [1,0,10, 9],
      [2,0,5, 7],
      [2,2,6, 7],
      [1,0,13, 10],
      [1,0,14, 9],
      [2,2,8, 10],
      [3,3,6, 10],
      [1,0,17, 13],
      [3,0,6, 8],
      [5,5,5, 6],
      [1,0,21, 11],
      [3,0,7, 8],
      [5,4,5, 11],
      [5,0,5, 6],
      [1,0,30, 11],
      [2,0,15, 14],
      [3,0,10, 13],
      [5,0,6, 14],
      [1,0,33, 15],
      [6,2,6, 11],
      [7,7,7, 6],
      [3,0,14, 18],
      [6,0,7, 18],
      [3,0,15, 15],
      [7,0,7, 9],
      [5,0,10, 13],
      [10,10,10, 7],
      [3,0,30, 20],
      [6,0,15, 20],
      [13,13,13, 12],
      [14,14,14, 12],
      [15,0,15, 18]
    ];
    GetLorMat_dim4:=function(eEnt)
        local LorMat;
        LorMat:=NullMat(4,4);
        LorMat[1][2]:=1;
        LorMat[2][1]:=1;
        LorMat[3][3]:=2 * eEnt[1];
        LorMat[3][4]:=eEnt[2];
        LorMat[4][3]:=eEnt[2];
        LorMat[4][4]:=2 * eEnt[3];
        return rec(LorMat:=LorMat, n_simple:=eEnt[4]);
    end;
    ListRec:=List(ListCasesDim4, GetLorMat_dim4);
    return ListRec;
end;


LORENTZ_GetReflectiveDim5:=function()
    local ListCasesDim5, GetLorMat_dim5;
    ListCasesDim5:=
    [
      [1, [1,1,1], 5],
      [1, [1, [2, 1, 2]], 6],
      [1, [1,1,3], 7],
      [2, [1,1,1], 5],
      [1, [1,1,5], 7],
      [1, [1, [2,1,3]], 8],
      [1, [1,1,6], 7],
      [1, [2, [2,1,2]], 6],
      [1, [1,1,7], 10],
      [1, [3, [2,1,2]], 7],
      [1, [1,3,3], 7],
      [1, [1, [2,1,6]], 9],
      [2, [1, [2,1,2]], 6],
      [1, [1,2,7],13],
      [1, [2, [2,1,4]],8],
      [1, [3, [2,1,3]],10],
      [1, [1,3,5],15],
      [1, [1,1,15],12],
      [1, [5,[2,1,2]],10],
      [1, [2,3,3],8],
      [1, [6,[2,1,2]],7],
      [2, [1,1,5],7],
      [1, [7,[2,1,2]],14],
      [1, [1,3,7],18],
      [1, [1,5,5],9],
      [1, [5,[2,1,3]],14],
      [1, [1,2,15],19],
      [1, [2,[2,1,8]],11],
      [1, [10,[2,1,2]],10],
      [2, [3,[2,1,2]],7],
      [1, [14,[2,1,2]],11],
      [1, [15,[2,1,2]],16],
      [1, [3,[2,1,8]],21],
      [2, [3,[2,1,3]],11],
      [2, [5,[2,1,2]],12],
      [1, [1,[10,5,10]],14],
      [1, [1,5,15],51],
      [2, [7,[2,1,2]],15],
      [2, [1,5,5],11],
      [1, [10,[2,1,8]],33],
      [2, [15,[2,1,2]],17],
      [2, [1,[10,5,10]],19]
    ];

    GetLorMat_dim5:=function(eEnt)
        local LorMat, x, eL, eP, n_simple;
        LorMat:=NullMat(5,5);
        x:=eEnt[1];
        LorMat[1][2]:=x;
        LorMat[2][1]:=x;
        eL:=eEnt[2];
        if Length(eL)=3 then
            LorMat[3][3]:=eL[1];
            LorMat[4][4]:=eL[2];
            LorMat[5][5]:=eL[3];
        fi;
        if Length(eL)=2 then
            LorMat[3][3]:=eL[1];
            eP:=eL[2];
            LorMat[4][4]:=eP[1];
            LorMat[4][5]:=eP[2];
            LorMat[5][4]:=eP[2];
            LorMat[5][5]:=eP[3];
        fi;
        n_simple:=eEnt[3];
        return rec(LorMat:=LorMat, n_simple:=n_simple);
    end;
    return List(ListCasesDim5, GetLorMat_dim5);
end;


LORENTZ_GetReflectiveDim6:=function()
    local eDir, eFile;
    eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/Lorentzian_Lattices")[1];
    eFile:=Filename(eDir, "Records_dim6");
    return ReadAsFunction(eFile)();
end;




LORENTZ_GetReflectiveDiagonal:=function()
    local ListCasesDiagonal, GetLorMat_Diagonal;
    # Work by Vinberg, McLeod, Alice Mark
    ListCasesDiagonal:=
    [
      rec(p:=1, n:=2, n_simple:=3),
      rec(p:=2, n:=2, n_simple:=3),
      rec(p:=3, n:=2, n_simple:=3),
      rec(p:=5, n:=2, n_simple:=4),
      rec(p:=7, n:=2, n_simple:=4),
      rec(p:=11, n:=2, n_simple:=4),
      rec(p:=17, n:=2, n_simple:=7),

      rec(p:=1, n:=3, n_simple:=4),
      rec(p:=2, n:=3, n_simple:=5),
      rec(p:=3, n:=3, n_simple:=4),
      rec(p:=5, n:=3, n_simple:=6),
      rec(p:=7, n:=3, n_simple:=5),
      rec(p:=11, n:=3, n_simple:=7),
      rec(p:=17, n:=3, n_simple:=13),

      rec(p:=1, n:=4, n_simple:=5),
      rec(p:=2, n:=4, n_simple:=6),
      rec(p:=3, n:=4, n_simple:=6),
      rec(p:=5, n:=4, n_simple:=7),
      rec(p:=11, n:=4, n_simple:=9),

      rec(p:=1, n:=5, n_simple:=6),
      rec(p:=2, n:=5, n_simple:=7),
      rec(p:=3, n:=5, n_simple:=7),
      rec(p:=5, n:=5, n_simple:=8),

      rec(p:=1, n:=6, n_simple:=7),
      rec(p:=2, n:=6, n_simple:=8),
      rec(p:=3, n:=6, n_simple:=8),
      rec(p:=5, n:=6, n_simple:=10),

      rec(p:=1, n:=7, n_simple:=8),
      rec(p:=2, n:=7, n_simple:=9),
      rec(p:=3, n:=7, n_simple:=9),
      rec(p:=5, n:=7, n_simple:=11),

      rec(p:=1, n:=8, n_simple:=9),
      rec(p:=2, n:=8, n_simple:=10),
      rec(p:=3, n:=8, n_simple:=10),
      rec(p:=5, n:=8, n_simple:=12),

      rec(p:=1, n:=9, n_simple:=10),
      rec(p:=2, n:=9, n_simple:=12),
      rec(p:=3, n:=9, n_simple:=12),

      rec(p:=1, n:=10, n_simple:=12),
      rec(p:=2, n:=10, n_simple:=13),
      rec(p:=3, n:=10, n_simple:=14),

      rec(p:=1, n:=11, n_simple:=13),
      rec(p:=2, n:=11, n_simple:=15),
      rec(p:=3, n:=11, n_simple:=15),

      rec(p:=1, n:=12, n_simple:=14),
      rec(p:=2, n:=12, n_simple:=16),
      rec(p:=3, n:=12, n_simple:=18),

      rec(p:=1, n:=13, n_simple:=15),
      rec(p:=2, n:=13, n_simple:=19),
      rec(p:=3, n:=13, n_simple:=22),

      rec(p:=1, n:=14, n_simple:=17),
      rec(p:=2, n:=14, n_simple:=20),

      rec(p:=1, n:=15, n_simple:=18),

      rec(p:=1, n:=16, n_simple:=20),

      rec(p:=1, n:=17, n_simple:=22)
    ];
    GetLorMat_Diagonal:=function(eEnt)
        local n, LorMat;
        n:=eEnt.n+1;
        LorMat:=IdentityMat(n,n);
        LorMat[1][1]:=-eEnt.p;
        return rec(LorMat:=LorMat, n_simple:=eEnt.n_simple);
    end;
    return List(ListCasesDiagonal, GetLorMat_Diagonal);
end;





LORENTZ_GetHardReflective_Cases:=function(eEnt)
    local ListNames, eName, Hmat, GramMat, LorMat, len, Basis0, Basis1, TheSpann, TheOrth, GeneratingSet, TheBasis;
    Hmat:=[[0,1],[1,0]];
    ListNames:=[];
    eName:="Even_sublattice_I1_21";
    Add(ListNames, eName);
    if eEnt = eName then
        GramMat:=LatticeDn(20).GramMat;
        LorMat:=LORENTZ_AssembleDiagBlocks([Hmat, GramMat]);
        return rec(LorMat:=LorMat, n_simple:=210);
    fi;
    #
    eName:="Orthogonal_II3_19";
    Add(ListNames, eName);
    if eEnt = eName then
        GramMat := LORENTZ_AssembleDiagBlocks([Hmat, Hmat, Hmat, ClassicalSporadicLattices("E8"), ClassicalSporadicLattices("E8")]);
        len:=Length(GramMat);
        Basis0:=Concatenation([-1,4,0,0], ListWithIdenticalEntries(len - 4,0));
        Basis1:=Concatenation([0,0,-1,4], ListWithIdenticalEntries(len - 4,0));
        TheSpann:=[Basis0, Basis1];
        TheOrth:=NullspaceIntMat(TransposedMat(TheSpann * GramMat));
        LorMat:=TheOrth * GramMat * TransposedMat(TheOrth);
        return rec(LorMat:=LorMat);
    fi;
    #
    eName:="Kondo_A2_A2";
    Add(ListNames, eName);
    if eEnt = eName then
        LorMat:=
[ [   98,   -3,  -38,   -8,  -18,    1,   70,    3,   -9,  -47,   76,   38,   -4,   17,  -15,    2,   -1,   46,  -35,   49,  -24,  -38 ],
  [   -3,    4,    2,    3,   -2,    0,   -4,   -2,    1,    1,   -3,   -2,    0,   -3,    0,   -1,    0,   -5,    2,   -3,    2,    0 ],
  [  -38,    2,   18,    6,    6,    1,  -29,   -1,    3,   19,  -31,  -16,    1,   -8,    4,   -3,    0,  -21,   12,  -22,   10,   15 ],
  [   -8,    3,    6,    6,   -1,    2,  -10,   -2,    0,    6,   -9,   -5,   -2,   -5,    0,   -4,   -2,  -10,    3,   -9,    3,    4 ],
  [  -18,   -2,    6,   -1,    8,   -1,  -11,    2,    1,    8,  -11,   -6,    3,   -1,    3,    1,    0,   -4,    6,   -7,    4,    7 ],
  [    1,    0,    1,    2,   -1,    4,   -1,    1,   -1,    1,   -2,   -2,   -2,    0,   -2,   -2,   -2,   -3,   -1,   -3,    0,    1 ],
  [   70,   -4,  -29,  -10,  -11,   -1,   56,    5,   -7,  -35,   56,   28,    0,   16,   -9,    6,    1,   38,  -26,   39,  -18,  -28 ],
  [    3,   -2,   -1,   -2,    2,    1,    5,    4,   -1,   -1,    3,    1,    2,    3,   -1,    2,    0,    4,   -3,    2,   -1,   -1 ],
  [   -9,    1,    3,    0,    1,   -1,   -7,   -1,    4,    3,   -6,   -2,    1,   -2,    1,    0,    1,   -3,    3,   -4,    3,    2 ],
  [  -47,    1,   19,    6,    8,    1,  -35,   -1,    3,   28,  -39,  -18,    0,  -10,    7,   -3,   -2,  -25,   16,  -27,   11,   21 ],
  [   76,   -3,  -31,   -9,  -11,   -2,   56,    3,   -6,  -39,   64,   32,    0,   15,  -11,    4,    1,   41,  -27,   42,  -19,  -31 ],
  [   38,   -2,  -16,   -5,   -6,   -2,   28,    1,   -2,  -18,   32,   18,    0,    7,   -5,    2,    1,   21,  -14,   21,  -10,  -15 ],
  [   -4,    0,    1,   -2,    3,   -2,    0,    2,    1,    0,    0,    0,    6,    1,    1,    4,    3,    2,    0,    1,    1,    0 ],
  [   17,   -3,   -8,   -5,   -1,    0,   16,    3,   -2,  -10,   15,    7,    1,    8,   -2,    4,    1,   13,   -7,   12,   -5,   -7 ],
  [  -15,    0,    4,    0,    3,   -2,   -9,   -1,    1,    7,  -11,   -5,    1,   -2,    6,    2,    1,   -5,    7,   -5,    3,    6 ],
  [    2,   -1,   -3,   -4,    1,   -2,    6,    2,    0,   -3,    4,    2,    4,    4,    2,    6,    3,    6,   -1,    6,   -1,   -2 ],
  [   -1,    0,    0,   -2,    0,   -2,    1,    0,    1,   -2,    1,    1,    3,    1,    1,    3,    4,    2,    0,    3,    0,   -1 ],
  [   46,   -5,  -21,  -10,   -4,   -3,   38,    4,   -3,  -25,   41,   21,    2,   13,   -5,    6,    2,   32,  -17,   30,  -12,  -19 ],
  [  -35,    2,   12,    3,    6,   -1,  -26,   -3,    3,   16,  -27,  -14,    0,   -7,    7,   -1,    0,  -17,   16,  -16,    8,   14 ],
  [   49,   -3,  -22,   -9,   -7,   -3,   39,    2,   -4,  -27,   42,   21,    1,   12,   -5,    6,    3,   30,  -16,   32,  -13,  -20 ],
  [  -24,    2,   10,    3,    4,    0,  -18,   -1,    3,   11,  -19,  -10,    1,   -5,    3,   -1,    0,  -12,    8,  -13,    8,    8 ],
  [  -38,    0,   15,    4,    7,    1,  -28,   -1,    2,   21,  -31,  -15,    0,   -7,    6,   -2,   -1,  -19,   14,  -20,    8,   18 ] ];
        return rec(LorMat:=LorMat);
    fi;
    #
    eName:="Borcherds_960";
    Add(ListNames, eName);
    if eEnt = eName then
        GeneratingSet:=
        [
          [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
          [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
          [0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
          [0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1],
          [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]
        ];
        Append(GeneratingSet, 2*IdentityMat(16));
        TheBasis:=GetZbasis(GeneratingSet);
        GramMat:=TheBasis * TransposedMat(TheBasis) / 2;
        LorMat:=LORENTZ_AssembleDiagBlocks([Hmat, GramMat]);
        return rec(LorMat:=LorMat);
    fi;
    #
    Print("ListNames=", ListNames, " eEnt=", eEnt, "\n");
    Error("Please correct your input eEnt");
end;



LORENTZ_GetTurkaljList:=function()
    local ListLines, eLine, ListGram, GramMat, i, j, pos;
ListLines:=[
 [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1 ],
    [ 0, 0, 0, 0, 0, -2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0, 0, 0, 0, -4 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 7 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 4, -2, 0, 0, 0, 0, -2, 8 ],
    [ 0, -1, -1, -3, 2, -6, -1, 0, 0, 1, -1, -3, -1, 0, 2, -1, 0, 0, -3, 1, -1, 12, -3, -4, 2, -1, 0, -3, 12, -4, -6, -3, 0, -4, -4, -20 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0, 0, 0, 1, 2 ],
    [ 0, -1, 0, 0, 1, 0, -1, -2, 0, 0, 1, -1, 0, 0, 2, -1, 1, -1, 0, 0, -1, 2, -1, 1, 1, 1, 1, -1, 2, 0, 0, -1, -1, 1, 0, 2 ],
    [ 0, -1, -1, -1, -2, 1, -1, 0, -1, -1, -2, 1, -1, -1, 0, -1, -2, 1, -1, -1, -1, 0, -2, 1, -2, -2, -2, -2, -4, 2, 1, 1, 1, 1, 2, 4 ],
    [ 0, 2, 2, -1, 2, -6, 2, 0, -3, -1, 5, 12, 2, -3, 0, -1, -2, 19, -1, -1, -1, 2, 0, 0, 2, 5, -2, 0, 26, 10, -6, 12, 19, 0, 10, -58 ],
    [ 0, -4, 1, -5, 2, 5, -4, -2, -1, 0, -1, 1, 1, -1, 4, 0, -2, 0, -5, 0, 0, 10, -5, 5, 2, -1, -2, -5, 10, -1, 5, 1, 0, 5, -1, 14 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -5 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -4, 2, 0, 0, 0, 0, 2, 4 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, -5 ],
    [ 0, -1, 0, 0, 0, -2, -1, 0, 0, 0, 1, -2, 0, 0, 2, -1, 1, 1, 0, 0, -1, 4, 1, 1, 0, 1, 1, 1, 4, 1, -2, -2, 1, 1, 1, -4 ],
    [ 0, -1, 0, 1, -1, -5, -1, 2, -1, 0, -1, 0, 0, -1, 2, 0, 0, 0, 1, 0, 0, 2, 0, 0, -1, -1, 0, 0, 4, 0, -5, 0, 0, 0, 0, -10 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, -5 ],
    [ 0, 0, 0, 0, 0, -5, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -5, 0, 0, 0, 0, -15 ],
    [ 0, 0, 0, 0, 0, -10, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -10, 0, 0, 0, 0, -80 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2 ],
    [ 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, 0, -1, 1, 0, 0, 0, 2, -1, -1, 0, 0, -1, -1, 3, 1, 0, 0, 1, -1, 1, 3 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3 ],
    [ 0, 0, 0, 0, 0, -6, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, -6, 0, 0, 0, 0, -24 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 3 ],
    [ 0, 0, 0, 0, 0, -2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, -2, 0, 0, 0, 0, -4 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 3 ],
    [ 1, 0, 0, 0, 0, 0, 0, -2, 0, -1, 1, 0, 0, 0, 2, 1, -1, 0, 0, -1, 1, 3, 0, 0, 0, 1, -1, 0, 3, 0, 0, 0, 0, 0, 0, 3 ],
    [ 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, -1, -1, 0, 0, 2, 1, 0, 1, 0, 0, 1, 2, 0, 0, 0, -1, 0, 0, 4, 1, 1, -1, 1, 0, 1, -6 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 15 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0, 0, 0, 1, 7 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 10, 5, 0, 0, 0, 0, 5, 10 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 3 ],
    [ 0, 0, 0, 0, 0, -6, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -6, 0, 0, 0, 0, -24 ],
    [ 0, -1, 0, 0, -1, -2, -1, -2, -1, 1, 0, 0, 0, -1, 2, 0, 0, 0, 0, 1, 0, 2, 1, 1, -1, 0, 0, 1, 10, 2, -2, 0, 0, 1, 2, 12 ],
    [ 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0, -8 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 2, 4 ],
    [ 0, -1, 0, 1, 0, -3, -1, 2, -1, -1, 0, -1, 0, -1, 2, 0, 0, 0, 1, -1, 0, 2, 0, 1, 0, 0, 0, 0, 2, -1, -3, -1, 0, 1, -1, -10 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, -2 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 14 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -10 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 6 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 6 ],
    [ 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, -10 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 6 ],
    [ 0, 0, 0, 0, -6, 6, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -6, 0, 0, 0, -18, 0, 6, 0, 0, 0, 0, 24 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, -6 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -6 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 6 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 6 ],
    [ 0, 0, 0, -2, 0, -4, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, -4, 0, -2, 0, 0, 0, 0, 6, 0, -4, 0, 0, -2, 0, 11 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, -6 ],
    [ 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 2, 4 ],
    [ 0, -1, -1, 1, 0, 2, -1, 0, -1, 1, 0, 2, -1, -1, 0, 1, 1, 3, 1, 1, 1, 0, -1, -3, 0, 0, 1, -1, 2, 0, 2, 2, 3, -3, 0, -6 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2 ],
    [ 0, 0, 0, -1, 2, -1, 0, 2, 0, -1, 0, 0, 0, 0, 2, -1, 0, 1, -1, -1, -1, 4, -1, -2, 2, 0, 0, -1, -6, 2, -1, 0, 1, -2, 2, 16 ],
    [ 2, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 1, 1, 1, 0, 1, -6, 1, 1, 1, 0, 1, 1, 8 ],
    [ 0, -1, 2, 1, 0, -5, -1, 0, 2, 1, 0, -5, 2, 2, 0, 0, -3, 7, 1, 1, 0, 2, 0, 0, 0, 0, -3, 0, 4, -1, -5, -5, 7, 0, -1, -16 ],
    [ 0, -1, -1, 2, 0, -5, -1, 2, 1, 0, 1, 0, -1, 1, 2, 0, 1, 0, 2, 0, 0, 4, -2, 0, 0, 1, 1, -2, 10, 0, -5, 0, 0, 0, 0, -10 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2 ],
    [ 2, 0, 0, 0, -1, 0, 0, 2, 0, 0, -1, 0, 0, 0, 2, 0, -1, 0, 0, 0, 0, -2, 0, 1, -1, -1, -1, 0, 4, 0, 0, 0, 0, 1, 0, 2 ],
    [ 0, 1, -1, 1, 3, -5, 1, 0, 1, -1, 0, 4, -1, 1, 2, 1, 0, -1, 1, -1, 1, 2, 0, -1, 3, 0, 0, 0, 6, 0, -5, 4, -1, -1, 0, -6 ],
    [ 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 6 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 6 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6 ],
    [ 0, -1, -1, -1, -2, 0, -1, 0, -1, -1, -2, 0, -1, -1, 0, -1, -2, 3, -1, -1, -1, 0, -2, 0, -2, -2, -2, -2, -4, 0, 0, 0, 3, 0, 0, 12 ],
    [ 0, -3, 2, -1, 1, -6, -3, 0, 0, 0, 0, -6, 2, 0, 2, -1, 0, 0, -1, 0, -1, 2, 0, 0, 1, 0, 0, 0, 2, 0, -6, -6, 0, 0, 0, -12 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3 ],
    [ 0, 0, 0, -6, 12, 12, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -6, 0, 0, 20, 9, 10, 12, 0, 0, 9, -42, 9, 12, 0, 0, 10, 9, 98 ],
    [ 2, 1, -1, 1, 0, 0, 1, 2, -1, 0, 0, 0, -1, -1, 2, -1, 0, 0, 1, 0, -1, 2, 0, 0, 0, 0, 0, 0, 2, -1, 0, 0, 0, 0, -1, -10 ],
    [ 0, 0, 0, -2, 1, -5, 0, 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, -2, 0, 0, 2, 0, 0, 1, 0, 0, 0, 4, 0, -5, 0, 0, 0, 0, -10 ],
    [ 2, -1, -1, 1, 1, 0, -1, 2, 1, -1, -1, 0, -1, 1, 2, -1, -1, 0, 1, -1, -1, 2, 1, 0, 1, -1, -1, 1, 2, 0, 0, 0, 0, 0, 0, -10 ],
    [ 0, 1, 0, 0, 0, 0, 1, -2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 1, 8 ],
    [ 0, 3, 8, -3, 0, 3, 3, 0, -12, 1, -3, -4, 8, -12, 0, -1, -1, -1, -3, 1, -1, 2, 1, 0, 0, -3, -1, 1, 2, 0, 3, -4, -1, 0, 0, 6 ],
    [ 0, 0, 0, 0, 0, 3, 0, 2, -1, -1, -1, 0, 0, -1, 2, 1, 1, 0, 0, -1, 1, 2, 0, 0, 0, -1, 1, 0, 2, 0, 3, 0, 0, 0, 0, -210 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 6 ],
    [ 0, 0, 0, 0, -1, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, -1, 0, -1, 0, 0, -1, -4, 0, 0, 0, 0, 0, 0, 6 ],
    [ 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6 ],
    [ 2, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 2, -1, 1, 0, 0, 1, -1, -6 ]
];
  ListGram:=[];
  for i in [1..Length(ListLines)]
  do
      eLine:=ListLines[i];
      GramMat:=NullMat(6,6);
      pos:=0;
      for i in [1..6]
      do
          for j in [1..6]
          do
              pos:=pos+1;
              GramMat[i][j]:=eLine[pos];
          od;
      od;
      Add(ListGram, GramMat);
  od;
  return ListGram;
end;











#
#
# We check that all the vectors are in a plane
LORENTZ_CheckCorrectnessVectorFamily:=function(ListVect)
  local dim, ListVectExt, rnk;
  dim:=Length(ListVect[1]);
  ListVectExt:=List(ListVect, x->Concatenation([1], x));
  rnk:=RankMat(ListVectExt);
  if rnk<> dim then
    Print("We have dim=", dim, " rnk=", rnk, " they should be equal\n");
    Error("Please correct this problem");
  fi;
end;


LORENTZ_GetSpace_K3:=function(k)
  local Hmat, Smat, eMatE8, ListMat;
  Hmat:=[[0,1],
         [1,0]];
  Smat:=[[-2*k]];
  eMatE8:=ClassicalSporadicLattices("E8");
  ListMat:=[Smat, Hmat, -eMatE8, -eMatE8];
  return LORENTZ_AssembleDiagBlocks(ListMat);
end;


LORENTZ_GetTestSpace:=function(k)
  local Hmat, Smat, eMatE8, ListMat;
  Hmat:=[[0,1],
         [1,0]];
  Smat:=[[-2*k]];
  eMatE8:=ClassicalSporadicLattices("E8");
  ListMat:=[Smat, Hmat, -eMatE8];
  return LORENTZ_AssembleDiagBlocks(ListMat);
end;


#
# we enumerate all vectors having a fixed distance pattern with
# a list of vectors.
LORENTZ_ListVectorFixedDistancePattern:=function(GramMat, ListVect, DistVector)
  local n, eVect, ListVectRed, ListEqua, ListB, iVect, eDiff, eVal, ListEquaSec, ListBsec, eLine, ListEquaTot, ListBtot, MinDistPointRed, MinDistPoint, eSquareDistDiff, OneIntegralPoint, TheBasis, TheDim, AffineBasis, eCentRed, eCent, ListSolutionSet, GramMatSpec, eSolRed, eSolSpec, eSol, eDist;
  n:=Length(GramMat);
  for eVect in ListVect
  do
    if eVect[1]<>1 then
      Error("first coordinate should be 1");
    fi;
    if Length(eVect)<>n+1 then
      Error("vector length should be n+1");
    fi;
  od;
  ListVectRed:=List(ListVect, x->x{[2..n+1]});
  ListEqua:=[];
  ListB:=[];
  for iVect in [2..Length(ListVect)]
  do
    eDiff:=ListVectRed[iVect]-ListVectRed[1];
    Add(ListEqua, -2*eDiff*GramMat);
    eVal:=DistVector[iVect]-DistVector[1]-ListVectRed[iVect]*GramMat*ListVectRed[iVect]+ListVectRed[1]*GramMat*ListVectRed[1];
    Add(ListB, eVal);
  od;
  ListEquaSec:=[];
  ListBsec:=[];
  for eLine in NullspaceMat(TransposedMat(ListVect))
  do
    Add(ListEquaSec, -eLine{[2..n+1]});
    Add(ListBsec, eLine[1]);
  od;
  ListEquaTot:=Concatenation(ListEqua, ListEquaSec);
  ListBtot:=Concatenation(ListB, ListBsec);
  MinDistPointRed:=SolutionMat(TransposedMat(ListEquaTot), ListBtot);
  if MinDistPoint=fail then
    return [];
  fi;
  MinDistPoint:=Concatenation([1], MinDistPointRed);
  eDiff:=MinDistPointRed-ListVectRed[1];
  eSquareDistDiff:=DistVector[1]-eDiff*GramMat*eDiff;
  OneIntegralPoint:=SolutionIntMat(TransposedMat(ListEqua), ListB);
  TheBasis:=NullspaceIntMat(TransposedMat(ListEqua));
  TheDim:=Length(TheBasis);
  AffineBasis:=[Concatenation([1], OneIntegralPoint)];
  Append(AffineBasis, List(TheBasis, x->Concatenation([0],x)));
  eCent:=SolutionMat(AffineBasis, MinDistPoint);
  eCentRed:=eCent{[2..TheDim+1]};
  ListSolutionSet:=[];
  GramMatSpec:=TheBasis*GramMat*TransposedMat(TheBasis);
  for eSolRed in ClosestAtDistanceVallentinProgram(GramMatSpec, eCentRed, eSquareDistDiff)
  do
    eDist:=(eSolRed-eCentRed)*GramMatSpec*(eSolRed-eCentRed);
    if eDist=eSquareDistDiff then
      eSolSpec:=Concatenation([1], eSolRed);
      eSol:=eSolSpec*AffineBasis;
      Add(ListSolutionSet, eSol);
    fi;
  od;
  return ListSolutionSet;
end;





#
# We enumerate all the vectors fVect such that
# fVect * LorMat * fVect >= 0 (or =0)     and      0 < fVect * LorMat * eVect <= MaxScal
#
# TheOption can be "isotrop" or "total"
# isotrop means all the vectors that are isotrop
#
# OnlyShortest is true if we return only the vectors of minimal values fVect * LorMat * eVect
LORENTZ_FindPositiveVectors:=function(LorMat, eVect, MaxScal, TheOption, OnlyShortest)
  local eNorm, Ubasis, GramMat, TheRec, eValMax, TotalListSol, eVal, eBasSol, alpha, eTrans, eSol, eSquareDist, ListSol, eSolA, eSolB, eSolC, fScal, fNorm;
#  Print("Beginning of LORENTZ_FindPositiveVectors\n");
  eNorm:=eVect*LorMat*eVect;
  if MaxScal<=0 then
    Print("MaxScal=", MaxScal, "\n");
    Error("We should have MaxScal > 0");
  fi;
  if TheOption<>"isotrop" and TheOption<>"total" then
    Print("TheOption=", TheOption, "\n");
    Error("AllowedValues for TheOption are isotrop or total");
  fi;
  if eNorm <= 0 then
    Print("eNorm=", eNorm, "\n");
    Error("Wrong norm of vector, will not work 1");
  fi;
  if IsIntegralVector(eVect)=false then
    Print("eVect=", eVect, "\n");
    Error("Vector should be integral.");
  fi;
  Ubasis:=NullspaceIntMat(TransposedMat([eVect*LorMat]));
  GramMat:=-Ubasis*LorMat*TransposedMat(Ubasis);
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Error("deep error");
  fi;
  TheRec:=GcdVector(eVect*LorMat);
  Print("eVect*LorMat=", eVect * LorMat, " TheRec=", TheRec, "\n");
  
  if TheRec.TheGcd<0 then
    Error("deep error 2");
  fi;
  eValMax:=LowerInteger(MaxScal/TheRec.TheGcd);
#  Print("MaxScal=", MaxScal, " TheRec.TheGcd=", TheRec.TheGcd, " eValMax=", eValMax, "\n");
  TotalListSol:=[];
  for eVal in [1..eValMax]
  do
    eBasSol:=eVal*TheRec.ListCoef; # a solution of eVect * LorMat * fVect = TheGcd * eVal
    alpha:=eVal*TheRec.TheGcd/eNorm;
    eTrans:=eBasSol - alpha*eVect;
    eSol:=SolutionMat(Ubasis, eTrans);
    if eSol=fail then
      Error("Please debug from here Lorentian 1");
    fi;
    Print("eSol=", eSol, "\n");
    eSquareDist:=alpha*alpha*eNorm;
    Print("alpha=", alpha, " eNorm=", eNorm, "\n");
    Print("eVal=", eVal, " eSquareDist=", eSquareDist, " det(GramMat)=", DeterminantMat(GramMat), "\n");
    ListSol:=ClosestAtDistanceVallentinProgram(GramMat, -eSol, eSquareDist);
    for eSolA in ListSol
    do
      eSolB:=eSolA*Ubasis;
      eSolC:=eBasSol + eSolB;
      fScal:=eSolC*LorMat*eVect;
      fNorm:=eSolC*LorMat*eSolC;
      if fNorm < 0 or fScal < 0 or fScal > MaxScal then
        Error("Error in norm or scalar product");
      fi;
      if IsIntegralVector(eSolC)=false then
        Error("Non integral eSolC, debug ....");
      fi;
      if TheOption="total" then
        Add(TotalListSol, eSolC);
      else
        if fNorm=0 then
          Add(TotalListSol, eSolC);
        fi;
      fi;
    od;
    if OnlyShortest and Length(TotalListSol)>0 then
      return TotalListSol;
    fi;
  od;
  return TotalListSol;
end;




LORENTZ_SearchInitialVectorOpt:=function(LorMat, PosVect, TheOption, OnlyShortest)
  local n, MaxScal, ListPosVect, ListIsotrop, ListScal, eScal, eSet;
  n:=Length(LorMat);
  MaxScal:=PosVect*LorMat*PosVect;
  Print("Beginning of LORENTZ_SearchInitialVector\n");
  Print("LorMat=\n");
  PrintArray(LorMat);
  Print("PosVect=", PosVect, " MaxScal=", MaxScal, "\n");
  while(true)
  do
    ListPosVect:=LORENTZ_FindPositiveVectors(LorMat, PosVect, MaxScal, TheOption, OnlyShortest);
    Print("LORENTZ_SearchInitialVector MaxScal=", MaxScal, " |ListPosVect|=", Length(ListPosVect), "\n");
    if Length(ListPosVect)>0 then
      ListScal:=List(ListPosVect, x->x*LorMat*PosVect);
      eScal:=Minimum(Difference(Set(ListScal), [0]));
      eSet:=Filtered([1..Length(ListScal)], x->ListScal[x]=eScal);
      return ListPosVect{eSet};
    fi;
    MaxScal:=MaxScal+1;
  od;
end;

LORENTZ_SearchInitialVector:=function(LorMat, PosVect, TheOption)
    local OnlyShortest;
    OnlyShortest:=false;
    return LORENTZ_SearchInitialVectorOpt(LorMat, PosVect, TheOption, OnlyShortest);
end;



LORENTZ_GetDefiningIneq:=function(LorMat, ListVect)
  local nbVect, ListB, eSol;
  nbVect:=Length(ListVect);
  ListB:=ListWithIdenticalEntries(nbVect,1);
  eSol:=SolutionMat(TransposedMat(ListVect), ListB);
  return RemoveFraction(eSol*Inverse(LorMat));
end;

LORENTZ_GetDeterminingVectFamily:=function(LorMat, eFamEXT)
  local eVectDef, ListScal, MaxScal, ListVect, TheDet, AffBas, TheSel, ListCollScal, LColl, LSize, LType, nbCase, iCase, ePerm, LTypeS, ListVectB, CurrDet, eListSel, TestVect, NewDet, OnlyShortest;
  Print("Running LORENTZ_GetDeterminingVectFamily |eFamEXT|=", Length(eFamEXT), "\n");
  eVectDef:=LORENTZ_GetDefiningIneq(LorMat, eFamEXT);
  ListScal:=List(eFamEXT, x->x*LorMat*eVectDef);
  if Length(Set(ListScal))<>1 then
    Error("We are wrong");
  fi;
  MaxScal:=ListScal[1];
  TheDet:=AbsInt(DeterminantMat(BaseIntMat(eFamEXT)));
#  Print("MaxScal=", MaxScal, " det=", TheDet, "\n");
  if TheDet=1 then
    return eFamEXT;
  fi;
  while(true)
  do
    OnlyShortest:=false;
    ListVect:=LORENTZ_FindPositiveVectors(LorMat, eVectDef, MaxScal, "total", OnlyShortest);
    TheDet:=AbsInt(DeterminantMat(BaseIntMat(ListVect)));
    if TheDet=1 then
      AffBas:=GetZbasis(eFamEXT);
      TheSel:=Filtered(ListVect, x->SolutionIntMat(AffBas, x)=fail);
      ListCollScal:=List(TheSel, x->Collected(List(eFamEXT, y->y*LorMat*x)));
      LColl:=Collected(ListCollScal);
      LSize:=List(LColl, x->x[2]);
      LType:=List(LColl, x->x[1]);
      nbCase:=Length(LColl);
      ePerm:=SortingPerm(LSize);
      LTypeS:=Permuted(LType, ePerm);
      ListVectB:=ShallowCopy(eFamEXT);
      CurrDet:=AbsInt(DeterminantMat(BaseIntMat(eFamEXT)));
      for iCase in [1..nbCase]
      do
        eListSel:=Filtered([1..Length(TheSel)], x->ListCollScal[x]=LTypeS[iCase]);
        TestVect:=Concatenation(ListVectB, TheSel{eListSel});
        NewDet:=AbsInt(DeterminantMat(BaseIntMat(TestVect)));
        if NewDet<CurrDet then
          ListVectB:=ShallowCopy(TestVect);
          CurrDet:=NewDet;
          if CurrDet=1 then
            return ListVectB;
          fi;
        fi;
      od;
    fi;
    MaxScal:=MaxScal+1;
  od;
end;


LORENTZ_ComputeFundamentalStabInfo:=function(LorMat, eFamEXT, GRPint)
  local ListPermGen, ListMatrGenB, eGen, eMatr, GRPintMatr, PhiPermMat;
  ListPermGen:=SmallGeneratingSet(GRPint);
  ListMatrGenB:=[];
  for eGen in ListPermGen
  do
    eMatr:=FindTransformation(eFamEXT, eFamEXT, eGen);
    if IsIntegralMat(eMatr)=false then
      Error("Bug: Non integral matrix");
    fi;
    if eMatr*LorMat*TransposedMat(eMatr)<>LorMat then
      Error("Bug: eMatr does not preserve LorMat");
    fi;
    Add(ListMatrGenB, eMatr);
  od;
  GRPintMatr:=Group(ListMatrGenB);
  PhiPermMat:=GroupHomomorphismByImagesNC(GRPint, GRPintMatr, ListPermGen, ListMatrGenB);
  return rec(GRP_int:=GRPint, GRPintMatr:=GRPintMatr, PhiPermMat:=PhiPermMat);
end;

LORENTZ_ComputeStabilizer:=function(LorMat, eFamEXT)
  local GRPrat, ListMatrGen, test, ListVect, GRPtot, ListPermGen, ListMatrGenB, eGen, eMatr, eList, GRPint, GRPintMatr, eVect, testB, ListPGen, PhiPermMat, TheStrategy;
  Print("|eFamEXT|=", Length(eFamEXT), "\n");
  GRPrat:=LinPolytope_AutomorphismStabSubset_AddMat(eFamEXT, eFamEXT, [LorMat]);
  Print("|GRPrat|=", Order(GRPrat), "\n");
  ListPGen:=GeneratorsOfGroup(GRPrat);
  Print("Before ListMatrGen construction\n");
  ListMatrGen:=List(ListPGen, x->FindTransformation(eFamEXT, eFamEXT, x));
  Print("After ListMatrGen construction\n");
  test:=First(ListMatrGen, x->IsIntegralMat(x)=false);
  if test=fail then
    GRPintMatr:=Group(ListMatrGen);
    PhiPermMat:=GroupHomomorphismByImagesNC(GRPrat, GRPintMatr, ListPGen, ListMatrGen);
    return rec(GRP_rat:=GRPrat, GRP_int:=GRPrat, GRPintMatr:=GRPintMatr, PhiPermMat:=PhiPermMat);
  fi;
  TheStrategy:=2;
  if TheStrategy=1 then
    Print("Before ListVect computation\n");
    ListVect:=LORENTZ_GetDeterminingVectFamily(LorMat, eFamEXT);
    Print("det(EXT)=", DeterminantMat(BaseIntMat(eFamEXT)), " |ListVect|=", Length(ListVect), "\n");
    GRPtot:=LinPolytope_AutomorphismStabSubset_AddMat(ListVect, eFamEXT, [LorMat]);
    ListPermGen:=[];
    ListMatrGenB:=[];
    for eGen in GeneratorsOfGroup(GRPtot)
    do
      eMatr:=FindTransformation(ListVect, ListVect, eGen);
      for eVect in eFamEXT*eMatr
      do
        if Position(eFamEXT, eVect)=fail then
          Error("Bug: eFamEXT vector is not invariant");
        fi;
      od;
      eList:=List(eFamEXT, x->Position(eFamEXT, x*eMatr));
      Add(ListPermGen, PermList(eList));
    od;
    GRPint:=Group(ListPermGen);
  fi;
  if TheStrategy=2 then
    GRPint:=KernelLinPolytopeIntegral_Automorphism_Subspaces(eFamEXT, GRPrat).GRPperm;
  fi;
  return LORENTZ_ComputeFundamentalStabInfo(LorMat, eFamEXT, GRPint);
end;


LORENTZ_GetAnsatzGraphInformation:=function(LorMat, eFamEXT, Qmat, HeuristicScal)
  local nbVert, ThePartition, TheListAdjacency, i, eList, j, eScal, ScalarMat, DistMat, korig, pos, LineScalar, iVert, jVert, SetV, n, SecVal;
  nbVert:=Length(eFamEXT);
  Print("Computing ScalarMat for nbVert=", nbVert, "\n");
  ScalarMat:=[];
  for i in [1..nbVert]
  do
    LineScalar:=[];
    for j in [1..nbVert]
    do
      eScal:=[];
      if HeuristicScal.UseLorMat then
        Add(eScal, eFamEXT[i] * LorMat * eFamEXT[j]);
      fi;
      if HeuristicScal.UseQmat then
        Add(eScal, eFamEXT[i] * Qmat * eFamEXT[j]);
      fi;
      if HeuristicScal.UseAllValues then
        Add(LineScalar, eScal);
      else
        pos:=Position(HeuristicScal.ListAllowedValues, eScal);
        Add(LineScalar, eScal);
      fi;
    od;
    Add(ScalarMat, LineScalar);
  od;
  Print("We have ScalarMat\n");
  if HeuristicScal.UseDiagonal then
    Print("Using the diagonal\n");
    DistMat:=MappedScalarMatrixDistanceMatrix(ScalarMat);
    SetV:=__SetValue(DistMat);
    korig:=Length(SetV);
    n:=Length(DistMat);
    TheListAdjacency:=Method4modelEdgeColoredGraph(DistMat, SetV);
    ThePartition:=__Method4Partition(korig, n);
    return rec(ThePartition:=ThePartition, ListAdjacency:=TheListAdjacency);
  else
    SetV:=__SetValue(ScalarMat);
    Print("Not using the diagonal |SetV|=", Length(SetV), "\n");
    if Length(SetV)=2 then
      SecVal:=SetV[2];
      ThePartition:=[[1..nbVert]];
      TheListAdjacency:=[];
      for iVert in [1..nbVert]
      do
        eList:=[];
        for jVert in [1..nbVert]
        do
          if iVert<>jVert then
            if ScalarMat[iVert][jVert]=SecVal then
              Add(eList, jVert);
            fi;
          fi;
        od;
        Add(TheListAdjacency, eList);
      od;
      return rec(ThePartition:=ThePartition, ListAdjacency:=TheListAdjacency);
    else
      SetV:=__SetValue(ScalarMat);
      korig:=Length(SetV);
      n:=Length(ScalarMat);
      TheListAdjacency:=Method4modelEdgeColoredGraph(ScalarMat, SetV);
      ThePartition:=__Method4Partition(korig, n);
      return rec(ThePartition:=ThePartition, ListAdjacency:=TheListAdjacency);
    fi;
  fi;
end;


LORENTZ_GetAnsatzSubpolytope:=function(LorMat, eFamEXT, Qmat, HeuristicSub)
  local nbVert, TheSub, iVert, eScal;
  nbVert:=Length(eFamEXT);
  TheSub:=[];
  for iVert in [1..nbVert]
  do
    eScal:=[];
    if HeuristicSub.UseLorMat then
      Add(eScal, eFamEXT[iVert] * LorMat * eFamEXT[iVert]);
    fi;
    if HeuristicSub.UseQmat then
      Add(eScal, eFamEXT[iVert] * Qmat * eFamEXT[iVert]);
    fi;
    if HeuristicSub.UseAllValues then
      Add(TheSub, iVert);
    else
      if Position(HeuristicSub.ListAllowedValues, eScal)<>fail then
        Add(TheSub, iVert);
      fi;
    fi;
  od;
  return TheSub;
end;




#
# This is an ansatz for specific cases.
# We have to deal with huge polytopes (2000 vertices, 5000 vertices, etc.)
# Thus what we do is reduce to a common scalar product
LORENTZ_ComputeStabilizer_Specific:=function(LorMat, eFamEXT, TheHeuristic)
  local RecAnsatz, GRPpermA, GRPpermB, GRPpermExt, Qmat, TheSub, ListMatrGens, ListPermGens;
  Print("Beginning of LORENTZ_ComputeStabilizer_Specific\n");
  Qmat:=Get_QinvMatrix(eFamEXT);
  Print("We have Qmat\n");
  TheSub:=LORENTZ_GetAnsatzSubpolytope(LorMat, eFamEXT, Qmat, TheHeuristic.HeuristicSub);
  Print("We have TheSub |TheSub|=", Length(TheSub), "\n");
  Print("Det(eFamEXT)=", AbsInt(DeterminantMat(BaseIntMat(eFamEXT))), " Det(eFamEXT{TheSub})=", AbsInt(DeterminantMat(BaseIntMat(eFamEXT{TheSub}))), "\n");
  RecAnsatz:=LORENTZ_GetAnsatzGraphInformation(LorMat, eFamEXT{TheSub}, Qmat, TheHeuristic.HeuristicScal);
  Print("We have RecAnsatz\n");
  GRPpermA:=SymmetryGroupVertexColoredGraphAdjList(RecAnsatz.ListAdjacency, RecAnsatz.ThePartition);
  Print("We have GRPpermA |GRPpermA|=", Order(GRPpermA), "\n");
  GRPpermB:=KernelLinPolytopeIntegral_Automorphism_Subspaces(eFamEXT{TheSub}, GRPpermA).GRPperm;
  Print("We have GRPpermB |GRPpermB|=", Order(GRPpermB), "\n");
  ListMatrGens:=List(GeneratorsOfGroup(GRPpermB), x->FindTransformation(eFamEXT{TheSub}, eFamEXT{TheSub}, x));
  Print("We have ListMatrGens\n");
  ListPermGens:=GetListPermGens(eFamEXT, ListMatrGens);
  Print("We have ListPermGens\n");
  GRPpermExt:=Group(ListPermGens);
  return LORENTZ_ComputeFundamentalStabInfo(LorMat, eFamEXT, GRPpermExt);
end;







LORENTZ_TestEquivalence_CheckAndReturn:=function(LorMat1, LorMat2, eFamEXT1, eFamEXT2, eMatrB)
  if IsIntegralMat(eMatrB)=false then
    Error("Bug: he matrix should be integral");
  fi;
  if Inverse(eMatrB)*LorMat1*TransposedMat(Inverse(eMatrB))<>LorMat2 then
    Error("Bug: the matrix does not map the Lorentzian quadratic form");
  fi;
  if Set(eFamEXT1*eMatrB)<>Set(eFamEXT2) then
    Error("Bug: the matrix does not map the vector configurations");
  fi;
  return eMatrB;
end;


LORENTZ_TestEquivalence_General:=function(LorMat1, LorMat2, eFamEXT1, eFamEXT2)
  local eEquiv, eEquivB, eMatr, TheStrategy, ListVect1, ListVect2, eMatrB, GRP2;
  Print("Before LinPolytope_IsomorphismStabSubset_AddMat |eFamEXT1|=", Length(eFamEXT1), " |eFamEXT2|=", Length(eFamEXT2), "\n");
  eEquiv:=LinPolytope_IsomorphismStabSubset_AddMat(eFamEXT1, eFamEXT1, eFamEXT2, eFamEXT2, [LorMat1], [LorMat2]);
  Print("After LinPolytope_IsomorphismStabSubset_AddMat\n");
  if eEquiv=false then
    return false;
  fi;
  eMatr:=FindTransformation(eFamEXT1, eFamEXT2, eEquiv);
  if IsIntegralMat(eMatr) and Inverse(eMatr)*LorMat1*TransposedMat(Inverse(eMatr))=LorMat2 then
    return eMatr;
  fi;
  if AbsInt(DeterminantMat(BaseIntMat(eFamEXT1)))=1 then
    Error("It should have ended at this stage");
  fi;
  TheStrategy:=2;
  if TheStrategy=1 then
    ListVect1:=LORENTZ_GetDeterminingVectFamily(LorMat1, eFamEXT1);
    ListVect2:=LORENTZ_GetDeterminingVectFamily(LorMat2, eFamEXT2);
    eEquivB:=LinPolytope_IsomorphismStabSubset_AddMat(ListVect1, eFamEXT1, ListVect2, eFamEXT2, [LorMat1], [LorMat2]);
    if eEquivB=false then
      return false;
    fi;
    eMatrB:=FindTransformation(ListVect1, ListVect2, eEquivB);
  fi;
  if TheStrategy=2 then
    Print("Before LinPolytope_AutomorphismStabSubset_AddMat\n");
    GRP2:=LinPolytope_AutomorphismStabSubset_AddMat(eFamEXT2, eFamEXT2, [LorMat2]);
    Print("After LinPolytope_AutomorphismStabSubset_AddMat\n");
    eMatrB:=KernelLinPolytopeIntegral_Isomorphism_Subspaces(eFamEXT1, eFamEXT2, GRP2, eEquiv);
    if eMatrB=false then
      Print("Subspaces algo returns false\n");
      return false;
    fi;
    Print("We have eMatrB\n");
  fi;
  return LORENTZ_TestEquivalence_CheckAndReturn(LorMat1, LorMat2, eFamEXT1, eFamEXT2, eMatrB);
end;



LORENTZ_TestEquivalence_Specific:=function(LorMat1, LorMat2, eFamEXT1, eFamEXT2, TheHeuristic)
  local RecAnsatz1, RecAnsatz2, test, eMatrB, Qmat1, Qmat2, TheSub1, TheSub2;
  Print("Beginning of LORENTZ_TestEquivalence_Specific\n");
  #
  Qmat1:=Get_QinvMatrix(eFamEXT1);
  Print("We have Qmat1\n");
  TheSub1:=LORENTZ_GetAnsatzSubpolytope(LorMat1, eFamEXT1, Qmat1, TheHeuristic.HeuristicSub);
  Print("We have TheSub1\n");
  RecAnsatz1:=LORENTZ_GetAnsatzGraphInformation(LorMat1, eFamEXT1{TheSub1}, Qmat1, TheHeuristic.HeuristicScal);
  Print("We have RecAnsatz1\n");
  #
  Qmat2:=Get_QinvMatrix(eFamEXT2);
  Print("We have Qmat2\n");
  TheSub2:=LORENTZ_GetAnsatzSubpolytope(LorMat2, eFamEXT2, Qmat2, TheHeuristic.HeuristicSub);
  if Length(TheSub1)<>Length(TheSub2) then
    Print("Returning false at this case |TheSub1|=", Length(TheSub1), " |TheSub2|=", Length(TheSub2), "\n");
    return false;
  fi;
  Print("We have TheSub2\n");
  RecAnsatz2:=LORENTZ_GetAnsatzGraphInformation(LorMat2, eFamEXT2{TheSub2}, Qmat2, TheHeuristic.HeuristicScal);
  Print("We have RecAnsatz2\n");
  #
  if TheHeuristic.BlockMethod="PolytopeIntegral" then
    eMatrB:=LinPolytopeIntegral_Isomorphism(eFamEXT1{TheSub1}, eFamEXT2{TheSub2});
  else
    test:=EquivalenceVertexColoredGraphAdjList(RecAnsatz1.ListAdjacency, RecAnsatz2.ListAdjacency, RecAnsatz1.ThePartition);
    Print("We have test\n");
    if test=false then
      Print("Returning false at second case\n");
      return false;
    fi;
    eMatrB:=FindTransformation(eFamEXT1{TheSub1}, eFamEXT2{TheSub2}, PermList(test));
  fi;
  Print("We have eMatrB\n");
  if eMatrB=false then
    return false;
  fi;
  return LORENTZ_TestEquivalence_CheckAndReturn(LorMat1, LorMat2, eFamEXT1, eFamEXT2, eMatrB);
end;



LORENTZ_TestEquivalence:=function(LorMat, eFamEXT1, eFamEXT2)
  return LORENTZ_TestEquivalence_General(LorMat, LorMat, eFamEXT1, eFamEXT2);
end;



LORENTZ_IsPerfectConf:=function(LorMat, ListVect)
  local test, n, nbVect, ListB, eSol, eVect, eNorm, ListScal, MaxScal, ListIso, ListCount, OnlyShortest;
  Print("Beginning of LORENTZ_IsPerfectConf\n");
  test:=First(ListVect, x->x*LorMat*x<>0);
  if test<>fail then
    return rec(reply:=false, reason:="Some vectors are not isotropic", eVect:=test);
  fi;
  n:=Length(LorMat);
  if RankMat(ListVect)<>n then
    return rec(reply:=false, reason:="family not of full rank", rnk:=RankMat(ListVect));
  fi;
  eVect:=LORENTZ_GetDefiningIneq(LorMat, ListVect);
  eNorm:=eVect*LorMat*eVect;
  ListScal:=List(ListVect, x->x*LorMat*eVect);
  if Length(Set(ListScal))<>1 then
    Error("Error somewhere");
  fi;
  MaxScal:=ListScal[1];
  if eNorm<=0 then
    return rec(reply:=false, reason:="Not right norm", eNorm:=eNorm);
  fi;
  OnlyShortest:=false;
  ListIso:=LORENTZ_FindPositiveVectors(LorMat, eVect, MaxScal, "total", OnlyShortest);
  ListCount:=Filtered(ListIso, x->eVect*LorMat*x<MaxScal);
  if Length(ListCount)>0 then
    return rec(reply:=false, reason:="nearer vectors", ListCount:=ListCount);
  else
    return rec(reply:=true, ListVect:=ListIso, eVect:=eVect);
  fi;
end;


GetRationalIsotropyVectors:=function(LorMat22)
    local a, b, c, DeltaB, TheSqrt, root1, root2, v1, v2;
    # The matrix is written as
    # | a b |
    # | b c |
    # The quadratic form is a x^2 + 2b x y + c y^2
    # We have Delta = 4 (b^2 - a c)
    # So { a (x / y)^2 + 2b (x/y) + c } y^2
    # This gets us
    # x1 / y1 = (-2 b + sqrt(Delta) ) / (2a)
    #         = (-b + sqrt(DeltaB)) / a
    # x2 / y2 = (-2 b - sqrt(Delta) ) / (2a)
    #         = (-b - sqrt(DeltaB) ) / a
    a:=LorMat22[1][1];
    b:=LorMat22[1][2];
    c:=LorMat22[2][2];
    DeltaB:=b*b - a*c;
    if DeltaB < 0 then
        Error("If the discriminant is negative, then we cannot have signature (1,1)");
    fi;
    TheSqrt:=RatSqrt(DeltaB);
    if TheSqrt = fail then
        return [];
    fi;
    if a<>0 then
        root1:=(-b + TheSqrt) / a;
        root2:=(-b - TheSqrt) / a;
        v1:=[ root1, 1];
        v2:=[ root2, 1];
        return [v1, v2];
    fi;
    v1:=[1,0];
    # Remaining equation is 2 b x + c y = 0
    v2:=[-c, 2*b];
    return [v1, v2];
end;



# We compute an upper bound TheMult on the possible values of x such that
# eNSP = eNSPbas + x * eNSPdir is admissible as a facet vector
#
# We also check for the isotropy situation that could happen and report it
# on the output. That is if the best x_upp gives eNSP[1] = 0 and eNSP{[2..n+1]}
# is isotropic than in the following call to the LORENTZ_FindPositiveVectors
# the following happens:
# -- MaxScal = 0 (because eNSP[1] = 0)
# -- eVect * LorMat * fVect = 0 (because 0 <= val <= 0)
# -- Thus fVect is in the orthogonal of an isotropic vector and is of norm >= 0.
# -- By the geometry this gets us to fVect a multiple of eVect
# That scenario is not acceptable for finding perfect domain.
GetUpperBound:=function(LorMat, eNSPbas, eNSPdir)
    local n, eCstBas, eCstDir, eBas, eDir, eVectBas, eVectDir, eNorm, iShift, eV, eVect, ListUpperBound, TheBasis, LorMat22, fact, ListIso, eIso, BestUpper, UpperBound_constant, UpperBound_isotropic, ListUpperBound_Iso;
    n:=Length(LorMat);
    eCstBas:=eNSPbas[1];
    eCstDir:=eNSPdir[1];
    eBas:=eNSPbas{[2..n+1]};
    eDir:=eNSPdir{[2..n+1]};
    Print("eCstBas=", eCstBas, " eCstDir=", eCstDir, "\n");
    # For an acceptable vector w of length n+1 in return we must have w[1] < 0.
    # Since we have w = u + TheMult * v we have a potential upper bound
    # on TheMult, but only if v[1] > 0
    ListUpperBound:=[];
    UpperBound_constant:=fail;
    if eCstDir>0 then
        UpperBound_constant:=-eCstBas / eCstDir;
        if UpperBound_constant <= 0 then
            Error("The upper bound from constant is not correct");
        fi;
        Add(ListUpperBound, UpperBound_constant);
    fi;
    #
    # Get Raw upper bound
    #
    iShift:=1;
    while(true)
    do
        eV:=eBas + iShift * eDir;
        eVect:=eV * Inverse(LorMat);
        if eVect * LorMat * eVect < 0 then
            Add(ListUpperBound, iShift);
            break;
        fi;
        iShift:=iShift * 2;
    od;
    #
    # More subttle upper bound coming from isotropy computation
    #
    eVectBas:=eBas * Inverse(LorMat);
    eVectDir:=eDir * Inverse(LorMat);
    TheBasis:=[eVectBas, eVectDir];
    LorMat22:=TheBasis * LorMat * TransposedMat(TheBasis);
    ListIso:=GetRationalIsotropyVectors(LorMat22);
    UpperBound_isotropic:=fail;
    ListUpperBound_Iso:=[];
    for eIso in ListIso
    do
        if eIso[1] <> 0 then
            fact:=eIso[2] / eIso[1];
            eVect:=eVectBas + fact * eVectDir;
            if eVect * LorMat * eVect <> 0 then
                Error("eVect should be isotropic");
            fi;
            if fact > 0 then
                Add(ListUpperBound_Iso, fact);
            fi;
        fi;
    od;
    if Length(ListUpperBound_Iso) > 0 then
        UpperBound_isotropic:=Minimum(ListUpperBound_Iso);
        Add(ListUpperBound, UpperBound_isotropic);
    fi;
    if UpperBound_constant<>fail and UpperBound_isotropic<>fail then
        if UpperBound_constant = UpperBound_isotropic then
            return fail;
        fi;
    fi;
    # Need to see if better upper bounds are possible, but this is a secondary question
    BestUpper:=Minimum(ListUpperBound);
    eV:=eBas + BestUpper * eDir;
    eVect:=eV * Inverse(LorMat);
    eNorm:=eVect * LorMat * eVect;
    if eNorm > 0 then
        Error("We should have eNorm <= 0");
    fi;
    return BestUpper;
end;




# Given a Critical set a vector eNSPbas and a direction eNSPdir
# we are looking for a lambda > 0 such that eNSP = eNSPbas + lambda * eNSPdir
# such that the list of vectors satisfying eNSP * v = 0 defines a bigger
# set than CritSet.
#
# eNSPbas must be of positive norm. eNSPdir must be of negative norm.
#
LORENTZ_Kernel_Flipping:=function(LorMat, CritSet, eNSPbas, eNSPdir, TheOption)
  local n, EXT, NSP, eVert, eEXT, eNSP, NSPb, eNSPb, eNSPtest, eVectTest, MaxScal, ListTotal, EXTtest, ListIsoTest, NSPtest, eVectB, eNormTest, eVect, OnlyShortest, eDen, aShift, TheLowerBound, TheUpperBound, uVal, vVal, TheMidVal, n_iter, eVectBas, eVectDir, eNormBas, eNormDir, eVectBasDir, eNormBasDir, GetMidVal;
#  SaveDebugInfo("LORENTZ_Kernel_Flipping", rec(LorMat:=LorMat, CritSet:=CritSet, eNSPbas:=eNSPbas, eNSPdir:=eNSPdir, TheOption:=TheOption));

  Print("Beginning of LORENTZ_Kernel_Flipping\n");
  Print("LorMat=\n");
  PrintArray(LorMat);
  Print("CritSet=");
  PrintArray(CritSet);
  Print("eNSPbas=", eNSPbas, "  eNSPdir=", eNSPdir, "\n");
  Print("TheOption=", TheOption, "\n");
  if RankMat([eNSPbas,eNSPdir])<>2 then
      Error("The vector eNSPbas and eNSPdir should be linearly independent");
  fi;
  if First(CritSet, x->Concatenation([1],x)*eNSPbas<>0)<>fail then
      Error("eNSPbas should have scalar product 0 with all entries in CritSet");
  fi;
  if First(CritSet, x->Concatenation([1],x)*eNSPdir<>0)<>fail then
      Error("eNSPdir should have scalar product 0 with all entries in CritSet");
  fi;
  if TheOption="isotrop" then
    if First(CritSet, x->x*LorMat*x<>0)<>fail then
      Print("CritSet=", CritSet, "\n");
      Error("CritSet contains some non-isotrop vectors");
    fi;
  fi;
  n:=Length(LorMat);
  OnlyShortest:=true;
  TheLowerBound:=0;
  TheUpperBound:=GetUpperBound(LorMat, eNSPbas, eNSPdir);
  Print("At the beginning TheUpperBound=", TheUpperBound, "\n");
  n_iter:=0;
  eVectBas:=RemoveFraction(eNSPbas{[2..n+1]}*Inverse(LorMat));
  eVectDir:=RemoveFraction(eNSPdir{[2..n+1]}*Inverse(LorMat));
  eNormBas:=eVectBas * LorMat * eVectBas;
  eNormDir:=eVectDir * LorMat * eVectDir;
  eVectBasDir:=eVectBas + eVectDir;
  GetMidVal:=function(TheLow, TheUpp)
      local eFrac, TargetLow, TargetUpp, TheSeq, eVal;
      eFrac:=(TheLow + TheUpp) / 2;
      TargetLow:=(2*TheLow + TheUpp) / 3;
      TargetUpp:=(TheLow + 2*TheUpp) / 3;
      TheSeq:=GetSequenceContinuousFractionApproximant(eFrac);
      Print("TheSeq=", TheSeq, "\n");
      for eVal in TheSeq
      do
          if TargetLow <= eVal and eVal <= TargetUpp then
              return eVal;
          fi;
      od;
      Error("Should never reach that stage");
  end;
  while(true)
  do
    Print("TheLowerBound=", TheLowerBound, " TheUpperBound=", TheUpperBound, "\n");
    TheMidVal:=GetMidVal(TheLowerBound, TheUpperBound);
    eNSPtest:=eNSPbas + TheMidVal * eNSPdir;
    eVectTest:=RemoveFraction(eNSPtest{[2..n+1]}*Inverse(LorMat));
    eNormTest:=eVectTest*LorMat*eVectTest;
    MaxScal:=CritSet[1]*LorMat*eVectTest;
#    Print("TheMidVal=", TheMidVal, " eNormTest=", eNormTest, " MaxScal=", MaxScal, " eNSPtest=", eNSPtest, " eVectTest=", eVectTest, "\n");
    Print("TheMidVal=", TheMidVal, " eNormTest=", eNormTest, " MaxScal=", MaxScal, " eNSPtest=", eNSPtest, "\n");

    if eNormTest <= 0 or MaxScal <= 0 then
      TheUpperBound:=TheMidVal;
    else
      ListTotal:=LORENTZ_FindPositiveVectors(LorMat, eVectTest, MaxScal, TheOption, OnlyShortest);
#      Print("ListTotal=", ListTotal, "\n");
      Print("  |ListTotal|=", Length(ListTotal), "\n");
      if IsSubset(CritSet, Set(ListTotal)) and Length(CritSet) > Length(ListTotal) then
        Error("Bug: if included, it should be equal");
      fi;
      if Set(ListTotal)=Set(CritSet) then
        TheLowerBound:=TheMidVal;
      else
        if IsSubset(Set(ListTotal), CritSet) then
          Print("EXIT 1 |ListTotal|=", Length(ListTotal), " NSPtest=", eNSPtest, " MaxScal=", MaxScal, "\n");
          return rec(ListTotal:=ListTotal, eNSPtest:=eNSPtest, eVectTest:=eVectTest, MaxScal:=MaxScal);
        else
          break;
        fi;
      fi;
    fi;
#    if n_iter > 10 then
#        Print("n_iter=", n_iter, " is too large\n");
#        Error("Stop here");
#    fi;
    n_iter:=n_iter+1;
  od;
  Print("Going to the second scheme\n");
  while(true)
  do
    eVect:=ListTotal[1];
    eVert:=Concatenation([1], eVect);
    ListIsoTest:=Concatenation(CritSet, [eVect]);
    aShift:=-( eNSPbas*eVert) / ( eNSPdir*eVert );
    eNSPtest:=eNSPbas + aShift*eNSPdir;
    Print(" aShift=", aShift, "\n");
    eVectTest:=RemoveFraction(eNSPtest{[2..n+1]}*Inverse(LorMat));
    MaxScal:=CritSet[1]*LorMat*eVectTest;
#    SaveDebugInfo("LORENTZ_FindPositiveVectors", rec(LorMat:=LorMat, eVectTest:=eVectTest, MaxScal:=MaxScal, TheOption:=TheOption, OnlyShortest:=OnlyShortest));
    ListTotal:=LORENTZ_FindPositiveVectors(LorMat, eVectTest, MaxScal, TheOption, OnlyShortest);
    if IsSubset(Set(ListTotal), Set(ListIsoTest)) then
      Print("EXIT 2 |ListTotal|=", Length(ListTotal), " NSPtest=", eNSPtest, " MaxScal=", MaxScal, "\n");
      return rec(ListTotal:=ListTotal, eNSPtest:=eNSPtest, eVectTest:=eVectTest, MaxScal:=MaxScal);
    fi;
  od;
end;


# We want to find a short vector of positive norm in a Lorentzian matrix

LORENTZ_GetShortPositiveVector:=function(LorMat)
    local L1_Norm, n, GraverBasis, k, LVect, eVect, fVect, eSet, DirectImprovement, ePerturb, n_no_improv, CurrNorm, CurrVect, LorMat_Pert, TheVect, eNorm, norm1, norm2, uVect, ListCurrVect, i, GetAlpha, uVect_Pert;
    n:=Length(LorMat);
    L1_Norm:=function(eMat)
        return Sum(List(eMat, x->Sum(List(x, AbsInt))));
    end;
    GraverBasis:=[];
    for k in [1..2]
    do
        LVect:=BuildSet(k, [-1,1]);
        for eSet in Combinations([1..n], k)
        do
            eVect:=ListWithIdenticalEntries(n,0);
            for fVect in LVect
            do
                for i in [1..k]
                do
                    eVect[eSet[i]] := fVect[i];
                od;
                Add(GraverBasis, ShallowCopy(eVect));
            od;
        od;
    od;
    GetAlpha:=function(TheVect, DirVect)
        local Norm1, Norm2, NewVect, alpha;
        Norm1:=TheVect * LorMat * TheVect;
        alpha:=0;
        while(true)
        do
            NewVect:=TheVect + (alpha+1) * DirVect;
            Norm2:=NewVect * LorMat * NewVect;
            if Norm2 < Norm1 and Norm2 > 0 then
                Norm1:=Norm2;
                alpha:=alpha+1;
            else
                return alpha;
            fi;
        od;
    end;
    DirectImprovement:=function(TheVect)
        local ImpVect, NoImprov, eVectBasis, NewVect, NewNorm, n_chg, alpha;
        ImpVect:=TheVect;
        while(true)
        do
            n_chg:=0;
            for eVectBasis in GraverBasis
            do
                alpha:=GetAlpha(ImpVect, eVectBasis);
                ImpVect:=ImpVect + alpha * eVectBasis;
                Print("eVectBasis=", eVectBasis, " alpha=", alpha, "\n");
                n_chg:=n_chg + alpha;
            od;
            Print("n_chg=", n_chg, "\n");
            if n_chg = 0 then
                return ImpVect;
            fi;
        od;
    end;
    ePerturb:=IdentityMat(n);
    n_no_improv:=0;
    CurrNorm:=infinity;
    CurrVect:="unset";
    while(true)
    do
        LorMat_Pert:=ePerturb * LorMat * TransposedMat(ePerturb);
        uVect_Pert:=EigenvalueFindNegativeVect(-LorMat_Pert);
        uVect:=uVect_Pert * ePerturb;
        TheVect:=DirectImprovement(uVect);
        eNorm:=TheVect * LorMat * TheVect;
        Print("n_no_improv=", n_no_improv, "  eNorm=", eNorm, " TheVect=", TheVect, " CurrNorm=", CurrNorm, "\n");
        if eNorm <= 0 then
            Error("eNorm should be strictly positive");
        fi;
        if eNorm < CurrNorm then
            n_no_improv:=0;
            CurrVect:=TheVect;
            CurrNorm:=eNorm;
        else
            n_no_improv:=n_no_improv+1;
        fi;
        if n_no_improv=500 or CurrNorm < 10 then
            if CurrVect="unset" then
                Error("CurrVect is unset");
            fi;
            return CurrVect;
        fi;
        norm1:=L1_Norm(LorMat_Pert);
        norm2:=L1_Norm(LorMat);
        if norm1 > 10000 * norm2 then
            ePerturb:=IdentityMat(n);
        fi;
        ePerturb:=ePerturb * GetRandomMatrixPerturbation(n);
    od;
end;







# Given a Lorentzian form, find:
# ListTotal: vectors that correspond to a perfect form
# eNSPtest: A vector v such that v*w = 0 for all w in ListTotal
# CentralVect: A vectors v of positive norm that correspond essentially
#    to one of the selected cones.
LORENTZ_GetOnePerfect:=function(LorMat, TheOption)
    local eRec, n, pos, eVect, eScal, CritSet, eNSPbas, EXT, NSP, eVEctB, eNSPdir, eRecB, rnk, eVectB, CentralVect, IsInCone, ListDir, GetOneOutsideRay, Viso, CheckVectorEXT;
    n:=Length(LorMat);
    Print("Beginning of LORENTZ_GetOnePerfect, TheOption=", TheOption, "LorMat=\n");
    PrintArray(LorMat);
    if LORENTZ_IsLorentzian(LorMat)=false then
        Error("LorMat should be Lorentzian");
    fi;
    GetOneOutsideRay:=function(SpannBasis, TheSet)
        local TheMat, n_dim, uVect, RetVect, ListScal, eScal, TheNorm, ePerturb, TheMatPerturb;
        TheMat:=SpannBasis * LorMat * TransposedMat(SpannBasis);
        Print("From SpannBasis, TheMat=\n");
        PrintArray(TheMat);
        if DiagonalizeSymmetricMatrix(TheMat).nbMinus=0 then
            Error("We should have a negative entry in the matrix");
        fi;
        n_dim:=Length(TheMat);
        ePerturb:=IdentityMat(n_dim);
        while(true)
        do
            TheMatPerturb:=ePerturb * TheMat * TransposedMat(ePerturb);
            uVect:=EigenvalueFindNegativeVect(TheMatPerturb);
            RetVect:=uVect * ePerturb * SpannBasis;
            TheNorm:=RetVect * LorMat * RetVect;
            Print("TheNorm=", TheNorm, "\n");
            if TheNorm >= 0 then
                Error("The vector should be outside of the cone and so have negative norm");
            fi;
            ListScal:=List(TheSet, x->x*LorMat*RetVect);
            if Length(Set(ListScal))<>1 then
                Error("The scalar products should all be the same");
            fi;
            eScal:=ListScal[1];
            eNSPdir:=Concatenation([-eScal], LorMat*RetVect);
            # We need to check for the bad scenario of obtaining an isotropic space 
            if GetUpperBound(LorMat, eNSPbas, eNSPdir)<>fail then
                return eNSPdir;
            fi;
            ePerturb:=ePerturb * GetRandomMatrixPerturbation(n_dim);
        od;
    end;
    CheckVectorEXT:=function(EXT, eVect)
        if First(EXT, x->x*eVect<>0)<>fail then
            Error("Please debug from here Lorentzian CheckVectorEXT");
        fi;
    end;
    CentralVect:=LORENTZ_GetShortPositiveVector(LorMat);
    Print("CentralVect=", CentralVect, "\n");
#  Print(NullMat(5));
    if n > 4 and false then # In that case an isotropic vector
        Print("Running isotropic code\n");
        Viso:=INDEF_FindIsotropic(LorMat);
        eScal:=Viso * LorMat * CentralVect;
        Print("eScal=", eScal, "\n");
        if eScal < 0 then
            Viso:=-Viso;
        fi;
        CritSet:=[Viso];
    else
        Print("Running classic SearchInitialVector code\n");
        CritSet:=LORENTZ_SearchInitialVector(LorMat, CentralVect, TheOption);
    fi;
    eScal:=CritSet[1]*LorMat*CentralVect;
    Print("|CritSet|=", Length(CritSet), " eScal=", eScal, " l_norm=", List(CritSet, x->x*LorMat*x), "\n");
    eNSPbas:=Concatenation([-eScal], CentralVect*LorMat);
    while(true)
    do
        rnk:=RankMat(CritSet);
        Print("LORENTZ_GetOnePerfect: rnk=", rnk, " ListTotal=", Set(CritSet), "\n");
        if rnk = n then
            LORENTZ_CheckCorrectnessVectorFamily(CritSet);
            return rec(ListTotal:=CritSet, eNSPtest:=eNSPbas, eVectTest:=CentralVect);
        fi;
        EXT:=List(CritSet, x->Concatenation([1], x));
        CheckVectorEXT(EXT, eNSPbas);
        NSP:=NullspaceMat(TransposedMat(EXT));
        if Length(NSP)=0 then
            Error("NSP should be non-empty");
        fi;
        Print("LORENTZ_GetOnePerfect: |NSP|=", Length(NSP), "\n");
        ListDir:=List(NSP, x->RemoveFraction(x{[2..n+1]}*Inverse(LorMat)));
        eNSPdir:=GetOneOutsideRay(ListDir, CritSet);
        CheckVectorEXT(EXT, eNSPdir);
        Print("LORENTZ_GetOnePerfect: eNSPdir=", eNSPdir, "\n");
        eRecB:=LORENTZ_Kernel_Flipping(LorMat, CritSet, eNSPbas, eNSPdir, TheOption);
        CritSet:=eRecB.ListTotal;
        eNSPbas:=RemoveFraction(eRecB.eNSPtest);
    od;
end;













# The function computes the flipping.
# It is essentially just a syntactic sugar of the LORENTZ_Kernel_Flipping
LORENTZ_DoFlipping:=function(LorMat, ListIso, eInc, TheOption)
  local n, EXT, NSP, eVert, eEXT, eNSP, NSPb, eNSPb, iShift, CritSet, eNSPtest, eVectTest, MaxScal, ListTotal, EXTtest, ListIsoTest, NSPtest, eVectB, eNormTest, eNSPdir, eNSPbas, TheFlip;
  if LORENTZ_IsLorentzian(LorMat)=false then
    Error("LorMat should be Lorentzian");
  fi;
  n:=Length(LorMat);
  EXT:=List(ListIso, x->Concatenation([1], x));
  eVert:=Difference([1..Length(EXT)], eInc)[1];
  eEXT:=EXT[eVert];
  NSP:=NullspaceMat(TransposedMat(ListIso{eInc}));
  if Length(NSP)<>1 then
    Error("The array NSP should have size 1");
  fi;
  if NSP[1]*ListIso[eVert]<0 then
    eNSPdir:=RemoveFraction(Concatenation([0], -NSP[1]));
  else
    eNSPdir:=RemoveFraction(Concatenation([0],  NSP[1]));
  fi;
  NSPb:=NullspaceMat(TransposedMat(EXT));
  eVectB:=NSPb[1]{[2..n+1]};
  if eVectB*ListIso[eVert]>0 then
    eNSPbas:=RemoveFraction(NSPb[1]);
  else
    eNSPbas:=RemoveFraction(-NSPb[1]);
  fi;
  CritSet:=Set(ListIso{eInc});
  TheFlip:=LORENTZ_Kernel_Flipping(LorMat, CritSet, eNSPbas, eNSPdir, TheOption).ListTotal;
  LORENTZ_CheckCorrectnessVectorFamily(TheFlip);
  return TheFlip;
end;


LORENTZ_GetIndependentDirection:=function(LorMat, CritSet)
  local CentralVect, n, rnkCrit, a, eVect, i;
  CentralVect:=EigenvalueFindNegativeVect(-LorMat);
  n:=Length(LorMat);
  rnkCrit:=RankMat(CritSet);
  if RankMat(Concatenation(CritSet, [CentralVect]))=rnkCrit+1 then
    return CentralVect;
  fi;
  a:=2;
  while(true)
  do
    eVect:=[];
    for i in [1..n]
    do
      Add(eVect, Random([-a..a]));
    od;
    if RankMat(Concatenation(CritSet, [eVect]))=rnkCrit+1 then
      break;
    fi;
  od;
  while(true)
  do
    if eVect*LorMat*eVect>0 then
      return eVect;
    fi;
    eVect:=eVect + CentralVect;
  od;
end;


LORENTZ_PrintInfinityInformation:=function(eRecComplex)
  local	TheDim, nbPerf, nbCusp, iPerf, ListListMatch, iDim, eListMatch, iIdx, IsConjectureOk;
  TheDim:=Length(eRecComplex.ListListCells);
  nbPerf:=Length(eRecComplex.ListListCells[1]);
  nbCusp:=Length(eRecComplex.ListListCells[TheDim]);
  IsConjectureOk:=true;
  for iPerf in [1..nbPerf]
  do
    ListListMatch:=[ [iPerf] ];
    for iDim in [2..TheDim]
    do
      eListMatch:=[];
      for iIdx in ListListMatch[iDim-1]
      do
        Append(eListMatch, eRecComplex.ListListBoundary[iDim-1][iIdx].ListIFace);
      od;
      Add(ListListMatch, Set(eListMatch));
    od;
    if Length(ListListMatch[TheDim])<>nbCusp then
      Print("nbPerf=", nbPerf, " nbCusp=", nbCusp, "\n");
      Print("iPerf=", iPerf, " ListListMatch=", ListListMatch, "\n");
      IsConjectureOk:=false;
    fi;
  od;
  return IsConjectureOk;
end;


LORENTZ_PrintInfinityInformation_IsStrongCounterexample:=function(eRecComplex)
  local	TheDim, nbPerf, nbCusp, iPerf, ListListMatch, iDim, eListMatch, iIdx, IsConjectureOk, ListPerfectUnmatched, TheDiff;
  TheDim:=Length(eRecComplex.ListListCells);
  nbPerf:=Length(eRecComplex.ListListCells[1]);
  nbCusp:=Length(eRecComplex.ListListCells[TheDim]);
  ListPerfectUnmatched:=[];
  for iPerf in [1..nbPerf]
  do
    ListListMatch:=[ [iPerf] ];
    for iDim in [2..TheDim]
    do
      eListMatch:=[];
      for iIdx in ListListMatch[iDim-1]
      do
        Append(eListMatch, eRecComplex.ListListBoundary[iDim-1][iIdx].ListIFace);
      od;
      Add(ListListMatch, Set(eListMatch));
    od;
    TheDiff:=Difference([1..nbCusp], ListListMatch[TheDim]);
    Append(ListPerfectUnmatched, TheDiff);
  od;
  return Length(Set(ListPerfectUnmatched)) = nbCusp;
end;




#
# Using the ListVect, we get a slightly finer invariant.
# But the cost of computing ListVect can be tremendous, so better not to
# in general.
LORENTZ_Invariant:=function(LorMat, eFamEXT)
#  local ListVect;
#  ListVect:=LORENTZ_GetDeterminingVectFamily(LorMat, eFamEXT);
#  return GetScalarMatrixInvariant_PolytopeStabSubset_AddMat(ListVect, eFamEXT, [LorMat]);
  Print("Computing invariant for det(LorMat)=", DeterminantMat(LorMat), " |eFamEXT|=", Length(eFamEXT), "\n");
  return GetScalarMatrixInvariant_PolytopeStabSubset_AddMat(eFamEXT, eFamEXT, [LorMat]);
end;




LORENTZ_EnumeratePerfect:=function(LorMat)
  local ListFamily, FuncInsertVectFamily, IsFinished, nbOrb, iOrb, ListIso, EXT, ListOrb, eOrb, ListTotal, TheGRP, eInitial, eRec, BF, DataPolyhedral, FuncStabilizer, FuncIsomorphy, FuncInvariant, IsBankSave, TmpDir, IsRespawn, WorkingDim, eAdj, ListAdj, iOrbFac, nbOrbFac, nbOrbitTreated, GetFullComplex, EXTfacet, EXTneigh;
  ListFamily:=[];
  FuncStabilizer:=LinPolytope_Automorphism;
  FuncIsomorphy:=LinPolytope_Isomorphism;
  FuncInvariant:=LinPolytope_Invariant;
  WorkingDim:=Length(LorMat);
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if EllapsedTime>=600 then
      return true;
    fi;
    if Length(EXT)<=WorkingDim+5 then
      return false;
    fi;
    return true;
  end;
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if OrdGRP>=50000 and TheDepth<=2 then
      return true;
    fi;
    if OrdGRP<100 then
      return false;
    fi;
    if Length(EXT)<WorkingDim+20 then
      return false;
    fi;
    if TheDepth=2 then
      return false;
    fi;
    return true;
  end;
  TmpDir:=Filename(POLYHEDRAL_tmpdir, "");
  FuncInsertVectFamily:=function(eFamEXT)
    local eRecStab, eNewRec, eFamily, test, iFamily, eInv;
    eInv:=LORENTZ_Invariant(LorMat, eFamEXT);
    for iFamily in [1..Length(ListFamily)]
    do
      if ListFamily[iFamily].eInv=eInv then
        test:=LORENTZ_TestEquivalence(LorMat, ListFamily[iFamily].eFamEXT, eFamEXT);
        if test<>false then
          return rec(iFamily:=iFamily, eEquiv:=test);
        fi;
      fi;
    od;
    eRecStab:=LORENTZ_ComputeStabilizer(LorMat, eFamEXT);
    eNewRec:=rec(eRecStab:=eRecStab, eInv:=eInv, eFamEXT:=eFamEXT, Status:="NO");
    Add(ListFamily, eNewRec);
    Print("Now |ListFamily|=", Length(ListFamily), " new: |EXT|=", Length(eFamEXT), " |G|=", Order(eRecStab.GRP_int), "\n");
    return rec(iFamily:=Length(ListFamily), eEquiv:=IdentityMat(Length(LorMat)));
  end;
  eInitial:=LORENTZ_GetOnePerfect(LorMat, "isotrop").ListTotal;
  FuncInsertVectFamily(eInitial);
  BF:=BankRecording(rec(Saving:=false, BankPath:="/irrelevant/"), FuncStabilizer, FuncIsomorphy, FuncInvariant, OnSetsGroupFormalism(500));
  DataPolyhedral:=rec(IsBankSave:=IsBankSave,
        TheDepth:=0,
        IsRespawn:=IsRespawn,
        Saving:=false,
        GetInitialRays:=GetInitialRays_LinProg,
        ThePathSave:="/irrelevant/",
        ThePath:=TmpDir,
        DualDescriptionFunction:=__DualDescriptionLRS_Reduction,
        GroupFormalism:=OnSetsGroupFormalism(500));
  nbOrbitTreated:=0;
  while(true)
  do
    IsFinished:=true;
    nbOrb:=Length(ListFamily);
    for iOrb in [1..nbOrb]
    do
      if ListFamily[iOrb].Status="NO" then
        ListFamily[iOrb].Status:="YES";
        IsFinished:=false;
        ListIso:=ListFamily[iOrb].eFamEXT;
        EXT:=List(ListIso, x->Concatenation([1], x));
        TheGRP:=ListFamily[iOrb].eRecStab.GRP_int;
        Print("Working with |EXT|=", Length(EXT), " |GRP|=", Order(TheGRP), "\n");
        ListOrb:=__ListFacetByAdjacencyDecompositionMethod(EXT, TheGRP, DataPolyhedral, BF);
        nbOrbFac:=Length(ListOrb);
        ListAdj:=[];
        Print("nbOrbitTreated=", nbOrbitTreated, " |ListFamily|=", Length(ListFamily), "\n");
        for iOrbFac in [1..nbOrbFac]
        do
          eOrb:=ListOrb[iOrbFac];
          EXTfacet:=ListIso{eOrb};
          Print("   iOrbFac=", iOrbFac, "/", nbOrbFac, " |eOrb|=", Length(eOrb), "\n");
          ListTotal:=LORENTZ_DoFlipping(LorMat, ListIso, eOrb, "isotrop");
          eAdj:=FuncInsertVectFamily(ListTotal);
          EXTneigh:=ListFamily[eAdj.iFamily].eFamEXT*eAdj.eEquiv;
          if IsSubset(Set(EXTneigh), Set(EXTfacet))=false then
            Error("Inconsistency in Lorentzian neighbor facet search");
          fi;
          eAdj.eOrb:=eOrb;
          Add(ListAdj, eAdj);
        od;
        ListFamily[iOrb].ListAdj:=ListAdj;
        nbOrbitTreated:=nbOrbitTreated+1;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  GetFullComplex:=function()
    local ListListAdjInfo, eFamily, TheGRP, ListAdjInfo, nbAdj, iAdj, eAdj, RecOrb, nbEnt, iEnt, eAdjInfo, TestEquivalenceTriple, SaturationAndStabilizer, TheDim, ListCells, ListListCells, eSpMat, ListSpMat, i, iFamily, eTriple, eBasis, eRecCell, ListListBoundary, ListBoundary, GetPositionCell, eSum, ListIFace, ListElt, ListSign, ThePos, eSol, eBasisImg, TheQuot, TheSign, IsOrientable, eSet, fTriple, TheBound, nbCell1, nbCell2, ListIdx1, ListIdx2, ListEntries, ListCol, ListVal, pos, posB, eEntry, ListBoundaryImage, iFace, iCell, eGen, eMatB, eIdx, eSign, TheCoho, fRecCell;
    ListListAdjInfo:=[];
    for eFamily in ListFamily
    do
      TheGRP:=eFamily.eRecStab.GRP_int;
      ListAdjInfo:=[];
      nbAdj:=Length(eFamily.ListAdj);
      for iAdj in [1..nbAdj]
      do
        eAdj:=eFamily.ListAdj[iAdj];
        RecOrb:=OrbitWithAction(TheGRP, eAdj.eOrb, OnSets);
        nbEnt:=Length(RecOrb.ListElement);
        for iEnt in [1..nbEnt]
        do
          eAdjInfo:=rec(ePerm:=RecOrb.ListElement[iEnt], iAdj:=iAdj, eSet:=RecOrb.ListCoset[iEnt]);
          Add(ListAdjInfo, eAdjInfo);
        od;
      od;
      Add(ListListAdjInfo, ListAdjInfo);
    od;
    TestEquivalenceTriple:=function(eTriple1, eTriple2)
      local test, testMatr;
      if eTriple1.iPerfect<>eTriple2.iPerfect then
        return false;
      fi;
      test:=RepresentativeAction(ListFamily[eTriple1.iPerfect].eRecStab.GRP_int, eTriple1.eSet, eTriple2.eSet, OnSets);
      if test=fail then
        return false;
      fi;
      testMatr:=Image(ListFamily[eTriple1.iPerfect].eRecStab.PhiPermMat, test);
      return Inverse(eTriple1.eMat)*testMatr*eTriple2.eMat;
    end;
    SaturationAndStabilizer:=function(eTriple)
      local ListGenStab, ListTriple, ListStatus, FuncInsert, nbTriple, IsFinished, iTriple, iPerfect, jPerfect, eSet, fSet, eMat, fMat, eMatF, EXTimg, fTriple, eBasis, FuncInsertMatrGen, TheStab, eGenMatr;
      ListGenStab:=[];
      ListTriple:=[];
      ListStatus:=[];
      EXT:=ListFamily[eTriple.iPerfect].eFamEXT{eTriple.eSet}*eTriple.eMat;
      FuncInsertMatrGen:=function(eMat)
        Add(ListGenStab, eMat);
        if First(EXT, x->Position(EXT, x*eMat)=fail)<>fail then
          Error("Clearly the generator is wrong");
        fi;
      end;
      TheStab:=Stabilizer(ListFamily[eTriple.iPerfect].eRecStab.GRP_int, eTriple.eSet, OnSets);
      for eGen in GeneratorsOfGroup(TheStab)
      do
        eGenMatr:=Image(ListFamily[eTriple.iPerfect].eRecStab.PhiPermMat, eGen);
        FuncInsertMatrGen(eGenMatr);
      od;
      FuncInsert:=function(eTriple)
        local fTriple, test;
        for fTriple in ListTriple
        do
          test:=TestEquivalenceTriple(eTriple, fTriple);
          if test<>false then
            FuncInsertMatrGen(test);
            return;
          fi;
        od;
        Add(ListTriple, eTriple);
        Add(ListStatus, 1);
      end;
      FuncInsert(eTriple);
      while(true)
      do
        nbTriple:=Length(ListTriple);
        IsFinished:=true;
        for iTriple in [1..nbTriple]
        do
          if ListStatus[iTriple]=1 then
            ListStatus[iTriple]:=0;
            eTriple:=ListTriple[iTriple];
            iPerfect:=eTriple.iPerfect;
            eSet:=eTriple.eSet;
            eMat:=eTriple.eMat;
            IsFinished:=false;
            for eAdjInfo in ListListAdjInfo[iPerfect]
            do
              if IsSubset(eAdjInfo.eSet, eSet) then
                eMatF:=Image(ListFamily[iPerfect].eRecStab.PhiPermMat, eAdjInfo.ePerm);
                eAdj:=ListFamily[iPerfect].ListAdj[eAdjInfo.iAdj];
                jPerfect:=eAdj.iFamily;
                fMat:=eAdj.eEquiv*eMatF*eMat;
                EXTimg:=ListFamily[jPerfect].eFamEXT*fMat;
                fSet:=Set(List(EXT, x->Position(EXTimg, x)));
                if Position(fSet, fail)<>fail then
                  Error("Equivalence matrix error");
                fi;
                fTriple:=rec(iPerfect:=jPerfect, eMat:=fMat, eSet:=fSet);
                FuncInsert(fTriple);
              fi;
            od;
          fi;
        od;
        if IsFinished=true then
          break;
        fi;
      od;
      eBasis:=RowReduction(EXT).EXT;
      return rec(ListTriple:=ListTriple, GRP:=Group(ListGenStab), eBasis:=eBasis);
    end;
    TheDim:=Length(LorMat);
    ListListCells:=[];
    ListCells:=[];
    for iFamily in [1..Length(ListFamily)]
    do
      EXT:=ListFamily[iFamily].eFamEXT;
      eTriple:=rec(iPerfect:=iFamily, eMat:=IdentityMat(TheDim), eSet:=[1..Length(EXT)]);
      eBasis:=RowReduction(EXT).EXT;
      eRecCell:=rec(ListTriple:=[eTriple], GRP:=ListFamily[iFamily].eRecStab.GRPintMatr, eBasis:=eBasis);
      Add(ListCells, eRecCell);
    od;
    Add(ListListCells, ListCells);
    ListListBoundary:=[];
    for i in [2..TheDim]
    do
      ListCells:=[];
      GetPositionCell:=function(eTriple)
        local iCell, fTriple, test;
        for iCell in [1..Length(ListCells)]
        do
          for fTriple in ListCells[iCell].ListTriple
          do
            test:=TestEquivalenceTriple(fTriple, eTriple);
            if test<>false then
              return rec(iCell:=iCell, eMat:=test);
            fi;
          od;
        od;
        eRecCell:=SaturationAndStabilizer(eTriple);
        Add(ListCells, eRecCell);
        return rec(iCell:=Length(ListCells), eMat:=IdentityMat(TheDim));
      end;
      ListBoundaryImage:=[];
      for fRecCell in ListListCells[i-1]
      do
        eTriple:=fRecCell.ListTriple[1];
        EXT:=ListFamily[eTriple.iPerfect].eFamEXT{eTriple.eSet}*eTriple.eMat;
        eSum:=Sum(EXT);
        ListIFace:=[];
        ListElt:=[];
        ListSign:=[];
        for eSet in DualDescriptionSets(EXT)
        do
          fTriple:=rec(iPerfect:=eTriple.iPerfect, eMat:=eTriple.eMat, eSet:=eTriple.eSet{eSet});
          ThePos:=GetPositionCell(fTriple);
          eBasisImg:=Concatenation(ListCells[ThePos.iCell].eBasis*ThePos.eMat, [eSum]);
          eSol:=List(eBasisImg, x->SolutionMat(fRecCell.eBasis, x));
          TheQuot:=DeterminantMat(eSol);
          if TheQuot>0 then
            TheSign:=1;
          else
            TheSign:=-1;
          fi;
          Add(ListIFace, ThePos.iCell);
          Add(ListElt, ThePos.eMat);
          Add(ListSign, TheSign);
        od;
        TheBound:=rec(ListIFace:=ListIFace, ListElt:=ListElt, ListSign:=ListSign);
        Add(ListBoundaryImage, TheBound);
      od;
      Add(ListListCells, ListCells);
      Add(ListListBoundary, ListBoundaryImage);
    od;
    for i in [1..TheDim]
    do
      for iCell in [1..Length(ListListCells[i])]
      do
        IsOrientable:=true;
        eBasis:=ListListCells[i][iCell].eBasis;
        for eGen in GeneratorsOfGroup(ListListCells[i][iCell].GRP)
        do
          eMatB:=List(eBasis, x->SolutionMat(eBasis, x*eGen));
          if DeterminantMat(eMatB)=-1 then
            IsOrientable:=false;
          fi;
        od;
        ListListCells[i][iCell].IsOrientable:=IsOrientable;
      od;
    od;
    ListSpMat:=[];
    for i in [2..TheDim]
    do
      nbCell1:=Length(ListListCells[i-1]);
      nbCell2:=Length(ListListCells[i]);
      ListIdx1:=Filtered([1..nbCell1], x->ListListCells[i-1][x].IsOrientable=true);
      ListIdx2:=Filtered([1..nbCell2], x->ListListCells[i][x].IsOrientable=true);
      ListEntries:=[];
      for eIdx in ListIdx1
      do
        TheBound:=ListListBoundary[i-1][eIdx];
        nbEnt:=Length(TheBound.ListIFace);
        ListCol:=[];
        ListVal:=[];
        for iEnt in [1..nbEnt]
        do
          iFace:=TheBound.ListIFace[iEnt];
          pos:=Position(ListIdx2, iFace);
          if pos<>fail then
            posB:=Position(ListCol, pos);
            eSign:=TheBound.ListSign[iEnt];
            if posB<>fail then
              ListVal[posB]:=ListVal[posB]+eSign;
            else
              Add(ListCol, pos);
              Add(ListVal, eSign);
            fi;
          fi;
        od;
        eEntry:=rec(ListCol:=ListCol, ListVal:=ListVal);
        Add(ListEntries, eEntry);
      od;
      eSpMat:=rec(nbLine:=Length(ListIdx1), nbCol:=Length(ListIdx2), ListEntries:=ListEntries);
      Add(ListSpMat, eSpMat);
    od;
    TheCoho:=GettingCohomologyFromSparseMatrices(ListSpMat);
    return rec(ListListCells:=ListListCells,
               ListListBoundary:=ListListBoundary,
               ListSpMat:=ListSpMat,
               TheCoho:=TheCoho);
  end;
  return rec(ListFamily:=ListFamily,
             GetFullComplex:=GetFullComplex);
end;




LORENTZ_EnumeratePerfect_DelaunayScheme:=function(LorMat, RecInput)
  local n, FuncStabilizer, FuncIsomorphy, FuncInvariant, WorkingDim, IsBankSave, IsRespawn, BF, IsSaving, MainPath, ThePathSave, ThePathTmp, PathPermanent, FindAdjacentDelaunay, KillingDelaunay, KillingAdjacency, DataLattice, DataPolyhedral, TheReply, DelaunayDatabase, EXT, eStab, FuncStabilizerDelaunay, FuncIsomorphismDelaunay, MaximalMemorySave, ListFamily, iOrb, TheRec, TheOption, ListVertAnsatz, ListAnsatzInfo, TestNeedMoreSymmetry, testSym, ListAdj, eInv;
  n:=Length(LorMat)-1;
  FuncStabilizer:=LinPolytope_Automorphism;
  FuncIsomorphy:=LinPolytope_Isomorphism;
  FuncInvariant:=LinPolytope_Invariant;
  TheOption:="isotrop";
  if IsBound(RecInput.TheOption) then
    TheOption:=RecInput.TheOption;
  fi;
  KillingDelaunay:=function(EXT, eInv)
    return false;
  end;
  if IsBound(RecInput.KillingDelaunay) then
    KillingDelaunay:=RecInput.KillingDelaunay;
  fi;
  WorkingDim:=Length(LorMat);
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if EllapsedTime>=600 then
      return true;
    fi;
    if Length(EXT)<=WorkingDim+5 then
      return false;
    fi;
    return true;
  end;
  if IsBound(RecInput.IsBankSave) then
    IsBankSave:=RecInput.IsBankSave;
  fi;
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if OrdGRP>=50000 and TheDepth<=2 then
      return true;
    fi;
    if OrdGRP<100 then
      return false;
    fi;
    if Length(EXT)<WorkingDim+20 then
      return false;
    fi;
    if TheDepth=2 then
      return false;
    fi;
    return true;
  end;
  if IsBound(RecInput.IsRespawn) then
    IsRespawn:=RecInput.IsRespawn;
  fi;
  BF:=BankRecording(rec(Saving:=false, BankPath:="/irrelevant/"), FuncStabilizer, FuncIsomorphy, FuncInvariant, OnSetsGroupFormalism(500));
  IsSaving:=false;
  if IsBound(RecInput.IsSaving) then
    IsSaving:=RecInput.IsSaving;
  fi;
  MainPath:="/irrelevant/";
  if IsBound(RecInput.MainPath) then
    MainPath:=RecInput.MainPath;
  fi;
  ThePathSave:=Concatenation(MainPath, "Saving/");
  if MainPath<>"/irrelevant/" then
    ThePathTmp:=Concatenation(MainPath, "tmp/");
  else
    ThePathTmp:=Filename(POLYHEDRAL_tmpdir, "");
  fi;
  PathPermanent:=Concatenation(MainPath, "Permanent/");
  if IsSaving then
    Exec("mkdir -p ", ThePathTmp);
    Exec("mkdir -p ", ThePathSave);
    Exec("mkdir -p ", PathPermanent);
  fi;
  TestNeedMoreSymmetry:=function(EXT)
    if Length(EXT) > RankMat(EXT) + 4 then
      return true;
    else
      return false;
    fi;
  end;
  if IsBound(RecInput.TestNeedMoreSymmetry) then
      testSym:=RecInput.TestNeedMoreSymmetry;
  else
      testSym:=TestNeedMoreSymmetry;
  fi;
  DataPolyhedral:=rec(IsBankSave:=IsBankSave,
        TheDepth:=0,
        IsRespawn:=IsRespawn,
        Saving:=IsSaving,
        GetInitialRays:=GetInitialRays_LinProg,
        TestNeedMoreSymmetry:=testSym,
        ThePathSave:=ThePathSave,
        ThePath:=ThePathTmp,
        FuncStabilizer:=FuncStabilizer,
        FuncIsomorphy:=FuncIsomorphy,
        FuncInvariant:=FuncInvariant,
        DualDescriptionFunction:=__DualDescriptionLRS_Reduction,
        GroupFormalism:=OnSetsGroupFormalism(500));
  #
  # The geometrical part
  #
  KillingAdjacency:=function(EXT1, EXT2)
    return false;
  end;
  ListAnsatzInfo:=[];
  if IsBound(RecInput.ListAnsatzInfo) then
    ListAnsatzInfo:=RecInput.ListAnsatzInfo;
  fi;
  ListVertAnsatz:=List(ListAnsatzInfo, x->x.nbVert);
  FuncStabilizerDelaunay:=function(eRec, EXT)
    local pos, RecRet;
    pos:=Position(ListVertAnsatz, Length(EXT));
    if pos<>fail then
      RecRet:=LORENTZ_ComputeStabilizer_Specific(LorMat, EXT, ListAnsatzInfo[pos].Heuristic);
    else
      RecRet:=LORENTZ_ComputeStabilizer(LorMat, EXT);
    fi;
    RecRet.PermutationStabilizer:=RecRet.GRP_int;
    return RecRet;
  end;
  FuncIsomorphismDelaunay:=function(eRec, EXT1, EXT2, eStab1)
    local pos;
    if Length(EXT1)<>Length(EXT2) then
      return false;
    fi;
    pos:=Position(ListVertAnsatz, Length(EXT1));
    if pos<>fail then
      return LORENTZ_TestEquivalence_Specific(LorMat, LorMat, EXT1, EXT2, ListAnsatzInfo[pos].Heuristic);
    else
      return LORENTZ_TestEquivalence(LorMat, EXT1, EXT2);
    fi;
  end;
  FindDelaunayPolytope:=function()
    return LORENTZ_GetOnePerfect(LorMat, TheOption).ListTotal;
  end;
  FuncInvariant:=function(eRec, EXT)
    return LORENTZ_Invariant(LorMat, EXT);
  end;
  FindAdjacentDelaunay:=function(EXT, eOrb)
    local ListVect;
    ListVect:=List(EXT, x->x{[2..n+1]});
    return LORENTZ_DoFlipping(LorMat, EXT, eOrb, TheOption);
  end;
  DataLattice:=rec(n:=n,
                   Saving:=IsSaving,
		   PathPermanent:=PathPermanent,
                   KillingDelaunay:=KillingDelaunay,
                   KillingAdjacency:=KillingAdjacency,
                   FindDelaunayPolytope:=FindDelaunayPolytope,
                   FindAdjacentDelaunay:=FindAdjacentDelaunay,
                   FuncInvariant:=FuncInvariant,
		   FuncIsomorphismDelaunay:=FuncIsomorphismDelaunay,
                   FuncStabilizerDelaunay:=FuncStabilizerDelaunay);
  #
  # The saving business part
  #
  MaximalMemorySave:=IsSaving;
  DelaunayDatabase:=DelaunayDatabaseManagement(PathPermanent, IsSaving, MaximalMemorySave);
  TheReply:=ComputeDelaunayDecomposition(DataLattice, DataPolyhedral, DelaunayDatabase);
  if TheReply<>"all was ok" then
    return TheReply;
  fi;
  ListFamily:=[];
  for iOrb in [1..DelaunayDatabase.FuncDelaunayGetNumber()]
  do
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iOrb);
    eInv:=DelaunayDatabase.FuncDelaunayGetINV(iOrb);
    eStab:=DelaunayDatabase.FuncDelaunayGetGroup(iOrb);
    ListAdj:=DelaunayDatabase.FuncDelaunayGetAdjacencies(iOrb);
    TheRec:=rec(EXT:=EXT, eInv:=eInv, eStab:=eStab, ListAdj:=ListAdj);
    Add(ListFamily, TheRec);
  od;
  return ListFamily;
end;



LORENTZ_EnumeratePerfect_ForIndefinite:=function(LorMat, TheOption)
    local RecInput;
    RecInput:=rec(TheOption:=TheOption);
    return LORENTZ_EnumeratePerfect_DelaunayScheme(LorMat, RecInput);
end;






LORENTZ_PrintEnumerationResult:=function(output, LorMat, ePrefix)
  local PreListSizes, PreListEXT, PreListDet, PreListInv, PreListGRP, PreListGRPsiz, ListDisc, i, eFileEXT, eFileINV, eFileGRP, EXT, eDet, eSize, eInv, eGRP, eDisc, nbCone, ePerm, ListSizes, ListEXT, ListInv, ListDet, ListGRP, ListGRPsiz, iCone, nbIso, nbNonIso, GRP_int;
  PreListSizes:=[];
  PreListEXT:=[];
  PreListDet:=[];
  PreListInv:=[];
  PreListGRP:=[];
  PreListGRPsiz:=[];
  ListDisc:=[];
  i:=1;
  while(true)
  do
    eFileEXT:=Concatenation(ePrefix, "ListEXT/DelaunayEXT", String(i));
    eFileINV:=Concatenation(ePrefix, "ListINV/DelaunayINV", String(i));
    eFileGRP:=Concatenation(ePrefix, "ListGRP/DelaunayGroup", String(i));
    if IsExistingFilePlusTouch(eFileEXT) then
      EXT:=ReadAsFunction(eFileEXT)();
      Print("i=", i, " |EXT|=", Length(EXT), "\n");
      eDet:=AbsInt(DeterminantMat(BaseIntMat(EXT)));
      eSize:=Length(EXT);
      eInv:=ReadAsFunction(eFileINV)();
      eGRP:=ReadAsFunction(eFileGRP)();
      eDisc:=[1/Length(EXT), 1/Order(eGRP.GRP_int)];
      Add(PreListEXT, EXT);
      Add(PreListSizes, eSize);
      Add(PreListDet, eDet);
      Add(PreListInv, eInv);
      Add(PreListGRP, eGRP);
      Add(PreListGRPsiz, Order(eGRP.GRP_int));
      Add(ListDisc, eDisc);
    else
      break;
    fi;
    i:=i+1;
  od;
  nbCone:=Length(PreListSizes);
  ePerm:=SortingPerm(ListDisc);
  #
  ListSizes:=Permuted(PreListSizes, ePerm);
  ListEXT:=Permuted(PreListEXT, ePerm);
  ListDet:=Permuted(PreListDet, ePerm);
  ListInv:=Permuted(PreListInv, ePerm);
  ListGRP:=Permuted(PreListGRP, ePerm);
  ListGRPsiz:=Permuted(PreListGRPsiz, ePerm);
  #
  AppendTo(output, "We found ", nbCone, " perfect cones\n");
  for iCone in [1..nbCone]
  do
    EXT:=ListEXT[iCone];
    nbIso:=Length(Filtered(EXT, x->x*LorMat*x=0));
    nbNonIso:=Length(Filtered(EXT, x->x*LorMat*x>0));
    GRP_int:=ListGRP[iCone].GRP_int;
    eDet:=ListDet[iCone];
    AppendTo(output,
             "iCone=", iCone, "/", nbCone,
             " nbIso=", nbIso, " nbNonIso=", nbNonIso,
             " index=", eDet, " |GRP|=", Order(GRP_int),
      "\n");
  od;
  #
end;





LORENTZ_InvariantOfLorentzianForm:=function(LorMat)
  return DeterminantMat(LorMat);
end;

#
# It is very heavy handed (compute all perfect forms ...)
# but it works
LORENTZ_TestIsomorphismLorentzianMatrices:=function(LorMat1, LorMat2)
  local eInv1, eInv2, TheOption, RecInput, eFamEXT2, eInvPerfect, KillingDelaunay, TheResult;
  eInv1:=LORENTZ_InvariantOfLorentzianForm(LorMat1);
  eInv2:=LORENTZ_InvariantOfLorentzianForm(LorMat2);
  if eInv1<>eInv2 then
    return false;
  fi;
  TheOption:="total";
  eFamEXT2:=LORENTZ_GetOnePerfect(LorMat2, TheOption).ListTotal;
  eInvPerfect:=LORENTZ_Invariant(LorMat2, eFamEXT2);
  Print("|eFamEXT2|=", Length(eFamEXT2), " eInvPerfect=", eInvPerfect, "\n");
  
  #
  KillingDelaunay:=function(eFamEXT1, eInv)
      local test, testInv;
      Print("|eFamEXT1|=", Length(eFamEXT1), " eInv=", eInv, "\n");
      if eInv=eInvPerfect then
          test:=LORENTZ_TestEquivalence_General(LorMat1, LorMat2, eFamEXT1, eFamEXT2);
          if test<>false then
              testInv:=Inverse(test);
              if testInv*LorMat1*TransposedMat(testInv)<>LorMat2 then
                  Error("The program still has some bugs");
              fi;
              return rec(TheEquiv:=testInv); # Need to encapsulate the matrix into a record, otherwise it matches the IsList
          fi;
      fi;
      return false;
  end;
  RecInput:=rec(TheOption:=TheOption, KillingDelaunay:=KillingDelaunay);
  TheResult:=LORENTZ_EnumeratePerfect_DelaunayScheme(LorMat1, RecInput);
  if IsList(TheResult) then # TheResult is then the list of perfect forms
      return false; # None of the perfect forms matched
  fi;
  return TheResult.TheEquiv; # Has to be a record
end;

LORENTZ_OrthogonalGroup_Kernel:=function(LorMat, ListFamily)
    local n, ListGenerators, ePerf, eGen, eAdj, SetGen;
    n:=Length(LorMat);
    ListGenerators:=[ - IdentityMat(n)]; # We need a transformation that flips the cone. The other below dont.
    for ePerf in ListFamily
    do
        for eGen in GeneratorsOfGroup(ePerf.eStab.GRPintMatr)
        do
            Add(ListGenerators, eGen);
        od;
        for eAdj in ePerf.ListAdj
        do
            Add(ListGenerators, eAdj.eBigMat);
        od;
    od;
    SetGen:=Set(ListGenerators);
    for eGen in SetGen
    do
        if eGen * LorMat * TransposedMat(eGen) <> LorMat then
            Error("The matrix does not preserve the quadratic form");
        fi;
        if IsIntegralMat(eGen)=false then
            Error("The matrix is not integral");
        fi;
    od;
    return Group(SetGen);
end;


LORENTZ_OrthogonalGroup:=function(LorMat)
    local RecInput, ListFamily;
    RecInput:=rec(TheOption:="total");
    ListFamily:=LORENTZ_EnumeratePerfect_DelaunayScheme(LorMat, RecInput);
    return LORENTZ_OrthogonalGroup_Kernel(LorMat, ListFamily);
end;


LORENTZ_CandidateIsotropicVectors_Kernel:=function(LorMat, ListFamily)
    local n, ListCand, ePerf, GRPperm, EXT, O, eO, eVectCand, eNorm;
    n:=Length(LorMat);
    ListCand:=[];
    for ePerf in ListFamily
    do
        GRPperm:=ePerf.eStab.PermutationStabilizer;
        EXT:=ePerf.EXT;
        O:=Orbits(GRPperm, [1..Length(EXT)], OnPoints);
        for eO in O
        do
            eVectCand:=EXT[eO[1]];
            eNorm:=eVectCand * LorMat * eVectCand;
            if eNorm=0 then
                Add(ListCand, eVectCand);
            fi;
        od;
    od;
    return ListCand;
end;


LORENTZ_CandidateIsotropicVectors:=function(LorMat)
    local RecInput, ListFamily;
    RecInput:=rec(TheOption:="total");
    ListFamily:=LORENTZ_EnumeratePerfect_DelaunayScheme(LorMat, RecInput);
    return LORENTZ_CandidateIsotropicVectors_Kernel(LorMat, ListFamily);
end;




LORENTZ_ListPairScal:=function(LorMat, ListIso)
  local nbVect, ListScal, ListNb, iVect, jVect, eScal, pos;
  nbVect:=Length(ListIso);
  ListScal:=[];
  ListNb:=[];
  for iVect in [1..nbVect]
  do
    for jVect in [iVect..nbVect]
    do
      eScal:=ListIso[iVect]*LorMat*ListIso[jVect];
      pos:=Position(ListScal, eScal);
      if pos=fail then
        Add(ListScal, eScal);
        Add(ListNb, 1);
      else
        ListNb[pos]:=ListNb[pos]+1;
      fi;
    od;
  od;
  return rec(ListScal:=ListScal, ListNb:=ListNb);
end;



GetAll:=function(d)
  local PreLorMat, LorMat, LVal, i, iPerf, nbPerf, ListPerf, HMat;
  HMat:=[
[1, 0, 0, 0],
[0, 1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  PreLorMat:=NullMat(4,4);
  LVal:=[-1, -d, -1, 1];
  for i in [1..4]
  do
    PreLorMat[i][i]:=LVal[i];
  od;
  LorMat:=HMat*PreLorMat*TransposedMat(HMat);
  ListPerf:=LORENTZ_EnumeratePerfect(LorMat).ListFamily;
  nbPerf:=Length(ListPerf);
  Print("nbPerf=", nbPerf, "\n");
  for iPerf in [1..nbPerf]
  do
    Print("iPerf=", iPerf, " |EXT|=", Length(ListPerf[iPerf].eFamEXT), " |G|=", Order(ListPerf[iPerf].eRecStab.GRP_int), "\n");
  od;
  return rec(ListPerf:=ListPerf, LorMat:=LorMat, d:=d, HMat:=HMat, PreLorMat:=PreLorMat);
end;


GetAll_Sch2:=function(d)
  local PreLorMat, LorMat, LVal, i, iPerf, nbPerf, ListPerf, HMat;
  if IsInt(d/4) then
    HMat:=[
[2, 0, 0, 0],
[0, 1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  else
    HMat:=[
[1, 1, 0, 0],
[1,-1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  fi;
  PreLorMat:=NullMat(4,4);
  LVal:=[-1, -d, -1, 1];
  for i in [1..4]
  do
    PreLorMat[i][i]:=LVal[i];
  od;
  LorMat:=HMat*PreLorMat*TransposedMat(HMat);
  ListPerf:=LORENTZ_EnumeratePerfect(LorMat).ListFamily;
  nbPerf:=Length(ListPerf);
  Print("nbPerf=", nbPerf, "\n");
  for iPerf in [1..nbPerf]
  do
    Print("iPerf=", iPerf, " |EXT|=", Length(ListPerf[iPerf].eFamEXT), " |G|=", Order(ListPerf[iPerf].eRecStab.GRP_int), "\n");
  od;
  return rec(ListPerf:=ListPerf, LorMat:=LorMat, d:=d, HMat:=HMat, PreLorMat:=PreLorMat);
end;


GetAll_Sch2_complex:=function(d)
  local PreLorMat, LorMat, LVal, i, iPerf, nbPerf, ListPerf, HMat, eRec, eRecComplex;
  if IsInt(d/4) then
    HMat:=[
[2, 0, 0, 0],
[0, 1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  else
    HMat:=[
[1, 1, 0, 0],
[1,-1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  fi;
  PreLorMat:=NullMat(4,4);
  LVal:=[-1, -d, -1, 1];
  for i in [1..4]
  do
    PreLorMat[i][i]:=LVal[i];
  od;
  LorMat:=HMat*PreLorMat*TransposedMat(HMat);
  eRec:=LORENTZ_EnumeratePerfect(LorMat);
  ListPerf:=eRec.ListFamily;
  eRecComplex:=eRec.GetFullComplex();
  nbPerf:=Length(ListPerf);
  Print("nbPerf=", nbPerf, "\n");
  for iPerf in [1..nbPerf]
  do
    Print("iPerf=", iPerf, " |EXT|=", Length(ListPerf[iPerf].eFamEXT), " |G|=", Order(ListPerf[iPerf].eRecStab.GRP_int), "\n");
  od;
  return rec(ListPerf:=ListPerf, LorMat:=LorMat, d:=d, HMat:=HMat, PreLorMat:=PreLorMat, eRecComplex:=eRecComplex);
end;





GetStrPlural:=function(nb)
  if nb=1 then
    return "";
  fi;
  return "s";
end;

G_WriteToFile:=function(FileName, TheTotalRec)
  local output, LL_EXT, L_EXT, TheDim, iRank, nbOrbit, iOrbit, eTriple, EXT, nbPerf, ListFaces, LL_ListFaces, ListPosRank, jRank, BndImg, ListOth, eEnt, L_ListFaces, d, len, pos, eRank, MatrixEdges, MatrixPoints, MatrixFaces, eSet, TheFilt, iFace, eElt, eFace, iPerf, i, eRec, PreListTrig, ListTrig, ListEList, eGen, eList, FindAdjacent, LL_Corresp, L_Corresp, eCorresp, LFaces, PrintComment, CStr, nbFacet, iFacet;
  LL_EXT:=[];
  d:=TheTotalRec.d;
  TheDim:=Length(TheTotalRec.eRecComplex.ListListCells);
  for iRank in [1..TheDim]
  do
    nbOrbit:=Length(TheTotalRec.eRecComplex.ListListCells[iRank]);
    L_EXT:=[];
    for iOrbit in [1..nbOrbit]
    do
      eTriple:=TheTotalRec.eRecComplex.ListListCells[iRank][iOrbit].ListTriple[1];
      EXT:=TheTotalRec.ListPerf[eTriple.iPerfect].eFamEXT{eTriple.eSet}*eTriple.eMat;
      Add(L_EXT, EXT);
    od;
    Add(LL_EXT, L_EXT);
  od;
  #
  LL_ListFaces:=[];
  for iRank in Reversed([1..TheDim-2])
  do
    nbOrbit:=Length(TheTotalRec.eRecComplex.ListListBoundary[iRank]);
    L_ListFaces:=[];
    for iOrbit in [1..nbOrbit]
    do
      BndImg:=TheTotalRec.eRecComplex.ListListBoundary[iRank][iOrbit];
      ListFaces:=[];
      ListPosRank:=[];
      for jRank in [iRank+1..TheDim-1]
      do
        Add(ListFaces, rec(iRank:=jRank, LFaces:=[]));
        Add(ListPosRank, jRank);
      od;
      len:=Length(BndImg.ListIFace);
      for i in [1..len]
      do
        iFace:=BndImg.ListIFace[i];
        eElt:=BndImg.ListElt[i];
        EXT:=LL_EXT[iRank+1][iFace]*eElt;
        Add(ListFaces[1].LFaces, Set(EXT));
        if iRank<TheDim-2 then
          ListOth:=LL_ListFaces[iRank+1][iFace];
          for eEnt in ListOth
          do
            eRank:=eEnt.iRank;
            pos:=Position(ListPosRank, eRank);
            for EXT in eEnt.LFaces
            do
              AddSet(ListFaces[pos].LFaces, Set(EXT*eElt));
            od;
          od;
        fi;
      od;
      Add(L_ListFaces, ListFaces);
    od;
    LL_ListFaces[iRank]:=L_ListFaces;
  od;
  FindAdjacent:=function(iPerf, eSet)
    local EXTfacet, eAdj, test, eMat, eMatB, EXTimg, pos, EXTfacetB, eRecAdj;
    EXTfacet:=TheTotalRec.ListPerf[iPerf].eFamEXT{eSet};
    for eAdj in TheTotalRec.ListPerf[iPerf].ListAdj
    do
      test:=RepresentativeAction(TheTotalRec.ListPerf[iPerf].eRecStab.GRP_int, eAdj.eOrb, eSet, OnSets);
      if test<>fail then
        eMat:=Image(TheTotalRec.ListPerf[iPerf].eRecStab.PhiPermMat, test);
        eMatB:=eAdj.eEquiv*eMat;
        EXTimg:=TheTotalRec.ListPerf[eAdj.iFamily].eFamEXT*eMatB;
        if IsSubset(Set(EXTimg), Set(EXTfacet))=false then
          Error("Wrong inclusion");
        fi;
        EXTfacetB:=Set(EXTfacet*Inverse(eMatB));
        pos:=Position(LL_ListFaces[1][eAdj.iFamily][1].LFaces, EXTfacetB);
        if pos=fail then
          Error("We did not find the matching facet");
        fi;
        eRecAdj:=rec(iPerf:=eAdj.iFamily, pos:=pos, eMat:=eMatB);
        return eRecAdj;
      fi;
    od;
    Error("Failed to find entry");
  end;
  nbPerf:=Length(LL_EXT[1]);
  LL_Corresp:=[];
  for iPerf in [1..nbPerf]
  do
    L_Corresp:=[];
    EXT:=TheTotalRec.ListPerf[iPerf].eFamEXT;
    LFaces:=LL_ListFaces[1][iPerf][1].LFaces;
    for iFace in [1..Length(LFaces)]
    do
      eFace:=LFaces[iFace];
      if IsSubset(Set(EXT), Set(eFace))=false then
        Error("Inclusion error");
      fi;
      eSet:=Set(List(eFace, x->Position(EXT, x)));
      if Position(eSet, fail)<>fail then
        Error("eSet is not correct");
      fi;
      eCorresp:=FindAdjacent(iPerf, eSet);
      Add(L_Corresp, eCorresp);
    od;
    Add(LL_Corresp, L_Corresp);
  od;
  Print("d=", d, " nbPerf=", nbPerf, "\n");
  #
  RemoveFileIfExist(FileName);
  output:=OutputTextFile(FileName, true);
  if d<=10 then
    PrintComment:=true;
  else
    PrintComment:=false;
  fi;
  CStr:=function(eStr)
    if PrintComment then
      return eStr;
    else
      return "";
    fi;
  end;
  AppendTo(output, "{[", d, ",", CStr(" /* value of d */"), "\n");
  AppendTo(output, nbPerf, ",", CStr(" /* number of perfect forms */"), "\n[");
  for iPerf in [1..nbPerf]
  do
    eRec:=TheTotalRec.ListPerf[iPerf];
    EXT:=LL_EXT[1][iPerf];
    MatrixEdges:=[];
    for eFace in LL_ListFaces[1][iPerf][2].LFaces
    do
      eSet:=Set(List(eFace, x->Position(EXT, x)-1));
      Add(MatrixEdges, eSet);
    od;
    MatrixFaces:=[];
    for eFace in LL_ListFaces[1][iPerf][1].LFaces
    do
      if IsSubset(Set(EXT), Set(eFace))=false then
        Error("Inclusion error");
      fi;
      eSet:=Set(List(eFace, x->Position(EXT, x)-1));
      TheFilt:=Filtered(MatrixEdges, x->IsSubset(eSet, x));
      eFace:=ExpressPairsAsCycle(TheFilt);
      Add(MatrixFaces, eFace);
    od;
    #
    MatrixPoints:=EXT*TheTotalRec.HMat;
    #
    PreListTrig:=GetTriangulationFromLRS(MatrixPoints);
    ListTrig:=List(PreListTrig, x->x.LV);
    #
    ListEList:=[];
    for eGen in GeneratorsOfGroup(eRec.eRecStab.GRPintMatr)
    do
      eList:=List(eRec.eFamEXT, x->Position(eRec.eFamEXT, x*eGen));
      Add(ListEList, eList);
    od;
    #
    #
    #
    AppendTo(output, "[", CStr(Concatenation(" /* form number ", String(iPerf), " */")), "\n");
    AppendTo(output, CStr("/* vertices of the cone */"), "\n");
    PariB_WriteMatrix(output, MatrixPoints);
    AppendTo(output, ",\n", CStr("/* list of faces */\n"));
    PariB_WriteMatrix(output, MatrixFaces);
    AppendTo(output, ",\n", CStr("/* list of edges */\n"));
    PariB_WriteMatrix(output, MatrixEdges);
    AppendTo(output, ",\n", CStr("/* one triangulation of the cone */\n"));
    PariB_WriteMatrix(output, ListTrig);
    AppendTo(output, ",\n", CStr("/* list of generators of symmetry group*/\n"));
    PariB_WriteMatrix(output, ListEList);
    AppendTo(output, ",\n", CStr("/* size of the symmetry group */\n"));
    AppendTo(output, Order(eRec.eRecStab.GRP_int));
    AppendTo(output, ",\n", CStr("/* matching facets */\n"));
    AppendTo(output, CStr("/* iDomain, iFacet, Matrix equivalence */\n"));
    nbFacet:=Length(LL_Corresp[iPerf]);
    for iFacet in [1..nbFacet]
    do
      eCorresp:=LL_Corresp[iPerf][iFacet];
      AppendTo(output, "[", eCorresp.iPerf, ",", eCorresp.pos, ",");
      PariB_WriteMatrix(output, eCorresp.eMat);
      AppendTo(output, "]");
      if iFacet < nbFacet then
        AppendTo(output, ",\n");
      fi;
    od;
    AppendTo(output, "]");
    if iPerf < nbPerf then
      AppendTo(output, ",\n");
    fi;
  od;
  AppendTo(output, "]];}");
  CloseStream(output);
end;

PariExportResultSpecific:=function(d)
  local FileSave, RecPerf, nbPerf, AllInfoFile, output, iPerf, eRec, eStr, eSize, HMat, eMat, ListEList, PreListTrig, ListTrig, eGen, eList;
  FileSave:=Concatenation("DATAgangl/Perf_Sch2_", String(d));
  if IsExistingFilePlusTouch(FileSave)=false then
    Error("Cannot print results when we do not have them\n");
  fi;
  RecPerf:=ReadAsFunction(FileSave)();
  nbPerf:=Length(RecPerf.ListPerf);
  #
  HMat:=RecPerf.HMat;
  Print("Printing results for d = ", d, "\n");
  AllInfoFile:=Concatenation("Perfect_Pari_", String(d));
  RemoveFileIfExist(AllInfoFile);
  output:=OutputTextFile(AllInfoFile, true);
  AppendTo(output, "{[", d, ",/* value of d */\n");
  AppendTo(output, nbPerf, ", /* number of perfect forms */\n[");
  for iPerf in [1..nbPerf]
  do
    eRec:=RecPerf.ListPerf[iPerf];
    eStr:=StructureDescription(eRec.eRecStab.GRP_int);
    eSize:=Length(eRec.eFamEXT);
    eMat:=eRec.eFamEXT*HMat;
    AppendTo(output, "[");
    PariB_WriteMatrix(output, eMat);
    AppendTo(output, ",\n");
    #
    PreListTrig:=GetTriangulationFromLRS(eMat);
    ListTrig:=List(PreListTrig, x->x.LV);
    PariB_WriteMatrix(output, ListTrig);
    AppendTo(output, ",\n");
    #
    ListEList:=[];
    for eGen in GeneratorsOfGroup(eRec.eRecStab.GRPintMatr)
    do
      eList:=List(eRec.eFamEXT, x->Position(eRec.eFamEXT, x*eGen));
      Add(ListEList, eList);
    od;
    PariB_WriteMatrix(output, ListEList);
    AppendTo(output, ",", Order(eRec.eRecStab.GRP_int), "]");
    #
    if iPerf < nbPerf then
      AppendTo(output, ",\n");
    fi;
  od;
  AppendTo(output, "]];}");
  CloseStream(output);
end;







DoGlobal_PARI_out:=function(UpperBound)
  local d, FileSave, FileOut, TheTotalRec;
  for d in [2..UpperBound]
  do
    FileSave:=Concatenation("DATAgangl/Perf_Sch2_compl_", String(d));
    FileOut:=Concatenation("PariCompl/compl_", String(d));
    if IsExistingFilePlusTouch(FileSave) then
      TheTotalRec:=ReadAsFunction(FileSave)();
      RemoveFileIfExist(FileOut);
      G_WriteToFile(FileOut, TheTotalRec);
    fi;
  od;
end;



PresentResultSpecific:=function(d)
  local FileSave, RecPerf, nbPerf, AllInfoFile, output, iPerf, eRec, eStr, eSize, HMat, eMat;
  FileSave:=Concatenation("DATAgangl/Perf_Sch2_", String(d));
  if IsExistingFilePlusTouch(FileSave)=false then
    Error("Cannot print results when we do not have them\n");
  fi;
  RecPerf:=ReadAsFunction(FileSave)();
  nbPerf:=Length(RecPerf.ListPerf);
  #
  HMat:=RecPerf.HMat;
  Print("Printing results for d = ", d, "\n");
  AllInfoFile:=Concatenation("AllInfo_Sch2_", String(d));
  RemoveFileIfExist(AllInfoFile);
  output:=OutputTextFile(AllInfoFile, true);
  AppendTo(output, "Case d = ", d, "\n");
  AppendTo(output, "We have ", nbPerf, " perfect forms\n");
  for iPerf in [1..nbPerf]
  do
    eRec:=RecPerf.ListPerf[iPerf];
    eStr:=StructureDescription(eRec.eRecStab.GRP_int);
    eSize:=Length(eRec.eFamEXT);
    AppendTo(output, "Perfect form ", iPerf, " with ", eSize, " vertices and group ", eStr, "\n");
    eMat:=eRec.eFamEXT*HMat;
    WriteMatrix(output, eMat);
  od;
  CloseStream(output);
end;

GetGlobalInformation:=function()
  local FileOut, output, d, TotalListSize, TotalListGRP, FileSave, RecPerf, strPlural, eRecComplex, eEnt, nbPerf, eRec, eSize, ListPair, nb, i, eStr, ePair;
  FileOut:="ListNumberPerfect_Sch2_compl";
  RemoveFileIfExist(FileOut);
  output:=OutputTextFile(FileOut, true);
  d:=2;
  TotalListSize:=[];
  TotalListGRP:=[];
  while(true)
  do
    FileSave:=Concatenation("DATAgangl/Perf_Sch2_compl_", String(d));
    Print("d=", d, "\n");
    if IsExistingFilePlusTouch(FileSave) then
      RecPerf:=ReadAsFunction(FileSave)();
      nbPerf:=Length(RecPerf.ListPerf);
      ListPair:=[];
      for eRec in RecPerf.ListPerf
      do
        eStr:=StructureDescription(eRec.eRecStab.GRP_int);
        eSize:=Length(eRec.eFamEXT);
        ePair:=rec(siz:=eSize, str:=eStr);
        Add(TotalListSize, eSize);
        Add(TotalListGRP, eStr);
        Add(ListPair, ePair);
      od;
      strPlural:=GetStrPlural(nbPerf);
      AppendTo(output, "For d=", d, " we have ", nbPerf, " perfect form", strPlural, "\n");
      for eEnt in Collected(ListPair)
      do
        nb:=eEnt[2];
        strPlural:=GetStrPlural(nb);
        AppendTo(output, "  ", eEnt[2], " perfect form", strPlural);
        AppendTo(output, " with ", eEnt[1].siz, " vectors");
        AppendTo(output, " and symmetry ", eEnt[1].str, "\n");
      od;
      AppendTo(output, "  Cells of the complex\n");
      eRecComplex:=RecPerf.eRecComplex;
      for i in [1..4]
      do
        nb:=Length(eRecComplex.ListListCells[i]);
        AppendTo(output, "  For dimension ", 5-i, " we have ", nb, " cell", GetStrPlural(nb), "\n");
      od;
      AppendTo(output, "  Cohomology groups\n");
      for i in [1..Length(eRecComplex.TheCoho)]
      do
        AppendTo(output, "  H^", i, "=");
        PrintHomologyGroup(output, eRecComplex.TheCoho[i]);
        AppendTo(output, "\n");
      od;
    else
      break;
    fi;
    d:=d+1;
  od;
  #
  AppendTo(output, "Occuring for all d <= ", d-1, "\n");
  AppendTo(output, "Possible number of shortest vectors\n");
  for eEnt in Collected(TotalListSize)
  do
    nb:=eEnt[2];
    strPlural:=GetStrPlural(nb);
    AppendTo(output, eEnt[1], " vectors (", nb, " time", strPlural, ")\n");
  od;
  #
  AppendTo(output, "Possible number of symmetry groups\n");
  for eEnt in Collected(TotalListGRP)
  do
    nb:=eEnt[2];
    AppendTo(output, "group of size ", eEnt[1], "\n");
  od;
  #
  CloseStream(output);
end;
