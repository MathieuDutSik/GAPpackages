eInvMat:=[
[0,0,0,1],
[0,0,1,0],
[0,-1,0,0],
[-1,0,0,0]];

TheChoice:=1;
if TheChoice=1 then
  # Sp4Z
  FuncTestBelong:=function(eMat)
    if eMat*eInvMat*TransposedMat(eMat)=eInvMat and IsIntegralMat(eMat)=true then
      return true;
    fi;
    return false;
  end;
elif TheChoice=2 then
  # GSp4Z
  FuncTestBelong:=function(eMat)
    if Position([eInvMat, -eInvMat], eMat*eInvMat*TransposedMat(eMat))<>fail and IsIntegralMat(eMat)=true then
      return true;
    fi;
    return false;
  end;
else
  Print("Please put what you have in mind\n");
  Print(NullMat(5));
fi;


eFace4:=IdentityMat(4);
eFace4stab:=SymplecticStabilizer(eFace4, FuncTestBelong);

eFace3_1:=Concatenation(IdentityMat(4), [[1,0,0,1]]);
eFace3_2:=Concatenation(IdentityMat(4), [[0,1,0,1], [1,0,1,0]]);
eFace3_3:=Concatenation(IdentityMat(4), [[0,0,1,1], [1,0,1,0], [-1,1,0,1]]);
eFace3_1stab:=SymplecticStabilizer(eFace3_1, FuncTestBelong);
eFace3_2stab:=SymplecticStabilizer(eFace3_2, FuncTestBelong);
eFace3_3stab:=SymplecticStabilizer(eFace3_3, FuncTestBelong);



eFace2_1:=Concatenation(IdentityMat(4), [[1,0,0,1],[0,1,1,0]]);
eFace2_2:=Concatenation(IdentityMat(4), [[0,0,1,1],[1,0,0,1],[1,0,1,0],[1,1,0,1]]);
eFace2_3:=Concatenation(IdentityMat(4), [[0,0,1,1],[0,1,0,1],[1,0,1,0],[1,1,0,1]]);
eFace2_1stab:=SymplecticStabilizer(eFace2_1, FuncTestBelong);
eFace2_2stab:=SymplecticStabilizer(eFace2_2, FuncTestBelong);
eFace2_3stab:=SymplecticStabilizer(eFace2_3, FuncTestBelong);

eFace1_1:=Concatenation(IdentityMat(4), 
[[0,0,1,1],[0,1,0,1],[1,0,0,1],[1,0,1,0],[1,1,0,1]]);
eFace1_2:=Concatenation(IdentityMat(4), 
[[0,0,1,1],[1,0,1,0],[-1,1,0,0],[0,1,1,1],[1,1,0,1]]);
eFace1_1stab:=SymplecticStabilizer(eFace1_1, FuncTestBelong);
eFace1_2stab:=SymplecticStabilizer(eFace1_2, FuncTestBelong);

eFace0_1:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[1,0,1,0],[1,0,0,-1],[0,1,0,1],[1,1,1,0],[1,0,1,-1]]);
eFace0_2:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[1,0,-1,0],[0,1,0,-1],[0,0,1,-1],[1,1,-1,0],[1,1,0,-1],[1,0,-1,1],[0,1,1,1]]);
eFace0_1stab:=SymplecticStabilizer(eFace0_1, FuncTestBelong);
eFace0_2stab:=SymplecticStabilizer(eFace0_2, FuncTestBelong);

eFaceDesargues:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[1,0,1,0],[0,0,1,1],[1,1,1,0],[1,0,1,1],[1,1,1,1]]);
eFaceDesarguesStab:=SymplecticStabilizer(eFaceDesargues, FuncTestBelong);
eFaceReye:=Concatenation(IdentityMat(4), 
[[1,1,0,0],[1,0,1,0],[0,1,0,1],[0,0,1,1],[1,1,1,1],[1,1,1,0],
 [0,1,1,1],[1,0,0,-1]]);
eFaceReyeStab:=SymplecticStabilizer(eFaceReye, FuncTestBelong);
