# You need the plangraph package for this example ....

Read("BuildResolution.g");
n:=4;
TheRES:=GetEnumerationPerfectForm(n);
IsInSmallGroup:=function(eBigMat)
  local ePrevMat;
  ePrevMat:=RevTRS_SymmRep(n, eBigMat);
  return DeterminantMat(ePrevMat)=1;
end;
SplittingInfo:=rec(TheBigGroup:=TheRES.TheGroup, IsInSmallGroup:=IsInSmallGroup);

DoGroupHomology:=true;

Print("TheTessel1:\n");
TheTessel1:=TheRES.TheTesselation;
PrintOrbitwiseTesselationInformation(TheTessel1);
Print("\n\n");
#
Print("TheTesselSL1:\n");
TheTesselSL1:=MappingToSubgroupPolyhedralTesselation(TheTessel1,SplittingInfo);
PrintOrbitwiseTesselationInformation(TheTesselSL1);
Print("\n\n");
#
Print("TheTesselSL2:\n");
TheTesselSL2:=DomainSplitting(TheTesselSL1, [1,2]);
PrintOrbitwiseTesselationInformation(TheTesselSL2);
CheckTilingFaceToFace(TheTesselSL2);
Print("\n\n");
#
Print("TheTesselSL2bis:\n");
ListFusion:=[[1, 1], [3,1], [2,1]];
TheTesselSL2bis:=MergeFacetsOrbitwiseTesselation(TheTesselSL2, ListFusion);
PrintOrbitwiseTesselationInformation(TheTesselSL2bis);
CheckTilingFaceToFace(TheTesselSL2bis);
Print("\n\n");

GetResolutionHacked:=function(GRP, kLevel)
  local phi, TheResolA5, TheResolS4, TheResol288, TheResolA4, TheResolS3, TheInfoS3, TheInfoC2, TheResolC2, ResolC2_S3_S3, ResolC2_C2, TheResolS3_S3;
  phi:=IsomorphismGroups(GRP, AlternatingGroup(5));
  if phi<>fail then
    TheResolA5:=GetResolutionA5();
    return TheResolutionMoveToOtherGroup(TheResolA5, GRP, kLevel);
  fi;
  phi:=IsomorphismGroups(GRP, SymmetricGroup(4));
  if phi<>fail then
    TheResolS4:=GetResolutionS4();
    return TheResolutionMoveToOtherGroup(TheResolS4, GRP, kLevel);
  fi;
  phi:=IsomorphismGroups(GRP, AlternatingGroup(4));
  if phi<>fail then
    TheResolA4:=GetResolutionA4();
    return TheResolutionMoveToOtherGroup(TheResolA4, GRP, kLevel);
  fi;
  phi:=IsomorphismGroups(GRP, SymmetricGroup(3));
  if phi<>fail then
    TheInfoS3:=GetPeriodicForS3();
    TheResolS3:=ResolutionPeriodic(TheInfoS3);
    return TheResolutionMoveToOtherGroup(TheResolS3, GRP, kLevel);
  fi;
  phi:=IsomorphismGroups(GRP, SmallGroup(72,46));
  if phi<>fail then
    TheInfoS3:=GetPeriodicForS3();
    TheResolS3:=ResolutionPeriodic(TheInfoS3);
    TheInfoC2:=InformationResolutionCyclic(2);
    TheResolC2:=ResolutionPeriodic(TheInfoC2);
    ResolC2_S3_S3:=ResolutionsDirectProduct([TheResolC2, TheResolS3, TheResolS3]);
    return TheResolutionMoveToOtherGroup(ResolC2_S3_S3, GRP, kLevel);
  fi;
  phi:=IsomorphismGroups(GRP, SmallGroup(36,10));
  if phi<>fail then
    TheInfoS3:=GetPeriodicForS3();
    TheResolS3:=ResolutionPeriodic(TheInfoS3);
    TheResolS3_S3:=ResolutionsDirectProduct([TheResolS3, TheResolS3]);
    return TheResolutionMoveToOtherGroup(TheResolS3_S3, GRP, kLevel);
  fi;
  phi:=IsomorphismGroups(GRP, SmallGroup(4,2));
  if phi<>fail then
    TheInfoC2:=InformationResolutionCyclic(2);
    TheResolC2:=ResolutionPeriodic(TheInfoC2);
    ResolC2_C2:=ResolutionsDirectProduct([TheResolC2, TheResolC2]);
    return TheResolutionMoveToOtherGroup(ResolC2_C2, GRP, kLevel);
  fi;
  phi:=IsomorphismGroups(GRP, SmallGroup(288, 1026));
  if phi<>fail then
    TheResol288:=GetResolution288_1026();
    return TheResolutionMoveToOtherGroup(TheResol288, GRP, kLevel);
  fi;
  return ResolutionComingFromHAP(GRP, kLevel);
end;

if DoGroupHomology=true then
  #WorkingTesselation:=TheTesselSL1;
  #WorkingTesselation:=TheTesselSL2;
  WorkingTesselation:=TheTesselSL2bis;
  #WorkingTesselation:=TheTesselSL3;
  #WorkingTesselation:=TheTesselSL4;
  #WorkingTesselation:=TheTesselSL5;
  #
  kHomology:=5;
  kLevel:=kHomology+1;
  RecOption:=rec(DoBound:=true, DoSign:=true, DoElt:=true, 
                 DoRotationSubgroup:=true);
  eRecIAI:="unset";
  TheBoundDirect:=BoundaryOperatorsFromPolyhedralTesselation(WorkingTesselation, kLevel, TheRES.FuncDoRetraction, eRecIAI, RecOption);
  TheBoundDirect.GetResolution:=GetResolutionHacked;
  ListFuncResolution:=GroupHomologyByCellDecomposition(TheBoundDirect);
  ListFuncResolution.Initialization(kLevel);
  ListMatrices:=[];
  for i in [1..kLevel]
  do
    Add(ListMatrices, ListFuncResolution.GetDifferentiation(i));
  od;
  TheHomologies:=GettingHomologies(ListMatrices);
fi;


