SolveOneCase:=function(GramMat, eName)
  local LFC, ListBelt, eRecFree, LFC2, KillingFunctionLtype, KeepInKillBank, eRecMaximalMinimal, nbVect, eFileMaximalMinimal, eFileFree, IsSaving, ThePrefix, ThePrefixPartial, eFileSCV, ListRelevantVector, eRecRelevant1, eRecRelevant2, eFileRelevant, PreRecFree, eRecTransvers;
  ThePrefix:=Concatenation(eName, "_freesearch/");
  CreateDirectory(ThePrefix);
  eFileFree:=Concatenation(ThePrefix, "eRecFree");
  eFileMaximalMinimal:=Concatenation(ThePrefix, "eRecMaximalMinimal");
  eFileSCV:=Concatenation(ThePrefix, "eRecSCV");
  eFileRelevant:=Concatenation(ThePrefix, "ListRelevantVector");
  if IsExistingFilePlusTouch(eFileFree)=true and IsExistingFilePlusTouch(eFileMaximalMinimal)=true then
    return;
  fi;
  LFC:=DelaunayComputationStandardFunctions(GramMat);
  eRecRelevant1:=LFC.GetOrbitDefiningVoronoiFacetInequalities();
  eRecRelevant2:=eRecRelevant1.GetCompleteListFacetDefining();
  ListRelevantVector:=eRecRelevant2.ListVectors;
  SaveDataToFilePlusTouch(eFileRelevant, ListRelevantVector);
  #
  ListBelt:=LFC.GetFreeVectors();
  PreRecFree:=ListBelt.FuncGetAllFreeVectors();
  eRecFree:=rec(GramMat:=PreRecFree.GramMat,
                ListMatrGens:=PreRecFree.ListMatrGens,
                ListPermGens:=PreRecFree.ListPermGens,
                ListFreeVect:=PreRecFree.ListFreeVect,
                PermGRPfree:=PreRecFree.PermGRPfree);
  SaveDataToFilePlusTouch(eFileFree, eRecFree);
  #
  LFC2:=ApplicationPOLYDEC_FreeStructure(PreRecFree);
  GetCorrectIncorrectSets:=function(eSet)
    local eCase, TheGramMat, LFC, eRec, eDiff, ListCorrect, ListIncorrect, idx, eVectOrig, eVectOrigB, eVectOrigC;
    eCase:=LFC2.GetECase(eSet);
    TheGramMat:=POLYDEC_GetSymmetricGramMat(eCase);
    LFC:=DelaunayComputationStandardFunctions(TheGramMat);
    eRec:=LFC.GetFreeVectors();
    eDiff:=Difference([1..Length(eRecFree.ListFreeVect)], eSet);
    ListCorrect:=[];
    ListIncorrect:=[];
    for idx in eDiff
    do
      eVectOrig:=eRecFree.ListFreeVect[idx];
      eVectOrigB:=eVectOrig*eRecFree.GramMat;
      eVectOrigC:=eVectOrigB*Inverse(TheGramMat);
      if eRec.TestVectorFreeness(eVectOrigC) then
        if eRec.TestVectorScalCondition(eVectOrigC) then
          Print("We found a parallelotope not a Voronoi, allelujah!\n");
          Print(NullMat(5));
        fi;
        Add(ListCorrect, idx);
      else
        Add(ListIncorrect, idx);
      fi;
    od;
    return rec(ListCorrect:=ListCorrect, ListIncorrect:=ListIncorrect);
  end;
  nbVect:=Length(eRecFree.ListFreeVect);
  IsSaving:=true;
  ThePrefixPartial:=Concatenation(eName, "_freesearch/PartialEnum/");
  CreateDirectory(ThePrefixPartial);
  eRecMaximalMinimal:=MyEnumerationMaximalMinimalSpanning(IsSaving, ThePrefixPartial, nbVect, eRecFree.PermGRPfree, GetCorrectIncorrectSets);
  SaveDataToFilePlusTouch(eFileMaximalMinimal, eRecMaximalMinimal);
  #
  eRecTransvers:=LFC.GetStronglyTransversal();
  SaveDataToFilePlusTouch(eFileSCV, eRecTransvers.ReturnListListOrbit);
end;


ListCases:=[];
DualPair:=function(eName)
  local TheList, TheGramMat, test, DualGramMat, DualName;
  Print("Inserting lattice ", eName, "\n");
  TheList:=[];
  TheGramMat:=ClassicalSporadicLattices(eName);
  Add(TheList, rec(eName:=eName, GramMat:=TheGramMat));
  test:=IsSelfDualLattice(TheGramMat);
  if test=false then
    DualGramMat:=RemoveFractionMatrix(Inverse(TheGramMat));
    DualName:=Concatenation("Dual_", eName);
    Add(TheList, rec(eName:=DualName, GramMat:=DualGramMat));
  fi;
  Append(ListCases, TheList);
end;

GetDual:=function(eName)
  local TheGramMat, DualGramMat, DualName, TheList;
  TheGramMat:=ClassicalSporadicLattices(eName);
  DualGramMat:=RemoveFractionMatrix(Inverse(TheGramMat));
  DualName:=Concatenation("Dual_", eName);
  TheList:=[rec(eName:=DualName, GramMat:=DualGramMat)];
  Append(ListCases);
end;

GetDirect:=function(eName)
  local TheList, TheGramMat, test, DualGramMat, DualName;
  Print("Inserting lattice ", eName, "\n");
  TheList:=[];
  TheGramMat:=ClassicalSporadicLattices(eName);
  Add(ListCases, rec(eName:=eName, GramMat:=TheGramMat));
end;
#DualPair("E6");
#DualPair("E7");
DualPair("ER7");
#DualPair("Kappa7");
#DualPair("E8");
#DualPair("Kappa8");
#DualPair("Lambda9");
#DualPair("Kappa9");
#DualPair("Lambda10");
#DualPair("O10");
#DualPair("K12");
#DualPair("Kappa10");
#DualPair("Kappa11");
#DualPair("Lambda11max");
#DualPair("Lambda11min");
#DualPair("Lambda12max");
#DualPair("Lambda12mid");
#DualPair("Lambda12min");
#DualPair("Lambda13max");
#DualPair("Lambda13mid");
#DualPair("Lambda13min");

for eCase in ListCases
do
  SolveOneCase(eCase.GramMat, eCase.eName);
od;
