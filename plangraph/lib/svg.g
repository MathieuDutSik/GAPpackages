GetSplitOperationPlanGraph:=function(PL)
  local GRPinfo, eSymb, NatureElement, PairStatus, ListFold, ListFold3, ListFold4, ListFold5, eSymb1, eSymb2, eSymb3, eFold, i, ListPairStatus, eFirst;
  GRPinfo:=GroupPlan(PL);
  eSymb:=GRPinfo.TotalGroup.SchoenfliesSymbol;
  NatureElement:=function(eEnt)
    local IsVert, IsEdge, IsFace, len, eDE1, eDE2;
    IsVert:=false;
    IsEdge:=false;
    IsFace:=false;
    if IsList(eEnt)=false then
      IsVert:=true;
    else
      len:=Length(eEnt);
      if len=2 then
        eDE1:=eEnt[1];
	eDE2:=eEnt[2];
	if ReverseDE(PL, eDE1)=eDE2 then
	  IsEdge:=true;
	fi;
      fi;
      if IsEdge=false then
        IsFace:=true;
      fi;
    fi;
    return rec(IsVert:=IsVert, IsEdge:=IsEdge, IsFace:=IsFace);
  end;
  PairStatus:=function(ePair)
    local eEnt1, eEnt2, eNat1, eNat2, eVert, eEdgeRed;
    eEnt1:=ePair[1];
    eEnt2:=ePair[2];
    eNat1:=NatureElement(eEnt1);
    eNat2:=NatureElement(eEnt2);
    if eNat1.IsFace=true or eNat2.IsFace=true then
      return rec(split:="nosplit");
    fi;
    if eNat1.IsVert=true or eNat2.IsVert=true then
      if eNat1.IsVert=true then
        eVert:=eEnt1;
      else
        eVert:=eEnt2;
      fi;
      return rec(split:="vertsplit", eVert:=eVert);
    fi;
    return rec(split:="edgesplit", eEdge:=eEnt1);
  end;
  if eSymb="Ih" or eSymb="I" then
    ListFold5:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=5);
    eFold:=ListFold5[1];
    return PairStatus(eFold.axis);
  fi;
  if eSymb="Oh" or eSymb="O" then
    ListFold4:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=4);
    eFold:=ListFold4[1];
    return PairStatus(eFold.axis);
  fi;
  if eSymb="Th" or eSymb="T" or eSymb="Td" then
    ListFold3:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=3);
    eFold:=ListFold3[1];
    return PairStatus(eFold.axis);
  fi;
  if eSymb="C1" or eSymb="Ci" or eSymb="Cs" then
    return rec(split:="nosplit");
  fi;
  for i in [2..100]
  do
    eSymb1:=Concatenation("C", String(i));
    eSymb2:=Concatenation("C", String(i), "h");
    eSymb3:=Concatenation("C", String(i), "v");
    if eSymb=eSymb1 or eSymb=eSymb2 or eSymb=eSymb3 then
      ListFold:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=i);
      eFold:=ListFold[1];
      return PairStatus(eFold.axis);
    fi;
  od;
  if eSymb="D2" or eSymb="D2d" or eSymb="D2h" then
    ListFold:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=2);
    ListPairStatus:=List(ListFold, x->PairStatus(x.axis));
    eFirst:=First(ListPairStatus, x->x=rec(split:="nosplit"));
    if eFirst<>fail then
      return eFirst;
    fi;
    eFirst:=First(ListPairStatus, x->x.split="vertsplit");
    if eFirst<>fail then
      return eFirst;
    fi;
    return ListPairStatus[1];
  fi;
  for i in [3..100]
  do
    eSymb1:=Concatenation("D", String(i));
    eSymb2:=Concatenation("D", String(i), "d");
    eSymb3:=Concatenation("D", String(i), "h");
    if eSymb=eSymb1 or eSymb=eSymb2 or eSymb=eSymb3 then
      ListFold:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=i);
      eFold:=ListFold[1];
      return PairStatus(eFold.axis);
    fi;
  od;
  for i in [2..100]
  do
    eSymb1:=Concatenation("S", String(2*i));
    if eSymb=eSymb1 then
      ListFold:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=i);
      eFold:=ListFold[1];
      return PairStatus(eFold.axis);
    fi;
  od;
  Error("Did not matched anything. Need to rethink");
end;






GetSplitOperationPlanGraphOriented:=function(PLori)
  local GRPinfo, eSymb, GetView, ListFold, ListFold3, ListFold4, ListFold5, eSymb1, eSymb2, eSymb3, eFold, i, ListView, eFirst, VEFori, CCori;
  GRPinfo:=GroupPlanOriented(PLori);
  eSymb:=GRPinfo.TotalGroup.SchoenfliesSymbol;
  GetView:=function(eFold)
    local ListType, ListListDE;
    ListType:=eFold.type;
    ListListDE:=eFold.axis;
    for i in [1..2]
    do
      if ListType[i]="face" then
        return rec(eNature:="face", ListDE:=ListListDE[i]);
      fi;
    od;
    for i in [1..2]
    do
      if ListType[i]="vert" then
        return rec(eNature:="vert", ListDE:=ListListDE[i]);
      fi;
    od;
    for i in [1..2]
    do
      if ListType[i]="edge" then
        return rec(eNature:="edge", ListDE:=ListListDE[i]);
      fi;
    od;
    Error("Should not reach here");
  end;
  if eSymb="Ih" or eSymb="I" then
    ListFold5:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=5);
    eFold:=ListFold5[1];
    return GetView(eFold);
  fi;
  if eSymb="Oh" or eSymb="O" then
    ListFold4:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=4);
    eFold:=ListFold4[1];
    return GetView(eFold);
  fi;
  if eSymb="Th" or eSymb="T" or eSymb="Td" then
    ListFold3:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=3);
    eFold:=ListFold3[1];
    return GetView(eFold);
  fi;
  if eSymb="C1" or eSymb="Ci" or eSymb="Cs" then
    CCori:=GRPinfo.CC;
    VEFori:=CCori.VEF;
    return rec(eNature:="face", ListDE:=VEFori.FaceSet[1]);
  fi;
  for i in [2..100]
  do
    eSymb1:=Concatenation("C", String(i));
    eSymb2:=Concatenation("C", String(i), "h");
    eSymb3:=Concatenation("C", String(i), "v");
    if eSymb=eSymb1 or eSymb=eSymb2 or eSymb=eSymb3 then
      ListFold:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=i);
      eFold:=ListFold[1];
      return GetView(eFold);
    fi;
  od;
  if eSymb="D2" or eSymb="D2d" or eSymb="D2h" then
    ListFold:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=2);
    ListView:=List(ListFold, GetView);
    eFirst:=First(ListView, x->x.eNature="face");
    if eFirst<>fail then
      return eFirst;
    fi;
    eFirst:=First(ListView, x->x.eNature="vert");
    if eFirst<>fail then
      return eFirst;
    fi;
    return ListView[1];
  fi;
  for i in [3..100]
  do
    eSymb1:=Concatenation("D", String(i));
    eSymb2:=Concatenation("D", String(i), "d");
    eSymb3:=Concatenation("D", String(i), "h");
    if eSymb=eSymb1 or eSymb=eSymb2 or eSymb=eSymb3 then
      ListFold:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=i);
      eFold:=ListFold[1];
      return GetView(eFold);
    fi;
  od;
  for i in [2..100]
  do
    eSymb1:=Concatenation("S", String(2*i));
    if eSymb=eSymb1 then
      ListFold:=Filtered(GRPinfo.TotalGroup.RotationAxis, x->x.folding=i);
      eFold:=ListFold[1];
      return GetView(eFold);
    fi;
  od;
  Error("Did not matched anything. Need to rethink");
end;

WritePlanGraphOrientedToCpp:=function(eFile, PLori)
  local output, nbP, i, j;
  nbP:=PLori.nbP;
  RemoveFileIfExist(eFile);
  output:=OutputTextFile(eFile, true);
  AppendTo(output, nbP, "\n");
  #
  for i in [1..nbP]
  do
    j:=OnPoints(i, PLori.invers);
    AppendTo(output, " ", j-1);
  od;
  AppendTo(output, "\n");
  #
  for i in [1..nbP]
  do
    j:=OnPoints(i, PLori.next);
    AppendTo(output, " ", j-1);
  od;
  AppendTo(output, "\n");
  #
  CloseStream(output);
end;

WriteExtViewPlanGraphOrientedToCPP:=function(eFile, eExtInfo)
  local output, len, i;
  RemoveFileIfExist(eFile);
  output:=OutputTextFile(eFile, true);
  AppendTo(output, eExtInfo.eNature, "\n");
  len:=Length(eExtInfo.ListDE);
  AppendTo(output, len, "\n");
  for i in [1..len]
  do
    AppendTo(output, " ", eExtInfo.ListDE[i]-1);
  od;
  AppendTo(output, "\n");
  CloseStream(output);
end;

WriteListDEoverline:=function(eFile, ListDEoverline)
  local output, len, i;
  RemoveFileIfExist(eFile);
  output:=OutputTextFile(eFile, true);
  len:=Length(ListDEoverline);
  AppendTo(output, len, "\n");
  for i in [1..len]
  do
    AppendTo(output, " ", ListDEoverline[i]);
  od;
  AppendTo(output, "\n");
  CloseStream(output);
end;

WriteOptionToPlottingCpp:=function(eFile, eRec)
  local output, NamelistReal, NamelistBool, NamelistListInt, NamelistString, fStr;
  NamelistReal:=function(x)
    return GetFractionAsReal(x);
  end;
  NamelistBool:=function(x)
    if x then
      return ".T.";
    fi;
    return ".F.";
  end;
  NamelistListInt:=function(x)
    local len, eStr, i;
    len:=Length(x);
    eStr:="";
    for i in [1..len]
    do
      if i>1 then
        eStr:=Concatenation(eStr, ",");
      fi;
      eStr:=Concatenation(eStr, String(x[i]));
    od;
    return eStr;
  end;
  NamelistString:=function(x)
    return Concatenation("\"", x, "\"");
  end;
  RemoveFileIfExist(eFile);
  output:=OutputTextFile(eFile, true);
  #
  # PLOT section block
  #
  AppendTo(output, "&PLOT\n");
  AppendTo(output, " PlaneFile = ", NamelistString(eRec.PlaneFile), ",\n");
  AppendTo(output, " OutFile = ", NamelistString(eRec.OutFile), ",\n");
  if eRec.Charac=2 then
    AppendTo(output, " ViewFile = ", NamelistString(eRec.ViewFile), ",\n");
  fi;
  AppendTo(output, " MAX_ITER_PrimalDual = ", eRec.MAX_ITER_PrimalDual, ",\n");
  AppendTo(output, " MAX_ITER_CaGe = ", eRec.MAX_ITER_CaGe, ",\n");
  AppendTo(output, " CaGeProcessPolicy = ", eRec.CaGeProcessPolicy, ",\n");
  AppendTo(output, " RoundMethod = ", eRec.RoundMethod, ",\n");
  AppendTo(output, " width = ", eRec.width, ",\n");
  AppendTo(output, " height = ", eRec.height, ",\n");
  AppendTo(output, " MethodInsert = ", eRec.MethodInsert, ",\n");
  AppendTo(output, " ListExportFormat = ");
  for fStr in eRec.ListExportFormat
  do
    AppendTo(output, " \"", fStr, "\", ");
  od;
  AppendTo(output, "\n");
  AppendTo(output, "/\n\n\n");
  #
  # EDGE section block
  #
  AppendTo(output, "&EDGE\n");
  AppendTo(output, " DoMethod1 = ", NamelistBool(eRec.DoMethod1), ",\n");
  AppendTo(output, " DoMethod2 = ", NamelistBool(eRec.DoMethod2), ",\n");
  AppendTo(output, " DoMethod3 = ", NamelistBool(eRec.DoMethod3), ",\n");
  AppendTo(output, " MultTangent = ", NamelistReal(eRec.MultTangent), ",\n");
  AppendTo(output, " NormalTraitSize = ", eRec.EDGE_NormalTraitSize, ",\n");
  WriteAll(output, Concatenation(" ListTraitIDE = ", NamelistListInt(eRec.EDGE_ListTraitIDE), ",\n"));
  WriteAll(output, Concatenation(" ListTraitGroup = ", NamelistListInt(eRec.EDGE_ListTraitGroup), ",\n"));
  WriteAll(output, Concatenation(" ListTraitSize = ", NamelistListInt(eRec.EDGE_ListTraitSize), ",\n"));
  AppendTo(output, " DefaultRGB = ", NamelistListInt(eRec.EDGE_DefaultRGB), ",\n");
  WriteAll(output, Concatenation(" SpecificRGB_iDE = ", NamelistListInt(eRec.EDGE_SpecificRGB_iDE), ",\n"));
  WriteAll(output, Concatenation(" SpecificRGB_Group = ", NamelistListInt(eRec.EDGE_SpecificRGB_Group), ",\n"));
  WriteAll(output, Concatenation(" SpecificRGB_R = ", NamelistListInt(eRec.EDGE_SpecificRGB_R), ",\n"));
  WriteAll(output, Concatenation(" SpecificRGB_G = ", NamelistListInt(eRec.EDGE_SpecificRGB_G), ",\n"));
  WriteAll(output, Concatenation(" SpecificRGB_B = ", NamelistListInt(eRec.EDGE_SpecificRGB_B), ",\n"));
  if eRec.Charac=2 then
    AppendTo(output, " DoExternalArrow = ", NamelistBool(eRec.DoExternalArrow), ",\n");
    AppendTo(output, " ScalExtensionArrow = ", NamelistReal(eRec.ScalExtensionArrow), ",\n");
    AppendTo(output, " LengthExtensionArrow = ", NamelistReal(eRec.LengthExtensionArrow), ",\n");
  fi;  
  AppendTo(output, "/\n\n\n");
  #
  # VERT section block
  #
  AppendTo(output, "&VERT\n");
  AppendTo(output, " NormalRadius = ", NamelistReal(eRec.VERT_NormalRadius), ",\n");
  WriteAll(output, Concatenation(" ListRadiusIDE = ", NamelistListInt(eRec.VERT_ListRadiusIDE), ",\n"));
  WriteAll(output, Concatenation(" ListRadiusGroup = ", NamelistListInt(eRec.VERT_ListRadiusGroup), ",\n"));
  WriteAll(output, Concatenation(" ListRadius = ", NamelistListInt(eRec.VERT_ListRadius), ",\n"));
  AppendTo(output, " DefaultRGB = ", NamelistListInt(eRec.VERT_DefaultRGB), ",\n");
  WriteAll(output, Concatenation(" SpecificRGB_iDE = ", NamelistListInt(eRec.VERT_SpecificRGB_iDE), ",\n"));
  WriteAll(output, Concatenation(" SpecificRGB_Group = ", NamelistListInt(eRec.VERT_SpecificRGB_Group), ",\n"));
  WriteAll(output, Concatenation(" SpecificRGB_R = ", NamelistListInt(eRec.VERT_SpecificRGB_R), ",\n"));
  WriteAll(output, Concatenation(" SpecificRGB_G = ", NamelistListInt(eRec.VERT_SpecificRGB_G), ",\n"));
  WriteAll(output, Concatenation(" SpecificRGB_B = ", NamelistListInt(eRec.VERT_SpecificRGB_B), ",\n"));
  AppendTo(output, "/\n\n\n");
  #
  # TORUS section block
  #
  if eRec.Charac=0 then
    AppendTo(output, "&TORUS\n");
    AppendTo(output, " minimal = ", NamelistReal(eRec.minimal), ",\n");
    AppendTo(output, " tol = ", NamelistReal(eRec.tol), ",\n");
    AppendTo(output, " AngDeg = ", NamelistReal(eRec.AngDeg), ",\n");
    AppendTo(output, " scal = ", NamelistReal(eRec.scal), ",\n");
    AppendTo(output, " shiftX = ", NamelistReal(eRec.shiftX), ",\n");
    AppendTo(output, " shiftY = ", NamelistReal(eRec.shiftY), ",\n");
    AppendTo(output, " FundamentalRGB = ", NamelistListInt(eRec.FundamentalRGB), ",\n");
    AppendTo(output, " FundamentalTraitSize = ", NamelistReal(eRec.FundamentalTraitSize), ",\n");
    AppendTo(output, " DrawFundamentalDomain = ", NamelistBool(eRec.DrawFundamentalDomain), ",\n");
    AppendTo(output, "/\n\n\n");
  fi;
  CloseStream(output);
end;
