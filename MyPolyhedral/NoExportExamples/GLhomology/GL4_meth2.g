n:=4;
TheRES:=GetEnumerationPerfectForm(n);

DoHomology:=true;

TheTessel2:=DomainSplitting(TheRES.TheTesselation, [1,2]);
Print("TheTessel2:\n");
PrintOrbitwiseTesselationInformation(TheTessel2);

ListFusion:=[[1, 1], [3,1], [2,1]];
Print("ListFusion=", ListFusion, "\n");



TheTessel3:=MergeFacetsOrbitwiseTesselation(TheTessel2, ListFusion);

TheTessel4:=DomainSplitting(TheTessel3, [2]);

WorkingTesselation:=TheTessel4;


#TheSplit2:=DomainSplitting(TheSplit1, [1,2]);
#TheSplit3:=DomainSplitting(TheSplit1, [1,2,3]);


if DoHomology then
  kLevel:=4;
  TheBound:=BoundaryOperatorsFromPolyhedralTesselation(WorkingTesselation, kLevel, TheRES.FuncDoRetraction);
  TheResolution:=GroupHomologyByCellDecomposition(TheBound);
  TheHomologies:=GettingHomologies(TheResolution);
fi;
