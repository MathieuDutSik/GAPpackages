#  PlanGraphSpecial:=[];
#  for i in [1..nbVert]
#  do
#    Ladj:=[];
#    for k in [1..Length(PlanGraph[i])]
#    do
#      DE:=[i,k];
#      DErev:=Reverse(PlanGraph, DE);
#      Ladj[k]:=Position(VEF[2], Set([DE,DErev]))+nbVert;
#    od;
#    PlanGraphSpecial[i]:=Ladj;
#  od;
#  for i in [1..nbEdge]
#  do
#    DE1:=VEF[2][i][1];
#    DE2:=VEF[2][i][2];
#    for iFac in [1..nbFac]
#    do
#      if DE1 in VEF[3][iFac] then
#    	pos1:=iFac+nbVert+nbEdge;
#      fi;
#      if DE2 in VEF[3][iFac] then
#	    pos2:=iFac+nbVert+nbEdge;
#      fi;
#      Vert1:=DE1[1];
#      Vert2:=DE2[1];
#    od;
#    PlanGraphSpecial[i+nbVert]:=[pos1, Vert1, pos2, Vert2];
#  od;
#  for i in [1..nbFac]
#  do
#    Ladj:=[];
#    Face:=VEF[3][i];
#    for k in [1..Length(Face)]
#    do
#      DE:=Face[k];
#      DErev:=Reverse(PlanGraph, DE);
#      Ladj[k]:=Position(VEF[2], Set([DE,DErev]))+nbVert;
#    od;
#    PlanGraphSpecial[i+nbVert+nbEdge]:=Ladj;
#  od;
