n:=4;

EXT:=[];
for eVect in BuildSet(n, [-1/2, 3/2])
do
  Add(EXT, Concatenation([1], eVect));
od;

#FAC:=DualDescription(EXT);
ListFAC:=DualDescription(EXT);
Print("|ListFAC|=", Length(ListFAC), "\n");
