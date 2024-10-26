


BigGroup:=MathieuGroup(12);
SmaGroup:=MathieuGroup(10);



LiftFunc:=GlobalLiftingFunctionality(SmaGroup, BigGroup);

for iter in [1..100]
do
    eSet:=Set([]);
    for i in [1..Random([1..6])]
    do
        eVal:=Random([1..12]);
        AddSet(eSet, eVal);
    od;
    List1:=Orbit(BigGroup, eSet, OnSets);
    ListRepr:=LiftFunc(eSet);
    List2:=[];
    for eRepr in ListRepr
    do
        Append(List2, Orbit(SmaGroup, eRepr, OnSets));
    od;
    if Set(List1)<>Set(List2) then
        Error("Found bug in the orbit splitting");
    fi;
    Print("iter=", iter, " |eSet|=", Length(eSet), " |List1|=", Length(List1), "\n");
od;
