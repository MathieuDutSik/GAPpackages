# GLP_IntegerLinearProgramming
var x1;
var x2;
minimize obj: x1 + x2;
s.t. c1: x1 >= 0;
s.t. c2: x2 >= 0;
s.t. c3: - x1 - x2 >= 1;
solve;
display x1, x2;
end;
