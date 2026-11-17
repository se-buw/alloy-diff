sig A {}
var sig P in A {}
var sig R in A {}
sig S in P + R {}
fact { always S in P }
run {} for 3 but 4 steps
