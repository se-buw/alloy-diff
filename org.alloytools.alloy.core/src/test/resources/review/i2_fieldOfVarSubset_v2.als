sig B { g: set B }
var sig S in B {}
fact { always (g.B in S) }
run {} for 3 but 4 steps
