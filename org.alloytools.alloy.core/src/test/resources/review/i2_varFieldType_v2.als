sig B {}
var sig S in B {}
sig A { f: set B }
fact { always (all a: A | a.f in S) }
run {} for 3 but 4 steps
