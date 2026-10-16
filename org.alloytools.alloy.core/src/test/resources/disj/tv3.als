sig B {}
var sig A { f: disj set B }
run { eventually some disj a1, a2: A | some a1.f & a2.f } for 3
