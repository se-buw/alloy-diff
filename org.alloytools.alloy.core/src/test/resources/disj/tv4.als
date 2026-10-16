sig B {}
sig A { disj f, g: set B }
var sig V in A {}
run { eventually some V } for 3
