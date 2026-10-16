sig B {}
sig A { var disj f, g: set B }
run { eventually some f & g } for 3
