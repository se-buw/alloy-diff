sig B {}
sig A { var f, g: set B }
run { eventually some f & g } for 3
