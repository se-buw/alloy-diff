sig B {}
sig A { disj f, g, h: set B }
run { some g & h } for 3
