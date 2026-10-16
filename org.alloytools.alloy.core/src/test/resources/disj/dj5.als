sig B {}
sig A { disj f, g: set B }
run { some a: A | some a.f & a.g } for 3
