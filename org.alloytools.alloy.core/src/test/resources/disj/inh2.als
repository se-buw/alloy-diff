sig B {}
sig P { disj f, g: set B }
sig C extends P {}
run { some c: C | some c.f & c.g } for 3
