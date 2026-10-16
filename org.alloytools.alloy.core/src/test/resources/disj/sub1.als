sig B {}
sig P {}
sig S in P { disj f, g: set B }
run { some s: S | some s.f & s.g } for 3
