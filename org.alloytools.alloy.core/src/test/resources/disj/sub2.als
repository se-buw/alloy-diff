sig B {}
sig P {}
sig S in P { f: disj set B }
run { some disj s1, s2: S | some s1.f & s2.f } for 3
