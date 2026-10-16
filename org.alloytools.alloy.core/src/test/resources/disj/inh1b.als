sig B {}
abstract sig P { f: set B }
sig C1, C2 extends P {}
run { some c1: C1, c2: C2 | some c1.f & c2.f } for 3
