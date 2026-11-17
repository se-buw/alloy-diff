sig A { f : set A}

fact {
	all a,b: A | a != b implies no a.f & b.f
}
