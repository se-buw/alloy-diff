sig Node { edges: set Node }

fact {
	// RELAXED: Every node has at most one edge (can have zero)
	all n: Node | lone n.edges
}
run {} for 2 Node
