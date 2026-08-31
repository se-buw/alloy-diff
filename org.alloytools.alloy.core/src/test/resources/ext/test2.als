sig Node { edges: set Node }

fact {
	
	some n: Node | lone n.edges
}
run {} for 3 Node
