sig Node {next: one Node}
fact {all n: Node | Node in n.^next}

one sig Token {var at: one Node}
fact{always Token.at' = Token.at.next}

run Ring3 {} for exactly 5 Node, 6 steps
run Ring3Short {} for exactly 3 Node, 2 steps
