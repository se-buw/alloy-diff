sig A {}
var sig S in A {}
fact {
  no S
  always S in S'
  always lone (S' - S)
}
run { eventually #S = 3 } for exactly 3 A, 3 steps
