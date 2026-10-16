sig A {}
var sig S in A {}
fact {
  no S
  always S in S'
  always lone (S' - S)
}
run { eventually #S = 5 } for exactly 5 A, 4 steps
