sig A {}
var lone sig S in A {}
fact {
  no S
  after no S
  after after some S
}
run { always eventually no S and always eventually some S } for 1 A, 2..3 steps
