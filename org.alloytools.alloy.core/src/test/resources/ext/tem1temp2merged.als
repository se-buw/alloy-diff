sig A {
  var more : set A
}

pred v1 {}

pred v2 {
	more = more'
}

run {v1 and not v2}
