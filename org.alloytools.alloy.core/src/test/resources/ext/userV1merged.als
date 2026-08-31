module UserV1

sig User {
  helper: one Helper
}

sig Helper {
  others : set Helper
}
