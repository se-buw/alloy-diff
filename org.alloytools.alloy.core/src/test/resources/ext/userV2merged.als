module UserV2

sig User {
  helper: one Helper
}

fact noSharedHelpers {
//  all disj u, v : User | no u.helper.^others & v.helper.^others
} 


sig Helper {
  others : some Helper
}
