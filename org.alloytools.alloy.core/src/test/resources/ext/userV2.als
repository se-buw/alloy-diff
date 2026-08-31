module UserV2

open helperV1 as helper

sig User {
  helper: one Helper
}

fact noSharedHelpers {
//  all disj u, v : User | no u.helper.^others & v.helper.^others
} 
