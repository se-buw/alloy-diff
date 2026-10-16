sig Endpoint {}
abstract sig Request {
  to: set Endpoint
}
sig LoginRequest extends Request {
  from: one Endpoint
}
var sig Sent in Request {}
fact {
  no Sent
  always Sent in Sent'
}
run { eventually some Sent } for 3 but 5 steps
