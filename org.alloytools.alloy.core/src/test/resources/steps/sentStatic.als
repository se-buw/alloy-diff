sig Endpoint {}
abstract sig Request {
  to: set Endpoint
}
sig LoginRequest extends Request {
  from: one Endpoint
}
sig Sent in Request {}
fact {
  no Sent
}
run { some Request } for 3
