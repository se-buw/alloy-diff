one sig Light {}
var sig On in Light {}

fact {
	no On
	always On' = Light - On
}

run {} for 1 but 2..6 steps
