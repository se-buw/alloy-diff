sig Request {}
var sig Sent in Request {}
fact { 
	no Sent 
	and  always Sent in Sent' 
} 
run SomeSent { eventually some Sent } for 3 but 2..5 steps

check AlwaysSends { eventually some Sent} for 3 but 2..5 steps
