sig Request {}
var sig Sent in Request {}
fact { 
	no Sent 
	-- either no new request is sent, or exactly one new request is sent.
	always (Sent = Sent' or one (Sent' - Sent))
	-- request that has been sent can never be removed
	always Sent in Sent'
}

run AllSent { eventually Sent = Request } for 3 but exactly 3 Request, 5 steps
run TooShort { eventually Sent = Request } for 3 but exactly 3 Request, 3 steps
