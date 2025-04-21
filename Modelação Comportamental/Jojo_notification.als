/*

Finish the specification of this notification concept,
including its events, scenarios, and operational principles.

*/ 

sig Event {}

sig User {
	var subscriptions : set Event,
	var notifications : set Event
}

pred stutter {
	subscriptions' = subscriptions
	notifications' = notifications
}

pred read [u : User] {
	// Read all notifications
	some u.notifications
	u.notifications' = none
	all x : User - u | x.notifications' = x.notifications
	subscriptions' = subscriptions
}

pred subscribe [u : User, e : Event] {
	// Subscribe an event
	e not in u.subscriptions
	u.subscriptions' = u.subscriptions + e
	all x : User - u | x.subscriptions' = x.subscriptions
	notifications' = notifications
}

pred unsubscribe [u : User, e : Event] {
	// Unsubscribe from a event
	e in u.subscriptions
	u.subscriptions' = u.subscriptions - e
	u.notifications' = u.notifications - e
	all x : User - u | x.subscriptions' = x.subscriptions
	all x : User - u | x.notifications' = x.notifications
}

pred occur [e : Event] {
	// Occurrence of an event
	all u : User | e in u.subscriptions implies { u.notifications' = u.notifications + e }
	all u : User | e not in u.subscriptions implies { u.notifications' = u.notifications }
	subscriptions' = subscriptions
}

fact {
	no subscriptions
	no notifications
	always {
		stutter or
		(some u : User | read[u]) or
		(some u : User, e : Event | subscribe[u,e] or unsubscribe[u,e]) or
		(some e : Event | occur[e])
	}
}

// Validation

run Example {
	// Empty run to be used for simulation
}

run Scenario1 {
	// An event is subscribed, then occurs, and the respective notification is read 
	some u : User, e : Event {
		subscribe[u, e];
		occur[e];
		read[u]
	}
} expect 1

run Scenario2 {
	// An event is subscribed, unsubscribed, and then occurs
	some u : User, e : Event {
		subscribe[u, e];
		unsubscribe[u, e];
		occur[e]
	}
} expect 1

run Scenario3 {
	// An event is subscribed by two users and then occurs
	some u, x : User, e : Event {
		subscribe[u, e];
		subscribe[x, e];
		occur[e]
	}
} expect 1

run Scenario4 {
	// An user subscribes two events, then both occur, then unsubscribes one of them, and finally reads the notifications
	some u : User, e, v : Event {
		subscribe[u, e];
		subscribe[u, v];
		occur[e];
		occur[v];
		unsubscribe[u, e];
		read[u]
	}
} expect 1

run Scenario5 {
	// An user subscribes the same event twice in a row
	some u : User, e : Event {
		subscribe[u, e];
		subscribe[u, e]
	}
} expect 0

run Scenario6 {
	// Eventually an user reads nofications twice in a row
	some u : User | eventually {
		read[u];
		read[u]
	}
} expect 0

// Verification 

check OP1 {
	// Users can only have notifications of subscribed events
	all u : User, e : u.notifications | always {
		once subscribe[u, e]
	}
}

check OP2 {
	// Its not possible to read notifications before some event is subscribed
	all u : User | always {
		read[u] implies some u.subscriptions
	}
}

check OP3 {
	// Unsubscribe undos subscribe
	all u : User, e : u.subscriptions | always {
		unsubscribe[u, e] implies after no (e & u.subscriptions)
	}
}

check OP4 {
	// Notify is idempotent
	all e : Event | always {
		(occur[e]; occur[e]) implies after stutter
	}
}

check OP5 {
	// After reading the notifications it is only possible to read again after some notification on a subscribed event occurs
	all u : User | always { 
		read[u] implies eventually ((some e : Event | e in u.subscriptions and occur[e]) releases not read[u])
	}
}
