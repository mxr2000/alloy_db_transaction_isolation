open util/ordering[Time]

sig Time {}

pred init[t: Time] {
    no Table.rows.t
}

sig Row {}

one sig Table {
	rows: Row -> Time
}

fact traces {
	init[first]
	all t: (Time - last) | let t' = t.next {
		(some row: Row | {
			row not in Table.rows.t
			Table.rows.t' = Table.rows.t + row
		}) or
			(some row: Row | {
			row in Table.rows.t
			Table.rows.t' = Table.rows.t - row
		})
	}
}

run {} for 4 but exactly 1 Table, exactly 4 Row
