open util/ordering[Time]
open util/ordering[Line]

sig Time {}

abstract sig LockType {}
one sig LockTypeRead, LockTypeWrite extends LockType {}

abstract sig Lock {
	lockType: LockType
}

sig TableLock extends Lock {}

sig LineLock extends Lock {
	lines: set Line //  A transaction can lock multiple lines at the same time	
}

sig Line {
	versions: Version lone -> Time
} 

fact {
	all v: Version | one line: Line, t: Time | line.versions.t = v
	Version = Line.versions.Time 
}

sig Version {
	transaction: Transaction,
	undo: lone Version,
	line: Line
} {
	// undo cannot be self
	undo != this

	// no undo circle
	one v' : Version | v' in this.*@undo && no v'.@undo

	// must undo the same line
	one undo => undo.@line = line
}

fact "if two versions belong to the same transaction and line, one must be the undo of another" {
	all v1, v2: Version | 
		v1.transaction = v2.transaction && v1.line = v2.line
	    => v1 in v2.*undo or v2 in v1.*undo
}

one sig Table {
	lines: set Line
} {
	lines = Line
}

abstract sig Operation {
	transaction: Transaction
}

sig ReadOp extends Operation {
	reads: some Line
}
	

sig WriteOp extends Operation {
	writes: some Line
}

sig LockOp extends Operation {}

sig CommitOp extends Operation {}

sig BeginOp extends Operation {}

sig RollbackOp extends Operation {}

sig insertOp extends Operation {
	line: Line
}

sig deleteOp extends Operation {
	line: set Line
}

sig Transaction {
	lock : Lock lone -> Time,
	operations: Operation lone -> Time
} {
	// no trivial transaction
	#operations >= 2

	// first opeartion must be begin
	first[operations] in BeginOp

	// Last operation must be commit or rollback
	last[operations] in CommitOp + RollbackOp

	// Other operations cannot be begin, commit or rollback
	all t: Time | t not in first + last => operations.t not in CommitOp + RollbackOp
}

fun snapshotRead(line: Line): set Version {
	Version
}

pred commit [t, t': Time, transaction: Transaction, commitOp: CommitOp] {
	transaction.opeartion.t' = transaction.opeartion.t + commitOp -> t'
}

pred read [t, t': Time, transaction: Transaction, line: Line] {
	canReadLine[t, transaction, line]
}

pred write [t, t': Time, transaction: Transaction, line: Line] {
	canWriteLine[t, transaction, line]
}



pred dirtyRead [t1, t2: Transaction] {
	
}

pred unrepeatableRead [t1, t2: Transaction] {

}

pred phantomRead [t1, t2: Transaction] {

}



// no locks

pred noWriteLockOnLines [t: Time, lines: set Line] {
	no lock in Transaction.lock.t | some line in lines | line in lock.lines and lock.lockType = LockTypeWrite
}

pred noReadLockOnLines [t: Time, lines: set Line] {
	no line in Line | line in Transaction.lock.lines 
}

pred noWriteLockOnTable [t: Time] {
	no lock in Transaction.lock.t | some line in lines | line in lock.lines and lock.lockType = LockTypeWrite
}

pred noReadLockOnTable [t: Time] {
	no line in Line | line in Transaction.lock.lines 
}

pred noTableLock [t: time] {
	noReadLockOnTable[t] 
	noWriteLockOnTable[t]
}

pred noLockOnLines [t: Time, lines: set Line] {
	noReadLockOnLines[t, lines]
	noWriteLockOnLines[t, lines]
}

// can read and write

pred canReadLines [t: Time, transaction: Transaction, lines: set Line] {
	noTableLock[t] and noLockOnLines[t, lines] or 
	hasTableLock[t, transaction] or 
	hasLinesLock[t, transaction, line]
}

pred canWriteLine [t: Time, transaction: Transaction, lines: set Line] {
	noTableLock[t] and noLockOnLines[t, lines] or 
	hasTableWriteLock[t, transaction] or
	hasLinesWriteLock[t, transaction, lines]
}

// has locks

pred hasTableReadLock [t: Time, transaction: Transaction] {
	let l = transaction.lock.t | l in TableLock and isLockRead[t, transaction]
}

pred hasTableWriteLock [t: Time, transaction: Transaction] {
	let l = transaction.lock.t | l in TableLock and isLockWrite[t, transaction]
}

pred hasTableLock [t: Time, transaction: Transaction] {
	hasTableReadLock[t, transaction] or hasTableWriteLock[t, transaction]
}

pred hasLinesReadLock [t: Time, transaction: Transaction, set lines: Line] {
	//lines in transaction.lock.t.lines
}

pred hasLinesWriteLock [t: Time, transaction: Transaction, set lines: Line] {
	//lines in transaction.lock.t.lines
}

pred hasLinesLock [t: Time, transaction: Transaction, set lines: Line] {
	hasLinesReadLock[t, transaction, lines] or hasLinesWriteLock[t, transaction, lines]
}



pred isLockWrite[t: Time, transaction: Transaction] {
	transaction.lock.t.lockType = LockTypeWrite
}

pred isLockRead[t: Time, transaction: Transaction] {
	transaction.lock.t.lockType = LockTypeRead
}


// set locks
pred setWriteLockOnLines[t, t': Time, transaction: Transaction, lines: set Line] {
	noTableLock[t]
	noLockOnLines[t, lines]
	hasLineLock[t', transaction, lines]
	isLockWrite[t', transaction]
}

pred setReadLockOnLines[t, t': Time, transaction: Transaction, lines: set Line] {
	noTableLock[t]
	noLockOnLines[t, lines]
	hasLineLock[t', transaction, lines]
	isLockWrite[t', transaction]
}

pred setReadLockOnTable[t, t': Time, transaction: Transaction] {
	noWriteLockOnTable[t]
	noWriteLockOnLines[t, Line]
	hasTableReadLock[t', transaction]
}

pred setWriteLockOnTable[t, t': Time, transaction: Transaction] {
	noTableLock[t]
	noLockOnLines[t, Line]
	hasTableWriteLock[t', transaction]
}

// release locks

pred releaseLock[t, t': Time, transaction: Transaction] {
	hasTableLock[t, transaction] or hasLinesLock[t, transaction, Line]
	not hasTableLock[t', transaction] 
	not hasLinesLock[t', transaction, Line]
}

pred init[t: Time] {
		
}

run {} for 4 but exactly 1 Transaction, exactly 2 Line //but exactly 2 Line, exactly 1 Transaction

