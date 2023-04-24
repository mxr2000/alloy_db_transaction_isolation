open util/ordering[Time]
open util/ordering[Transaction]
open util/ordering[Row]

sig Time {}

abstract sig Table {
    rows: Row -> Time
}

one sig UndoTable extends Table { }

one sig DataTable extends Table {
    locks: Lock -> Time
}

sig Row {
    transaction: Transaction,
    rollPointer: lone Row
} {
    // a row cannot be in data table and undo table at the same time
    all t: Time | not (this in UndoTable.rows.t and this in DataTable.rows.t)

    // Every time, a row can only appear once in both tables
    all t: Time | lone row : Row | (row in Table.rows.t and row = this)

    // At least appear once
    some t: Time | this in Table.rows.t

    // roll pointer cannot be self
    rollPointer != this

    // No circle in roll chain
    this not in this.^@rollPointer
}

fact nullPointerMustBeInUndotable {
	no t: Time, row1, row2: Row | row1 -> row2 in rollPointer and (row1 in DataTable.rows.t and row2 not in UndoTable.rows.t)
}

fact {
	all row: Row, t: Time | row in UndoTable.rows.t => row.rollPointer in UndoTable.rows.t
}

fact {
	all row1, row2: Row | row1.transaction = row2.transaction => (row1 in row2.*rollPointer or row2 in row1.*rollPointer)
}

one sig Program {
    operations: Op one -> one Time
} 

sig Transaction {

} {
    // Each transaction must have exactly one begin operation
    one t: Time, op: BeginOp 
        | op.transaction = this and 
        op -> t in Program.operations and 
        (no t': Time | (lt[t', t] and Program.operations.t'.transaction = this))

    // Each transaction must have exactly one commit or rollback operation
    one t: Time, op: (CommitOp + RollbackOp)
        | op.transaction = this and 
        op -> t in Program.operations and 
        (no t': Time | (lt[t, t'] and Program.operations.t'.transaction = this))
    
    one op: BeginOp | op.transaction = this and op in Program.operations.Time
    one op: (CommitOp + RollbackOp) | op.transaction = this and op in Program.operations.Time
}

abstract sig LockType {}

sig ReadLock, ReadWriteLock extends LockType {}

abstract sig Lock {
    transaction: Transaction,
    type: LockType
}

sig TableLock extends Lock {}

sig RowLock extends Lock {
    row: Row
} 


abstract sig Op {
    transaction: Transaction,
	time: Time
} {
	Program.operations.time = this
}

sig UpdateOp extends Op {
    oldRow: Row,
    newRow: Row
} {
    oldRow != newRow
}

sig ReadOp extends Op {
    row: Row
}

sig SnapshotReadOp extends ReadOp {}

sig InsertOp extends Op {
    row: Row
}

sig DeleteOp extends Op {
    row: Row
}  

sig SetLockOp extends Op {
    lock: Lock
}

sig ReleaseLockOp extends Op {
    lock: Lock
}

sig BeginOp extends Op {}
sig CommitOp extends Op {}
sig RollbackOp extends Op {}

pred isRowInDataTable [t: Time, row: Row] {
    row in DataTable.rows.t
}

pred isRowInUndoTable [t: Time, row: Row] {
    row in UndoTable.rows.t
}

pred isTransactionRunning [t: Time, trans: Transaction] {

    // No time lt than this has a rollback or commit
    all t': Time | 
        lt[t', t] => 
            (no op: (CommitOp + RollbackOp) | (op in Program.operations.t' and op.transaction = trans))

    // One time larger than this has a begin 
    all t': Time | 
        (lt[t, t']) => 
            (no op: BeginOp | (op in Program.operations.t' and op.transaction = trans))
}

pred noLockChange [t, t': Time] {
    DataTable.locks.t = DataTable.locks.t'
}

pred noTableWriteLock [t: Time] {
    no lock: TableLock | lock in Table.locks.t and lock.type in ReadWriteLock
}

pred noTableReadLock [t: Time] {
    no lock: TableLock | lock in Table.locks.t and lock.type in ReadLock
}

pred noTableLock [t: Time] {
    noTableReadLock[t]
    noTableWriteLock[t]
}

pred noRowWriteLock [t: Time, row: Row] {
    no lock: RowLock | lock in Table.locks.t and row = lock.@row and lock.type = ReadWriteLock
}

pred noRowReadLock [t: Time, row: Row] {
    no lock: RowLock | lock in Table.locks.t and row = lock.@row and lock.type = ReadLock
}

pred noWriteLock [t: Time] {
    noTableWriteLock[t]
    no lock: RowLock | lock.type = ReadWriteLock
}

pred noReadLock [t: Time] {
    noTableReadLock[t]
    no lock: RowLock | lock.type = ReadLock
}

pred noLock [t: Time] {
    noWriteLock[t]
    noReadLock[t]
}

pred noRowLock [t: Time, row: Row] {
    noRowReadLock[t, row]
    noRowWriteLock[t, row]
}

pred noChangeInTable [t, t': Time, table: Table] {
    table.rows.t = table.rows.t'
}

pred noChangeInTables [t, t': Time] {
    noChangeInTable[t, t', DataTable]
    noChangeInTable[t, t', UndoTable]
}

pred undoWrite [t, t': Time, transaction: Transaction] {
    let eliminated = {
        row: Row | one op: UpdateOp | op.@transaction = transaction and op.newRow = row
    } | {
        let original = {
            row: Row | (row in eliminated.^rollPointer and (one parent: Row | parent in eliminated and parent.rollPointer = row))
        } | {
            DataTable.rows.t' = DataTable.rows.t - eliminated + original
            UndoTable.rows.t' = UndoTable.rows.t - eliminated - original
        }
    }
}

pred isRowASnapshotRow [t: Time, row: Row, transaction: Transaction] {
    // The trasanction of the row is this one 
    row.@transaction = transaction or 

    // The transaction of the row is older than all active transactions 
    (all transaction': Transaction | isTransactionRunning[t, transaction'] => lt[row.@transaction, transaction']) or 

    // The transaction of the row is in [min, max], only ok when the transaction of the row is not active
    (some min, max: Transaction | {
        isTransactionRunning[t, min] 
        isTransactionRunning[t, max]  
        lte[min, row.@transaction]  
        lte[row.@transaction, max]  
        no trans': Transaction | (lt[trans', min] and isTransactionRunning[t, trans'])
        no trans': Transaction | (lt[max, trans'] and isTransactionRunning[t, trans'])
        not isTransactionRunning[t, row.@transaction]
    }) 
}

pred snapshotRead [t, t': Time, op: SnapshotReadOp] {
	Program.operations.t = op
    let row = op.row {
        let transaction = op.transaction {

            isRowASnapshotRow[t, row, transaction]

            // Not to read older version
            no row': Row | (row' != row and isRowASnapshotRow[t, row', transaction] and row'.rollPointer = row)
        }
    }
	noChangeInTables[t, t']
    noLockChange[t, t']
}

pred beginTransaction [t, t': Time, op: BeginOp] {
    Program.operations.t = op
    noChangeInTables[t, t']
    noLockChange[t, t']
    no lock: Lock | lock in Table.locks.t and lock.transaction = op.transaction
}

fact newerTransactionIsGreaterThanOlderOnes {
    all disj op1, op2: BeginOp | let t1 = op1.(Program.operations), t2 = op2.(Program.operations) {
        ordering/lt[t1, t2] => lt[op1.transaction, op2.transaction] 
    }
}

pred commitTransaction [t, t': Time, op: CommitOp] {
    Program.operations.t = op
    noChangeInTables[t, t']
    noLockChange[t, t']
}

pred rollbackTransaction [t, t': Time, op: RollbackOp] {
	Program.operations.t = op
    let transaction = op.transaction {
        undoWrite[t, t', transaction]
        noLockChange[t, t']
    }
}

pred read [t, t': Time, op: ReadOp] {
    Program.operations.t = op
    let row = op.row {
        let transaction = op.transaction {
            isTransactionRunning[t, transaction]
            isRowInDataTable[t, row]
            noChangeInTables[t, t']
            noLockChange[t, t']
        }
    }
}

pred insert [t, t': Time, op: InsertOp] {
    Program.operations.t = op
    let row = op.row {
        DataTable.rows.t' = DataTable.rows.t + row 
        noChangeInTable[t, t', UndoTable]
        noLockChange[t, t']
    }
}

pred update [t, t': Time, op: UpdateOp] {
    Program.operations.t = op
    let oldRow = op.oldRow, newRow = op.newRow | {
    	let transaction = op.transaction | {
    		isTransactionRunning[t, transaction]

            not isRowInDataTable[t, newRow]
            not isRowInUndoTable[t, newRow]
            isRowInDataTable[t, oldRow]

   	 		newRow.rollPointer = oldRow
    		newRow.@transaction = transaction
            
            UndoTable.rows.t' = UndoTable.rows.t + oldRow
            DataTable.rows.t' = DataTable.rows.t - oldRow + newRow
    		
            all lock: RowLock | lock in DataTable.locks.t and oldRow in lock.row => 
                (one newLock: RowLock | newLock.row = newRow and DataTable.locks.t' = DataTable.locks.t + newLock)
		}
	}
}

pred delete [t, t': Time, op: DeleteOp] {
    Program.operations.t = op
    let row = op.row, transaction = op.transaction {
    	isTransactionRunning[t, transaction]
    	isRowInDataTable[t, row]
		noChangeInTable[t, t', UndoTable]
        DataTable.rows.t' = DataTable.rows.t - row
    	noLockChange[t, t']
	} 
} 

pred noConflictLock[t: Time, op: SetLockOp] {
    let lock = op.lock {
        (
            lock in RowLock and (
                (lock.type in ReadLock and noTableWriteLock[t] and noRowWriteLock[t, lock.row]) or
                (lock.type in ReadWriteLock and noTableLock[t] and noRowLock[t, lock.row]) 
            )   
        ) 
        or
        (
            lock in TableLock and (
                (lock.type in ReadLock and noWriteLock[t]) or
                (lock.type in ReadWriteLock and noLock[t]) 
            )   
        ) 
    }
}

pred setLock [t, t': Time, op: SetLockOp] {
    Program.operations.t = op
    let lock = op.lock {
    	let transaction = op.transaction {
            noConflictLock[t, op]
            op.@lock.row in DataTable.rows.t
    		lock.@transaction = transaction
    		DataTable.locks.t + lock = DataTable.locks.t'
    		noChangeInTables[t, t']
		}
	}
}

pred releaseLock [t, t': Time, op: ReleaseLockOp] {
    Program.operations.t = op
    let lock = op.lock {
        let transaction = op.transaction {
            lock in Table.locks.t
            lock.@transaction = transaction
            DataTable.locks.t' + lock = DataTable.locks.t
            noChangeInTables[t, t']
        }
    }
}

pred isTransactionGoingToCommit [transaction: Transaction] {
    some t: Time, op: CommitOp | Program.operations.t = op and op.@transaction = transaction
}

pred isTransactionGoingToRollback [transaction: Transaction] {
    some t: Time, op: RollbackOp | Program.operations.t = op and op.@transaction = transaction
}

pred isDirtyRead [readOp: ReadOp] {
    some writeTime: Time | let writeOp = Program.operations.writeTime {
        writeOp.transaction != readOp.transaction
        writeOp in UpdateOp + InsertOp
        lt[writeOp.time, readOp.time]
        readOp.row in writeOp.newRow + writeOp.(InsertOp <: row)
        isTransactionRunning[readOp.time, writeOp.transaction]
        isTransactionGoingToRollback[writeOp.transaction]
    }
}

fun rowsBetween [t: Time, min, max: Row]: set Row {
    DataTable.rows.t & (prevs[max] + max - prevs[min])
}

pred isUnrepeatableRead [ro1, ro2: ReadOp] {
    let t1 = ro1.time, t2 = ro2.time | {
        lt[t1, t2]
        ro1.transaction = ro2.transaction and 
        ro1.row in ro2.row.^rollPointer
    } 
}

pred thereIsDirtyRead {
    some op: ReadOp | isDirtyRead[op]
}

pred thereIsUnrepeatableRead {
    some disj op1, op2: ReadOp | isUnrepeatableRead[op1, op2]
}



pred transactionHasNOperations [transaction: Transaction, cnt: Int] {
    #({op: Op | op.@transaction = transaction}) = cnt
}



pred thereIsPhantomRead {
    some disj rt1, rt2, rt3, rt4: Time | (lt[rt1, rt2] and lt[rt2, rt3] and lt[rt3, rt4]) =>
        some ro1, ro2, ro3, ro4: ReadOp | 
            ro1 in Program.operations.rt1 and 
            ro2 in Program.operations.rt2 and 
            ro3 in Program.operations.rt3 and 
            ro4 in Program.operations.rt4 and

            ro1.row = ro3.row and 
            ro2.row = ro4.row and 

            lt[ro1.row, ro2.row] and 

            #(ro1 + ro2 + ro3 + ro4).transaction = 1 and 

            rowsBetween[rt2, ro1.row, ro2.row] != rowsBetween[rt4, ro3.row, ro4.row]
}

pred alwaysSetLineLockBeforeUpdate {
    all op: UpdateOp |
        one t: Time | Program.operations.t = op =>
            some lock: RowLock | {
                op.oldRow in lock.row 
                lock in DataTable.locks.t 
                lock.transaction = op.transaction 
                lock.type in ReadWriteLock
            }
}

pred alwaysSetTableLockBeforeUpdate {
    all op: UpdateOp |
        one t: Time | Program.operations.t = op =>
            some lock: TableLock | {
                lock in DataTable.locks.t
                lock.transaction = op.transaction
                lock.type in ReadWriteLock
            }
}

pred alwaysSetLineLockBeforeRead {
    all op: ReadOp | let t = op.time {
        some lock: RowLock | {
                op.row in lock.row 
                lock in DataTable.locks.t 
                lock.transaction = op.transaction 
        }
    }
}

pred alwaysSetTableLockBeforeRead {
    all op: ReadOp | let t = op.time {
        some lock: TableLock | {
            lock in DataTable.locks.t
            lock.transaction = op.transaction
        }
    }
}

pred alwaysSetTableLockBeforeInsert {
    all op: InsertOp |
        one t: Time | Program.operations.t = op => 
            some lock: TableLock | {
                lock in DataTable.locks.t
                lock.transaction = op.transaction
                lock.type in ReadWriteLock
            }
}

pred alwaysSnapshotRead {
    ReadOp = SnapshotReadOp
}

pred neverSnapshotRead {
    no SnapshotReadOp
}

fact releaseAllLocksBeforeCommitOrRollback {
    all transaction: Transaction, t: Time, op: (CommitOp + RollbackOp) | op in Program.operations.t => transaction not in Table.locks.t.@transaction
}

pred init[t: Time] {
    Program.operations.t in BeginOp
	no Table.rows.t
}

pred traces {
    init[first]

    all t: (Time - last) | let t' = t.next {
        (some op: BeginOp                   | beginTransaction[t, t', op])      or 
        (some op: CommitOp                  | commitTransaction[t, t', op])     or 
        (some op: RollbackOp                | rollbackTransaction[t, t', op])   or 
        (some op: (ReadOp - SnapshotReadOp) | read[t, t', op])                  or
        (some op: UpdateOp                  | update[t, t', op])                or 
        (some op: InsertOp                  | insert[t, t', op])                or 
        (some op: DeleteOp                  | delete[t, t', op])                or 
        (some op: SetLockOp                 | setLock[t, t', op])               or 
        (some op: ReleaseLockOp             | releaseLock[t, t', op])           or
        (some op: SnapshotReadOp            | snapshotRead[t, t', op]) 
    } 
}

pred testTransaction1[transaction: Transaction] {
    transactionHasNOperations[transaction, 3]
    one readOp: ReadOp | indexedOp[transaction, readOp, 1]
}

pred indexedOp [transaction: Transaction, op: Op, index: Int] {
    one t: Time | op in Program.operations.t and op.@transaction = transaction
    #({opBefore: Op | lt[opBefore.time, op.time] and opBefore.@transaction = transaction}) = index
}

pred test {
	traces
	some op: UpdateOp | op in Program.operations.Time
	//all t: Time | Program.operations.t not in (SnapshotReadOp)
    //all row1, row2: Row | row1 != row2 => (row1 -> row2 in rollPointer or row2 -> row1 in rollPointer)
	//testCase1
}

pred initTransaction[transaction: Transaction] {
    all transaction': Transaction, t: Time | 
        transaction' != transaction => {
            isTransactionRunning[t, transaction] => not isTransactionRunning[t, transaction']
            lt[transaction, transaction']
        }
}

pred isInitTransaction[transaction: Transaction] {
	initTransaction[transaction]
	transactionHasNOperations[transaction, 3]
	one op: InsertOp | indexedOp[transaction, op, 1]
	//one op: InsertOp | indexedOp[transaction, op, 2]
//	one op: InsertOp | indexedOp[transaction, op, 3]
	one op: CommitOp | indexedOp[transaction, op, 2]
}

pred testCaseAllReadTransactions {
	traces
    some disj t0, t1, t2: Transaction | {
        isInitTransaction[t0]
        
        transactionHasNOperations[t1, 4]
        one op: ReadOp | indexedOp[t1, op, 1]
        one op: ReadOp | indexedOp[t1, op, 2]

        transactionHasNOperations[t2, 4]
        one op: ReadOp | indexedOp[t2, op, 1]
        one op: ReadOp | indexedOp[t2, op, 2]
    } 
}

pred testCaseReadUpdateTransactions {
	traces
    some disj t0, t1, t2: Transaction | {
        isInitTransaction[t0]

        transactionHasNOperations[t1, 4]
        one op: ReadOp | indexedOp[t1, op, 1]
        one op: ReadOp | indexedOp[t1, op, 2]

        transactionHasNOperations[t2, 4]
        one op: UpdateOp | indexedOp[t2, op, 1]
        one op: ReadOp | indexedOp[t2, op, 2]
    } 
}

// test case 1
check { (testCaseAllReadTransactions and neverSnapshotRead) => not thereIsDirtyRead } for 11 but exactly 1 Program, exactly 1 Row,
exactly 3 Transaction, exactly 2 Table, exactly 1 Lock

// test case 2
check { (testCaseReadUpdateTransactions and neverSnapshotRead) => not thereIsDirtyRead } for 11 but exactly 1 Program, exactly 2 Row,
exactly 3 Transaction, exactly 2 Table, exactly 1 Lock // have counterexample

// test case 3
check { (testCaseAllReadTransactions and neverSnapshotRead) => not thereIsUnrepeatableRead } 
for 11 but exactly 1 Program, exactly 1 Row,
exactly 3 Transaction, exactly 2 Table, exactly 1 Lock

// test case 4
check { (testCaseReadUpdateTransactions and neverSnapshotRead) => not thereIsUnrepeatableRead } for 11 but exactly 1 Program, exactly 2 Row,
exactly 3 Transaction, exactly 2 Table, exactly 1 Lock // have counterexample

// test case 5
check {
	(testCaseReadUpdateTransactions and (alwaysSetLineLockBeforeRead or alwaysSetTableLockBeforeRead)) => 
        (not thereIsDirtyRead and not thereIsUnrepeatableRead)
} for 13 but exactly 1 Program, exactly 3 Row,
exactly 3 Transaction, exactly 2 Table, exactly 1 Lock

// test case 6
check {
    (testCaseReadUpdateTransactions and alwaysSnapshotRead) => (not thereIsDirtyRead and not thereIsUnrepeatableRead)
} for 13 but exactly 1 Program, exactly 3 Row,
exactly 3 Transaction, exactly 2 Table, exactly 1 Lock

run testCaseReadUpdateTransactions for 12 but exactly 1 Program, exactly 3 Row,
exactly 3 Transaction, exactly 2 Table, exactly 1 Lock

