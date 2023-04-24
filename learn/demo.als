sig FSObject {
	parent: lone Dir
}

sig Dir extends FSObject {
	contents: set FSObject
}

sig File extends FSObject {}

fact {
	all d: Dir, o: d.contents | o.parent = d
}

fact { 
	File + Dir = FSObject 
}

// There exists a root
one sig Root extends Dir { } { no parent }

// File system is connected
fact { FSObject in Root.*contents }

// The contents path is acyclic
assert acyclic { no d: Dir | d in d.^contents }

// Now check it for a scope of 5
check acyclic for 5

// File system has one root
assert oneRoot { one d: Dir | no d.parent }

// Now check it for a scope of 5
check oneRoot for 5

// Every fs object is in at most one directory
assert oneLocation { all o: FSObject | lone d: Dir | o in d.contents }

// Now check it for a scope of 5
check oneLocation for 5


assert Wrong {
    all obj, p: (FSObject - Root) | (obj.parent = p.parent)
  }


check Wrong for 3
