abstract sig FSObject {}

sig File, Dir extends FSObject {}

sig FileSystem {
	live: set FSObject,
	root: Dir & live,
	parent: (live - root) -> one (Dir &live),
	contents: Dir -> FSObject
} {
	live in root.*contents
	parent = ~contents
}

pred move [fs, fs2 : FileSystem, x : FSObject, d: Dir] {
	(x + d) in fs.live
	fs2.parent = fs.parent - x->(x.(fs.parent)) + x->d
} 

pred remove [fs, fs2 : FileSystem, x: FSObject] {
	x in (fs.live - fs.root)
	fs2.parent = fs.parent - x->(x.(fs.parent))
}

pred removeAll [fs, fs2: FileSystem, x: FSObject] {
	x in (fs.live - fs.root)
	let subtree = x.*(fs.contents) |
		fs2.parent = fs.parent - subtree->(subtree.(fs.parent))
}

run move for 2 FileSystem, 4 FSObject
run remove for 2 FileSystem, 4 FSObject
run removeAll for 2 FileSystem, 4 FSObject
