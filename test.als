sig Person {
    friends: set Person
} {
    this not in friends
}

fact {
    #({p: Person| #p.friends > 5}) = 2
}

run {} for 10 Person
