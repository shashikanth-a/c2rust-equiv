/*
 * Comparing the heaps old and new leave behind.
 *
 * Each version runs on its own copy of the input heap, so the comparison
 * can't use addresses. The harness walks both heaps in lockstep from their
 * roots and records which object corresponds to which. The walk reports
 * "equal" when corresponding objects have the same value, the same null
 * fields, and the correspondence is consistent.
 *
 * Claim: with the injectivity check, "equal" holds exactly when the two
 * reachable heaps are isomorphic. Without it, a heap that shares one object
 * between two fields looks the same as one with two equal objects, though
 * writing through one alias changes what the other sees.
 */
module heap

abstract sig Val {}
one sig V0, V1 extends Val {}

sig Obj {
    val: one Val,
    l: lone Obj,  // two pointer fields, each possibly null
    r: lone Obj
}

abstract sig Heap {
    root: one Obj,
    objs: set Obj
}
one sig A, B extends Heap {}

fact Heaps {
    // Each heap is what its root reaches, and the two are disjoint.
    all h: A + B | h.objs = h.root.*(l + r)
    no A.objs & B.objs
    Obj = A.objs + B.objs
}

// The walk visits pairs of corresponding objects, starting from the roots
// and following a field when both sides have it.
sig Pair {
    x: one Obj,
    y: one Obj
}

fact Walk {
    all disj p, q: Pair | p.x != q.x or p.y != q.y
    some p: Pair | p.x = A.root and p.y = B.root
    all p: Pair {
        some p.x.l and some p.y.l implies some q: Pair | q.x = p.x.l and q.y = p.y.l
        some p.x.r and some p.y.r implies some q: Pair | q.x = p.x.r and q.y = p.y.r
    }
    // Only pairs the walk reaches.
    let step = { p, q: Pair | (q.x = p.x.l and q.y = p.y.l) or (q.x = p.x.r and q.y = p.y.r) } |
        all p: Pair | p in { s: Pair | s.x = A.root and s.y = B.root }.*step
}

// The correspondence the walk builds.
fun M: Obj -> Obj { { a, b: Obj | some p: Pair | p.x = a and p.y = b } }

pred sameShape {
    all a, b: Obj | a -> b in M implies {
        a.val = b.val
        (no a.l) iff (no b.l)
        (no a.r) iff (no b.r)
    }
}
pred functional { all a: Obj, b, b2: Obj | a -> b in M and a -> b2 in M implies b = b2 }
pred injective { all a, a2: Obj, b: Obj | a -> b in M and a2 -> b in M implies a = a2 }

pred walkEqual { sameShape and functional and injective }
pred walkEqualNoInjectivity { sameShape and functional }

// f is an isomorphism between the two reachable heaps.
pred iso[f: Obj -> Obj] {
    f in A.objs -> one B.objs
    all b: B.objs | one f.b
    A.root.f = B.root
    all a: A.objs {
        a.f.val = a.val
        a.l.f = a.f.l
        a.r.f = a.f.r
    }
}

// The walk's "equal" means the heaps are isomorphic (M is the isomorphism)...
assert WalkSound { walkEqual implies iso[M] }
// ...and isomorphic heaps are always reported equal.
one sig Witness { f: Obj -> Obj }
assert WalkComplete { iso[Witness.f] implies walkEqual }
// Without injectivity, sharing differences are missed.
assert WalkWithoutInjectivitySound { walkEqualNoInjectivity implies iso[M] }

// When the walk without injectivity is wrong, it's because of sharing.
assert MissedOnlyBySharing { (walkEqualNoInjectivity and not iso[M]) implies not injective }

check WalkSound for 6 but 12 Pair expect 0
check WalkComplete for 6 but 12 Pair expect 0
check WalkWithoutInjectivitySound for 6 but 12 Pair expect 1
check MissedOnlyBySharing for 6 but 12 Pair expect 0
