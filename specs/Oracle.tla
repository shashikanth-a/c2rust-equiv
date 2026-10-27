----------------------------- MODULE Oracle -----------------------------
(***************************************************************************)
(* Shared memoized oracles for unchanged callees.                          *)
(*                                                                         *)
(* In a harness, an unchanged callee g is replaced by a stub that returns  *)
(* a symbolic result, memoized by a key, and shared by old and new. That   *)
(* is the same as replacing g by m(key) for an arbitrary function m. The   *)
(* question is when "old and new agree for every m" implies "old and new   *)
(* agree for every real g".                                                *)
(*                                                                         *)
(* A program either returns a value, or sets a global that g reads, calls  *)
(* g with an argument, sets the global again, and continues based on the  *)
(* result. What a caller can observe is the return value, the final        *)
(* global, and the log of call arguments (which matters when g has         *)
(* external effects). The global g read is not observable by itself.      *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Args,          \* arguments to g
    Globals,       \* values of the global g reads
    Results,       \* results of g, which are also the programs' return values
    Depth,         \* maximum number of calls per run
    KeyHasGlobal   \* the memo key includes the global, not only the argument

\* A program maps the results seen so far to its next action.
Histories == UNION {[1..n -> Results] : n \in 0..Depth}
Call(a, w, w2) == [op |-> "call", arg |-> a, global |-> w, after |-> w2]
Ret(v) == [op |-> "return", value |-> v]
Actions(h) ==
    IF Len(h) = Depth THEN {Ret(v) : v \in Results}
    ELSE {Ret(v) : v \in Results} \cup {Call(a, w, w2) : a \in Args, w, w2 \in Globals}
Programs == {p \in [Histories -> UNION {Actions(h) : h \in Histories}] :
                \A h \in Histories : p[h] \in Actions(h)}

\* Run p with callee c(arg, global), starting from global g0.
\* Returns the observation <<return value, final global, call log>>.
RECURSIVE Run(_, _, _, _, _)
Run(p, c, h, global, log) ==
    LET act == p[h] IN
    IF act.op = "return" THEN <<act.value, global, log>>
    ELSE Run(p, c, Append(h, c[act.arg, act.global]), act.after, Append(log, act.arg))

Observe(p, c, g0) == Run(p, c, <<>>, g0, <<>>)

\* Real callees: any deterministic function of what g reads.
RealCallees == [Args \X Globals -> Results]
\* Oracles: an arbitrary function of the key, seen as a callee.
Keys == IF KeyHasGlobal THEN Args \X Globals ELSE Args
Key(a, w) == IF KeyHasGlobal THEN <<a, w>> ELSE a
OracleCallees == {[x \in Args \X Globals |-> m[Key(x[1], x[2])]] : m \in [Keys -> Results]}

AgreeUnder(Callees, o, n) ==
    \A c \in Callees, g0 \in Globals : Observe(o, c, g0) = Observe(n, c, g0)

VARIABLES old, new
vars == <<old, new>>
Init == old \in Programs /\ new \in Programs
Spec == Init /\ [][UNCHANGED vars]_vars

\* If the harness proves old and new equal under every oracle, they are
\* equal under every real callee.
OracleSound == AgreeUnder(OracleCallees, old, new) => AgreeUnder(RealCallees, old, new)
=============================================================================
