---------------------------- MODULE Verdict ----------------------------
(***************************************************************************)
(* The verdict logic of `check.rs`, for one function.                      *)
(*                                                                         *)
(* `old` and `new` are arbitrary functions from inputs to a value, a panic *)
(* or undefined behaviour (a memory-safety violation). Old and new are     *)
(* equivalent when, on every input where old is defined, they return the   *)
(* same value or both panic: C gives undefined behaviour no meaning, so    *)
(* the rewrite may do anything there.                                      *)
(*                                                                         *)
(* Kani runs two harnesses, old then new and new then old. A panic is an   *)
(* assertion followed by an assumption, so it ends the path. A memory-     *)
(* safety violation is an assertion only: Kani reports it and the path     *)
(* continues with an arbitrary value. Old's copy can be instrumented so    *)
(* that its memory accesses are assumptions instead (OldUBExcluded), which *)
(* removes those inputs. New's copy can be instrumented so that a memory   *)
(* violation sets a flag instead (NewUBFlagged): the two main harnesses    *)
(* then assume the flag is clear, and a third harness runs new, assumes    *)
(* the flag is set, and runs old, so that every failure there is new       *)
(* misbehaving where old is defined. For each failing harness Kani prints  *)
(* one concrete *)
(* input. The tool replays inputs natively (or under Miri, for undefined   *)
(* behaviour in new), then decides.                                        *)
(*                                                                         *)
(* Kani's own choices (which input it prints, timeouts, and whether the    *)
(* output parser lost the failed checks) are picked in the initial state,  *)
(* and TLC checks every combination.                                       *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS
    Inputs,         \* a small input domain
    Values,         \* return values
    GuardEnabled,   \* the check that Kani's verdict agrees with the parsed checks
    TargetedRerun,  \* on unexplained failures, rerun Kani on each such check alone
    OldUBExcluded,  \* old's memory accesses are assumptions, not assertions
    MiriConfirms,   \* undefined behaviour in new is confirmed by running under Miri
    NewUBFlagged    \* new's memory violations set a flag, checked by a third harness

Panic == "panic"
UB == "ub"
None == "none"
Outcomes == Values \cup {Panic, UB}

\* Running version v (in file f) on input x inside a harness: whether the
\* path continues, and the checks that fail.
Step(v, f, x) ==
    IF v[x] = Panic THEN [cont |-> FALSE, fails |-> {<<f, "panic">>}]
    ELSE IF v[x] = UB /\ f = "old" /\ OldUBExcluded THEN [cont |-> FALSE, fails |-> {}]
    \* The main harnesses assume new's flag is clear.
    ELSE IF v[x] = UB /\ f = "new" /\ NewUBFlagged THEN [cont |-> FALSE, fails |-> {}]
    ELSE IF v[x] = UB THEN [cont |-> TRUE, fails |-> {<<f, "ub">>}]
    ELSE [cont |-> TRUE, fails |-> {}]

\* Checks a harness reports failing on input x, when it calls `first` (in
\* file ff) and then `second` (in file sf). "lib" is the harness's own
\* comparison; after undefined behaviour the compared value is arbitrary, so
\* the comparison may fail too.
Fails(first, second, ff, sf, x) ==
    LET s1 == Step(first, ff, x)
        s2 == Step(second, sf, x)
        differ == first[x] = UB \/ second[x] = UB \/ first[x] # second[x]
    IN  IF ~s1.cont THEN s1.fails
        ELSE IF ~s2.cont THEN s1.fails \cup s2.fails
        ELSE s1.fails \cup s2.fails \cup (IF differ THEN {<<"lib", "assert">>} ELSE {})

\* The third harness: run new, assume it misbehaved, then run old. With old
\* instrumented, old's undefined behaviour ends the path; otherwise old's
\* violation is reported and is benign here (both are undefined).
FailsNewUB(o, n, x) ==
    IF ~NewUBFlagged \/ n[x] # UB THEN {}
    ELSE IF o[x] = UB THEN (IF OldUBExcluded THEN {} ELSE {<<"old", "ub">>})
    ELSE IF o[x] = Panic THEN {<<"old", "panic">>}
    ELSE {<<"lib", "new-ub">>}

FailingInputs(first, second, ff, sf) ==
    {x \in Inputs : Fails(first, second, ff, sf, x) # {}}

FailedChecks(first, second, ff, sf) ==
    UNION {Fails(first, second, ff, sf, x) : x \in Inputs}

\* The only failed check the tool may ignore: a panic in the version the
\* harness calls first, whose input the other harness covers.
Benign(c, ff) == c = <<ff, "panic">>

Unexplained(first, second, ff, sf) ==
    {c \in FailedChecks(first, second, ff, sf) : ~Benign(c, ff)}

\* The inputs a rerun restricted to check c can print.
InputsFor(c, first, second, ff, sf) == {x \in Inputs : c \in Fails(first, second, ff, sf, x)}

\* One rerun per unexplained check, each printing one of its inputs.
Reruns(first, second, ff, sf) ==
    LET U == Unexplained(first, second, ff, sf)
    IN {f \in [U -> Inputs] : \A c \in U : f[c] \in InputsFor(c, first, second, ff, sf)}

\* The input Kani prints for a harness: one of the failing ones, or none.
Playbacks(S) == IF S = {} THEN {None} ELSE S

InputsNewUB(o, n) == {x \in Inputs : FailsNewUB(o, n, x) # {}}
ChecksNewUB(o, n) == UNION {FailsNewUB(o, n, x) : x \in Inputs}
\* In the third harness, only old's own undefined behaviour is benign.
UnexplainedNewUB(o, n) == ChecksNewUB(o, n) \ {<<"old", "ub">>}
RerunsNewUB(o, n) ==
    {f \in [UnexplainedNewUB(o, n) -> Inputs] :
        \A c \in UnexplainedNewUB(o, n) : c \in FailsNewUB(o, n, f[c])}

VARIABLES old, new, pbOldFirst, pbNewFirst, pbNewUB, rerunOldFirst, rerunNewFirst,
          rerunNewUB, lostChecks, timedOut, verdict
vars == <<old, new, pbOldFirst, pbNewFirst, pbNewUB, rerunOldFirst, rerunNewFirst,
          rerunNewUB, lostChecks, timedOut, verdict>>

Decide(o, n, pON, pNO, pNU, rON, rNO, rNU, lost, tout) ==
    LET \* What the parser recovers: every failed check, or none if it lost them.
        checksON == IF lost THEN {} ELSE FailedChecks(o, n, "old", "new")
        checksNO == IF lost THEN {} ELSE FailedChecks(n, o, "new", "old")
        \* Kani's per-harness verdict line, which the parser always reads.
        verifiedON == FailingInputs(o, n, "old", "new") = {}
        verifiedNO == FailingInputs(n, o, "new", "old") = {}
        checksNU == IF lost THEN {} ELSE ChecksNewUB(o, n)
        verifiedNU == InputsNewUB(o, n) = {}
        \* Replay confirms a difference natively, except undefined behaviour,
        \* which only Miri can confirm. Old's undefined behaviour is no difference.
        Confirmed(x) == o[x] # UB /\ o[x] # n[x] /\ (n[x] = UB => MiriConfirms)
        diffs == {x \in ({pON, pNO, pNU} \ {None}) : Confirmed(x)}
        rerunDiffs == {x \in {rON[c] : c \in DOMAIN rON} \cup {rNO[c] : c \in DOMAIN rNO}
                              \cup {rNU[c] : c \in DOMAIN rNU} : Confirmed(x)}
        unexplained == {c \in checksON : ~Benign(c, "old")} \cup {c \in checksNO : ~Benign(c, "new")}
                       \cup (checksNU \ {<<"old", "ub">>})
    IN  IF tout THEN [kind |-> "fallback", input |-> None]
        ELSE IF diffs # {} THEN [kind |-> "counterexample", input |-> CHOOSE x \in diffs : TRUE]
        ELSE IF unexplained # {}
            THEN IF TargetedRerun /\ rerunDiffs # {}
                 THEN [kind |-> "counterexample", input |-> CHOOSE x \in rerunDiffs : TRUE]
                 ELSE [kind |-> "fallback", input |-> None]
        \* The verdict must agree with the checks, or the output wasn't parsed.
        ELSE IF GuardEnabled /\ ((verifiedON # (checksON = {})) \/ (verifiedNO # (checksNO = {}))
                                 \/ (verifiedNU # (checksNU = {})))
            THEN [kind |-> "fallback", input |-> None]
        ELSE [kind |-> "proved", input |-> None]

Init ==
    /\ old \in [Inputs -> Outcomes]
    /\ new \in [Inputs -> Outcomes]
    /\ pbOldFirst \in Playbacks(FailingInputs(old, new, "old", "new"))
    /\ pbNewFirst \in Playbacks(FailingInputs(new, old, "new", "old"))
    /\ rerunOldFirst \in Reruns(old, new, "old", "new")
    /\ rerunNewFirst \in Reruns(new, old, "new", "old")
    /\ pbNewUB \in Playbacks(InputsNewUB(old, new))
    /\ rerunNewUB \in RerunsNewUB(old, new)
    /\ lostChecks \in BOOLEAN
    /\ timedOut \in BOOLEAN
    /\ verdict = Decide(old, new, pbOldFirst, pbNewFirst, pbNewUB, rerunOldFirst,
                        rerunNewFirst, rerunNewUB, lostChecks, timedOut)

Spec == Init /\ [][UNCHANGED vars]_vars

\* The same result, or both panic, on every input where old is defined.
Equivalent == \A x \in Inputs : old[x] = UB \/ old[x] = new[x]
Normal == ~timedOut /\ ~lostChecks

(* Soundness. *)
\* `proved` only when old and new are equivalent.
Soundness == verdict.kind = "proved" => Equivalent
\* A reported counterexample is a real difference on an input where old is defined.
CounterexamplesAreReal ==
    verdict.kind = "counterexample" =>
        old[verdict.input] # UB /\ old[verdict.input] # new[verdict.input]

(* Completeness, for runs that didn't time out. *)
\* Every difference comes back as a counterexample.
FindsEveryDifference == (Normal /\ ~Equivalent) => verdict.kind = "counterexample"
\* Equivalent functions are proved, however often old has undefined behaviour.
ProvesEveryEquivalence == (Normal /\ Equivalent) => verdict.kind = "proved"
=============================================================================
