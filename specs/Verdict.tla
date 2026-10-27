---------------------------- MODULE Verdict ----------------------------
(***************************************************************************)
(* The verdict logic of `check.rs`, for one function.                      *)
(*                                                                         *)
(* `old` and `new` are arbitrary functions from inputs to a value or a     *)
(* panic. Kani runs two harnesses: one calls old then new, the other new   *)
(* then old. A panic ends the path, so a harness reports a failure in the  *)
(* file of the version that panicked, or in the harness file ("lib") when  *)
(* both returned and the results differ. For each failing harness Kani     *)
(* prints one concrete input, any one of those that fail. The tool replays *)
(* those inputs natively, then decides.                                    *)
(*                                                                         *)
(* Kani's own nondeterminism is modelled by choosing, in the initial       *)
(* state, which input each harness prints, whether the run timed out, and  *)
(* whether the output parser lost the list of failed checks. TLC checks    *)
(* every combination.                                                      *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS
    Inputs,        \* a small input domain
    Values,        \* return values
    GuardEnabled,  \* the check that Kani's verdict agrees with the parsed checks
    TargetedRerun  \* on an unexplained failure, rerun Kani on only those properties

Panic == "panic"
None == "none"
Outcomes == Values \cup {Panic}

\* Files in which a harness reports a failure on input x, when it calls
\* `first` (in file ff) and then `second` (in file sf).
Fails(first, second, ff, sf, x) ==
    IF first[x] = Panic THEN {ff}
    ELSE IF second[x] = Panic THEN {sf}
    ELSE IF first[x] # second[x] THEN {"lib"}
    ELSE {}

FailingInputs(first, second, ff, sf) ==
    {x \in Inputs : Fails(first, second, ff, sf, x) # {}}

\* Inputs that fail a check outside the first-called version's file: both
\* returned and differ, or the first returned and the second panicked.
UnexplainedInputs(first, second, ff, sf) ==
    {x \in Inputs : Fails(first, second, ff, sf, x) \ {ff} # {}}

FailedFiles(first, second, ff, sf) ==
    UNION {Fails(first, second, ff, sf, x) : x \in Inputs}

VARIABLES old, new, pbOldFirst, pbNewFirst, rerunOldFirst, rerunNewFirst,
          lostChecks, timedOut, verdict
vars == <<old, new, pbOldFirst, pbNewFirst, rerunOldFirst, rerunNewFirst,
          lostChecks, timedOut, verdict>>

\* The input Kani prints for a harness: one of the failing ones, or none.
Playbacks(S) == IF S = {} THEN {None} ELSE S

Decide(o, n, pON, pNO, rON, rNO, lost, tout) ==
    LET failON == FailingInputs(o, n, "old", "new")
        failNO == FailingInputs(n, o, "new", "old")
        \* What the parser recovers: everything, or (if it lost them) no checks.
        checksON == IF lost THEN {} ELSE FailedFiles(o, n, "old", "new")
        checksNO == IF lost THEN {} ELSE FailedFiles(n, o, "new", "old")
        \* Kani's per-harness verdict line, which the parser always reads.
        verifiedON == failON = {}
        verifiedNO == failNO = {}
        \* Native replay of the printed inputs: a difference is a counterexample.
        diffs == {x \in ({pON, pNO} \ {None}) : o[x] # n[x]}
        \* Inputs printed by the targeted reruns, replayed natively.
        rerunDiffs == {x \in ({rON, rNO} \ {None}) : o[x] # n[x]}
    IN  IF tout THEN [kind |-> "fallback", input |-> None]
        ELSE IF diffs # {} THEN [kind |-> "counterexample", input |-> CHOOSE x \in diffs : TRUE]
        \* A failure outside the file of the version a harness calls first is unexplained.
        ELSE IF (checksON \ {"old"}) # {} \/ (checksNO \ {"new"}) # {}
            THEN IF TargetedRerun /\ rerunDiffs # {}
                 THEN [kind |-> "counterexample", input |-> CHOOSE x \in rerunDiffs : TRUE]
                 ELSE [kind |-> "fallback", input |-> None]
        \* The verdict must agree with the checks, or the output wasn't parsed.
        ELSE IF GuardEnabled /\ ((verifiedON # (checksON = {})) \/ (verifiedNO # (checksNO = {})))
            THEN [kind |-> "fallback", input |-> None]
        ELSE [kind |-> "proved", input |-> None]

Init ==
    /\ old \in [Inputs -> Outcomes]
    /\ new \in [Inputs -> Outcomes]
    /\ pbOldFirst \in Playbacks(FailingInputs(old, new, "old", "new"))
    /\ pbNewFirst \in Playbacks(FailingInputs(new, old, "new", "old"))
    \* A rerun restricted to the unexplained properties prints one of their inputs.
    /\ rerunOldFirst \in Playbacks(UnexplainedInputs(old, new, "old", "new"))
    /\ rerunNewFirst \in Playbacks(UnexplainedInputs(new, old, "new", "old"))
    /\ lostChecks \in BOOLEAN
    /\ timedOut \in BOOLEAN
    /\ verdict = Decide(old, new, pbOldFirst, pbNewFirst, rerunOldFirst, rerunNewFirst,
                        lostChecks, timedOut)

Spec == Init /\ [][UNCHANGED vars]_vars

Equivalent == \A x \in Inputs : old[x] = new[x]

(* Must hold. *)
\* `proved` only when every input gives the same result or both panic.
Soundness == verdict.kind = "proved" => Equivalent
\* A reported counterexample really differs.
CounterexamplesAreReal ==
    verdict.kind = "counterexample" => old[verdict.input] # new[verdict.input]

(* Known not to hold; checked to document the limitation. *)
\* Every difference Kani's model contains comes back as a counterexample.
FindsEveryDifference ==
    (~timedOut /\ ~lostChecks /\ ~Equivalent) => verdict.kind = "counterexample"
=============================================================================
