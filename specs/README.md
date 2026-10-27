# Design specs

Formal models of the parts of the design that could silently turn a real
difference into `proved`. `check.sh` model-checks every configuration and
compares the result with the one expected in the `.cfg` file's first line:
configurations marked "Must fail" document a known limitation, or show that
removing a safeguard breaks soundness.

```sh
specs/check.sh path/to/tla2tools.jar                 # TLA+ tools 1.7.4
specs/check_alloy.py path/to/alloy.jar specs/Heap.als  # Alloy 6.2.0
```

- `Verdict.tla`: the verdict logic in `src/check.rs`. Old and new are arbitrary
  functions from a small input domain to a value, a panic, or undefined
  behaviour, and they are equivalent when they agree wherever old is defined.
  A panic ends Kani's path; a memory-safety violation doesn't. Kani's choice
  of printed inputs, timeouts and lost output are nondeterministic.
  - `Verdict.cfg`, `VerdictUninstrumented.cfg`: a `proved` verdict implies
    equivalence and every counterexample is real, with or without the
    instrumentation below. Only a panic in the version a harness calls first
    may be ignored.
  - `VerdictNoGuard.cfg` (must fail): without the check that Kani's verdict
    agrees with the parsed checks, lost output reads as a proof.
  - `VerdictLimits.cfg` (must fail): without targeted reruns, a difference
    Kani found can come back as a fallback to testing.
  - `VerdictFull.cfg`: the design for pointer inputs is sound **and** complete
    for runs that finish. It combines:
    - one targeted rerun per unexplained check;
    - old's memory accesses instrumented as assumptions, so its undefined
      behaviour excludes the input;
    - new's memory accesses instrumented to set a flag, which the main
      harnesses assume is clear and a third harness checks;
    - Miri to confirm undefined behaviour in new.
  - `VerdictOldUB.cfg`, `VerdictNoNewUBFlag.cfg`, `VerdictNoMiri.cfg` (must
    fail): without each of those, equivalent functions fall back, or
    differences go unreported.
- `Oracle.tla`: shared memoized stubs for unchanged callees. A memoized stub
  is an arbitrary function of its key, so "old and new agree under every
  stub" implies "they agree under every real callee" only when the key
  determines everything the callee reads.
  - `Oracle.cfg`: keyed by the argument and the state the callee reads, the
    stub is sound.
  - `OracleArgsOnly.cfg` (must fail): keyed by the argument alone, the stub
    hides a rewrite that changes state the callee reads and then restores it.
  - Checked with up to one call per run. Two calls make the program space too
    large to enumerate.
- `Heap.als`: comparing the heaps old and new leave behind. Each version runs
  on its own copy, so the harness walks both heaps in lockstep from their
  roots and builds a correspondence between their objects. Checked up to 6
  objects (also run locally up to 8).
  - `WalkSound`, `WalkComplete`: with the injectivity check, the walk says
    "equal" exactly when the reachable heaps are isomorphic.
  - `WalkWithoutInjectivitySound` (expected counterexample): without it, one
    object shared by two fields looks the same as two equal objects, though
    writing through one alias changes what the other sees.
  - `MissedOnlyBySharing`: that is the only way the weaker walk goes wrong.
