# Design specs

Formal models of the parts of the design that could silently turn a real
difference into `proved`. `check.sh` model-checks every configuration and
compares the result with the one expected in the `.cfg` file's first line:
configurations marked "Must fail" document a known limitation, or show that
removing a safeguard breaks soundness.

```sh
specs/check.sh path/to/tla2tools.jar   # TLA+ tools 1.7.4
```

- `Verdict.tla`: the verdict logic in `src/check.rs`. Old and new are arbitrary
  functions from a small input domain to a value or a panic, and Kani's choice
  of printed inputs, timeouts and lost output are nondeterministic.
  - `Verdict.cfg`: a `proved` verdict implies equivalence, and every reported
    counterexample is real.
  - `VerdictNoGuard.cfg` (must fail): without the check that Kani's verdict
    agrees with the parsed checks, lost output reads as a proof.
  - `VerdictLimits.cfg` (must fail): without targeted reruns, a difference
    Kani found can come back as a fallback to testing.
  - `VerdictTargeted.cfg`: with targeted reruns, every difference Kani finds is
    reported as a counterexample.
