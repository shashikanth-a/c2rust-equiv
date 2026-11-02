# c2rust-equiv

Checks whether functions in a rewritten Rust crate behave the same as the
corresponding functions in the original crate. For each function it first tries
to prove equivalence with [Kani](https://github.com/model-checking/kani)
(bounded model checking), and falls back to differential testing when Kani
can't decide.

The motivating use case is checking LLM rewrites of C2Rust's transpiled code:
rewrites that compile can still change behaviour.

## Running it

```sh
cargo install --path .
# Optional, for proofs:
cargo install --locked kani-verifier && cargo kani setup

c2rust-equiv --old original/src --new rewritten/src --report report.json
```

This checks every function whose code differs between the two crates (or the
ones named with `--function`), and writes `report.json` and `report.md`. A
function missing from the rewrite is an error.
`--cache cache.json` skips functions whose code, callees and options haven't
changed. `--eligibility out.jsonl` lists which functions are in scope, and why
the others aren't. See `--help` for timeouts, the unwinding bound and the seed.

Exit codes: 0 if every checked function was proved or tested (skipped functions
don't count), 1 if any has a counterexample, 2 on a tool error.

As a library, `check(old, new, &options)` compares two `FnUnit`s (a function
plus its callee closure). `CrateIndex` and `extract` build units from source
files; nothing assumes a particular directory layout.

## What "equivalent" means

For every input, both versions return the same value, or both panic.

- Floats are compared by bit pattern, so identical NaNs are equal, and NaNs
  with different payloads, or `0.0` and `-0.0`, are not.
- Arithmetic overflow is a panic, as in a build with overflow checks. Kani always
  checks for overflow, so the native runs use the same setting. A rewrite of
  `a.wrapping_add(b)` to `a + b` is therefore a counterexample.
- Panic messages don't matter, only whether a panic happens.

## How it works

1. **Extract.** For each function, collect its callee closure: the functions,
   constants and type aliases it uses, directly or through callees. A call
   through an `extern "C"` declaration resolves to the crate's own
   `#[no_mangle]` definition of that symbol, if there is one. Each version gets
   its own closure, so each side only calls its own callees.
2. **Generate** a scratch crate with the two closures in `mod old` and
   `mod new`, a Kani harness, and a native runner. The copies lose attributes
   such as `#[no_mangle]`, and `extern "C"` functions get the Rust ABI, so a
   panic can be caught instead of aborting the process.
3. **Kani.** There are two harnesses on `kani::any()` arguments. One calls old,
   then new, and asserts the results are equal; the other calls new first. Kani
   treats a panic as a failed check that ends the path, so a panic in the
   version called first only means "this input is covered by the other
   harness". Kani gives a concrete input for each failing harness, which is
   replayed natively; a difference there is reported as a counterexample. If
   there are no failures, the result is `proved(bounded, unwind=N)`. Kani's unwinding
   checks are on, so this also means no loop needed more than `N` iterations.
4. **Fall back** to differential testing when Kani times out, doesn't support a
   construct, needs more loop iterations than the bound, or reports a failure
   that doesn't reproduce natively (for example, a panic in shared library code
   that can't be attributed to one side). Testing runs combinations of edge
   cases per argument (0, ±1, `MIN`, `MAX`, NaN, ±inf, ±0.0, subnormals) and
   then random inputs from a recorded seed. A pass is reported as
   `tested(n_cases, seed)`: no difference was found, which is not a proof.

### The heap path — experimental

Functions with pointer or struct arguments, or that touch globals, foreign
calls or I/O, go through a second path. Instead of only scalar inputs, the
harness builds a **symbolic heap**: it generates a bounded symbolic object for
each pointer argument (structs, fixed arrays, discriminated unions, nested
pointers), runs both versions on corresponding inputs linked by a pointer
**bijection**, and compares the final heap state structurally — so a divergent
write is caught, not just a divergent return value. Equivalence here is
*observable behaviour* (in the sense of VOC / CoVaC): beyond the result and the
heap, both versions must make the same sequence of external effects.

External effects that can't be executed under verification are **modelled**, so
that both versions are treated identically and any real divergence still shows
up:

- **Foreign calls and I/O** become observable-call traces: each call records
  its arguments (scalars by value, strings by content, pointers by bijection)
  and returns one shared symbolic result, so both versions must call the same
  function with corresponding arguments in the same order. This covers calls of
  any arity, the `printf`/`sprintf` family, `sscanf`/`scanf`, `open`/`fcntl`,
  and indirect calls through function-pointer struct fields, globals,
  callback-table elements, and thread-local accessors.
- **Globals** are compared by final state: a scalar, struct or array `static
  mut` starts from its shared initialiser and its final value must agree; a
  read-only data global is carried as an identical copy (and rejected if the
  unit writes it). Error reporting (`xmlLastError`) is modelled this way, which
  is what makes "the error state is observable" hold.
- **Standard idioms** are modelled or normalised: an uncontended mutex as a
  sequential no-op, the allocator hooks (`xmlMalloc` …) and stdio stream globals
  as fixed definitions, a C incomplete type (`extern "C" { pub type X; }`) as an
  opaque pointer target, a C `goto` lowered to a `loop`+`match` over a
  function-local `enum`, and c2rust's per-file duplicate anonymous types,
  constants and `extern` redeclarations.

The guiding rule is soundness, not coverage: where an effect's real semantics
can't be reproduced (a syscall's effect on the filesystem, the bytes a `scanf`
parses, a dereferenced symbolic pointer returned by a modelled callback), the
value is left shared-symbolic and the function is conservatively left
*unproved* rather than proved on an unfaithful model. A model may make the tool
fail to prove a true equivalence; it never makes it prove a false one. Every
model has Kani tests in both directions — it proves an equivalent rewrite and
catches a divergent one.

Each function gets one status: `proved(bounded, unwind=N)`,
`counterexample(inputs, old_out, new_out)`, `tested(n_cases, seed)`,
`skipped(reason)` or `error(reason)`.

### The algebraic path (equality saturation) — experimental

Before Kani runs, a function pair is tried with a second, independent backend:
equality saturation over Program Expression Graphs (Tate et al.'s PEG / Peggy),
using the [`egg`](https://github.com/egraphs-good/egg) e-graph library. Both
bodies are translated to expression nodes and placed in one e-graph, a set of
**semantics-preserving** rewrite rules is saturated, and the two are equivalent
if they land in the same e-class. Unlike Kani this is **unbounded**: a proof
holds for all inputs, not only within an unwinding bound, and it needs no
environment model.

It is sound but deliberately incomplete:

- A proof is reported only as `proved(unbounded)`. Anything the backend cannot
  decide falls through to the Kani / testing path; it never reports a
  difference, so a "no" only means "not proved here".
- **Signature gate.** It is attempted only when both functions take and return
  exactly the same types. Equal bodies imply equal behaviour only then — an
  identity on `i32` and one on `i64` have equal expression graphs but different
  behaviour — so a signature change is left to the checks below. Argument
  *renames* are fine; the gate compares types, not names.
- **Overflow is a panic** here too, so for the checked operators (`+`, `-`,
  `*`, unary `-`) only rules that preserve both value *and* where an overflow
  can occur are kept: commutativity of `+`/`*`, `x+0`, `x*1`, `x*0`, `x-x`, and
  `x*2 = x+x`. Associativity, distributivity and `a-b = a+(-b)` are **excluded**
  for them, because they can move an overflow. c2rust's `wrapping_*` operators
  never panic (two's-complement modular arithmetic, a commutative ring), so for
  those the **full ring axioms** are kept — associativity, distributivity,
  negation — as a distinct node kind that never equates with a checked operator.
- **Fragment.** Straight-line integer functions: `let` bindings and a final or
  `return` expression over those operators, integer literals and parameters.
  Loops, pointers, calls and control flow are out of the fragment and return
  "not decided" rather than a guess.

### The relational loop path (route B) — experimental

Before the heap path's bounded run, a function pair is tried relationally when
both versions are **exactly a single flat map-style loop**: a counter from `0`
to a loop-invariant bound, each iteration writing a fresh counter-indexed
location, with no loop-carried state but the counter and a `()` return. Rather
than unroll the loop, it proves **one symbolic iteration** equivalent — an
arbitrary counter `c` in `[0, bound)` over an arbitrary initial heap. Because an
arbitrary heap over-approximates every reachable one, equal-heap-in ⟹
equal-heap-out for one iteration lifts by induction to the whole loop, for any
trip count, without a loop in the harness at all. The check compares the full
post-iteration heaps and the external-call trace, so a divergent write *value*,
a divergent write *address* (the right value to the wrong cell), or a divergent
call sequence are all caught; a proof is reported as `proved(relational)`.

It is sound but narrow, and declines (falling through to the bounded path) for
anything it is not certain of: a non-unit return, any statement after the loop,
loop-carried state other than the counter (an accumulator would be invisible to
the per-iteration check), a nested loop, a non-counter-indexed write, or pre-loop
code that is not token-identical between the two versions. The detector fails
closed — see `src/looprel.rs`.

Its reach today is bounded by the heap model, which **materialises** a
fixed-size array field (building and comparing all `N` elements), so the
unwinding bound must still cover the array's byte length even though the logical
loop is not unrolled. It therefore helps a fixed-size-array map loop whose body
is too expensive to unroll `N` times, but it does **not** yet help a loop over a
runtime-sized buffer (e.g. genann's `weight: *mut f64` with `total_weights`
elements), which the model represents as a single cell rather than an array.
Reaching those needs a non-materialising per-iteration abstraction (future work).

## Design specs

`specs/` has a TLA+ model of the verdict logic, checked in CI with TLC. It
shows that `proved` implies equivalence and every counterexample is real, for
every pair of functions on a small domain and every choice Kani can make. It
also shows why the tool reruns Kani on only the unexplained checks: Kani prints
one input per failing harness, and without the rerun that input can be a panic
both versions share, hiding the real difference. See `specs/README.md`.

## Scope and limitations

In scope (transitively through callees):

- **Scalar** functions: integers, floats, `bool`, `char`, and C type aliases
  such as `c_int`.
- **Heap** functions (see "The heap path"): pointers to structs, fixed arrays
  and discriminated unions; scalar/struct/array `static mut` globals (compared
  by final state) and read-only data globals; foreign calls and I/O modelled as
  observable-call traces; indirect calls through function-pointer fields,
  globals, callback tables and accessors; the standard C idioms listed above.

Everything else is `skipped`, with the reason. Still out of scope:

- A foreign call whose compared output depends on its *real* semantics beyond
  the shared-symbolic model (a filesystem syscall's effect, the value a `scanf`
  parses) — admitted but conservatively left unproved, never proved on the
  model. A by-value struct argument to a foreign call, a call with more than 16
  arguments, an undiscriminated union, or inline assembly is skipped outright.
- Name resolution is syntactic. It handles `use` imports, `crate::`/`super::`
  paths, `extern "C"` declarations and function-local type definitions, but not
  glob imports, macros other than `assert!`/`panic!`-style ones, or trait
  methods on crate types.
- Kani is slow on some arithmetic. Proving two 16-bit divisions equal takes
  about 40 seconds per harness on an M-series Mac, and 32-bit division hits the
  default 60-second timeout. Float-heavy functions get a shorter timeout
  (default 20s), because those proofs are often slow too. A function can be *in
  scope* (its harness builds) yet still fall back to testing or time out when
  proved — eligibility and provability are separate.
- Floating-point division is the worst case: CBMC bit-blasts the IEEE-754
  divider, so a single symbolic-`f64` divide can make an otherwise trivial proof
  time out (even proving a function equal to an identical copy). On the heap
  path the tool therefore models a float `/` as an *uninterpreted* operation,
  keyed on its operands' bit patterns — the same device it already uses for
  external calls like `exp`. This is sound for equivalence: a division is a
  deterministic function of its operands, so identical operands give an
  identical result in both versions (never a false equality), while a rewrite
  that changes the operands or their order is still caught. The cost is
  completeness — an equivalence that holds only by a floating-point algebraic
  identity (reassociation, `x/x == 1.0`, …) is reported "not proved" rather than
  "different". Integer `/` keeps its real divide-by-zero and `MIN / -1` panics.
- Functions are checked one at a time. Each check builds a small crate, which
  takes a few seconds.
- Cache keys include the tool's version but not its build, so clear the cache
  after changing the tool itself.

## Integration options

1. **External command**: a postprocessor that validates rewrites with a shell
   command can run `c2rust-equiv --old … --new … --function <name>` and use the
   exit code.
2. **Library**: call `extract` and `check` from a Rust validation step, with a
   cache shared across runs.
3. **Workspace member**: the crate has no dependencies on a particular
   toolchain or project layout, and is BSD-3-Clause licensed.

## Results

On C2Rust output, on an M-series Mac with Kani 0.68.

**Catching real changes — the headline result.** To check that the tool catches
behavioural changes, and that bounded model checking earns its keep over testing
alone, one small mutation was applied to each SQLite function that had an obvious
place for one (`<` to `<=`, a constant plus one, `wrapping_add` to `+`, `&` to
`|`, and so on):

| Mutants | Method | Counterexamples | Tested only | Proved |
|---|---|---|---|---|
| 25 | Kani, then testing | **24** (all by Kani) | 0 | 1 |
| 25 | Testing only (`--no-kani`) | **21** | 4 | 0 |

Kani finds 24 of the 25; testing alone finds only 21, missing three real bugs
that each change the result for a single boundary input, such as `allowedOp(58)`
when `>` becomes `>=`. The one "proved" mutant doesn't change behaviour (it turns
`n.wrapping_add(8)` into `n + 8` in a branch where `n` is at most 9). Some
counterexamples:

- `walHash(0)` returns 0, but the mutant returns 8191.
- `sqlite3RealToI64(-9.223372036854775e18)` returns -9223372036854774784, but
  the mutant returns `i64::MIN`.
- `sqlite3HexToInt(i32::MIN)` returns 0, but the mutant panics on overflow.

**LLM rewrites.** The next two experiments check the other direction — that
`proved` means equivalent on real, idiomatic rewrites. They were run on
the scalar path over C2Rust's C unit tests and a transpiled SQLite 3.53.4
(timings for runs without cache hits). An LLM was asked to rewrite every
in-scope function into more idiomatic Rust, keeping its signature and
behaviour. It wasn't told about this tool.

| Rewrites | Checked | Proved (bounded) | Counterexamples | Tested only | Skipped | Median / p95 time |
|---|---|---|---|---|---|---|
| Unit tests, larger model | 19 | 19 | 0 | 0 | 0 | 1.8 s / 2.0 s |
| SQLite, larger model | 34 | 30 | 0 | 3 | 1 | 2.4 s / 17.7 s |
| SQLite, smaller model | 33 | 30 | 0 | 3 | 0 | 2.1 s / 13.4 s |

None of these rewrites changed behaviour. Several looked risky but turned out
correct, for example `wrapping_rem` replaced with `%` on unsigned values, or an
`abs` that maps `i32::MIN` to `i32::MAX` replaced with `saturating_abs()`. Of
the tested-only functions, two are floating-point functions where Kani hit the
20-second float timeout, and one has a loop that needs more than 8 iterations.
With a 300-second timeout and an unwinding bound of 12, the loop is proved in
4 seconds, but both float functions still time out.
The skip uses an unstable intrinsic. A second run with `--cache` hit the cache
for every checked function, and took 5 seconds instead of 2 minutes 16.

The SQLite crate was only transpiled for this evaluation, not built.

**Heap-path proof rate (experimental, one crate).** Building the harness is not
the same as proving the function. To measure the gap, the checker was run on
genann against an identical copy of each eligible function — the simplest
equivalent rewrite — with a 120-second Kani timeout and an unwinding bound of 8,
on an unloaded machine (parallel runs starve the solver and inflate the
timeouts). Of the 12 `genann.rs` library functions (the `build.rs` script and
the `#[test]` harnesses are excluded):

| Verdict | Count |
|---|---|
| proved (algebraic or bounded) | 3 |
| exceeded the unwinding bound (a loop needs more than 8 iterations) | 1 |
| timed out at 120 s | 7 |
| an undecidable construct, skipped | 1 |
| counterexample | 0 |
| **total** | **12** |

Three functions prove: `genann_act_linear` by the algebraic backend in 0.2 s,
`genann_act_threshold` bounded in ~3 s, and `genann_act_sigmoid`
(`1.0 / (1.0 + exp(-a))`) bounded in ~37 s. The sigmoid is straight-line with no
loop, yet it proved only once floating-point division was modelled as an
uninterpreted operation: CBMC bit-blasts IEEE-754 division, and a single
symbolic-`f64` divide makes even proving the function equal to an identical copy
time out past 120 s. Modelling the divide as a deterministic function of its
operand bits (sound for equivalence; see the floating-point limitation above)
brings it inside the budget while still catching a rewrite that changes the
operands.
The loop- and float-heavy network functions (`genann_run`, `genann_train`,
`genann_init`, `genann_read`, …) loop over a runtime-sized network, which
bounded model checking cannot discharge: seven exhaust the 120-second solver
budget, one (`genann_act_sigmoid_cached`, a 4096-entry lookup table) exceeds the
unwinding bound, and one (`genann_free`) hits a pointer-alignment construct Kani
can't decide. A larger timeout and unwinding would prove a few more, as the
SQLite loop above did at 300 s, but the genuinely unbounded loops would still not
close. So on this crate the 12 functions the harness builds for reduce to 3
actually proved. Eligibility is the reach of the method, not a verification
count — read the next table accordingly.

**How far the heap path reaches (experimental).** The table below counts, per
crate, the functions the equivalence **harness builds** for — the function is in
the supported fragment and every effect it reaches is modelled soundly. This is
**not** a count of functions proved equivalent: whether Kani then proves a built
function (versus timing out or falling back to testing) is a separate question,
measured above only for the scalar path. Read it as reachability of the method,
not a verification result.

| Crate | Functions | Harness builds | % of functions |
|---|---|---|---|
| lil | 162 | 159 | 98.1% |
| genann | 25 | 24 | 96.0% |
| libxml2 | 4,867 | 3,890 | 79.9% |
| json-c | 265 | 217 | 81.9% |
| tmux | 1,389 | 651 | 46.9% |

Small, algorithmic crates approach their ceiling. The large systems crates sit
lower because their remaining functions are tightly co-blocked (a foreign call,
a global and an indirect dispatch at once) or depend on effects that can't be
soundly modelled (filesystem syscalls, FILE-buffer internals); tmux is lowest
because most of it is built on libevent's opaque event-loop machinery and its
observable behaviour is largely the external interaction itself.

## License

BSD-3-Clause. See [LICENSE](LICENSE).
