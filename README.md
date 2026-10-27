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
ones named with `--function`), and writes `report.json` and `report.md`.
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

Each function gets one status: `proved(bounded, unwind=N)`,
`counterexample(inputs, old_out, new_out)`, `tested(n_cases, seed)`,
`skipped(reason)` or `error(reason)`.

## Scope and limitations

- Only functions with scalar arguments and return values (integers, floats,
  `bool`, `char`, including C type aliases such as `c_int`) are checked, with no
  raw pointers, globals, foreign calls or I/O, transitively through callees.
  Everything else is `skipped`, with the reason.
- Name resolution is syntactic. It handles `use` imports, `crate::`/`super::`
  paths and `extern "C"` declarations, but not glob imports, macros other than
  `assert!`/`panic!`-style ones, or trait methods on crate types.
- Kani is slow on some arithmetic. Proving two 16-bit divisions equal takes
  about 40 seconds per harness on an M-series Mac, and 32-bit division hits the
  default 60-second timeout. Float-heavy functions get a shorter timeout
  (default 20s), because those proofs are often slow too.
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

On C2Rust output for two crates, on an M-series Mac with Kani 0.68. Timings
are for runs without cache hits.

**How many functions are in scope.**

| Crate | Functions | In scope | Main reasons for skipping |
|---|---|---|---|
| C2Rust's C unit tests (51 files) | 95 | 19 (20%) | raw pointers (67), globals (3), crate types (3) |
| SQLite 3.53.4 (102 files) | 2,772 | 34 (1.2%) | raw pointers (2,669), globals (47), foreign calls (11) |

**LLM rewrites.** An LLM was asked to rewrite every in-scope function into
more idiomatic Rust, keeping its signature and behaviour. It wasn't told about
this tool.

| Rewrites | Checked | Proved (bounded) | Counterexamples | Tested only | Skipped | Median / p95 time |
|---|---|---|---|---|---|---|
| Unit tests, larger model | 19 | 19 | 0 | 0 | 0 | 1.8 s / 2.0 s |
| SQLite, larger model | 34 | 30 | 0 | 3 | 1 | 1.8 s / 13.2 s |
| SQLite, smaller model | 33 | 30 | 0 | 3 | 0 | 2.1 s / 14.2 s |

None of these rewrites changed behaviour. Several looked risky but turned out
correct, for example `wrapping_rem` replaced with `%` on unsigned values, or an
`abs` that maps `i32::MIN` to `i32::MAX` replaced with `saturating_abs()`. Of
the tested-only functions, two are floating-point functions where Kani hit the
20-second float timeout, and one has a loop that needs more than 8 iterations.
The skip uses an unstable intrinsic. A second run with `--cache` hit the cache
for every checked function, and took 5 seconds instead of 2 minutes 16.

**Planted bugs.** To check that the tool catches real changes, one small
mutation was applied to each SQLite function that had an obvious place for one
(`<` to `<=`, a constant plus one, `wrapping_add` to `+`, `&` to `|`, and so on):

| Mutants | Counterexamples (all found by Kani) | Proved |
|---|---|---|
| 25 | 24 | 1 |

The proved one doesn't change behaviour: it turns `n.wrapping_add(8)` into
`n + 8` in a branch where `n` is at most 9. Some counterexamples:

- `walHash(0)` returns 0, but the mutant returns 8191.
- `sqlite3RealToI64(-9.223372036854775e18)` returns -9223372036854774784, but
  the mutant returns `i64::MIN`.
- `sqlite3HexToInt(i32::MIN)` returns 0, but the mutant panics on overflow.

The SQLite crate was only transpiled for this evaluation, not built.

## License

BSD-3-Clause. See [LICENSE](LICENSE).
