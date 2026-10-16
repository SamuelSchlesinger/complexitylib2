# complexitylib v2

A Lean 4 formalization of computational complexity theory, built on
[cslib](https://github.com/leanprover/cslib) as its base and written so that every module can be
upstreamed into cslib as-is.

## Implementation and direction

Machines, circuits and languages come from cslib. The library builds complexity theory on these
models and Christian Reitwiessner's vendored calculus of time- and space-bounded Lean functions.
Its polynomial-time closure rules are registered with `fun_prop`: many compositions of
arithmetic, conditionals and list operations have one-line proofs that an actual Turing machine
computes them in polynomial time. A universal simulator is implemented as ordinary Lean functions
with correctness and explicit time/space bounds.

The intended programming interface uses `PFunctor.FreeM`, straight-line `do` code, queries and
coins, with machine realizations and resource certificates obtained compositionally. That program
layer, the general effectful machine, and `ppt` remain to be integrated into v2. The deterministic
`polytime` tactic now combines `fun_prop`, named and local routine certificates, and bounded-growth
loop rules. Fold and iteration specifications prove both efficiency and a final invariant from
value-level contracts. These interfaces adapt the local cslib `crypto` branch to the existing tidy
TM calculus. See `ROADMAP.md` for implemented results, measured proof reductions, and the remaining
integration work.

## Layout

Every file lives at the path and in the namespace it would have inside cslib, under the library
root `Complexity` instead of `Cslib`:

```
Complexity/Foundations/…                 ↔  Cslib/Foundations/…
Complexity/Computability/Machines/…      ↔  Cslib/Computability/Machines/…
Complexity/Computability/Complexity/…    ↔  Cslib/Computability/Complexity/…   (new upstream dir)
Complexity/Languages/Programs/…          ↔  Cslib/Languages/Programs/…         (new upstream dir)
```

Each file records its upstream status on the line after `module`
(`-- upstream: candidate | submitted #N | merged @SHA | local-only (reason)`); `UPSTREAM.md` is
the ledger, and `scripts/upstream.py` prepares a module for a cslib pull request.

## Building

```bash
lake exe cache get   # Mathlib oleans
lake build --wfail --iofail
lake test --wfail --iofail
lake exe mk_all --check
lake lint
lake exe lint-style
lake exe checkInitImports
```

The toolchain and the cslib pin in `lakefile.toml` move together: `lean-toolchain` must equal
cslib's at the pinned commit, and Mathlib is never pinned separately.

## License

Apache 2.0, as cslib.
