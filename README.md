# complexitylib v2

A Lean 4 formalization of computational complexity theory, built on
[cslib](https://github.com/leanprover/cslib) as its base and written so that every module can be
upstreamed into cslib as-is.

## Design in one paragraph

Machines, circuits and languages come from cslib. On top of them this library adds a parametric
multi-tape machine with effects (nondeterminism, randomness, oracles) that is step-for-step
equivalent to cslib's `Turing.MultiTapeTM`/`MultiTapeNTM` in the effect-free case; a calculus of
time- and space-bounded Lean functions whose closure rules are registered with `fun_prop`, so
that "this reduction is polynomial-time" is a one-line proof; a free-monad program layer
(`PFunctor.FreeM`) in which Turing-machine programs read like straight-line code with queries and
coins; a universal machine built as an interpreter *program* rather than a hand-made machine; and,
on that foundation, complexity classes and the classical theorems. See `ROADMAP.md`.

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
