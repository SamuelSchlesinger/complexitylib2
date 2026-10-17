# Complexitylib

Complexitylib is a Lean 4 library of computational complexity theory, built on
[CSLib](https://github.com/leanprover/cslib) and Mathlib. It develops reusable arguments about
algorithms, resource bounds, reductions, lower bounds, and cryptographic security.

A central goal is to let you write recognizable functional programs and prove their efficiency
compositionally, with Turing-machine implementations justified underneath. Nonconstructive
mathematics and model-specific lower bounds also belong. Developments should establish useful
results or make those results easier to state, prove, and reuse.

## Start here

| I want to… | Start with… |
| --- | --- |
| Certify functional programs and loops | [PolyTime examples](ComplexityTests/PolyTimeTactic.lean) |
| Write probabilistic programs or oracle reductions | [PPT examples](ComplexityTests/PPTTactic.lean), [oracle examples](ComplexityTests/OraclePPT.lean) |
| Find a computational model or mathematical tool | [Module index](Complexity.lean); each module documents its definitions, results, and references |
| Contribute a result or improve an API | [Contributing](CONTRIBUTING.md) |

The checked examples show `fun_prop`, `polytime`, and `ppt` with explicit encodings and
client-supplied invariants. The deterministic backend builds on Christian Reitwiessner's tidy
machine calculus.

## Selected developments

* [Cook–Levin](Complexity/Computability/Complexity/CookLevin/Completeness.lean): SAT NP-completeness
  and UNSAT coNP-completeness, including the polynomial-time tableau reduction.
* [One-way functions to PRGs](Complexity/Crypto/Computational/OneWayToPRG.lean) and
  [adaptive PRFs](Complexity/Crypto/Computational/OneWayToPRF.lean), including
  [Goldreich–Levin](Complexity/Crypto/Computational/GoldreichLevin/HardCore.lean),
  [polynomial stretch](Complexity/Crypto/Computational/Stretch.lean), and
  [GGM](Complexity/Crypto/Computational/GGM/Security.lean), with efficient security reductions.
* [Circuit APIs](Complexity/Computability/Circuit/SourceComplexity.lean): Boolean, monotone,
  and arithmetic developments share CSLib's circuit definitions, costs, and simulations.
  The [quadratic-form correlation bound](Complexity/Computability/Circuit/Frontier/Correlation.lean)
  uses a nonconstructively chosen family; it supplies no efficient construction.
* [The PCP theorem](Complexity/Computability/PCP/Completeness.lean): `NP = PCP(log n, 1)`, with
  polynomial-time construction and verification, perfect completeness and soundness at most
  one half. The proof uses [Dinur's gap construction](Complexity/Computability/PCP/Encoded/GapTheorem.lean)
  and the library's deterministic-verifier definition of NP. Expander rotations are polynomial
  in the vertex count; the fixed construction constants remain enormous.

## Build and use

The package is named `complexitylib2`; imports begin with `Complexity.`. Most declaration
namespaces begin with `Cslib`, and Turing-machine declarations use `Turing`. Use the version in
[lean-toolchain](lean-toolchain) and the pinned dependencies in [lakefile.toml](lakefile.toml).
From a checkout:

```bash
lake exe cache get
lake build --wfail --iofail
```

Import the specific modules you need. `import Complexity` imports the whole library.

## Project information

Modules follow CSLib's APIs, paths, namespaces, and contribution standards so they can move
upstream with the import prefix changed from `Complexity.` to `Cslib.`. Acceptance requires
CSLib review. [ROADMAP.md](ROADMAP.md) records outstanding work;
[UPSTREAM.md](UPSTREAM.md) records upstream coordination and exceptional integration decisions.

Source headers retain authorship, module docstrings credit mathematical and formalization
sources, and [references.bib](references.bib) contains the bibliography.
Licensed under [Apache 2.0](LICENSE).
