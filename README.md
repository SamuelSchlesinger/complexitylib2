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

For example, an ordinary list fold has a polynomial-time machine certificate:

```lean
import Complexity.Tactic.PolyTime

open Turing.MultiTapeTM

example : ComputableTidilyInPolyTime
    (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
    encBits encBits := by
  polytime
```

The claim is uniform in the input and measures time and space against its encoded length.
The deterministic backend builds on Christian Reitwiessner's tidy machine calculus. Clients
supply algorithm-specific invariants and size bounds; shared certificates and tactics handle
supported operations and composition. The linked examples cover encodings, named certificates,
correctness invariants, and limits of the automation.

## Selected developments

* [Cook–Levin](Complexity/Computability/Complexity/CookLevin/Completeness.lean): SAT NP-completeness
  and UNSAT coNP-completeness, including the polynomial-time tableau reduction.
* [Goldreich–Levin](Complexity/Crypto/Computational/GoldreichLevin/HardCore.lean),
  [polynomial stretch](Complexity/Crypto/Computational/Stretch.lean), and
  [adaptive GGM](Complexity/Crypto/Computational/GGM/Security.lean): one-way permutations to PRGs
  and PRGs to PRFs, with efficient security reductions. General OWF → PRG remains unfinished.
* [Circuit APIs](Complexity/Computability/Circuit/SourceComplexity.lean): Boolean, monotone,
  and arithmetic developments share CSLib's circuit definitions, costs, and simulations.
  The [quadratic-form correlation bound](Complexity/Computability/Circuit/Frontier/Correlation.lean)
  uses a nonconstructively chosen family; it supplies no efficient construction.
* [Dinur's gap construction](Complexity/Computability/PCP/GapTheorem.lean): combinatorial
  correctness and polynomial output size. Full PCP polynomial-time constructibility remains open,
  including integration of the [computable expander family](Complexity/Foundations/Combinatorics/Expander/AffineFamily.lean).

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
CSLib review. [UPSTREAM.md](UPSTREAM.md) tracks integration;
[ROADMAP.md](ROADMAP.md) holds plans, design decisions, and development records.

Source headers retain authorship, module docstrings credit mathematical and formalization
sources, and [references.bib](references.bib) contains the bibliography.
Licensed under [Apache 2.0](LICENSE).
