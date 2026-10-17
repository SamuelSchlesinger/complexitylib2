# Complexitylib

Complexitylib is a Lean 4 library of computational complexity theory, built on
[CSLib](https://github.com/leanprover/cslib) and Mathlib. It develops reusable arguments about
algorithms, resource bounds, reductions, lower bounds, and cryptographic security.

A central goal is to let you write recognizable functional programs and prove their efficiency
compositionally, with Turing-machine implementations justified underneath. The library also
supports the mathematical arguments these programs and complexity results need: circuits,
probability, Boolean analysis, combinatorics, algebra, and logic.

## Start here

| I want to… | Start with… |
| --- | --- |
| Prove a functional program runs in polynomial time | [Programs and efficiency proofs](docs/PROGRAMS.md) |
| Write a probabilistic program or an oracle reduction | [Probabilistic programs](docs/PROGRAMS.md#probabilistic-programs) |
| Find a theorem, computational model, or mathematical tool | [Library guide](docs/LIBRARY.md) |
| Understand the library's scope and design standards | [Mission and design](docs/DESIGN.md) |
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
The [program guide](docs/PROGRAMS.md) explains encodings, reusable certificates, correctness
invariants, and the obligations left to the programmer. This example is also exercised in
[the tactic tests](ComplexityTests/PolyTimeTactic.lean).

## Selected developments

* **Cook–Levin:** SAT NP-completeness and UNSAT coNP-completeness, with a polynomial-time
  certificate for the entire tableau reduction.
* **Cryptography:** Goldreich–Levin, one-way permutations to pseudorandom generators,
  polynomial stretch, and adaptive GGM security giving PRG → PRF.
* **Circuits:** Boolean, monotone, and arithmetic results using CSLib's circuit definitions;
  shared cost, simulation, and lower-bound APIs.
* **Supporting mathematics:** expanders, Boolean Fourier analysis, concentration, entropy,
  hashing, communication protocols, and logical interpretations.

The [library guide](docs/LIBRARY.md) links these claims to their Lean statements and records
model restrictions and open parts. In particular, general OWF → PRG and full PCP
polynomial-time constructibility remain unfinished. The quadratic-form correlation family is
chosen nonconstructively; its lower bound supplies no efficient construction.

## Build and use

The package is named `complexitylib2`; its imports begin with `Complexity.`. Most declaration
namespaces begin with `Cslib`, and Turing-machine declarations use `Turing`. Use the Lean version
in [lean-toolchain](lean-toolchain) and the pinned dependencies in [lakefile.toml](lakefile.toml).
From a checkout:

```bash
lake exe cache get
lake build --wfail --iofail
```

Import the specific modules your development needs. `import Complexity` imports the whole
library. The [contributor guide](CONTRIBUTING.md#validation) lists all six validation commands.

## Relationship to CSLib

Modules follow CSLib's APIs, paths, namespaces, and contribution standards so they can move
upstream with the import prefix changed from `Complexity.` to `Cslib.`. Upstream acceptance
requires CSLib review. [UPSTREAM.md](UPSTREAM.md) tracks that work;
[ROADMAP.md](ROADMAP.md) records implementation plans, review evidence, and development history.

The library builds on work by many authors. Source headers retain authorship, module docstrings
credit mathematical and formalization sources, and [references.bib](references.bib) contains the
bibliography. The code is licensed under [Apache 2.0](LICENSE).
