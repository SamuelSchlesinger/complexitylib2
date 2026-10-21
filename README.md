# Complexitylib

Complexitylib is a Lean 4 library of computational complexity theory, built on
[CSLib](https://github.com/leanprover/cslib) and Mathlib. It develops reusable arguments about
algorithms, resource bounds, reductions, lower bounds, and cryptographic security.

A central goal is to let you write recognizable functional programs and prove their efficiency
compositionally, with Turing-machine implementations justified underneath. Nonconstructive
mathematics and model-specific lower bounds also belong. Developments should establish useful
results or make those results easier to state, prove, and reuse.

Development is AI-assisted. Contributors are responsible for the mathematical statements,
source attribution, and maintainability of their changes. Lean checks proofs against their stated
definitions; independent review checks that those definitions and statements express the intended
mathematics. See [Contributing](CONTRIBUTING.md) to propose, implement, or review a development.

## Start here

| I want to… | Start with… |
| --- | --- |
| Certify functional programs and loops | [PolyTime examples](ComplexityTests/PolyTimeTactic.lean) |
| Construct circuits for polynomial-time function families | [Uniform circuit examples](ComplexityTests/UniformCircuits.lean) |
| Write probabilistic programs or oracle reductions | [PPT examples](ComplexityTests/PPTTactic.lean), [oracle examples](ComplexityTests/OraclePPT.lean) |
| Find a computational model or mathematical tool | [Module index](Complexity.lean); each module documents its definitions, results, and references |
| Contribute a result or improve an API | [Contributing](CONTRIBUTING.md) |

The checked examples show `fun_prop`, `polytime`, and `ppt` with explicit encodings and
client-supplied invariants. The deterministic backend builds on Christian Reitwiessner's tidy
machine calculus.

The [theorem index](https://github.com/cslib-community/complexitylib/releases/download/theorem-index/main.pdf)
gives selected proved statements with their assumptions,
formalization scope and links to Lean declarations. Its [LaTeX source and editing guide](paper/README.md)
are maintained alongside the library; it is a curated catalogue, not an exhaustive API reference.

## Selected developments

* [Cook–Levin](Complexity/Computability/Complexity/CookLevin/Completeness.lean): SAT NP-completeness
  and UNSAT coNP-completeness, including the polynomial-time tableau reduction.
* Structural complexity:
  [Ladner's theorem](Complexity/Computability/Complexity/Classes/Ladner.lean),
  a [Baker–Gill–Solovay](Complexity/Computability/Complexity/Classes/Oracle/BakerGillSolovay.lean)
  oracle with `P^A ≠ NP^A`,
  a [time hierarchy](Complexity/Computability/Complexity/Classes/Hierarchy/Time.lean)
  with a polynomial gap for bit-string problems and
  [`P ⊊ EXP`](Complexity/Computability/Complexity/Classes/EXP.lean),
  [`NPSPACE = PSPACE`](Complexity/Computability/Complexity/Classes/Space/Savitch.lean),
  [TQBF PSPACE-completeness](Complexity/Computability/Complexity/Classes/Space/TQBF.lean),
  [`NL ⊆ P`](Complexity/Computability/Complexity/Classes/LogSpace/PolyTime.lean),
  [`USTCON ∈ L`](Complexity/Computability/Complexity/Classes/LogSpace/USTCON.lean),
  [Toda's theorem `PH ⊆ P^#P`](Complexity/Computability/Complexity/Classes/Toda.lean),
  [Sipser–Gács–Lautemann](Complexity/Computability/Complexity/Classes/PH/SipserLautemann.lean),
  [`BPP ⊆ P/poly`](Complexity/Computability/Circuit/Boolean/PolynomialTime.lean) and
  [worst-case-hardness derandomization](Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean).
* Interactive proofs: [`NP ⊆ IP`](Complexity/Computability/Complexity/Classes/IP.lean),
  [Shamir's theorem `IP = PSPACE`](Complexity/Computability/Complexity/Classes/IP/Shamir.lean), and
  private- and public-coin protocols for [graph non-isomorphism](Complexity/Computability/Complexity/Classes/IP/GraphNonIsomorphism.lean)
  ([in `AM`](Complexity/Computability/Complexity/Classes/ArthurMerlin/GraphNonIsomorphism.lean)).
* NP-completeness of [3-coloring](Complexity/Computability/Complexity/Problems/Coloring.lean),
  [Hamiltonian cycle](Complexity/Computability/Complexity/Problems/Hamiltonian/Undirected.lean),
  [TSP](Complexity/Computability/Complexity/Problems/TSP.lean),
  [subset sum](Complexity/Computability/Complexity/Problems/SubsetSum.lean) and further graph and number problems,
  by polynomial-time reductions.
* [Total search](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Completeness.lean):
  `LocalOpt`, `Pigeon`, `EndOfLine` and `Leaf` are complete for PLS, PPP, PPAD and PPA,
  using polynomial-time construction of their circuit codes.
* [Fagin's theorem](Complexity/Computability/Complexity/Fagin/Converse.lean): a class of finite relational
  structures is definable in existential second-order logic exactly when it is closed under
  isomorphism and in NP.
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

The package is named `complexitylib`; imports begin with `Complexity.`. Most declaration
namespaces begin with `Cslib`, and Turing-machine declarations use `Turing`. Use the version in
[lean-toolchain](lean-toolchain) and the pinned dependencies in [lakefile.toml](lakefile.toml).
From a checkout:

```bash
lake exe cache get
lake build --wfail --iofail
```

Import the specific modules you need. `import Complexity` imports the whole library.

To build searchable API documentation from the module docstrings (Python 3.11+):

```bash
python3 scripts/check_docs.py --config-only
lake -d docbuild build Complexity:docs
python3 scripts/check_docs.py
python3 -m http.server --bind 127.0.0.1 --directory docbuild/.lake/build/doc
```

Open `http://localhost:8000` to browse and search. The on-demand **API documentation** workflow
also produces an `api-docs` artifact; serve it by replacing the directory argument above with
the extracted artifact directory.

This is the canonical CSLib-based Complexitylib. The
[pre-CSLib implementation](https://github.com/SamuelSchlesinger/complexitylib-v1) is preserved as
an archive; it has a different API, and some developments remain to be ported. The temporary
repository and package name `complexitylib2` was retired when this repository moved to CSLib
Community. Downstream projects using that package name should change it to `complexitylib`; Lean
imports remain unchanged. APIs are still evolving, so downstream projects should pin a commit.

## Project information

Modules follow CSLib's APIs, paths, namespaces, and contribution standards so they can move
upstream with the import prefix changed from `Complexity.` to `Cslib.`. Acceptance requires
CSLib review. [ROADMAP.md](ROADMAP.md) records outstanding work;
[UPSTREAM.md](UPSTREAM.md) records upstream coordination and exceptional integration decisions.

Source headers retain authorship, module docstrings credit mathematical and formalization
sources, and [references.bib](references.bib) contains the bibliography.
Licensed under [Apache 2.0](LICENSE).
