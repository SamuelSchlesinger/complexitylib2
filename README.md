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

The [selected formal abstracts](abstracts/README.md) present a small set of major results with
inspectable definitions and checked Lean statements. The [combined PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/catalogue.pdf)
and individual PDFs are generated from those sources. Each states its model and limitations;
the selection is not an exhaustive API reference.

## Selected results

* [Cook–Levin: SAT is NP-complete](ComplexityTests/Abstracts/CookLevinAbstract.lean): Every efficiently checkable bit-string problem reduces in polynomial time to satisfiability.
* [The PCP theorem](ComplexityTests/Abstracts/PCPAbstract.lean): NP proofs can be checked with logarithmic randomness and constantly many nonadaptive queries.
* [Fagin: logic captures NP](ComplexityTests/Abstracts/FaginAbstract.lean): Existential second-order logic captures precisely the isomorphism-invariant NP properties of finite relational structures.
* [Savitch: NPSPACE equals PSPACE](ComplexityTests/Abstracts/SavitchAbstract.lean): Nondeterminism does not enlarge polynomial space.
* [Reingold: undirected reachability is in L](ComplexityTests/Abstracts/USTCONAbstract.lean): Undirected graph connectivity can be decided with logarithmic work space.
* [Immerman–Szelepcsényi: NL equals coNL](Complexity/Computability/Complexity/Classes/LogSpace/Complement.lean): Native nondeterministic logarithmic-space machines are closed under complement, with every branch of the complement machine halting.
* [Shamir: IP equals PSPACE](ComplexityTests/Abstracts/ShamirAbstract.lean): Interaction and randomness give a polynomial-time verifier the power of polynomial space.
* [Toda: a counting oracle decides the polynomial hierarchy](ComplexityTests/Abstracts/TodaAbstract.lean): Every problem in the polynomial hierarchy is decidable in polynomial time with an exact counting oracle.
* [Barrington: five states capture NC¹](ComplexityTests/Abstracts/BarringtonAbstract.lean): Polynomial-length permutation programs on five states capture logarithmic-depth polynomial-size Boolean circuits.
* [Håstad and Razborov–Smolensky: parity resists shallow circuits](ComplexityTests/Abstracts/ConstantDepthAbstract.lean): At fixed depth, parity requires more than polynomially many gates, including over an odd-prime modular basis.
* [Formula lower bounds: parity and Andreev](ComplexityTests/Abstracts/FormulaBoundsAbstract.lean): Tree-shaped computation pays for repeated work: parity requires quadratic leaf size, and Andreev gives a stronger explicit bound.
* [One-way functions yield pseudorandom generators and adaptive functions](ComplexityTests/Abstracts/CryptographyAbstract.lean): One-wayness yields pseudorandomness, from an extra output bit to functions secure against adaptive oracle queries.
* [Haken: pigeonhole formulas require long resolution proofs](ComplexityTests/Abstracts/ResolutionAbstract.lean): The pigeonhole principle has short CNF statements but requires exponentially many resolution lines.

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

This is the canonical CSLib-based Complexitylib. The renamed historical
[pre-CSLib implementation](https://github.com/SamuelSchlesinger/complexitylib-v1) remains available
with archival pending; it has a different API, and some developments remain to be ported. The temporary
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
