# Selected formal abstracts

The catalogue promotes twelve major result groups. Each has a checked Lean abstract with the
definitions needed to understand its statement, a bridge to the library proof, and an audited
dependency boundary. The generated PDFs display those definitions and statements with proof
bodies omitted. Lean checks the proofs; independent review must still check their intended meaning.

The [combined PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/catalogue.pdf)
and individual PDFs are published from main by the **Formal abstract PDFs** workflow. PR builds
provide review artifacts with checked-out and PR-head revisions. Publication requires integration;
a newly proposed entry may not yet appear in the main release.

## Selection

A headline must establish a substantial full endpoint with conventional, inspectable semantics,
satisfiable hypotheses, explicit models and encodings, and honest quantitative bounds. The
catalogue does not promote a partial construction, assumed core reduction, bounded experiment
or helper API as a standard theorem. Many useful library results remain outside this selection.
The former paper/TeX index is retired; Git history retains its sources.

| Result | Model and scope |
| --- | --- |
| [Cook–Levin: SAT is NP-complete](../ComplexityTests/Abstracts/CookLevinAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/cook-levin.pdf) | Explicit CNF encoding, total native-machine reductions, and UNSAT coNP-completeness. |
| [The PCP theorem](../ComplexityTests/Abstracts/PCPAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/pcp.pdf) | Perfect completeness, soundness at most one half, and explicit native efficiency; construction constants are large. |
| [Fagin: logic captures NP](../ComplexityTests/Abstracts/FaginAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/fagin.pdf) | Finite relational signatures, explicit encodings, empty universes and nullary relations. |
| [Savitch: NPSPACE equals PSPACE](../ComplexityTests/Abstracts/SavitchAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/savitch.pdf) | Native machines and polynomial space; this abstract states class equality rather than a parameterized quadratic-space bound. |
| [Reingold: undirected reachability is in L](../ComplexityTests/Abstracts/USTCONAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/reingold.pdf) | Explicit unary-size header and adjacency-matrix encoding; native logspace, without a reduction-defined SL corollary. |
| [Shamir: IP equals PSPACE](../ComplexityTests/Abstracts/ShamirAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/shamir.pdf) | All prover strategies are quantified explicitly, with a uniform native clock and specified completeness and soundness. |
| [Toda: a counting oracle decides the polynomial hierarchy](../ComplexityTests/Abstracts/TodaAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/toda.pdf) | Witness counts and oracle bit answers are explicit; correctness holds for every extension of valid oracle answers. |
| [Barrington: five states capture NC¹](../ComplexityTests/Abstracts/BarringtonAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/barrington.pdf) | Nonuniform circuits and permutation programs; no uniform generator or compiler runtime is asserted. |
| [Håstad and Razborov–Smolensky: parity resists shallow circuits](../ComplexityTests/Abstracts/ConstantDepthAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/constant-depth.pdf) | Explicit finite bounds, gate semantics and depth conventions; nonuniform lower bounds. |
| [Formula lower bounds: parity and Andreev](../ComplexityTests/Abstracts/FormulaBoundsAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/formula-bounds.pdf) | De Morgan formulas, literal leaves, explicit block indexing and finite quantitative bounds; no general-circuit lower bound. |
| [One-way functions yield pseudorandom generators and adaptive functions](../ComplexityTests/Abstracts/CryptographyAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/cryptography.pdf) | Uniform probabilistic polynomial time with explicit native evaluators, negligible advantage and full stateful oracle semantics; asymptotic security, not a concrete implementation audit. |
| [Haken: pigeonhole formulas require long resolution proofs](../ComplexityTests/Abstracts/ResolutionAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/resolution.pdf) | The non-onto pigeonhole formula and a line-based resolution rule, with bound 2^(floor(n/24)); proof size is not solver runtime. |

## Generate and review PDFs

With Python 3.11+, `latexmk`, Poppler utilities and a TeX distribution containing Libertine,
newtxmath, Inconsolata (`zi4`), microtype, tcolorbox and the usual LaTeX extras:

```bash
python3 -B scripts/build_abstracts.py --check
python3 -B scripts/build_abstracts.py
```

On Debian/Ubuntu, the workflow installs `latexmk`, `lmodern`, `poppler-utils`, `texlive-latex-extra`,
`texlive-fonts-extra`, `texlive-science` and `texlive-plain-generic`. Outputs go to `abstracts/build/`:
individual PDFs, `catalogue.pdf`, generated TeX, and `provenance.json`. They are untracked. Use `--require-clean`
for publication builds; a local build with edits records dirty-source digests and labels links as
pointing to the base revision.

Run the Lean validation sequence in [CONTRIBUTING.md](../CONTRIBUTING.md), including `lake test`,
before accepting changed abstracts. Independently compare the abstract and bridge against the
final implementation: quantifiers, machine model, encodings, resource bounds, satisfiability of
premises and mathematical source credit. Inspect every rendered page for legibility and clipping,
verify exact declaration links, and record the reviewed source revision and artifact/run. The
provenance identifies source files, bridge files, their digests, PDFs and selected declarations;
it supplements these reviews rather than replacing them.

## Layout and sources

The typography, syntax colors and pale code boxes adapt Erik Demaine’s
[translation-tiling paper style](https://github.com/edemaine/translation-tiling-paper/blob/5309313e662377d2efb353acba454859469606bd/paper.texlish)
and [Lean snippet extraction workflow](https://github.com/edemaine/translation-tiling-paper/blob/5309313e662377d2efb353acba454859469606bd/figures/extract_lean_snippets.py).
No logo is copied. Mathematical sources and earlier formalizations are credited in each Lean
abstract and its implementation. The local [lean-abstract skill](../.agents/skills/lean-abstract/SKILL.md)
describes the statement/bridge discipline and the limits of `#check_abstract`.
