# Selected formal abstracts

The catalogue promotes twelve major result groups. Each has a checked Lean abstract with the
definitions needed to understand its statement, a bridge to the library proof, and an audited
dependency boundary. Some abstracts also allowlist a few library modules for foundational models
(for example circuit signatures or oracle runs); each such abstract names them in its docstring, and
a reader must inspect them as well. The generated PDFs present the mathematical definitions and
selected statements first, followed by exact representation details and any shared foundations in
appendices. Proof bodies are omitted. Lean checks the proofs; independent review must still check
their intended
meaning.

The [combined PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/catalogue.pdf)
and individual PDFs are published from main by the **Formal abstract PDFs** workflow. PR builds
provide review artifacts with checked-out and PR-head revisions. Publication requires integration;
a newly proposed entry may not yet appear in the main release.

Lean sources live in `abstracts/ComplexityAbstracts/`, built as the dedicated `ComplexityAbstracts`
library (`lake build ComplexityAbstracts`). The library root imports every abstract and bridge;
`lake test` also runs their audits and the regression tests in `ComplexityTests/Abstracts/`.
Existing declaration namespaces are preserved; the catalogue records them separately from
module names when needed. Generated products remain in the ignored `abstracts/build/` folder.

## Selection

A headline must establish a substantial full endpoint with conventional, inspectable semantics,
hypotheses that are satisfiable or are standard open assumptions stated as such (such as the
existence of a one-way function), explicit models and encodings, and honest quantitative bounds. The
catalogue does not promote a partial construction, assumed core reduction, bounded experiment or
helper API as a standard theorem. Many useful library results remain outside this selection. The
former paper/TeX index is retired; Git history retains its sources.

| Result | Model and scope |
| --- | --- |
| [Cook–Levin: SAT is NP-complete](ComplexityAbstracts/CookLevinAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/cook-levin.pdf) | Explicit CNF encoding, total native-machine reductions, and UNSAT coNP-completeness. |
| [The PCP theorem](ComplexityAbstracts/PCPAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/pcp.pdf) | Perfect completeness, soundness at most one half, and explicit native efficiency; construction constants are large. |
| [Fagin: logic captures NP](ComplexityAbstracts/FaginAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/fagin.pdf) | Finite relational signatures, explicit encodings, empty universes and nullary relations. |
| [Savitch: NPSPACE equals PSPACE](ComplexityAbstracts/SavitchAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/savitch.pdf) | Native machines and polynomial space; this abstract states class equality rather than a parameterized quadratic-space bound. |
| [Reingold: undirected reachability is in L](ComplexityAbstracts/USTCONAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/reingold.pdf) | Explicit unary-size header and adjacency-matrix encoding; native logspace, without a reduction-defined SL corollary. |
| [Shamir: IP equals PSPACE](ComplexityAbstracts/ShamirAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/shamir.pdf) | All prover strategies are quantified explicitly, with a uniform native clock and specified completeness and soundness. |
| [Toda: a counting oracle decides the polynomial hierarchy](ComplexityAbstracts/TodaAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/toda.pdf) | Witness counts and oracle bit answers are explicit; correctness holds for every extension of valid oracle answers. |
| [Barrington: five states capture NC¹](ComplexityAbstracts/BarringtonAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/barrington.pdf) | Nonuniform circuits and permutation programs; no uniform generator or compiler runtime is asserted. |
| [Håstad and Razborov–Smolensky: parity resists shallow circuits](ComplexityAbstracts/ConstantDepthAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/constant-depth.pdf) | Explicit finite bounds, gate semantics and depth conventions; nonuniform lower bounds. |
| [Formula lower bounds: parity and Andreev](ComplexityAbstracts/FormulaBoundsAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/formula-bounds.pdf) | De Morgan formulas, literal leaves, explicit block indexing and finite quantitative bounds; no general-circuit lower bound. |
| [One-way functions yield pseudorandom generators and adaptive functions](ComplexityAbstracts/CryptographyAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/cryptography.pdf) | Uniform probabilistic polynomial time with explicit native evaluators, negligible advantage and full stateful oracle semantics; asymptotic security, not a concrete implementation audit. |
| [Haken: pigeonhole formulas require long resolution proofs](ComplexityAbstracts/ResolutionAbstract.lean) · [PDF](https://github.com/cslib-community/complexitylib/releases/download/formal-abstracts/resolution.pdf) | The non-onto pigeonhole formula and a line-based resolution rule, with bound 2^(floor(n/24)); proof size is not solver runtime. |

## Generate and review PDFs

With Python 3.11+, `latexmk`, Poppler utilities and a TeX distribution containing Libertine,
newtxmath, Inconsolata (`zi4`), microtype, tcolorbox and the usual LaTeX extras:

```bash
python3 -B scripts/build_abstracts.py --check
python3 -B scripts/build_abstracts.py
```

On Debian/Ubuntu, the workflow installs `latexmk`, `lmodern`, `poppler-utils`, `texlive-latex-extra`,
`texlive-fonts-extra` and `texlive-plain-generic` without recommended packages, and caches the
downloaded archives. Outputs go to `abstracts/build/`:
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

Release publication additionally requires successful **Lean Action CI** for the exact artifact
source SHA, from a `push` to `main` in this repository. The publication job waits up to 20 minutes
for that run, selects the latest workflow run and current attempt, and rejects missing, failed,
cancelled, mismatched or still-pending validation. It rechecks Lean success and current main
before every release creation, asset deletion/replacement and release edit. PR PDF review
artifacts remain available without publication. No second Lean build is started for this gate.

After a failed Lean run, rerun Lean CI first; once its latest attempt succeeds, the failed
publication job can be retried while that SHA is still main. It downloads the immutable artifact
ID exported by the successful PDF build, rather than assuming a new artifact exists for the
publication retry's attempt number. API checks and release mutations are separate operations:
a concurrent main update or rerun can still occur after a check. Each subsequent write rechecks
the gate, and an already-started write cannot be rolled back atomically with GitHub's CI state.

This gate addresses the two codebase-review findings recorded in
[#432](https://github.com/cslib-community/complexitylib/issues/432). Its workflow identity,
event/SHA filtering, pagination and attempt handling follow the
[GitHub workflow-run REST API](https://docs.github.com/en/rest/actions/workflow-runs);
artifact selection follows [download-artifact v4](https://github.com/actions/download-artifact/tree/v4).

## Layout and sources

The source section `/-! ## Representation details ... -/` marks definitions and explanations
to display in an appendix. The group ends at the next `##` section heading. Its definitions are
retained in full; selected theorem statements must remain in the main presentation. A
`## Compatibility aliases` section is omitted only when all its code consists of explicit
`@[deprecated ...] alias old := target` declarations. Any substantive declaration there fails
validation. These are presentation conventions in comments, not new Lean syntax.

An entry using shared definitions lists their modules in its `foundations` array, for example
`["ComplexityAbstracts.Encoding", "ComplexityAbstracts.Computation"]`. The list must exactly match
the abstract's direct foundation imports and their transitive foundation imports. The audit helper
and proof bridges are excluded from that display check; Lean's `#check_abstract` still checks the
actual elaborated dependency boundary, including dependencies of allowed definitions. A listed
foundation cannot be another abstract or bridge, and missing, duplicate, unused or cyclic
foundation modules fail validation.

Individual PDFs include the needed foundations with their definitions, theorem signatures,
namespaces and source links. The combined catalogue displays each foundation once, after the
selected abstracts. `provenance.json` records each foundation's source digest and declaration
links, and a source change during rendering invalidates the build. Single-file Markdown and TeX
previews also include imported foundations and identify their local source digests. Moving a
definition to an appendix does not establish an encoding-invariance or model-equivalence theorem;
any such change still needs a checked correspondence in Lean.

The typography, syntax colors and pale code boxes adapt Erik Demaine and Stefan Langerman’s
[translation-tiling paper style](https://github.com/edemaine/translation-tiling-paper/blob/5309313e662377d2efb353acba454859469606bd/paper.texlish)
and [Lean snippet extraction workflow](https://github.com/edemaine/translation-tiling-paper/blob/5309313e662377d2efb353acba454859469606bd/figures/extract_lean_snippets.py).
No logo is copied. Mathematical sources and earlier formalizations are credited in each Lean
abstract and its implementation. The local [lean-abstract skill](../.agents/skills/lean-abstract/SKILL.md)
describes the statement/bridge discipline and the limits of `#check_abstract`.
