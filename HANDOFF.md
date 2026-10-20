# Handoff: October 2026 coverage batch (written 2026-10-19)

This branch (`handoff/2026-10-19`) is `main` plus this file and `handoff/`. It is a work order,
not something to merge: when every item below is integrated, delete the branch. Each epic lives on
its own `epic/*` branch; the state recorded here is exact as of the SHAs named.

## Goal and where it stands

The standing goal was seventeen results that had become cheap given the library, plus "keep the
library at cslib's standards as we go". Sixteen are on `main` (parsimonious Cook–Levin and the
counting classes, gap Clique/IS/VC, the short collapses, Kabanets–Cai, sharp Håstad, parity not FO,
PH ⊆ P^PP and FewP ⊆ SPP, Tseitin, KKL and Friedgut, Arthur–Merlin through BHZ, randomized
disjointness and Raz–Wigderson, ETH, LMN and Kushilevitz–Mansour, Generalized Geography,
IP = PSPACE, USTCON ∈ L). The seventeenth, worst-case hardness ⇒ P = BPP, is finished and approved
on `epic/stv`. Samuel also asked for first-order (FO) reduction automation (on `main`), for as
many reductions as possible to be made FO (`epic/fo-reductions`), and for the connection between
FO reducibility and logarithmic space (`epic/fo-logspace`); Circuit Value P-completeness
(`epic/circuit-value`) was added as the logspace-completeness anchor.

## How work is integrated here

Read `AGENTS.md` first. Every epic gets independent correctness and API reviews of an exact SHA;
fixes get a delta review of the fix range. The briefs used for workers and reviewers are in
`handoff/kit/` (`worker-brief.md`, `review-brief.md`).

Integration, in the primary checkout on `main`:

1. `git merge --no-ff epic/<name>`, with a message `feat(<scope>): integrate reviewed <result>`
   that names the reviewed SHAs and the review verdicts.
2. Conflicts: for `Complexity.lean` run `lake exe mk_all`; for `references.bib` run
   `handoff/kit/bin/union-conflicts.py references.bib`, then check brace balance and that no key
   is duplicated (`grep -oE '^@\w+\{\s*[^,\s]+' references.bib | sort | uniq -d`).
3. Gates: `scripts/check.sh` (or `handoff/kit/bin/run-gates <checkout>`, which holds one of two
   machine-wide slots); all six must print `ok`.
4. Paper index: add or edit the entry in `paper/sections/<file>.tex`. New links are
   `\declat{<full reviewed SHA>}{<path>}{<line>}{<declaration>}`, pinned to the reviewed head
   (which becomes an ancestor of `main` by the merge); check every line with
   `git show <SHA>:<path> | sed -n '<line>p'`. Update the count in `paper/main.tex` (it should
   equal the number of `^\begin{result}` lines in the sections listed by `sections/statements.tex`;
   110 at `80875a39`). Record the batch in `paper/review.md`. Build with
   `cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`, require exit 0 and
   no `undefined` in `main.log`, and commit `main.pdf` with the sources.
5. Update `ROADMAP.md` rows; never mark unproved work complete.
6. Commit the documentation separately (`docs(paper): …`), then push `main`. Agents are blocked
   from pushing by a guardrail: ask Samuel to run `git push origin main`.

Pitfalls met in this batch: in zsh, a variable named `path` overwrites `PATH`; plain
`lake env lean` ignores the lakefile's `autoImplicit = false` (pass `-DautoImplicit=false`); Git
can factor a shared `}` out of a `references.bib` conflict (the script repairs it); non-ASCII
symbols break `pdflatex`; `until ! pgrep -f "<pattern>"` loops match themselves and never end.

## Epics, in suggested integration order

Shared low-level files are touched by several epics (`Foundations/Data/List/Basic`, `InSpaceLib`,
`Encodings/Frame`, `Probability/PMF`, `BitString/Block`, `Logics/FirstOrder/Basic`); merge one
epic at a time, re-run the gates after each, and expect small additive conflicts.

### 1. `epic/stv`: worst-case hardness ⇒ P = BPP (goal item 15). Ready.

* Head `8cfc8e81` (includes a merge of `main` at `a9858e29`). Gates: all six `ok` at the head.
* Reviews: correctness and API reviews of `6477f06f` (milestone-1 fixes and milestone 2): APPROVE.
  The API cleanup round `6477f06f..8cfc8e81`: APPROVE (correctness and API): headline statements identical apart from namespace, no alias needed, built and axiom-clean at `8cfc8e81`, clean merge with `main` at `80875a39`. Optional non-blocking polish: move `leastIrreducible_zero`, `irreducible_leastIrreducible'` and `monic_leastIrreducible'` next to their unprimed versions in `Combinatorics/AffineDisperser/BinaryField.lean`; use `BitString.listBlock` at `HardnessEncoding/Program.lean:119,122`; in `Substitution.lean:33-34` say "more than a `δ` fraction" and "at most two gates larger".
* Integrate as above. Mention the edits to files already on `main` in the merge message:
  `AffineDisperser/Coordinates` (fold lemmas generalized to `IsMulTable`), `BitString/Block`
  (`listBlock`, `listBlock_ofFn`), `Classes/Padding` (`setOf_mem_E_of_computableTidilyInPolyTime_pad`),
  `Circuit/Boolean/Substitution` (`exists_complexity_le_of_agree_prefix`; now publicly imports
  Mathlib's reals), `Probability/PMF` (main's `toOuterMeasure_uniformOfFintype_toReal` re-proved,
  statement unchanged), `Code/Sudan`, `LocalDecoding`, `GoldreichLevin`. No deprecated aliases
  are needed (no renamed name was on `main`).
* Paper: insert `handoff/drafts/stv-entry.tex` into `paper/sections/randomness.tex` after
  "Derandomization from average-case hardness", replacing the `% \declat links` comment with links pinned to
  `8cfc8e81`: `Cslib.Complexity.P_eq_BPP_of_eventually_two_pow_le_complexity`
  (`Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean:80`),
  `Cslib.HardnessEncoding.encodedLanguage_mem_E` (`…/HardnessEncoding/PolyTime.lean:336`),
  `Cslib.HardnessEncoding.eventually_isAverageCaseHard_encodedSlice`
  (`Complexity/Computability/Circuit/Boolean/HardnessAmplification/Schedule.lean:438`),
  `Cslib.HardnessEncoding.encodedProgram_eq` (`…/HardnessEncoding/Program.lean:369`),
  `Cslib.BinaryField.card` (`Complexity/Foundations/FieldTheory/Finite/BinaryField.lean:152`).
  In the preceding entry replace "Worst-case exponential circuit hardness alone is not the
  hypothesis proved sufficient here." by a pointer to the new entry.
* ROADMAP: the "Worst-case hardness and derandomization" bullet (about line 258) and the
  "Worst-case-hardness derandomization" table row (about line 308) become done for eventual
  hardness; what remains is the infinitely-often variant, the EXP ⊄ P/poly endpoint of Babai,
  Fortnow, Nisan and Wigderson, and optional reorganizations (`Circuit/Full/`, `Matrix/` for
  `KernelVector`, cost-function namespaces, a multilinear-extension bridge).

### 2. `epic/standards-sweep`: deprecated aliases for earlier renames. Ready.

* Head `b1293417`, based on `2110aa5a` (older than `main`; the merge-tree check against `main` was
  clean). Gates: all six `ok` at the head (on its base).
* Reviews: the delta review of `2110aa5a..6d1941cf` required one fix (the `RWVertex` alias had to be
  a deprecated `abbrev` so instances still resolve) and recommended filling missed aliases; both done
  in `6d1941cf..b1293417`. Delta review of that range: APPROVE (correctness and API). The merged tree with `main` at `80875a39` builds with `--wfail` and passes `mk_all --check` and `lake lint`. Non-blocking: add `+typeChanged` to the five deprecated GNI theorems (`GraphNonIsomorphism.lean:473–497`), as on `relabelMatrix`.
* After merging, build with `--wfail`: any newer `main` code that uses a name the sweep
  deprecates would now warn and fail.
* Append `handoff/drafts/upstream-grandfather.md` to `UPSTREAM.md`, with `%SWEEP%` replaced by the
  merge SHA. Paper: no impact (the four entries that displayed old names were repinned in
  `80875a39`).

### 3. `epic/fo-logspace`: first-order model checking in L. Milestone 1 ready.

* Milestone 1 head `a1c2cb1d`; gates all six `ok`. Main results:
  `Cslib.Logic.Vocabulary.queryLanguage_mem_L` and `Cslib.Logic.FO.Definable.queryLanguage_mem_L`
  (FO-definable classes of finite relational structures have query languages in L), through
  counter programs and query machines simulated in logspace.
* Reviews: `fd3cf84a` approved with items; cleanup `ad887c0f` approved by delta review; pre-merge
  round `ad887c0f..a1c2cb1d` (merge of `main`, import and naming fixes, tests): APPROVE (correctness and API); the merge resolutions of `List/Basic` and `InSpaceLib` are additions to main only, headline statements are byte-identical to `ad887c0f`, and the branch merges cleanly with `main`, `epic/stv` and `epic/circuit-value`. Non-blocking: four non-terminal `simp`s in `ComplexityTests/FOLogSpace.lean:194-196` should be `simp only`.
* Paper: `handoff/drafts/fo-logspace-entry.tex` (links pinned to `a1c2cb1d` and checked) goes in
  `paper/sections/structure.tex` after the Fagin entry.
* Milestone 2 (FO reductions are logspace reductions) is on `epic/fo-logspace-m2-wip`
  (`ba083377`, a `wip:` commit; it does not compile and is not in `Complexity.lean`).
  `Logics/FirstOrder/Interpretation/Rank.lean` is complete (`rankEquiv`); in
  `Classes/LogSpace/FirstOrder/Reduction.lean` the scan, unrank and table-emission lemmas are
  proved and `reachesOut_rejectCode`/`encStructure_reject` fail. Still to do: assemble the
  transducer, prove `ComputableInLogSpace` for it, prove
  `FO.Reduces K K' → IsoClosed K' → LogSpaceReducible (v.queryLanguage K) (v'.queryLanguage K')`,
  and the L/P corollaries. The worker's notes on Lean pitfalls are in its final report, summarized:
  `simp` turns `List.getD` into `getElem?`; avoid `set` before `omega`; write `.halt List.nil`
  rather than `.halt []` before `]]`.

### 4. `epic/fo-reductions`: SAT NP-complete under FO reductions; FO versions of classical reductions.

* Head `03d0253b`; gates all six `ok`. Milestone-1 review fixes end at `543b3522` (gates `ok`).
* Reviews: correctness and API reviews of `de4d64bb`: APPROVE (non-blocking items C1–C6, A1–A10,
  all addressed in `dc2afc26..543b3522`, which also merges the fo-automation work now on `main`).
  Needed: a delta review of `de4d64bb..543b3522` and a full review of milestone 2
  (`543b3522..03d0253b`).
* Results: `ESO.Definable.reduces_SAT`, `ESO.definable_iff_reduces_SAT`, the Fagin forms in
  `Fagin/SAT.lean`, 3SAT ⇄ 3COL, 3SAT → simple-graph 3-colorability, SAT → independent set on
  structures with at least two elements (`FO.ReducesNontrivial`), ESO-definability of IS, clique
  and VC. Hardness assumes the class contains the empty structure (positive-dimensional
  interpretations send it to the empty, satisfiable CNF); the nonempty-structure forms are proved
  as existential corollaries. Paper: `handoff/drafts/fo-reductions-entry.tex`.
* Remaining: IS/clique/VC hardness corollaries and NP membership through vocabularies;
  reachability and NL; bridges to the encoded `SAT`/`ThreeColoring`/`IndependentSet`; SAT → 3SAT
  (see the ordered-setting section below). Given that decision, the paper should present these
  results as order-free variants (the draft does), and the standard statements belong in the
  ordered setting.

### 5. `epic/circuit-value`: Circuit Value is P-complete under logspace reductions.

* `epic/circuit-value-m1-reviewed` (`78cfcff8`) is the reviewed milestone 1: correctness and API
  APPROVE, with an API cleanup recommended before merge. `epic/circuit-value` (`645439f7`) has
  merged `main` (`73cf7ce2`), done the `simp only` item and moved `ReadMachine.runFrom_loop`; it
  builds, but the gates were not run. Still to do from the review: delete the unused
  `getElem?_frame_two_mul{,_add_one}` (they shadow main's names); use main's `budget_nat*`
  lemmas and move `sub/mod/lt/pow/finMod` budget lemmas into `InSpaceLib`; move the frame helpers
  (`dbl`, `dblT`, `frameTr`, `computableInLogSpace_frame`) to `Encodings/Frame` and
  `MultiTape/Complexity/LogSpace` (make main's private `frameT` public); rename `Tableau.Inv` and
  `inv_*` (they clash with the root `Inv` and Mathlib's `inv_zero`); shrink the public surface
  (about 160 file-local lemmas); template, docstring and naming items; add `LogSpaceHard.trans`
  and `LogSpaceHard.subset_L`; stop calling this "Ladner's theorem" (the library uses that name
  for NP-intermediate languages); axiom guards for `logSpaceReducible_of_mem_P` and `run_writer`.
  Then a delta review, then integrate.
* Paper: `handoff/drafts/cvp-entry.tex` replaces the "Circuit evaluation" entry in
  `paper/sections/completeness.tex`; add links pinned to the final reviewed head for
  `logSpaceComplete`, `logSpaceHard`, `logSpaceReducible_of_mem_P`, `mem_L_iff_forall_P_eq_L`,
  `computableInLogSpace_tableauInstance`, `Tableau.eval_circuit`, `Tableau.gateCode_inSpace`, and
  keep `CircuitValue.mem_P`. Qualify `structure.tex` line 30 ("or prove Circuit Value
  completeness") to "under first-order projections"; update ROADMAP lines about 157–165 and 369.
* Monotone Circuit Value is on `epic/monotone-circuit-value-wip` (`71b00ef2`, `wip:`; one `sorry`
  in `encMonotoneCircuitValue_dualTableauInstance`, a leftover `trace_state`, files not in
  `Complexity.lean`). Dual rail, the problem, MCVP ∈ P and MCVP ≤ CVP are proved; the
  P-hardness of MCVP goes through the dual rail of the tableau and a generic writer
  (`CircuitValue/Writer.lean`, which should absorb milestone 1's writer internals). Add the
  Goldschlager 1977 bibliography entry (check the DOI).

## Decided next step: the ordered setting, in standard terminology

Samuel decided (2026-10-19) that first-order complexity in this library should follow the standard
convention of descriptive complexity, as in Immerman's *Descriptive Complexity* and the
first-order-reduction literature, rather than the order-free framework the FO work currently uses.

What is wrong now. Immerman's structures are ordered: the universe is `{0, …, n-1}` with
`n ≥ 1`, and the numeric predicates `≤` and `BIT` (with the definable constants `0`, `1`, `max`,
and `SUC`, `PLUS`, `TIMES` definable from `≤` and `BIT`) are always available. "FO" means
FO(≤, BIT); first-order reductions are first-order queries whose output universe is the set of
k-tuples, ordered lexicographically, and whose numeric predicates are the canonical ones on that
universe; first-order and quantifier-free projections are the restricted forms. The library's
`FO.Reduces`, `FO.QFReduces` and `FO.Definable` range over arbitrary finite structures with no
built-in order, and the projection framework has a numeric-vocabulary hook without the canonical
instance. Consequences on the current branches:

* the SAT completeness theorem on `epic/fo-reductions` is order-free, so it is a different
  statement from Immerman's, and its empty-structure hypothesis exists only because the empty
  universe is allowed;
* SAT → 3SAT seems to need an order (the worker believes it is impossible without one, with no
  proof); with `≤` it is a standard quantifier-free projection, and 3SAT and 3COL hardness follow;
* FO model checking on `epic/fo-logspace` excludes `≤` and `BIT`, which Immerman's FO ⊆ L includes.

What to build.

1. Ordered structures and FO(≤, BIT): structures on `Fin n`, `n ≥ 1`, with the canonical numeric
   predicates interpreted by the order and binary expansion of `Fin n`; queries are classes of such
   structures closed under isomorphism of the input relations (equivalently, languages through the
   finite-structure encoding, which already lays structures out on `Fin n`). Fagin's theorem holds
   in both settings; state the bridge.
2. Reductions in the standard sense: k-ary first-order queries with the lexicographic order on
   tuples (the "positive-dimensional full-universe specialization and canonical numeric
   preservation" of the ROADMAP), with `≤_fo`, `≤_fop` and `≤_qfp` as the standard names, plus
   transitivity and closure of the complexity classes.
3. Restate the headline results in the standard form: SAT (and 3SAT, 3COL, IS/clique/VC) NP-complete
   under first-order (or quantifier-free) projections; FO(≤, BIT) model checking in L; first-order
   reductions are logspace reductions; then REACH NL-complete and Circuit Value P-complete under
   first-order reductions, following Immerman.
4. Keep the order-free notions as the general layer, documented as first-order interpretations
   without built-in order. Do not reuse an existing public name with a new meaning (the
   deprecated-alias rule cannot cover that): give the ordered notions their own names or
   namespace, and make the paper and docstrings say "first-order reduction" for the standard
   notion only.
5. Verify theorem and definition numbers against the book before citing them; earlier reviewers
   could not check Immerman's numbering offline.

Order of work: integrate the ready epics first (sections 1–3 above, then the reviewed parts of 4
and 5), so that the ordered layer is built on the merged FO code rather than beside it.

## Smaller follow-ups

* FO automation (on `main` since `01a8c347`), from its delta review: add an `@[fo_realize]` lemma
  `RelMap R (x : Fin n → Bundled.of X) ↔ RelMap (M := X) R x` so that `fo_reduction` simplifies
  the relations of composite and higher-dimensional interpretations; let elaboration errors in
  the interpretation propagate instead of the generic failure message; document that composites
  must appear syntactically in `fo_simp`; consider narrowing `Unique.forall_iff` in `fo_realize`;
  define `fo_iso_closed` through `fo_qf`; tighten the `hasNeighbour` test and docstring; list
  `Reduces.of_interpretation` and `Interpretation.mem_iff_unitStructure` in `Reduction.lean`'s
  Main results; in `Reduction/QuantifierFree.lean` say "a different notion from" projections.
* Unify the `length_encNat` bounds (private copies in `LogSpace.lean` and `IP/PSPACE.lean`,
  `CircuitValue.length_encNat_le_log` on `epic/circuit-value`) in fo-logspace's
  `Encodings/NatLength.lean` once both land.
* Not pushed: `main` at `88afe178` is two commits ahead of `origin/main`; all `epic/*` branches and
  this branch are local. Ask Samuel to run
  `git push origin main handoff/2026-10-19 'refs/heads/epic/*:refs/heads/epic/*'`.
