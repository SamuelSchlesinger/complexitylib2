# Theorem-index review

## 2026-10-22: PP is closed under truth-table reductions (#386 / PR #389)

Worker `worker-jetski-54e3dbd2` (Jetski, for Samuel Schlesinger, continuing the work of
`worker-jetski-92802680`) adds the entry "PP is closed under truth-table reductions" to
`paper/sections/randomness.tex`. It has twelve declaration links pinned at
`186effd8a94ec88b9d8bb4b6b1f9f5bf0667f94e` (`Classes/PP/TruthTable.lean`,
`Reduction/TruthTable.lean`). The entry states the Fortnow–Reingold theorem for arbitrary
injective encodings, the indexed form with a polynomial-time unary query count and Boolean
combiner, the Beigel–Reingold–Spielman Boolean corollaries, bounded quantifiers and `P` closure.
It sketches the Newman-polynomial proof and states that adaptive closure (`P^PP = PP`) is not
claimed.

An independent AI subagent (session `653043ec`) reviewed `33f5224a` (style/API, correctness,
index) and approved with non-blocking findings. Its suggestions were applied in `8f8fcea3` and
`f8abf0e3`: reuse of the existing bit-string map lemmas, trimmed public imports, lemma
docstrings, and the per-index gap-bound wording in the entry. Moving
`GapP.exists_abs_le_two_pow` into `Classes/SharpP.lean` is deferred to #394.

A second independent subagent (session `4b34f225`) reviewed `f8abf0e3` and approved. It checked
all twelve links against the exact source lines, the quantifiers, encodings, unary-output
conditions and gap bounds, and the nonadaptive scope. LaTeX was unavailable locally, so the
rendered PDF must be inspected from the CI artifact. This records AI review, not human editorial
approval.

Coordinator reviewer `c4bd95db` approved `7f51726e` and asked for a follow-up delta before merge.
It credits Newman [Newman1964] in the module docstring and the entry, and makes the unindexed
amplification helpers (`newmanAmp` and its lemmas, `one_le_newmanPoly`) private. The links were
re-pinned to `186effd8`, where only line numbers moved. The coordinator arranges review of this
delta.

## 2026-10-22: Search-tree deletion (#359)

Worker `worker-crei-dc679113` (Claude Code, for Christian Reitwiessner) extends the existing
unbalanced search-tree entry with a paragraph on the pure deletion operation and five
declaration links pinned at `490f03d7092b12bd9b6d62cebc066f632c865da8`
(`Complexity/Algorithms/Lean/SearchTree/Erase.lean`, lines 141/182/201/232/244). The prose states
that deletion is not part of the stateful interface, which hypotheses need the ordering invariant,
and the deviation from Chapter 12 of CLRS for nodes with only a right subtree.

An independent AI subagent reviewed source revision `f4b5694a` (style/API, correctness,
documentation) and found the original no-impact assessment for this entry wrong; the entry was
added in response, and `erase_eq_self` was renamed `erase_eq_of_notMem`. A second independent
subagent reviewed the delta at `9ee31b1d`, verified every link against the exact source line,
checked quantifiers, hypotheses, cost model and height claims, and approved; its wording nit
("leftmost (least)") was applied. LaTeX was unavailable locally, so the rendered PDF must be
inspected from the CI artifact. This records AI review, not human editorial approval.

## 2026-10-22: Fan-in-`d` Cook–Mertz procedure (#363)

Worker `worker-crei-dc679113` (Claude Code, for Christian Reitwiessner) extends the Cook–Mertz
Tree Evaluation entry with a paragraph on the fan-in-`d` procedure and three declaration links
pinned at `4e9da5a9b9fe8c45d08d85b23c776b9cf04937b9` (`Ary/CookMertz.lean` lines 211/240,
`Ary/Basic.lean` line 127). The prose states that only correctness is proved for the
fan-in-`d` procedure and that the machine and space bounds concern the binary procedure.

An independent AI subagent reviewed `8ae8219c` (style/API, correctness, index) and approved.
It verified the register layout coincides with the binary one at `d = 2`, the degree bound
`d * ℓ < |K| - 1`, non-vacuous test instances, and every link. Its findings (a gate declared in
the wrong namespace, and wording implying a fan-in-`2` machine exists for the new procedure)
were fixed in `4e9da5a9` and `11fee324`; the links were re-pinned and re-checked against the
exact source lines. LaTeX was unavailable locally, so the rendered PDF must be inspected from the
CI artifact. This records AI review, not human editorial approval.

## 2026-10-22: AWPP is low for PP (#364 / PR #366)

Reviewed Lean revision: `58e1be2840acca3c0169f8b032ed9542afe3994e`.
Reviewed index and PR-head revision: `cff320b911f370292144063b5560d18649d8dd03`.
Scope: “AWPP is low for PP” in `paper/sections/randomness.tex`, section 4.33.
The entry states lowness for every AWPP word oracle and arbitrary injective input encoding
in the strict adaptive oracle-verifier model. It records the common dyadic denominator,
the aggregate error bound, rejection of exact majority ties, and the separate probabilistic
oracle-machine characterization that remains outside the result.

Independent read-only Codex reviewers `review_awpp_style` (API/style) and
`review_awpp_foundations` (correctness and theorem-index semantics) approved these source
and index revisions, as recorded in the PR. A stale index limitation was corrected before
the final index review. Coordinator `coordinator-crei-dc679113` independently approved
the mathematics and Lean sources at PR head `cff320b9` in
[review comment 6343670967](https://github.com/cslib-community/complexitylib/pull/366#issuecomment-6343670967),
requesting this review record and successful API-documentation evidence before merge.

CI PDF provenance, checked by Codex worker `worker-awpp-review-20261022`:

- [Theorem index PDF run 39769087126, attempt 2](https://github.com/cslib-community/complexitylib/actions/runs/39769087126/attempts/2),
  [artifact 12433196414](https://github.com/cslib-community/complexitylib/actions/runs/39769087126/artifacts/12433196414).
- Checked-out merge revision: `7954e28f09305e096f3ef1dd8ca48f81301b895f`.
- PR head: `cff320b911f370292144063b5560d18649d8dd03`;
  PR base: `62bbf525e2d7edce00dc8b6c79a52040223c5bed`.
- The artifact's `provenance.json` reports clean sources and PDF SHA256
  `c3f2ccfbf8629258cb8b8d2d4f87d9652d88969b2f9b65f917ff53c81074cd28`;
  hashing the downloaded PDF reproduces it.
- Visually inspected rendered page 58 of the 144-page artifact: the complete entry,
  formulas, citation and three declaration links are readable, without clipping or overlap.
  All three PDF URI annotations target the reviewed code revision, at `AWPP/Lowness.lean:145`,
  `AWPP/OracleWeights.lean:43` and `SharpP/WeightedReplay.lean:63`; the published source
  at each target contains the named declaration and matches the PR-head source.

[API documentation run 39794423110](https://github.com/cslib-community/complexitylib/actions/runs/39794423110)
succeeded at `cff320b911f370292144063b5560d18649d8dd03` on 22 October 2026.
Documentation-pin checks, API generation, generated-documentation checks and artifact upload
all succeeded. The evidence-record commit `504539b0fee950310d40ce1732defa6fb383cb63` changed
only this review record. These AI reviews do not imply maintainer or human editorial approval,
or a Lean proof of prose equivalence.

### Optional review nits

Worker `worker-awpp-review-20261022` also addressed all five optional nits from the coordinator's
review: distinguish oracle-reply replay from saved-coin replay in the module documentation,
write `replyStep_eq_answerStep` as a term, restrict the `p` unfolding to `dsimp only`, make
the `2 ^ 4 = 16` rewrite explicit in `sum_error`, and credit Li's 1993 work alongside
Fenner--Fortnow--Kurtz--Li and Fenner's amplification argument. The historical attribution
was checked against Section 6.1 of *An Oracle Builder's Toolkit*, using its existing
`FennerEtAl2003` bibliography entry.

Independent read-only Codex reviewer `/root/review_awpp_nits` approved API/style, correctness
and source credit with no findings. Reviewed base: `504539b0fee950310d40ce1732defa6fb383cb63`;
SHA256 of `git diff --binary` against that base, restricted to `*.lean`:
`f9307b13202b6474a9e4b884e2c8543e4158d62e4fb8b658a4a38d08aff3dc60`.
The reviewer rechecked the final library-relative replay-module path for upstreamability.
No public definitions, statements, hypotheses, models or bounds change, so the theorem index
needs no prose rewrite. Its immutable declaration links still resolve at the reviewed source
revision and original lines. This follow-up does not extend the earlier CI results to the
changed sources; validation of this revision is recorded in its commit description.

## 2026-10-22: Query machines in the space of their states (#367)

Source revision: `3450e5b40702816dc5504c60be8d87cf27fc9049`. Worker `worker-crei-dc679113` (Claude Code, Claude Opus 5.5, for
Christian Reitwiessner) extends the query-machine paragraph of the first-order model checking
entry in `structure.tex`. It adds one sentence and a link to `Turing.QueryMachine.computableInSpace`,
pinned at `9ab11b36b32709fd85bebd07d00e106125fa904b`, line 341. The log-space theorem keeps its
signature and becomes a corollary. This is the first slice of implicit Tree Evaluation (M2 of #361).

An independent AI review of `6f1e43eb` approved the statement, the corollary, the pin (checked with
`git show`) and the prose. Its nits are applied: the module doc is reflowed, the docstring now says
"length of the input", and the index sentence states the linear-space hypothesis on the parts.
No author reviewed their own change.

Validation: all six gates of `scripts/check.sh` passed at `6f1e43eb`. Later commits change only
documentation and were rebuilt with targeted builds. LaTeX is not installed locally, so the CI
"Theorem index PDF" artifact still needs inspection.

## 2026-10-22: Withdrawal of hollow and overclaimed results (#372 / PR #375)

Coordinator `coordinator-jetski-90c7e6c8` and worker `worker-jetski-90c7e6c8-docs` (Jetski, for
Samuel Schlesinger, by maintainer decision) withdrew results merged earlier on 2026-10-22 after five
independent read-only audit agents and a separate holistic review found them hollow or overclaimed.
In the theorem index, the oblivious-transfer completeness entry (#340) and the Regev LWE entry
(#343) are deleted from `crypto.tex`. The ACC⁰ entry in `circuits.tex` (#344), the permanent/PIT
entry in `synthesis.tex` (#341) and the Håstad entry in `completeness.tex` (#347) are retitled and
rewritten to say that Williams's `NEXP ⊄ ACC⁰`, Kabanets–Impagliazzo and Håstad's MAX-E3SAT hardness
are *not* proved. The uniform-`P` frontier entry (#339/#350) is retitled "Conditional". Links to
deleted declarations are removed; the Håstad dichotomy link is re-pinned to `cc3bf009` because its
statement changed, and all other pins are kept. The theorem-index entries introduced by #340, #341,
#343, #344 and #347 have no `review.md` entries of their own; this entry records their withdrawal or
rewriting. The Gentry entry (#348) is unchanged and already states the interface boundary.

Two independent AI reviewers that did not author the change reviewed `83154d45` ([review comment
6346010319](https://github.com/cslib-community/complexitylib/pull/375#issuecomment-6346010319)).
`acbe3d2f` (correctness and cslib API) approved. Its non-blocking findings were a stale Håstad test
docstring and the `≈ 4.5624977` notation, both fixed in `e9cb03bf`/`fbf95767`, and pointers to the
pre-withdrawal SHA `62bbf525`, added in ROADMAP. Possibly unused `IdentityTesting.lean` imports were
left as a follow-up (listed in #381, now covered by #390); the cosmetic `Inclusions.lean` prose was
left as an untracked follow-up. `67f11a80` (theorem index and documentation) approved. It verified
every `\declat` link at its pin, including the Håstad dichotomy at `cc3bf009` line 1207, and checked
that no withdrawn result is still claimed in `paper/`, `README.md` or `ROADMAP.md`. Its findings
were applied before merge: the "folded Long Code tables" wording, the Håstad title, and the
"Conditional" frontier titles. The delta to the merged head `fbf95767` contains only these fixes.
The coordinator integrated the PR with a merge commit, so `cc3bf009` stays reachable ([integration
note](https://github.com/cslib-community/complexitylib/pull/375#issuecomment-6347215382)).

CI PDF provenance, inspected by `coordinator-jetski-90c7e6c8`: run
[39815565810](https://github.com/cslib-community/complexitylib/actions/runs/39815565810),
artifact `theorem-index-fed926282746e3543df6ce370aa02f5df763940d-1`, `source_sha` `fed92628`,
`pull_request_head_sha` `fbf95767`. Pages 11 (§1.15), 61 (§5.8), 69 (§6.20), 83 (§6.30) and 113
(§13.7) were checked. The PDF text contains no occurrence of `Regev`, `ObliviousTransfer`,
`kabanets_impagliazzo` or `not_NEXP_subset_ACC0`. Link URIs were not checked byte by byte. Recorded
on 2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381). This records AI review, not
human editorial approval.

## 2026-10-22: Single-tape, TM0/TM1 and multi-tape simulations and Partrec bridges (#318 / PR #345)

Worker `worker-8f698304` (Antigravity) adds three entries to `paper/sections/structure.tex`
(after the Kolmogorov uncomputability entry), with 44 declaration links pinned at
`b7c399478f6dc2fe3b50d4bc18396df450207f30`: tape equivalences with Mathlib and `SingleTapeTM` ↔
`TM0`/`TM1` translations plus the one-work-tape multi-tape simulation (time `2|x|+4+(t+(|y|+1))`,
input-only time `3|x|+2t+6`, space `T+1`); `Partrec`/`Computable` bridges for single-tape,
`TM0`/`TM1` and multi-tape machines; and machine-backed Kolmogorov complexity with additive
optimality of `universal`. The prose states finite inhabited alphabet, inhabited state and local
store hypotheses, and that reverse multi-tape-to-single-tape simulation, prefix-free complexity
and multi-tape-to-single-tape time-bounded transfer are not formalized.

The PR body records independent subagent reviews: correctness `d93d2e32` and API/style `7fb754d2`
(both approved; docstring nits fixed in `b7c39947`), and a theorem-index review `0e8b1992` of
`structure.tex` (initial review at `e68b7190`, re-review at `b7c39947`). That review found a
subscript typo, a duplicate `whenever` clause, and imprecise alphabet, state/store, `toTM1`/`toTM0`
and quantifier wording. All of them (the PR body counts five) were fixed in `6f82f255`, the 44 links
were verified, and the re-review approved. Coordinator `agy-coordinator-e5f10553` approved with
reviewer `2683ca0d` at `6f82f255` and head `a90687f0` (entry split, equation wrap, merge of `main`)
in [comment
6334347036](https://github.com/cslib-community/complexitylib/pull/345#issuecomment-6334347036). It
records Theorem index PDF run `39733205950` (source `d26e697b`, PR head `a90687f0`, PDF SHA256
`d825e097755bd9638253b94dacae16f27e8ada3c232e8db127ead798ec9d613d`), with rendered pages 27–29
inspected; no artifact ID is recorded. The comment names `paper/sections/models.tex` and module
names that differ from the merged diff (`structure.tex`). Backfilled on 2026-10-22 by
`worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human editorial
approval.

## 2026-10-22: Uniform P sumset-extractor frontier lower bounds (#342 / PR #350)

Worker `worker-887d7d77` (Claude Opus 4.6) revises the sumset-extractor frontier entry in
`paper/sections/circuits.tex` (Entry 6.19) and adds Entry 6.20, "Uniform P frontier lower bounds,
affine dispersers, and balanced padding". Entry 6.19 notes the polylogarithmic case of `k_n = o(n)`
and replaces the fan-in-`r` bound with `(1 + 1/A_{r+1} - ε)n < (r-1) innerSize(C)`, defining `A_d`
inline. Entry 6.20 covers nondeterministic and aggregate-gate variants, the sumset-disperser to
affine-disperser bridge with the Mishra–Santhanam gate-elimination bound, one-bit balanced padding,
and membership in `Cslib.Complexity.P encBits`. It states that the extractor or disperser family
and its polynomial-time certificate are explicit hypotheses. All 28 declaration links are pinned
at `2586065df0d42bc13b40a1832855a45e0c19d779`.

The PR records three independent AI reviews of `2586065d`: style/API
(`018af067-5ef2-4ba9-91de-0a8825a7f5fd`) and mathematical correctness
(`af57a71a-25b2-4155-8a35-0585bd554a96`) both approved. The theorem-index review
(`ec7e2a56-0330-4909-8fc4-5019e22ef3d2`) checked all 28 links, quantifiers, models and bounds. It
requested three changes: pin links at `2586065d`, define `A_d` inline, and state the finite
commutative monoid `T` with capacity `β(n) = o(n)`. All three were fixed in `089c076c` and approved
on re-check. Coordinator `agy-coordinator-e5f10553` approved in [comment
6334321748](https://github.com/cslib-community/complexitylib/pull/350#issuecomment-6334321748), with
independent reviewer `47325b9f-8cd0-4db4-9d06-0b0a07003e2b`, at `089c076c` (full Lean and index
review) and head `c7b02b44` (layout split into Entries 6.19 and 6.20, merge of `main`). The comment
records Theorem index PDF run `39732739073` (source `f72ab6ab`, PR head `c7b02b44`, PDF SHA256
`561fc322190ac5d3181e49e58c09a1d12881008c4a83a0244f12f65bb9b9b7db`); rendered pages 67–68 were
inspected, and all 28 links resolve at `2586065d`. No artifact ID is recorded. Backfilled on
2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human
editorial approval.

## 2026-10-22: Sumset-extractor bridge to the Gaussian frontier bound (#320 / PR #339)

Worker `worker-887d7d77` (Gemini) adds the `paper/sections/circuits.tex` entry "Sumset-extractor
bridge to the Gaussian frontier lower bound" (rendered as entry 6.19), with twelve declaration
links pinned at `7ec92e6d` (`Gaussian/Coefficient.lean`, `FanInTwo.lean`, `InnerSize.lean`,
`Frontier/Extractor.lean`). It states the Chor–Goldreich flat-source equivalence, the
rectangle-bias bridge via `zeroPad`, the constant `L_* ≥ 4.56249`, and conditional average- and
worst-case lower bounds. The prose says the extractor family is a hypothesis and that no explicit
extractor construction or Turing-machine runtime is proved.

The PR records independent API review by `018af067-5ef2-4ba9-91de-0a8825a7f5fd` and correctness
review by `af57a71a-25b2-4155-8a35-0585bd554a96`, both of the working tree before `7ec92e6d`. The
correctness review found no issues. All three API findings (moving the PMF distance lemmas, citing
`ChorGoldreich1988`, listing a main result) were fixed in `7ec92e6d`. Theorem-index reviewer
`ec7e2a56-0330-4909-8fc4-5019e22ef3d2` checked `circuits.tex` against `7ec92e6d` and found no
issues: quantifiers, hypotheses, models, bounds, limitations and all 12 links. Coordinator
`agy-coordinator-e5f10553` approved head `8b3edf57`, with reviewer
`031528e0-8785-4498-b4f3-a494411d50c0`, in [comment
6333775653](https://github.com/cslib-community/complexitylib/pull/339#issuecomment-6333775653). That
comment records PDF run
[39726538132](https://github.com/cslib-community/complexitylib/actions/runs/39726538132), artifact
`theorem-index-e68f7d3c…-1`, source `e68f7d3c`, PR head `8b3edf57`, PDF SHA256
`37858275b8fc83d06aac4fbd6fa5d60c10c24dd9adaaae08215ad377e2bf7070`. The coordinator visually checked
page 63 and found all 12 link annotations targeting `7ec92e6d`. Backfilled on 2026-10-22 by
`worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human editorial
approval.

## 2026-10-22: Semifilter covers and De Morgan circuit size (#334 / PR #336)

Claude Opus 5.5 in Claude Code (session `9f9433f2`) adds the entry "Semifilter covers and De
Morgan circuit size" to `paper/sections/circuits.tex`, with six declaration links pinned at
`46bde484` (`Fusion/Quadratic.lean` line 322, `Fusion/DeMorgan.lean` lines 164/178/201/213/233).
It states `ρ(f) ≤ C_∧(f) ≤ ρ(f)²`, `ρ(f) ≤ 2C(f)` and `C(f) ≤ 4(ρ+1)²(2n+ρ+1) + n`. The prose
says the lower bound holds for every admissible witness class and the upper bound needs
unrestricted semifilters. It also says the bound on `C(f)` depends on `n`, is cubic when
`ρ(f) ≥ n` only because of the construction, and formalizes known correspondences.

The PR records three reviews by separate, edit-free Claude Opus 5.5 subagents: correctness and
cslib-style API reviews of `4746ce93`, whose findings (including overstated "polynomially
equivalent" wording) were resolved in `46bde484`, and a fresh fix and theorem-index review of
`7a745a18`. That review found an unproved "not in ρ(f) alone" claim and a missing link for
`pairCoverComplexity_le_two_mul_complexity`, both resolved in `213783db`. It also checked every link
against `46bde484` and every bib key. Coordinator `agy-coordinator-e5f10553` approved head
`213783db` with independent reviewer `agy-reviewer-subagent-1e7a7626` ([comment
6333204109](https://github.com/cslib-community/complexitylib/pull/336#issuecomment-6333204109)). The
coordinator inspected PDF run 39725680620 (source `76e43681`, PR head `213783db`, PDF SHA256
`0b3359f9…`): page 74, entry 6.26, all six links matching the Lean declarations. Backfilled on
2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human
editorial approval.

## 2026-10-22: Ordered first-order reductions are logspace reductions (PR #312)

Main session `claude-opus-5-5-48cb80c1` (Claude (Opus 5.5), with Claude subagents as workers and
reviewers; milestones 1 and 2 of #309) adds the `paper/sections/structure.tex` entry "Ordered
first-order reductions are logspace reductions", with 20 declaration links pinned at
`834487c03e8b5c978728c85dc4d45266f4a5408a`. It also rewrites the full-tuple transducer and
order-free interpretation entries around the shared domain-counting transducer, re-pinning their
links to `834487c0`, and fixes the stale "restricted-domain … remain open" sentence in the preceding
entry. The prose states admissibility (`m ≥ 2`) as a library convention, that certificates are
supplied rather than derived, and that only lexicographic image orders and relational targets are
covered, excluding projections and completeness.

At `d3840a07`, unnamed independent AI subagents approved correctness and API/style with nits (fixed
or documented). The theorem-index reviewer requested prose changes (31/31 links OK): a stale
neighbouring disclaimer, the certificate-scope sentence and a fixed-interpretation caveat. The PR
body says these were fixed in the fix batch `5e78416e` and that a re-review of that batch was
stopped before reporting, so the prose fixes rest on the author's account; the later approval below
checked the links, not these prose changes. Reviewer `ea300e14-88c3-47b1-86e6-7f52e0fee39f`
(research subagent, coordinator `agy-coordinator-b99e4a87`) then approved source `834487c0` and head
`5e78416e` in [comment
6331708147](https://github.com/cslib-community/complexitylib/pull/312#issuecomment-6331708147). The
review covered API/style and correctness, and checked all 28 `structure.tex` links against
`834487c0`. The author built the paper locally (pages 19–21); no CI PDF artifact or provenance is
recorded. Backfilled on 2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this
records AI review, not human editorial approval.

## 2026-10-22: Native van Emde Boas set operations on the word RAM (#273 / PR #313)

Worker sessions `codex-veb-273-20261021-1949` and `edf4ee40-4dec-41b0-92d4-e4f7bfbd3290`
(Antigravity), for Samuel Schlesinger, rewrite the `paper/sections/query.tex` entry
"Fixed-program van Emde Boas membership on the word RAM" as "Fixed-program van Emde Boas sets
on the word RAM". It now covers insertion, membership and strict successor through one
213-instruction dispatcher. It also covers a separate charged initializer, the space footprint,
generic-RAM transfer, and admissible adaptive clients. The prose states that client control
between calls, argument writes and result decoding are not charged, and that deletion and
predecessor are not implemented. Sixteen links are pinned at source commit `c48d7153`
(`Init.lean`, `Call.lean`). The `Model.lean:125` link stays at `c4de62e6`. The index commit is
the PR head, `bb7b987c`.

The PR records one review in [comment
6331659911](https://github.com/cslib-community/complexitylib/pull/313#issuecomment-6331659911),
posted from the shared account. Reviewer session `b74d5b21-b22a-41b8-8514-41d708ce0ebc` (`research`
subagent) wrote it as an "Independent Review Report" and approved. It names coordinator session
`agy-coordinator-b99e4a87`. It reviewed `c48d7153` and `bb7b987c` for cslib API/style, correctness
and non-vacuity. For the theorem index, the report states only that all 17 `\declat` links match the
exact paths, lines and declaration names. It records no check of the prose's quantifiers, hypotheses
or bounds, and no findings or resolutions. The PR lists a local `python3 scripts/build_paper.py` run
under validation. No CI PDF artifact or rendered-page inspection is recorded. Backfilled on
2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human
editorial approval.

## 2026-10-22: Whole-run generic-RAM simulation and certificate transport (#292 / PR #311)

Antigravity worker session `3d6e71a5-59b4-4b8b-811a-3d4048ee1042` (for Samuel Schlesinger)
adds the entry "Whole-run generic-RAM simulation and certificate transport" to
`paper/sections/query.tex`. It has 16 declaration links pinned at source commit `5349b55a`
(`GenericRAM/Simulation/Run.lean` and `BigO/Sum.lean`). The same PR revises the preceding
"Certified encoded steps for fixed generic-RAM programs" entry: variables are renamed, and its
closing limitation now points to the new result. The new prose covers clocked `run`/`eval`,
sparse-memory growth and refinement against the semantic interpreter, trajectory-maximum
bounds and per-step bound retention. It covers general and polynomial-time transport to
native multitape TM certificates, with word-RAM specializations. It keeps configuration
selection and the trajectory length bound as caller hypotheses and claims no universal
variable-program interpreter. The index text is in commit `92e5b496` (PR head).

One review is recorded in [comment
6331087484](https://github.com/cslib-community/complexitylib/pull/311#issuecomment-6331087484). Its
reviewer is `research` subagent session `9ce9b544-65ac-4a4f-b3c8-3b83f8053ac1`, and it lists
coordinator session `agy-coordinator-b99e4a87`. The review covered source `5349b55a` and index
commit `92e5b496` and approved, with no findings recorded. It covered cslib API/style, correctness
and non-vacuity, and the theorem index. For the index, it checked all 16 links against `5349b55a`
(path, line, name) and judged the prose and scope limits accurate. The PR records no theorem-index
PDF artifact or CI provenance, and no rendered-page check. Backfilled on 2026-10-22 by
`worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human editorial
approval.

## 2026-10-22: Word-RAM doubling arrays (#160 / PR #310)

PR #310 adds the entry "Doubling arrays with charged allocation on the word RAM" to
`paper/sections/query.tex`. It has eight declaration links pinned at `992832d5`, all in
`Complexity/Algorithms/WordRAM/DynamicArray.lean`. The entry states the twelve-register invariant,
15-instruction initialization, append and growth bounds, the potential 15(2n-c) with amortized
append cost 49, and dispatcher charges 52 and 6. It also states the `15 + 52m` total for
initialized adaptive clients and the frontier bound f < 4n. Its limitations are that old blocks
are never reclaimed, so f < 4n bounds the total words ever allocated, and that shrinking,
deletion, argument delivery, result decoding and compiled client controllers are not claimed.
OpenAI Codex worker `worker-dynamic-platform-20261021` wrote the prototype. Google Antigravity
worker `6af1a6ac-54e0-44a9-8f47-e8985b0e86b2` completed it under coordinator
`agy-coordinator-b99e4a87`.

Independent `research` subagent `d72f7fb3-7779-49dc-a06c-d83f06af2e89` approved the Lean sources,
tests and `ROADMAP.md` at `992832d5`, and the index at PR head `0bf9852a`. It passed cslib
API/style, correctness and non-vacuity, and theorem-index parity, and checked all eight pins against
`992832d5`. It recorded no findings. Its report was posted in [comment
6330678781](https://github.com/cslib-community/complexitylib/pull/310#issuecomment-6330678781) from
the shared `SamuelSchlesinger` account. The PR records no separate coordinator verdict. The Theorem
index PDF CI run 39707489275 succeeded at head `0bf9852a`, but the PR records no inspection of its
artifact or rendered pages. Backfilled on 2026-10-22 by `worker-jetski-89a6c8ae` from the PR record
(#381); this records AI review, not human editorial approval.

## 2026-10-22: Polynomial-time rational hitting-list generator (#201 / PR #308)

Google Antigravity worker `8583d3ab-5631-41b6-acf5-9118b0d39efa` (under coordinator
`agy-coordinator-b99e4a87`) adds the entry "Polynomial-time rational matrix hitting-list generator"
to `paper/sections/synthesis.tex`. It has 33 declaration links pinned at `9901fecb`. The entry
states the hitting property, the dimension and encoding-length bounds, and the parameter,
lift-table, Cramer and grid stages. It also states that the standalone generator is computable
tidily in polynomial time on a multi-tape Turing machine (per the PR body and the Lean theorem,
`hittingGenerator : List Bool → List Bool` from `encBits` to `encBits`). Its stated limitation is
that polynomial bit complexity of evaluating a formula on the emitted matrices is not asserted. The
"remains open" and "remains separate" sentences in the determinant-stage and rational-encoding
entries now point to the new entry.

The PR records one independent reviewer, `research` subagent `0075a653-f49b-4475-a801-0d730c582e84`.
It reviewed the Lean sources and tests at `9901fecb`, and the roadmap and theorem index at
`05f6a11f` (the PR head). Its verdict was APPROVE, with PASS on cslib API/style, mathematical
correctness and non-vacuity, and theorem-index parity. It reported no findings and verified the
`\declat` pins against `9901fecb`. The report is in [comment
6330641156](https://github.com/cslib-community/complexitylib/pull/308#issuecomment-6330641156). No
separate coordinator approval is recorded. The Theorem index PDF CI run 39707258917 succeeded at
head `05f6a11f`, but no inspection of its artifact is recorded. Backfilled on 2026-10-22 by
`worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human editorial
approval.

## 2026-10-22: Certified encoded steps for fixed generic-RAM programs (#298 / PR #307)

The PR adds the entry "Certified encoded steps for fixed generic-RAM programs" to
`paper/sections/query.tex`, with twelve declaration links pinned at
`ead23ddb44ccb64c4c5796a0e19c275aaac714b7` (`GenericRAM/Simulation/Finite.lean`,
`GenericRAM/Simulation/Turing.lean`, `BigO/Sum.lean`). The entry states that the finite-state step
agrees exactly with `M`'s step, gives the framed encoding-length bound, and says each fixed program
has a tidy native multitape TM certificate. Primitive and sparse-memory costs stay as parameters.
The prose says that no universal interpreter for variable programs is claimed. It also leaves input
initialization, output decoding, clocked iteration, word-width selection and whole-run transport as
separate work. OpenAI Codex workers `worker-stateful-classics-20261021` (`f1f9b6e1`) and
`worker-native-step-20261021` wrote it. Google Antigravity worker
`3d6e71a5-59b4-4b8b-811a-3d4048ee1042` completed and validated it (`ead23ddb` / `9d3f4e47`), working
under coordinator `agy-coordinator-b99e4a87`.

Independent `research` subagent `86ddbaef-91ff-4a0b-b90f-7113ad52b9c0` reviewed the Lean sources and
tests at `ead23ddb` and the roadmap and index at `9d3f4e47` (PR head). It covered cslib API/style,
correctness and non-vacuity, and theorem-index parity, and approved in [comment
6330244350](https://github.com/cslib-community/complexitylib/pull/307#issuecomment-6330244350). It
re-reviewed the index after fixes to the `FiniteState` 4-tuple description and the
`length_encoding_le` formula, and checked all 12 `\declat` pins. The PR records no separate
coordinator approval, and no PDF/CI artifact provenance. Backfilled on 2026-10-22 by
`worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human editorial
approval.

## 2026-10-22: Fixed-program van Emde Boas membership on the word RAM (#302 / PR #306)

OpenAI Codex worker `codex-veb-273-20261021-1949` (Lean `c4de62e6`, index `10f41219`), preserving
prototype contributions by `/root/veb_273/veb_layout` and `/root/veb_273/veb_ram_plan`, adds the
entry "Fixed-program van Emde Boas membership on the word RAM" to `paper/sections/query.tex`;
coordinator `agy-coordinator-b99e4a87` integrated it onto `main` at `a8b00acd`. The entry states a
fixed 32-register standard unsigned word-RAM program (213 compiled instructions) answering
membership within `28(d+1)+18` instructions, preserving memory and root, with stale extrema and
arbitrary bounded surrounding memory. It records as uncharged or open: represented-memory
construction, argument delivery/result decoding, a space/stack bound, an adaptive client, and
insertion/strict-successor correctness. Four links are pinned at
`c4de62e616a2a5859a089f60b0aa8c2546b7638b` (`Call.lean` lines 98/123/138, `Model.lean` line 125).

Independent reviewer subagent `1ce2e5b0-36e4-4573-80c0-12c1c5dde0e3` (`research`) reviewed
`c4de62e6` / `10f41219` for cslib API/style, correctness and non-vacuity, and theorem-index parity,
and approved in [comment
6329884332](https://github.com/cslib-community/complexitylib/pull/306#issuecomment-6329884332). It
found the prose accurate on quantifiers, model, exact bound, assumptions and limitations, and all
four links matching the exact lines; it recorded no findings. The integration commit `a8b00acd`
merges `main` and, beyond that, changes only `ROADMAP.md` URLs. The Theorem index PDF CI run
39701451685 succeeded at that head, but no inspection of its artifact is recorded. Backfilled on
2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human
editorial approval.

## 2026-10-21: Subbotovskaya shrinkage and Andreev's formula lower bound (#268 / PR #286)

Gemini worker `agy-worker-b24933fa` (implementation subagent `agy-worker-b24933fa/formula-lb`,
`db62e14a`) adds the entry "Subbotovskaya shrinkage and Andreev's formula lower bound" to
`paper/sections/circuits.tex`, with seven declaration links pinned at `41d3ef2c` (Lean commit;
`Subbotovskaya.lean` lines 353/560/573/615, `Andreev.lean` lines 264/364/399). The prose counts
De Morgan formula input leaves (constants contribute none), not general circuit gates with
fanout; truncates `S_k - k N_k` and `L(h) - 2br` at `0`; and states that `Andreev_{b,m}` is
explicit only because its truth table is part of the input, while the hard `b`-bit table inside
the proof comes existentially from Shannon counting. Review fixes came from worker subagent
`723f3e35` (continuing recovery work `agy-subbotovskaya-recovery-20261021-2228`).

The author's independent subagent `agy-worker-b24933fa/review-268` (`4d8a0023`) reviewed `ad6af114`
and `491c1653`: API/style passed with one module-docstring nit (fixed in `491c1653`); correctness
and theorem-index review passed with no issues, checking quantifiers, bounds, limitations and all
seven links. Coordinator `agy-coordinator-d55a006b`, with independent subagents `9157150e`
(API/placement) and `6fb68dfb` (correctness and index), then requested changes at `491c1653`
([comment
6324334296](https://github.com/cslib-community/complexitylib/pull/286#issuecomment-6324334296)),
including the missing truncation-at-0 caveats in the index, the main merge conflict and link
re-pinning, and moving `PartialAssignment` and leaf-size lemmas to shared modules. Coordinator
`agy-coordinator-b99e4a87` and independent re-reviewer `agy-reviewer-pr286-20261021` (`9bcb1cfd`)
approved head `6dbe675e` (Lean `41d3ef2c`) ([comment
6328441065](https://github.com/cslib-community/complexitylib/pull/286#issuecomment-6328441065)),
listing resolutions for the earlier findings: the index now states both truncations and all seven
links are re-pinned to `41d3ef2c` with checked line numbers. The author ran `scripts/build_paper.py`
locally. The Theorem index PDF CI run 39690369346 succeeded at head `6dbe675e`, but no inspection of
its artifact or rendered pages is recorded. Backfilled on 2026-10-22 by `worker-jetski-89a6c8ae`
from the PR record (#381); this records AI review, not human editorial approval.

## 2026-10-21: MOD_q gates in TC and threshold gates in NC^1 (#269 / PR #285)

Gemini worker `agy-worker-b24933fa` (implementation subagent `agy-worker-b24933fa/tc-nc`) adds two
entries to `paper/sections/circuits.tex`: simulating MOD_q gates with majority gates (giving
`AC^i[q] ⊆ TC^i` and `AC^0[p] ⊊ TC^0` for odd primes `p`), and carry-save bit counting with
threshold/majority in `NC^1` and fan-in-bounded `TC^i` in `NC^(i+1)`. The prose states that the
inclusions are nonuniform and that unbounded wire multiplicity in `TC^i` without a fan-in bound
is not covered. Its 25 declaration links are pinned at `5c7a9990`.

The author's review subagent `agy-worker-b24933fa/review-269` reviewed `28552bfd` and `0df188f8`
(style/API, correctness, theorem index) with no issues except unpinned `\decl` links, fixed in
`0df188f8`. Coordinator `agy-coordinator-d55a006b` and independent subagent `c25e9fce` requested
changes at head `0df188f8` (Lean `28552bfd`) in [comment
6324473636](https://github.com/cslib-community/complexitylib/pull/285#issuecomment-6324473636). They
verified the bounds and the 25 anchors, but found misplaced test guards, a duplicate XOR formula,
bit-string helpers outside `Cslib.BitString`, and API/import problems, and asked for re-pinned
anchors. Coordinator `agy-coordinator-b99e4a87` and independent re-reviewer
`agy-reviewer-pr285-20261021` approved head `682b0a72` (Lean `5c7a9990`) in [comment
6328533529](https://github.com/cslib-community/complexitylib/pull/285#issuecomment-6328533529),
recording every finding as resolved and the anchors re-pinned with checked line numbers. No CI PDF
artifact provenance is recorded; the PR reports only a local `python3 scripts/build_paper.py` run.
Backfilled on 2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI
review, not human editorial approval.

## 2026-10-21: Native bounds for fixed tuples and option branches (#301 / PR #304)

OpenAI Codex worker `worker-native-products-20261021` adds the entry "Native bounds for fixed
tuples and retained-input option branches" to `paper/sections/query.tex` (Section 10.10), with
six declaration links pinned at source `798d9514` (`BigO/Pi.lean` lines 43/58/82/99/110,
`BigO/Option.lean` line 39). The prose states `O(E+1)` time and space for fixed tuple selection,
gathering and update, summed arbitrary bounds `E + sum_i T_i` / `E + sum_i S_i` for tuple
construction, and retained-input option elimination charging `2T_v + E` plus the selected handler.
It notes that dimensions are fixed, constants are existential, and that an encoded RAM step
simulator and whole-run theorem transport remain separate work.

Independent reviewer `controller_review / codex-coordinator-20261021-2200` approved API,
correctness, tests and theorem-index content at source `798d9514` and exact head `0a70be7e`
([comment
6327631484](https://github.com/cslib-community/complexitylib/pull/304#issuecomment-6327631484)). Its
sole finding, in a test-file header, was fixed and rechecked. A local rendering review checked page
84 of the 116-page PDF and all six annotations. Coordinator `agy-coordinator-b99e4a87` inspected the
CI artifact ([comment
6328104218](https://github.com/cslib-community/complexitylib/pull/304#issuecomment-6328104218)):
[Theorem index PDF run
39682036237](https://github.com/cslib-community/complexitylib/actions/runs/39682036237), synthetic
merge `b53dace8`, `source_dirty = false`, PR head `0a70be7e`, base `b235d43c`, PDF SHA256
`8ace530b4cded53473dfaf1c5e36a9172f230fe0280b217663978368572e921b` (checked against the download).
The coordinator viewed page 84 and checked all six URI annotations against `798d9514`. Backfilled on
2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human
editorial approval.

## 2026-10-21: Encoded sparse memory on native multitape machines (#293 / PR #299)

Codex worker `worker-sparse-memory-20261021` adds the entry "Encoded sparse memory on native
multitape machines" to `paper/sections/query.tex`, with seven declaration links pinned at
`33579ebf` (`GenericRAM/SparseMemory/Basic.lean` lines 82/98, `Turing.lean` lines
96/323/266/359/335). The prose states `AList` functional-update semantics, that default-valued
writes retain a binding (the count is stored cells, not nondefault support), the `m(4K+2V+3)`
encoding bound, and asymptotic `O((E+1)^3)` time and `O(E+1)` workspace in full encoded input
length (not exact step counts), crediting Christian Reitwiessner's calculus. It is a finite-memory
component only, not a simulation of whole RAM programs.

Independent Codex reviewer `/root/controller_review` approved source/API, correctness, tests and
index semantics at source `33579ebf` and documentation-only PR head `584a4001`, after its
documentation findings (asymptotic rather than exact bounds; dependence on encoded address length,
not magnitude) were resolved; it inspected local page 82 and all seven links. Coordinator
`codex-coordinator-20261021-1949` with nonauthor `/root/review_288` approved `584a4001` for source
and index statements/links with no findings ([comment
6326855292](https://github.com/cslib-community/complexitylib/pull/299#issuecomment-6326855292)).
`controller_review / codex-coordinator-20261021-2200` approved CI artifact `12382706420` of [run
39676209285](https://github.com/cslib-community/complexitylib/actions/runs/39676209285) (merge
`f4cb7021`, base `7ebefd57`, head `584a4001`; 115-page PDF SHA256 `0f5c69bd3e11dac9...`, matching
provenance): page 82 clean, all URI annotations at `33579ebf` ([comment
6327632872](https://github.com/cslib-community/complexitylib/pull/299#issuecomment-6327632872)). It
also approved a combined tree with #303 (`552ef833`, index block byte-unchanged) and asked for
refreshed-head CI evidence before integration; the PR records none. Backfilled on 2026-10-22 by
`worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human editorial
approval.

## 2026-10-21: Native certificates for encoded RAM primitives (#296 / PR #303)

PR #303 adds the entry "Native certificates for encoded RAM primitives" to
`paper/sections/query.tex`. It covers arbitrary-bound native certificates, which exist exactly
when a function is natively computable, and their composition. It also covers fixed-symbol scalar
bundles, the bounded-natural addition/order model, and checked word addition with unary width.
The prose excludes memory access, control dispatch, initialization/output, whole-run simulation,
charged width selection with input fit, exact-real bit encodings and the full standard word basis.
No explicit degree is claimed. OpenAI Codex authored it; the PR gives no author agent/session ID.
All five links pin `0e4ef81e` (`Native.lean` 116/88/185, `Native/Nat.lean` 131,
`WordRAM/Native.lean` 48). Final head is `915660b9`, which is documentation-only.

Independent nonauthor Codex reviewer `/root/controller_review` approved source `0e4ef81e` and head
`915660b9` with no findings ([comment
6326897033](https://github.com/cslib-community/complexitylib/pull/303#issuecomment-6326897033)). The
approval covers API, correctness, tests and theorem-index prose. The reviewer inspected local PDF
page 82 of 115 and all five link annotations. Coordinator `controller_review /
codex-coordinator-20261021-2200` approved head `915660b9` and the CI artifact ([comment
6327630636](https://github.com/cslib-community/complexitylib/pull/303#issuecomment-6327630636)). The
artifact is `12383540126` from Theorem index PDF run `39678547035`. Its provenance records clean
merge `6ae61459`, head `915660b9` and base `1e2dcd0c`. The PDF has 116 pages and SHA256
`b190dde0d1f927542f25e8ab455d4615d865431af439e956101315527c828956`. Page 82 and all five links were
checked, with no findings. Comment 6327940549 approves a combined tree with #299 and records no
findings. Backfilled on 2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this
records AI review, not human editorial approval.

## 2026-10-21: Recursive van Emde Boas sets (#291 / PR #300)

OpenAI Codex worker `/root/veb_273`, with subagents `/root/veb_273/veb_layout` and
`/root/veb_273/veb_ram_plan`, adds the entry "Recursive van Emde Boas sets: functional
correctness" to `paper/sections/query.tex`. It has six declaration links pinned at public source
`c76e69150ffb627ee0166044826ff463f198e334`. The prose states bounded insertion for `x < U_d`,
membership, successor for every natural query, and the layout bound `S_d <= 10 U_d`. It also says
the layout is arithmetic, not a proved memory representation. No RAM instruction bound, charged
initializer, machine-space bound or compiled controller is claimed, and deletion and predecessor
are excluded. The PR is the first milestone of #273.

Independent reviewers `/root/review_288` (API and correctness) and `/root/index_288` (theorem-index
semantics, public links and local rendering) approved exact head `5c1c4772` (tree `b1886a71`) with
no findings. A paper typo and the test-module witness from preliminary review were fixed.
Coordinator `codex-coordinator-20261021-1949` approved in [comment
6326751486](https://github.com/cslib-community/complexitylib/pull/300#issuecomment-6326751486) and
[comment
6326953691](https://github.com/cslib-community/complexitylib/pull/300#issuecomment-6326953691).
`/root/index_288` inspected CI PDF run 39676853239, artifact 12382577980 (synthetic checkout
`81d30c0d`, base `7ebefd57`). It reports clean provenance and PDF SHA256 `41b20973…daee`. It viewed
page 86 and checked all six URI targets against `c76e6915`, with no findings. Backfilled on
2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human
editorial approval.

## 2026-10-21: Binary division, GCD and reduced-rational encoding (#283 / PR #288)

Worker `agy-worker-f29e46b2/rational-m2` added the `synthesis.tex` entry "Polynomial-time binary
division, Euclidean GCD, and reduced-rational encoding" (section 13.4). It also removed
canonical rational serialization from the open milestones listed in the determinant entry. The
entry certifies tidy polynomial-time multi-tape computation of `a / b` and `a % b` (where
`a / 0 = 0` and `a % 0 = a`), of `Nat.gcd` with fuel `ℓ(a) + ℓ(b) + 1`, of `encodeNat`, and of
`encodeRat (Rat.divInt a b)`. It has 14 declaration links pinned at `20c7c139`. The prose says
that generating the full rational hitting list remains separate (M3–M5 of #201, per the PR body).

Independent subagent `agy-reviewer-f29e46b2/m2-review` reviewed head `0089e7b2` (Lean `20c7c139`)
for correctness, API/style and the theorem index, and approved with 0 findings after checking all 14
links. For coordinator `codex-coordinator-20261021-1949`, nonauthor reviewers `/root/review_288`
(source/API/correctness) and `/root/index_288` (theorem index) approved the same head with no
findings. Nonblocking items: the PR description's milestone range (corrected to M3–M5) and an extra
blank line at `Gcd.lean:219` (left unfixed). Samuel supplied the downloaded archive of CI PDF
artifact 12375449349 (Theorem index PDF run 39664876749, attempt 1; synthetic merge `06887829`, head
`0089e7b2`, base `23d97bee`). Root matched the archive hash and PDF SHA256
`f715ecb06c562667dab92f7ff6130e0414eaf5813fb905056d81565bf5ef3344` (115 pages). Root also inspected
page 89 and checked all 14 PDF URI targets, and `/root/index_288` independently repeated these
checks with no findings. The coordinator gave final approval in [comment
6326714226](https://github.com/cslib-community/complexitylib/pull/288#issuecomment-6326714226).
Backfilled on 2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI
review, not human editorial approval.

## 2026-10-21: Polynomial-time division-free integer determinant (PR #281)

Worker `agy-worker-f29e46b2/detrows-m1` (Antigravity, Claude and Gemini) adds the entry
"Polynomial-time division-free integer determinant" to `paper/sections/synthesis.tex`, with seven
declaration links pinned at `ccbd129b70945682840a7c36525544c317b23d53`
(`Rational/Runtime/Determinant.lean`, lines 184/265/286/432/474/537/670). The prose states `detRows
A = det (ofRows A)`, the stage bit-length and `stageTableBound` length bounds, and
`detRows_polytime` for `encList (encList encIntBin)` to `encIntBin`. It completes only Milestone 1
of #201 and says the remaining generator-runtime milestones (rational serialization, lift tables,
Cramer words, grid enumeration) remain open.

Independent review subagent `agy-reviewer-f29e46b2/detrows-review` (`2c67fe90`) reviewed head
`9bc03446` (Lean `72da75e2`) for correctness, attribution, API/style and the theorem index, and
approved with no findings. Coordinator `agy-coordinator-d55a006b`, with independent subagent
`32a1f222` (`DetRows M1 Reviewer`), requested changes at the same revision. The Theorem index PDF
run `39657509819` failed on the undefined `\lean` macro. The coordinator also asked for docstring,
proof and import cleanups and for re-pinned links. All items were fixed at head `0634a2b6` (Lean
`ccbd129b`). `2c67fe90` re-reviewed this revision, rechecked all seven links against the exact
lines, and approved with no findings. The coordinator re-reviewed and approved in [comment
6324535442](https://github.com/cslib-community/complexitylib/pull/281#issuecomment-6324535442). It
inspected artifact `theorem-index-3c417c14…-1` from fork run
[39660203891](https://github.com/SamuelSchlesinger/complexitylib2/actions/runs/39660203891) (source
`3c417c14`, PR head `0634a2b6`, base `9e161a05`, PDF SHA256 `6753da8b…`). It viewed rendered page 87
(Section 13.2) and checked that all seven link annotations point to `ccbd129b`. Backfilled on
2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human
editorial approval.

## 2026-10-21: Haken's pigeonhole lower bound for resolution (#271 / PR #279)

Worker `agy-worker-f29e46b2` (`agy-worker-f29e46b2/php-resolution`; Antigravity, Claude and
Gemini) adds the entry "Haken's pigeonhole lower bound for resolution" to
`paper/sections/proofs.tex` (section 7.4), with six declaration links pinned at `c9fdac89`. It
states satisfiability of PHP^m_n iff `m ≤ n`, the critical-pair bound `2n^2 ≤ 9|satPairs(c)|`,
`12^⌊n/3⌋ ≤ 11^⌊n/3⌋ s` for `n ≥ 8`, and `2^⌊n/24⌋ ≤ s` for every `n`, also for tree-like
derivations. Scope: the Beame–Pitassi argument rather than size–width, non-onto PHP without
hole-surjectivity clauses, and proof size rather than solver runtime.

Independent review subagent `agy-reviewer-f29e46b2/php-review` (`dfb49593`) reviewed `d8fe9cdb`
(Lean `c9fdac89`). It approved correctness, cslib API/style and the theorem index with no blocking
findings, and checked quantifiers, model, bounds, the non-onto scope note and all six links.
Coordinator `agy-coordinator-d55a006b` approved PR head `cd4a64dd` (Lean `c9fdac89`) in [comment
6323978217](https://github.com/cslib-community/complexitylib/pull/279#issuecomment-6323978217). It
cited API/style reviewer `a1dbdd38` and correctness/index reviewer `c7d73924`, both approving. CI
PDF: artifact `theorem-index-afb57fae…-1` from [run
39656060894](https://github.com/SamuelSchlesinger/complexitylib2/actions/runs/39656060894) (source
`afb57fae`, head `cd4a64dd`, base `028724cc`, PDF SHA256 `01fafb24…c16db6e9`). The coordinator
inspected page 73 and checked all six URI annotations against `c9fdac89`. Backfilled on 2026-10-22
by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI review, not human editorial
approval.

## 2026-10-21: Buss polynomial kernel for vertex cover (#270 / PR #277)

Worker `agy-worker-f29e46b2` / `agy-worker-f29e46b2/buss-kernel` (Antigravity agent, Claude and
Gemini) adds the entry "Buss's polynomial kernel for vertex cover" to
`paper/sections/completeness.tex`, with ten declaration links pinned at
`29c6c5e0ed7b97de51a4cb18276f3a2b72b07036` (`Parameterized/VertexCover/BussKernel.lean`), and
removes the Buss-kernel limitation from the existing "Kernelization and parameterized vertex cover"
entry. The prose states the exact-size cover encoding, the high-degree rule, active-vertex
relabelling and isolated-vertex padding, the fixed rejecting instance, the `k(k+2)`-vertex,
`(k(k+1))^2`-edge and `40(k+1)^6` bounds, and that crown and LP-based `O(k)`-vertex kernels are not
covered; the computable-`g` limitation remains in the existing kernelization entry.

Review subagent `agy-reviewer-f29e46b2/buss-review` (`9d8d595d`), separate from the authoring
worker, reviewed PR head `a437d35a` (Lean commit `29c6c5e0`) and approved correctness, cslib
API/style and the theorem index with no findings, checking quantifiers, encodings, bounds,
limitations and all ten link lines. Coordinator `agy-coordinator-d55a006b` approved the same
revision in [comment
6323614289](https://github.com/cslib-community/complexitylib/pull/277#issuecomment-6323614289), with
independent subagents `8f5ade95` (API/style, approve) and `df572301` (correctness and theorem index,
approve); no findings or fixes are recorded. CI: Lean Action CI run 39652686366 and Theorem index
PDF run 39652686110 (both in `SamuelSchlesinger/complexitylib2`) succeeded; artifact
`theorem-index-12a31b6cb1cd6618e3f7532631decede0e7411a3-1` reports PR head `a437d35a`,
`source_dirty: false` and PDF SHA256
`a7623eed13987a61cf913f06c2d023672ac154f314c7aeddf250dfda5cc644d2`. The coordinator inspected
rendered pages 8 and 99 and checked all ten URI annotations against declaration names and lines.
Backfilled on 2026-10-22 by `worker-jetski-89a6c8ae` from the PR record (#381); this records AI
review, not human editorial approval.

## 2026-10-21: Client resource contracts through interface refinements (#274)

Published source revision: `5d9eefc4f20726054a71df3539c2471f1c18712c`.
Its tree `61377bf7b2d7e0210250df65a78d50b604b8079b` exactly matches the locally validated
source `e4539513d61a349a849792061f2ef0fcf397aad2`; only commit metadata changed during publication.
Worker `worker-refinement-20261021`, assisted by OpenAI Codex, extends the existing Stateful
entry with client operation-cost contracts, initial-state-dependent budgets, adaptive sequencing,
method-budget composition, and transport to native execution evidence. The prose explicitly
requires a represented initial state satisfying the precondition. Existence of a finite execution
and bounds on every supplied finite execution remain distinct from demonic termination.
Pure controller computation, argument delivery, decoding and integration with `polytime`
machine certificates remain outside this milestone. No whole-machine runtime claim is added.

Independent source correctness review by `/root/ordered_fagin_recovery` approved the core and
adaptive example without findings. Independent API/tactic review by `/root/recovery_integration`
approved the core, four structural Aesop rules, final named axiom guards and a parametric
state-dependent cost example. The latter review also approved the changed index, roadmap and
upstream prose after making the represented-initial-state premise explicit. Reviewed core hash:
`5cc1a1b0bfd222877227dbf7d38fd403c332540b78f999ab03c2af7608866833`;
final test hash: `c18a26b2fb3f1fc1a6f9c5cec97284e2996b20cd3e4ac6016d4a4c4e0ceccc9a`.
The source commit matches these reviewed files. No author reviewed their own change.

Validation: complete actual-file MCP diagnostics and all six strict local gates passed in
session 38388 before the source commit. Tests exercise costs seven and two on distinct adaptive
branches, reject budget six, transport through two implementation layers, preserve hidden spare
storage in concrete executions, and charge the second operation at its updated state. Named
axiom guards and the global audit pass. Three new declaration links pin exact source lines.
Independent reviewer `/root/recovery_integration` approved the final local page 81 rendering
and all three PDF URI annotations against the committed declarations at lines 147, 164 and 108.
Final repinned PDF SHA256: `a3965808f84ed5b5f42d98f4a55f0c00b0fc898f8c7d6127db8c8f3d7ef6dafc`.
The reviewer repeated page/annotation checks after publication and verified the remote source
blob and all declaration lines against the local source. CI artifact provenance and coordinator
review remain required before integration. AI reviews do not imply human editorial approval or a formal proof of prose equivalence.


After main integrated the operation-basis and generic-RAM work at `c7d0d1da`, the owned PR
branch was refreshed. The only textual conflict joined these independent review records;
all four implementation/test files and the Stateful result prose remained byte-identical.
Independent reviewer `/root/recovery_integration` approved preservation of both parent records,
the combined PDF pages 82--83 and all three source pins on page 83. Combined PDF SHA256:
`73a514399409c9bb08145918945d9eb961645da3f1df373e8fc94b4d514f87fd`.
The refreshed tree's full validation and exact published head are recorded in PR #278.

## Configurable RAM value domains (#266), 21 October 2026

Reviewed Lean source: `8fc64c86ce21bb6876b08b50f4f14e21799be217`, tree
`51f961e802172cfc20346923cbfb3ae57a8be064`, on operation-basis prerequisite
`6532753dc17bd27793511246f4f12346c291ab61`. Bibliography is isolated in
`696eab2bae32f662ebe1be33df7cf7ddfb31dc83`.

Scope: `GenericRAM/{Defs,Signed,Algebraic}`, `WordRAM/Generic`, four focused test modules,
and the index entry “RAMs over configurable value domains” in `paper/sections/query.tex`.
The entry distinguishes configurable fault policies, exact execution/halting cost, the
WordRAM adapter on arbitrary states, and signed and tagged algebraic instance boundaries.
ROADMAP and UPSTREAM retain the open structured-calculus, cost-model and simulation work.

Independent AI reviews (OpenAI Codex, separate author/reviewer scopes):

- `recovery_integration` approved the core and WordRAM adapter API/correctness and their
  index prose; it did not approve its own signed-instance source. Its final local rendered
  review independently approved page 80 and all eight pinned annotations, with no findings,
  at the same PDF hash recorded below.
- `ordered_fagin_recovery` approved the signed/algebraic source and tests, and their index
  prose, without findings. It independently checked the root-authored Boolean test at
  SHA256 `24646e028af681540ea4d4d65fc951d773b301849cce64071a7a27b0796261aa`:
  nonnumeric values/addresses and configuration, observable memory use, exact six-step cost,
  and a failed-test fault. It did not approve its own core/adapter source.
- Final local rendered instance review by `ordered_fagin_recovery` approved page 80 of
  PDF SHA256 `fb04e36ac9483d95e1510fd128369fd18ec1fb0309630385a10f48366f4a5f7e`.
  The eight annotations all target the reviewed source commit and exact declaration lines
  (Defs 63/309/314, WordRAM/Generic 125/156, Signed 91, Algebraic 190/194).
  Signed/algebraic claims, ranges, formulas and citations are readable without clipping or
  overlap. The reviewer checked all eight link targets against committed local blobs.

This is local source/render review, not human editorial approval. At this checkpoint the
source commit is unpublished: remote link availability, final remote commit/tree parity,
CI, and independent inspection of the CI theorem-index artifact/provenance remain required
before integration. The original canonical six-gate run continues separately; no duplicate
validation run was started. Source credit remains in the modules and bibliography, including
lean-trominoes contributors / Erik Demaine and Erickson–van der Hoog–Miltzow.

## Word-RAM operation bases, 21 October 2026

Reviewed Lean revision: `72e92283` (code `291ff2f1`); review fixes in `2435c31e`, the revision named
in the index links.

Scope:
- `Complexity/Computability/WordRAM/{Basis,MapOp}.lean` (new), `Complexity/Computability/Circuit/SignatureHom.lean`
  (split from `Circuit/MapOp`), and the basis parameter throughout `Complexity/Computability/WordRAM`
  and `Complexity/Algorithms/WordRAM`
- `ComplexityTests/WordRAMBasis.lean`
- `paper/sections/query.tex` (`Word-RAM decision grows with the basis of operations`, new; `Element
  distinctness for entries below n on the word RAM` and the additive-simulation links, updated)

Independent AI reviews (read-only subagents, not the authoring session):
- cslib API review (`7689ca09-88e1-4103-914b-e663256fe8a9`) of `72e92283`: requested changes, none
  blocking. Resolved in `2435c31e` and the accompanying documentation commit: unaliased breaking changes recorded in
  `UPSTREAM.md`; `ram_eval` extended to `alu` instructions; `Op.rename_bin`, `Op.rename_width`,
  `Op.dest_bin`, `Op.dest_width`; `Signature.Hom` split so `WordRAM/Basis` no longer imports the formula
  library; docstring wording of `Basis.Hom`; dead variables and unused import removed; the
  `Instr.IsAdditive`/`Basis.additive` overlap recorded in `ROADMAP.md`. Not adopted: a `FunLike`
  instance and category lemmas for `Basis.Hom`, `mapOp` functoriality for `Instr`/`Code`, restoring
  `Repr` (recorded as removed).
- Correctness and theorem-index review (`3e173ba3-a738-46ac-9cd9-e421194913be`) of `72e92283`: approved
  with should-fix items. Verified that `Basis.standard` reproduces the previous `bin`/`width`
  semantics (width never faults), the `ReadsWidth` invariant and monotonicity, the named bases,
  satisfiability of `Basis.Hom`, `MapOp` transfer statements, and every declaration link. Resolved:
  the standard basis is described as Hagerup's operations together with division, remainder and the
  word size; the arithmetic basis is described as the source's operation symbols with truncated
  subtraction; `DecidableInTime.mapOp` linked; map-of-bases wording distinguishes the `ReadsWidth`
  marker from semantic width-independence.

Re-review of the fixes and inspection of the CI theorem-index PDF remain for the coordinator.

## Canonical full-tuple ordered interpretation transducers (#137), 20 October 2026

Reviewed Lean revision: `bf7afb0a2bb77c5b0c67a8a1b9e643763b312a60` (prerequisite shared output commit `97622143391f6777b14b832420787b5a79d7109d`).

Scope:
- `Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Output.lean`
- `Complexity/Logics/FirstOrder/Ordered/FullTuple/Encoding.lean`
- `Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Reduction.lean`
- `ComplexityTests/OrderedReduction.lean`
- `paper/sections/structure.tex` (`Canonical full-tuple ordered interpretations as logspace transducers`) and `ROADMAP.md`

Independent reviews:
- cslib API review (`14919544-d52b-40a4-aa1f-d7fa16f654b7` and `coordinator-ops-20261020`): **APPROVED**. Verified module paths, `Cslib.Logic.FO.Ordered.FullTupleInterpretation` namespace, naming conventions, shared `FirstOrder/Output.lean` factoring, docstrings, citations (`[Immerman1999]`), and proof hygiene.
- Mathematical correctness review (`0cdeb10e-3db3-44c3-81d1-6ef4f4507c85` and `coordinator-ops-20261020`): **APPROVED**. Verified `encodedMap`, `card_encodedMap`, `wellFormed_encodedMap_iff`, `two_le_card_encodedMap`, `table_encodedMap`, `length_encStructure_encodedMap`, `encodedModelEquiv`, `encodedModelEquiv_apply_val`, `computableInLogSpace_encodedMap`, `mem_queryLanguage_encodedMap_iff`, `logSpaceReducible_onSentence`, counter-program unpacking of `Fin (a.1 ^ k)` ranks into reversed base-`a.1` coordinates (`lexEquiv.symm`) while streaming tables in `tupleIndex` order, register/polynomial bounds, and non-vacuity/orientation tests in `ComplexityTests/OrderedReduction.lean`.
- Theorem-index review (`bbf779fa-0ff8-44cc-9a13-d5cbbbf120ba`): **APPROVED**. Verified all 10 `\declat{bf7afb0a2bb77c5b0c67a8a1b9e643763b312a60}` declaration links, mathematical statements, quantifiers, resource bounds, and scope limitations (`k > 0` for canonical target numerics, full-domain hypothesis, encoding-relative contract, and open class-level ordered reduction closure and projection completeness).

## Cook-Mertz Tree Evaluation, 19 October 2026

Integrated Lean revision: `aa72232abd8858a2c4103eb6aebc039e3b02f52d`.
Prose revision: `7531e6c1f87fd6e601a86a1574add35c1227eeb7`.
PR #1 head: `724d7be362770de480fcd609ca964760a4562694`.
Main base: `244c8208535f7263876b4f001674929b49ec8092`.

Samuel authorized fixing the review findings and merging Crei's PR. The integration
preserves Christian Reitwiessner's original commits, authorship and disclosed Claude
assistance. OpenAI Codex resolved conflicts, corrected documentation, relocated named
axiom guards, prepared the index entry and performed local validation. The mathematical
sources are Cook-Mertz (TR23-174/STOC 2024), Goldreich's exposition (TR24-109 revision 2),
and Cook et al.'s original Tree Evaluation problem (2012).

Independent read-only Codex reviews, including fresh review of corrections:

- `proof_api` approved integrated source `aa72232a`. All 49 captured scope files match
  the final reviewed hashes, and the merge parents match the intended revisions.
  The aggregate imports preserve both parents; the global axiom audit is byte-identical
  to main, and all eleven PR guards are preserved in the two topic tests. Corrected
  stale declaration names, the binary-sum bound description, and padded-log prose.
- `proof_correctness` approved algorithm correctness at `aa72232a`: finite-field sums,
  multilinear extension, recursive procedure, concrete reader, encoding, phase
  invariants and nonvacuity tests. All 23 captured Lean files match reviewed hashes.
  Corrected the subtraction signs in round descriptions, initialization/modulus
  wording and perfect-tree description. No mathematical statements or proofs changed.
- `resume_alternation` approved resource correctness at `aa72232a`: the space calculus,
  read-to-step simulation, compilation, state certificates, invariant, size bound and
  headline theorem. It checks a fixed machine across sizes, charged input addressing,
  work-space reuse and streaming output; the newer main interfaces retain the relevant
  contracts. Review did not separately re-audit every inherited arithmetic/plumbing
  helper. No resource-correctness blocker was found.
- `resume_alternation` approved exposition `7531e6c1` against `aa72232a`, and
  `proof_correctness` separately approved its algorithm/encoding portion. Review
  corrected 'full binary tree' to perfect tree/all leaves at depth H and made the
  exhaustive nonzero-field enumeration hypothesis explicit. Final pin replacement
  reproduces the previously approved prose hashes; all three anchors match source.

All reported findings are resolved. The unpublished vendored step-machine provenance
at `9cce4cc7` remains explicitly recorded in UPSTREAM.md. The code itself was reviewed
and validated; equality to that unavailable original source was not independently
verified. This is a provenance limitation, not an assertion of upstream acceptance.

Validation: all six gates passed in a fresh uninterrupted run after the final source
edits: `lake build --wfail --iofail`, `mk_all --check`, `lake test --wfail --iofail`,
`lint`, `lint-style`, and `checkInitImports`. An earlier run caught overlong corrected
comments and a missing build artifact while dependencies were being rebuilt; those
results were superseded by the clean complete run. MCP diagnostics were requested
but stayed partial during dependency preparation; the complete build/test run supplies
the compilation evidence. The concrete sample exercises a height-two XOR/AND tree
over ZMod 7, and all eleven named axiom guards plus the global audit pass.

The PDF has 32 pages, 75 numbered entries and 93 references. Every page was rendered
and inspected. After final source pin replacement, only page 1 changed visually; it
was reinspected, along with the new entry on page 7. All three new PDF URI targets
match the exact committed declaration lines. The final LaTeX log has no warnings or
underfull/overfull boxes; existing unrelated bibliography metadata warnings remain.
The index retains the valid-input restriction and outstanding input-length-only
corollary, refined parameter bound and malformed-input handling in ROADMAP.md.
AI review is not human editorial approval or a Lean proof of prose equivalence.

Final artifact hashes:

```
34088cd61ef8aa4b081e6c9d023530c6fe2cd2dc93ae3a60a77a3adcbce8e6c0  paper/main.tex
063f7351eacf00a30a162402ae67603549fff28d2fd659c21573985d9f4ffe2a  paper/sections/space.tex
b338bce9594c093dbccafa79458f3f37d836af0477a3336ef8a7d619973fa4d1  paper/main.pdf
```

## Counting containment and closure, 19 October 2026

Lean source revision: `c7feb301c4c55ecda7bc22ad1fc6ff1b6fe7d108`.
Prose revision: `5ad66c8052d9b7ebbd57e4b3e94d9bcb61c49216`.
Bibliography revision: `7ff74d38`.
Base: `7f62fb4da0b0cff19bb7478f1b4090bb35ee04cf`.

Samuel requested all four follow-ons and authorized review followed by direct merge
and push for this session, without a PR. OpenAI Codex implemented WPP containment
in AWPP (and its LWPP corollary), fixed AWPP amplification to error at most one
eighth and Boolean closure, arbitrary fixed positive SBP gap powers, and SBP
intersection with a BPP language. The development reuses verifier counting algebra,
polynomial-time arithmetic, dyadic padding and BPP amplification. It does not claim
counting-machine equivalence or uniform input-dependent AWPP amplification.

Independent read-only Codex reviews:

- `proof_api` approved source `c7feb301`, including bibliography parent `7ff74d38`.
  The reviewer suggested sharing repeated dyadic-witness construction through
  `GapP.two_pow_mem`; the helper and all three client replacements were added,
  MCP-checked and freshly reviewed. Existing AWPP theorem statements are unchanged,
  so their index text and earlier declaration pins need no rewrite. A source-credit
  wording question was resolved by checking Fenner's cubic amplification method.
  All eight committed blobs match the final reviewed hashes; no remaining findings.
- `proof_correctness` approved source `c7feb301`, including the bibliography,
  after checking signed non-dyadic WPP targets, the quadratic normalization,
  the three majority rounds and exponent factor 27, the strict SBP powers,
  and both rejecting cases for intersection with BPP. The helper delta received
  fresh review. All eight committed blobs match reviewed hashes; no findings.
- `resume_alternation` reviewed the new index entry, revised limitation paragraph,
  overview, README and roadmap against the final definitions and statements.
  Quantifiers, encoded models, bounds, limitations and source credit match Lean;
  all nine declaration anchors are checked. Approved prose `5ad66c80` against
  Lean `c7feb301`; committed prose matches the reviewed text after replacing
  provisional source pins. No findings.

Sources: Fenner--Fortnow--Kurtz--Li, *An Oracle Builder's Toolkit*, Section 6.1
for WPP containment; Fenner's AWPP amplification method; Watson Section 1.1 for
SBP gap strengthening. The prose separates classical results from the particular
normalization and fixed-round constructions implemented here.

All six gates passed after the final helper refactor: strict build and test with
`--wfail --iofail`, `mk_all --check`, `lint`, `lint-style`, and `checkInitImports`.
Tests include negative exponentially growing non-dyadic targets, variable dyadic
exponents, nonconstant Boolean clients, arbitrary fixed positive gap powers, and
an original zero-threshold SBP witness. Nine new headline axiom guards pass.

The rebuilt PDF has 31 pages, 74 numbered entries and 91 references. Every page
was rendered and visually inspected. After replacing the final revision pins,
only page 1 changed visually; it was reinspected, along with the new entry on
page 12. All nine new PDF URI targets match the committed declaration lines.
The final LaTeX log has no warnings or underfull/overfull boxes. Existing unrelated
bibliography metadata warnings remain. AI review is not human editorial approval,
a Lean proof of prose equivalence, or CSLib maintainer acceptance.

Final artifact hashes:

```
dd5b496a1b6ba403f867b55e6fc46e8638e61dbe945cbd769045de968ce5184c  paper/main.tex
a47302946108d4fe815784042949172548d2640fd0d8ae35be181e8f64c1ebce  paper/sections/randomness.tex
490582479d3848c4df8fd45a17312da04f69fa520af98291fef2c7fbb5464940  paper/main.pdf
```

## Approximate counting classes, 19 October 2026

Lean source revision: `e903aba8b29ef85b94c453114f12d604768587a5`.
Prose revision: `e525a9faba85e10464c35436b6414ee8a0dff382`.
Base: `ef189ec5b370c81cf4eb59ac9cbbfed41fa04a17`.

Samuel requested the next Zoo batch and authorized review followed by direct merge
and push for this session, without a PR. OpenAI Codex implemented SBP and AWPP on
the existing verifier-based #P/GapP algebra. The results include NP and BPP in SBP,
SPP and BPP in AWPP, both classes in PP, SBP union closure, AWPP complement closure,
and polynomial-time many-one reduction closure for both. Supporting results make
SBP thresholds positive without changing the class and pad input-dependent unary
AWPP exponents to length-polynomial dyadic denominators.

Independent read-only Codex reviews:

- `proof_api` approved source `e903aba8`, including the bibliography. Two import
  nits were resolved: the test driver was regenerated in sorted order, and proof
  dependencies were made private while public base-class and Reduction imports
  were retained. The revised imports received fresh review. No remaining findings.
- `proof_correctness` approved source `e903aba8`, checking the cited definitions,
  strict SBP threshold gap including zero, positive normalization, cross-product
  union construction, strict PP sign tests, AWPP complement and denominator
  padding under arbitrary polynomial-time reductions, and concrete witnesses.
  Final committed blobs were compared with the reviewed hashes; no findings.
- `resume_alternation` approved prose `e525a9fa` against source `e903aba8`, checking
  quantifiers, encoded models, bounds, source credit and unfinished endpoints.
  All 12 new declaration names and anchors match that committed source; no findings.

Literature credits are isolated in `cb98ce48`: Fenner's constant-error dyadic
AWPP characterization, Böhler–Glaßer–Meister's SBP introduction, and Watson
Definition 2 for the nonnegative FP threshold formulation. The containments and
closures in this batch are identified as elementary consequences of existing
counting algebra and BPP amplification. ROADMAP.md retains counting-machine
characterizations, MA/SBP/AM containments, AWPP amplification, further AWPP Boolean
closure, WPP containment and PP-lowness as unfinished work.

All six project gates passed on the final source: strict build and test with
`--wfail --iofail`, `mk_all --check`, `lint`, `lint-style` and `checkInitImports`.
An earlier run caught only the generated test-driver ordering; it was corrected
before the complete successful rerun. Concrete tests cover ratios 3/4 and 1/4,
exponentially large targets, length-changing reductions, zero thresholds and
positive no-instance counts. All 12 headline axiom guards pass.

The PDF has 30 pages, 73 numbered entries and 90 references. Every page was
rendered and visually inspected. After final pin replacement only page 1 changed
visually; it was reinspected, along with the new entry on page 11. All 12 new PDF
link targets agree with the committed declaration lines. The final LaTeX log has
no warnings or underfull/overfull boxes; unrelated bibliography metadata warnings
are unchanged. AI review is not human editorial approval, a Lean proof of prose
equivalence, or CSLib maintainer acceptance.

Final artifact hashes:

```
22f26e19775839d1d8ab0bac3d532d416dbd9f9ac1b1811b8800b2a37847c4a2  paper/main.tex
b2a44fc545945fa9db0bed59d6d98f4fe648e71d5194d6bf0379840633c3a84d  paper/sections/randomness.tex
5c1c29b8c5f03b8de847e8b914f94f74e0396a8c22fceaf72a43f69b27d2c773  paper/main.pdf
```

## Wide gaps and the Boolean hierarchy, 19 October 2026

Lean source revision: `814e76e29fa938afaed4e1bd5763fa490bc39ca9`.
Prose revision: `eeb1ffcffcff6e93d192966fb44f9ca91365bb82`.
Base: `aa916f216902f1975b4b3e3e62e896f1f7c38304`.

Samuel requested implementation of the next Zoo batch and authorized independent
review followed by direct integration into main for this session, without a PR.
The batch adds US, coDP, coModP, finite Boolean-hierarchy levels, WPP and LWPP.
A reusable bridge embeds binary-output polynomial-time natural functions into
#P and binary-output integer functions into GapP. Fixed-width binary counting and
decoding lemmas are shared with existing Kannan and graph-nonisomorphism proofs;
those earlier public statements are unchanged. The index adds two numbered entries
and contextual FP-to-counting, US and complementary-class results.

Independent Codex reviews:

- `proof_api` approved source `814e76e2` after checking all committed source,
  imports, tests and bibliography against reviewed hashes. One should-fix finding
  identified remaining duplicate binary decoding in Kannan. It was resolved by
  sharing the decoding bridge and retaining compatibility aliases; the fix received
  a fresh review. The final public Decoder/proof-only Nat.Binary import boundary
  was also reviewed. No outstanding findings.
- `proof_correctness` approved source `814e76e2`, checking exact threshold counts,
  binary output-size bounds, signed targets, unary length dependence, US no-instance
  multiplicity, the difference-hierarchy convention, reductions, prime-modulus
  equality and concrete clients. The helper refactor and import delta received
  fresh review. No findings.
- `resume_alternation` approved prose `eeb1ffcf` against source `814e76e2`, checking
  models, quantifiers, resource bounds, limitations, sources, counts and all 30 new
  declaration anchors. No findings. All independent reviews were read-only.

Sources: Fortnow Theorem 3.5 for the FP counting bridge; Blass–Gurevich for US;
Cai et al. for the Boolean hierarchy; Fenner–Fortnow–Kurtz and
Hemaspaandra et al. Definitions 2.4–2.5 for WPP/LWPP. Elementary algebraic
consequences are identified in the module and index text. Bibliography changes
are isolated in commit `f3822ac7`.

All six project gates passed on the final source: strict build and test with
`--wfail --iofail`, `mk_all --check`, `lint`, `lint-style` and `checkInitImports`.
A preceding validation caught two proof-search timeouts when binary arithmetic
was exposed publicly through the bit-string module. Narrowing the public import
to Decoder resolved both; no heartbeat limits were increased. Tests cover
nonconstant languages, negative exponentially large LWPP targets, nonidentity
reductions, US no-instances with two witnesses, composite moduli, hierarchy
levels and 21 headline axiom guards. No Lean changes followed the successful gates.

The rebuilt PDF has 29 pages, 72 numbered entries, 198 declaration links and
87 references. All pages were rendered and inspected. After pinning the final
source, the pages were rendered again: only page 1 changed visually, and it was
reinspected. All 30 new PDF link annotations match checked declaration lines at
`814e76e2`. The final LaTeX log has no warnings or underfull/overfull boxes.
Existing bibliography metadata warnings are unchanged. AI review does not imply
human editorial approval, a proof that prose and Lean are equivalent, or CSLib
maintainer acceptance. Machine characterizations, lowness, robustness and stronger
hierarchy endpoints remain explicitly outside the completed scope in ROADMAP.md.

Final artifact hashes:

~~~text
12265e1eadc49edc6364acdce8f4a850042b5f602e05fa4aa385987ff88c6069  paper/main.tex
d8468f4ccc67fbb9d1c44f2bd31c8b7b40b27a892e0946fd1b07741294a1ace6  paper/sections/randomness.tex
af80f3c844d4087d1ec54547f0e2b28e812bb0a3e25d77e35eef47ada0a3b22c  paper/sections/completeness.tex
aa827c0cf56e649c5e6134a6735afdae1466ff18d7f3491f9a67844000b74253  paper/README.md
7daead0487ea2a3a0f0431b3dc341999d177e4f942ff67f53b66e9a52ec31e7e  references.bib
6f696ce4d764dd9bf0971ebd0d55240675f24dcceedd8f74f8ac1b616dc2224e  paper/main.pdf
~~~

## Small counting classes, 19 October 2026

Lean source revision: `2f492c03c060ed95662dd942ef7feca1bebda7aa`.
Prose revision: `df6cfe340df963943fbea6039097290dbdad9d0a`.
Base: `c8a1b9a798a11ca775ad3bfa585ee6a51c462e88` (PR #8).

The batch adds SPP, FewP, fixed-modulus ModP, coUP and coCeqP. It reuses
SharpP/GapP arithmetic, exact-count polynomial-time precomposition, complement
and reduction APIs, and Mathlib's finite-field arithmetic. Boolean closure for
ModP is asserted only for prime moduli. Definitions use polynomial-time
verifiers; nondeterministic-machine characterizations remain outstanding.

Independent Codex reviews:

- `proof_api` approved final Lean revision `2f492c03`, reviewing the five class
  modules, aggregate imports, tests, placement, reuse and source credit. No findings.
- `proof_correctness` approved the same revision, checking definitions,
  containments, closures, reductions, encoded-input ambiguity bounds, prime-only
  modular closure, degenerate moduli and non-vacuous examples. No findings.
- `resume_alternation` approved prose `df6cfe34` against Lean `2f492c03`, checking
  quantifiers, models, bounds, limitations, sources and all 20 new anchors.
  No findings. All three independent reviews were read-only static reviews.

Fortnow's Counting Complexity supplies the SPP and modular classifications and
specified containments. The FewP acceptance convention is checked against
Borchert–Hemaspaandra–Rothe section 1, which credits Allender–Rubinstein.
Fenner–Fortnow–Kurtz and Papadimitriou–Zachos retain credit for their respective
counting frameworks. Module and index prose distinguish sourced results from
elementary algebraic deductions; new bibliography entries are in a focused commit.

All six project gates passed on final Lean revision `2f492c03`: build and test
with `--wfail --iofail`, `mk_all --check`, `lint`, `lint-style` and
`checkInitImports`. Tests include a nonconstant language, a two-witness FewP
verifier, reductions, zero/one modulus conventions, composite zero divisors,
prime-modulus closures and 21 headline axiom guards. No Lean changes followed.

The rebuilt index has 70 numbered entries, 168 declaration links, 84 references
and 27 pages. All 27 rendered pages were inspected; the changed pages were also
inspected individually. All 20 new PDF URL annotations were checked against exact
source-line anchors at the final Lean revision. The final LaTeX log has no
warnings or underfull/overfull boxes. Existing bibliography metadata warnings
are unchanged. These AI reviews do not imply human editorial approval,
machine-checked equivalence of prose and Lean, or upstream maintainer acceptance.

Final artifact hashes:

~~~text
7eedf39e298f8e6f204cd6ac76efacf6bb89a8a5c41bf35b4180821ed947a323  paper/main.tex
66e11001a9aba983c5c5bedf278d3adb66aed19d484109b56e4f1e74d8ac789f  paper/sections/randomness.tex
dd7d273f65bb7798bc812425fb1206eb6c72103be03e8ff9b2647d5777ef0f21  paper/README.md
b8db27a77b98f180b0466f414b25b097e70e622d3be0aeced7861c7f01894259  references.bib
51338c8c67bbe6e3634729fd88d48dd930eabd3a72ce93146ab2eca2d7056052  paper/main.pdf
~~~

## Basic classes and DP completeness, 19 October 2026

Lean source revision: `4f6bdaf35ebe60aec6d1063ae513ac342df13589`.
Prose revision: `683cfcf5c4ff8ff3b4be7a41ecd78b363e83495e`.
Base: `bd00a271e316dc6403b3ab075677855e64aca867`.

The batch adds exact-count polynomial-time precomposition for #P and GapP;
union/intersection closure for P, NP, coNP and parity-P; parity symmetric
difference; verifier-based UP; C=P as GapP zero sets; and generic product DP
completeness with SAT–UNSAT as a corollary. The index adds three numbered entries
and expands the counting-algebra entry. It now has 68 entries, 148 declaration
links, 80 references and 26 pages. The 17 new declaration links use the final
Lean revision above; existing source pins are preserved.

Independent Codex reviews:

- `proof_api` approved all new modules, modified APIs, placement, imports, source
  credit and tests at `8c12d2a9`, then verified the documentation-only correction
  and approved final Lean revision `4f6bdaf3`. No outstanding findings.
- `proof_correctness` checked counts, global uniqueness, integer zero sets,
  arbitrary-encoding reductions, generic product completeness and concrete
  clients. The single wording finding was resolved: DP's definition intersects
  languages; the text does not assert a separation from NP intersect coNP.
  Final source approval is `4f6bdaf3`.
- `resume_alternation` approved the changed exposition at `683cfcf5` against
  `4f6bdaf3`, including hypotheses, model boundaries, 68-entry count and all
  17 new anchors. No findings.

All six project gates passed on `8c12d2a9`: build and test with `--wfail --iofail`,
`mk_all --check`, `lint`, `lint-style` and `checkInitImports`. The sole subsequent
Lean-file change is the independently reviewed DP docstring correction; no
statement, proof or import changed. New tests include concrete empty/nonempty
languages, variable-length precomposition, exact false-padding counts, a
SAT–UNSAT yes-instance and no-instance, and 16 headline axiom guards.

The final PDF rebuilt successfully. Its final LaTeX log has no warnings or
underfull/overfull boxes. All 26 rendered pages were inspected; all 17 new URL
annotations were matched to their exact source-line anchors. Existing bibliography
metadata warnings (the authorless threshold-circuit draft and Fagin's empty
publisher field) are unchanged. These are AI reviews, not human editorial approval
or machine-checked equivalence of prose and Lean.

Final artifact hashes:

~~~text
61be9194dc2bcda4c3f697c978587a38fa7e7757691847851126e81531cdbc7f  paper/main.tex
6ca6b29f2ffb7d84ca507092b43eca6d2a44919ce1f3a6c6f5c6080470a6ae5f  paper/sections/completeness.tex
8ffff2a87360321cc8d1592e056a0ddaaa6b7b63eb079364120a5b25e88023e7  paper/sections/randomness.tex
7a6de32908b8bca83037998b38ce598207210a69f511e6599f847d161807081c  paper/README.md
244763cde8c1ebeffd5e98ed4d9b2422170cc1a320ecef13a82f13ac8697b252  paper/main.pdf
~~~

## Integration on main, 19 October 2026

Merged parents: 46deb511074655f6701ed712bb568b59f5e57d9d (main, including PR #7)
and 5c4046da (assorted results and the expanded index). Historical review snapshots
below retain the counts and source pins of their respective revisions.

The integrated index has 65 numbered entries in 14 subjects, 131 declaration
links, 79 references and 25 pages. It preserves the FO projection entry from
PR #7 and every assorted-results entry. The 128 existing links retain source pin
8d38f775; the three FO links retain source pin 811ad02a through an explicit
revision-parameterized link macro. No mathematical prose was changed by integration.

Independent integration reviews, in addition to the parent reviews recorded below:

- proof_api approved the exact union of parent modules, aggregate imports and
  all 258 bibliography entries.
- proof_correctness checked all 1,420 Lean files against both parents: every file
  preserves its parent content, except the sunflower docstring correction.
  Definitions, theorem statements and proofs are unchanged. The library driver
  has the exact union of 1,176 imports and the test driver 241 imports.
- resume_alternation approved the merged index wording and link macros, including
  the unchanged FO and Kolmogorov entries and all 12 structure-section anchors.
- The remaining sunflower wording nit from the earlier branch review is resolved:
  at each coordinate some pair agrees; the pair may depend on the coordinate.
  Both source reviewers approved that correction. There are no outstanding findings.

The integrated revision passed all six project validation gates. Its PDF rebuilt
without warnings or overfull/underfull boxes; all 25 rendered pages were inspected.
All 131 declaration names compiled with #check; source-line anchors were checked
against the exact pinned revisions, and all 131 URL targets were verified in
the PDF annotations. Both parent developments and their test coverage are preserved.

These are AI reviews, not human editorial approval or machine-checked prose equivalence.
The final staged content is bound by the SHA-256 hashes below; the merge commit
records the parent revisions, review scope and validation.

~~~text
5762a8e575c95bdf812bbc8ecc867e1959fa3697f41accc3a090388d3c9850b2  Complexity.lean
d80878c176965a01fb2c558bab54823f1d7a3f623b79aa4b03c67efb3520e48b  ComplexityTests.lean
57e13cff537bf692a027af78c04a449c75ac56a8faef80fd384694e4a7f2d6ac  references.bib
a61517a26173eb3bff639f3db3bb87a3867fb6c0477b470aec37d97a38ab2008  Complexity/Foundations/Combinatorics/Sunflower/LowerBound.lean
4e9e75ab5f94abaf7a835d36888d9d3bb2fcf5d7e9bd81fc0b462fb821333268  paper/main.tex
7dd4ac3dc18830f40443f4c2611f545dd610b6850182a4c9d6c38011fd5f397a  paper/README.md
16468eac86cec71de4bcc33dabc453d0fbfa715872d6068aacd4c237cb697e07  paper/sections/structure.tex
641633b3cc80ea3fa27fd0be67d6d647f9003fa815192fa0e4f04c16efebea42  paper/main.pdf
~~~

## Assorted results, 19 October 2026

Scope: documentation-only changes on top of 8d38f7753b6c651c3363a157c806d05794d6ea11
(the reviewed remote feat/assorted-results head). All declaration links now target
that exact Lean revision. The index has 65 numbered entries in 14 subjects,
128 declaration links and 78 references across 24 pages. The earlier 50-entry
review is preserved in paper/review.md at that base revision.

The 15 new entries cover plain Kolmogorov uncomputability, counting algebra and
PP, zero-randomness PCP, PRG-to-OWF implications, parity formula depth, deterministic
communication bounds, relevant coordinates, decision-tree Fourier bounds, spectral
expansion, four query-complexity topics including the superquadratic sensitivity
separation, and two finite combinatorial inequalities. Existing entries now include
exact-three-literal SAT, Yablonskii's parity formula bound and the all-encoding
P=NP implication for BPP. Supporting helpers and routine closure corollaries do not
each receive an entry. No unproved machine characterization or Circuit Value
completeness endpoint is asserted. Samuel retains editorial control.

### Independent AI correspondence reviews

The following Codex reviewers compared the changed prose with the final Lean
definitions and statements at 8d38f775, then approved the final section hashes
recorded below:

- proof_api: query.tex, combinatorics.tex, and the additions in analysis.tex.
  Checked sensitivity measures and quantifiers, monotone and threshold conventions,
  symmetric evasiveness, approximate-degree constants, Fourier normalization and
  zero-depth cases, finite-product and sunflower hypotheses, and rotation-map
  spectral norms. All 29 declaration anchors in these files were checked.
- proof_correctness: additions in structure.tex, randomness.tex,
  completeness.tex, and crypto.tex. Checked unbounded computable lower-bound
  quantifiers for plain complexity, all-encoding collapse, verifier-based counting
  classes, repeated literals in ExactThreeSAT, PCP model, and any-length preimages
  in one-wayness. All 38 declaration anchors in these files were checked.
- resume_alternation: changes in circuits.tex and communication.tex.
  Checked leaf/depth costs, constants and arity hypotheses, transcript-determined
  outputs, field characteristic, source credit and selection. All 30 declaration
  anchors in these files were checked.

Resolved findings: explicitly defined the threshold convention as accepting when
at least j bits are true; refreshed all declaration anchors to the pinned revision;
removed branch-relative wording from the SAT entry. All final changed entries
were approved. This is AI correspondence review, not a machine-checked equivalence
between prose and Lean, and does not imply human editorial approval.

### Validation

- The reviewed Lean revision passed all six project gates: strict build,
  mk_all --check, strict tests (including the global axiom audit), lint,
  lint-style and checkInitImports.
- This update changes only paper/; no Lean, dependency or bibliography files changed.
- latexmk -pdf -interaction=nonstopmode -halt-on-error -cd paper/main.tex
  passed with no warnings or overfull/underfull boxes.
- Rendered and visually inspected all 24 pages. After the final wording edit,
  page 2 was re-inspected and all other pages were verified pixel-identical.
- Verified all 128 fully qualified names by Lean #check, all source-line anchors
  against git show at the pinned revision, and every target URL in the final
  PDF annotations. All cited bibliography keys exist.
- Verified the entry/subject/reference counts and git diff --check.

### Related branch review

Independent API/correctness reviews covered the new sensitivity-separation port,
class/problem changes, Boolean/query/formula/communication developments; the main
review additionally checked the cryptographic, Kolmogorov and combinatorial modules.
No concrete mathematical/API blocker was found. The large port received selected
internal-proof inspection and source comparison, not an independent rederivation
of every copied combinatorial argument.

One low-severity source-docstring issue remains outside this documentation-only
change: Complexity/Foundations/Combinatorics/Sunflower/LowerBound.lean:114
says two petals agree at every coordinate. The pigeonhole step instead chooses
a possibly different agreeing pair at each coordinate. The Lean proof uses the
correct quantifier order. The index states the result without that ambiguity.

## Reviewed SHA-256 hashes

~~~text
00d2a008377abc936f303a83391b2080804bbc71613658913577bdfe4d83933c  paper/main.tex
f00d2ad4e89ce0ba2d50cb66f2e32ae3ed43c3d477458ab6e32e7b4cd90f2eb1  paper/README.md
6a05f77e2a8f1f73bc1f2305c54897a9284bcdc44facfd487f1686fc583479e2  paper/sections/analysis.tex
837e513e2bf2bb09b9e2e4121edf893072903ab4974f4e4e70d6dfd926e799ac  paper/sections/circuits.tex
32edc7e3310bffccb3cb6e8485b3f2a72de89a67dbeacbcd2a25511b6e184ba2  paper/sections/coding.tex
cbcd26c55ddc7c74394ba75cf3fbd8b88f32b158838820082486ab41c8423d2c  paper/sections/combinatorics.tex
d0452458f1ed181c52822b3e1f92db68bd3d685bb75f17ffa2491897641fc406  paper/sections/communication.tex
b482320f18f507629992bdfff4c03a1ce518ba93e566d98a5c8b288c68458ccc  paper/sections/completeness.tex
b93a982fd1dddbb7ba8c2ee01f1f83468c41525f6a46d390a5b9d3822512c175  paper/sections/crypto.tex
bd7eb9e9d9744b5f5cec6f18135b0a0f92dd6a30878be7ed3c462c03cdc9df2f  paper/sections/iteration.tex
541179288b86a3e5f99131f7c6bebffcb8a82af4838e91ca81fcbf25432f1216  paper/sections/proofs.tex
13ed92486e4347bb53115f8e0b0d38953860b8bad7644f4d17e19d3da1b90cc0  paper/sections/query.tex
399a336e826579f674f5c0780d576aef74fd749eef559d217d3397351f6e0093  paper/sections/randomness.tex
c4bd382d2f113b65e127e48d362c431e60149f4b1fba3a883250dde5bae539e4  paper/sections/space.tex
8df69e5af6433f4926c72f43872e7734c34306f9b5c23de2080966533436dd70  paper/sections/statements.tex
af07d8884873f80bb4f86c31b3c05835be9331477335b1f4476030c1c459fbdc  paper/sections/structure.tex
cbb8084fa13318bb9b3408d76e042bd49d3c37d326447d71a036b810250b08b1  paper/sections/synthesis.tex
~~~


## First-order projection core (19 October 2026)

Lean revision: `811ad02abdab6bc2b9f945d58d2a1ff2ed1c282b`.
The new supporting entry in the logic section records the generalized, relativized
projection core. The 50 numbered entries and their selection are unchanged.
All declaration links are now pinned to this Lean revision.

Independent Codex reviews of the exact committed Lean revision:

- `proof_api`: API, placement, reuse, documentation and regression tests; approved.
- `proof_correctness`: numeric/input separation, quantifier order, disjoint cases,
  substitution, composition isomorphisms, QF assumptions and nonvacuity; approved.
- `resume_alternation`: changed statement-index prose, quantifiers, models, premises,
  scope limitations, three exact declaration anchors and mathematical credit; approved.

Resolved findings: cite Immerman and Landau directly for their projection and BIT
conventions; restrict the graph client's numeric-preservation wording to relational
languages; clarify the warning about arbitrary quantifier-free formulas. The strict
axiom reports use explicit expected-message guards. Fixes received fresh review.
No outstanding review finding remains. These are AI reviews, not human editorial
approval or machine-checked equivalence of prose and Lean.

Validation:

- All six project gates passed. Strict tests also passed after the final formatting
  of the nine axiom guards. The guards report only the permitted standard axioms.
- The upstream synchronization check reported CURRENT for the CSLib pin and every
  copied dependency revision.
- The PDF build passed with no warnings or overfull/underfull boxes. Rendered and
  visually inspected all 19 final pages, including the new entry and references.
- Verified all 81 fully qualified declaration names against the compiled library,
  every declaration-line anchor at the pinned commit, and all 81 URLs in the PDF.
  Sources for the 78 preexisting links are byte-identical to their prior pinned
  revision. The three new links point to the exact new declarations.
- Verified 50 numbered entries, 12 subject sections, 62 references, and `git diff --check`.

Reviewed source and rendered-output SHA-256:

```text
1226466dcca87b814b9f3a2e598ce927fd0649bf377a20f6f0e73b85dda20abc  paper/main.tex
8e1fd8ee11cdb4846d53af4e667b2e9a5142cc5c14c5ae2495bc52284415b67a  paper/README.md
b3aadb3e3a3e6199be6ac1452ffcc24b770062eff2db499cf6aa481d7271739b  paper/sections/structure.tex
fb18b863ba3cee9dc5a0e6686d24d7f3028073cfc0ac3534980987a617e4cb77  references.bib
cea453e9e2b3b390fa62131e49e6ac2498a8598a019b49806cf497d137bb3cd6  paper/main.pdf
```

## Coverage batch 1: Arthur–Merlin classes and ETH lower bounds (2026-10-19)

Integrated `fbd9aed2` (Arthur–Merlin milestone 1) and `b6f69ede` (ETH lower bounds for graph
problems) into `main`, adding the entries "Arthur--Merlin classes" (`randomness.tex`) and
"Exponential lower bounds for graph problems under ETH" (`completeness.tex`), and updating the
SBP entry's outstanding list to SBP ⊆ AM only.

Independent reviews of the exact commits, against their merge base `0c1dab07`:

- Correctness review (statements, definitions against Babai 1985, Arora–Barak §8.2, Cygan et al.
  Ch. 14 and Impagliazzo–Paturi–Zane; nonvacuity probes; axiom audits; paper drafts): APPROVE for
  both, no blocking findings. Resolved wording findings: the ETH entry now gives a separate δ for
  each problem and says the diamond reduction can have size up to Θ(m²).
- API review (conventions, placement, duplication, bibliography): APPROVE for both. Non-blocking
  placement and duplication findings (BitString helpers, private list lemmas) were returned to the
  authors as follow-up commits.

Validation: all six gates passed on the integration revision; the PDF builds with no undefined
references, and the two new entries were rendered and inspected. These are AI reviews, not human
editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 2: sharp Håstad bound and parity outside FO (2026-10-19)

Integrated `fa8e0065` (`ac0-sharp`), adding the entries "Håstad's theorem with the sharp
exponent" and "Parity is not first-order definable" (`circuits.tex`), and pointing the existing
random-restriction entry to the sharp exponent.

Independent reviews of the exact commit against `0c1dab07`:

- Correctness review (depth convention, constants, comparison with Hastad.lean, TopDown.lean and
  ShallowSymmetric.lean, nondegeneracy of the FO[Arb] statement): the Lean is approved. Blocking
  finding in the paper draft, resolved here: only the base bound, not every derived form, is
  stated for negation-counting depth and for formulas. Also noted that constants are nullary
  AND/OR gates.
- API review: APPROVE; non-blocking duplication and helper-placement findings were returned to
  the author as follow-up commits.

Validation: all six gates passed on the integration revision; the PDF builds with no undefined
references. These are AI reviews, not human editorial approval or machine-checked equivalence of
prose and Lean.

## Coverage batch 3: counting completeness and Reingold's combinatorial core (2026-10-19)

Integrated `74a300c2` (`counting-completeness`) and `cb631cc9` (`reingold` milestone 1), adding
"Parsimonious Cook--Levin and complete counting problems" (`completeness.tex`) and "Undirected
connectivity by short walks in Reingold's graph" (`space.tex`).

Independent reviews of the exact commits against `0c1dab07`:

- Correctness review: APPROVE for counting completeness (exact model counts against `acceptCount`,
  unchanged satisfiability statements, class definitions used as-is, standard Karp completeness).
  For Reingold the Lean is approved (the iff is not trivialized; the base expander is instantiated);
  the paper draft's description of Reingold's eighth power and of the start vertex was corrected
  here.
- API review: APPROVE for both; non-blocking duplication, placement and naming findings were
  returned to the authors as follow-up commits. Recorded API change: `CookLevin.eval_tableau`
  gains the `uniqueClauses` conjunct.

Validation: all six gates passed on the integration revision; the PDF builds with no undefined
references. These are AI reviews, not human editorial approval or machine-checked equivalence of
prose and Lean.

## Coverage batch 4: KKL and Friedgut, the QBF protocol, and randomized disjointness (2026-10-19)

Integrated `f355a73f` (`kkl-friedgut`), `b18f4389` (`ip-pspace` milestone 1) and `aba42b50`
(`disjointness` milestone 1), adding "The Kahn--Kalai--Linial theorem and Talagrand's inequality"
and "Friedgut's junta theorem" (`analysis.tex`), "The algebraic protocol for quantified Boolean
formulas" (`space.tex`) and "Randomized communication complexity of disjointness"
(`communication.tex`).

Independent reviews of the exact commits against `0c1dab07`:

- Correctness review: APPROVE for all three (standard influence and variance definitions; Lean's
  log and division conventions do not trivialize the statements; the prover model quantifies over
  all stateful, adaptive, randomized strategies with no information leak; the corruption lemma and
  amplification constants were recomputed). Wording findings resolved in the entries: Friedgut's
  witness description is marked as the proof's, zero-influence terms are read as zero, round degree
  and formula size are defined, the verifier is described as Shamir--Shen-style, and the
  disjointness caveat now states how the distribution differs from Razborov's.
- API review: APPROVE for all three; non-blocking duplication and placement findings were returned to
  the authors. The fourth epic in this review batch (Tseitin) has one required fix outstanding and is
  not integrated.

Validation: all six gates passed on the integration revision; the PDF builds with no errors or
undefined references. These are AI reviews, not human editorial approval or machine-checked
equivalence of prose and Lean.

## Coverage batch 5: one-way function consequences and Kabanets–Cai (2026-10-19)

Integrated `ad94a1a8` (`owf-metacomplexity`), adding "One-way functions separate P and BPP from NP"
and "Kabanets--Cai: MCSP in BPP rules out one-way functions" (`crypto.tex`).

Independent correctness and API reviews of the exact commit against `0c1dab07`: APPROVE on both
(library OWF, PRF, BPP and MCSP definitions untouched; the MCSP hypothesis is full membership in
BPP; the distinguisher is a genuine oracle-PPT adversary; the circuit bound is uniform in the key;
the advantage bound and BPP inverter were checked). Wording findings resolved in the entries: the
threshold remark now states that the hypothesis covers all thresholds, sizes are "at most", and the
error parameter's length L is defined. Non-blocking API findings were returned to the author.

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 6: uniform learning, LMN and Kushilevitz–Mansour (2026-10-19)

Integrated the `fourier-learning` branch through `f2ede479`, adding "The Linial--Mansour--Nisan
low-degree learning algorithm" and "The Kushilevitz--Mansour algorithm with membership queries"
(`analysis.tex`), and pointing the decision-tree spectral entry to the new learning entry.

Independent reviews: milestone 1 (`52857f33`) correctness APPROVE; its API review required
building on CSLib's `PACLearning` types, resolved in `b989a609`. Correctness and API reviews of
`52857f33..f2ede479`: APPROVE (KM error bound, threshold and union bound recomputed; query model is
standard membership queries; restructure leaves the low-degree statements unchanged; the bridge is
CSLib's PAC event). Wording findings resolved in the entries: O'Donnell's bucket notation, PAC
parameters in (0,1), and the informal polynomial reading of the query count.

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 7: linear Hamiltonian reductions and ETH (2026-10-19)

Integrated `bb828997` (on top of the integrated `b6f69ede`) and replaced the ETH entry in
`completeness.tex` to cover directed and undirected Hamiltonian cycle and path.

Independent correctness and API reviews of `b6f69ede..bb828997`: APPROVE on both (diamond theorem's
side conditions are non-vacuous and match Sipser's geometry; the sparse reduction is correct in
both directions; size bounds re-derived; the Directed.lean refactor keeps every public statement).
Wording finding resolved in the entry: the bound (23k+1)m+1 is for the directed path graph only;
the cycle and undirected graphs have their own linear bounds. Non-blocking API findings were
returned to the author.

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 8: Arthur–Merlin protocols, Tseitin, and cleanups (2026-10-19)

Integrated `090dc682` (Arthur–Merlin milestone 2: set lower bound, SBP ⊆ AM, GNI ∈ AM,
Boppana–Håstad–Zachos and the graph-isomorphism corollary), `38abf7bf` (Tseitin formulas are hard
for resolution), and the reviewed cleanup ranges `fa8e0065..b4f8337a` (sharp Håstad),
`74a300c2..8d8e8516` (counting completeness) and `f355a73f..813d8f38` (KKL and Friedgut). The
Arthur–Merlin entry is replaced, a Tseitin entry is added to `proofs.tex`, the SBP and private-coin
GNI entries are updated, and the counting entry gains its modular and exact counting sources.

Independent reviews: Arthur–Merlin milestone 2 correctness and API APPROVE (set lower bound
arithmetic, GNI counts and the BHZ argument checked; the all-encodings hypothesis follows from
coNP ⊆ AM for bit-string languages); Tseitin correctness and API first required an explicit
threshold in the headline, and the delta review approved the fix and the restructure; the three
cleanup ranges were approved by a delta review (statements unchanged, deprecated aliases correct).
Entry wording follows the reviewers' notes (encoding of the GI corollary, connectivity and
unnormalized edge expansion in the Tseitin bounds).

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 9: monotone depth of bipartite matching (2026-10-19)

Integrated `85a17075` (disjointness milestone 2 and milestone-1 cleanups), adding "Monotone depth of
bipartite perfect matching" (`communication.tex`). Existing disjointness links stay pinned to
`aba42b50`, where they resolve.

Independent correctness and API reviews of `aba42b50..85a17075`: APPROVE (matching function, KW
game, gadgets, symmetry argument and constants checked; milestone-1 headline statements unchanged
under the renames). The entry states the bipartite scope and the intermediate reduction, as the
reviewer suggested. Non-blocking findings were returned to the author.

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 10: class collapses and counting containments (2026-10-19)

Integrated `38bfe757` (`class-corollaries`), adding "SAT in BPP collapses the hierarchy"
(`structure.tex`) and "Toda's theorem with a PP oracle", "Easy oracles and the Valiant--Vazirani
collapse" and "FewP is in SPP" (`randomness.tex`), and pointing the bounded-ambiguity entry to the
FewP containment.

Independent correctness and API reviews of `f91c5eda`: the Lean was approved (P^PP is the standard
class; the binary search, oracle lowness, PromiseP hypothesis and FewP gap function were checked);
two blocking documentation findings: FewP ⊆ SPP was credited to the wrong papers and a docstring
claimed an equality where an inclusion was proved. The delta review of `f91c5eda..38bfe757`
approved both fixes (Köbler–Schöning–Toda–Torán 1992 verified against Crossref; the equality is now
proved) and the non-blocking follow-ups.

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 11: gap hardness, Generalized Geography, and cleanups (2026-10-19)

Integrated the `gap-graphs-geography` branch through `a385efa7`, adding "Constant gaps for
Independent Set, Clique and Vertex Cover" (`completeness.tex`) and "Generalized Geography is
PSPACE-complete" (`space.tex`), and the reviewed cleanup ranges `bb828997..26cf1dc6` (ETH
Hamiltonian) and `f2ede479..d1c9ea21` (learning). The two learning links whose declarations were
renamed are repinned to `d1c9ea21`.

Independent reviews of `f775b563`: correctness found the Lean correct but required citation fixes
(Sipser 3rd ed. Theorem 8.14 for Geography; the vertex game is due to Lichtenstein–Sipser, the arc
game to Schaefer); API approved. Delta review of `f775b563..a385efa7`: APPROVE. The two cleanup
ranges were approved by the same delta review (statements unchanged; removed names unused).

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 12: IP = PSPACE and USTCON ∈ L (2026-10-19)

Integrated `3fd63a13` (`ip-pspace` milestone 2 and fixes) and `dec8b239` (`reingold` milestone 2 and
fixes), adding "Interactive proofs capture polynomial space" and "Undirected connectivity is in
logarithmic space" (`space.tex`) and correcting the three sentences that said these results were not
yet formalized.

Independent reviews:
- IP = PSPACE: correctness and API reviews of `b18f4389..53ea22c0` approved the mathematics (IP
  definition unchanged, simulation covers every word prover, soundness constant, closedness, full
  polynomial-time certificate) and required four mechanical fixes. The delta review of the fixes
  approved the API and found two docstrings stating theorems without one hypothesis each; those
  were corrected by the coordinator in the integration follow-up, with the exact wording the
  reviewer gave, together with deprecated theorems for two removed primality lemmas.
- USTCON ∈ L: correctness and API reviews of `cb631cc9..9d7510ce` approved (L unchanged; correctness
  on encoded instances only, as for every problem in L; space bound O(log m) with a closed constant;
  in-place evaluation equals the rotation map; parameters correct). The delta review of the alias and
  docstring round approved; the coordinator replaced two deprecation hints that suggested a
  replacement with a different meaning.

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 13: first-order reduction automation (2026-10-19)

Integrated `d22fe934` (`fo-automation`), adding "Quantifier-free reductions and their automation"
(`structure.tex`). The stated entry count was corrected to the number of entries in the index (110);
earlier increments had drifted below it.

Independent reviews: correctness and API reviews of `e624edf0..6682dade` found one blocking defect
(`fo_reduction` swallowed elaboration errors in its lemma list under `try`) and API items (module
placement, `IsoClosed.of_forall_imp`, composite support in `fo_simp`). The delta review of
`6682dade..d22fe934` approved; its non-blocking findings (composite and higher-dimensional
relations not simplified by `fo_reduction`, a broad failure message, test precision) are recorded in
`ROADMAP.md` or left for follow-up.

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 14: worst-case hardness, the alias sweep and FO model checking in L (2026-10-19)

Integrated `8cfc8e81` (`stv`), `b1293417` (`standards-sweep`) and `a1c2cb1d` (`fo-logspace`
milestone 1), adding "Derandomization from worst-case hardness" (`randomness.tex`, with the
preceding entry's closing sentence updated) and "First-order model checking in logarithmic space"
(`structure.tex`). The sweep has no paper impact; its grandfathered changes are listed in
`UPSTREAM.md`.

Independent reviews:
- Worst-case hardness: correctness and API reviews of the milestone-1 range (fixes reviewed), then
  of `6477f06f` (milestone-1 fixes and milestone 2): APPROVE. Correctness confirmed the headline is
  the Impagliazzo–Wigderson theorem for eventual hardness in cslib's De Morgan model with
  E = DTIME(2^O(n)) on bit words, that the field arithmetic and the encoding in E are proved
  rather than computed, and that the schedule constants match. The delta review of the API cleanup
  `6477f06f..8cfc8e81` approved; headline statements are unchanged apart from namespace.
- Alias sweep: the delta review of `2110aa5a..6d1941cf` required one fix (a deprecated `abbrev`
  so that instances resolve on the old type name) and recommended the missed aliases; the delta
  review of `6d1941cf..b1293417` approved, checking each old statement against `@Old.Name`.
- FO model checking in L: correctness and API reviews of `fd3cf84a`, then delta reviews of
  `fd3cf84a..ad887c0f` and `ad887c0f..a1c2cb1d`: APPROVE. The entry states that order, BIT and
  constants are not covered.

Validation: all six gates passed on the integration revision; the PDF builds without errors. These
are AI reviews, not human editorial approval or machine-checked equivalence of prose and Lean.

## Coverage batch 15: order-free SAT and graph reductions (2026-10-20)

Integrated `ac6116f6efabc191a18554a8e063b162e46a7c11` in merge `10d93bb4`.
The new entry states the order-free model, the hypothesis containing every empty structure
(including different nullary valuations), the nonempty corollary, and the singleton obstruction
for SAT-to-independent-set. It does not claim the standard ordered completeness endpoints.

Independent Claude correctness/API reviews covered `de4d64bb..543b3522` and milestone 2
`543b3522..03d0253b`; the first fix delta through `6d76bedb` required further wording fixes.
The implementation worker resolved the findings at `ac6116f6`: source attribution and terminology,
nonexistent reference, missing impossibility theorem, generic helper placement, redundant
hypotheses, restored main Coloring theorem interfaces, and nonvacuous tests. Samuel authorized
Codex review and merge on 2026-10-20. The Codex coordinator's correctness/API review of
`6d76bedb..ac6116f6` approved, with only grammar/spacing nits deferred. A separate Codex reviewer
approved the entry against the exact source and all sixteen links; its suggested precision about
simplicity being guaranteed on yes-instances was adopted.

All six integration gates passed on `10d93bb48b5bf1749ecc3ac33bef218de9896a98`.
AI assistance: Claude for earlier development/reviews, Codex for fixes, final reviews and index.
Source credit remains in the modules and bibliography. These are AI reviews, not human editorial
approval or a machine-checked equivalence between prose and Lean.

The PDF built successfully without undefined references or overflow warnings; the changed page
was rendered and visually checked. The index now contains 113 entries.

## Coverage batch 16: Circuit Value P-completeness (2026-10-20)

Integrated `dcbc89d8316f3f53f4a77bdb188061d8618a0716` in merge `7a6434e3`.
The replacement Circuit Value entry states logspace many-one completeness, encoded-instance
correctness, the logarithmic work-space model, the polynomial tableau clock and exact accepting
output. The projection-infrastructure entry now correctly leaves first-order-projection
completeness outstanding. The index still contains 113 entries.

Independent Claude correctness/API reviews approved `f42fb5cb` after the original milestone.
The implementation worker addressed the remaining nits at `dcbc89d8`: reused the canonical
`doubled` encoding, shared arithmetic and list/evaluation API, reduced writer exposure, and
clarified vendored provenance. Independent Codex correctness/API and paper review of
`f42fb5cb..dcbc89d8` approved with no findings, verifying all eight pinned links and unchanged
main-public interfaces. Samuel authorized Codex review and merge on 2026-10-20.

All six integration gates passed on `7a6434e32ef22a01e990f0d776a858a755257618`.
AI assistance: Claude for earlier development/reviews, Codex for cleanup, final review and index.
Mathematical credit remains with Ladner and the cited sources. These are AI reviews, not human
editorial approval or a machine-checked equivalence between prose and Lean.

The PDF built without undefined references or overflow warnings; the changed page was rendered
and visually checked.

## Coverage batch 17: order-free interpretations in logspace (2026-10-20)

Integrated `ec952980ee9ce16d14771a8738e13219dca27c81` in merge `045e147a`.
The new entry states the finite relational model, target isomorphism closure, fixed structure
encoding, L/P closure, and empty-domain, nullary and dimension-zero coverage. Invalid parsed
structure shape is distinguished from arbitrary strings outside the encoding image. The previous
model-checking entry now points to this bridge. Standard ordered FO results remain outstanding.

Independent Claude full correctness/API reviews of `dc33e6e6..df5c5c18` approved the mathematics
and requested explicit order-free terminology. The fix round `df5c5c18..ec952980` also reused
Mathlib counting/enumeration, moved the semantic map and tuple equivalence to the logic layer,
and added a concrete restricted two-dimensional interpretation and non-identity reduction client.
Independent Codex correctness/API/paper delta review approved with no findings and checked all
four links. A further Codex merge-delta check approved `045e147a`: source/test files are unchanged
from the reviewed head, and both drivers are sorted unions. The sole merge conflict was the
generated import index, resolved with `lake exe mk_all`.

An attempted gate run before index resolution failed; after the merge was completed, all six
gates passed on `045e147aa2ac963289816e071e8b14d24a972c72`.
AI assistance: Claude for the earlier WIP/reviews, Codex for completion, fixes, final reviews and
index. Source credit remains recorded. These are AI reviews, not human editorial approval or a
machine-checked equivalence between prose and Lean. The index now contains 114 entries.

The PDF built without undefined references or overflow warnings; both affected entries were
rendered together and visually checked.

## Coverage batch 18: Monotone Circuit Value P-completeness (2026-10-20)

Integrated `a060a8434ffb243af65ccad54a30b3a663ce9a07` in merge `a6f23928`.
The new entry states logarithmic-space many-one completeness for AND/OR circuits with
constants, explicit input assignments and one output. It records the dual-rail gate count,
the shared streaming writer, and the absence of a planarity restriction. The preceding
Circuit Value entry now points to this result. The index contains 115 entries.

Independent Codex correctness/API/paper review of `dcbc89d8..bd019669` approved the
mathematics and paper, requesting two API/style fixes: make a generic implementation
helper private and use `simp only` in a non-terminal simplification. The delta review of
`bd019669..a060a843` approved all three scopes with no findings. It explicitly approved
the mechanical repinning of all six declaration links; their lines were verified against
the reviewed revision. The shared writer preserves existing Circuit Value endpoints.

All six integration gates passed on `a6f2392875e85b32eec060c0bf6dac522347e4f0`.
AI assistance: Claude for the earlier WIP, Codex for completion, fixes, independent reviews
and index, as authorized by Samuel on 2026-10-20. Goldschlager's mathematical source credit
is retained; its bibliographic DOI was verified. These are AI reviews, not human editorial
approval or a machine-checked equivalence between prose and Lean.

The PDF built without undefined references or overflow warnings; the changed page was
rendered and visually checked.

## Batch 19: halting space deciders, fine mass production and defect fixes (2026-10-20)

Integrated at Samuel's request before review: `495e5ea6`/`cd8ba181` (merge `6c90880b`), which make
`Turing.MultiTapeNTM.DecidesInSpace` require every branch to halt so that `NL` and `NPSPACE`
follow Sipser's Definition 8.1, keep the former predicate as `RecognizesInSpace`, and generalize
`NL ⊆ P` and Savitch to recognizers; and `2357cdd8`/`4cde4948` (merge `8fc0cf63`), which rename
"sharp" mass production to "fine", since no matching lower bound exists for γ > 0. The NL and
Savitch entries (`space.tex`) and the mass-production entry (`synthesis.tex`) changed; the index
still contains 115 entries.

Independent Jetski (Gemini) reviews, run after integration:
- Space deciders, correctness/API/paper review of `41ba45c1..cd8ba181`: request changes,
  documentation only. Blocking: the claim that a per-instance step bound is equivalent to every
  branch halting holds only for machines with finitely many states (König), not for the general
  definition. Non-blocking: "no stronger" overclaimed for logspace recognizers; ROADMAP wording;
  a genuinely branching decider test; named projections instead of `.1`; the in-place
  strengthening of `DecidesInSpace` accepted as a literature-matching fix, to be recorded as a
  breaking change; the paper should state the formal convention and stuck paths. All addressed in
  `c4bd6312` and this commit; the breaking change is listed in `UPSTREAM.md`.
- Fine renaming, rename/API/correctness/paper review of `41ba45c1..4cde4948`: approve after one
  fix. Blocking: the paper said the coefficient is optimal *only* at γ = 0, implying
  non-optimality for γ > 0; now "optimal at γ = 0 … no matching lower bound is claimed", with
  Shannon credited. The γ = 0 claim was checked for this cost model (bounded fan-in, constants
  free, `massComplexity_mono` for k ≥ 1). Non-blocking: deprecated field notation (now deprecated
  theorems on the old type), attribution via Jukna Theorem 1.14, the constant of `MassProducesAt`,
  section headings, and module stubs. Following the review, no `deprecated_module` stubs are kept
  (they would have no upstream counterpart); the renamed modules are listed in `UPSTREAM.md`.
  Addressed in `1c295e0f` and this commit. The pin list in `main.tex` now names renamed or changed
  declarations.

Defect fixes in the same batch: `9a8dc0a8` repins three USTCON links at `dec8b239` from docstring
starts or an `open … in` line to their theorem lines, after all 419 links were checked against their pinned revisions;
`7a61e7be` makes the frontier multigraph share `Cslib.Multigraph.toSimpleGraph` and proves the edge
cuts agree; `72747d26` removes an unwarranted "sharp" in Nechiporuk's lemma and a stale FIXME.

All six gates passed on `1c295e0f`. The PDF builds without undefined references; the changed
pages were rendered and inspected.

Follow-up rounds: an independent delta review of `6c90880b..a52ff443` approved with nits (all
addressed in `a2d52d3f`: a `toSimpleGraph_eq` bridge and `edgeSet_toSimpleGraph`, an
`UPSTREAM.md` bullet on the two multigraph namespaces, a test of deprecated field notation with an
explicit argument, the scope of cslib's `Shannon.lt_complexity`, the Jukna citation in the index).
A scan resolving every backticked declaration name against the built environment led to `8ece142a`,
which fixes docstring references naming no declaration. The final delta review of
`a52ff443..a2d52d3f` approved; following its suggestions, module paths cited in docstrings say
"the module", and `scripts/upstream.py` now also rewrites backticked references to existing local
modules from `Complexity.` to `Cslib.`, so such docstrings stay correct when upstreamed. These are AI reviews, not human editorial approval or a
machine-checked equivalence between prose and Lean. AI assistance: Jetski (Gemini).

## Quadratic Fusion completeness (PR #19, 20 October 2026)

OpenAI Codex worker `fusion-quadratic-20261020` added the acyclic compiler and the corresponding
index entry, under coordinator dispatch. Independent coordinator review checked core revision
`dbb5eddb2bd1ce9ee9971d00f22c69c26ae0d542` for API design and correctness: pointwise finite-chain
stabilization and its round count, native circuit cost and semantics, the infinity case, and
zero/nonzero/infinite-carrier examples. Verdict: no findings.

The coordinator also compared the new index entry with the final Lean statements and definitions.
The stated cost, free-constant convention, infinite-carrier scope and noncomputability limitation
were accurate. One quantifier clarification was requested and applied: the cover defeats
"every semifilter above any point of A". The three declaration links are pinned to the reviewed
core revision, and each target line was checked against `git show`. The PDF builds without
undefined references or overfull boxes; the new entry on page 30 and bibliography entry on
page 42 were rendered and visually inspected. Final documentation review is requested on PR #19.
These are AI reviews, not human editorial approval or a machine-checked proof of equivalence
between prose and Lean.

## 2026-10-20: Graph Fusion transfer and inequality complexity

The new circuit-index entry describes graph-to-Boolean cover transfer (including the
semi-ultrafilter subclass) and the exact canonical/full/intersection complexity of inequality
on `2^n` vertices per side. It links to source revision
`45d71952d39a80bf96fd8e6144d9fd9ec3ecf5c5`, at the exact theorem lines (98 and 212).
The index now contains 116 entries.

The coordinating Codex agent, independent of authoring worker `fusion-graph-20261020`, reviewed
correctness/API and the changed prose against the final Lean statements. It approved the
quantifiers, two-block Boolean representation, free-OR/constant AND-cost convention,
semi-ultrafilter restriction, trivial-graph transfer, and zero-bit equality. The source review
requested only the missing `Main definitions` module-doc section, which was added and re-reviewed
at the source revision above; no remaining findings. The final PR records the reviewed document
revision. These are AI reviews, not human editorial approval or a machine-checked prose equivalence.

All six Lean gates pass; the named headline axiom guards use only `propext`, `Classical.choice`,
and `Quot.sound`. The PDF builds without undefined citations/references. Page 30 was rendered
and visually inspected; after pinning the links, the final rendered page is pixel-identical.
Both new declaration links were checked against their pinned Git source and line numbers.
Mathematical credit: Cavalar–Oliveira (2025), Lemmas 39/48 and Proposition 40. Canonical definitions
also retain credit to Samuel Schlesinger's earlier formalization. AI assistance: OpenAI Codex.

Integration reconciliation: PR #21 retains both the quadratic and graph entries after merging
main at `f024eb43a11c80a9db843a8b354295f7bdd2d80e`; the index count is 117. The source
declaration links remain pinned to their separately reviewed revisions. No theorem statement
or proof changed during conflict resolution; the PDF was regenerated from both entries.

## Fusion sampling and fixed-distribution barrier (2026-10-20)

OpenAI Codex worker `fusion-barrier-20261020` authored the sampler and barrier and this index
entry. Independent coordinator review checked the source mathematics, API, nonvacuous clients,
and draft prose. The final core revision is `503ce2b0d3d0b5cc3dd3fa793aab840d07e448fa`.
The review checked the cylinder path, uniform marginal transport, endpoint independence,
complement estimate, the `8n+8` normalization, and weighted averaging. No mathematical or API
findings were reported. One scope wording correction was requested and applied: the theorem
still applies to circuit-adaptively selected weights if the capacity bound holds for every pair;
the limitation concerns bounds restricted to the gate pairs of a particular circuit. The paper
also now states explicitly that all three sampler components are chosen uniformly.

The three new declaration links were checked against their exact source lines at the core SHA.
The PDF rebuilt without undefined references or overfull boxes; the new entry on page 30 was
rendered and visually inspected. The coordinator reviewed the final entry at `79d530cf`
against core `503ce2b0` and reported no outstanding findings after the two wording corrections.
This is AI review, not human editorial approval or a machine-checked proof of prose-to-Lean
equivalence.

Integration reconciliation: PR #22 preserves the quadratic, graph, and sampling entries after
rebasing onto main at `2fb260fffdce0fe5eeb019b202192243d74863f4`. The index count is 118.
The sampling source and tests are unchanged; declaration links are pinned to the rebased core
commit `fc0d4439550559e2773786234f13648021fa0ce0` (originally reviewed at pre-rebase
`503ce2b0d3d0b5cc3dd3fa793aab840d07e448fa` with identical line numbers).
The PDF was regenerated without undefined references or overfull boxes, and combined pages
30 and 31 were rendered and visually inspected. The sampling entry now appears on page 31.
Final integration review is recorded in PR #22.

## Random graph cover complexity (PR #23, 20 October 2026)

OpenAI Codex worker `fusion-random-20261020` implemented finite cover descriptions and the
quantitative random-graph theorem. The independent coordinator reviewed exact core revision
`5eb6d9a109234ce5579765b93bb24b7cfaca6e60`: description cardinality, decoding through bounded
closure, padding, finite-budget attainment, the row cover, the uniform probability bound, and
nonvacuous tests. An earlier API request moved padding and finite-budget attainment into
`Semifilter.lean` and generalized both to every admissibility predicate. Fresh review of the
updated revision found no outstanding correctness or API findings.

Independent review also checked the new index entry against those definitions and statements:
finite encoding cardinality; uniform distribution over all labelled bipartite graphs; the strict
lower event `floor(N/16) < rho(G)`; the upper bound `rho(G) <= N`; the `N >= 16` hypothesis and
`1 - 2^(-N)` probability; and the absence of an explicit hard-graph construction. No findings.
All four declaration links were checked against the pinned source revision. The PDF builds
without undefined references or overfull boxes, and the new entry on page 31 was rendered and
visually inspected. All six project validation gates passed again after rebasing onto the merged
prerequisites. Final documentation review is requested on PR #23. These are AI reviews, not human
editorial approval or a machine-checked equivalence between the prose and Lean.

Integration reconciliation: PR #23 merges main at
`fb8bcf29945ea529fd2dc5a41e302d519961ff8e`, retaining both the sampling and random-graph
entries and both test imports. The index contains 119 entries. Neither development
changed its Lean statements, proofs, or tests during reconciliation. All seven declaration
links were rechecked against their pinned source revisions. The rebuilt PDF has no undefined
references or overfull boxes; both entries appear on page 31, which was rendered and visually
inspected. All six validation gates pass on the combined tree. Fresh coordinator review of
this integration revision is requested in PR #23.

## 2026-10-20: Semi-ultrafilter bounds for universal verifiers

Worker `fusion-graph-20261020` added the universal-verifier lower bound and one curated index
entry, bringing the count to 118. The independently authoring-free coordinating agent reviewed
source revision `fc111b65726f9b5bc721b9c63bef8a218fcf4b35` for correctness and API design,
including the counterexample pullback, auxiliary polarity selection, exact AND count,
nonempty witness example and zero-auxiliary case. No findings remained. Its independent prose
review checked arbitrary auxiliary counts, the fixed-verifier minimum, free literals/constants/OR,
and the explicit lower-only boundary; no findings.

All six Lean validation gates pass. The headline axiom guards use only `propext`,
`Classical.choice` and `Quot.sound`. The declaration link is pinned to the source revision above,
line 137, and was checked against `git show`. The PDF builds, and the new entry on page 31 was
rendered and visually inspected. The converse and minimization over all verifiers remain in
issue #24 under #16; this entry will be extended when they are proved. Final document-head
review is recorded in PR #25. These are AI reviews, not human editorial approval or a
machine-checked equivalence of prose and Lean. AI assistance: OpenAI Codex.

Integration reconciliation: PR #25 merges main at
`fd3f45211011471c96394e4fea256235ece028ed`, preserving the sampling and random-graph
entries and all generated imports. The combined index has 120 entries. No theorem
statement, proof or test changed in reconciliation; declaration links retain their reviewed
source revisions. All six validation gates pass on the combined tree. All eight sampling,
random-graph and universal-verifier links were rechecked against pinned source lines. The
combined PDF was rebuilt and pages 31 and 32 were rendered and visually inspected.

## 2026-10-20: Universal verifiers from semi-ultrafilter covers

Worker `fusion-graph-20261020` formalized the converse and extended the existing universal-verifier
entry; the index count remains 120. Source revision
`f23523de46ed56aef9aaa7cd5c9cd7abcff6b8dd` adds the maximal extension, finite certificate,
native formula compiler, Boolean verifier specialization, and minimum over all finite auxiliary
counts and all verifiers. The coordinating agent proposed the substantive factor-five
construction and is therefore not counted as an independent reviewer of this work.

Independent reviewer `fusion-barrier-20261020`, who did not author the source, reviewed all five
new modules and the tests for correctness and API design. The review checked the fixed empty
rejection, equal rejected pairs, empty carrier, exact three-bit/five-AND accounting, both
quantifier directions, extended-natural minimization and nonconstant examples. No source or
test findings remained. Supplementary exhaustive small-carrier checks supported the certificate
semantics but do not replace Lean proofs.

The same independent reviewer checked the extended index against the final Lean statements:
quantifiers, free literals/constants/OR, exact auxiliary and AND counts, zero cases,
extended-natural infimum, construction/runtime limitations and source attribution. One link
correction was requested and applied: the lower-direction link now points to the exact-length
extraction theorem at `fc111b65726f9b5bc721b9c63bef8a218fcf4b35`, line 123. The new verifier
and headline-bound links point to lines 66 and 131 of the squash-merged main revision
`fddf011fc21ee2b3d148dea54d07822c13d817f0` (reviewed on the branch at
`f23523de46ed56aef9aaa7cd5c9cd7abcff6b8dd` with identical line numbers). All three
links were checked against `git show`.

All six validation gates pass on the source revision; named axiom guards contain only
`propext`, `Classical.choice` and `Quot.sound`. The PDF was rebuilt and the extended entry on
page 32 was rendered and visually inspected. Exact-head approval and integration evidence
are recorded in PR #28. These are AI reviews, not human editorial approval or machine-checked
prose equivalence. AI assistance: OpenAI Codex. Mathematical credit remains Cavalar–Oliveira's
presentation of Karchmer's characterization; the explicit factor five is the checked certificate
deduction described above.


## 2026-10-20: Canonical numeric structures for ordered first-order logic

Worker `ordered-fo-20261020` added native numeric vocabulary/structures and the relational
forgetting bridge at source revision `223f5289aa5809f50251aba7aced4d7e98478a78`. One new
curated prerequisite entry brings the index to 121 entries. The source credit includes
Immerman's Section 1.2 conventions and Proposition 3.5, and Samuel Schlesinger's earlier
canonical-expansion interface at its pinned revision. No earlier custom syntax was ported.

The independent parent coordinator's preliminary API/correctness review found no substantive
issues: native language sums retain input functions/constants, canonical structures require
`n ≥ 2`, BIT indices start at zero, and the existing interpretation target remains relational.
Final exact-source and index review verdicts are tracked in PR #37. The prose distinguishes this
semantic prerequisite from target constants, arbitrary-base tuple BIT lifting, numeric-preserving
composition and ordered complexity/capture results, all of which remain open in the roadmap.

All six validation gates pass. Concrete clients cover two- and three-element universes,
constant separation, bit orientation, quantified formulas containing input constants, and a
nontrivial BIT-defined interpreted relation; named axiom guards use only `propext`,
`Classical.choice` and `Quot.sound`. The three declaration links are pinned to the source
revision above, lines 142 and 149 of `Ordered/Basic.lean` and line 68 of
`Ordered/Interpretation.lean`, and checked against `git show`. The PDF builds, and page 8
was rendered and visually inspected. These are AI reviews, not human editorial approval
or machine-checked prose equivalence. AI assistance: OpenAI Codex.
## Uniform counting aggregation (PR #36, 20 October 2026)

OpenAI Codex worker `awpp-amplification-20261020` extends the counting-algebra entry with
uniform #P/GapP word sums, variable unary GapP powers, and exact certificate padding.
Source revision `8e76ae85c0544966f2c2d074a1610d31da405c3b` passes all six project gates;
clients exercise negative values, input-dependent counts, overlapping positive/negative
acceptance, and exponent zero including a zero base. Named axiom guards use only the three
permitted axioms. Early independent coordinator review found no correctness issues in the
signed cancellation or padding; exact-revision source/API and index review is requested on
PR #36. The index count stays 120: this extends an existing entry. The full AWPP amplification
endpoint remains open in #31.

All four declaration links were checked against the pinned Git source. The PDF builds without
undefined references or overfull boxes, and the changed entry on page 18 was rendered and
visually inspected. Review is AI-assisted, not human editorial approval or machine-checked
prose equivalence.

## 2026-10-20: Equality of PP and counting oracle classes

Worker `counting-oracle-20261020` proved the reverse inclusion and oracle-class equality in
source `39c2e0198d7f0db5555e7f478933789d7d772631`. The existing Toda/PP-oracle entry is
extended; the curated result count is unchanged. The result uses the existing encoded classes,
with one fixed deterministic program correct for every admissible oracle and arbitrary answers
outside valid codes.

Independent coordinator `/root` performed an early source/API review and checked the revised
prose against the exact source revision. The review
checked the shifted count `2c + (2^p - 1)`, zero random bits, strict-majority ties, the polynomial
bit index, bounded reply consumption in open substitution, and the preimage language that
preserves malformed-word freedom. The new claims and quantifiers matched the exact source.
One wording correction was requested in the existing oracle description: replace “queries are
not counted” by “no fixed query-count bound is imposed”, to avoid suggesting free query cost.
That correction is applied.

All six validation gates pass on the source revision. Tests include a nonconstant PP oracle
client, boundary arithmetic, and admissible counting oracles disagreeing on the empty non-code
word. Named guards for the bit representation, reverse inclusion and equality use only
`propext`, `Classical.choice` and `Quot.sound`. All six links in the affected entry were checked
against pinned source declarations. The PDF was rebuilt and page 16 rendered and inspected.

Source credit distinguishes Gill's PP definition and Fortnow's Theorem 4.14 and Corollary 3.7
from the direct shifted-count implementation used here. Existing source authors and references
are preserved. Final exact-head approval and integration are recorded in PR #35. This is an AI
review, not human editorial approval or a machine-checked equivalence between prose and Lean.
AI assistance: OpenAI Codex at Samuel Schlesinger's request.

PR #36 integration: merged current main after PR #35, preserving both counting entries and
the unchanged index count of 120. No Lean source or test changed in this reconciliation.
Independent exact-head approval of source and index at `35bf8a1f` is recorded in PR #36;
the combined document and validation gates are rechecked before integration.


PR #37 integration reconciliation incorporates reviewed PR #29 head
`ac5b1e70` (including PRs #35 and #36). Both sets of review notes, all generated imports,
and the counting and ordered-FO index changes are retained. No ordered-FO source or test
changed. The combined index contains 121 entries; all six validation gates pass. The PDF
was rebuilt. Ordered-FO page 8 is pixel-identical to its reviewed rendering; the combined
counting pages 19, 23 and 25 were rendered and inspected. Exact integration-head review
is tracked in PR #37.

## Uniform AWPP error reduction (PR #40, 20 October 2026)

Worker `awpp-amplification-20261020` adds a uniform-amplification entry with
one uniform GapP numerator attaining error at most `2^(-r(x))` for any requested
exponent polynomially bounded in encoded input length. The construction chooses a
fixed dominating length polynomial `q`, uses `12q(n)` majority trials and denominator
exponent `12q(n)p(n)`, and does not need to compute the requested rate or efficiently
sample the original GapP value. This adds one curated entry.

Independent coordinator `/root` reviewed source and tests at
`c7d716f413c92d69597f5f6dee1863e9cb095a68`, including the uniform GapP construction,
finite counting identity, strict-majority ties, zero repetitions and denominator one.
Reviewer `fusion-barrier` supplied an additional independent early source/API review.
No findings remained. The coordinator also checked the index draft against this source,
including quantifier order, arbitrary dominated rates, exact denominator accounting and
the verifier-model boundary; no findings remained. Final document-head review is
recorded in PR #40. These are AI reviews, not human editorial approval or a machine-checked
prose equivalence. AI assistance: OpenAI Codex.

All six gates pass on the source revision. Nonconstant clients have genuine quarter error
before amplification; other clients cover a varying rate, a possibly noncomputable dominated
rate, zero exponent and denominator one. Named axiom guards use only the three permitted
axioms. All three new declaration links were checked against pinned Git source lines.
The source credits Fenner's characterization and error reduction, with the explicit factor
12 coming from the existing formalized BPP majority estimate and Arora–Barak's majority
framework. Nondeterministic counting-machine characterizations and AWPP PP-lowness remain open.

Integration includes the reviewed WPP branch at `ac5b1e70` and ordered-FO branch at
`fc80b922`, preserving their entries and all generated imports. All six gates pass on
the combined source tree. The combined index has 122 entries. The final PDF builds
without undefined citations or overfull boxes; pages 25 and 26 were rendered and visually
inspected. Uniform amplification has a separate entry to keep the existing closure entry
within one page. Its standalone text explicitly repeats the encoding and verifier-model scope.
Final coordinator prose review requested two wording corrections after splitting the entry:
refer to the following entries in the plural, and use “there exist” for the witnesses.
Both are applied; the PDF was regenerated and the corrected page rendered and checked.
No theorem statement or proof changed.

## Uniform SBP multiplicative gap amplification (PR #46, 20 October 2026)

Worker `sbp-amplification-20261020` adds unary variable #P powers and uniform SBP gap
strengthening. Source `56e55d873fe57730bf723d7c56af0b6c16fc4d30` passes all six gates.
Independent coordinator `/root` performed an early source/API review without findings,
checking exact row counts, zero width and empty products, count-preserving certificate
padding, the binary-output threshold power and the positive dominating repetition count.
Exact-revision source, test and index review is requested in PR #46.

The existing counting-algebra and amplification entries are extended, keeping the curated
count at 122. The SBP statement has one #P count and one positive binary-output polynomial-time
threshold for all inputs. The requested exponent may be noncomputable if polynomially bounded;
a fixed dominating length polynomial supplies the repetition schedule. The prose distinguishes
a multiplicative gap from normalized additive error. Watson's powering argument is credited,
with the uniform dominated-rate formulation identified as a checked consequence.

Tests give a nonconstant language with count 3 on members and 1 on nonmembers and threshold 3;
clients cover varying, zero and possibly noncomputable requested rates, along with #P zero-width
and empty-product boundaries. Named axiom guards use only the three permitted axioms. Both new
index links were verified against the pinned source. The PDF builds without undefined citations
or overfull boxes; pages 19 and 25 were rendered and visually inspected. Review remains AI-assisted,
not human editorial approval or machine-checked prose equivalence. AI assistance: OpenAI Codex.

## 2026-10-20: Formula-defined target constants

Worker `ordered-fo-constants-20261020` extended the relational interpretation API at source
revision `d5382b56b3be600056b71729e34a40aac1faf3f7`. The existing ordered-FO entry now states
constant-aware formula and sentence pullback under explicit unique-domain selection validity,
and the canonical `0`/`1`/`max` client for every `n ≥ 2`. No new entry is added; after incorporating
approved PR #40 head `2c6f5cacff2aeea0efde34c5f01f9a6139dd7855`, the combined index has 122 entries.

The independent parent coordinator reviewed the new API, proofs, tests and draft index without
findings. Review covered finite constant/dimension types, validity inside the interpreted domain,
separation of free variables and quantified constant coordinates, native Mathlib syntax reuse,
and the relational-plus-constants target boundary. The tests include a constant defined solely
by an input relation with no source constants, free variables under quantification, canonical
values, missing and ambiguous definitions, and no constants on an empty domain. Exact-head
review verdicts are tracked in PR #41.

The source conventions were checked against Immerman's primary text: Definition 1.26 includes
formula-defined constants; Definition 3.3 gives the dual syntactic map; Proposition 3.5 and
Remark 3.6 give sentence and free-variable truth preservation. The four new declaration links
are pinned to the source revision above, lines 103/138 in `Interpretation/Constants.lean` and
52/66 in `Ordered/Constants.lean`, and verified with `git show`.

All six gates pass on both the source and combined integration tree. The named axiom guards use
only `propext`, `Classical.choice` and `Quot.sound`. The PDF builds; the extended ordered-FO entry
on page 8 and preserved AWPP entry on page 26 were rendered and visually inspected. Tuple BIT
lifting for arbitrary bases, numeric-preserving composition and ordered complexity/capture results
remain open. These AI reviews do not imply human editorial approval or machine-checked prose
equivalence. AI assistance: OpenAI Codex.

### Polynomial-family wide-gap robustness (2026-10-20)

- Worker `poly-wpp-20261020` added the full one-sided polynomial-family WPP/LWPP
  characterization, including uniformly computed signed binary target lists and indexed forms,
  at source revision `3910fa96e6b22221363c38f3b3f0f33c49d20650`.
- Independent coordinator `coordinator-ops-20261020` reviewed the source, meaningful variable
  target clients, and index draft against that revision. No mathematical/API findings were
  reported. The requested prose clarification now states that the target count is computed in
  polynomial time with unary output. The review checked the unknown accepting index, list-output
  bounds, length-only LWPP family, negative/duplicate/empty lists, and the one-sided scope.
- The new entry credits Hemaspaandra, Hemaspaandra, Spakowski and Watanabe (Theorems 3.1 and 3.7)
  and Fenner--Fortnow--Kurtz. It leaves two-sided target families, oracle lowness and counting-machine
  characterizations separate. The previous wide-gap entry now points to this result.
- All six prescribed checks passed on the source revision. The reviewed PR41 dependency stack was
  then integrated without changes to this source; integrated validation and final exact-head
  coordinator approval are recorded in the PR.
- All five new declaration anchors were checked against the pinned source. The combined PDF has
  123 entries; rendered pages 23 and 24 were inspected for layout and clipping. This AI review is
  not human editorial approval or a formal proof of prose equivalence.

PR #46 integration merges the independently reviewed WPP branch at `8cb09256`, preserving
its polynomial-family robustness entry and the formula-defined constants entry from PR #41.
The combined index has 123 entries; SBP source and tests are unchanged. All six gates pass
on the combined tree. The PDF was rebuilt without undefined citations or overfull boxes;
the changed SBP/counting pages 19 and 26 were rendered and visually inspected. Source links
retain their previously checked revisions. Final integration approval is recorded in PR #46.

### Two-sided polynomial-target robustness (2026-10-20)

- Worker `two-sided-wpp-20261020` proved both WPP/LWPP two-sided characterizations and indexed
  forms at source `83f5e8ab8dcde006b3fb28bbd72e9ba837e23fef`, following Definition 3.8,
  Corollary 3.11, Theorem 3.12 and Appendix A of Hemaspaandra--Hemaspaandra--Spakowski--Watanabe.
- The existing polynomial-family robustness entry now states the full disjoint acceptance and
  rejection family theorem. It preserves the one-sided specialization, explicit uniform binary
  output and unary-index/count conventions, all-length LWPP disjointness, zero on either original
  side, signed/repeated targets, unknown indices, and empty-family boundaries. The curated count
  remains 123. Oracle lowness and counting-machine equivalences remain separate.
- Source and tests are MCP-clean; all six prescribed gates pass. Nonvacuous tests accept zero
  against nonzero rejection, reverse the roles, grow both signed/repeated lists, check length zero
  and forbidden overlap, and exercise empty-family and indexed-family clients. Headline axiom
  guards use only the standard three allowed axioms.
- Four new declaration links were verified against the exact source. The PDF was rebuilt and
  rendered page 24 inspected without clipping. Independent API/correctness/index review has been
  requested from a separate coordinator; the exact-head verdict and any revisions are recorded
  in the PR. This does not imply human editorial approval.


PR #52 integration preserves source and tests at `83f5e8ab` and incorporates main `37f07692`,
including PR #46. All six gates pass on the combined tree. The independent coordinator reviewed
source, tests and the rendered entry with no correctness/API findings; its requested index
clarification now names GapP closure for this product of differences, without asserting general
indexed-product closure. The PDF was rebuilt after that correction; exact-head approval is
recorded in the PR. The combined count remains 123.

## 2026-10-20: Lexicographic tuple order and canonical constants

Worker `ordered-tuples-20261020` first factored generic tuple helpers into a lightweight
module at `b231228b`, retaining all public names and the existing Encoding import interface.
Source revision `51e253c1e9d3b0ea81512eb7ff0fe830a00435bc` then adds arbitrary-base,
first-coordinate-most-significant tuple numbering, first-difference order, native quantifier-free
strict/weak order formulas and uniquely selected full-domain canonical constants. A new curated
entry records this prerequisite; successor, BIT lifting, numeric-preserving composition and
ordered complexity/capture results remain open.

The independent parent coordinator reviewed the refactor, source, tests and draft index with no
API, correctness or prose findings, and independently checked MCP diagnostics and the rendered
entry on page 9. Review covered arbitrary bases, the full-domain hypothesis, coordinate order,
zero-dimensional singleton behavior and positive-dimensional constants. Exact final-head review
is tracked in PR #51. These AI reviews do not imply human editorial approval or machine-checked
prose equivalence. AI assistance: OpenAI Codex.

All six gates pass separately after the refactor and after the source addition. Tests distinguish
base-three lexicographic order from the existing colexicographic enumeration, check a base-five
rank and its inverse, zero dimensions, constant ranks and native sentence pullback. Named axiom
guards use only `propext`, `Classical.choice` and `Quot.sound`. The source credits existing tuple
helpers, Mathlib's enumeration and Pi.Lex, and Immerman's Remark 1.32 and Exercise 1.33(1). The
primary text's restricted-domain BIT warning is retained explicitly in the roadmap. The five new
declaration links are pinned to the source revision above and verified against its exact lines.

PR #51 integration preserves PR #52 head `70766f5b29c1fd2fa83cba5d04d6e83d569c5962`,
including current main and PR #46. Tuple source and tests remain unchanged. All six gates pass on
the combined tree. The curated index has 124 entries; the rebuilt PDF's tuple page 9 and preserved
two-sided counting page 25 were rendered and inspected. No undefined citations or overfull boxes
were introduced. The final integration revision is submitted for fresh coordinator approval.

## Uniform indexed counting products (PR #53, 20 October 2026)

Worker `indexed-products-20261020` proves uniform indexed products for jointly uniform #P
and GapP families on the pair of an encoded input and unary natural index. Source revision
`d80cc187edf729390f830cc2a44fa508168e9587` passes all six project checks. The #P verifier
uses rows padded with false bits to width `p(2|x|+1+r(x))`; the pre-padding total is `r(x)`
times that width. The GapP proof uses Boolean expansion, the certified #P product theorem,
a binary polynomial-time sign and the existing uniform word-sum closure. No general indexed
product closure is assumed.

Tests instantiate varying quadratic certificate lengths, empty products including zero
factors, zero-width rejection, indexed negative factors and exact cancellation between
explicit overlapping positive/negative #P counts. Named axiom guards contain only the three
permitted axioms. Both new declaration links have been checked against pinned Git source.
The existing counting-algebra entry is extended; this adds no curated entry. The prose states
the joint uniformity and unary-bound requirements, the explicit certificate accounting and
the still-open oracle-lowness boundary. Mathematical source credit remains Fenner–Fortnow–Kurtz.
The independent parent coordinator reviewed the exact source, tests and draft index with no
correctness, API or prose findings, and independently verified MCP diagnostics, all six gate
results and both pinned declaration links. Final combined PDF evidence and exact-head approval
are recorded in PR #53 before integration. AI assistance: OpenAI Codex; AI review is not human
editorial approval or a machine-checked equivalence between prose and Lean.

PR #53 integrates the reviewed PR #51 head `defa850c` (including PR #52) without changing
its indexed-product source or tests. All six gates pass on the combined tree. The existing
counting-algebra entry is extended, preserving the 124-entry count and the tuple/two-sided
robustness entries. The PDF was rebuilt without undefined citations or overfull boxes;
rendered pages 20 (products), 9 (tuples) and 25 (two-sided robustness) were inspected.
The two new source anchors retain the independently checked source revision above.

### Integration with the updated cslib pin

Coordinator `coordinator-ops-20261020` merges main revision
`cf03096b8b61b89417f7a3fb4552bc1b9c47cc16` into PR #53, preserving its source and tests.
The dependency pin is now `b5f3b77d9f045ed8f2dfec05505b159c2417e1c6`. The text merge
preserves main's corrected Fusion links, Unique-SAT cross-reference, zig-zag typography,
module documentation and README changes, as well as the indexed-product entry. The PDF
was rebuilt, its final log has no undefined citations or overfull boxes, the result count
remains 124, and all seven affected product/Fusion declaration anchors were checked.
Final validation and independent exact-revision integration review are recorded in PR #53.

The upstream audit confirms that the public cslib pin and submitted copies are current.
Independent reviewer `relativized-counting-20261020` inspected all 16 reported `@9cce4cc7`
marker differences: they are the unpublished rewrite already documented in `UPSTREAM.md`,
with additions absent from the older published `7f7c0696` tree. The local code and provenance
markers are preserved. The unpublished commit object was unavailable for a byte-for-byte
source comparison; this audit does not certify that missing comparison or relabel the
rewrite as the older published source. AI assistance: OpenAI Codex.

## 2026-10-20: Non-wrapping successor on full tuple universes

Worker `ordered-successor-20261020` extends the existing tuple entry for source revision
`72b80bbaccd792d6ee9e7858d0f23a40ed3f3f57`; the curated count remains 124. The coordinatewise
carry condition is proved equivalent to exact rank increment for arbitrary bases. The native
compiler preserves quantifier-freeness conditional on its supplied source successor. The canonical
instance in the library's `≤`/BIT basis uses one universal adjacency quantifier in each carry
alternative; the index makes this scope explicit. Dimension-zero and maximum/no-wrap boundaries
are stated. BIT lifting, arithmetic definability and numeric-preserving composition remain open.

All six gates pass on the source revision, and source/tests are MCP-clean. Clients cover base-three
carry/non-carry, multiple carried digits, base-five carry, skipped ranks, maximum/no-wrap and zero
dimension. A distinct input language with an actual atomic successor relation supplies a nonvacuous
client for conditional quantifier-free compilation. The three named headline axiom guards use only
`propext`, `Classical.choice` and `Quot.sound`. The two new index links are pinned to the source
revision above, lines 263 and 185, and checked against the declarations. The source basis and
full-domain assumption were checked against Immerman's Remark 1.32 and Exercise 1.33(2).

Independent coordinator `fusion_barrier` approved the exact source revision above after reviewing
API, correctness, tests and the draft index against the primary source. No findings remained;
fresh MCP diagnostics for both new files were clean. Exact final integration/PDF review is tracked
in PR #59. AI assistance: OpenAI Codex. These reviews do not imply human editorial approval or
machine-checked prose equivalence.

PR #59 preserves the source and tests while integrating PR #57 head
`ae7a65d0add5b89d234ba8274e04dfde09562955`, including the reviewed indexed-product stack.
All six gates pass on the combined tree. The rebuilt index has 124 entries; page 9 (successor),
page 14 (preserved SL) and page 21 (preserved counting products) were rendered and inspected. The
final LaTeX log has no undefined citations or overfull boxes. Independent coordinator
`fusion_barrier` inspected the final successor page with no findings; exact integration-head
approval is recorded in PR #59.

### Successor integration with the refreshed SL dependency

PR #59 incorporates independently reviewed PR #57 revision
`c6f694bd5f4cb77b17714c4f41d6ab8c59d61cf8`, including the main documentation corrections and
cslib pin `b5f3b77d9f045ed8f2dfec05505b159c2417e1c6`. The successor source and tests are
byte-identical to `72b80bbaccd792d6ee9e7858d0f23a40ed3f3f57`, and its index text and pinned
links are unchanged. Both appended review histories are preserved. All six combined gates pass
on this dependency revision. The rebuilt PDF retains 124 entries, with clean final LaTeX output;
pages 9 (successor), 14 (SL) and 21 (counting products) were rendered and inspected. Independent
coordinator `fusion_barrier` inspected those pages and the preservation delta without findings;
final exact-head approval is recorded in PR #59. This integration introduces no new theorem scope.

## 2026-10-20: Exact canonical addition from order and BIT

Worker `ordered-addition-20261020` adds the PLUS entry for source revision
`49531f8754cc310d21216bc7e5a0da33499036b0`. One native formula, independent of universe size,
realizes ordinary natural-number addition on every canonical `Fin n`, `n ≥ 2`, without a fit
premise. The out-of-range theorem rejects every result. The index records the least-significant-bit
convention and leaves TIMES, the Bit Sum Lemma, unrestricted arbitrary-base tuple BIT lifting and
numeric-preserving composition open. The source credits Immerman Proposition 1.9 and the PLUS
part of Theorem 1.17(1), existing library propagation, and Lean BitVec carry/addition proofs.

All six gates pass on the source revision. Source and test MCP diagnostics are clean; clients cover
n = 2, 3, 5, 9, zero, maximum results, multiple carries, killed carries, rejection for every
overflow candidate and native free-variable relabeling. Named headline axiom guards admit only
`propext`, `Classical.choice` and `Quot.sound`. Declaration links are pinned to source lines
142 and 162 and checked against their exact names.

Independent coordinator `fusion_quadratic` approved the exact source/API/correctness/tests and
draft index with no findings, checked both files with fresh MCP diagnostics, and verified the
primary-source references. The exact-revision review is recorded in
[PR #66](https://github.com/cslib-community/complexitylib/pull/66#issuecomment-6297706327).
Final combined ancestry, dependency validation and rendered PDF review remain pending in the PR.
AI assistance: OpenAI Codex. This review is not human editorial approval or a machine-checked
prose-to-Lean equivalence.

The PLUS preparation integrates successor revision
`17ae942e0737495057544f6d74a8f695a85ad72b` with cslib
`b5f3b77d9f045ed8f2dfec05505b159c2417e1c6`. Source and tests remain byte-identical to the
approved revision. All six preparation gates pass on the new pin. The local index contains
125 entries; the new PLUS entry on page 8 was rendered and inspected, with no undefined
citations or overfull boxes in the final LaTeX log. Final combined counting-stack integration,
entry-count reconciliation and exact-head PDF review remain pending before publication.

## 2026-10-20: Uniform bounded Boolean closure of wide-gap classes

Worker `bounded-wide-gap-20261020` adds a separate curated entry for source revision
`b0490b92e868b218d36cfb1fd8d1c9f0e56b8cd5`. It states bounded conjunction and disjunction
closure of WPP and LWPP for a single jointly uniform language on instances and unary indices,
with a polynomial-time unary input-dependent bound. The LWPP target family contains every
prefix product through a fixed length-polynomial bound; it therefore normalizes counts that
vary between inputs of the same length. Empty ranges, signed targets, the verifier model and
remaining adaptive-oracle/lowness boundaries are explicit. The mathematical construction is
credited as a deduction from Fenner–Fortnow–Kurtz counting algebra and the polynomial-family
robustness of Edith Hemaspaandra, Lane A. Hemaspaandra, Holger Spakowski and Osamu Watanabe.

All six source validation gates pass and source/tests have clean MCP diagnostics. Nonconstant
indexed-bit clients use a negative length-only target, different counts on equal-length inputs,
growing bounds, differing prefix signs/magnitudes and empty ranges. Four headline axiom guards
admit only `propext`, `Classical.choice` and `Quot.sound`. The four declaration links are pinned
to the source revision, lines 70, 96, 106 and 138.

Independent coordinator `fusion-quadratic` approved exact-source API/correctness/tests and the
draft index with no findings in PR #60, comment 6297275055. Final combined-head/PDF inspection
and CI are tracked in that PR. The added entry brings the current 124-entry stack to 125.
AI assistance: OpenAI Codex. AI review does not imply human editorial approval or a Lean proof
of prose equivalence.

Final PR #60 integration includes PR #57 and the independently approved successor head
`dfd28a29b4e779a944e96fe7107abd9589f574b2`. The bounded-closure source and tests remain
byte-identical to `b0490b92`. All six gates pass on the combined tree. The rebuilt PDF's new
entry on page 27 was rendered and inspected; the four pinned declaration links were verified,
the final LaTeX log has no undefined citations or overfull boxes, and the count is 125.
Independent coordinator `fusion-quadratic` inspected this final rendering and the explicit
fixed-polynomial wording with no findings; exact-head approval is tracked in the PR.

### Bounded-closure integration with the refreshed dependency stack

PR #60 integrates independently approved PR #59 head
`17ae942e0737495057544f6d74a8f695a85ad72b`, including the current cslib pin
`b5f3b77d9f045ed8f2dfec05505b159c2417e1c6`. Its bounded-closure source and tests remain
byte-identical to `b0490b92e868b218d36cfb1fd8d1c9f0e56b8cd5`; the four pinned links and
entry prose are unchanged. Both review histories and the dependency's documentation corrections
are preserved. All six combined gates pass. The rebuilt PDF retains 125 entries, with no final-log
undefined citations or overfull boxes. Page 27 was rendered and inspected by the author and
independent coordinator `fusion-quadratic`, who found no scope or layout issues. Final exact-head
integration approval is recorded in PR #60. This refresh introduces no new theorem scope.

## 2026-10-20: Truth-table closure of wide-gap classes

Worker `truth-table-wide-gap-20261020` adds one curated entry for source revision
`5df0e7da9798d62d5506dc90e4cb3c2f381b82d9`. It states closure of WPP and LWPP under the
encoded polynomial-time truth-table reduction interface, together with the more general joint
indexed-language endpoints. The unary polynomial-time count, total joint query generator,
input-sensitive Boolean combiner and nonadaptive answer-word semantics are explicit. Query
lengths and query counts may vary at fixed input length; LWPP uses many-one normalization and
then polynomial-family prefix-target robustness. Empty batches are included. The entry credits
Holger Spakowski, Mayur Thakur and Rahul Tripathi's Theorem 5.6(a), the counting algebra of
Stephen Fenner, Lance Fortnow and Stuart Kurtz, and the robustness theorem of Edith Hemaspaandra,
Lane A. Hemaspaandra, Holger Spakowski and Osamu Watanabe. Adaptive WPP closure, the source's
separate UP-oracle containment and oracle lowness are not claimed.

Independent coordinator `coordinator-ops-20261020` approved the exact source, tests and draft
index in PR #69, comment 6297944865. The primary source's Theorems 5.6(a) and 5.9 were checked
on rendered author-report pages 24 and 25. Tests include a nonconstant XOR reduction with
signed length targets, differing query lengths in one batch, differing counts at equal input
length, and zero-query combiners that accept, reject or depend on the original input. Four
headline axiom guards admit only the standard allowed axioms. The five index links are pinned
to the reviewed source revision and their declaration lines were checked.

The local preparation incorporates reviewed PR #60 head
`c46186f7ca68ae941c86b1d8b0a5f9d20bb5c135` and cslib pin
`b5f3b77d9f045ed8f2dfec05505b159c2417e1c6`, preserving the source and tests byte-for-byte.
Fresh MCP diagnostics are clean and all six combined gates pass. The PDF builds without
undefined citations or overfull boxes; page 28 was rendered and inspected. This preparation
has 126 entries before the remaining dependency-stack entries are integrated. Final combined
PDF/count reconciliation and exact-head independent review remain pending in PR #69.
AI assistance: OpenAI Codex. AI review does not imply human editorial approval or a Lean proof
of prose equivalence.

## Relativized counting and majority verifiers (PR #61, 20 October 2026)

Worker `relativized-counting-20261020` adds #P^A, GapP^A and PP^A using the existing strict
oracle-program certificate and fixed polynomial-length Boolean witnesses. Source revision
`21c83869180e7e9238477d021280352addf96e30` passes all six prescribed checks. Independent
coordinator `/root/fusion_graph` read both new class modules, the oracle-result product rule,
the tests and the underlying resource/counting contracts, obtained fresh clean MCP diagnostics,
and approved the exact source/API/correctness revision with no findings.

The positive-gap characterization pads certificates of lengths p and q with false tails to p+q,
then uses one selector bit; zero lengths and exact ties are covered. Ignoring the oracle gives
ordinary inclusions; the existing certified simulation eliminates P-decidable oracles. Clients
use genuine membership queries, zero-width witnesses, positive/negative gaps, exact width-one
ties, a zero gap with p=q=0, and empty/nonempty P oracles. Named axiom guards use only the three
permitted axioms.

The new index entry records the fixed program, arbitrary-stateful-oracle resource certificate,
correctness against the stateless language oracle, exact witness accounting, strict threshold,
and the verifier/machine-equivalence and lowness boundaries. Seven declaration anchors are
pinned to the source revision above. Mathematical credit is given to Fenner--Fortnow--Kurtz,
Fortnow (Lemma 3.6 and Classification 4.3), and Arora--Barak Section 3.4. The same independent
coordinator approved the draft index with no findings and verified all seven pinned anchors
(review comment 6297302134 in PR #61). Final PDF and integration evidence are recorded there. AI assistance: OpenAI Codex; independent AI review
does not imply human editorial approval or machine-checked prose equivalence.

The first PR #61 combined integration incorporates reviewed PR #60 head `bc424325` and
its PR #59/#57 predecessors without changing source or tests at `21c83869`. All six combined
gates pass. The actual curated entry count is126; the rebuilt PDF has no undefined citations
or overfull boxes. Rendered pages22 (relativized counting),28 (bounded wide-gap closure) and9
(tuple successor) were inspected; `/root/fusion_graph` independently inspected page22 with no
findings. This completed revision is preserved locally while the coordinator refreshes the
stack against the subsequently landed upstream synchronization; final publication will use
that refreshed base and receive a fresh integration review.

### Relativized-counting integration with the refreshed dependency stack

PR #61 integrates independently approved PR #60 revision
`c46186f7ca68ae941c86b1d8b0a5f9d20bb5c135` and its PR #59/#57 predecessors, including
cslib pin `b5f3b77d9f045ed8f2dfec05505b159c2417e1c6`. Its two class modules, oracle product
helper and tests remain byte-identical to source `21c83869180e7e9238477d021280352addf96e30`.
The entry prose and seven pinned declaration anchors are unchanged. All 125 predecessor entries
and their review histories are preserved; the combined count is 126. All six combined gates pass,
fresh MCP diagnostics for all four source/test files are clean, and the documentation configuration
check passes. The rebuilt PDF has no undefined citations or overfull boxes. Pages 22, 28 and 9
were rendered and inspected; independent coordinator `fusion_graph` inspected the new page 22
with no scope or layout findings. Final exact-head integration review is recorded in PR #61.
This dependency refresh introduces no new theorem scope.

## 2026-10-20: Final canonical-addition integration

Worker `ordered-addition-20261020` integrated independently approved Boolean-hierarchy revision
`7555a6120e593cc17369e019180a6e43f3ff0427`, including the merged successor, bounded-closure,
oracle-counting and cleanup milestones. The addition source and tests are byte-identical to
`49531f8754cc310d21216bc7e5a0da33499036b0`; no theorem statement or proof changed. Both review
histories and all predecessor index entries are preserved. The combined index contains 127
entries. Both addition declaration links were checked against their pinned source lines.

The PDF was rebuilt and pages 9 (PLUS), 4 (Boolean hierarchy), 23 (oracle counting) and 29
(bounded closure) were rendered and inspected. The final LaTeX log has no undefined references
or overfull boxes. Independent coordinator `fusion_quadratic` checked source/test identity,
predecessor prose preservation, the exact PLUS scope, links and all four rendered pages without
findings. Fresh MCP diagnostics for the source and tests are clean. Final validation and exact
revision approval are recorded in PR #66; this AI review does not imply human editorial approval.
All six combined validation gates passed in
`.worktrees/ops-coordinator-logs/ordered-addition-final-check.log`; the only subsequent edit
records this validation evidence.

## 2026-10-20: MAJSAT integration

The MAJSAT development is by `worker-agy-majsat-20261020`, assisted by Claude Opus 4.6
in Antigravity; mathematical credit is to Simon (`Simon1975`). Source revision
`3f273bbfa63b964c32474cd341e253ddcf466fb0` and final test revision
`f8c10c461983134f053687a529bdf4489afbcfda` received independent API, correctness and
index review. Final bounded fixes restored the literal PR description and genuine majority-tie
and zero-padding tests. Coordinator `fusion_quadratic` verified these fixes and approved the
unchanged author revision in PR #67, comment 6298385907. Completeness is for general CNF;
restricted clause-width completeness is not asserted.

Coordinator `fusion_quadratic`, assisted by OpenAI Codex, integrates independently reviewed
PR #66 revision `49b13382a079632ef215a4d23692c9cdd1170311`, preserving the original author
branch and byte-identical MAJSAT source and tests. The roadmap union retains both MAJSAT
completeness and the predecessor's Boolean-hierarchy milestones. This extends the existing
counting-completeness entry, preserving all other entries and the total of 127. Its 12 source
anchors remain pinned to the reviewed declarations. Final combined validation, rendered-page
inspection and independent exact integration review are recorded in PR #67. AI review does not
imply human editorial approval or machine-checked equivalence of prose and Lean.

All six combined gates pass in `.worktrees/ops-coordinator-logs/majsat-final-check.log`.
The source and tests have clean fresh MCP diagnostics. The rebuilt PDF has no undefined
citations or overfull boxes; pages 2 (counting completeness) and 4 (Boolean hierarchy) were
rendered and inspected. Documentation configuration and whitespace checks pass. Only this
validation record was appended after the gates; final exact-head review is recorded in PR #67.

## 2026-10-20: Tree Evaluation input-size corollary integration

The corollary development is by `worker-agy-treeeval-20261020`, assisted by Claude Opus 4.6
in Antigravity. Christian Reitwiessner's earlier formalization credit is preserved; mathematical
sources remain Cook--Mertz and Goldreich's exposition. Source revision
`3a10a7a7c55bc0b5ec4588e369ab19daf66418f7` and document revision
`b110fbb558d07b1d5597a62b5828bbe568e8a998` received independent API, correctness,
nonvacuity and theorem-index review. Coordinator `fusion_quadratic` verified the repaired
PR-body notation and recorded final approval in PR #68, comment 6298114614.

Coordinator `fusion_quadratic`, assisted by OpenAI Codex, integrates the validated MAJSAT
revision `45fd65f150b9daaccc09c3b8dbea88ebbeac6aea` and its reviewed predecessor stack.
The original author branch and all new bounds and clients are preserved. The only additional
TreeEval source difference from the author's revision is the existing main-branch refactor of
unary-block decoding to the shared list helper; its public statement is unchanged. The six new
source anchors and entry text remain pinned to the reviewed source. The input-size result
still restricts to positive value length and height, one fixed evaluator and valid encoded
instances, without an asserted asymptotic running time. The sharp Cook--Mertz parameter bound,
malformed-input recognition and Williams's simulation remain unproved here. This extends an
existing entry, retaining all predecessor entries and the total of 127. Final validation,
rendered-page inspection and independent exact integration review are recorded in PR #68;
AI review is not human editorial approval or machine-checked prose equivalence.

All six combined gates pass in `.worktrees/ops-coordinator-logs/treeeval-final-check.log`.
Fresh MCP diagnostics for Encoding, Instance, Space and the TreeEval tests are clean. The
rebuilt PDF has no undefined citations or overfull boxes; pages 18 (Tree Evaluation) and 2
(MAJSAT) were rendered and inspected. Documentation configuration and whitespace checks pass.
Only this validation record was appended after the gates; final exact-head review is recorded
in PR #68.

## 2026-10-20: Final truth-table closure integration (PR #69)

Worker `truth-table-wide-gap-20261020` reconciled the prepared entry with independently reviewed
PR #68 head `f5f986b4f5dd2bb4af2b1248d85dfddd23fa0b72` and main
`9b14946fcf33415b4ad4fe7e48910a49c235a65c`. The five source/test files remain byte-identical
to approved source `5df0e7da9798d62d5506dc90e4cb3c2f381b82d9`. Merge conflicts were confined
to roadmap prose, appended bibliography/review records, the entry count, and the generated PDF;
both sides' contributions and source credits are preserved. All other index sections are
byte-identical to final PR #68; the combined index contains 128 entries.

Fresh source/test MCP diagnostics are clean. All six combined gates pass (exit 0), recorded in
`.worktrees/ops-truth-table-prepare/.lake/truth-table-final-check.log`. The PDF builds without
undefined citations or overfull boxes; pages 31 (truth-table closure) and 18 (Tree Evaluation)
were rendered and inspected. The five declaration anchors remain pinned to the approved source
and were rechecked. Only this validation record was appended after the gates. Independent
exact-revision integration and rendered-index review is recorded in PR #69; no human editorial
approval or machine-checked prose equivalence is implied.

# Additive WordRAM compiler: padded-input milestone (20 October 2026)

Author validation by worker `wordram-bridge-20261020`: the added query-section entry is pinned
to Lean source `80a79abcb959601b9a3d570d9c6d3ad347e9f0fe`. The source and boundary clients pass all
six project checks. The four declaration links were checked against that commit and the index
contains 130 result entries. `latexmk` builds the 64-page PDF; rendered pages 1 and 50 were
inspected for the count, new entry and adjacent section transition.

The entry describes the proved additive compiler and its exact logarithmic-cost bound from
an explicitly supplied padded, length-bearing input. It does not describe construction of that
input or the end-to-end element-distinctness corollary as complete; these remain issues #84 and
#81. Coordinator `fusion_barrier` independently reviewed the exact source and tests, then the
draft prose and four anchors, without findings. Final revision/PDF approval is recorded in the
PR review rather than implied to be human editorial approval.


## 2026-10-20: Charged WordRAM bridge and element distinctness

Worker `wordram-bridge-20261020`, assisted by OpenAI Codex, composed the actual input preparer
from worker `ram-input-preparation-20261020` with the fixed additive-memory compiler. Source and
boundary tests at `aec70b38fb3158a09850dc3640fba31e8e312f1e` pass all six project checks, with
fresh MCP diagnostics clean. Independent coordinator `ram-preparation-review-20261020`
approved that exact revision for API, correctness, nonvacuity, cost composition and tests without
findings in issue #81, comment 6300618074. The preparation dependency preserves its original
source commit `890862e155a0c9f87bb98eb8548bd42e19a83ef9` and final PR #87 integration.

The compiler index entry now includes the charged preparation bound with its explicit constant;
one new entry states the fixed-program logarithmic-cost element-distinctness bound of
`2735 * (n + 1) * (Nat.log 2 (n + 1) + 1)`, with the `2448` padded-input variant. Both entries
retain the uncharged external input convention, successful-run and bounded-universe scope, and
absence of a Turing-machine or unrestricted encoding claim. Cook--Reckhow, direct addressing,
the local RAM and lean-trominoes provenance are retained in source, citations and PR text.

All eight declaration anchors were checked against their pinned commits. The index has 131
entries; `latexmk` builds a 65-page PDF without undefined citations or overfull boxes. Rendered
pages 1, 50 and 51 were inspected. Coordinator `coordinator-ops-20261020` reviewed the changed
entries against the source, requested wording that distinguishes a compiled program from
runtime compilation, and that wording was corrected before publication. Final exact-document
approval is recorded in the PR; AI review is not human editorial approval or a Lean proof of
prose equivalence.

## 2026-10-20: Native BIT on arbitrary-base full tuple universes (#112)

Worker `ordered-times-20261020`, assisted by OpenAI Codex, adds a curated entry for
`92915665afb129fbdbe0051fcb4a56c4b994be96`: one native formula for each fixed dimension
realizes BIT of full lexicographic tuple ranks on every canonical `Fin n`, `n ≥ 2`.
The entry records arbitrary-base semantics, full-word indices, high-index rejection, false
zero dimension, exact witness arithmetic and the fixed small-universe branch. It makes no
formula-size efficiency claim, no restricted-domain claim and no completed composition claim.
The preceding numeric entries now point to the completed full-tuple BIT result; their existing
statements and source anchors are preserved. Mathematical credit remains Immerman's Remark
1.32 / Exercise 1.33(3), with a direct link to printed page 25 / PDF page 37.

Independent design reviews and the arithmetic checkpoint review are recorded in issue #112;
that checkpoint approval is not final-source or index approval. Exact full-source correctness,
API and index review, six-gate validation and rendered CI-artifact review are tracked in the
linked PR. This AI review workflow does not imply human editorial approval or machine-checked
equivalence of prose and Lean. Generated PDFs are not committed.

Author validation at source 92915665: all six repository gates passed; fresh focused MCP
checks and the headline axiom guard are clean. The local index builds without undefined
references or overfull boxes, contains 138 result environments at this pre-integration base,
and its new rendered page 12 and three pinned declaration anchors have been checked.
Independent final prose/artifact review is still required; the PR records its verdict.

## 2026-10-20: Canonical full-tuple interpretation composition (#121)

Worker `ordered-times-20261020`, assisted by OpenAI Codex, adds a curated entry pinned to
source `9263445cb6115e5a9f14385cae4ab9fb3d07629d`. The actual native construction combines the
proved full-tuple order, BIT and constant formulas with the existing relational interpretation
and constant-aware pullback. Its canonical rank map preserves the entire ordered language.
Composition flattens `(j,i)` to `j*k+i`, preserving arbitrary-base ranks and all formula and
sentence pullbacks. The entry states positive dimensions, source size at least two and relational
intermediate/output input vocabularies; source input functions are allowed. Restricted-domain
numeric preservation and ordered logspace/capture endpoints remain separate.

Mathematical credit is Immerman's Definition 1.26, Proposition 1.28 / Exercise 1.30 and
Remark 1.32 / Exercise 1.33, with direct source links to the composition and canonical-numeric
passages. Five declaration links point to the fixed Lean source. Preceding numeric entries now
refer to the completed composition result; their statements and previous source pins are preserved.

Fresh Lean MCP checks and all six repository gates passed at that source. Non-vacuous clients
cover unequal dimensions and orientation, mixed input/numeric relations, a BIT index larger than
the source universe, high-index rejection, constants under quantification, the smallest source
size, and the excluded zero dimension. Independent design review is recorded in issue #121;
exact-source/API/correctness, final index and rendered CI-artifact review are recorded in the PR.
These AI reviews do not imply human editorial approval or a Lean proof of prose equivalence.
Generated PDFs remain outside Git.


## 2026-10-20: Native canonical ordered model checking in L (#128)

Worker `ordered-times-20261020`, assisted by OpenAI Codex, adds a curated entry pinned to
source `e7cab391135be9da1becec0fbfd62c63e37853b6`. For each fixed sentence over a finite relational input vocabulary
with genuine canonical 0/1/max/order/BIT, the actual encoded query language belongs to L.
The entry states the source-size restriction, the unchanged unary-cardinality/framed-input-table
encoding and its first-coordinate-least-significant order, rejection of invalid shapes and
sizes zero/one, full-input-length work space, fixed-sentence scope, and the encoding-image
boundary. Ordered interpretation transducers, reduction closure, projections and capture remain
open. The old order-free entry, including its empty-universe behavior and pinned declarations,
is preserved; earlier numeric entries now point to the completed model-checking slice.

Credit is given to Immerman's Theorem 3.1 (direct link to printed pages 57–59), the existing
counter/query/native-machine model checker, and Christian Reitwiessner's native binary arithmetic
and digit-access proof. Focused migration `9bf2748ff4aca3a4740a707a972547f21022de4c` keeps that
proof and statement unchanged, with its authorship and a dated deprecated old full name.
Coordinator review of that prerequisite is recorded in issue #128, comment 6304267267;
it is not approval of the full new endpoint. The native BIT bound charges both binary operands;
no time bound for its potentially long suffix iteration is asserted.

Fresh MCP diagnostics, source gates, independent exact-source/API/correctness and changed-entry
reviews, and the rendered CI PDF/provenance review are recorded in the linked PR. Boundary
clients cover mixed quantified input/numeric atoms, constants in input predicates and equalities,
nested quantifiers, size two and non-power-of-two inputs, high BIT indices, malformed tables,
small-universe rejection and asymmetric binary table orientation. AI review does not imply
human editorial approval or a Lean proof of prose equivalence. Generated PDFs stay outside Git.

Author validation at source `e7cab391`: all six gates and the final boundary clients pass.
The local pre-integration PDF builds without warnings, contains 145 result environments and
77 pages, and changed pages 9, 11, 13 and 14 have been inspected. All 68 existing structure-section
pins are preserved and the four new declaration links have been verified in source and PDF.
Final independent review and the integrated CI artifact are recorded in the PR.


## 2026-10-21: Exact replay of native oracle occurrences (#136)

Worker `counting-machine-scope-20261020`, assisted by OpenAI Codex, adds one curated entry
pinned to source `431701e98547ad45e3b2445a17e35d8231e4ac8e`. It states the explicit positive
uniform local-list length bound and quantifies arbitrary full configurations, clocks,
private state types and deterministic stateful word handlers. The proved equality is of ordered
Lists retaining consumed occurrence indices, complete final configurations and branch-local
private state. Singleton/query instructions are recorded; replies and terminal padding add no
extra occurrence. Raw cutoff retention, separate terminal filtering, both verdict counts,
observer erasure and the two closed-machine compatibility statements are kept distinct.

The entry records the native query/write/access convention, arbitrary stored reply suffixes,
and the absence of an encoded copying or checker-time theorem. Uniform nonvacuous oracle clock
contracts and native #P/GapP oracle characterizations remain open. Fortnow's Section 2 and
Definition 3.1 supply language-oracle/path-counting conventions; the stateful word interface
is explicitly more general. Existing shared-machine, FreeM and occurrence-certificate work is
reused, with its author credits retained in the source modules. Five links target exact
source declarations; prior entries and pins are preserved.

The design-only independent review is issue #136 comment 6304677099. Exact-source/API/correctness,
final semantic-index review, six-gate validation and rendered PDF/provenance evidence are recorded
in the linked PR. AI review does not imply human editorial approval or a Lean proof of prose
equivalence. Generated PDFs remain outside Git.

## 2026-10-21: Charged adaptive RAM controllers (#280)

Worker `worker-controller-20261021` and authoring subagent `/root/controller_scout`, using
OpenAI Codex, add the fixed-code controller refinement and uniform word-valued RAM-time
certificates. The source revision is `73b30ec4371e6bd75592ed6f98d89900f486bcb9`, tree
`3c3baf8d008eb5569abe8584f7577d18f6adeb1d`; it exactly matches the tested local source
`3e4cb7cc8dd4213ba0cdbf38745cad6d84b86157` apart from publication commit metadata.
All six strict gates passed on this source over main `9e161a05` (session 50678, exit 0).
The global axiom audit and four named guards pass. Tests instantiate charged calls, adaptive
argument passing, bind, branches and initialization; reject an insufficient budget; and check
named certificate reuse and separation between RAM and Turing-machine predicates.

Independent nonauthor reviewer `/root/controller_review` approved the final API, correctness,
tests and index against the exact published source. Two documentation nits were resolved:
standard input memory placement is the machine convention, while register loading is charged;
arbitrary refinement entry data requires word-boundedness through its entry assertion.
A representation-preserving source link was added alongside the halting execution link.
The review confirms the fixed continuation code, real argument-preparation executions,
49/29 exact total instructions, empty final stack, numerical-magnitude size parameter,
logarithmic threshold and universal input-fit witness. No arbitrary host-continuation or
Turing-machine simulation theorem is asserted. Quang Dao's FreeM and the existing credited
stack/word-RAM execution substrate are reused; this example is a composition test.

The changed local rendering was inspected independently on pages 84–85, and all five new PDF
annotations were checked against published source lines 84, 155, 170, 182 and 211. PDF SHA256:
`583aaca3cfffc9693bed4b9bf796de9f52695403bca272c05abcdb83436dafe2` (112 pages).
The source and rendered entry have no unresolved review findings. The CI theorem-index
artifact/provenance inspection and coordinator integration approval remain separate gates;
AI review does not imply human editorial approval. Generated artifacts remain unversioned.

## 2026-10-21: Shared-memory FIFO queue (#289)

Source revision: `f21c5d6ea700bfaa2dc3281065c68ff0092738f9`, tree
`8721d18c4395220d3c4b14b22b47607fa8f06114`, identical to tested local commit `ab1df1a1`.
OpenAI Codex worker `worker-stateful-classics-20261021` authored the FIFO model, dynamic
realization, resource packaging and tests; delegated worker `/root/controller_scout` authored
the eleven-register machine and its proofs. CLRS and the existing word-RAM substrate retain credit.

All six strict project gates passed (session 3425): library build, generated import check,
full tests and axiom audit, environment lint, style lint and Init-import check. All affected
files also passed complete Lean MCP diagnostics. Documentation configuration passed; a full API-documentation build was not run.

Independent nonauthor `/root/controller_review` approved final source and tests: Model hash
`d818e6c5fd48c897a69f628dceb442f4899f0548575634020f6b4568c9c61c86`, Basic
`c3e156100280149f4f092efb8145f7cc2e9fc1df7a91e35b466e0127030b2722`, Dynamic
`b17c236f801d2bd75538140aece439096af76c3a5e470eee188084799c5c7c11`, tests
`12491f3dfc086cf65c28acc4392f36fae66e73527aa31ca0e710024ec3ff4cc2`.
Review covered transfer orientation, disjoint live prefixes, bounded addresses and lengths,
framing, empty-versus-zero observations, exact operation costs, arbitrary bounded initial
memory and adaptive execution. No blocking source findings. The index review required an
explicit initial representation hypothesis for the adaptive bound; that correction was made
and re-reviewed. All other model, capacity, reservation and cost boundaries match the source.

Local theorem-index PDF: 115 pages, changed page 86, SHA256
`f7714c6dfc793190b4c33e9e32b2f828858aa3dd52826b75b526299126721e40`.
The worker inspected the rendered page and verified the four declaration annotations at
source lines 324/383 in Basic and 113/143 in Dynamic. Independent reviewer `/root/controller_review` also verified the exact published source,
rendered page and all four links, approving with no remaining findings; index SHA256
`7f99a6773db39936b10568b022be573ce3313ea19b8001997d11a7ce5b5f8433`. Actual CI artifact/provenance inspection remains a separate
coordinator integration obligation. AI review is not human editorial approval; the worker
neither approves nor merges their own PR. Generated artifacts are unversioned.

Scope: initialized operation histories cost at most `6 + 14*m` instructions with retained
final potential, using `2*capacity` reserved words and at most `capacity` live values. External
client computation, argument delivery and result decoding are outside this native-call sum.
This is a direct FIFO implementation, not a compilation of the older abstract queue methods.
Allocation/growth, complete client compilation and TM simulation are separate work.

## 2026-10-21: Stateful unbalanced binary search trees (#290)

Worker `worker-search-tree-20261021`, using OpenAI Codex, adds the finite ordered-set realization,
its executable adaptive client interpreter and shape-dependent node-visit bounds. Source revision
`11744afb1a743008b73935dfd8e11f156f79565b` has tree
`cab7acda3a81e519e5f4816d6d79a22ba5624691`, exactly matching the validated source over main
`7ebefd57bbcfcaa138b3f094d63ae763bd17dd41`. All six strict gates passed (session 40889, exit 0),
including the global axiom audit and five named guards. Actual-file Lean MCP diagnostics,
documentation configuration and whitespace checks passed.

Independent nonauthor `/root/controller_review` approved API, correctness, tests and index
semantics, then checked the exact published source tree, declaration pins and rendered page.
One documentation nit was fixed: only `firstTwo`, not the construction client `insertAll`,
chooses its second query from the first answer. Tests include satisfiable strict ordering,
a malformed-tree counterexample, duplicate tree identity, empty/equal/absent/exhausted queries,
height-three and height-seven shapes, and exact adaptive node-visit traces.

The entry quantifies arbitrary linearly ordered key types, states the strict invariant and
finite-set semantics, and bounds each operation by the initial height and set cardinality.
It explicitly excludes empty-child tests, allocation/reconstruction, comparison implementation
and pure continuation computation; it makes no balancing, logarithmic or RAM-time claim.
The source credits CLRS Chapter 12 and reuses Mathlib's binary trees and the existing Stateful
calculus. The final index SHA256 is
`3ad381d93708f507cbf5bf8d1c1f54aaf652e40c7baee120d26fd20b9c0e7d7d`.

The locally generated PDF has 115 pages; new page 86 was independently visually inspected.
All four PDF URI annotations point to the named declarations in source `11744afb` at
Basic lines 128/260 and Stateful lines 116/161. PDF SHA256:
`7c9195b965aeafb12ce23d55c2940ced8afd40d6133afd3fc9ad6d523b7d730a`.
There are no unresolved source or local-render review findings. Actual CI artifact/provenance
inspection and coordinator integration approval remain separate gates. AI review is neither
human editorial approval nor a Lean proof of prose equivalence. Generated artifacts are unversioned.

### Ordered-set interface factoring revision (#290 / PR #294)

Worker `worker-search-tree-20261021`, delegated by `codex-coordinator-20261021-2200`, addresses
coordinator review 6326622668. The earlier tree-owned interface is now factored into
`Foundations/Data/OrderedSet.lean` and `Foundations/Semantics/Stateful/OrderedSet.lean`, both under
`Cslib.OrderedSet`. These neutral modules import no tree representation or cost module. They
contain the complete optional-minimum contract, total typed finite-set specification and generic
construction/adaptive clients. The BST realization, interpreter and node-visit bounds stay in
SearchTree. No bounded-key vEB realization or machine-time result is added.

Reviewed source `b3aac7104315ae4004236afd3b01df17ddd59220`, tree
`e2943b28dbbe8ebe8930da27c39cc2f2ba04abdb`, is a focused descendant of the prior PR head
`13b5a0fd44b4c0a11a8e8a5bb4a2cc31500895a0`. All six strict gates passed on the final source
(session 36758, exit 0). An initial doc-line-length warning was corrected before that successful
full rerun. The new neutral test driver imports only the shared interface and checks finite keys,
strict/absent/exhausted queries, adaptive traces and a separate bounded insertion-admissibility
specialization. Both test drivers have clean final MCP diagnostics, including the unchanged
BST correctness/height examples and named axiom guards. Documentation configuration and
whitespace checks also pass.

Independent nonauthor `/root/controller_review` approved the exact source, tests and index
semantics and confirmed the prior must-fix is addressed. It independently verified the published
source tree, all six declaration pins and local rendered page 86. The theorem-index source hash is
`9331ac755b303379e8130cebab69c881f07028aab4c1f7a13d58a756a92e13ca`;
the 115-page PDF hash is `39bfb9ca2668638581df674b4d1beea022d6d7e1020092c1a929972c15a903e6`.
The links target neutral declarations at lines 49/56, SearchTree Basic at 130/225 and Stateful
at 91/136. No clipping or overlap was found. The final documentation commit changes no Lean
bytes. Actual final-head CI PDF artifact/provenance inspection and coordinator integration
approval remain separate gates. This records AI review, not human editorial approval.

## 2026-10-21: Mathlib TM2 polynomial-time bridge

Worker `/root`, assisted by OpenAI Codex, adds one entry pinned to source
`670c5abcbfea59068c817ce0ba96c56ff7d09a1f` (tree
`2693c452ed5f7e39b6d229cb1c4c10031bfe2274`). It transfers Mathlib's typed
`TM2ComputableInPolyTime` certificate to the tidy binary multi-tape calculus.
The statement requires injective typed word encoders and finite working alphabets;
input and output alphabets may differ or be empty. It specifies the existing unary-rank,
framed-word encodings and polynomial time and space in encoded input length. It does not
claim quadratic overhead, preservation of a separate source space bound, or a converse
class equivalence. The direct configuration proof is independent of Complexitylib PR #72;
its regression examples informed the new tests.

Independent nonauthor agents `/root/tm2_api_review` and `/root/tm2_correctness_review`
approved the API, correctness, nonvacuous examples and semantic index statement. Optional
requests for nonidentity alphabet conversions and concrete nonpalindromic outputs were
implemented and re-reviewed. The final source and test contents are those in the pinned
commit; no findings remain unresolved. `/root/tm2_design_review` contributed source code
and is not counted as an independent reviewer. Existing entries and their pins are preserved.

`python3 scripts/build_paper.py` built the local 115-page index. The author and independent
reviewer `/root/tm2_api_review` inspected page 25 and checked its PDF annotation against the
pinned source declaration at line 150. PDF SHA-256:
`05b2da8072118e52a4f25d480337894635006693e8cc822f2647d3b27095e3b8`.
Reviewed `paper/sections/space.tex` SHA-256:
`40fc13984ce778b4e687a5e8fdee5e7c8167e20e7046c51fdd2c4ce8c934b8c8`.
This is local rendering evidence; the CI theorem-index artifact/provenance review and
maintainer integration approval remain pending. AI review does not imply human editorial
approval or a Lean proof of prose equivalence. Generated artifacts remain unversioned.


## 2026-10-22: Terminating Mathlib TM2 computations within polynomial space

Worker `/root`, assisted by OpenAI Codex, adds the polynomial-space entry pinned to source
`d519401281aca7ebe881ae9ea21b08991d4b9acf`, tree
`77cc631dfb1c518c2d90e5e4b07d915a1a49bb7f`, on base `126a59b7`. It starts from a
`TM2Computable` termination/correctness certificate with finite working alphabets and
injective typed encoders. A polynomial bound on each stack over every source configuration,
including initialization and padded halting, suffices. Input and output stacks both count.
No source runtime bound or computability certificate for the space-bound function is required:
a polynomial majorant gives an exponential clock, stored in binary, through a finite
configuration-counting argument. The conclusion is tidy polynomial-space computation under
standard binary word encodings; the Boolean adapter gives native `PSPACE` membership.
Polynomial overhead is asserted, without linear overhead, a sublinear work-space simulation,
or a converse class equivalence.

Authoring subagent `/root/tm2_design_review` contributed configuration counting and regression
proofs and is not an independent reviewer. Independent nonauthor agents `/root/tm2_api_review`
and `/root/tm2_correctness_review` approved the source, exact tests and semantic index entry.
A missing References section and a declaration-line pin were fixed and re-reviewed. No findings
remain unresolved. Test SHA-256 is
`39c36614b820cf596728038c52595faabe5ffa3bc42ff91d147052f581dbca0b`; examples include
termination-only certificates on infinite input domains, an explicit exponential binary clock
with early-halting padding, empty alphabets, distinct Boolean-input/empty-output stacks and
Boolean answer recoding. Three named axiom guards permit only the standard three axioms.

On this source, the full strict library build (11241 jobs), all 358 test modules and their
aggregate driver (11962 jobs), global axiom audit, environment/style lint and public Init-import
audit passed. Import generation checks passed for both explicit library roots. Windows default
`mk_all` and `lint-style` commands hit duplicate `Lake.packageAttr` workspace registration;
the equivalent explicit-root and exact-option checks passed. The first global axiom audit
failed with resource exhaustion/no space left on device; a retry alone passed without code
changes once disk space was available. Failed attempts are not counted as successful checks.
Python maintenance tests (18), documentation configuration and offline upstream synchronization
passed. API documentation generation retains the previously identified missing native `cc`
prerequisite; generated API coverage was not checked. Full command evidence is in the code
commit description.

The local theorem index builds as 115 pages. The author and independent nonauthor reviewer
`/root/tm2_api_review` inspected page 25 and verified its three PDF annotations against the
pinned source declarations at lines 118, 75 and 39; no rendering or link findings remain. PDF SHA-256:
`c1de2cccbf55e0682222256d4099c0b69355dbe9af044b2e2134cad3f0bbf99b`.
Final `paper/sections/space.tex` SHA-256:
`00efb4d2ae8bd0d89476f341918624a92f268737c7a6f7adf2de49528f4093b8`.
Local provenance records the source commit and a dirty documentation tree. Independent final
pin/render review is recorded in the companion documentation commit. CI artifact/provenance
review and maintainer integration approval remain separate gates; AI review is not human
editorial approval or a Lean proof of prose equivalence. Generated artifacts remain unversioned.
