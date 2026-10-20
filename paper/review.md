# Theorem-index review

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
The sampling source and tests are unchanged; declaration links remain pinned to `503ce2b0`.
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
and headline-bound links point to lines 66 and 131 of the source revision above. All three
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
