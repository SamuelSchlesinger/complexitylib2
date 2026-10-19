# Theorem-index review

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
