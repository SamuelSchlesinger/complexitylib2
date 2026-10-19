# Theorem-index review

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
