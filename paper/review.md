# Theorem-index review

## Selection and missing results, 19 October 2026

Scope: documentation-only delta from `dac6e41b7f8928a1124b81a6967328426eca03ad`.
The index now has 50 numbered entries in 12 subjects, 78 declaration links,
and 61 references in 19 pages. All links still target the unchanged Lean source
at `cec38657ddf1b93dd1be123e86d0ecdd9728c610`. The full prior 48-entry review
is preserved in Git at the base revision; unchanged entries retain that review.

The additions cover Shannon--Lupanov/MCSP bounds, quadratic-form correlation,
weighted-threshold activity and capacity, polynomial PRG stretch with quantitative
resources, general input-time iteration, and shared-table batched iteration.
An unnumbered containment map connects the existing class results.
Circuit Value membership is now a contextual note. The two sparse-counter
coordinate-transfer statements and the cycle-label construction are grouped with
their main results; their mathematical statements and links are preserved.

Three independent Codex reviewers compared the changed entries against the actual
Lean statements and underlying definitions:

- `proof_api`: the three added circuit entries, including precise MCSP thresholds,
  correlation quantifiers/coefficient, positive-arity cost, effective threshold
  coefficients, activity and readout restrictions, both-fiber rectangle hypotheses,
  citation correspondence, and all seven new declaration anchors.
- `proof_correctness`: PRG stretch and its exact time/workspace certificate, all
  arrows and common encoding in the containment map, and the Circuit Value note.
  Checked the new declaration links and the primary length-extension source.
- `resume_alternation`: general input-time and batched iteration, preservation of
  all sparse-counter claims after regrouping, all ten iteration declaration links,
  the 50-entry count, and the README's selection policy.

Resolved findings:

1. Replaced an absent Goldreich bibliography key with the existing `Barak2016PRG`
   source credited by the linked PRG-stretch module.
2. Corrected the correlation theorem link to its declaration's first line, 279.
3. Added direct links for the P-to-NP and NP-to-PH arrows in the containment map.

All three reviewers approved their final mathematical scope. Subsequent layout
changes split long groups at supporting statements, moved each pair of activity
links beside its claim, and made declaration links ragged-right. References flow
after the last result to avoid a nearly empty page. No mathematical finding remains.
Review is correspondence checking, not a new proof audit or a machine-checked
prose equivalence. No human editorial approval is implied.

Validation:

- `latexmk -pdf -interaction=nonstopmode -halt-on-error -cd paper/main.tex` passed;
  the final log contains no warnings or overfull/underfull boxes.
- Rendered and visually inspected every final page. Verified final pages 1--14
  pixel-identical to their inspected render after the last bibliography-layout
  change, and inspected final pages 15--19 separately.
- Checked all 78 fully qualified names against the compiled declaration index,
  their exact declaration-line anchors against `git show` at the pinned revision,
  and the corresponding URLs in actual PDF annotations. Every linked Lean file
  still matches that pinned source exactly.
- Verified 50 numbered entries, 12 subject sections, 61 references, and
  `git diff --check`. No Lean source, dependency, or bibliography entries changed.
- No Lean builds were repeated for this documentation-only delta. The original
  library baseline passed the six project gates; current CI is recorded in the PR.

## Reviewed SHA-256 hashes

```text
03f3ee1840d3aff3534f232be510aef60d392869ace2a32464423f6183e77192  paper/main.tex
f50826dd029dee289f6f60872e87e9e53dca142c307587633461c6c6451f52ef  paper/README.md
5fefaa60bf1ed9cd83205d12a91752ccbefefc87cf0ce1b24f670b8624d75849  paper/sections/analysis.tex
1f0364a48e180b4ab4119c8e1f3ac79ed5a6e83e9edfb710254b776d0e02aaac  paper/sections/circuits.tex
32edc7e3310bffccb3cb6e8485b3f2a72de89a67dbeacbcd2a25511b6e184ba2  paper/sections/coding.tex
56a77e130a465246f04c79f455c25ff54922ea05202090e2b7a7f4e19f173cbd  paper/sections/communication.tex
9e97be44f5295ae00274c1ceb48ba80e320aa66a8f8d213f296cb0646230eec3  paper/sections/completeness.tex
6de8f7822423efdb334ecd9e2c05eed325685025a825fb713a845670b17f07b4  paper/sections/crypto.tex
bd7eb9e9d9744b5f5cec6f18135b0a0f92dd6a30878be7ed3c462c03cdc9df2f  paper/sections/iteration.tex
541179288b86a3e5f99131f7c6bebffcb8a82af4838e91ca81fcbf25432f1216  paper/sections/proofs.tex
7c9fbae2cfcdc99d364f0b74cc89f481367d4c58e79344d0818d4d031d0fcf11  paper/sections/randomness.tex
e17d0f2eb2b26f30258c32b6582fa0ba91bfd9cb1fdbbd74b2bf60e2af0505b5  paper/sections/space.tex
1f91c79f59dffd890e5c49712eb254ad39646781f18ad3377ce15d6c17546391  paper/sections/statements.tex
ccd3ee5a924c3bcaa884751b2b618d5911d6aca4972df5840f85c7523204ca0b  paper/sections/structure.tex
cbb8084fa13318bb9b3408d76e042bd49d3c37d326447d71a036b810250b08b1  paper/sections/synthesis.tex
```
