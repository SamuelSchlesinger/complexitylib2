# Theorem-index review

Scope: the thirteen entries in `sections/statements.tex` and their model conventions
in `main.tex`, against library revision
`d2c5e5812794ca1a39cf126de44e236789623215`.

Reviewed SHA-256 hashes:

- `sections/statements.tex`:
  `8591e5917848566e8040bc0908da702c651ac6813936d4b42029bcfba94ff42c`
- `main.tex`:
  `85ac555e65cb29cc01760e63e7d21b4bf86f9cab68d163cd7693eee3d9aa7534`

Two independent Codex reviewers approved the final snapshot:

- `proof_correctness` checked all thirteen statements against the formal definitions,
  including encoded classes, tidy reductions, PCP constant multiples, native space
  and alternation models, IP thresholds and private coins, Toda's oracle quantifiers,
  the determinant's ring-general bound, and sparse circuit quantifiers and costs.
- `proof_api` checked index organization, scope, all declaration links, and consistency
  among AGENTS.md, CONTRIBUTING.md, the PR template, ROADMAP.md, README.md and the paper
  guide. The policy maintains a curated statement index and permits documented
  no-impact assessments for proof-only changes preserving statements and scope.

Resolved findings: corrected the three sparse theorem line anchors; credited
Moreno and Rivera specifically for their related block characterization; clarified
that Toda's target class has no separate query-count parameter (polynomial time
still bounds interaction). Both reviewers approved the final wording. No findings
remain. All sixteen declaration links target the exact named declaration at the
pinned revision, and all linked source files match that revision locally.

Validation: `latexmk -pdf -interaction=nonstopmode -halt-on-error -cd paper/main.tex`
succeeded. The final LaTeX log has no warnings or overfull/underfull boxes. The
authoring agent rendered and visually inspected all five pages, including the
revised counting page, and ran `git diff --check`. No Lean files or dependencies
changed, so Lean builds were not repeated locally for this documentation-only change.

This is a statement-index review, not a new audit of the Lean proofs or a formal
proof of prose equivalence. No human editorial approval is claimed. Samuel retains
control over selection and wording. Earlier proof translations and their reviews
remain in Git history at the pinned library revision.

## Sparse-counter variable-time circuits

The three entries in section 5 and the updated conventions in `main.tex` were
independently reviewed by Codex agent `resume_alternation` against implementation
`6bbebfe6d438e495f3981b9d6d1734d936bcc5af`. Verdict: approve, no findings.
The preceding thirteen entries are unchanged. The reviewer checked the two
quantitative bounds, the charged coordinate conversions, the state/time input split,
zero widths, numeric representative order, phase direction and nonuniform scope.
All three new declaration anchors match the pinned source. The updated roadmap
correctly leaves sparse navigation, visit schedules, hitting times, affine controllers
and hard-power counting outstanding.

Reviewed SHA-256 hashes:

- `sections/statements.tex`:
  `0397532c33c2b53ad8b17b9576d216609595b7f164cd46765a9959a930695441`
- `main.tex`:
  `f09eeeee22179b4bd7c0bfd8855a6a6a90027014364cd6443b6fc2a13dc4c02b`
- `../ROADMAP.md`:
  `78f883d658e582069de4517cf40f211b37f03e6c1827cc5378c44e9ad5699414`

The six implementation gates passed, and independent Codex API and correctness
reviewers approved the exact implementation commit. Resolved findings clarified
reduced-residue preconditions and additive constants in summary bounds; the full
linter also identified a redundant global simp attribute, which was removed.
The named theorem remains available. No mathematical endpoint was weakened.

The six-page PDF builds without warnings or overfull/underfull boxes. The authoring
agent rendered and visually inspected every page and checked all nineteen pinned
Lean declaration links. The index now contains sixteen entries. This review does
not claim machine-checked prose equivalence or human editorial approval.
