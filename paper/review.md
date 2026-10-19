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
