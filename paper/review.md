# Theorem-index review

## Comprehensive tour, 19 October 2026

Scope: all 48 entries in the 12 subject files included by `sections/statements.tex`,
the conventions in `main.tex`, and the editing guide in `README.md`. All 62 Lean
declaration links target the single library revision
`cec38657ddf1b93dd1be123e86d0ecdd9728c610`. No Lean source or dependencies changed.
Earlier 13-entry and 16-entry index reviews remain in Git history at that revision.

Three independent Codex reviewers compared the entries with the actual theorem
statements and underlying definitions, rather than relying only on module summaries:

- `proof_correctness`: completeness, structural complexity, space/interaction,
  randomness/counting and cryptography (23 entries). Checked encodings, machine
  and oracle models, quantifiers, numerical bounds, security assumptions, citations
  and all 30 declaration anchors in these subjects.
- `proof_api`: circuit depth/lower bounds/barriers, proof complexity, communication
  and arithmetic/simultaneous computation (14 entries). Checked circuit and formula
  costs, natural-proofs security quantifiers, expanded monotone-clique error budgets,
  rounding conventions, mass-production cutoffs, citations and 19 declaration anchors.
- `resume_alternation`: Boolean analysis/expanders, coding and iteration (11 entries),
  plus overall organization and the editing guide. Checked normalized norms, field
  generality, decoder correctness versus runtime, fixed/input-time quantifiers,
  all 13 declaration anchors, and the 48-entry/12-subject count.

Resolved findings:

1. Made the OWF experiment explicit: uniform n-bit input, unary parameter, and
   success for any preimage, without a length-preservation premise.
2. Specified PRF key/query/output lengths, malformed-query behavior and empty
   auxiliary input in the security experiments.
3. Specified Fagin's unary universe cardinality and framed relation truth tables,
   including rejection of malformed tables.
4. Clarified that formula leaf counts exclude constants, and separated Spira's
   zero-input-leaf case from the positive-argument logarithm.
5. Corrected an iteration cross-reference after reorganizing the subject sections.

All three reviewers approved the corrected snapshot and subsequently verified
that the final pagination changes only added layout wrappers and whitespace.
No findings remain. The authoring agent performed the PDF visual review; the
independent reviewers did not run Lean builds or inspect rendered pages.

Validation:

- `latexmk -pdf -interaction=nonstopmode -halt-on-error -cd paper/main.tex` passed.
  The final log has no warnings or overfull/underfull boxes.
- Rendered and visually inspected all 16 pages, including all four reference pages.
  The initial render exposed stranded links and a split contents list; keeping each
  statement with its links and compacting the contents resolved those defects.
- Checked all 62 fully qualified names against the compiled declaration index and
  all line anchors against `git show` at the pinned revision. Linked source files
  match that revision exactly. Checked that all 62 expected URLs occur as actual
  PDF link annotations.
- Verified 48 numbered entries, 12 subject sections, 53 bibliography entries,
  and `git diff --check`. Citations resolve without missing-key warnings.
- No Lean builds were repeated locally: this change only edits the theorem index
  and its review/usage documentation; the underlying library revision already
  passed the six project gates. Repository CI is recorded in the pull request.

This is a review of correspondence between prose and formal statements, not a new
audit of every Lean proof or a machine-checked equivalence proof. No human editorial
approval is claimed. Samuel retains control over selection and wording.

## Reviewed SHA-256 hashes

```text
f34ae14c312693049be6c5c185553100fef92d925543cf9ef1c98d82b1a359bf  paper/main.tex
c784211d766ae6abd5e9ecc90645c74a884460432cea8449e465e91cb4084aa2  paper/README.md
5fefaa60bf1ed9cd83205d12a91752ccbefefc87cf0ce1b24f670b8624d75849  paper/sections/analysis.tex
4a1e3d82c0bde217258f2e9e5b5de195203e76bf923e0db5643ee58b028f6520  paper/sections/circuits.tex
32edc7e3310bffccb3cb6e8485b3f2a72de89a67dbeacbcd2a25511b6e184ba2  paper/sections/coding.tex
56a77e130a465246f04c79f455c25ff54922ea05202090e2b7a7f4e19f173cbd  paper/sections/communication.tex
ff032d954d5bd16445aac5b6c8022cb182085581e933fd3e7e6cfc481d513c61  paper/sections/completeness.tex
3489e8817ec266ece37958eabf35a0a25a5fb374cf384f011c3900516e83ec02  paper/sections/crypto.tex
1ce5bcf5171c38c8874ee83f4246c35d82ac1ca7cd3c48d66a4b3f3cd660bf04  paper/sections/iteration.tex
541179288b86a3e5f99131f7c6bebffcb8a82af4838e91ca81fcbf25432f1216  paper/sections/proofs.tex
7c9fbae2cfcdc99d364f0b74cc89f481367d4c58e79344d0818d4d031d0fcf11  paper/sections/randomness.tex
4cb75c959697c9d2317c5413160e3440a822b92791c849701db73e21687c3389  paper/sections/space.tex
1f91c79f59dffd890e5c49712eb254ad39646781f18ad3377ce15d6c17546391  paper/sections/statements.tex
ccd3ee5a924c3bcaa884751b2b618d5911d6aca4972df5840f85c7523204ca0b  paper/sections/structure.tex
cbb8084fa13318bb9b3408d76e042bd49d3c37d326447d71a036b810250b08b1  paper/sections/synthesis.tex
```
