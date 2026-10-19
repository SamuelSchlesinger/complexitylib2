# Human-readable proof companion

This manuscript translates the arguments actually used in the Lean formalization.
The draft contains an annotated coverage plan and Cook–Levin and sparse-counter proof translations;
other chapters are proposed, not completed translations. Samuel controls the wording,
selection and organization. The copy remains a working draft for editorial discussion.

Build from the repository root:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -cd paper/main.tex
```

Output: `paper/main.pdf`. Sources share the repository's `references.bib`.
Edit `sections/outline.tex` for scope, `sections/cook-levin.tex` for Cook–Levin, and
`sections/sparse-counter.tex` for the sparse-counter argument.
Cook–Levin links to the proof route at library revision `263e7321`; the sparse-counter
section links to `904ac4e1`.
It treats the local machine step-equation lemma and compositional resource rules
as named prerequisites; it does not claim to translate all imported proofs.

Every AI-authored PR must synchronize affected exposition, including proof changes
that preserve theorem statements, and obtain independent AI review against the final
Lean revision. See AGENTS.md and CONTRIBUTING.md for the repository policy. Record
no-impact assessments explicitly for changes without mathematical/expository effects.
An AI review is not a machine-checked equivalence proof or human editorial approval.

This draft was prepared with Codex assistance. Review evidence is recorded in
`review.md`; proposed coverage must remain distinct from completed translations.
