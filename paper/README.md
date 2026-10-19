# Index of proved statements

`main.tex` and `main.pdf` present a curated, human-readable index of sixteen
landmark results, grouped by subject. Each entry states the result, its assumptions
and model, important limitations, and links to exact Lean declarations. It is not
an exhaustive API reference. Samuel controls selection, organization and wording.

Edit `sections/statements.tex` to revise or extend the index. The original entries link to library revision
`d2c5e5812794ca1a39cf126de44e236789623215`; the variable-time entries link to the
implementation revision recorded in `review.md`.
The earlier proof translations remain available in Git history at that revision.
Outstanding development priorities belong in `../ROADMAP.md`, not as speculative
chapters in the index.

Build from the repository root:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -cd paper/main.tex
```

The bibliography is shared with the library (`../references.bib`). Every AI-authored
PR must check the index and update affected statements, assumptions, limitations
and links; new headline results need entries. Proof-only changes with unchanged
statements and scope may record a no-impact assessment instead. See AGENTS.md and
CONTRIBUTING.md for the policy. Changed entries require independent AI review
against the final Lean definitions and statements, plus PDF build and visual checks.

Prepared with Codex assistance. Review evidence is in `review.md`; an AI review is
neither a machine-checked equivalence proof nor human editorial approval.
