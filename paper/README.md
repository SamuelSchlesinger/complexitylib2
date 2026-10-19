# Index of proved statements

`main.tex` and `main.pdf` present a curated, human-readable index of 72 entries covering significant
results, grouped by subject. Each entry states the result, its assumptions
and model, important limitations, and links to exact Lean declarations. It is not
an exhaustive API reference. Standalone entries emphasize substantial endpoints;
coordinate-transfer corollaries and supporting constructions stay with the results
they support, and basic membership facts may appear as short contextual notes. Samuel controls selection, organization and wording.

`sections/statements.tex` lists the subject files in reading order. Edit the relevant
subject file in `sections/` to revise or extend the index. Declaration links point to reviewed library revision
`8d38f7753b6c651c3363a157c806d05794d6ea11`, or `811ad02abdab6bc2b9f945d58d2a1ff2ed1c282b`
for the first-order projection entry, and `4f6bdaf35ebe60aec6d1063ae513ac342df13589`
for the basic class developments, and `2f492c03c060ed95662dd942ef7feca1bebda7aa`
for the small counting classes, and `814e76e29fa938afaed4e1bd5763fa490bc39ca9` for wide gaps and the Boolean
hierarchy; review evidence is
recorded in `review.md`.
Earlier proof translations remain available in Git history at `d2c5e581`.
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
