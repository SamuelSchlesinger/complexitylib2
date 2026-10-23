# Contributing

Follow CSLib's [contribution guidelines](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md)
and [code style](https://github.com/leanprover/cslib/blob/main/CODESTYLE.md).
The pinned copies are in `.lake/packages/cslib/` after fetching dependencies.
[AGENTS.md](AGENTS.md) records the local file, proof, validation, and review requirements.

## Proposing and contributing work

Use this repository's Issues or pull requests to agree on a substantial development
before implementing it.
State the mathematical endpoint, cite its source, identify existing APIs and missing dependencies,
and propose a first independently useful milestone. [ROADMAP.md](ROADMAP.md) lists open directions;
an item there is not an assignment or a claim that its prerequisites are complete.
Small fixes and API improvements can go directly to a pull request.

Keep a pull request small enough to review as one mathematical or engineering change. Include a
checked client for a new API and instances showing that bundled hypotheses can be met. Preserve
the original authors and licenses when porting code; cite mathematical sources in module
docstrings through [references.bib](references.bib).

Develop against representative clients and state the public contract: model or encodings,
mathematical behavior, and resource or security claim. Test automation on ordinary expressions,
alternative encodings, and important failure cases. Distinguish correctness, executability,
certified efficiency, and security in declaration docstrings.

For documentation-only changes, check links, claims against source, and Lean examples with the
imports shown. Record the scope of validation and review accurately.

## AI assistance and review

AI-assisted and human-written contributions follow the same standards. Disclose which AI tools
you used and for what in the PR description. The contributor is responsible for the result and
for resolving review findings; a generated proof or review is not evidence of human approval.
Maintainers decide scope and acceptance, and arrange the independent API and correctness reviews
required by [AGENTS.md](AGENTS.md#review-cycle). Contributors need not install a maintainer's
agent tooling to submit a change.

Run `scripts/check.sh` for the six project checks. The test suite audits the axiom dependencies
of every declaration stored in imported `Complexity` modules; the named headline checks remain
readable regression tests. This trusts the compiled Lean artifacts and permits `Classical.choice`;
it does not certify efficient computation or agreement with a textbook statement.

For concurrent local validation, choose a thread budget for the shared host, for example
`LEAN_NUM_THREADS=2 scripts/check.sh`. Lean's
[thread-pool setting](https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/)
defaults to the number of logical processors and is not a hard process or memory cap; check the
observed concurrency and memory use. Keep mutable build outputs separate between worktrees
(for example with `scripts/worktree.sh create <branch> [dir_name]`, which seeds `.lake/build` from
the root checkout and, when `<branch>` exists only on `origin`, checks it out tracking
`origin/<branch>`). Run `python3 scripts/check_hygiene.py` to audit `-- upstream:` markers,
forbidden proof tokens, and `set_option` justifications (pass `--check-simp` to also run the
heuristic check for non-terminal bare `simp` calls in candidate modules).

The helper hard-links package sources by default, but copies root and dependency build caches
with independent files, including symlink targets. Do not edit shared package sources; use
`--copy-cslib` or `--copy-packages` when those sources must change. Seeding preserves existing
destination caches and does not repair worktrees created with shared dependency caches by an
older helper; use a fresh worktree for isolated validation.

Coordinate with a run's owner before rescheduling it, preserve completed artifacts, and record
an interrupted run as incomplete. A fresh run must pass all six strict checks on the final revision.

Record validation and review in the PR, or in the commit description for work without a PR:
the tested revision (or base revision and exact diff), commands and outcomes, reviewer/tool and
scope, findings and their resolution, and any remaining limitations. Preserve enough evidence
there for another contributor to assess the change; a path into a local `.lake/` directory is not
a durable review record. Recheck changes made after review and identify the final reviewed revision.

## Documentation

Keep each fact in one maintained location. The README explains the purpose and points to useful
entry points; module docstrings explain the mathematics and API; checked Lean examples show
usage. ROADMAP records outstanding work; UPSTREAM records coordination and exceptional integration
decisions, while source markers record module status. Batch measurements and validation/review
evidence belong in commit or PR descriptions.
Link to these sources instead of repeating them in new guides. Add a separate document only when
it provides useful explanation that does not already have a suitable home.

The [README](README.md#build-and-use) explains how to generate API documentation using
[doc-gen4](https://github.com/leanprover/doc-gen4). Its separate `docbuild` project shares the
library's toolchain, bibliography and dependency checkouts. After changing library dependencies,
run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d docbuild update complexitylib`. When changing Lean,
also update the doc-gen4 tag in `docbuild/lakefile.toml` and run
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d docbuild update doc-gen4`.
Commit the refreshed documentation lockfile and run the documentation checks and build.

## Maintaining the headline abstracts

The small selection in [abstracts/catalogue.json](abstracts/catalogue.json) is the public headline
catalogue. Every selected result has a checked Lean abstract and bridge, with explicit definitions,
models, encodings, hypotheses, bounds and limitations. The library contains many other results;
selection is an editorial decision, not an automatic consequence of adding a theorem. A headline
must establish a substantial full endpoint with conventional semantics and nonvacuous premises.
Keep incomplete endpoints in `ROADMAP.md` and credit mathematical and formalization sources.

Every AI-authored PR must assess its final Lean changes against the selection. Update affected
abstracts and scope notes, or explain why the catalogue is unaffected. Proof-only changes with
unchanged statements and scope can record that assessment without rewriting the abstract. Follow
the repository's `lean-abstract` skill, import new abstracts in `ComplexityTests.lean`, and run their
`#check_abstract` audits. Allow only narrow, explained foundational models; do not allowlist the
result's class definitions or construction to evade a self-contained statement.

Arrange independent API, correctness and abstract reviews against the final source revision.
Reviewers must check quantifiers, semantics, encodings, bounds, nonvacuity and readability. Record
reviewers, exact revisions, findings and resolutions. These checks supplement Lean's proof checking;
they are not a proof that the English interpretation is equivalent or human editorial approval.

Run `python3 -B scripts/build_abstracts.py --check` to check the selection. The **Formal abstract
PDFs** workflow generates individual PDFs and a combined catalogue with source digests, revision
provenance and exact declaration links. Inspect its rendered pages and links before integration,
recording the artifact/run and source revisions. Local generation is supported; see
[the build guide](abstracts/README.md). The `formal-abstracts` release publishes the latest main
build. Generated TeX and PDFs stay untracked; the former paper/TeX index has been retired.

## Upstreaming

```bash
python3 scripts/upstream.py Complexity.Computability.DecisionTree.Basic --cslib ../cslib --dry-run
```

This previews copying a module to its mirrored CSLib path, rewriting imports, and removing the
upstream marker. Omit `--dry-run` to prepare the worktree and regenerate its root imports.
The script writes whole files; integrate additions to existing files and alternative destinations
manually.
Validate there according to CSLib's current instructions before opening a PR. Record its number
and head SHA in the module's `-- upstream:` marker.

Coordinate cross-cutting abstractions with CSLib before proposing them upstream. Follow
[AGENTS.md](AGENTS.md#staying-current-with-upstream) for pin updates, synchronization checks,
and removal of superseded local copies.
