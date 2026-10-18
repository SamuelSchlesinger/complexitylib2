# Contributing

Follow CSLib's [contribution guidelines](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md)
and [code style](https://github.com/leanprover/cslib/blob/main/CODESTYLE.md).
The pinned copies are in `.lake/packages/cslib/` after fetching dependencies.
[AGENTS.md](AGENTS.md) records the local file, proof, validation, and review requirements.

## Proposing and contributing work

Use this repository's Issues to coordinate a substantial development before implementing it.
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
