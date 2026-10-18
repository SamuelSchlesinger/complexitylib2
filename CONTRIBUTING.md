# Contributing

Follow CSLib's [contribution guidelines](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md)
and [code style](https://github.com/leanprover/cslib/blob/main/CODESTYLE.md).
The pinned copies are in `.lake/packages/cslib/` after fetching dependencies.
[AGENTS.md](AGENTS.md) records the local file, proof, validation, and review requirements.

## Proposing and contributing work

Use this repository's Issues or the coordination board below to agree on a substantial development
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

Record validation and review in the PR, or in the commit description for work without a PR:
the tested revision (or base revision and exact diff), commands and outcomes, reviewer/tool and
scope, findings and their resolution, and any remaining limitations. Preserve enough evidence
there for another contributor to assess the change; a path into a local `.lake/` directory is not
a durable review record. Recheck changes made after review and identify the final reviewed revision.

## Coordinated agent work

An agent can join by receiving the instruction **"become a worker in complexitylib"** in this
checkout. [AGENTS.md](AGENTS.md#coordinated-workers) defines its operating loop. The Lean executable
behind `scripts/coordinate` stores assignments, leases, reports, and exact-commit reviews on the
Git branch `coordination`. It needs the repository's Lean toolchain, Git, and push access; SSH is
sufficient, with no GitHub API token or pull request required. It builds independently of the library.

Each agent uses its own linked worktree, branch, and build directory. Joining creates
`.worktrees/NAME` from remote `main`; `--here` instead registers an existing linked worktree.
Choose a unique lowercase name. Commands after joining run inside that worktree:

```bash
scripts/coordinate join worker-alice
cd .worktrees/worker-alice
scripts/coordinate status
scripts/coordinate heartbeat
scripts/coordinate start assigned-epic
# Implement, validate, commit, then push the branch printed by status.
git push -u origin HEAD
scripts/coordinate ready assigned-epic 'Result, checks, source credit, and remaining limitations'
```

The coordinator initializes the board with `scripts/coordinate init` once and joins with
`join NAME --coordinator`. It records each epic's endpoint, acceptance criteria, source paths,
and dependencies, then assigns it to a registered worker. Include any test files in the scope.
Overlapping assigned scopes are rejected; generated root imports are the shared exception.

```bash
scripts/coordinate plan scan-api 'Endpoint and acceptance criteria' Complexity/Path ComplexityTests/Client.lean
scripts/coordinate assign scan-api worker-alice
# After submission, assign two independent agents, neither of whom contributed to the epic.
scripts/coordinate assign scan-api worker-bob api
scripts/coordinate assign scan-api worker-carol correctness
```

Workers own their development's design and may delegate within its assigned scope, using separate
worktrees and disjoint file ownership. Record every contributor; an implementation subagent cannot
provide an independent final review of that work. The coordinator can send guidance without
replacing worker reports or revoking claims, and can revise an unsubmitted goal or add paths:

```bash
scripts/coordinate instruct scan-api 'Use the existing encoded loop contract; report missing lemmas'
scripts/coordinate revise scan-api 'Revised endpoint and acceptance criteria' Complexity/AdditionalPath
```

`revise` retains all existing paths and dependencies. Assigned epics cannot expand into another
assigned scope; future unassigned plans may overlap until assignment. It preserves the worker's
branch and claim; a submitted plan must be reopened
before revision. `instruct` is advisory and does not change the acceptance criteria or approvals.
Both commands leave completed records unchanged. Read coordinator guidance in `status --json`
even when using an older checkout whose dashboard does not display it. At clean implementation
checkpoints, merge current `main` to pick up shared APIs and tooling updates.

Land large developments in independently useful milestones. Before submission, the coordinator
records the remaining development as a continuation epic, then revises the current epic to the
milestone actually delivered. A milestone's completion does not claim the whole development is
finished. Its continuation may depend on the milestone via `plan ... --after EPIC`.

Reviewers run `start EPIC api` or `start EPIC correctness`, which checks out the submitted commit
in their own clean worktree. They record their review with
`review EPIC KIND BASE HEAD approve|changes 'Scope, evidence, findings, and limitations'`.
`note EPIC KIND 'Progress or blocker' --blocked` is available to both authors and reviewers.
Starting a review again withdraws its previous verdict. The coordinator uses `reopen EPIC REASON`
before revision; this invalidates reviews and any pending integration. The author restarts, merges
current `main`, validates, pushes normally, and submits again. Never force-push these branches.

`land EPIC` is coordinator-only. It checks out the reviewed commit, runs all six project checks
and the coordination tests, and atomically publishes both `main` and the completed board record.
It requires two independent approvals of that exact base and head. A moved `main`, withdrawn review,
lost lease, dirty worktree, or failed check prevents landing. Servers without atomic push support
are rejected. Validation failures retain the reservation for retry; `cancel` releases it.

Sessions last four hours by default (`join --minutes N` changes this). Heartbeats renew only held,
unexpired generations. After expiry plus a one-minute grace period, `join NAME --here --takeover`
creates a fresh session; the coordinator reassigns or reopens work as appropriate. Coordinators
also pass `--coordinator`; repeat a nondefault `--minutes` value when retrying.
`assign ... --replace` explicitly revokes a live claim. `unassign EPIC REASON` releases its scope while preserving
authors and the previous branch as a continuation point. Push partial work before a planned handoff.
If a command loses its network response, inspect `status` to determine whether it succeeded.
Joining and acquiring work or integration claims can be retried with the same arguments because
their pending identities and tokens survive locally. For other commands, reconcile the recorded
state before retrying; a submitted review or completed landing may already be present.
A definitive rejection leaves existing work intact.
To change the role or duration after a rejected join, repeat it with `--takeover`; a pending
identity is replaced only when the board shows it was never accepted, was replaced, or has expired.
Mutating commands take a worktree-local lock. After an interrupted process, inspect the lock's
`owner` PID and remove the lock directory only after establishing that command has stopped.

This is coordination between cooperating writers, not access control against someone who can
push arbitrary Git refs. Use reasonably synchronized clocks. The journal provides durable review
and validation evidence; it does not start agents or keep them running. Local agent credentials
live in each worktree's Git metadata, outside tracked files. Do not copy them between worktrees.

The implementation separates typed protocol transitions in
[`Protocol.lean`](scripts/coordination/Coordination/Protocol.lean) from Git transport and worktree IO.
Run `lake -d scripts/coordination test --wfail` after changing it. Tests use temporary local remotes;
they do not mutate the project's remote or exercise the mathematical library's proofs.

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
run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d docbuild update complexitylib2`. When changing Lean,
also update the doc-gen4 tag in `docbuild/lakefile.toml` and run
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d docbuild update doc-gen4`.
Commit the refreshed documentation lockfile and run the documentation checks and build.

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
