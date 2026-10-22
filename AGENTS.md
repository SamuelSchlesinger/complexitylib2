# Project Instructions

Complexitylib is a Lean 4 library of computational complexity theory built on **cslib**
(`leanprover/cslib`). Its defining constraint: **every module must be upstreamable into cslib
unchanged**, apart from rewriting the import prefix `Complexity.` → `Cslib.`. cslib's own rules
therefore apply here verbatim; read cslib's `AGENTS.md`, `CONTRIBUTING.md` and `CODESTYLE.md`
(pinned checkout: `.lake/packages/cslib`, or a local clone at `../cslib`) and follow them.
`ROADMAP.md` records outstanding work;
`UPSTREAM.md` records coordination and exceptional integration decisions.

## Agent roles and task ownership

Each agent works as either a **coordinator** or a **worker**. Follow the role assigned by the
human or coordinating agent; otherwise default to worker. State your role when starting work.
Changing roles does not make an author eligible to approve their own changes.

Maximize useful parallel progress: both coordinators and workers may handle multiple tasks
and spawn subagents. Roles define responsibilities, not concurrency limits. Give each subagent
a role and a clear scope; use separate issues for independently deliverable tasks and record
smaller delegated subtasks in the parent issue. Keep ownership, branches, and mutable build
outputs distinct where concurrent edits could conflict. The delegating agent remains responsible
for tracking delegated work, keeping issue status current, and bringing results to completion.

Issues are the task queue and durable record of ownership and progress. Humans, coordinators,
and workers may create tasks. Search existing issues and PRs before creating a duplicate; use
an existing human-created issue when it describes the work. Give each task a concrete scope,
completion criteria, and relevant dependencies.

### Completion and scope

Optimize for trustworthy, reusable results, not the number of closed issues or merged PRs.
When narrowing a task, preserve its original objective and record the bounded deliverable and
remaining gap prominently. A restricted model, conditional result, or partial theorem does not
complete a broader objective. Do not silently retitle an ambitious issue into an easier completed
task.

Distinguish these dispositions in the issue:

- **Completed:** the agreed acceptance criteria are satisfied.
- **Milestone completed:** a bounded deliverable is finished; link the remaining objective.
- **Deferred / not planned:** work is intentionally stopped; preserve its results and explain
  what remains unproved.

Close a milestone issue as completed when its own criteria are met. Keep the broader objective
open, or, when authorized to defer it, close it as not planned and link the completed milestone.
PR descriptions must distinguish mathematical progress from infrastructure, refactoring, and
documentation progress.

### Durable records

The issue is authoritative for scope, ownership, current state, and remaining work. The PR is
authoritative for the final change, validation, and review verdicts. Work without a PR records
validation and review in its commit description, linked from the issue.

Keep the reporting cadence below, but report changes since the previous update and link existing
evidence instead of duplicating full validation reports across related issues. Local paths alone
are insufficient for a durable handoff; publish the relevant branch, commit, or concise findings.

At integration, summarize what was proved or improved, what remains deferred, and what became
reusable by future contributors.

### Workers

1. Before implementation, create or claim an issue and assign it to yourself. Post a claim
   comment identifying your agent/session, scope, and branch or worktree. Agents sharing a
   GitHub account must use distinct agent/session IDs in comments; the assignee alone does not
   identify the active worker. A worker may own multiple active issues; identify the responsible
   agent for each delegated task in its issue.
2. Report status in that issue at least hourly while actively working, and whenever you become
   blocked, hand off, or stop. Include your agent/session ID, current state, completed work,
   validation performed, blockers, and next step. Link the branch, commits, or draft PR so
   another worker can resume. Report on every active issue, including delegated work; the owner
   or its delegating agent may report, identifying whose work is covered. An idle or stopped
   agent must not promise unattended updates.
3. If active work has had no status report from its owner or delegating agent for **three hours**,
   another worker may claim it. Re-read the issue and linked PR immediately before taking over,
   post a takeover comment, update the assignment, and verify ownership before editing.
   Preserve existing work and credit.
   If claims overlap, ask a coordinator to resolve ownership; do not work competing versions.
   A returning worker must check ownership before resuming. Explicitly released work is
   available immediately.
4. Implement, self-review, and validate according to the requirements below. Include documentation
   changes caused by your work and assess the headline abstract catalogue before submitting the PR.
5. When ready, open a PR linked to the issue, record validation and remaining limitations, and
   request coordinator review. Post an `awaiting review` status with the PR link in the issue.
   Keep the issue open until the work is merged or explicitly dispositioned by a coordinator.
   Awaiting review is a handoff, not abandoned active work: hourly worker reports and the
   three-hour takeover rule are suspended while the PR waits in the coordinator's queue.
6. Await coordinator review for that PR while freely progressing other tasks; do not approve or
   merge your own PR. Address requested changes, post an `active` status when resuming,
   restart hourly reports, and request fresh review of the updated revision. If unavailable,
   release the task explicitly so another worker can take over.

Use plain issue comments for states such as `active`, `blocked`, `available`,
`awaiting review`, and `changes requested`; this workflow does not depend on custom labels or
automation. Blocked work must have a status update or be released, rather than retaining
ownership indefinitely.

### Coordinators

**Reviewing worker PRs and approving or requesting changes is the coordinator's highest
priority.** Keep reviews moving while planning, implementation, and documentation proceed in
parallel. Use review subagents when helpful; do not make unrelated work wait for a serial queue.

- Review the exact PR revision for correctness, API design, scope, source credit, validation,
  and documentation. Arrange the independent reviews required below, record concrete findings,
  and give an explicit approval or request for changes. Re-review fixes before approval.
  If the platform prevents a formal review because agents share an account, record the verdict,
  reviewer agent/session ID, and reviewed SHA in a PR comment; do not represent this as a
  platform approval or bypass required maintainer approval.
- When requesting changes, also post `changes requested` with the review link in the issue.
  That comment ends the review-wait exemption and starts a fresh three-hour response window.
  If neither the owner nor its delegating agent posts a status update within that window,
  another worker may take over using the claim procedure above. The responding agent must
  record whether work is active, blocked, or released; hourly reporting resumes for active or
  retained blocked work, with the normal three-hour takeover rule.
- Review existing tasks, resolve ownership or dependency conflicts, and create or split issues
  when useful. Human-created issues belong to the same queue. Check stale active tasks and
  unattended review requests; help workers reach a clear next step.
- Own the consistency of `ROADMAP.md`, `abstracts/catalogue.json`, `UPSTREAM.md`, and the other project
  documentation. Ensure completed results, open work, limitations, and upstream coordination
  remain accurate. Workers still supply updates affected by their PRs; coordinators check their
  integration and arrange the formal-abstract review described below.
- Keep approval distinct from integration: merge only within the authority granted by maintainers
  and after required checks and reviews. Close completed issues on merge, and record remaining
  work in follow-up issues and the roadmap where appropriate.
- If implementing a task yourself, follow the worker ownership and reporting rules and obtain
  review from another coordinator. Self-review never substitutes for independent approval.
  Review subagents must be independent of authoring the changes they review; an authoring
  subagent's self-review does not count as independent review.

## Working on changes

Use ordinary Git branches or isolated worktrees for substantial changes. Preserve other
contributors' work and keep mutable build outputs separate between worktrees. Agree substantial
scope through Issues or pull requests, and split large developments into independently useful,
reviewable milestones. Record unfinished work in `ROADMAP.md` without claiming it complete.

Contributors self-review and validate their changes. Maintainers arrange independent API and
correctness reviews of the exact revision before integration; reviewers report findings, and
fixes receive a fresh review. Preserve source credit and record all contributors and review
results in the pull request or commit description.

### Repository isolation

Treat the user's checkout and shared Git object database as protected infrastructure. Ordinary
worktrees share their Git object database. Never import reconstructed Git objects, install shallow
boundaries, or experiment with history repair in that shared database. Use an independent
repository with its own Git object database for such operations.

Before Git recovery or nonstandard object manipulation, verify the actual Git common directory,
object alternates, and storage sharing. The experimental repository must not use the shared
database through a gitfile, alternate object directory, or hard-linked object files. Never delete
objects, refs, worktree registrations, or metadata belonging to another session.

Keep mutable build outputs separate. Integration experiments must be contained so their failure
cannot damage the user's checkout or another worker's repository.

### Placement and reuse

Place reusable definitions and general lemmas in the lowest suitable mathematical module.
Specialized theorem modules should import their prerequisites. During review, look for general
APIs buried in a particular application or proof. Extract them when the dependency improvement is
concrete and the change is small; otherwise record a specific follow-up with declaration names,
consumers, and a proposed home. Preserve public interfaces under the compatibility rules below.
Do not expand a bounded PR into an unbounded architectural cleanup.

## Lean development: use the Lean MCP server first

Use MCP goal inspection, diagnostics and theorem search while iterating; reserve `lake` commands
for validation checkpoints. If MCP tools are unavailable, say so and use the smallest shell check.

## Validation sequence

```bash
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

`scripts/check.sh` runs this sequence. CI runs the same checks.

`lake exe mk_all` regenerates `Complexity.lean` after adding a file. New test files go in
`ComplexityTests/` and must be imported from `ComplexityTests.lean`.

## File rules

1. **Path and namespace mirror cslib.** `Complexity/Foundations/Data/Encoding.lean` is destined
   for `Cslib/Foundations/Data/Encoding.lean`; multi-tape machine files use the upstream root
   namespace `Turing`, everything else `Cslib.*` as upstream does.
2. **Template** (cslib's): Apache header with the exact wording below, `module`, an
   `-- upstream:` marker line, `public import` of API dependencies (plain `import` for proof-only
   ones), a module docstring with `## Main definitions` / `## Main results` / `## References`,
   then `@[expose] public section` or per-declaration `public`.
   ```lean
   /-
   Copyright (c) <year> <authors>. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: <authors>
   -/

   module
   -- upstream: candidate

   public import Complexity.Init
   ```
3. **Upstream marker** values: `candidate`, `submitted #N @SHA` (a copy of an open cslib pull
   request at its head `SHA`), `vendored <owner>:<branch> @SHA (unsubmitted)` (a copy of a branch
   of a contributor's cslib fork that has no pull request yet), `merged @SHA` (delete the file and
   bump the pin in the same commit), `local-only (reason)`. Nothing is `local-only` without a
   reason; valid reasons are project scaffolding and tests of local-only files.
   A port keeps the authors of the files it is ported from: v1's PCP internals, Sipser–Lautemann
   and containment internals are by Bolton Bailey, so their ports carry
   `Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger` and `Authors: Bolton Bailey, Samuel
   Schlesinger`; ports of Christian Reitwiessner's work carry his name likewise. Check the v1
   file's `Authors:` line before porting.
4. **Every module publicly imports `Cslib.Init`** (through `Complexity.Init`); the test driver
   runs `checkInitImports`.
5. **Reuse upstream first.** Before defining anything, search cslib (`.lake/packages/cslib/Cslib`,
   or the local `../cslib/Cslib` checkout) and the
   in-flight PRs recorded in source markers, and consult `UPSTREAM.md`. A thin local copy of an
   unmerged upstream PR (or an unsubmitted branch of an upstream contributor) is allowed at the
   mirrored path, keeping the
   original authors and declaration names, marked `-- upstream: submitted #N @SHA` (or
   `vendored …`). A copy holds only what the pinned cslib lacks: when a PR modifies an existing
   cslib file, the copy contains just its additions. Copies are deleted when the work merges.

## Staying current with upstream

- `lakefile.toml` pins cslib `main`; move the pin forward whenever `main` moves, fixing breakage
  in the same commit.
- `scripts/upstream_sync.py` reports, for every copied module, whether its pull request has
  merged (bump the pin past it and delete the copy), whether its head has moved (re-sync the
  copy) or whether it was closed. Run it whenever upstream is checked, and act on every line that
  is not `CURRENT`.
6. **Bit strings.** Declarations about bit strings and the cube `ι → Bool` (operations, sampling,
   Fourier analysis, sensitivity, influence, codes) live in `Cslib.BitString`; only the named
   Boolean functions `parityOn`, `parity`, `threshold`, `majority`, `strictMajority` sit in `Cslib`
   beside cslib's `BooleanFunction`. Bit strings add with `+` (Mathlib's `BooleanRing Bool`),
   single bits with `^^`.
7. **Citations.** Cite textbook sources in docstrings via `references.bib` keys
   (`[AroraBarak09]`, `[Papadimitriou94]`, `[Sipser2013]`, `[Jukna2012]`, …). Add new entries in cslib's
   format, keeping bibliography and project-documentation changes in focused commits.

## Proof hygiene

- No `sorry` on `main`, no custom `axiom`, no `native_decide`.
- `set_option maxHeartbeats` / `maxRecDepth` overrides need a justifying comment.
- Never put `[simp]` on machine step functions or transition tables (goals explode).
- Non-terminal `simp` only as `simp only`; definitions as terms, not `by` blocks, where possible.
- As in Mathlib, renaming, moving or removing a public declaration that is already on `main`
  leaves a deprecated alias at the old full name, `@[deprecated (since := "YYYY-MM-DD")] alias
  oldName := newName` (or a `@[deprecated]` theorem when the statement changes shape). Private
  declarations and declarations introduced in the same unmerged branch need no alias.
- `ComplexityTests/Axioms.lean` audits all declarations stored in imported `Complexity` modules
  for dependencies beyond `propext`, `Classical.choice` and `Quot.sound` and keeps its existing
  named guards. Add named `#print axioms` guards for an epic's headline theorems to the epic's
  own test module.
- Watch for vacuous hypotheses: when a structure bundles bounds, provide at least one instance in
  the test suite.

## Review cycle

Maintainers arrange these reviews; contributors do not need a particular agent installation.
Record the reviewed revision, scope, findings and resolutions in the PR or commit description,
following [CONTRIBUTING.md](CONTRIBUTING.md#ai-assistance-and-review).

- Every batch of new or refactored modules gets an independent cslib-style review (naming, API,
  duplication, placement, documentation) before or soon after it lands on `main`.
- Every batch also gets an independent correctness review:
  are the statements true and as the docstrings claim, are hypotheses satisfiable and
  non-vacuous, do definitions match the cited literature. Reviewers report findings; fixes are
  made separately.

### Independent review method

Reviewers must inspect the exact definitions and statements before relying on the author's
summary. For substantive mathematical results, briefly record in the existing review:

- what the formal theorem actually establishes;
- which hypotheses, model choices, or resource conventions limit it;
- which concrete instance or edge case was checked for non-vacuity or semantic mismatch.

For extractions and refactors, check declaration preservation, import boundaries, and a client
using the intended smaller imports.

Separate reviewers can share blind spots. Lean compilation establishes kernel acceptance under
the audited axioms; it does not establish that definitions express the intended mathematics or
that prose accurately describes them. State which questions the review actually checked.

Record findings and the evidence needed for the verdict. Reuse existing review records when the
reviewed content is unchanged, explicitly verify that identity on the final revision, and review
subsequent deltas. This does not replace the exact-revision approval and validation requirements.

## Curated formal abstracts

`abstracts/catalogue.json` selects the public headline results. Each selected group has a checked
`*Abstract.lean` and `*Bridge.lean` under `ComplexityTests/Abstracts/`, imported by
`ComplexityTests.lean`. The Lean definitions and statements are the source of truth; PDFs are
generated from them, with proof bodies omitted. There is no separately maintained paper/TeX index.

Selection has a higher bar than inclusion in the library: a headline must be a substantial proved
endpoint with conventional, inspectable semantics, satisfiable hypotheses, explicit models and
encodings, and honest quantitative bounds. Partial constructions, conditional substitutes for a
standard theorem, bounded experiments and helper APIs do not become headlines by acquiring an
abstract. Prefer a small coherent selection. Preserve Samuel's editorial choices and source credit;
keep outstanding endpoints in `ROADMAP.md`.

Before opening or updating **every AI-authored PR**, assess the selected abstracts against the
final Lean changes. Update affected statements, definitions, scope notes and catalogue entries.
New library theorems need not become headlines. Record a no-impact assessment when appropriate,
including proof-only refactors with unchanged statements and scope.

Follow the local `lean-abstract` skill and run `#check_abstract`. An allowlist may expose narrowly
identified foundational models with their meaning explained; it must not hide the result or its
complexity-class semantics. The audit checks elaborated dependencies, not human interpretation.
Obtain independent reviews of API quality, correctness, and each changed abstract against the final
Lean sources, including quantifiers, encoding, resource bounds, nonvacuity and readability. Record
exact revisions, findings and resolutions in the PR. Do not imply human editorial approval.

`scripts/build_abstracts.py` generates individual PDFs, a combined catalogue and provenance with
source digests and exact declaration links. The **Formal abstract PDFs** workflow uploads review
artifacts and publishes main builds as `formal-abstracts` release assets. Inspect the rendered
pages and declaration links before integration; record the artifact/run and reviewed revisions.
Local generation is supported. Generated TeX, PDFs and auxiliary products are not versioned.

## Design commitments (do not re-litigate casually)

- Base pin is upstream cslib `main` at a SHA; never a fork.
- One parametric machine extending upstream `Turing.Cfg`/`Turing.Action`, with `Choose := Id`
  recovering `MultiTapeTM` and `Choose := Set` recovering `MultiTapeNTM`, step-exactly.
- Computability predicates (`PolyTime`, `InTimeSpace`, …) are `@[fun_prop]`-registered; loops
  go through Hoare-style `iterate_spec` rules and the Aesop `polytime` set.
- Programs are `PFunctor.FreeM` values; a machine's clocked run is itself a program.
- The universal machine is an interpreter program certified by the calculus, not a hand-built
  machine.
- Do not cite the unpublished draft "A Small Calculus of Finite Computation" in source or PR text.

## PR titles (for upstream PRs and here)

`type(scope): description`, type ∈ `feat|fix|doc|style|refactor|test|chore|perf|ci`, no trailing
period. Disclose AI assistance in the PR description, as cslib's policy requires.
