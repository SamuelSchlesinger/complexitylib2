# Project Instructions

Complexitylib is a Lean 4 library of computational complexity theory built on **cslib**
(`leanprover/cslib`). Its defining constraint: **every module must be upstreamable into cslib
unchanged**, apart from rewriting the import prefix `Complexity.` → `Cslib.`. cslib's own rules
therefore apply here verbatim; read cslib's `AGENTS.md`, `CONTRIBUTING.md` and `CODESTYLE.md`
(pinned checkout: `.lake/packages/cslib`, or a local clone at `../cslib`) and follow them.
`ROADMAP.md` records outstanding work;
`UPSTREAM.md` records coordination and exceptional integration decisions.

## Coordinated workers

When asked to **"become a worker in complexitylib"**, follow the
[Git coordination workflow](CONTRIBUTING.md#coordinated-agent-work). Register a unique worker
name with `scripts/coordinate join NAME`, then change into the printed worktree before editing.
Never edit the starting checkout or another agent's worktree. Keep each worktree's `.lake`
directory separate; do not share mutable build outputs.

The registered coordinator assigns implementation and review work. Read `scripts/coordinate status`,
start only your assigned epic or review, and stay inside its scope. Report blockers and proposed
scope changes on the board. Check assignments and renew your heartbeat at each meaningful
checkpoint and at least every five minutes; while idle, check about once a minute. After submitting
work, remain available for reviews and follow-up assignments until asked to stop. If a lease or
session is lost, stop editing and reacquire authorization through the board.

Workers commit and push their assigned branches; only the coordinator lands work on `main`.
Reviewers inspect the exact submitted commit, record findings, and leave fixes to its author.
The coordinator owns design, dependencies, scope allocation, independent reviews, and integration.
The board is shared state, not a process scheduler: these duties run while the agents are active.

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
   (`[AroraBarak09]`, `[Papadimitriou94]`, `[Sipser2013]`, `[Jukna2012]`, …); add new entries in
   cslib's format.

## Proof hygiene

- No `sorry` on `main`, no custom `axiom`, no `native_decide`.
- `set_option maxHeartbeats` / `maxRecDepth` overrides need a justifying comment.
- Never put `[simp]` on machine step functions or transition tables (goals explode).
- Non-terminal `simp` only as `simp only`; definitions as terms, not `by` blocks, where possible.
- `ComplexityTests/Axioms.lean` audits all declarations stored in imported `Complexity` modules
  for dependencies beyond `propext`, `Classical.choice` and `Quot.sound`. Add named checks there
  for headline theorems as well.
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
