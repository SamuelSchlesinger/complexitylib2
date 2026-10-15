# Project Instructions

complexitylib v2 is a Lean 4 library of computational complexity theory built on **cslib**
(`leanprover/cslib`). Its defining constraint: **every module must be upstreamable into cslib
unchanged**, apart from rewriting the import prefix `Complexity.` → `Cslib.`. cslib's own rules
therefore apply here verbatim; read cslib's `AGENTS.md`, `CONTRIBUTING.md` and `CODESTYLE.md`
(local clone: `../cslib`) and follow them. `ROADMAP.md` holds the architecture and phase plan;
`UPSTREAM.md` is the upstreaming ledger.

## Lean development: use the Lean MCP server first

Use MCP goal inspection, diagnostics and theorem search while iterating; reserve `lake` commands
for validation checkpoints. If MCP tools are unavailable, say so and use the smallest shell check.

## Validation sequence (identical to cslib's CI)

```bash
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

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
   Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Samuel Schlesinger
   -/

   module
   -- upstream: candidate

   public import Complexity.Init
   ```
3. **Upstream marker** values: `candidate`, `submitted #N`, `merged @SHA` (delete the file and
   bump the pin in the same commit), `local-only (reason)`. Nothing is `local-only` without a
   reason; valid reasons are project scaffolding and tests of local-only files.
   A port keeps the authors of the files it is ported from: v1's PCP internals, Sipser–Lautemann
   and containment internals are by Bolton Bailey, so their ports carry
   `Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger` and `Authors: Bolton Bailey, Samuel
   Schlesinger`; ports of Christian Reitwiessner's work carry his name likewise. Check the v1
   file's `Authors:` line before porting.
4. **Every module publicly imports `Cslib.Init`** (through `Complexity.Init`); the test driver
   runs `checkInitImports`.
5. **Reuse upstream first.** Before defining anything, search cslib (`../cslib/Cslib`) and the
   in-flight PRs listed in `UPSTREAM.md`. A thin local copy of an unmerged upstream PR is allowed
   at the same path, marked `-- upstream: submitted #N`, and must be deleted when the PR merges.
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
- Headline theorems are listed in `ComplexityTests/Axioms.lean`, which checks they depend only
  on `propext`, `Classical.choice` and `Quot.sound`.
- Watch for vacuous hypotheses: when a structure bundles bounds, provide at least one instance in
  the test suite.

## Review cycle

- Every batch of new or refactored modules gets an independent cslib-style review (naming, API,
  duplication, placement, documentation) before or soon after it lands on `main`.
- Every batch also gets a Codex correctness review (`codex-companion.mjs adversarial-review`):
  are the statements true and as the docstrings claim, are hypotheses satisfiable and
  non-vacuous, do definitions match the cited literature. Codex only reviews; fixes are written
  here.

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
