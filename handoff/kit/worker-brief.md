# Worker brief — complexitylib2 coverage batch (2026-10-19)

You are an implementation worker for complexitylib2 (`/Users/samuelschlesinger/projects/lean/complexitylib2`,
call it MAIN), a Lean 4 complexity-theory library built on cslib. The coordinator (the session that
spawned you) reviews and integrates your branch. Throughput matters: deliver a correct, gated,
independently useful endpoint, commit it, and report. Correctness is gated by independent review
afterwards, so do not gold-plate, but never state more than you prove.

## Setup (do this first)

1. You run in your own git worktree (your cwd). Its branch is yours. Never touch MAIN's checkout,
   other worktrees, or `main`. Never push, never force anything, never `lake update`.
2. Build cache: if `.lake` is missing in your worktree, wait until the file
   `<a marker file the coordinator creates once MAIN's .lake is fresh>`
   exists (MAIN's cache is being refreshed; reading code meanwhile is fine), then run
   `cp -Rc /Users/samuelschlesinger/projects/lean/complexitylib2/.lake .lake` (APFS clone, ~1 min).
   Do not run any `lake`/`lean` command before that.
3. Read `AGENTS.md` (the file template, upstream markers, naming, placement, proof hygiene) and skim
   cslib's `CODESTYLE.md` in `.lake/packages/cslib/`. No Lean MCP tools are available: probe with
   `nice -n 10 lake env lean <file>` or `nice -n 10 lake build <Module.Name>`.

## Rules

- **Reuse first.** Search the library (`Complexity/`, `.lake/packages/cslib/Cslib`, Mathlib) before
  defining anything. The library has ~1200 modules; the pieces named in your task exist — find and
  use them. Prefer generalizing an existing lemma's statement in place over duplicating it only if
  that is cheap; otherwise add a local lemma.
- **New files only, where possible.** Put your work in new modules at the right cslib-mirrored path
  with the AGENTS.md template (`Copyright (c) 2026 Samuel Schlesinger`, `Authors: Samuel
  Schlesinger`, `module`, `-- upstream: candidate`, module docstring with `## Main definitions`,
  `## Main results`, `## References`). Small edits to existing files are allowed when needed (e.g.
  exposing a lemma, making a helper public); keep them minimal and mention them in the report.
- **Shared files.** You may run `lake exe mk_all` (regenerates `Complexity.lean`). Add one test module
  `ComplexityTests/<YourTopic>.lean` (import it from `ComplexityTests.lean`) with nonvacuity clients
  and `#print axioms` guards for your headline theorems. You may append BibTeX entries to
  `references.bib` (cslib format; verify DOIs; do not reorder). Do NOT edit `ROADMAP.md`,
  `UPSTREAM.md`, `README.md`, `ComplexityTests/Axioms.lean`, or anything under `paper/`; put the
  text you would add there into your report instead.
- **Hygiene.** No `sorry`, no `axiom`, no `native_decide`, no `[simp]` on machine step functions;
  heartbeat overrides need a justifying comment. Non-terminal `simp` only as `simp only`.
- **Honest statements.** State theorems with the hypotheses the literature uses. No vacuous
  hypotheses (show satisfiability in tests when you bundle assumptions). If the full target is too
  large, land the largest independently useful public endpoint and say exactly what remains. Do not
  name a weaker result after the full theorem.
- **Machine load.** The machine is shared by ~15 workers. Prefix every `lake`/`lean` command with
  `nice -n 10`. Prefer per-module checks while iterating. Run the full six-gate suite through the
  two-slot runner, in the background (it waits for a free slot):
  `handoff/kit/bin/run-gates "$PWD"`
  Kill any Lean/lake process you started that is still running when you finish.
- **Commits.** Commit on your branch in cslib style, `type(scope): description` (no trailing period),
  with a body summarizing the result and the line `Developed with Claude (Anthropic) assistance.`
  Several focused commits are fine.

## Report (your final message)

Return exactly these sections, concisely:
1. **Branch / head SHA / worktree path.**
2. **Results**: each headline declaration's full name, file:line, and its statement in one line of
   math (quantifiers, model, bounds). Note any hypothesis that differs from the literature.
3. **Scope**: what of the assigned target is done, what remains (honestly).
4. **Gates**: output summary of the final `run-gates` run on the head SHA (must be all `ok`).
5. **Edits to existing files**, bib keys added.
6. **Paper entry draft**: a LaTeX `\begin{result}...\end{result}` block in the style of
   `paper/sections/*.tex` (statement, model, hypotheses, limitations, `\citep{...}` keys, and
   `\declat{<head SHA>}{<path>}{<line>}{<decl>}` lines), plus which section file it belongs in.
7. **ROADMAP delta**: one or two sentences the coordinator should add/remove.
