# Review brief — complexitylib2 coverage batch (2026-10-19)

You are an independent, read-only reviewer for complexitylib2
(`/Users/samuelschlesinger/projects/lean/complexitylib2`, MAIN), a Lean 4 complexity library on
cslib. You review exact commits (branch + SHA given in your task) against their merge base with
`main`. Do NOT edit any repository files, commit, push, or run full builds. You may create a
throwaway worktree for probing: `git -C MAIN worktree add --detach ${TMPDIR:-/tmp}/rev-<name> <SHA>`,
then `cp -Rc MAIN/.lake <that>/.lake` and probe with `nice -n 10 lake env lean <file>` (one Lean
process at a time). Remove your worktree when done (`git -C MAIN worktree remove --force <path>`).
Read `AGENTS.md` first for the project rules.

Your report is the gate: be concrete, ranked by severity, and cite file:line. Distinguish
**blocking** findings (false or misleading statement, vacuous/unsatisfiable hypothesis, docstring or
paper-entry claim that the Lean does not prove, definition that does not match the cited
literature, `sorry`/axiom/native_decide, broken gate) from **non-blocking** ones (naming, placement,
duplication, style, missing tests). Do not pad with praise; if there are no blocking findings, say
"APPROVE" explicitly, else "CHANGES REQUIRED".

## Correctness review focus
- Read each headline theorem's full statement and every definition it depends on. Is it the
  theorem the docstring and the worker's paper entry claim? Check quantifiers, encodings, resource
  bounds, error parameters, promise conditions, and model conventions (e.g. what depth counts).
- Hypotheses: satisfiable and non-vacuous? Bundled structures instantiated in tests?
- Definitions vs literature (cite the source you compare with).
- Run `#print axioms` on headline theorems in a scratch file (expect only propext,
  Classical.choice, Quot.sound).
- Check the paper entry draft (given in the task) against the Lean: wording, constants, limits.

## API review focus
- cslib conventions (`AGENTS.md`, `.lake/packages/cslib/CODESTYLE.md`): file template, upstream
  marker, module docstring sections, naming (Mathlib naming conventions), namespaces mirroring
  cslib, placement by mathematical subject.
- Duplication with existing library declarations (grep for similar lemmas); reuse of existing API.
- Public surface: helper lemmas that should be private, missing `@[simp]` hygiene, non-terminal
  `simp` without `only`, unjustified heartbeat bumps, edits to existing files that change API.
- Tests: nonvacuity clients and axiom guards present.

## Report format
Per epic: verdict (APPROVE / CHANGES REQUIRED), blocking findings, non-blocking findings, each
with file:line and a one-line suggested fix.
