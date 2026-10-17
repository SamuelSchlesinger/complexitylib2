# Contributing

Contributions should make complexity-theoretic arguments easier to state, prove, and reuse.
Follow CSLib's `CONTRIBUTING.md` and `CODESTYLE.md`; [AGENTS.md](AGENTS.md) records the local file,
proof, validation, and review requirements.

## Workflow

1. Identify a useful result or client. Check CSLib and [UPSTREAM.md](UPSTREAM.md) for existing
   APIs and work in progress before introducing new infrastructure.
2. State the public contract: the model or encodings, mathematical behavior, and resource or
   security claim. Develop against representative clients. For automation, test ordinary
   expressions, relevant alternative encodings, and important failure cases.
3. Document the result's assumptions, use, limitations, and sources beside its declarations.
   Preserve the distinction between correctness, executability, certified efficiency, and
   security. Count helper lemmas and proof fields when measuring proof savings.
4. Validate and obtain the independent API and correctness reviews specified in
   [AGENTS.md](AGENTS.md). Commit coherent batches with `type(scope): description` titles;
   disclose AI tools and their role in PR descriptions, as CSLib requires.

## Documentation

Keep each fact in one maintained location. The README explains the purpose and points to useful
entry points; module docstrings explain the mathematics and API; checked Lean examples show
usage. ROADMAP records outstanding work and architectural decisions; UPSTREAM records integration
status. Batch measurements and validation/review evidence belong in commit or PR descriptions.
Link to these sources instead of repeating them in new guides. Add a separate document only when
it provides useful explanation that does not already have a suitable home.

## Validation

Run the six commands in [AGENTS.md](AGENTS.md#validation-sequence-identical-to-cslibs-ci) from the
repository root. For documentation-only changes, check links, claims against source, and Lean
examples with the imports shown. Record the scope of validation and review accurately.

## Upstreaming

```bash
python3 scripts/upstream.py Complexity.Computability.DecisionTree.Basic --cslib ../cslib --dry-run
```

This previews copying a module to its mirrored CSLib path, rewriting imports, and removing the
upstream marker. Omit `--dry-run` to prepare the worktree and regenerate its root imports.
Validate there according to CSLib's current instructions before opening a PR, and update
[UPSTREAM.md](UPSTREAM.md) with the PR number and head SHA.

Coordinate cross-cutting abstractions with CSLib before proposing them upstream. Follow
[AGENTS.md](AGENTS.md#staying-current-with-upstream) for pin updates, synchronization checks,
and removal of superseded local copies.
