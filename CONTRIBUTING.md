# Contributing

Follow CSLib's `CONTRIBUTING.md` and `CODESTYLE.md`; [AGENTS.md](AGENTS.md) records the local file,
proof, validation, and review requirements, including the six validation commands.

Develop against representative clients and state the public contract: model or encodings,
mathematical behavior, and resource or security claim. Test automation on ordinary expressions,
alternative encodings, and important failure cases. Distinguish correctness, executability,
certified efficiency, and security in declaration docstrings.

For documentation-only changes, check links, claims against source, and Lean examples with the
imports shown. Record the scope of validation and review accurately.

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
