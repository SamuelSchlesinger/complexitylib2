# Contributing

This library exists to feed [cslib](https://github.com/leanprover/cslib). Contributions follow
cslib's `CONTRIBUTING.md` and `CODESTYLE.md` in full; this file only lists what is specific here.

## Workflow

1. Read `ROADMAP.md` and pick a phase item. Check `UPSTREAM.md` and cslib's open PRs before
   writing anything that might already exist upstream or in flight.
2. Write the module at its future cslib path, with cslib's file template and an `-- upstream:`
   marker (see `AGENTS.md`).
3. Run the full validation sequence (`AGENTS.md`), including `lake exe checkInitImports`.
4. Open a PR here with a `type(scope): description` title. Keep PRs small; cslib-sized stacks of
   50–150 lines have the best review record.

## Upstreaming a module

```bash
python3 scripts/upstream.py Complexity.Foundations.Data.Encoding --cslib ../cslib
```

This copies the file into the cslib worktree at the mirrored path, rewrites import prefixes, drops
the marker line, runs `lake exe mk_all` there and prints a suggested PR title. Run cslib's five
gates in that worktree before opening the PR. Update `UPSTREAM.md` to `submitted #N`. When the PR
merges, delete the local file, set the marker in `UPSTREAM.md` to `merged @SHA`, and bump the
cslib pin and `lean-toolchain` together in the same commit.

Cross-cutting abstractions (new machine models, typeclasses, notation) are discussed on cslib's
Zulip or issue tracker first; complexity-theory plans belong on cslib issue #611.

## Licensing

Apache 2.0. Every file carries cslib's header wording so it can move without edits.
