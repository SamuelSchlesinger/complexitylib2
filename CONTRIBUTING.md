# Contributing

Contributions should make complexity-theoretic arguments easier to state, prove, and reuse.
Start with the [mission and design](docs/DESIGN.md) and the [library guide](docs/LIBRARY.md).
CSLib's `CONTRIBUTING.md` and `CODESTYLE.md` apply in full; this guide describes the workflow here.
[AGENTS.md](AGENTS.md) records the detailed file and proof rules.

## Choosing and developing a contribution

1. Identify the result or client that motivates the change. Check CSLib, the pinned dependency,
   and [UPSTREAM.md](UPSTREAM.md) for reusable definitions and work already in progress.
2. State the public contract first: inputs, encodings or computational model, mathematical
   behavior, and the resource or security claim. Keep remaining assumptions explicit.
3. Develop against a small representative client. For automation, exercise ordinary functional
   expressions, equivalent spellings, and relevant alternative encodings. Include failure cases
   when a missing certificate or growth bound would make the intended inference unsound.
4. Place the module at its future CSLib path and use CSLib's file template, namespace, and
   `-- upstream:` marker. Retain the original authors when adapting an existing formalization;
   cite mathematical sources through [references.bib](references.bib).
5. Document the public definitions and results. For a major development, add a useful entry to
   the library guide and a checked usage example. Record open construction or efficiency work
   beside the relevant result. Put implementation history and proof measurements in
   [ROADMAP.md](ROADMAP.md).
6. Validate and review the coherent batch, then commit it with a `type(scope): description`
   title. Keep changes small enough to review; separate prerequisite API changes when useful.
   Disclose AI tools and their role in PR descriptions, as CSLib requires.

Existing formalizations are valuable sources of theorems and proof ideas. Adapt their interfaces
to the shared library and evaluate them against current clients. General helpers should earn
their place through demonstrated reuse; include their implementation and proof cost when
reporting savings.

## Validation

Use Lean MCP diagnostics, goals, and theorem search during proof development. Run the following
from the repository root at the validation checkpoint:

```bash
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

After adding a library file, regenerate `Complexity.lean` with `lake exe mk_all`. Add tests to
`ComplexityTests/` and import them in `ComplexityTests.lean`. Headline theorems belong in the
axiom checks in [ComplexityTests/Axioms.lean](ComplexityTests/Axioms.lean). Supply a concrete
instance when a new contract bundles assumptions that could be vacuous.

Every batch of new or refactored modules receives an independent CSLib-style API review and a
Codex correctness review using `codex-companion.mjs adversarial-review`. Fix findings here;
reviewers review. Record what was actually checked, distinguishing source inspection, local
validation, and upstream review. For documentation-only changes, check local links, theorem
claims against source, and Lean examples with the imports shown.

## Upstreaming and dependency maintenance

```bash
python3 scripts/upstream.py Complexity.Computability.DecisionTree.Basic --cslib ../cslib --dry-run
```

The example previews the operation; omit `--dry-run` to prepare the CSLib worktree. The script
copies a module to its mirrored path, rewrites import prefixes, removes the upstream
marker, regenerates CSLib's root imports, and suggests a PR title. Validate in that CSLib
worktree according to its current instructions before opening a PR. Update `UPSTREAM.md` with
the PR number and head SHA. When the work merges, advance the CSLib pin past the merge and
remove the superseded local copy in the same commit.

Run `python3 scripts/upstream_sync.py` whenever checking upstream, and address every status other
than `CURRENT`. Keep `lean-toolchain` equal to CSLib's at the pinned commit. Mathlib comes through
CSLib's dependency; it is not pinned separately here.

Coordinate cross-cutting abstractions with CSLib's Zulip or issue tracker before proposing them
upstream. This repository's compatibility requirements prepare code for review; they do not
replace that review.

## Licensing

Apache 2.0. Every Lean file carries CSLib's header wording and preserves source authorship.
