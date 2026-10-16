# complexitylib v2

A Lean 4 formalization of computational complexity theory, built on
[cslib](https://github.com/leanprover/cslib) as its base and written so that every module can be
upstreamed into cslib as-is.

## Implementation and direction

Machines, circuits and languages come from cslib. The library builds complexity theory on these
models and Christian Reitwiessner's vendored calculus of time- and space-bounded Lean functions.
Its polynomial-time closure rules are registered with `fun_prop`: many compositions of
arithmetic, conditionals and list operations have one-line proofs that an actual Turing machine
computes them in polynomial time. A universal simulator is implemented as ordinary Lean functions
with correctness and explicit time/space bounds.

Programs now use `PFunctor.FreeM` and the typed-oracle interface from cslib PR #1129: ordinary
`do` code interpreted into probability, private state, or another program. Local invariant and
simulation rules preserve the joint result and final oracle state. The common effectful machine
now has exact deterministic/nondeterministic specializations and a clocked program interpreter,
including fair-coin runs. Closed `IsPPTOn` certificates now reuse deterministic proofs through
`fun_prop` and certify fair bits, uniform words of an efficiently computed length, monadic `bind`,
deterministic preprocessing and
postprocessing, captured inputs and conditionals. The compiler charges copying and fresh-input
preparation and guarantees actual halting. The `ppt` tactic combines these rules with deterministic
`polytime` automation, named certificates and locally supplied routines. Bounded probabilistic
loops have joint efficiency and invariant rules, including captured inputs; `ppt` handles
constant state growth. `IsPPT` supplies the standard unary security parameter and auxiliary word;
`ppt` reuses its local certificates; named certificates also register with `fun_prop`.
Word-oracle PPT has a uniform joint-state realization contract and efficient closed stateful
substitution; general open-program composition remains to be integrated.
Saved-coin replay preserves the full configuration and private oracle state under stateless
fair-coin semantics. Closed replay has a uniform linear-time and space certificate from the
ordinary encoded pair of coins and input, including preparation and final cleanup. Functional
clients invoke it through `fun_prop` or `polytime`. Every typed PPT program now has a total
polynomial-time saved-seed evaluator: arbitrary seeds give supported results, and sufficiently
long uniform seeds give the exact distribution. A shared tape can be reused across inputs.
The deterministic `polytime` tactic now combines `fun_prop`, named and local routine certificates,
and bounded-growth
loop rules. Fold and iteration specifications prove both efficiency and a final invariant from
value-level contracts. These interfaces adapt the local cslib `crypto` branch to the existing tidy
TM calculus. See `ROADMAP.md` for implemented results, measured proof reductions, and the remaining
integration work.

Cook–Levin is complete: the entire existing tableau reduction has a polynomial-time TM
certificate, and SAT NP-completeness and UNSAT coNP-completeness are unconditional. The tableau
certificate uses `unfold tableau; polytime`; parameter computation and binary relabelling compose
with it. Tests exercise computed bounds, alternative input encodings and zero-tape verifiers.

The crypto port includes GGM tree evaluation with a polynomial-time TM certificate, the upstream
nonnegative game/negligibility API, computational indistinguishability and its randomized
postprocessing rule, and one-way-function/permutation definitions. The complete inversion game
has a short `ppt` certificate. Word-based generators use the existing finite PRG security API,
and Goldreich–Levin now supplies a hard-core predicate and the complete one-way-permutation →
one-bit PRG theorem. The randomized inverter is ordinary functional code certified by `ppt`,
with an exact finite-game correspondence and a typed saved-seed evaluator. Polynomial stretch
uses a uniform random-hop reduction with an exact dyadic loss; arbitrary efficient larger output
lengths follow. Random functions have exact eager/lazy semantics, typed caches and an
association-list implementation with query-budget bounds. Memoized samplers have `fun_prop`/`ppt`
certificates and bounds on their complete encoded cache. The eager/lazy law and executable
list-cache bridge also cover independent private randomness. Word-oracle PPT uses the joint
stateful machine contract and reuses deterministic `fun_prop` certificates. Its clock bounds
external call counts and request lengths. The finite interpreter reuses cslib's tapes and has
exact program equality with the native machine, including stateful choice and query effects.
Its storage bounds charge installed replies separately. Tape operations now have `fun_prop`
certificates for arbitrary symbol encodings, including infinite and empty alphabets. Fixed finite
tables likewise support ordinary function construction, projection and updates through `fun_prop`,
charging all unbounded entries. Encoded configurations now have constructor, projection, local-step
and reply-installation certificates; their complete storage bound includes the largest installed
reply. Finite-control dispatch now selects certified deterministic or probabilistic branches with
captured input. Stateful substitution now certifies running an arbitrary oracle-PPT program
against a closed PPT handler. Clients supply a local invariant and a reply/storage-growth allowance;
the certificate retains the joint result and final state, including an entire memoization cache.
`IsOraclePPT` now supplies the unary security parameter and auxiliary word on that same contract.
PRF games use the shared nonnegative game-security API, with exact eager, lazy and executable-cache
equivalence. For every oracle-PPT adversary, the ideal game has a strict PPT realization through
that cache; the exponential eager table remains a specification. The GGM prefix hybrids and
cached expansion games have exact endpoint and adjacent-level laws, with uniform strict PPT
certificates for the entire adaptive experiments. Saved independent samples expose one uniform
single-challenge reduction, with an exact polynomial loss and complete strict PPT certificate.
Adaptive GGM security and PRG → PRF are proved. General OWF → PRG through pseudoentropy, and hence
general OWF → PRF, remain to be ported. Output normalization is implemented: every general OWF
yields an OWF whose output length depends only on its input length, with a polynomial-time
length function and a uniform strict PPT inversion reduction. The conditioning and collision APIs
are also ported, including the necessary negligible-output-collision consequence of one-wayness.
Finite Shannon entropy and the samplable pseudoentropy-pair interface are implemented, with a
strict PPT certificate for the complete prediction game. Every such sampler has an efficient
deterministic saved-seed evaluator, with exact joint-law and entropy accounting for unused coins;
finite-PMF concentration bounds support independent repetition. Universal hashing, the strong
leftover hash lemma with public side information, and preimage-isolation entropy bounds are
implemented. Binary matrix hashing and its seeded extractor now have compositional polynomial-time
certificates, exact finite/list laws, and a leftover-hash bound for arbitrary finite-result
randomized tests of the complete public output. Every general OWF now yields an exactly samplable
pseudoentropy pair with prediction gap `1 / (2(n + 7))`. The hashed-parity sampler and the complete
inverter use ordinary functional programs with two-line `fun_prop` certificates. Amplification,
extraction and the final general OWF → PRG security assembly remain pending. Empirical probability
tests now have exact independent-trial laws, exponential error bounds and complete PPT
certificates, providing the sampling prerequisites for amplification.

## Layout

Every file lives at the path and in the namespace it would have inside cslib, under the library
root `Complexity` instead of `Cslib`:

```
Complexity/Foundations/…                 ↔  Cslib/Foundations/…
Complexity/Computability/Machines/…      ↔  Cslib/Computability/Machines/…
Complexity/Computability/Complexity/…    ↔  Cslib/Computability/Complexity/…   (new upstream dir)
Complexity/Languages/Probabilistic/…     ↔  Cslib/Languages/Probabilistic/…
```

Each file records its upstream status on the line after `module`
(`-- upstream: candidate | submitted #N | merged @SHA | local-only (reason)`); `UPSTREAM.md` is
the ledger, and `scripts/upstream.py` prepares a module for a cslib pull request.

## Building

```bash
lake exe cache get   # Mathlib oleans
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

The toolchain and the cslib pin in `lakefile.toml` move together: `lean-toolchain` must equal
cslib's at the pinned commit, and Mathlib is never pinned separately.

## License

Apache 2.0, as cslib.
