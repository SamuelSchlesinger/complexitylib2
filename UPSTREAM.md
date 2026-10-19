# Upstream integration

Coordination and integration decisions not already recorded in source.

The authoritative records are:

* [lakefile.toml](lakefile.toml), [lake-manifest.json](lake-manifest.json) and
  [lean-toolchain](lean-toolchain) for pinned versions;
* each module's `-- upstream:` markers for candidate, submitted, vendored or local-only status,
  including PR numbers and copied revisions; markers can also identify blocks within a module;
* [Complexity.lean](Complexity.lean) for the module inventory.

Use `python3 scripts/upstream_sync.py --offline` to list copied dependencies, and
`python3 scripts/upstream_sync.py` to compare recorded revisions and the base pin with upstream.
It checks head revisions, not source equality or unrecorded overlaps. Follow
[AGENTS.md](AGENTS.md#staying-current-with-upstream) for synchronization and removal, and
[CONTRIBUTING.md](CONTRIBUTING.md#upstreaming) for preparing an upstream worktree.
Do not add a ledger row for an ordinary candidate or repeat its source marker here.

## Coordination before submission

* **Machine calculus.** Build on Christian Reitwiessner's `crei/tidy-universal` branch and its
  component PRs, including #1111, #1112 and #1138. Local `-- vendored:` comments identify required
  adaptations. The branch's `IterateWhile` supersedes the version from #1112. Coordinate the
  shared encodings and calculus through CSLib issue #611, including the `TapeEncodable`
  interface proposed in #590. Check #767 and its split #768 before adding space-to-time
  inclusions or overlapping class definitions; reconcile the local encoded, tidy-machine
  definitions of `P`/`NP` with its `DTIME`-based language classes. The local `L`, `DTIME` and
  `EXP` (`Classes/LogSpace`, `Classes/Hierarchy/Time`, `Classes/EXP`) use #767's shapes over
  encoded instances; once #767 lands, derive them from its language-indexed classes rather than
  keeping parallel definitions. The local `PSPACE` uses a different space bound and is not yet
  compared with #767's. Selected-tape specifications
  formerly in `Combinators/StreamFold` and `Encodings/MultiPass` now live beside the plumbing
  operations; preserve their exact space bounds when resynchronizing the copied files.
* **Polynomial bounds.** The tidy calculus's size-parameterized `PolyBounded` adapts CSLib's
  `PolynomiallyBounded` and shares its closure API. Coordinate this adaptation with the tidy
  branch; preserve it when resynchronizing the vendored files.
  `Foundations/Data/Nat/PolynomialBound/Closure.lean` is the proposed next submission following
  #1067.
* **Probabilistic programs.** Coordinate the shared `PFunctor.FreeM` API with #1086–#1089 and
  typed oracles with #1129. The copied PMF blocks have their own markers and removal instructions
  in [Probability/PMF.lean](Complexity/Probability/PMF.lean); remove only the merged blocks.
* **Security games.** `Crypto/Negligible.lean` and `Crypto/Game.lean` include the #1068 base
  beneath #1069. If #1068 lands first, remove its declarations and retain the #1069 additions.
  The following hybrid layer is tracked by its own marker in `Crypto/Game/Hybrid.lean`.
  `Crypto/Game/Statistical.lean` copies only the Boolean equality from #1072; its remaining
  declarations require the arbitrary-type metric replacement in #1065. Until that is in the
  base pin, extraction bounds quantify over every randomized test of the full encoded output,
  using the existing finite-PMF metric and `Game.Indistinguishable` with all tests admissible.
  Coordinate the finite PRG API and its distribution-based refactor in #1071 before adapting
  `Crypto/Primitives/PRG/Game`.
* **Query complexity.** Numerical measures and certificates use the merged
  `Computability/QueryComplexity` API directly, on `Fin n`/`Bool`. Generic decision trees,
  restrictions and Fourier analysis retain arbitrary coordinate/output types; sensitivity
  lower bounds there use explicit coordinate sets. The restriction representations agree
  definitionally, with `QueryComplexity/Restriction` connecting filling to `Forces`.
  Align the remaining tree representation in `Computability/DecisionTree` with #925 and
  coordinate its certificate follow-up `D ≤ C₀ C₁`; no second numerical measure API is retained.
* **Earlier review requests.** The withdrawn #1099–#1101 requested abstract word encodings and
  textbook sources for FP/poly, P/poly and their machine simulation. The withdrawn #869 and
  #871–#875 requested composition above configuration level; use `TransformsTapes`-style specs.

These are coordination references, not a second record of live PR status. Check the relevant
upstream discussion before starting or submitting overlapping work.

## Placement decisions not already recorded in source

Paths below omit `Complexity/` and `.lean`. The default CSLib destination mirrors the source
path. A destination recorded in a source marker takes precedence; the alternatives below need
agreement during upstream review.

| Local module or declarations | Integration note |
| --- | --- |
| `Computability/Machines/Turing/MultiTape/Encodings/StreamFold` | The candidate `streamFold_sum` generalizes the vendored proof; `streamFold` is its compatibility corollary. When resynchronizing or removing the copy, preserve the summed contract and shared proof until upstream includes them. |
| `Computability/Machines/Turing/MultiTape/Encodings/Length` | Add to the tidy branch's `Encodings/List`. |
| `Computability/Machines/Turing/MultiTape/Plumbing/Shadow` | Put general run lemmas in `TapeLemmas`. |
| `Turing.Action.instFinite` in `Computability/Machines/Turing/MultiTape/Machine/ChoiceTable` | Place beside `Action` in `Computability/Machines/Turing/MultiTape/Configuration`. |
| `Computability/Machines/Turing/MultiTape/Plumbing/ExtendTapesView` | Derive the old `tapeEmb`/`noTapes` lemmas from `viewCfg`; `oneTapeCfg i = viewCfg (tapeEmb i)` by `rfl`. |
| `Computability/Machines/Turing/MultiTape/Probabilistic/IterateWhile` | Its private tape helpers parallel the vendored deterministic `Combinators/IterateWhile`; share them once the tidy branch exposes them. |
| `Computability/Machines/Turing/MultiTape/Combinators/TidyNormalForm` | Place `runFrom_nop_withState` beside `runFrom_nop_one`. |
| `Computability/Machines/Turing/MultiTape/Encodings/Decoder` | Total decoders with tidy certificates; add to the tidy branch's `Encodings` beside `Option`/`Pair`/`List`. |
| `Computability/Machines/Turing/MultiTape/Encodings/NatPower` | Addition to the tidy branch's `Encodings/Nat`: `encNat (2 ^ n)` and its linear clock certificate. |
| `Computability/Circuit/Frontier/Correlation/{Rectangle,Circuit}` | Put `correlation` beside `agreement` in `AverageCase`, rectangle lemmas in `Rectangle`, and general network lemmas in `Network`. |
| `Computability/Circuit/{Unfolding,MapOp}` | Consider integrating into `Circuit/Formula` and `Circuit/Program`, respectively. |
| `Computability/Circuit/Boolean/FirstOrder` | Consider a descriptive-complexity directory. |
| `Foundations/Data/BitString/{Agree,Block,Hoeffding}` | Add to CSLib's `Foundations/Data/BitString`. |
| `Foundations/Data/BitString/QuadraticForm` | Move the general bit-polynomial lemmas to `Foundations/BooleanAnalysis/LowDegree`. |
| `Foundations/BooleanAnalysis/Fourier` | Consider Mathlib beside `Analysis/Fourier/FiniteAbelian`. |
| `Foundations/BooleanAnalysis/{Bernoulli,CoordinateSampling,Fibers,HarmonicMean,LightPatterns,MirrorSets}` | Consider Mathlib probability APIs; evaluate a shared coordinate-gluing operation and splitting `HarmonicMean`. |
| `Foundations/BooleanAnalysis/HadamardTester` | Consider the PCP hierarchy. |
| `Foundations/Combinatorics/{FiniteCover,Hypergeometric,Sunflower}` | Consider Mathlib combinatorics; probabilistic-method lemmas belong near `Combinatorics/Probabilistic`. |
| `Foundations/Combinatorics/Expander/Products` | Extract the private expectation helpers on product types to Mathlib if useful. |
| `Foundations/LinearAlgebra/{Rank,Matrix/CutRank,Matrix/Lindsey}` | Mathlib candidates: `LinearAlgebra/Dimension/LinearMap` and `LinearAlgebra/Matrix/Rank`; placement of Lindsey's lemma needs agreement. |
| `Probability/PairwiseIndependentHash/Shift` | Consider integration into `PairwiseIndependentHash`. |
| `Probability/PairwiseIndependentHash/Toeplitz` | Move `Matrix.toeplitz` to Mathlib beside `LinearAlgebra/Matrix/Circulant`. |
| `Probability/ApproximateCounting/Relative` | Extract the natural-number root lemmas to Mathlib. |
| `Computability/Kolmogorov/SelfDelimiting` | Move `Nat.foldr_bit_bits` to Mathlib's `Data/Nat/Bits`. |

The [historical ledger](https://github.com/SamuelSchlesinger/complexitylib2/blob/d0e6373970029a91018528463ca7a5ccd0fc9fd1/UPSTREAM.md)
preserves earlier integration notes and per-module follow-up ideas.
