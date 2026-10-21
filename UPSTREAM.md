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
  The step-machine layer (`StepMachine/*`, `Encodings/StepMachine*`, `Combinators/StepMachine`
  and their helpers) and the blocks marked `@9cce4cc7` in older copies come from a later local
  rewrite of the branch that is not yet published; `scripts/upstream_sync.py` reports them
  against the published head until it is. The rest of the branch is still copied at `@7f7c0696`.
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
* **Word RAM.** `Computability/WordRAM/*` adapt the bounded-word RAM of the Lean formalization
  accompanying the tromino undecidability paper,
  [`edemaine/lean-trominoes`](https://github.com/edemaine/lean-trominoes) @6d5b36c1 (Apache-2.0),
  which is not a CSLib branch. The adapted files retain the source's copyright notice
  (lean-trominoes contributors) and credit Erik Demaine alongside the adaptation author in their
  `Authors:` lines; confirm the attribution with him and submit the files with him,
  and first coordinate with the CSLib algorithm-model work: Shreyas Srinivas's query-combinator
  programs (#685, and the register word-RAM models in his Algolean repository) and #401, which
  count only lifted queries. A deeply embedded machine beneath such front ends answers, for the
  RAM, the objection that pure Lean computation is uncharged. The module docstrings record the
  deviations from the source. The unbounded-register `Computability/RAM`, inspired by
  Cook–Reckhow and supporting both unit and logarithmic costs, remains a separate candidate.
* **Stateful algorithms prototype.** `Foundations/Semantics/Stateful/*` reuses Quang Dao's merged
  `PFunctor.FreeM` for adaptive clients and substitution, adding persistent representation
  simulation, interface composition, semantic Hoare rules and separate native-resource
  certificates. Its queue and reset-and-replay constructions deliberately count backend calls;
  arbitrary pure continuations are not machine-compiled. `WordRAM/Dynamic` separately connects
  fixed bounded-word operation programs and faithful memory transcripts to those contracts.
  Coordinate placement and overlap with Srinivas's #685 and #401 before upstream submission;
  neither open framework is copied here. This is a prototype of composition and refinement,
  not a replacement for their query models or a general cell-probe lower-bound semantics.
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
| `Computability/Circuit/{Unfolding,MapOp}` | Consider integrating into `Circuit/Formula` and `Circuit/Program`, respectively. |
| `Computability/Circuit/Boolean/FirstOrder` | Consider a descriptive-complexity directory. |
| `Foundations/Data/BitString/{Agree,Block,Hoeffding}` | Add to CSLib's `Foundations/Data/BitString`. |
| `Foundations/BooleanAnalysis/Fourier` | Consider Mathlib beside `Analysis/Fourier/FiniteAbelian`. |
| `Foundations/BooleanAnalysis/{Bernoulli,CoordinateSampling,Fibers,HarmonicMean,LightPatterns,MirrorSets}` | Consider Mathlib probability APIs and evaluate splitting `HarmonicMean`. |
| `Foundations/BooleanAnalysis/HadamardTester` | Consider the PCP hierarchy. |
| `Foundations/Combinatorics/{FiniteCover,Hypergeometric,Sunflower}` | Consider Mathlib combinatorics; probabilistic-method lemmas belong near `Combinatorics/Probabilistic`. |
| `Foundations/Combinatorics/Expander/Products` | Extract the private expectation helpers on product types to Mathlib if useful. |
| `Foundations/LinearAlgebra/{Rank,Matrix/CutRank,Matrix/Lindsey}` | Mathlib candidates: `LinearAlgebra/Dimension/LinearMap` and `LinearAlgebra/Matrix/Rank`; placement of Lindsey's lemma needs agreement. |
| `Probability/PairwiseIndependentHash/Shift` | Consider integration into `PairwiseIndependentHash`. |
| `Probability/PairwiseIndependentHash/Toeplitz` | Move `Matrix.toeplitz` to Mathlib beside `LinearAlgebra/Matrix/Circulant`. |
| `Probability/ApproximateCounting/Relative` | Extract the natural-number root lemmas to Mathlib. |
| `Foundations/Data/Nat/Bits` | `Nat.foldr_bit_bits` is a candidate for Mathlib's `Data/Nat/Bits`; its local relocation is complete, but upstream integration is still pending. |

## Deprecation policy and grandfathered changes

Since `2110aa5a` (2026-10-19), renaming, moving or removing a public declaration already on `main`
leaves a deprecated alias or theorem at the old full name (`AGENTS.md`, Proof hygiene). The sweep
integrated at `7738dcea` added aliases for the names that changed before the rule existed and
restored old binder orders where they had changed. Changes that have no mechanical successor are
grandfathered without an alias; this list records them for downstream users.

* **Signature changes under the old name.** `GeneralizedGeography.decide_mem_eq_any` is now an
  alias of the more general `List.decide_mem_eq_any`; `RotationMap.le_edgeExpansion_of_spectralExpansion_le`
  takes `V` implicitly; `PolyTimeComplete` takes `{β}` before `C`; `PMF.iid_map` has the opposite
  orientation; `eval_toUnbounded_atomsOf` changed its signature.
* **Removed or made private, without a successor of the same shape.**
  - Raz–Wigderson helpers: `bobAnswer_aliceMatching`, `aliceGraph_swap_swap`, `bobGraph_swap_swap`,
    `exists_run_oneRun`, `run_oneRun_of_disjointness`, `run_oneRun_of_mem`.
  - Graph non-isomorphism: `PublicCoin.entry`, `entry_fin`, `value`, `value_fin` (use `matrixBit`)
    and `mem_orbit_self`.
  - Communication: `PublicCoin.majority` and `le_card_filter_ne_of_majority_ne` (use
    `BitString.strictMajorityOn` and `card_filter_eq_le_half_of_strictMajorityOn_ne`);
    `ecomplexity_le_succ`, `IsFoolingSet.le_ecomplexity`,
    `PublicCoin.Solves.sq_mul_two_pow_le_four_pow`.
  - Hamiltonian cycle: `SAT.rowLength`, `rowLength_sub_one`, `diamondArcs`, `literalArcs`,
    `diamondGraphArcs`, `diamondGraphVertices`, `mem_diamondGraphArcs`, `mem_diamondGraphVertices`
    (use `Diamond.graph`); `Diamond.Follows` and its lemmas are private.
  - `SAT.SparseIndependentSet.mem_clauseEdges` and `mem_variableEdges`; the eight
    `CookLevin.determined_of_mem_*` lemmas (private); `SharpSAT.getD_idxOf`,
    `getD_mem_of_isFirst`, `isFirst_idxOf`; `Crypto.le_length_encPreimagePrefix` and
    `UniformLearning.toOuterMeasure_uniformOfFintype_ne` (private);
    `UniformLearning.signVal_mul_chi_mem_Icc`.
  - Landings of 2026-10-19 before the rule: about 25 `AffineDisperser` names; the natural-proofs
    predicates `IsNatural`, `IsLarge`, `IsUseful`, `IsCircuitTest`, `truthTableGenerator` and their
    lemmas, moved into the `NaturalProof` namespace; 12 Ladner helpers (among them `boolDecoder`,
    `natDecoder`, `ofBits`, `dropFalsesT`); `BakerGillSolovay.unaryLanguage` and three lemmas.
* **Meaning strengthened under the old name.** On 2026-10-20 `Turing.MultiTapeNTM.DecidesInSpace`
  started to require that every branch halt (Sipser, Definition 8.1), so `NL` and `NPSPACE`
  follow the textbook convention. The former meaning is `Turing.MultiTapeNTM.RecognizesInSpace`
  (`DecidesInSpace.recognizesInSpace`); membership proofs now also need a per-instance halting
  bound, the second component of `DecidesInSpace` (read back with
  `DecidesInSpace.exists_runsInTime`).
* **Renamed modules.** On 2026-10-20 `Circuit/Boolean/MassProduction/{Sharp,SharpParameters,
  SharpStatement}` became `…/{Fine,FineParameters,FineStatement}`. Every declaration keeps a
  deprecated alias, but imports of the old module paths must be updated: a module stub would have
  no upstream counterpart, so none is kept.
* **Side effects of keeping aliases.** An alias that shares its base name with its successor makes
  the unqualified name ambiguous when both namespaces are open (for example `restrictTable`,
  `Ladner.cnfDecoder`); qualify the new name. A `def` alias does not unfold to the old body under
  `unfold` or `simp [old]`.
* **Two multigraph namespaces.** Since 2026-10-20 the frontier multigraph
  (`Cslib.Circuits.Frontier.Multigraph`) defines its simple graph as that of the multigraph given by
  its ends (`Cslib.Multigraph`), and its module publicly imports the latter. Their shared base names
  `toSimpleGraph`, `toSimpleGraph_adj`, `edgeCut` and `mem_edgeCut` are ambiguous when both
  namespaces are visible, for example inside `namespace Cslib.Circuits.Frontier` or with both
  opened; use dot notation (`G.toSimpleGraph_adj`) or full names. Upstreaming the frontier
  multigraph therefore follows `Foundations/Combinatorics/Multigraph.lean`.

The [historical ledger](https://github.com/SamuelSchlesinger/complexitylib2/blob/d0e6373970029a91018528463ca7a5ccd0fc9fd1/UPSTREAM.md)
preserves earlier integration notes and per-module follow-up ideas.
