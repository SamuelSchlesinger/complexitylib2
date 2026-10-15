# Upstream ledger

Base pin: `leanprover/cslib` main @ `b2d4c7c3c08420144c9f80f5277d4bb3e1c99df1` (2026-10-13),
toolchain `leanprover/lean4:v4.35.0-rc4`, Mathlib `44086b6e` (transitive).

Statuses: `candidate` (not yet proposed), `submitted #N`, `merged @SHA` (file deleted here),
`local-only (reason)`.

## Modules

| Module (here) | Upstream path | Status | Notes |
|---|---|---|---|
| `Complexity.Init` | — | local-only (root re-export of `Cslib.Init`) | |
| `Complexity.Foundations.Data.Nat.PolynomialBound` | `Cslib/Foundations/Data/Nat/PolynomialBound.lean` | merged @b2d4c7c3 (#1067) | local copy deleted |
| `Complexity.Foundations.Data.Nat.PolynomialBound.Closure` | `Cslib/Foundations/Data/Nat/PolynomialBound/Closure.lean` | candidate (ready: #1067 merged) | `fun_prop` registration and closure lemmas; the next PR to open |
| `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs` | same path | submitted #1126 (approved) | verbatim copy; delete when merged |
| `Complexity.Logics.Propositional.CNF`, `.CNF.ExactlyOne` | `Cslib/Logics/Propositional/CNF*.lean` | candidate | generic CNF over any variable type, renaming, one-hot constraints |
| `Complexity.Computability.Machines.Turing.MultiTape.{Encodings.{Basic,Pair,List,Option,Nat},Combinators.Encoding,Complexity.PolyTime}` | same paths in crei's branch | subset of `crei/tidy-universal` | verbatim definitions only (`frame`, `encPair`, `encList`, `encOption`, `encNat`, `encBool`, `encBits`, `PolyBounded`, `ComputableTidilyInPolyTime`); delete when crei's files land |
| `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length` | same path | candidate | length bounds for `encList` |
| `Complexity.Computability.Complexity.{Classes.P,Classes.NP,Reduction}` | `Cslib/Computability/Complexity/…` | candidate | explicit encodings; `P`/`NP` via crei's `ComputableTidilyInPolyTime`; must be reconciled with crei's #767 `DTIME`-based `P` over languages |
| `Complexity.Computability.Complexity.Problems.{SAT,ThreeSAT}` | `Cslib/Computability/Complexity/Problems/…` | candidate | `SAT` with `encCNF`, verifier correctness; `ThreeSAT`, correctness of `SAT ≤ 3SAT` |
| `Complexity.Logics.Propositional.CNF.ThreeCNF` | `Cslib/Logics/Propositional/CNF/ThreeCNF.lean` | candidate | splitting clauses into width three |
| `Complexity.Computability.Machines.Turing.MultiTape.{Run,OutView}` | additions to `Configuration.lean`/`Deterministic.lean`, new `OutView.lean` | candidate | generic run lemmas (`runFrom_succ` arrived upstream with #1021 and was deleted here); the shared time and space bounds read on deterministic runs (`halted_of_runsInTime`, `spaceUsed_le_of_runsInSpace`; the converses are in crei's #1111) |
| `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Shadow` | same path; the run lemmas into `TapeLemmas.lean` | candidate | shadowing every work tape with a tape marking the visited cells, for any alphabet and two marks; visited cells form an interval and unvisited cells keep their contents; uses twice the space |
| `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ClearShadowed` | same path | candidate | a two-tape machine clearing a work tape along its shadow in `a + 2 b + c + 5` steps, for any alphabet with two distinct marks |
| `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.SequentialSpace` | addition to `Plumbing/Sequential.lean` | candidate | the space of a `seq` run from any configuration (exported form of what `transformsTapes_seq` proves inline) |
| `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView` | addition to `Plumbing/ExtendTapes.lean` | candidate | `viewCfg` and the run/space of `extendTapes` under any embedding; on upstreaming, `oneTapeCfg i = viewCfg (tapeEmb i)` (by `rfl`) and the `tapeEmb` lemmas should be derived from these |
| `Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm` | same path | candidate (after #1126; coordinate with crei on #611) | **plain computations become tidy**: within `2 t + 3 s + 2 k + 4` steps and `2 s + 2 k (3 s + 2 k + 3)` cells, for any alphabet with two marks (`ComputesInTimeAndSpace.computesTidily_tidy`); function form `ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`; `runFrom_nop_withState` belongs next to `runFrom_nop_one`. crei's #1111 has only the zero-space case. Open: space `2 s + O(k)` (needs head bounds for `clearShadowed`); `Fin.castAdd_ne_natAdd` to Mathlib |
| `Complexity.Computability.Machines.Turing.MultiTape.Feature` | same path; `windowList` into `ConfigBound.lean` | candidate | features of a configuration, one-hot groups of basic features, the step equation as disjunctions of terms; shared by the circuit simulation and the Cook–Levin tableau |
| `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run` | addition to `Plumbing/Tidy` | candidate (after #1126) | a tidy computation as an equation on `runFrom` |
| `Complexity.Computability.Circuit.Boolean.PPoly` | `Cslib/Computability/Circuit/Boolean/PPoly.lean` | candidate | redo of withdrawn #1100 without frames: `SIZE` and `PPoly` over `Language.slice` and upstream `complexity` |
| `Complexity.Computability.Circuit.Boolean.PPolyHard` | same path | candidate | a language outside `P/poly`, from upstream Shannon |
| `Complexity.Computability.Complexity.Problems.{IndependentSet,Clique}` | same paths | candidate | Karp's `SAT ≤ IndependentSet` and `IndependentSet ≤ Clique`, correctness (polynomial time open) |
| `Complexity.Computability.Circuit.Boolean.Synthesis`, `Complexity.Computability.Languages.Slice` | additions to the upstream files of the same name | candidate | congruence and quantifier lemmas for `Synthesis`; slices of `⊥`, `⊤`, complement, union, intersection |
| `Complexity.Computability.Circuit.Boolean.Threshold` | same path | candidate | threshold and majority functions with quadratic synthesis cost |
| `Complexity.Computability.Circuit.Complexity` | addition to `Cslib/Computability/Circuit/Complexity.lean` | candidate | complexity of computing `m` functions side by side |
| `Complexity.Computability.Circuit.Boolean.Substitution` | same path | candidate | substituting variables and constants for inputs costs at most two gates |
| `Complexity.Computability.Circuit.Approximation` | same path | candidate | the approximation method over straight-line programs, using upstream `Program.cost` (port of v1 `Algebraic`) |
| `Complexity.Computability.Circuit.Boolean.Hierarchy` | same path | candidate | one truth-table entry costs `2n + 3` gates; the circuit size hierarchy `SIZE s ⊂ SIZE t` |
| `Complexity.Computability.Circuit.{Support,FanIn}` | same paths | candidate | input supports, essential inputs (stated with Mathlib's `DependsOn`), and the fan-in size and depth bounds |
| `Complexity.Computability.Circuit.Clique` | same path | candidate | the clique function on `Sym2` edges, its `SimpleGraph` reading, complete and multipartite test inputs |
| `Complexity.Computability.Circuit.Monotone.Basic` | same path | candidate | the monotone basis (constants, conjunction, disjunction) and monotonicity |
| `Complexity.Computability.Circuit.Monotone.Clique.{Approximator,Positive,Negative,LowerBound,Essential,Asymptotic}` | same paths | candidate | Razborov's monotone lower bound: the monotone circuit complexity of `k`-clique exceeds `2 ^ (2 ⌊√k⌋)` for `2 ≤ k`, `k ^ 4 ≤ n`; rewritten from the v1 port after a cslib-style review |
| `Complexity.Computability.Circuit.Program` | addition to `Cslib/Computability/Circuit/Program.lean` | candidate | lines read earlier gates (`Program.lt_of_lines_wires_eq_gate`), induction along the program order (`Program.wire_induction`) |
| `Complexity.Computability.Circuit.Simulation` | addition to `Cslib/Computability/Circuit/Simulation.lean` | candidate | `Program.cost_eq_sum`, `Program.cost_le_mul` |
| `Complexity.Computability.Circuit.Boolean.Restriction` | same path | candidate | restrictions `Fin n → Option Bool`, `fill`, `free`, as substitutions; `assign`/`unassign` as `Finset.piecewise`; the information order `Extends`; the `(m choose ℓ) 2 ^ (m - ℓ)` extensions with `ℓ` free bits; subfunctions on a set of bits as restrictions |
| `Complexity.Computability.Circuit.Boolean.Formula` | same path | candidate | De Morgan formula constructors `const`, `not`, `and`, `or`, `xor`, balanced `orList`/`andList`, literals, DNF existence, `formulaDepth` and its API; open: the constructors live in the generic `Formula` namespace and would clash with monotone formulas |
| `Complexity.Foundations.Data.Hamming` | Mathlib `InformationTheory/Hamming.lean` | candidate | `hammingDist_eq_one_iff`, `hammingDist_update_of_ne`, `hammingEdges` and their counts |
| `Complexity.Computability.DecisionTree.Basic` | same path | candidate | decision trees, depth, grafting, queried variables certify the output, decision tree complexity |
| `Complexity.Computability.DecisionTree.Sensitivity` | same path | candidate | sensitivity, block sensitivity, certificate complexity and `s ≤ bs ≤ C ≤ D` |
| `Complexity.Computability.DecisionTree.Certificate` | same path | candidate | certificates for different values conflict; `D(f) ≤ C₀(f) C₁(f) ≤ C(f)²` |
| `Complexity.Computability.DecisionTree.Parity` | same path | candidate | parity is sensitive everywhere, so its sensitivity, block sensitivity, certificate and decision tree complexity are all `n` |
| `Complexity.Logics.Propositional.DNF` | `Cslib/Logics/Propositional/DNF.lean` | candidate | terms and formulas in disjunctive normal form, dual to the CNF file, with de Morgan negation into CNF |
| `Complexity.Computability.DecisionTree.NormalForm` | same path | candidate | a depth-`d` decision tree as a DNF and a CNF of width `d` whose terms read each variable once |
| `Complexity.Computability.DecisionTree.CanonicalTree` | same path | candidate | the canonical decision tree of a restricted DNF (query the free variables of the first unfalsified term), its correctness and depth bound by query paths |
| `Complexity.Computability.DecisionTree.Switching` | same path | candidate | Håstad's switching lemma, counting version, by Razborov's encoding, among the extensions of any restriction: at most `#E(ℓ - s) (4k)^s` extensions with `ℓ` free variables leave a read-once width-`k` DNF of decision tree complexity `≥ s` |
| `Complexity.Computability.DecisionTree.Restrict` | same path | candidate | answering queries in a decision tree: restricting and post-composing do not raise decision tree complexity, post-composing with an injective map (e.g. negation) preserves it |
| `Complexity.Computability.Circuit.Boolean.Unbounded` | same path (next to cslib's `Boolean/Basic.lean`) | candidate | the AC⁰ basis: negation and conjunction/disjunction of every arity, and its extension by one gate family (`extSignature`, `extInterpretation g`, `toExt`), the bases of TC⁰ and AC⁰[q] |
| `Complexity.Computability.Circuit.Boolean.Hastad` | same path | candidate | shallow functions under restrictions; one stage of restrictions for any family of operations applied to shallow functions (`exists_extension_shallow`), run over the gates of a circuit sorted by depth: **Håstad's theorem**, a depth-`d` unbounded fan-in circuit for the parity of `n` bits has at least `2 ^ s` gates whenever `s ≥ 2` and `s (16 s + 1) ^ d ≤ n`, and the same for formulas through `Formula.toCircuit` |
| `Complexity.Computability.Circuit.Boolean.AC0` | same path | candidate | constant/negation/binary-gate circuits over any basis containing the unbounded one, closure of `ConstDepth` under the Boolean operations, the class AC⁰, **parity ∉ AC⁰** |
| `Complexity.Computability.Circuit.Boolean.Majority` | same path | candidate | the constant-depth reduction of parity to majority (padding gives every threshold, two thresholds give "exactly `k`") over every basis containing the unbounded fan-in basis, **majority ∉ AC⁰** |
| `Complexity.Computability.Circuit.CompositionDepth` | addition to `Circuit/Composition.lean` | candidate | depths of continued programs; `depth (d.comp c) ≤ depth d + depth c`, `depth (c.append d) ≤ max` |
| `Complexity.Computability.Circuit.Boolean.TC0` | same path | candidate | TC⁰ over the basis extended by majority, **AC⁰ ⊊ TC⁰**, parity ∈ TC⁰ |
| `Complexity.Computability.Circuit.MapOp` | same path (or `Circuit/Program.lean`) | candidate | maps of signatures (`Signature.Hom`: `FunLike`, `id`, `comp`), the Prop class `Hom.Preserves`, and the translation of lines/programs/circuits along them (functorial, keeping size, depth and evaluation); open: a bridge `Preserves → SimulatesWithCost (fun _ => 1)` to cslib's simulation API |
| `Complexity.Computability.Circuit.Boolean.ConstDepth` | same path | candidate | `Boolean.DepthClass I D` (polynomial size, depth `O(D n)`) and `ConstDepth I` (AC⁰, AC⁰[q] and TC⁰ are instances); monotone along meaning-preserving maps of bases |
| `Complexity.Computability.Circuit.Boolean.Spira` | same path | candidate | **Spira's theorem**: a De Morgan formula with `L` leaves has an equivalent formula with at most `4 ⌈log₂ L⌉` AND/OR gates on every path, via a balanced split (`C.substLast G = F`) over any basis of fan-in two; conversely `L ≤ 2 ^ depth`, so formula depth is `Θ(log` leaf size`)` |
| `Complexity.Foundations.Data.BitString.Fourier` | same path (or Mathlib, next to `Analysis/Fourier/FiniteAbelian`) | candidate | Fourier analysis on the cube: characters `χ_S`, orthonormality, the Fourier expansion and uniqueness of coefficients, linearity (`fourierCoeffₗ`), Plancherel and Parseval (O'Donnell Ch. 1); open for a Mathlib route: express `chi S` as an `AddChar` and reuse `Analysis/Fourier/FiniteAbelian/Orthogonality` |
| `Complexity.Computability.DecisionTree.Fourier` | same path | candidate | decision trees of depth `d` have Fourier degree at most `d` |
| `Complexity.Foundations.Data.BitString.FourierRestriction` | same path | candidate | Fourier coefficients of restrictions `x ↦ f (J.piecewise x z)` and their expected squares over `z` (O'Donnell Ch. 3), towards Linial–Mansour–Nisan |
| `Complexity.Foundations.Combinatorics.DepthReduction` | same path | candidate | **Valiant's depth reduction** for edge sets with a grading (labelling increasing along edges): removing `r / k` of the edges divides `2 ^ k` levels by `2 ^ r` |
| `Complexity.Computability.Circuit.Boolean.Nondeterminism` | same path | candidate | guessing the last `p` inputs (`∃`/`∀`) costs at most `2 ^ p (C + 3) + 1` gates |
| `Complexity.Logics.Propositional.Resolution` | same path | candidate | the resolution rule (with pivots), derivations, **soundness and refutation completeness** of resolution (Davis–Putnam splitting, lifting the refutations); open: weakening/subsumption for list clauses, a `Type`-valued derivation with a size for proof-complexity bounds, `satisfiable_iff_exists_restrict` |
| `Complexity.Computability.Circuit.Boolean.FirstOrder` | same path (or a descriptive-complexity directory) | candidate | first-order model checking over Mathlib's model theory (relational languages) on every structure with `n` elements by unbounded fan-in formulas of depth independent of `n` and size polynomial in `n`; open: numerical predicates (`<`, `BIT`, arbitrary: FO[Arb]) and constants, a size bound `O(|φ| n^{qr φ})` via quantifier rank, a bit-string encoding to state membership in `AC0` |
| `Complexity.Foundations.Data.HammingBound` | Mathlib `InformationTheory/Coding/HammingBound.lean` | candidate | sizes of Hamming spheres and balls for words `∀ i, β i`, and the **Hamming bound** (uniform `q`-ary corollary); open: `Hamming`/`Metric.closedBall` formulations |
| `Complexity.Computability.Circuit.Boolean.DepthClasses` | same path | candidate | `PolylogDepth I i := DepthClass I ((log n + 1)^i)` and the nonuniform hierarchies NCⁱ, ACⁱ, TCⁱ, ACⁱ[q]: monotone in `i`, `NCⁱ ⊆ ACⁱ ⊆ TCⁱ`, `ACⁱ ⊆ ACⁱ[q]`, exponent zero is constant depth; open: `ACⁱ ⊆ NCⁱ⁺¹` (needs depth-aware gate replacement) |
| `Complexity.Foundations.Combinatorics.Hypergeometric` | same path (or Mathlib `Combinatorics`) | candidate | `ℓ`-subsets containing a given set, the first two moments of `#(U ∩ J)` over random `ℓ`-subsets `J`, and Chebyshev's bound: at most half of them meet `U` in fewer than half the expected number once it is at least 8 (towards LMN) |
| `Complexity.Computability.Circuit.Boolean.HastadCounting` | same path (or inside `Hastad`) | candidate | double counting extensions of restrictions, and the counted stages of Håstad's argument: at most a `G / 2 ^ s` fraction of the restrictions leaving `n / (16 s + 1) ^ j` bits free make a gate of depth `≤ j` deep (towards LMN) |
| `Complexity.Computability.Circuit.Boolean.LMN` | same path | candidate | **the Linial–Mansour–Nisan theorem**: Fourier weight above `k` of a depth-`d` size-`g` unbounded fan-in circuit is at most `2 g / 2 ^ s` when `max 8 (2 s) n ≤ k ⌊n / (16 s + 1) ^ d⌋`; open: the asymptotic corollary and the learning consequence |
| `Complexity.Computability.Circuit.Boolean.NormalFormParity` | same path | candidate | DNFs for functions sensitive everywhere have a term per true input; DNFs and CNFs for parity have at least `2 ^ (n - 1)` terms/clauses |
| `Complexity.Foundations.Data.Fin.Append` | Mathlib `Algebra/BigOperators/Fin.lean` | candidate | `Fin.card_filter_append`: counting in an appended tuple |
| `Complexity.Foundations.Data.BitString.LowDegree` | same path | candidate | functions of degree at most `D` on the cube over a commutative ring, as the span of monomials of bits; closure, every function has degree `n`, dimension bound |
| `Complexity.Foundations.Data.BitString.LowDegreeParity` | same path | candidate | over a field with `2` invertible, a degree-`D` function agrees with parity on at most `#{S : |S| ≤ n/2 + D}` inputs |
| `Complexity.Foundations.Combinatorics.CentralBinomial` | Mathlib `Combinatorics/Choose` for the binomial bounds | candidate | `C(n, ⌊n/2⌋)² (n + 1) ≤ 4 ^ n`; at most `6/10` of sets have at most `n/2 + t` elements when `100 (t + 1)² ≤ n + 1` |
| `Complexity.Computability.Circuit.Boolean.ModGates` | same path | candidate | `MOD_q` gates, AC⁰[q] over the basis extended by them, `AC⁰ ⊆ AC⁰[q]` |
| `Complexity.Computability.Circuit.Boolean.Smolensky.{Gates,Approximation}` | same paths | candidate | gate approximators over `ZMod p` (OR by random subsets, exact `MOD_p` by Fermat) and Smolensky's approximation of circuits, via a paired interpretation (true function, approximant) |
| `Complexity.Computability.Circuit.Boolean.Smolensky` | same path | candidate | **Razborov–Smolensky**: the size–depth tradeoff for parity and parity ∉ AC⁰[p] for odd primes `p` |
| `Complexity.Computability.Circuit.Boolean.Smolensky.Majority` | same path | candidate | majority ∉ AC⁰[p] and **TC⁰ ⊄ AC⁰[p]** for odd primes `p` |
| `Complexity.Computability.Circuit.Pi` | addition to `Circuit/Composition.lean` | candidate | single-output circuits side by side (`Circuit.pi`) and one-gate circuits (`Circuit.oneGate`), with eval/size/depth |
| `Complexity.Computability.Circuit.Depth` | addition to `Circuit/Depth.lean` | candidate | the wires a gate reads are shallower than it; gates have positive depth |
| `Complexity.Foundations.Data.Nat.PolynomialBound.Exponential` | addition to `Foundations/Data/Nat/PolynomialBound.lean` | candidate | polynomially bounded functions are eventually below `2 ^ n` |
| `Complexity.Computability.Circuit.Boolean.BinaryCost` | same path | candidate | the binary-gate cost of De Morgan programs (Jukna's measure with free negations) |
| `Complexity.Foundations.Data.BitString.Parity` | same path | candidate | the parity function on bit strings and its basic facts |
| `Complexity.Computability.Circuit.Boolean.Parity` | same path | candidate | De Morgan circuits for parity with `3 n` binary and `4 n` gates in all |
| `Complexity.Computability.Circuit.Boolean.GateElimination` | same path | candidate | Schnorr's bound: parity needs `3 (n - 1)` binary gates, exactly; gate elimination by counting nonredundant gates under partial assignments, without circuit surgery (v1 needed about 6k lines of De Morgan infrastructure) |
| `Complexity.Computability.Circuit.Formula` | same path | candidate | formulas over a signature (trees of operations), evaluation, homomorphisms, leaf size, size, depth, leaf-size bounds under bounded fan-in, formulas as circuits (`toCircuit`: same function and size, no deeper), substitution for inputs (`bind`, `lift`, `substLast`); open review items: an `Equiv` with `PFunctor.FreeM`, a formula complexity measure |
| `Complexity.Computability.Circuit.Boolean.Khrapchenko` | same path | candidate | Khrapchenko's bound `|E(A,B)|² ≤ L · |A| · |B|`, the neighbour-count form, parity needs `n²` leaves and depth `2 log₂ n`, exact for powers of two |
| `Complexity.Computability.Circuit.Boolean.Nechiporuk` | same path | candidate | Nechiporuk's lemma (`≤ 16 ^ l / 4` subfunctions for `l ≥ 1` leaves in a block) and bound `∏ cᵢ ≤ 2 ^ (4 L + k)`; the binary step holds for any binary gate, so formulas over the full binary basis are a short extension |
| `Complexity.Computability.Circuit.Boolean.ElementDistinctness` | same path | candidate | element distinctness has at least `2 ^ (t (m - 1))` subfunctions per block, hence `m (m - 1) t ≤ 4 L + m`, also at `t = ⌈log₂ m⌉` |
| `Complexity.Computability.Communication.Protocol` | same path | candidate | deterministic two-party protocols (`Cslib.Communication.Protocol`), depth, leaves, solving a relation, communication complexity in `ℕ∞` with the API of cslib's `ecomplexity` |
| `Complexity.Computability.Circuit.Boolean.KarchmerWigderson` | same path | candidate | formulas give protocols and protocols give formulas (negations at leaves); formula depth with free negations equals the communication complexity of the Karchmer–Wigderson game; open: size version, monotone game |
| `Complexity.Computability.BranchingProgram.MonoidProgram` | same path | candidate | programs over a monoid (`FreeMonoid` of instructions, evaluation a monoid hom), maps along homs, inverses over groups, negation and commutators of computed functions |
| `Complexity.Foundations.GroupTheory.Perm.FiveCycle` | Mathlib `GroupTheory/Perm/Cycle/Type.lean` | candidate | `Equiv.Perm.IsFiveCycle` like `IsThreeCycle`; five-cycles are conjugate and every five-cycle of `Fin 5` is a commutator of five-cycles |
| `Complexity.Computability.Circuit.Boolean.Barrington` | same path | candidate | Barrington's theorem: depth-`d` formulas give width-`5` permutation branching programs of length `4 ^ d`; conversely width-`w` length-`L` branching programs (over `Function.End (Fin w)`) give formulas of depth `O(log w · log L)` with negations at the leaves |
| `Complexity.Foundations.Combinatorics.Sunflower.Pluck` | same path | candidate | plucking sunflowers as a relation, normal forms and their size |
| `Complexity.Foundations.Data.Nat.Choose` | Mathlib `Combinatorics/Choose/Bounds` or cslib | candidate | scaling bounds for binomial coefficients |
| `Complexity.Foundations.Combinatorics.Sunflower` | `Cslib/Foundations/Combinatorics/Sunflower.lean` (or Mathlib) | candidate | the Erdős–Rado sunflower lemma |
| `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame` | addition to crei's `Encodings/Basic.lean` | candidate | the bits of `frame w` |
| `Complexity.Foundations.Combinatorics.MajorityVote` | `Cslib/Foundations/Combinatorics/MajorityVote.lean` | candidate | counting form of the Chernoff bound for majority votes; good samples for `2 ^ n` tests at once |
| `Complexity.Computability.Circuit.Boolean.BoundedError` | same path | candidate | Adleman's theorem for Boolean functions `F (x ++ r)`, two-sided and one-sided error, per length and for `P/poly` |
| `Complexity.Computability.Complexity.Classes.BPP` | `Cslib/Computability/Complexity/Classes/BPP.lean` | candidate | `BPP` through polynomial-time machines reading random strings, mirroring `NP` |
| `Complexity.Computability.Complexity.Classes.RP` | `Cslib/Computability/Complexity/Classes/RP.lean` | candidate | `RP`, `coRP`; `RP ⊆ NP` (`coNP` added to `NP.lean`). `ZPP` deferred until it can be defined faithfully |
| `Complexity.Computability.Circuit.Boolean.{MachineSimulation,PolynomialTime}` | same paths | candidate | redo of withdrawn #1101: feature-by-feature simulation via `Synthesis`, `O(T(n+T))` cost; `PPoly.of_mem_P` (P ⊆ P/poly), `PPoly.of_mem_BPP` (BPP ⊆ P/poly) |
| `Complexity.Computability.Complexity.CookLevin.{Tableau,Correctness,Reduction}` | same paths | candidate | tableau over upstream `MultiTapeTM`, its correctness, the reduction's correctness |
| `Complexity.Computability.Complexity.CookLevin.Staging` | — | local-only (assembles the theorem from the two open polynomial-time facts; replaced by an unconditional statement once crei's calculus lands) | |

## Upstream work we depend on or must not duplicate

| Item | Where | Status (2026-10-13) | Our use |
|---|---|---|---|
| `PolynomiallyBounded` | cslib PR #1067 (`Cslib/Foundations/Data/Nat/PolynomialBound.lean`) | merged 2026-10-13 | L1; used directly from cslib. **Overlaps crei's `PolyBounded size u`** (a bound in terms of a size function); upstream will need one notion with a bridge lemma |
| `MultiTapeTM.comp` with intermediate-length bound | cslib PR #1111 (`Combinators/Comp.lean`, crei) | open | L3 composition primitive |
| `iterateWhile` | cslib PR #1112 (crei) | open | L3 loop primitive |
| `Tidy` computations | cslib PR #1126 (crei) | open | L3 normal form |
| Probabilistic programs with typed oracles | cslib PR #1129 (`Cslib/Languages/Probabilistic/Basic.lean`) | open | L4 template |
| `PFunctor.FreeM` extensions | cslib PRs #1086–#1089 (dtumad) | open | L4 base |
| `TapeEncodable` typeclass | cslib issue #590 | open | L1 `Encoding` must satisfy it |
| Complexity theory plan | cslib issue #611 (crei) | open | post L2/L3/L4 design there before PRs |
| **Tidy calculus, encodings, polynomial time with `fun_prop`, universal machine** | crei's fork branch `crei/tidy-universal` (39 commits, ~9.3k lines, based on cslib `1b51f0cc`; not yet a PR) | in progress | this *is* L1/L3/L4: `frame`/`encPair`/`encList`/`encNat`, `ComputableTidilyInPolyTime` registered with `fun_prop`, folds, iterate-while, arithmetic, and a polynomial-time universal machine as an interpreter program. Merges into current main with two trivial conflicts. v2 must build on it rather than duplicate it |
| `DSPACE s ⊆ ⋃ c, DTIME (n * 2 ^ (c * s n))`, `L ⊆ P`, `PSPACE ⊆ EXP`, class definitions | cslib PR #767 (crei, draft; part split into #768) | draft | do not duplicate; the space-to-time inclusion belongs there |

## Withdrawn upstream PRs this library redoes

| PR | Topic | Reviewer ask | Redo in |
|---|---|---|---|
| #1099 / #1100 / #1101 | FP/poly, P/poly, P ⊆ P/poly | more abstract word encoding, textbook source | L6 (phase 5) via L1 `Encoding` |
| #869, #871–#875 | TM composition | work above configuration level (now `TransformsTapes`) | L2 effectful combinators follow `TransformsTapes`-style specs |
