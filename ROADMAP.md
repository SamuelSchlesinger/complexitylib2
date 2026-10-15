# complexitylib v2 — roadmap and design

## Context

complexitylib v1 (`~/projects/lean/complexitylib`, 894k lines, 0 sorry, 0 axioms) proved a
large body of complexity theory, but over its *own* Turing machine and its *own* typed
circuits. cslib was bolted on in September 2026 through after-the-fact bridges
(`Complexitylib/Interop`, `Complexitylib/Cslib`), the cslib pin went stale, bespoke machines
cost 6k–50k lines each, and the upstream PRs that came out of it were withdrawn (FP/poly,
P/poly: encoding abstraction; TM composition: configuration-level plumbing, superseded by
crei's `TransformsTapes`).

v2 starts from an empty `lake new` project (`~/projects/lean/complexitylib2`) and is built
**on cslib as the base**, with every module written so it could be upstreamed as-is.
v1 supplies the *content* (which constructions and theorems, in which order); cslib and the
user's `crypto-frontier` branch supply the *ergonomics* (definitions, proof strategies,
`fun_prop`/Aesop-driven complexity proofs, free-monad programs).

## Design directives (from the user)

1. **Content from v1, ergonomics from cslib / crypto-frontier.**
2. **`fun_prop` for the complexity of reductions**: "this function is poly-time" is a
   compositional `fun_prop` call, following `PolynomiallyBounded` in
   `Cslib/Foundations/Data/Nat/PolynomialBound.lean` (crypto branch, upstream PR #1067).
3. **A universal, ergonomic combinator language**: programming TMs should feel like
   straight-line code in a free monad with queries, randomness, and whatever else; the
   machine realisation and its time bound come out compositionally.
4. **UTMs are a prerequisite** for (3) in full generality (programs as data, simulation with
   accounted overhead), so UTMs are on the critical path.

## Decisions (user Q&A, 2026-10-12)

| Decision | Choice |
|---|---|
| Base pin | **Upstream `leanprover/cslib` main**, pinned to a SHA. No fork pin. |
| Machine model | **One parametric machine** (crypto-frontier style) defined *in v2*, proven step-exactly equivalent to upstream `Turing.MultiTapeTM` / `MultiTapeNTM` in the effect-free case. See "Does that work?" below. |
| Milestone 1 | **Cook–Levin** (SAT is NP-complete), NP via verifiers [AroraBarak09, Def. 2.1]. Revised 2026-10-13 from "UTM + time hierarchy": the reduction is a Lean function on encoded data, so its polynomial-time proof is the real test of the `fun_prop` calculus, and no machine-level UTM is needed. |
| Tight hierarchy (later) | Tape-indexed, linear overhead: `DTIME_k f ⊊ DTIME_{k+c} g` for `f = o(g)`, via a `(k+3)`-tape UTM built from exact-cost tape transformers (one UTM tape per simulated tape with fixed-width symbol blocks, a table tape, an amortised binary clock). The Arora–Barak `f log f` form follows by adding Hennie–Stearns as a separate simulation lemma. Not a `fun_prop` artefact: the calculus certifies polynomial bounds only. |
| Free monad | **`PFunctor.FreeM`** (`Cslib/Foundations/Data/PFunctor/Free.lean`, dtumad's #1086–#1089 build on it; the pfunctor experiment ported the crypto stack with 3 files changed). |

### "Implement our own oracle TM and prove it equivalent to upstream without oracles — does that work?"

Yes, under three conditions, all of which v2 adopts:

1. **Extend, don't copy.** The parametric machine reuses upstream's `Turing.Cfg` and
   `Turing.Action` (`Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean`)
   as *components*: a general configuration is `{ core : Turing.Cfg k Symbol State input,
   channels : Oracle → Channel }` and a general action is upstream's action plus per-channel
   query/answer actions. Then the effect-free step *is* upstream's `Action.apply` on the
   `core` field, and `ofDeterministic`/`toDeterministic` are step-for-step bisimulations
   (one step = one step; the same work cells visited). Time and space therefore transfer
   *exactly*, not up to constants — unlike v1's interop (3× time, space one-way).
2. **Recover both upstream machines.** Make the choice functor cover nondeterminism too:
   `Tr : State → Option Symbol → (Fin k → Option Symbol) → Choose (Action …)` with
   `Choose := Id` (= `MultiTapeTM`), `Choose := Set` (= `MultiTapeNTM.Tr … → Action → Prop`),
   `Choose := (Bool → ·)` (fair coin, PTM). Prove `MultiTapeNTM ≃ Machine … Empty Set` and
   `MultiTapeTM ≃ Machine … Empty Id` as definitional-as-possible equivalences, so
   `ComputableInTimeAndSpace`, `TransformsTapes`, `RunsInTime/Space`, `ConfigBound`
   and every upstream combinator transfer by one lemma each.
3. **Upstream path exists.** This is exactly how #964 made `MultiTapeTM extends MultiTapeNTM`.
   The eventual upstream PR is "generalise MultiTapeNTM to effects; the current types become
   instances", with the equivalence theorems as the evidence that nothing downstream breaks.
   Until then the general machine lives in v2 at the upstream path.

What it does *not* buy: upstream combinators (`seq`, `extendTapes`, crei's `comp`,
`iterateWhile`) only transfer to the effect-free fragment. Effectful combinators
(query-preserving `seq`/`comp`, clock, replay) must be written for the general machine;
crypto-frontier's `Oracle/*.lean` (3.2k lines) is the template, and they should be written
*once* for the general machine rather than per effect.

## Status (2026-10-13)

Milestone 1 (Cook–Levin) is complete except for two polynomial-time facts:

| Piece | Module | State |
|---|---|---|
| CNF over any variables, relabelling, exactly-one | `Logics/Propositional/CNF*.lean` | proved |
| `P`, `NP` (verifiers, `Polynomial ℕ` certificate length), reductions, `NPHard` | `Computability/Complexity/{Classes,Reduction}` | defined |
| `SAT`, `encCNF`, verifier correctness | `Problems/SAT.lean` | proved |
| Tableau of a multi-tape run and its correctness | `CookLevin/{Tableau,Correctness}.lean` | proved (`tableau_satisfiable_iff`) |
| The reduction and its correctness | `CookLevin/Reduction.lean` | proved (`reduce_mem_SAT_iff`) |
| `NPComplete encCNF SAT` from the two polynomial-time facts | `CookLevin/Staging.lean` | proved (local-only staging) |
| `ComputableTidilyInPolyTime SAT.verifier …` and `… (reduce tm p c d enc) …` | — | **open**: needs crei's calculus |
| `ThreeSAT` and correctness of `SAT ≤ 3SAT` | `Problems/ThreeSAT.lean`, `CNF/ThreeCNF.lean` | proved (polynomial time open) |

Circuit track (independent of the calculus): `P/poly` over upstream circuits and `Language.slice`,
and **`P ⊆ P/poly` proved** (`Cslib.Circuits.Boolean.PPoly.of_mem_P`) by a feature-by-feature
simulation built from upstream `Synthesis` (state, heads, cells and output view at step `t + 1` as
Boolean combinations of step-`t` features, `O(n + T)` gates per feature, `fun_prop` for the
polynomial bound). This redoes the withdrawn cslib PRs #1100/#1101 without frame encodings. Also proved: some
language is not in `P/poly` (from upstream Shannon), and Karp's reductions `SAT ≤ IndependentSet`
and `IndependentSet ≤ Clique` are correct (their polynomial time awaits the calculus).
The simulation is stated over `Turing.MultiTapeTM.Feature` (`MultiTape/Feature.lean`): finite
observations of a configuration with one lemma per kind describing how a step changes it, meant
to be shared with the Cook–Levin tableau. `Threshold.lean` gives threshold and majority functions
with quadratic synthesis cost, the ingredient for amplification in `BPP ⊆ P/poly`. A non-vacuity
test builds a constant machine and checks that `P encBits` and the hypothesis of `P ⊆ P/poly` are
inhabited.

**BPP, RP, coRP ⊆ P/poly proved** (`Cslib.Circuits.Boolean.PPoly.of_mem_BPP`,
`PPoly.of_mem_RP`, `PPoly.of_mem_coRP`; for any instance encoding via `PPoly.exists_of_mem_BPP`
and `PPoly.exists_of_mem_RP`, from promise versions of Adleman's theorem), together with `RP ⊆ NP`
and `SIZE` classes with
`P/poly = ⋃ SIZE (c (n + 1) ^ c)`. Adleman's theorem is stated for Boolean functions `F (x ++ r)`
without machine encodings (`complexity_le_of_boundedError`); the `frame` bridge to machines lives
in `PolynomialTime.lean`. `ZPP` is deferred: its expected-time definition does not fit worst-case
`ComputableTidilyInPolyTime`, and a Las Vegas definition needs `Option Bool` outputs in the circuit
simulation. `BPP` is defined like `NP`,
through a polynomial-time function reading a random string, with the error written as a count.
The proof goes through Adleman's theorem in circuit form (`PPoly.of_boundedError`: bounded error
over a `P/poly` language stays in `P/poly`), built from three upstreamable pieces: a counting
Chernoff bound for majority votes (`Foundations/Combinatorics/MajorityVote.lean`), the cost of
computing functions side by side (`Circuit/Complexity.lean`), and restrictions that hardwire
inputs (`Circuit/Boolean/Substitution.lean`).

**The circuit size hierarchy proved** (`Cslib.Circuits.Boolean.SIZE_ssubset`): changing one
truth-table entry costs at most `2 n + 3` gates, so walking from a constant to a Shannon-hard
function attains every size below `2 ^ n / n` up to `2 n + 3`; in particular
`SIZE ((n + 1) ^ k) ⊂ SIZE ((n + 1) ^ (k + 1))` for `k ≥ 1` (`SIZE_pow_ssubset`).

**Razborov's monotone lower bound for cliques** (`Circuit/Monotone/Clique/`): for `2 ≤ k` with
`k ^ 4 ≤ n`, the monotone circuit complexity of `k`-clique on `n` vertices exceeds `2 ^ (2 ⌊√k⌋)`
(`Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_ecomplexity_clique`), and it is finite
(`ecomplexity_clique_ne_top`). Ported from v1 and then rewritten after a cslib-style review: edges
are `Sym2` pairs with a bridge to `SimpleGraph.IsNClique`, the monotone basis has constants,
approximators are one structure interpreted like any other interpretation of the circuit, plucking
is a `Prop`-valued relation reusing upstream `Relation.RelatesInSteps`, and the generic pieces live
in `Foundations` (`Sunflower`, `Sunflower/Pluck`, `Nat/Choose`) and `Circuit` (`Approximation`,
`Support`, `FanIn`, `Clique`). The clique-specific files went from about 3,400 lines in v1 to about 1,750; with the generic
infrastructure, from about 4,500 to about 2,600.

**Schnorr's bound for parity** (`Circuit/Boolean/GateElimination.lean`): a De Morgan circuit
computing the parity of `n` bits has at least `3 (n - 1)` AND and OR gates
(`Cslib.Circuits.Boolean.three_mul_le_cost_of_computes_parity`), and chaining
`x ⊕ y = (x ∨ y) ∧ ¬(x ∧ y)` attains it, so the count is exact (`isLeast_cost_parity`). The proof
never rewrites a circuit: for a partial assignment it counts the *nonredundant* gates (binary gates
that are neither constant, nor a literal, nor an argument up to negation once the fixed bits are
hardwired). Fixing more bits never adds one, and Schnorr's step fixes one bit so that
three of them become redundant. This replaces v1's certified-reduction framework and about 6,000
lines of De Morgan residual-circuit infrastructure with about 850 lines.

**Khrapchenko's bound** (`Circuit/Boolean/Khrapchenko.lean`, over the generic formulas of
`Circuit/Formula.lean`): a De Morgan formula that is true on `A` and false on `B` has leaf size at
least `|E(A, B)|² / (|A| |B|)`, where `E(A, B)` are the Hamming edges between them
(`Cslib.Circuits.Formula.sq_card_hammingEdges_le`). So formulas for parity have leaf size at
least `n²` and depth at least `2 log₂ n` (counting negations), threshold functions `Th^n_k` need
`k (n + 1 - k)`, and halving gives formulas of leaf size exactly `n²` for powers of two
(`isLeast_leafSize_parity_two_pow`). Formulas are trees of operations of any signature, evaluated
under an interpretation like upstream circuits, and they are circuits of at most the same size
(`Formula.exists_circuit`).

**Nechiporuk's bound** (`Circuit/Boolean/Nechiporuk.lean`): a De Morgan formula with `l ≥ 1` leaves
in a block `Y` has at most `16 ^ l / 4` subfunctions on `Y`, so `∏ᵢ cᵢ ≤ 2 ^ (4 L + k)` over
disjoint blocks. Element distinctness of `m` blocks of `2 t` bits, `m ≤ 2 ^ t`, has at least
`2 ^ (t (m - 1))` subfunctions per block, so its formulas have leaf size `L` with
`m (m - 1) t ≤ 4 L + m` (`Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_elementDistinctness`),
which at `t = ⌈log₂ m⌉` is of order `n² / log n` in the number `n` of bits.

**The Karchmer–Wigderson theorem** (`Circuit/Boolean/KarchmerWigderson.lean`, over the new
`Communication/Protocol.lean`): the least depth of a De Morgan formula for `f`, with negations
free, equals the communication complexity of finding a bit where a `1`-input and a `0`-input of
`f` differ (`Cslib.Circuits.Boolean.formulaDepth_eq_ecomplexity`, communication complexity in `ℕ∞`).

**Barrington's theorem** (`Circuit/Boolean/Barrington.lean`, over the monoid programs of
`BranchingProgram/MonoidProgram.lean`): a De Morgan formula of depth `d`, negations free, becomes a
permutation branching program of width `5` and length `4 ^ d` that is a fixed `5`-cycle exactly
where the formula is true (`Cslib.Circuits.Formula.exists_monoidProgram_computes`). Conversely, a
branching program of width `w` and length `L` gives a formula of depth
`(⌈log₂ w⌉ + 1) ⌈log₂ L⌉ + ⌈log₂ w⌉` with negations only at the leaves
(`Cslib.BranchingPrograms.MonoidProgram.exists_formula`), so the two models compute the same
functions with polynomially related sizes.

**Query complexity** (`DecisionTree/`): decision trees with grafting, sensitivity, block
sensitivity and certificate complexity with `s ≤ bs ≤ C ≤ D`, `D(f) ≤ C₀(f) C₁(f) ≤ C(f)²`
(`Cslib.DecisionTree.complexity_le_certificateComplexityFor_mul`), and all four measures equal `n`
for parity.

**The tidy normal form** (`Machines/Turing/MultiTape/Combinators/TidyNormalForm.lean`, over
`Plumbing/{Shadow,ClearShadowed,SequentialSpace,ExtendTapesView}.lean`): every computation of an
upstream `MultiTapeTM` within `t` steps and `s` cells becomes a tidy computation (crei's #1126)
within `2 t + 3 s + 2 k + 4` steps and `O(k s)` cells, over any alphabet with two marks
(`Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy`). An independent review (23
findings) was addressed: corrected docstrings, generic alphabets, Mathlib's `embFinTwo` and
`Finset.piecewise` reused, a named `Restriction.Extends`, redundant hypotheses dropped, the
switching lemma generalised to extensions, iff forms of the shared time and space bounds. The machine shadows every work
tape with a tape marking the visited cells, clears each work tape along its shadow, and rewinds the
input head; the shadows are needed because a work tape may hold blanks among written cells. With
it, tidiness is an implementation detail: classes can be stated over upstream's plain
`ComputableInTimeAndSpace`, and the tidy combinators (composition, iteration) apply to them.

**Håstad's switching lemma** (`DecisionTree/Switching.lean`, over `DecisionTree/CanonicalTree.lean`
and `Logics/Propositional/DNF.lean`), counting version by Razborov's encoding: if every term of a DNF
has at most `k` literals, at most `#R(ℓ - s) (4k)^s` of the restrictions leaving `ℓ` variables free
leave it with decision tree complexity at least `s`, where `#R(m) = (n choose m) 2 ^ (n - m)`
(`Cslib.Logic.PL.DNF.card_switching_le`, `Cslib.Circuits.Boolean.Restriction.card_withFree`).
The encoding is an explicit pair of functions with `decode ∘ encode = id`
(`Cslib.Logic.PL.DNF.decode_encode`). Both hold among the extensions of any restriction.

**Håstad's theorem** (`Circuit/Boolean/Hastad.lean`, over the unbounded fan-in basis
`Circuit/Boolean/Unbounded.lean`): a circuit of depth `d` with negations and conjunctions and
disjunctions of any arity that computes the parity of `n` bits has at least `2 ^ s` gates whenever
`s ≥ 2` and `s (16 s + 1) ^ d ≤ n`
(`Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity`), so size
`2 ^ Ω(n ^ (1 / (d + 1)))` at fixed depth (Håstad's exponent is `1 / (d - 1)`). The proof restricts
`d` times; after stage `j` every gate of depth at most `j` computes a function of decision tree
complexity below `s`, a gate one level up is then a narrow DNF up to negation, and the switching
lemma with a union bound over the gates gives the next stage. Formulas get the same bound through
`Formula.toCircuit` (same function and size, no deeper), and **parity is not in AC⁰**
(`Cslib.Circuits.Boolean.parity_notMem_AC0`, `Circuit/Boolean/AC0.lean`), with AC⁰ defined
over cslib circuits of
polynomially bounded size and constant depth. AC⁰ is closed under the Boolean operations, and
**majority is not in AC⁰** (`Circuit/Boolean/Majority.lean`): padding the input with constants
turns majority into every threshold function, so parity has circuits of depth four more and
polynomially larger size than majority. Depth bounds for cslib's `Circuit.comp`/`Circuit.append`
were added for this (`Circuit/CompositionDepth.lean`). AC⁰, TC⁰ and AC⁰[q] are all one
class `ConstDepth I` of polynomial-size constant-depth circuits over a basis `I`
(`Circuit/Boolean/ConstDepth.lean`), monotone along maps of bases (`Signature.Hom`, with the
translation of circuits in `Circuit/MapOp.lean`). With majority gates added to the basis
(`Circuit/Boolean/TC0.lean`), majority is one gate, so **AC⁰ ⊊ TC⁰**
(`Cslib.Circuits.Boolean.AC0_ssubset_TC0`).

**Spira's theorem** (`Circuit/Boolean/Spira.lean`): every De Morgan formula with `L` leaves has
an equivalent formula with at most `4 ⌈log₂ L⌉` AND and OR gates on every path
(`Cslib.Circuits.Boolean.exists_formula_depthWith_le_four_mul_clog`), and conversely `L ≤ 2 ^ depth`, so formula depth
and the logarithm of formula size agree up to a factor of four. The split at a subformula with a
third to two thirds of the leaves is stated for any basis of fan-in two, over substitution of
formulas for inputs (`Formula.bind`, `Formula.substLast`).

**Fourier analysis on the Boolean cube** (`Foundations/Data/BitString/Fourier.lean`, from v1's
`BooleanAnalysis/FourierExpansion` without its inner-product-space type synonym): characters
`χ_S` on cslib's `BitString`, orthonormality under Mathlib's `𝔼`, the Fourier expansion and
uniqueness of coefficients, Plancherel and Parseval. Decision trees of depth `d` have Fourier
degree at most `d` (`DecisionTree/Fourier.lean`), the first step towards Linial–Mansour–Nisan
over the switching lemma.

**First-order queries are in nonuniform AC⁰** (`Circuit/Boolean/FirstOrder.lean`, the main
result of v1's `DescriptiveComplexity` tree, rebuilt on Mathlib's model theory instead of a
bespoke first-order syntax): for a relational language, expanding quantifiers into
conjunctions over the universe decides any sentence on structures with `n` elements, read from
their atomic facts, by unbounded fan-in formulas of depth independent of `n` and size polynomial
in `n` (`Cslib.Circuits.Boolean.FirstOrder.exists_formula_realize`).

**The Linial–Mansour–Nisan theorem** (`Circuit/Boolean/LMN.lean`, beyond v1, whose docstring
mentioned but did not contain it): the Fourier weight above `k` of a function computed by an
unbounded fan-in circuit of depth `d` with `g` gates is at most `2 g / 2 ^ s` once
`max 8 (2 s) n ≤ k ⌊n / (16 s + 1) ^ d⌋`. It combines the counted stages of Håstad's argument
(`Circuit/Boolean/HastadCounting.lean`), Fourier coefficients of restrictions, decision-tree
degree, and a Chebyshev bound for random subsets (`Foundations/Combinatorics/Hypergeometric.lean`).

**Resolution** (`Logics/Propositional/Resolution.lean`): soundness and refutation completeness.

**Exponential-time SAT combinatorics.** The satisfiability coding lemma of Paturi, Pudlák and Zane
(`Logics/Propositional/CNF/Coding.lean`): a solution isolated in `ι` directions of a width-`k`
formula is coded in `N - ι / k` bits on average over orders, so `∑ₓ 2 ^ (ι(x) / k) ≤ 2 ^ N`. The
**sparsification lemma** of Impagliazzo, Paturi and Zane (`Logics/Propositional/ClauseSet/
Sparsification.lean`, over clause sets in `ClauseSet/Basic.lean`, with the proof of Calabro,
Impagliazzo and Paturi in `ClauseSet/Sparsification/{Step,Path,Tree,Bounds,Asymptotics}.lean`):
every width-`k` CNF over `N` variables is the disjunction of at most `2 ^ (ε N)` width-`k` CNFs in
which every variable occurs in at most `c(k, ε)` clauses. Normal forms of parity have at least
`2 ^ (n - 1)` terms (`Circuit/Boolean/NormalFormParity.lean`).

**Razborov–Smolensky** (`Circuit/Boolean/Smolensky.lean`, over `Smolensky/{Gates,Approximation}`,
`Foundations/Data/BitString/LowDegree{,Parity}.lean` and `Foundations/Combinatorics/CentralBinomial.lean`):
for every odd prime `p`, a depth-`d` circuit with `MOD_p` gates computing parity has size at least
`2 ^ ℓ · 2 / 5` whenever `100 (((p - 1) ℓ) ^ d + 1)² ≤ n + 1`, so **parity ∉ AC⁰[p]**
(`Cslib.Circuits.Boolean.Smolensky.parity_notMem_AC0Mod`). The circuit is evaluated on pairs of a
true function and its low-degree approximant, so each gate's approximator is chosen for its true
arguments without dependent recursion over the program. Generalises v1's `p = 3`. The reduction of
parity to majority is stated over every basis containing the unbounded fan-in basis
(`ConstDepth.parity_mem_of_majority_mem`), so parity ∈ TC⁰, majority ∉ AC⁰[p], and
**TC⁰ ⊄ AC⁰[p]** for odd primes `p`
(`Cslib.Circuits.Boolean.Smolensky.TC0_not_subset_AC0Mod`).

Independent cslib-style reviews of the gate-elimination and Khrapchenko modules were addressed:
a wrong Jukna citation was corrected (Section 1.6 for Schnorr, Section 6.8 for Khrapchenko, plus
the primary sources), a docstring overclaim was removed, Mathlib's `Function.IsConst` and
`DependsOn` replaced local duplicates (also in `Circuit/Support.lean`), generic program lemmas
moved to files mirroring `Program.lean` and `Simulation.lean` upstream, restrictions got their own
file related to substitutions, the elimination step was split into named lemmas over a new
`Program.wire_induction`, Hamming-distance-one lemmas moved to a Mathlib-bound file, two
unnecessary hypotheses were dropped from Khrapchenko's corollaries, and `Formula.leaves` became
`Formula.leafSize`. Decision trees (`DecisionTree/Basic.lean`) are started as the base for query
complexity and, later, the switching lemma.

The Cook–Levin tableau and the circuit simulation now share one description of a step. The
tableau has one variable per feature and time; its one-hot clauses come from `Feature.groups` and
its step clauses from `Feature.stepTerms`. The circuit simulation synthesises each basic feature
from the same terms (`Synthesis.any_all_literal`, with `Feature.length_stepTerms_le` bounding the
cost), replacing five per-kind constructions. Tableau and correctness shrank from 664 to about 440
lines and the simulation from about 500 to about 400. An independent cslib-style review of the
refactor (15 findings) was addressed, including implicit arguments, section-scoped instances,
`Std.Sat.Literal` for terms, and accurate docstrings on what is noncomputable and why.

An independent cslib-style review (29 findings) was addressed: generic run lemmas moved to
`Turing.MultiTapeTM` (`MultiTape/Run.lean`), CNF names aligned with `Std.Sat` (`relabel`, `imp`),
`Std.Sat.Literal` reused, one-hot reasoning factored (`Agrees.of_oneHot`), docstrings corrected
so nothing claims the polynomial-time parts, imports shaken, closure rules `protected` with a
`fun_prop` rule for `Polynomial.eval`, an axiom audit for every headline theorem. Deferred:
a local polynomial-time witness (crei's `const`/`id` will supply it), `FinEnum` instead of
`Finset.toList` (computable tableau), deriving `add`/`mul`/`pow` bounds from `IsBigO`.

## Realignment with crei's `tidy-universal` branch (2026-10-13)

crei's fork branch `crei/tidy-universal` (39 commits, ~9.3k lines; not yet a PR) implements
most of L1, L3 and the UTM part of L4 in exactly the style this plan wanted:

* explicit encodings `α ↪ List Bool` with capability classes (`PairEncoding`, `ListEncoding`,
  `OptionEncoding`) and canonical instances `encPair` (framed first component), `encList`,
  `encOption`, `encNat` (`Nat.bits`), `encBool`, `encBits`;
* `ComputableTidilyInPolyTime f encIn encOut`, closed under composition, pairing, case
  distinctions and folds, **registered with `fun_prop`**;
* combinators (composition, iterate-while, folds, streaming folds, transducers) and arithmetic;
* a universal multi-tape machine in polynomial time, as an interpreter program
  (`Universal/{Basic,Machine,Correct,Complexity,Bound}.lean`).

It merges into current cslib main with two trivial conflicts and the merge builds
(checked in a scratch clone). Consequences for v2:

1. v2's own `Encoding` typeclass is dropped in favour of crei's explicit encodings; problems are
   `Set α` with an explicit `enc : α ↪ List Bool`, as upstream `DecidableInTimeAndSpace` does.
2. `PolyTime` is crei's `ComputableTidilyInPolyTime`; v2 does not build its own calculus.
3. The UTM milestone is crei's; v2's hierarchy work will build on `Universal/`.
4. Until crei's work lands, v2 keeps verbatim *subset* copies of crei's definitions at their
   paths (definitions only, so the switch is deleting files). **Decided by the user
   (2026-10-13): Turing machines come from upstream main** — no merge with crei's branch;
   machine-level results are built against upstream `Turing.MultiTapeTM`, `TransformsTapes` and
   its combinators.
5. crei's draft #767 defines `DTIME`/`DSPACE`/`P`/`L`/`PSPACE`/`EXP` and proves
   `DSPACE s ⊆ ⋃ c, DTIME (n · 2^(c·s))`; v2 must not duplicate it.

## Survey findings that constrain the design

**cslib main (SHA `5281222c`, toolchain `v4.35.0-rc4`, Mathlib `44086b6e`)**
- Has: multi-tape TM/NTM with time and space (`MultiTape/{Configuration,Nondeterministic,Deterministic,Space,ConfigBound}.lean`), `ComputableInTimeAndSpace f encIn encOut t s` (general `t s : α → ℕ`), `TransformsTapes` Hoare triples (`Plumbing/`), `Combinators/{Id,AlmostConstant}`, generic circuits with Shannon/Lupanov (`Cslib/Computability/Circuit/`), `Language.slice`, `PFunctor.FreeM`, `Cslib.FreeM`, `Nat/Asymptotics`.
- Lacks: any complexity class, reductions, oracles, padding, encodings (only `α ↪ List Symbol` parameters), NTM acceptance, circuit families/SIZE/P-poly, UTM.
- In flight by crei (reuse, do not duplicate): #1111 `Combinators/Comp.lean` (composition with intermediate-length bound), #1112 `IterateWhile`, #1126 `Tidy`. By the user: #1067 `PolynomiallyBounded` (reviewers want `∃ d, f ≤ᶠ[atTop] (·^d)` spelling and a Big-O link), #1129 probabilistic programs with typed oracles.
- Roadmap: issue **#611** (crei). Its later comments abandon the function-free RTM in favour of "a combinator library where it is possible to directly derive the complexity of lean functions", a UTM over `List (index × cell)` tape encodings, and logspace composition via the UTM. v2's plan is aligned with it and should be posted there.
- Issue **#590**: `TapeEncodable` typeclass proposal (encode/decode/round-trip). v2's `Encoding` class should satisfy it.
- Rules: `module` + `public import` + `@[expose] public section`; Apache header with cslib wording; PR title `type(scope): desc`; CI = build/test (`--wfail --iofail`)/`mk_all --check`/`checkInitImports`/lint/lint-style; cite `references.bib`; discuss cross-cutting abstractions on Zulip/issue first; small stacked PRs (~50–100 lines each worked for the circuit stack).

**crypto-frontier (worktree `~/.codex/worktrees/3f7e/cslib`)**
- Three layers: spec (`OracleComp := FreeM (ProbEffect …)`, plain `do`), contract
  (`IsPolyTime`, `IsPPTOn`: ∃ one machine and `c d` with clocked run = program), machine
  (`MultiTapeMachine k Symbol State Oracle Choose`, `Machine.lean`).
- Ergonomics come from Aesop rule sets `polytime`/`ppt` + `@[program_certificate]`
  (`Tactic/PolyTime.lean`, 750 lines; ~230 call sites) and `fun_prop` only for the
  arithmetic side goals `PolynomiallyBounded (fun n => …)` (~40 sites). v2 upgrades this:
  register the *computability* predicates themselves with `fun_prop`.
- Loop rules are Hoare-style (`iterate_spec` with invariant + `PolynomiallyBounded size`).
  The "seeded evaluator" and "interpreter-as-program" tricks let most closure rules be proven
  at program level; only ~5 machine compilers exist. No UTM; adversaries are Lean functions
  with an existential certificate.
- Cost centre: `Oracle/`+`Plumbing/` ≈ 11.7k lines, 100–400 lines per combinator.
  Encodings are named explicitly in every statement (ugly); `c*(n+1)^d` clocks only; no
  bridge to upstream's general `ComputableInTimeAndSpace`.

**v1 lessons (from its own ROADMAP and docs)**
- Prove through characterisations before building machines; build the FP/logspace
  composition layer *first*; one circuit model; no 24 codecs; audit for vacuous hypotheses
  (three slipped in); `[simp]` on step functions explodes goals; UTM design in
  `docs/UTM-design.md` (6-tape, +1 shift, `C(α)·(T+|x|+1)` overhead) and hierarchy in
  `Classes/Hierarchy.lean` are the reference constructions for milestone 1.

## Architecture

Every module lives at the path it would occupy in cslib, in the namespace it would have
there (`Turing.*` for multi-tape machines, `Cslib.*` elsewhere), under lean_lib root
`Complexity` (so `Complexity/Computability/Complexity/P.lean` ↔ `Cslib/Computability/Complexity/P.lean`).
A script rewrites import prefixes when a module is submitted (see "Upstream mechanics").

```
L0  cslib main (pinned)        MultiTapeTM/NTM, ComputableInTimeAndSpace, TransformsTapes,
                               Circuits, PFunctor.FreeM, Language, Nat/Asymptotics
L1  Foundations                PolynomiallyBounded (+fun_prop: sub/max/log/ite), Encoding class,
    (Cslib/Foundations/…)      Word utilities, length lemmas
L2  Machine                    Machine k Symbol State Oracle Choose (extends upstream Cfg/Action);
    (…/Turing/MultiTape/…)     ≃ MultiTapeTM / MultiTapeNTM; run : … → FreeM; effectful seq/comp/
                               clock/extendTapes/replay written once for the general machine
L3  Function calculus          InTimeSpace T S f, PolyTime f, Logspace f, PolyTimeRel (effects);
    (Cslib/Computability/      all @[fun_prop]; primitives from L0+L2 combinators; Aesop
     Complexity/Calculus/)     `polytime` for the non-fun_prop shapes (loops with invariants)
L4  Programs                   Prog Eff α := PFunctor.FreeM (sig Eff) α; effects guess/coin/query;
    (Cslib/Languages/Programs/ eval into Set/PMF/StateT; Realizes m p; closure rules; UTM =
     + …/Complexity/Universal/) interpreter-as-program over encoded machines
L5  Classes & theorems         DTIME/DSPACE/NTIME/P/NP/coNP/PSPACE/L/NL/BPP, reductions,
    (…/Complexity/Classes/)    completeness, hierarchy, Cook–Levin, Savitch, …
L6  Circuits                   families, SIZE, P/poly, FP/poly (redo of #1099–#1101 with L1
    (…/Circuit/Family/…)       encodings), P ⊆ P/poly via L4 unrolling, uniformity
```

### L1 — Foundations
- `PolynomiallyBounded`: vendor #1067's file at the same path with `-- upstream: #1067`
  marker; add `@[fun_prop]` lemmas for `tsub`, `max`, `min`, `Nat.log`, `ite`, `List.length`
  of encodings. Track reviewer-requested spelling; if #1067 changes, change here.
- `class Encoding (α) where encode : α → Word; decode : Word → Option α; decode_encode;`
  plus `encode_injective`, and **length lemmas** as `@[fun_prop]`/`@[simp]` facts
  (`(encode (a, b)).length = 2*|a| + |b| + 1` for the tagged pair, etc.). `Word := List Bool`.
  Instances: `Bool`, `ℕ` (binary), `Fin n`, `α × β`, `List α`, `Option α`, `α ⊕ β`, `Word`,
  `Unit`, finite types via `Fintype.equivFin`. Unary ℕ as a separate newtype `Unary`.
  This is what crei asked for in the withdrawn FP/poly review and what #590 proposes;
  coordinate on #590 before the PR.
- Why typeclass, not explicit embeddings: `fun_prop` needs `PolyTime (f : α → β)` to have
  the function as the distinguished argument with everything else inferable.

### L2 — Machine
- `structure Machine (k) (Symbol State Oracle : Type*) (Choose : Type → Type)` with
  `q₀ : State`, `tr : State → Option Symbol → (Fin k → Option Symbol) → (Oracle → Option Symbol)
  → Choose (Action k Symbol State Oracle)`.
  `Action` = upstream `Turing.Action k Symbol State` + `channel : Oracle → ChannelAction Symbol`
  (write one query symbol / submit query / move answer head). `Cfg` = upstream `Turing.Cfg`
  + `channels : Oracle → Channel Symbol`. Exact definitions follow crypto-frontier
  `MultiTape/Machine.lean`, with upstream types as the `core`.
- Semantics: `step : Cfg → Choose Cfg` for `[Monad Choose]`; `run (fuel) : Cfg → Prog (Eff Oracle Choose) Cfg`
  as a `PFunctor.FreeM` program, so a machine's clocked run *is* an L4 program (the key
  crypto-frontier move, kept).
- Equivalences: `ofTM : MultiTapeTM k Symbol State → Machine k Symbol State Empty Id` and
  back, `step_ofTM` (rfl-ish), `runFrom_ofTM`, `spaceUsed_ofTM`; same for `Set`/NTM. Transfer
  lemmas for `ComputableInTimeAndSpace` and `TransformsTapes`.
- General combinators, written once: `extendTapes`, `seq`, `comp` (reuse crei's #1111 shape
  with channels threaded), `withClock`, `replayCoins` (seeded evaluator), `relabel`.
  Templates: crypto-frontier `Oracle/{Sequential,Composition,Clock,Replay,ExtendTapes}.lean`.
  Budget ≈ 2–3k lines; this is the one unavoidable low-level investment.

### L3 — Function calculus (the `fun_prop` layer)
- `def InTimeSpace [Encoding α] [Encoding β] (T S : ℕ → ℕ) (f : α → β) : Prop :=
  ∃ k State, Finite State ∧ ∃ tm : MultiTapeTM k Bool State, ComputesFunInTimeAndSpace tm … f (T ∘ len) (S ∘ len)`
  (definitionally a wrapper over upstream's `ComputableInTimeAndSpaceOfLength`).
  `PolyTime f := ∃ c d, InTimeSpace (c*(·+1)^d) _ f`; `Logspace f`; `PolyTimeRel` for
  effectful functions `α → Prog Eff β` (= crypto's `IsPPTOn`, generalised over `Eff`).
- `@[fun_prop]` registration: lambda theorems (`id`, `const`, `comp`, `pi`/pairing), then
  function theorems for every primitive: `Prod.mk/fst/snd`, `List.cons/head/tail/append/
  length/reverse/map/foldl` (with growth side-conditions, discharged recursively by
  `fun_prop` when they are `PolynomiallyBounded` goals, or by `(disch := …)`), `Nat` arith on
  binary, `ite`/`decide`, `Encoding.encode/decode`. Each primitive is proven *once* via an
  L2/L0 combinator or a transducer (crypto `Combinators/Transducer.lean` gives finite-state
  word functions for free).
- Loops: `iterate_spec`/`foldl_spec` Hoare rules as in crypto `Iteration.lean`/`Fold.lean`;
  `polytime` Aesop set (port of `Tactic/PolyTime.lean`) handles shapes `fun_prop` cannot
  (invariants, local certificates, `@[program_certificate]`).
- Test suite shows one-line `by fun_prop` for typical reductions (3SAT→CLIQUE-style
  list/pair manipulations).

### L4 — Programs and the UTM
- `Prog Eff α := PFunctor.FreeM (Eff.sig) α` with `Eff` a signature type carrying `guess :
  Bool`, `coin : Bool`, `query (o : Oracle) (w : Word) : Word`. Interpreters `evalDet`,
  `evalSet` (∃-acceptance), `evalPMF`, `runState oracle`. Laws via `FreeM.liftM_comp`.
  Follows #1129's `Languages/Probabilistic/Basic.lean` but generalised beyond probability.
- `Realizes (m : Machine …) (p : α → Prog Eff β) (clock)`: clocked `m.run` equals `p` under
  interpretation; `PolyTimeRel p := ∃ m c d, Realizes …`.
- **UTM (milestone 1 core).** Encode a machine as data: `Code := (k, states : ℕ, table :
  List (key × Action))` via L1 `Encoding`; configurations as `(state, inputPos, List (Fin k ×
  ℤ × Symbol) sparse tape, output)` (crei's #611 suggestion, also v1's `UTM/Interp.lean`).
  `stepCode : Code → EncCfg → EncCfg` is an ordinary Lean function proven `PolyTime` *by
  `fun_prop`/`polytime`*, then `runCode n` by `iterate_spec`. Theorem
  `utm_universal : ∀ tm x t, decode (runCode (encode tm) (initCfg x) t) = tm.runFrom … t`
  and `utm_polyTime : PolyTime (fun (c, x, t) => runCode c x t)` with the clock as unary.
  This replaces v1's 24k-line hand-built 6-tape UTM with an interpreter-as-program.
- From the UTM: `exists_machine_simulating_in_time (T ↦ poly(|code|) · T^2)`-type statement,
  and the NTM path-tape interpreter for `NP` verifier equivalence (phase 2).

### L5 — Classes and theorems
- `DTIME T`, `DSPACE S`, `NTIME T` (via `Machine … Set` or via certificate tapes, proven
  equal), `P`, `NP`, `coNP`, `PSPACE`, `L`, `NL`, `EXP`, `BPP`, over `Language := Set Word`
  with `Encoding`-indexed membership for typed problems. Time-constructibility
  (`TimeConstructible T := PolyTime-style computable unary clock`).
- Reductions: `ManyOneReduces L₁ L₂ := ∃ f, PolyTime f ∧ ∀ x, x ∈ L₁ ↔ f x ∈ L₂`; `fun_prop`
  does the first conjunct. Logspace reductions same with `Logspace`.
- Milestone-1 theorem: `time_hierarchy : TimeConstructible T → DTIME T ⊊ DTIME (T^c)` (weak
  form, matching v1's `DTIME_pow_ssubset`) and `P_ssubset_EXP`. Diagonalisation uses
  `runCode` with a unary clock and negated output.
- Later: Cook–Levin (SAT ∈ NP via verifier; hardness via tableau of `stepCode` — a `fun_prop`
  proof of the reduction, no emitter machine), Savitch (recursion in L4), Sipser–Lautemann,
  PH via oracles.

### L6 — Circuits
- `CircuitFamily`, `SIZE s`, `PPoly`, `FPPoly` over `Cslib.Circuits` with inputs via
  L1 `Encoding` and `Language.slice` (`Cslib/Computability/Languages/Slice.lean`); this is
  the redo of withdrawn #1099–#1101 with "a bit more abstraction" and textbook citations
  (Arora–Barak Ch. 6, Jukna). `P ⊆ P/poly` by unrolling `stepCode` into circuits using
  `Circuit.comp`/`Synthesis`; uniformity via `Logspace` generator.

## Repository conventions

- `lean-toolchain` **identical** to cslib's at the pinned SHA (currently `v4.35.0-rc4`; the
  repo now says `v4.35.0` — fix in phase 0). `[[require]] cslib` from git with `rev = <SHA>`;
  Mathlib comes transitively (no separate pin). Copy cslib's `[leanOptions]` verbatim.
- `lean_lib Complexity` (module system), `lean_lib ComplexityTests` with `allowNonModules = true`,
  `testDriver = "ComplexityTests"`, `lintDriver = "batteries/runLinter"`, `mk_all`.
- File template = cslib's: Apache header ("Released under Apache 2.0 license as described in
  the file LICENSE."), `module`, `public import …` reaching `Cslib.Init`, module docstring with
  `## Main definitions / ## Main results / ## References`, `@[expose] public section`.
- References in `references.bib` with cslib's keys (`AroraBarak09`, `Papadimitriou94`,
  `Sipser2013`, `Jukna2012`); add new keys in cslib's format.
- Every file carries `-- upstream: candidate | submitted #N | merged @SHA | local-only` on the
  line after `module`; `UPSTREAM.md` is the ledger. **Rule:** when an upstream PR merges,
  delete our copy and bump the pin in the same commit. Nothing is `local-only` without a
  written reason (test scaffolding, project scripts).
- No `sorry` on `main`; no custom axioms; no `native_decide`; `maxHeartbeats` overrides need a
  comment. No `[simp]` on machine step functions (v1 lesson).
- Private-draft policy from `cslib/circuit-stack-review/PUBLICATION_POLICY.txt` carries over:
  no citations of the unpublished calculus draft in source or PR text.

### Upstream mechanics
- `scripts/upstream.py <Complexity.Path.Mod>` copies the module into a cslib worktree at
  `Cslib/Path/Mod.lean`, rewrites `import Complexity.` → `import Cslib.`, runs `mk_all`, and
  prints the suggested PR title. Then run cslib's five gates there before opening the PR.
- Prefer stacked PRs of 50–150 lines (what landed for the circuit stack). Open an issue or
  comment on #611 before the first L2/L3 PR, since those are cross-cutting abstractions.
- Help land crei's #1111/#1112/#1126 and the user's #1067 early: L3 depends on them. Until
  merged, keep thin local copies at the same paths marked `-- upstream: #1111` etc.

## Phased roadmap

**Phase 0 — scaffold (small).** Fix toolchain; lakefile with cslib require + options + two
libs; `Complexity.lean` root via `mk_all`; CI mirroring cslib's (`build/test/mk_all/lint/
lint-style`); `AGENTS.md`, `CONTRIBUTING.md`, `UPSTREAM.md`, `references.bib`; axiom-audit
test (`ComplexityTests/Axioms.lean` with `#guard_msgs` + `#print axioms`); `scripts/upstream.py`.

**Phase 1 — L1 foundations.** `PolynomialBound` (+fun_prop lemmas), `Encoding` class and
instances with length lemmas, `Word` utilities. First upstream PRs: Encoding (coordinate
#590), fun_prop lemmas (onto #1067).

**Phase 2 — L2 machine + L3 calculus (deterministic fragment).** Parametric `Machine`;
`ofTM/toTM` equivalence; `InTimeSpace/PolyTime/Logspace`; `@[fun_prop]` lambda theorems and
primitives; `iterate_spec`/`foldl_spec`; port `polytime` Aesop set; tests with one-line
reduction proofs.

**Phase 3 — Cook–Levin (milestone 1).** `Language`, `P`, `NP` via verifiers, `ManyOneReduces`;
CNF syntax/semantics and `SAT`; `SAT ∈ NP` (verifier = clause evaluation, `fun_prop`); NP-hardness by
the tableau of the verifier's run with per-step action variables (no single-tape conversion:
each tape's window is checked against the shared action variables), correctness over upstream
`Turing.Cfg`, and the reduction's `PolyTime` proof by `fun_prop`.
**Exit criterion:** `SAT.npComplete` axiom-clean; the reduction's complexity proof is a `fun_prop`
call plus loop rules, with no hand-built machine beyond the L3 primitives.

**Phase 3b — L4 programs + UTM (deferred).** `Prog`, interpreters, `Realizes`, closure
rules; `Code`/`EncCfg` encodings; `stepCode` PolyTime by `fun_prop`; `runCode`; `utm_universal`,
`utm_polyTime`; `TimeConstructible`; `time_hierarchy`, `P_ssubset_EXP`.
Weak hierarchy via the interpreter program; the tight tape-indexed hierarchy is a separate,
machine-level phase (see the decisions table).

**Phase 4 — NP and reductions.** NTM ≃ `Machine … Set`; `NTIME`; verifier characterisation via
path-tape interpreter; `ManyOneReduces`; `NP`-completeness scaffolding; Cook–Levin via
`stepCode` tableau. **Phase 5 — circuits (L6)**: families, SIZE, P/poly, FP/poly redo,
P ⊆ P/poly. **Phase 6 — effects**: effectful `seq/comp/clock/replay` on the general machine,
`BPP`, `BPP ⊆ P/poly`, oracle machines and Turing reductions, PH; space: `L`, `NL`,
`PSPACE`, Savitch via L4 recursion, `DSPACE ⊆ DTIME(2^O(s))` from upstream `ConfigBound`.

## Verification

- Every phase: `lake build --wfail --iofail`, `lake test --wfail --iofail`, `lake exe mk_all --check`,
  `lake lint`, `lake exe lint-style` (same commands as cslib's CI), `grep -rn sorry Complexity` empty,
  axiom test file passes (only `propext`, `Classical.choice`, `Quot.sound` on headline theorems).
- Ergonomics check (phase 2/3): `ComplexityTests/Reductions.lean` contains ≥10 realistic
  reduction functions each proven `PolyTime` by `by fun_prop` or `by polytime` in one line;
  `ComplexityTests/Programs.lean` writes a small oracle/coin program in `do` notation and
  obtains its certificate by closure rules only.
- Upstream rehearsal (every phase): run `scripts/upstream.py` on at least one module into a
  fresh cslib worktree at the pinned SHA and pass cslib's gates there.
- Milestone 1 acceptance: `SAT.npComplete` compiles axiom-clean; the reduction's `PolyTime` proof
  is `fun_prop`/`polytime` plus loop rules, with no bespoke machine.
- Blocker log: the `comp` rule of the calculus needs cslib PR #1111 (crei) merged; until then
  L1, class definitions, SAT, and the reduction's correctness proof proceed; only the final
  complexity certification waits.

## Risks and mitigations

- **`fun_prop` fit.** Mathlib's `fun_prop` handles properties with extra arguments
  (`ContDiff 𝕜 n f`) and recursive side goals; hypotheses that are not fun_prop goals need
  `(disch := …)`. Mitigation: prototype `PolyTime` registration with `comp`/`Prod.mk`/`foldl`
  in phase 2 week 1 before building out primitives; fall back to Aesop `polytime` for loop shapes.
- **Upstream pace.** crei's composition PRs and #1067 are prerequisites; the user is a
  maintainer and can prioritise reviewing them. Local thin copies keep v2 unblocked.
- **Generalising `MultiTapeNTM` upstream** is a cross-cutting change; discuss on #611 before
  the PR, with the equivalence theorems as evidence. Worst case the general machine stays
  downstream while L1/L3/L4/L5 (which only need the deterministic fragment) upstream freely.
- **Universe/`Type` restrictions** on `Choose : Type → Type` and `FreeM`; keep `Oracle`,
  `State`, `Symbol` in `Type` initially, generalise only if a consumer needs it.
