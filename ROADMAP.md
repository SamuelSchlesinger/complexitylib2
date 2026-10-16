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

## Proof engineering checkpoint (2026-10-15)

The deterministic function calculus already provides actual TM certificates, composition,
conditionals, arithmetic, and bounded list traversals. Christian Reitwiessner's vendored
`Universal/` development certifies an interpreter written as ordinary Lean functions.
Its universal function takes a binary step count: its bound is polynomial in the **value** of
that count, not its binary length. The `PFunctor.FreeM` program interface and stateful simulation
rules and general effectful machine are now present. Closed `IsPPTOn` supplies the semantic
realization contract, a deterministic bridge, fair-bit sampling, monadic bind, captured inputs
and conditionals. The `ppt` tactic combines these with deterministic automation and
constant-growth probabilistic loops. General bounded loops use supported-state invariants;
the word-oracle PPT contract, deterministic bridge and derived query budgets are present,
and closed stateful substitution is now certified. General open-program composition remains
to be integrated.
The deterministic `polytime` tactic and invariant-oriented loop specifications have now been
adapted to this backend.
The architecture sections below describe that intended interface, not completed features.

### Existing crypto implementation to reuse

The local cslib `crypto` branch at `5ff69ca` already provides a substantial version of the
intended experience. Its public rules and `CslibTests/ComputationalCryptoPrograms.lean`
examples cover:

* one-call `polytime` proofs for nested captured callbacks, local algorithm calls, conditionals,
  encoded collections, and folds with inferred constant growth;
* `iterate_spec`, `iterate_with_spec`, and `list_foldl_spec` rules returning both efficiency and
  a final invariant, with the caller supplying initialization, preservation, and a size bound;
* one-call `ppt` proofs for `do` programs with several random draws, runtime-dependent sampling
  lengths, typed results, and calls to certified probabilistic routines;
* negative checks for missing certificates, a variable exponential unary output, and a fold
  that doubles its accumulator at each step.

These examples and the three tactic files are identical in the available `crypto-frontier`
worktree; a fresh Lean MCP check of that example file completed without diagnostics. This is a
targeted check, not a fresh full build of the crypto branch. Real clients include GGM's
`isPolyTime_child` (unfold plus `polytime`) and `isPPTOn_expansionOracle` (one local evaluator
certificate, unfolding, then `ppt`). Adaptive oracle simulation still supplies local invariants
and reply/storage bounds; the tactic does not automate general oracle sequencing.

The useful design is already present: `@[program_certificate]` indexes named routines before
unfolding, local certificates remain reusable through argument preparation, and collection and
bind rules settle encodings before searching callbacks. `fun_prop` proves polynomial bounds;
curated Aesop rules select computation certificates. The predicates quantify a single finite
machine and polynomial before inputs, so these are uniform machine guarantees.

The integration work is to adapt those public rules to v2's tidy deterministic calculus and
encoded input/output API, and to bring the effectful realization layer onto the agreed machine
model. The original crypto branch uses `FreeM`; the existing `codex/crypto-pfunctor-experiment-20261012`
at `1d7efae` changes only three probabilistic-language files in the relevant interface while leaving
the tactic and client files unchanged. The newer PR #1129 at `4e626b5` supersedes that experiment:
`OracleComp spec` has one typed query interface, and `interpret` handles all target monads.
`ProbComp` samples finite uniform ranges, rather than exposing an arbitrary-PMF primitive.
V2 now copies this current PR and adapts the invariant simulation rules to it. The remaining
crypto port must express executable sampling through this interface and keep arbitrary
distributions at the semantic level. Use the existing examples as acceptance tests and retain
their negative cases.

### Accounting

Baseline: commit `80f9b48`, before the list-automation refactor. Reproduce it with
`python3 scripts/proof_lengths.py --ref 80f9b48 --json /tmp/proof-lengths.json`.
The script counts nonblank, non-comment source lines in handwritten theorem/lemma bodies,
excluding statements and the initial `by`. It includes term and equation proofs, but excludes
proofs embedded in definitions/instances and generated declarations. It is a source-layout
measure, not elaboration time, proof-term size, or a measure of mathematical difficulty.
Folder totals count each source proof once; shared and imported dependencies are not charged
again to their clients.

Across 396 modules: **4,679 proof bodies, 33,077 body lines, median 3, 90th percentile 17**.
There are 1,545 one-line bodies. The 107 bodies of at least 40 lines contain 7,044 lines
(about 21% of the total). Vendored modules account for 640 bodies / 5,629 lines; submitted
upstream copies for 46 / 263. These are included below, with authorship retained in each file.

| Development | Proof bodies | Body lines | Median | 90th percentile | Largest |
|---|---:|---:|---:|---:|---:|
| Boolean circuits | 613 | 4,889 | 4 | 20 | 101 |
| Frontier circuit bounds | 519 | 4,873 | 4 | 22 | 127 |
| Machine plumbing and encodings | 389 | 3,129 | 3 | 16 | 364 |
| Boolean analysis | 354 | 2,449 | 3 | 18 | 60 |
| Propositional logic | 245 | 2,089 | 3 | 22 | 116 |
| Universal interpreter | 219 | 1,995 | 4 | 23 | 135 |
| Machine complexity calculus | 241 | 1,800 | 3 | 19 | 152 |
| Expanders | 256 | 1,720 | 3 | 18 | 49 |
| PCP | 247 | 1,454 | 2 | 15 | 87 |
| Shared circuit infrastructure | 294 | 1,247 | 1 | 11 | 66 |
| Shared data structures | 253 | 1,063 | 2 | 9 | 43 |
| Other combinatorics | 65 | 812 | 6 | 28 | 96 |
| Monotone circuits | 90 | 699 | 5 | 18 | 63 |
| Decision trees | 116 | 653 | 3 | 15 | 36 |
| Probability constructions | 62 | 565 | 6.5 | 19 | 51 |
| Communication complexity | 63 | 517 | 3 | 25 | 39 |
| Linear algebra | 38 | 453 | 3 | 39 | 79 |
| Complexity classes and reductions | 123 | 433 | 1 | 8 | 78 |
| Cryptography | 70 | 380 | 4 | 11 | 34 |
| Probability foundations | 36 | 332 | 6 | 28 | 34 |
| Cook–Levin | 38 | 193 | 2.5 | 12 | 26 |
| First/second-order logic | 43 | 182 | 3 | 10 | 22 |
| Other modules | 305 | 1,150 | 2 | 8 | 67 |

The longest individual bodies include Reitwiessner's `multiPassFold` (364),
`streamFold` (226), and time/space `foldl` (154); the Gaussian
`exists_multi_vertex_sample` (127); parity's
`CNF.card_isolatedInputs_mul_min_le` (116); `exists_runPath_tidy` (109);
the frontier ledger bound (103); the quadratic-form correlation asymptotic bound (102);
and PCP's `expect_numHits_sq_le` (87). Large reusable backend proofs can be good investments:
shortening clients by reusing them matters more than minimizing every local line count.

### Validated API improvement

Four thin rules in `PolyTime/List.lean` expose composition in the form clients write it:
`cons'`, `listAppend'`, `mapWithInput`, and `flatMapWithInput`. Constructor rules infer
encodings from the result; traversal rules infer the list's encoding before checking the body.
The existing fixed-list rules are also registered with `fun_prop`.
All four new proofs are one-line applications of existing machinery.

The actual initial-clause proof shrinks from 12 body lines to 1, the situation-clause proof
from 10 to 1, and the accepting-clause proof from 2 to 1. Tests check a nested traversal
capturing the original input in one `fun_prop` call and the existing feature-group
enumeration in three proof lines. The change adds four proof lines and removes 21 from clients;
it also adds theorem statements and documentation, so this is not a claim of shrinking total
repository source by 17 lines. The next batch below addresses filtering with negated equality
and the lookup compositions used by SAT.

The dynamic traversal rules require a **joint** certificate for `(input, element) ↦ body`.
Separate certificates for each fixed element would allow different machines and polynomial
degrees and would not establish a uniform algorithm over a variable list.

### Deterministic tactic integration and existing clients (2026-10-16)

The crypto interface now has a deterministic v2 adaptation: `polytime`,
`@[program_certificate]`, local algorithm calls with nested tuple arguments, constructor rules,
and constant-growth fold/iteration rules. Compositional goals use `fun_prop` and a bounded search;
constructor decomposition avoids expensive unsuccessful searches for unknown subroutines.
The certificate search checks argument preparation before choosing between two input encodings.
Tests retain failures for missing algorithm certificates, missing growth bounds, and doubling a
fold accumulator. No heartbeat limits were increased.

`foldl_spec`, `iterate_spec`, and `iterateWith_spec` combine a semantic invariant and encoded-size
bound to return both a TM certificate and the final postcondition. The captured iteration rule
requires a joint step certificate in the parameter and state. Tests prove reversal by a prefix
invariant and unary squaring by repeated addition with a captured input. These are API regression
examples; the demanding clients remain the complete Cook–Levin reduction and clocked universal
simulation.

Measured against `916363d`, existing client proof bodies change as follows:

| Existing proof | Before | After |
|---|---:|---:|
| SAT certificate assignment | 6 | 1 |
| SAT literal evaluation | 7 | 1 |
| SAT clause evaluation | 3 | 1 |
| SAT verifier | 1 | 1 |
| CNF at-most-one construction | 9 | 1 |
| Total | 26 | 5 |

Reusable list rules infer the traversed collection's encoding before checking captured
predicates; first-occurrence lookup and raw-bit access get compositional forms. Together with
negated equality these discharge the previous manual projection and filtering arguments.
The actual Cook–Levin one-hot family now has a one-line proof, using a three-line feature-group
certificate and the existing exactly-one CNF constructor. Input/read clauses, step clauses and
full assembly remain open; this is not yet the complete polynomial-time reduction.

The infrastructure has a real cost: 24 new theorem bodies add 89 body lines, while these clients
remove 21, for a library total of 4,707 bodies / 33,128 lines. The scanner excludes tactic
implementation definitions, theorem statements, documentation and tests. Thus this batch grows
the library overall; its measured benefit is client readability and reusable coverage, not a net
source reduction or a claim of faster elaboration. Strict project validation and the negative
tests check robustness, but compilation performance needs a separate benchmark.

### Cryptographic constructions as integration clients (2026-10-16)

The user's requested scope includes both the general OWF construction and the OWP route, plus
GGM security. The source is the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
Its `OneWay.exists_pseudorandomGenerator` assumes only uniform one-wayness; its pseudoentropy
construction follows Holenstein's simplification of Håstad–Impagliazzo–Levin–Luby. The OWP route
constructs a hard-core predicate through Goldreich–Levin. These remain conditional implications,
not existence proofs of one-way functions or permutations.

| Development | Port status |
|---|---|
| Typed programs and probability/state interpretation | PR #1129 copied at `4e626b5`; source credits Samuel Schlesinger and Devon Tuma and the VCVio design |
| Stateful invariant and simulation rules | adapted to `OracleComp.interpret`; tests retain the final state and exercise oracle substitution and a nontrivial state representation |
| Random-function semantics | joint eager/lazy completion law including independent private coins and adaptive queries; typed caches, association-list realization, compositional oracle-only query budgets and a closed-sampler bridge |
| Shared effectful machine and clocked programs | `Id` / `Set` equivalences to upstream, exact deterministic runs, one program interpreter with pause/resume and substitution laws; Boolean-indexed tables and closed fair-coin runs; shared-tape sequencing with additive actual halting bounds and exact agreement with upstream deterministic sequencing |
| GGM tree evaluation | ported, including truncation and size laws; uniform TM certificate through the existing tidy fold calculus |
| Uniform PPT and oracle PPT, `ppt` automation | closed `IsPPTOn`, deterministic bridge, fair bits and runtime-length uniform words, monadic bind, deterministic preprocessing/postprocessing, captured inputs and conditionals registered with `fun_prop`; `ppt` combines these with named/local certificates and `polytime`; total saved-seed evaluation certifies bounded adaptive loops, with one invariant for resources and postconditions; `ppt` handles constant growth. Word-oracle `IsOraclePPTOn` has the joint stateful contract, supported-output bound and deterministic `fun_prop` bridge; clock-derived external query budgets are present; closed stateful substitution is certified; general open-program composition remains pending |
| OWP → PRG | complete through Goldreich–Levin, the uniform one-bit PRG theorem and extension to any efficiently computed strictly larger output length |
| General OWF → PRG | output-length normalization is complete; queue `Pseudoentropy/*`, entropy-grid and uniform-length conversion, then `OneWayToPRG` |
| PRG → PRF and OWF → PRF | adaptive GGM security and PRG → PRF are complete through one uniform strict PPT reduction; general OWF → PRF awaits the pseudoentropy-based OWF → PRG theorem |

The raw dependency closure of `OneWayToPRF` and `GoldreichLevin/HardCore`, stopping at modules
already present in v2 at `316944d` or its cslib pin, has 183 absent modules / 33,887 source lines.
This is an inventory of the old branch, not an estimate of necessary new code: its deterministic
realizations overlap the existing calculus, and its program frontend has since changed upstream.
Reconcile the predicates with the current PRG/game APIs rather than importing parallel notions.
Preserve uniform, strict fair-coin PPT and the joint output/private-state oracle contract.

GGM evaluation already drives reusable improvements: raw-bit slicing rules and a transactional
zero-growth fold attempt let its certificate use a local step certificate and a length bound,
followed by `polytime`. Tests include a shrinking generator and surplus output, so the efficiency
theorem does not depend on a PRG security or exact-length hypothesis. The adaptive security
theorem is now proved through the saved-sample and single-challenge reductions described below.

The three GGM efficiency proofs have 2, 1 and 4 body lines. Including the copied frontend,
simulation rules and shared helpers, this batch adds 38 theorem bodies / 103 body lines, taking
the library from 4,707 / 33,128 at `316944d` to 4,745 / 33,231. This is additional functionality,
not a net proof reduction; tactic implementation code, definitions and tests are excluded by the
same accounting convention used above.

The machine batch adds 19 theorem bodies / 125 body lines, taking the total to 4,764 / 33,356.
One interpreter proves pause/resume and handler substitution for any transition-choice mechanism;
the fair-coin layer consists of specializations. This count excludes equivalence proofs inside
definitions, as the scanner always does. Tests cover stuck and halted configurations, distinct
nondeterministic successors, a pending query across clock exhaustion, shared request logging,
the fair-bit output distribution, and coin consumption when both branches agree. Its clock counts
machine instructions, not arbitrary handler computation. A PPT certificate must fix fresh fair
coins, finite machine data, a uniform polynomial clock, and account for substituted handlers.

The first PPT realization batch adds 10 theorem bodies / 74 body lines, reaching 4,774 / 33,430.
`ComputableTidilyInPolyTime.isPPTOn` directly reuses an existing tidy witness and its polynomial
clock. It introduces no parallel deterministic predicate or `Fin`-state normalization. Test clients
certify unary addition and GGM evaluation returned by a probabilistic program with one `fun_prop`
each. A one-instruction Boolean sampler is also certified, while a negative test ensures that
arbitrary finite uniform samplers are not silently accepted. `IsPPTOn` uses strict clock exhaustion;
the clock compiler below now provides an intrinsically halting witness. Its output bound covers every
supported result, and the deterministic embedding preserves all channels and private oracle state
under stateless coin semantics.

The shared sequencing batch adds 12 theorem bodies / 107 body lines, reaching 4,786 / 33,537.
The compiler maps actions through the existing choice functor; the probabilistic specialization
uses the same proof in three body lines. `HaltsWithin` and the additive sequencing rule retain
all communication channels and the final private state, and `toTM_seq` identifies deterministic
sequencing with upstream's compiler. Independent review shortened that bridge by 11 body lines
by comparing the transition-table constructors directly. Tests instantiate both halting premises
for arbitrary stateful probabilistic interpreters, exercise one- versus two-instruction stopping times and
coin-count-dependent replies, and exhibit failure of the proposed equality without actual
halting of the continuation. This is shared-tape composition; the following clock and fresh-input
batches supply the additional machinery needed for `IsPPTOn.bind`.

The clock batch adds 28 theorem bodies / 134 body lines, reaching 4,814 / 33,671. Its shared
block-simulation rule permits changing embeddings, alphabets and choice mechanisms. The clock
consumer implements `t` source instructions in `2*t + 1` instructions and actually halts, preserving
the joint source data and private state. The choice interpretation must commute with mapping and
send constant choices to pure, state-preserving results; the probabilistic specialization admits any
stateless coin law. A negative test shows why state-changing coin draws invalidate that contract.
Tests also cover a halted source, zero budget, negative clock position and a false stopping cell.

Polynomial budget generation reuses the tidy functional calculus: four proof-body lines certify
the unary polynomial, and twelve produce a uniform finite machine which writes it on the last
work tape, restores blank scratch tapes and all heads, and emits nothing. Its bound charges
generation and rewinding. This avoids porting the crypto branch's separate low-level polynomial
generator. Budget preparation and consumption are separately certified; connecting them through
tape extension and sequencing was left to the following batch.

The assembled compiler adds 24 theorem bodies / 159 body lines, reaching 4,838 / 33,830. Tape
extension preserves the full execution program and agrees exactly with upstream's deterministic
compiler. It places preparation and source tapes in disjoint ranges, then uses the shared
sequencing and clock laws. `exists_polynomialClock` chooses one finite-control target and polynomial
before input, coin law, and stateful query interpreter. `IsPPTOn.exists_halting_machine` is a
four-body-line client of this compiler: it retains the encoded output distribution and guarantees
halting on every raw word, including words outside the input encoding.

Tests include a nonhalting source with a quadratic cutoff; a concrete one-cell preparation whose
compiled machine stops in four instructions, with arbitrary padding; and a `fun_prop` fair-sampler
client. A separate reindexing test runs on the middle of three tapes, retaining nonblank outer tapes,
negative heads, channel data and stateful coin effects. This completes the clock obligation;
the next batch closes PPT `bind` through fresh-input composition.

The composition batch adds 53 theorem bodies / 331 body lines, reaching 4,891 / 34,161. Input and
output redirection preserve whole typed programs through one common one-step simulation rule;
their deterministic specializations agree exactly with upstream's compilers. The handoff reuses
the existing marker and rewind machines, charging the intermediate word length plus four
instructions. Separate blank continuation tapes permit arbitrary source scratch data. The
continuation clock is bounded by the first machine's supported output length, with actual halting
proved before padding. `IsPPTOn.bind` uses this compiler; deterministic preprocessing and
postprocessing are each one-body-line clients. These counts include the shared infrastructure.

Tests certify ordinary `do` programs and GGM evaluation after a certified sampler with `fun_prop`.
The machine test distinguishes generated input from the real input, dirty source scratch from
fresh continuation scratch, empty output from a one-bit word, and one- from two-instruction
stopping times. Adapter tests also preserve channel data and stateful coin effects at both ends
of an empty input. Independent review replaced tuple-index arithmetic with existing `Fin` tuple
identities. Later batches below supply captured caller inputs and probabilistic iteration;
oracle PPT remains separate work.

The capture batch adds 22 theorem bodies / 108 body lines, reaching 4,913 / 34,269. A common
program law preserves existing output prefixes, including channels and stateful interactions.
The tidy-run API now exposes the restored configuration directly; this makes the prefix
realization a 28-body-line proof using shared sequencing. Pairing reuses upstream framing;
`keep_input` and `bind_with` are one-body-line clients, and `map_with` uses two. Closed branch
selection is an eight-body-line `fun_prop` client followed by distributional simplification.
Its witness may run both total branches, so this rule is deliberately restricted to closed programs.

Client tests use one `fun_prop` for two samples with a retained unbounded word, GGM evaluation
on a sampled seed and the original query path, and a conditional between probabilistic branches.
The conditional exposed a missing computed-argument equality rule: `decide_eq'` now infers the
common encoding from its two arguments and is also reused by the existing inequality proof.
Concrete tests check a prepared prefix followed by the original input, and an oracle query that
retains both an existing output prefix and the private request log.

The `ppt` tactic is now integrated for these closed programs. Its module has 82 source lines;
the existing `polytime` routine-call matcher is shared, and `program_certificate` also registers
probabilistic certificates with `fun_prop`. Its initial integration added no mathematical theorem
bodies, leaving that total at 4,913 / 34,269; tactic implementation and tests remain outside the
metric. Clients cover
captured `do` programs, a deterministic bounded-growth fold after sampling, nested tuple arguments,
alternate local encodings, GGM evaluation, and irreducible named routines inside a conditional.
Regression tests require fallback from an inapplicable certificate and reject unknown samplers
and exact uniform sampling from `Fin 3`. Review exposed a sampled-output encoding choice that
could prevent a valid continuation proof. Captured composition now exposes both premises to
Aesop's joint search, retaining local and registered certificate alternatives for their shared
encoding. Named lookup now returns every matching certificate as a separate Aesop application,
with independent metavariable assignments and the remaining premises visible to search. Tests
cover unary/binary certificates in both orders and competing certificates on both sides of bind
and map, including irreducible named routines. Conditional fallback also lets `polytime` prove
a fold-based guard, including a negated
guard through a one-line wrapper around the existing Boolean certificate.

Uniform sampling of runtime-length words is now ported from the crypto branch. `BitString.uniformList`
keeps the finite-cube distribution and its split, prefix, support and permutation laws;
`BitString.sampleList` draws only independent fair bits. A single one-state, zero-work-tape scanner
outputs one bit per raw input symbol and halts after one additional transition. That last transition
draws and discards a coin, so the theorem is distributional rather than an equality of coin-query
programs. A unary count certificate lifts to sampling through one line of preprocessing. Tests
cover empty and mixed raw words, the last live versus halted configurations, lengths computed by
arithmetic or a bounded-growth population-count fold, and sampled-seed GGM evaluation with `by ppt`.
Binary-only counts are rejected. Including the guard wrapper, this batch adds 18 theorem bodies /
112 body lines, for 4,931 / 34,381 in 435 source files. The scanner's general configuration proof
is 33 body lines; its high-level sampler certificate is four, and its count-composition rule is
one. Subsequent batches below supply saved-seed evaluation and probabilistic iteration; oracle
PPT and the crypto security reductions are still pending.

Saved-coin semantics and its deterministic controller are now ported. Replay is a `foldlM` of
the shared one-step program, so pause/resume and interpretation use the existing list and monad
morphism laws. Averaging fixed tapes preserves both the final configuration and private oracle
state when the coin program is stateless and fair; query handlers may remain randomized and
stateful. In the closed case replay is a pure deterministic fold, and every supplied tape gives
a supported configuration and output. The controller adds one read-only work tape and uses
`Option State` control, scanning the tape to its first blank in `coins.length + 1` instructions
even when the source halts early or never halts. Tests cover empty and false-bit tapes, an
already-halted source, negative work-head movement, buffered queries and shared private state.
This batch adds 24 theorem bodies / 100 body lines, giving 4,955 / 34,481 in 437 source files;
the general averaging proof is 13 lines and the controller's arbitrary-position run proof is 16.
These counts include the two low-level modules and exclude statements, definitions and tests.
The controller itself starts with preloaded tapes; the next batch connects this to actual input
preparation and computability as follows.

Closed saved-coin replay is now tidily computable in linear time and space from the standard
encoded pair `(coins, input)`, even when the source never halts. A reusable selected-tape writer
preserves nonblank unselected words; `PairEncoding.exists_prepare` composes the existing certified
projections into a finite linear-time pair preparer. Its two output heads finish at zero, and the
replay compiler adds only the virtual-input marker before execution. The final tidy normalization
charges cleanup and restores every head. Clients can rearrange the arguments and preprocess their
coins with a one-line `fun_prop` proof. Tests also use `polytime` and cover the nonhalting source,
false bits, empty coin tapes and empty virtual input. Including all three compiler modules, this
batch adds 11 theorem bodies / 169 body lines, giving 4,966 / 34,650 in 440 source files. Statements,
definitions and tests are excluded from this source-layout metric.

Typed saved-coin evaluators are now ported for every `IsPPTOn` program. Normalizing each seed to
the witness budget makes every output valid and supported, including empty and short seeds.
The output embedding supplies a unique typed preimage; the TM certificate computes its encoding
without requiring a decoder on invalid words. Any sufficiently long uniform seed gives exactly
the original distribution. The padded raw evaluator also supports one saved tape across inputs
of different lengths, preserving their marginal distributions without asserting independence.
Tests instantiate a marked variable-length sampler, unary natural outputs with constrained
support, and a shared Boolean predictor tape. Including the generic PMF encoding lemma, this
batch adds 7 theorem bodies / 68 body lines, giving 4,973 / 34,718 in 441 source files.
Adaptive loops are supplied in the following batch. Repetition helpers, oracle PPT and the crypto
security reductions remain to be ported.

Bounded adaptive iteration now reuses the deterministic fold calculus. One invariant bounds every
supported intermediate state's encoded size and proves the final supported postcondition. A
common polynomial coin budget and independent rows of one uniform tape give the exact adaptive
distribution. The captured-input rule retains a uniform joint certificate for the input and
changing state. Constant-growth and nonincreasing variants are registered with `ppt`.
`BitString.listRows` uses ordinary dropping, padding and taking and reuses `blocksEquiv`; no new
machine table is needed. Its count, width and complete encoded output are charged.

Tests certify a quadratic-length random-list program with `ppt`, a captured capped counter, and
an implicit binary-graph walk whose invariant proves reachability. They cover zero iterations,
zero rows and width, short tapes, and reject an exponential-growth loop with only a polynomial
count. The captured counter also exposed ambiguous intermediate encodings in conditional guards:
pointwise Boolean and unary-comparison rules now let `fun_prop`, `polytime` and `ppt` handle the
compound guard directly. Including the five new modules and these rules, this batch adds
30 theorem bodies / 190 body lines, reaching 5,003 / 34,908 in 446 source files. The general loop
certificate uses 59 body lines, captured iteration 28, and the bounded-growth wrappers 14 and 1.
Statements, definitions, tests and tactic registration code are excluded from this layout metric.

### Computational crypto games (2026-10-16)

The next crypto slice uses the current upstream `Negligible` and `Game.Indistinguishable`
interfaces from PR #1069, including its prerequisite #1068, instead of reviving the old branch's
real-valued game API. Thin bridges identify the pinned finite PRG API's real advantage and
security with these nonnegative games. No second generator or security definition is introduced.

`IsPPT` specializes the same machine contract to `encPair encUnary encBits`. A single finite
machine and polynomial work for every security parameter and auxiliary word. `ppt` exposes this
contract automatically. Named curried certificates are registered through definitionally equal
uncurried theorems, so both `ppt` and `fun_prop` compose them while implementations stay folded.
A lawful Boolean equality rule handles the computed comparisons used by inversion experiments.

`ComputationallyIndistinguishable` quantifies over one uniform program before negligibility;
semantic tests must supply a uniform realization. Arbitrary ensemble laws stay outside the
program syntax. Randomized postprocessing preserves security, with its reduction's efficiency
proved by `ppt`. The one-way-function game accepts any preimage, including one of another length;
OWP adds length preservation and bijectivity. Efficient inverse and constant-function tests rule
out trivial instances. These definitions do not assert that OWFs exist.

This batch adds 59 theorem bodies / 106 body lines across seven new modules and the equality rule:
30 / 48 are copied upstream proofs and 29 / 58 are new adaptations. The total is 5,062 / 35,014 in
453 source files. The unary inversion efficiency proof is two body lines, its parameterized wrapper
one, randomized postprocessing five, and the three finite-PRG bridges five combined. Definitions,
statements, tests and certificate registration are outside this layout metric. Full OWP → PRG,
general OWF → PRG and adaptive GGM security remain unported.

### Hard-core predicates and one-bit expansion (2026-10-16)

`PseudorandomGenerator` wraps the existing finite `PRG.Family.Secure` on `BitString n` and
`BitString (length n)`. One uniform program realizes each admissible test on all valid output
words. The exact length hypothesis identifies finite and list experiments, so padding/truncation
cannot change the security claim. The real and ideal games are fair-bit programs. Computing the
length needs only efficient generation and its length equation: run the generator on a canonical
seed. No security hypothesis or extra sampling primitive is needed for that certificate.

`Prediction` and `HardCore` port the two-fixed-trial reduction. Their signed gap identity gives
an average-prediction-bias bound in the shared nonnegative game API. Each predictor is a uniform
program with a two-line `unfold; ppt` certificate. An efficient length-preserving permutation
with a hard-core predicate therefore yields a one-bit PRG. Goldreich–Levin still supplies the
missing predicate construction; this is not yet the complete OWP → PRG theorem.

Tests include an actual hard-core instance: a constant image perfectly hides the first bit of
a nonempty uniform seed. This checks that hard-core unpredictability does not itself assume
one-wayness. Constant-test admissibility and identity-family security exercise the finite/list
bridge without cryptographic assumptions. Folded reduction programs compose through `ppt`.

The three modules and copied PMF averaging lemmas add 38 theorem bodies / 125 body lines:
33 / 118 are adaptations and 5 / 7 are copied from current upstream PR #1062. The total is
5,100 / 35,139 in 456 source files. Statements, definitions, tests and tactic code are excluded.
The upstream checker now recognizes copied-block markers as well as whole-module markers,
including the independent #1062 and #1129 blocks in the shared PMF file.

### Finite Goldreich–Levin decoder (2026-10-16)

`GoldreichLevin/Decoding` ports the subset-sum list decoder: sample `k` base masks, enumerate
all guesses for their parities, and take a corrected strict majority for each coordinate.
For a predictor with agreement at least `1/2 + ε`, with `ε > 0` and `k > 0`, the failure
probability is at most `n / (4 ε² (2^k - 1))`. Every output has at most `2^k` candidates.
With `2^k - 1 ≥ n / (2 ε²)`, recovery succeeds with probability at least one half.
This direct-coordinate variant follows the crypto branch; its candidate bound is weaker than
Trevisan's two-stage presentation, but it remains polynomial under the eventual parameter choice.
These are finite distributional guarantees. The uniform PPT decoder and the hard-core theorem
remain separate porting work.

The shared probability API now derives uniformity of surjective additive homomorphisms from
translations and the existing hash-family fiber count. The counting lemmas moved to `Uniform`
without changing their names; they still serve the hash-family proof. A general PMF output-mass
formula is the density of its fiber. The existing uniform-experiment averaging proof falls from
six body lines to two. `BitString.strictMajorityOn` and its correct-vote bound replace the
crypto-specific majority operation and also supply the existing anti-checker majority lemma.

The three new modules have 26 theorem bodies / 225 body lines, including two existing fiber
lemmas moved from the shift module. Accounting for all shared helpers, moves and refactors, the
net addition is 28 / 211, compared with 25 / 248 in the three original crypto-branch files.
The library total is 5,128 / 35,350 in 459 source files. Definitions, statements and tests are
excluded from this source-layout metric. Tests cover overlapping subset masks, ties, zero target
length, arbitrary masks against perfect prediction, and the genuinely imperfect two-bit AND
predictor with exactly `3/4` agreement; the quantitative recovery theorem applies to it.

### Seeded Goldreich–Levin inversion and parameters (2026-10-16)

`GoldreichLevin/Reduction` samples one predictor seed per image and reuses it across all decoder
queries. The seed type and its law may depend on the image. Candidate checking accepts any valid
preimage, without injectivity, and retains first-match order and a defined zero fallback.
With the stated mask-count bound, positive average prediction bias `ε` gives inversion success
at least `ε/4`. One independent fair bit chooses whether to complement the predictor, giving a
single inverter with success at least `ε/8` for absolute bias `ε`; it receives no bias advice.

`Parameters` chooses `log₂(2 n p² + 1) + 1` base masks at precision `1/p`, with at most
`4 n p² + 2` guesses. For `p = (n+1)^d` at each fixed degree, enumeration size and random-mask
length are polynomially bounded. If every such inverter has negligible success, prediction bias
is negligible in the existing nonnegative `Game` API. Each degree selects one inverter for all
input lengths. These are finite and asymptotic probability theorems; uniform TM/PPT certificates
for the complete word decoder remain the next step.

The ordinary bit-string enumeration moved out of the crypto namespace into `BitString.enum`.
Two shared affine-average rules reduce `invert_success_ge` from 39 proof-body lines to 22, while
the existing game-complement law supplies the negative-bias case. Including enumeration and both
shared rules, this batch adds 28 theorem bodies / 184 body lines, versus 26 / 207 in the original
two crypto modules plus one two-line PMF helper (27 / 209 altogether). The total is 5,156 / 35,534
in 462 source files; definitions, statements and tests remain excluded. Tests exercise binary
enumeration order, a different valid preimage, the empty-list fallback, and negative prediction
bias with image-dependent finite seeds, including dimension zero.

### Executable Goldreich–Levin decoder (2026-10-16)

`GoldreichLevin/WordDecoder` now implements the complete deterministic decoder using ordinary
maps, filtering, folds and first-match search. The finite/list correspondence preserves order,
duplicates and the zero fallback for every mask tape, including short tapes. Uniform mask bits
give exactly the earlier finite inversion law and its half-success bound for correlated
predictors. The predictor certificate is joint in its captured input and query. Connecting saved
randomness to this callback and proving the complete uniform PPT inverter remain next.

Candidate decoding, candidate-list generation, checking and the full decoder each have an
`unfold …; fun_prop` efficiency proof. Their combined proof bodies are 8 lines versus 17 in the
crypto branch. A closed client with an input-dependent parity predictor is certified by one
`polytime`; no assumed algorithm certificate is needed for that example. Tests also cover short
selectors and rows, out-of-range coordinates, ties, noninjective checking and zero dimension.
Automation rejects an attempted certificate for unrestricted exponential enumeration.

The shared calculus gains captured search and runtime option defaults, raw-bit traversals,
Boolean folds, pointwise operations, strict majority, basis masks and selected row sums. Binary
logarithms reuse encoded lengths; unary logarithms first convert to binary. Enumeration requires
a polynomial bound on **all** `2^k * (2k+1)` encoded bits, and the loop proof bounds intermediate
states too. Algebraic list/finite identities live in `BitString.List.Operations`, while binary
enumeration has a shared `BitString.enumList` representation.

The crypto-specific module has 15 theorem bodies / 82 body lines. Counting all new shared
infrastructure, this batch adds 49 / 233, bringing the library to 5,205 / 35,767 in 466 source
files. The crypto branch's original `WordDecoder` alone had 29 / 166; the lower local module count
does not represent a reduction in total work, because generic operations and certificates have
moved into shared APIs. As before, definitions, statements and tests are excluded from the metric.

### Uniform Goldreich–Levin and OWP → one-bit PRG (2026-10-16)

`WordReduction` connects the typed saved-seed evaluator to the deterministic decoder. The
inverter samples one sign, one predictor seed, and independent masks, then calls `wordDecode`.
Both the prediction game and the complete inverter have two-line `unfold; ppt` certificates.
The exact distribution laws retain image-dependent seed lengths and the same private seed for
all decoder queries. The actual pair encoding requires `c * (3*n + image.length + 2)^d` coins;
the crypto branch's old framing formula is not reused. Every fixed precision degree selects
one uniform inverter for all security parameters, yielding negligible absolute prediction bias
from one-wayness. No extra heartbeat override is needed for these certificates.

`HardCore` splits every seed into equal halves and an optional final bit, transforms the first
half, and retains the rest. The parity of the equal halves is hard-core for any one-way function.
Two fixed uniform reductions handle even and odd lengths, with shared negligibility under
parameter rescaling. For a one-way permutation, appending that parity gives a secure uniform
polynomial-time PRG of length `n+1`. This theorem supplies the predicate as well as the security
reduction; it does not assume or prove that one-way functions exist. Polynomial stretch, the
general OWF → PRG implication, and adaptive GGM security remain separate work.

The shared calculus gains fixed unary division, including division by zero under Lean's
convention. One quotient/remainder invariant proves correctness and an encoded state bound;
unary equality fixes intermediate encodings so its conditional step is proved by `fun_prop`.
Generic polynomial parameter rescaling lives beside the shared nonnegative negligibility API.
Tests exercise zero and unit divisors, captured arithmetic, a closed typed randomized inverter,
arbitrary image lengths, empty games, and preservation and exclusion of the odd spare bit.

The two crypto modules have 19 theorem bodies / 118 body lines, compared with 22 / 124 in the
crypto branch. Including all shared rules, this batch adds 23 / 159 and brings the library to
5,228 / 35,926 in 469 source files. These are source-layout counts excluding definitions,
statements and tests; the modest crypto reduction does not erase the new shared proof work.

### Strict bounded index sampling (2026-10-16)

The next reduction primitive is exact fair-bit sampling in a power-of-two range above a supplied
bound. `sampleBoundedIndex` caps excess indices at a rejection sentinel; `sampleDyadicIndex`
retains the complete range, and `sampleDyadicCoin` compares that index with a supplied numerator.
All use a fixed number of fair bits and have two-line `unfold; ppt` certificates. The dyadic
range is at most `2*(bound+1)`, so producing the unary result is charged without an unbounded
rejection loop. These are the samplers required by uniform random-hop reductions.

Binary decoding and incremental saturation live in `BitString`, with exact uniform-distribution
laws in `Probability/UniformNat`. The shared captured-fold rule replaces manual paired-state
bookkeeping: its bounded decoder certificate takes 10 body lines versus 29 in the crypto branch,
plus a one-line Boolean-to-unary rule and one-line captured-input wrapper. Every intermediate
accumulator remains at most the supplied cap. The existing polynomial-logarithm bound also proves
the sampling range polynomial. Tests cover a power-of-two bound with half the mass at the sentinel,
zero bounds, probability-zero and probability-one coins, captured arithmetic, and rejection of an
automatic unary-output certificate for uncapped binary decoding.

Including shared helpers, this batch adds 28 theorem bodies / 115 body lines, bringing the total
to 5,256 / 36,041 in 473 source files. The three original crypto-branch files contain 28 / 138;
two grid-coordinate division/remainder helpers (2 / 5) are deferred, so the corresponding original
portion is 26 / 133. Definitions, statements and tests remain outside this source-layout metric.
Polynomial PRG stretch and adaptive GGM security still require their hybrid reductions.

### Polynomial PRG stretch (2026-10-16)

`PRGStretch` retains a fixed-width seed prefix and emits one bit per iteration. Its public
functional program is certified without a length promise on the generator: each call reads only
a bounded prefix, so its output has a polynomial bound in the original input. A new shared
`iterateWith_of_bounded_growth` rule charges this input-dependent growth at every iteration.
The existing invariant-based iteration proof now reuses the same captured loop rule.

The reduction samples one bounded hop and rejects the padded outcomes. The exact advantage loss
is `2^(log₂(count)+1)`, including `count = 0`; for positive counts it is at most `2*count`.
The signed averaging theorem comes unchanged from current upstream PR #1070. Both the ordinary
and captured hybrid tests have two-line `unfold; ppt` certificates. A client that captures a
Boolean, computes a quadratic count and runs a randomized length test closes with `ppt`.
That test exposed expensive encoding inference for a raw word's length in nested tuples;
one shared composition rule resolves it at the default heartbeat limit.

`PseudorandomGenerator.amplify` gives any efficiently computed, strictly larger output length;
`truncate` preserves security at an efficient intermediate length. The indexed theorem retains
one uniform reduction receiving the family index as input. Its secure choice need not be
computable, and the theorem does not certify evaluation of that chosen family as a PPT program.
General OWF → PRG and adaptive GGM security remain to be ported.

The stretch module has 25 theorem bodies / 174 body lines versus 25 / 168 in the crypto branch;
this is a broader captured-input interface, not a proof-length reduction. The two PPT certificate
bodies remain two lines each. Including the shared loop, composition and size rules and the
upstream hybrid copy, the net addition is 39 bodies / 237 lines, bringing the library to
5,295 / 36,278 in 475 source files. Counts exclude definitions, statements and tests.

### Random functions and memoized sampling (2026-10-16)

The GGM port now has a semantic foundation for consistent oracle replies. A cache records typed
answers, and the eager/lazy theorem preserves the joint result and completed function table.
It permits adaptive queries and preassigned answers. An association-list implementation preserves
this law even with duplicate initial keys, using the first occurrence. Its cache grows by at most
the number of calls; every new key came from the transcript and every new value from its sampler.
Query bounds compose through `pure`, queries, mapping and bind.

The proofs reuse the single `OracleComp.interpret` interface and generic state simulation.
A shared `IsMonadHom.stateT` rule transfers entire stateful executions through a monad morphism;
it gives the bridge from executable closed samplers to mathematical distributions. Tests cover
adaptive and repeated queries, retained initial entries, duplicate keys, exact sample counts
and query budgets. These are semantic laws for oracle-only programs. Fresh private randomness
in the client and the oracle-PPT machine realization still need to be connected for GGM security.

The random-oracle module has 19 theorem bodies / 155 body lines, versus 19 / 147 in the crypto
branch. Transcript, memoization and product-distribution APIs add compositional rules and retain
dependent response types; two conditioning corollaries are deferred. Including the shared APIs,
the batch adds 50 bodies / 308 body lines net, bringing the library to 5,345 / 36,586 in 481 source
files. Two existing PRG proofs now use the shared support-sensitive map congruence directly,
saving one line each. This batch expands the interface and is not an overall proof-length reduction.
Counts exclude definitions, statements and tests.

### Private coins and word-oracle PPT (2026-10-16)

`ProbOracleComp` is an abbreviation for the disjoint sum of the existing uniform sampling and
external query interfaces. Programs use `sample` and `query` inside ordinary `do` blocks, and
`OracleComp.interpret` remains the sole interpreter. The completion theorem now handles both
adaptive external requests and fresh private coins, preserving the joint result and final table.
Its proof uses the existing state simulation rule: random draws commute with table completion,
and external requests use the established one-query completion law.

`IsOraclePPTOn` fixes one finite-control, finite-channel fair-coin machine and one polynomial
before quantifying over inputs and shared stateful handlers. Requests and replies are words;
arbitrary typed codecs are not hidden in the external handler. The clock charges writing requests,
reading replies and writing output. Deterministic functional programs reuse tidy certificates
with `fun_prop`. Tests certify a functional client that requests a word and returns its first bit,
with exact joint-state behavior, and prove that returning an unrestricted reply cannot have a
uniform strict polynomial clock. Separate tests check independence of repeated private samples.

This is the realization contract and deterministic bridge. Extracting request budgets from the
machine clock, composing open programs and certifying efficient stateful oracle substitution are
the next requirements for the GGM reduction; the closed `ppt` tactic does not yet cover them.
The four source modules add 16 theorem bodies / 70 body lines, bringing the library to
5,361 / 36,656 in 485 source files. Counts include shared semantic and machine helpers, but exclude
definitions, statements and tests; they are not a claim of reduced elaboration time.

### Query budgets from oracle machine clocks (2026-10-16)

The common clocked run makes at most one external call and appends at most one symbol to each
request buffer per instruction. `MultiTapePTM.query_bounds_runFrom` accounts for arbitrary initial
buffers and an existing transcript. Starting from blank channels, the clock bounds both the
external call count and each request length, independently of all reply lengths and shared
oracle state. Private samples do not enter the external transcript.

`IsOraclePPTOn.query_bounds` derives those budgets from the machine realization by adding the
transcript to its quantified private state. There is no separate query-budget assumption in the
efficiency predicate. Tests derive a budget for the concrete functional reply-prefix client and
check its exact one-entry transcript with arbitrarily long replies and two private draws.

The value-level `ProbOracleComp.HasQueryBounds` rules cover private samples, external requests,
mapping and adaptive bind. Shared private-coin invariant, simulation and state-representation
lemmas also simplify the randomized completion proof from 20 to 8 body lines. Including all
these helpers and the machine unfolding rules, the net addition is 17 theorem bodies / 141 body
lines: the library has 5,378 / 36,797 in 489 source files. Definitions, statements and tests are
excluded. Efficient stateful oracle substitution remains an infrastructure requirement for GGM
security; the memoized-handler certificate is described below.

### Efficient memoization and randomized cache bounds (2026-10-16)

`IsPPTOn.memoize` certifies the ordinary list memoizer, including captured inputs, comparisons of
complete keys and writing the entire returned cache. It needs no default inhabitant of the key
or value type. The realizing machine may sample and discard a fallback on a hit; the source
program's joint result/cache law is unchanged. `fun_prop` handles concrete word samplers, while
the registered certificate lets `ppt` also handle an abstract captured sampler and repeated calls
threading a cache through ordinary `do` notation.

`memoize_call_size_le` preserves a reply-size invariant and charges the exact framing overhead
of one added entry. `memoize_cache_size_le` bounds the whole encoded cache from external call,
key and reply bounds. Randomized clients now have list-cache representation and eager-table
bridges as well as cache provenance; private samples are never cached. Tests include independent
private draws, repeated queries, a concrete 18-bit cache bound and duplicate preassigned entries
whose values are outside the sampler's support.

The memoization module has 4 theorem bodies / 42 body lines versus 4 / 64 on crypto `5ff69ca`.
The new option test and shared support lemma cost another 4 body lines. The support lemma also
reduces the existing cache-invariant proof from 14 to 7 lines and its transcript proof from 34
to 11. Including all new randomized-client bridges, shared helpers and refactors, this batch
adds 11 theorem bodies / 60 body lines net: 5,389 / 36,857 in 490 source files. Definitions,
statements and tests remain excluded; these source-length measurements do not measure runtime
or elaboration cost.

The remaining GGM infrastructure is the finite oracle interpreter's efficient stateful
substitution theorem. A PPT memoized handler and its storage bound are now available, but they
alone do not certify running an arbitrary oracle-PPT adversary against that handler.

### Finite oracle interpreter semantics (2026-10-16)

The common machine now runs on finite storage built from Bolton Bailey's upstream `StackTape`
and `BiTape`. The representation relation permits arbitrary native head positions, including
negative positions and blank gaps. Local instructions preserve that relation, and query
submission clears only the selected pending buffer and resets its answer head.

`finiteRunFrom_eq` proves equality of the entire output program with the native interpreter for
arbitrary choice and query programs. This retains all effects and any state maintained by a later
interpreter, including discarded choices and the final handler update. One proof serves the
common choice mechanism. `OracleComp.run_interpret_iterate` supplies the shared three-line law
for running a stateful handler as a loop on the joint program/handler state.

`FiniteConfig.SpaceBound` tracks input, work tapes, output, pending requests and answer storage.
The answer bound includes reply length independently of the clock: an oracle may install a long
reply in one instruction. Tests cover blank erasure, gaps and negative heads, both input
boundaries, retained channel state, long replies, and an effect log that detects extra choices
after halting or dropped choices before query submission.

The batch adds 34 theorem bodies / 170 body lines, giving 5,423 / 37,027 in 494 source files.
Statements, definitions, instances and tests are excluded. The equality theorem has a 24-line
body; the finite storage representation and bound lemmas have 72 body lines in total.
The next requirement is efficient encodings and transition certificates for these finite data,
followed by the stateful substitution theorem. These semantic and storage results alone do not
establish a PPT simulation.

### Encoded finite tape operations (2026-10-16)

`Encodings/Tape.lean` and `Complexity/PolyTime/Tape.lean` give cslib's existing stack and
bidirectional tapes standard framed encodings and tidy polynomial-time certificates. The symbol
encoding is arbitrary: neither a finite alphabet nor a default symbol is required. Tape moves,
blank erasure, loading lists and each fixed native action compose through `fun_prop`. Only the
size lemmas assume a uniform bound on encoded symbol lengths; their bounds charge blank gaps and
the complete list and pair framing.

The collection API now supplies optional heads, construction of `some`, emptiness tests and a
framed-list tail rule that determines its element encoding. The latter removes a real inference
failure in `fun_prop` for `StackTape.mapSome values.tail`; no tactic-specific syntax case was
added. Tests certify functional programs over an infinite word alphabet and an empty alphabet,
and check omitted trailing blanks versus charged interior blanks.

The two tape modules contain 19 theorem bodies / 50 body lines, including the shared product-view
lemma, versus 15 / 53 in crypto's tape module. Shared collection and stack helpers add another
5 bodies / 7 lines, so the full new surface costs 57 lines, four more than the old module while
providing the broader alphabet interface and additional reusable operations. The batch adds
24 bodies / 57 lines net: 5,447 / 37,084 in 496 source files. Statements, definitions, instances
and tests are excluded. Finite indexed tables, encoded configuration transitions and the final
efficient stateful substitution theorem remain next.

The follow-up correctness review found that the generic `listIsEmpty` rule left its element
encoding undetermined during proof search. Framed-list and raw-bit specializations now make both
`fun_prop` and `polytime` handle direct emptiness tests and composed tape guards. This removes
two manual certificate hints from `stackTape_cons`: two reusable one-line rules replace two
client lines, with no net body-line growth. Regression tests cover both encodings and a tape
program that branches on its stored left side.

### Fixed finite tables (2026-10-16)

`Encodings/Finite.lean` provides unary ranks for a fixed finite type, while `Encodings/Pi.lean`
stores every entry of a finite family in the existing framed-list encoding. Values may be
unbounded words or tapes. `Complexity/PolyTime/Pi.lean` certifies `List.ofFn`, ordinary function
construction and application, and fixed-index `Function.update`. The index type and its
enumeration are fixed independently of runtime input; this is not a uniform enumeration theorem
for growing types.

The projection certificate is registered in the application form expected by `fun_prop`, rather
than adding another tactic syntax case. It does not require an inhabited value type. Tests use
one `fun_prop` or `polytime` to rotate and reverse words, update word and tape tables, construct
fixed tuples with captured input, and construct an empty table over an empty value type.
Generic projection and update tests check the interface without default values.

The table encoding and operation modules have 6 theorem bodies / 28 body lines, versus 5 / 21
in crypto's original `Pi.lean`. The extra cost includes the empty-value projection case and the
encoding equation; this is a stronger interface, not a net proof-length reduction. The finite
rank bound adds 1 body / 2 lines. Together with the preceding emptiness fix, the current inventory
is 5,456 / 37,114 in 499 source modules. Statements, definitions, instances and tests are excluded.
Finite-control case analysis, encoded configuration transitions and efficient stateful
substitution remain next.

### Encoded configurations and predictable composition (2026-10-16)

`Encodings/Configuration.lean` stores ordinary finite storage and all oracle channels. Its bound
charges the input, unary head position, work tapes, output, requests, stored replies and framing.
The uniform constant depends only on the fixed machine types; the bound separately includes the
largest installed reply, since a short oracle run can receive a long word.
`Complexity/PolyTime/Configuration.lean` certifies construction, projections, observations, fixed
native actions, initialization and installation of computed replies. Functional structure updates,
captured configurations and channel access use these rules through `fun_prop` or `polytime`.
Tests cover empty state/channel types, zero work tapes and replies longer than the machine clock.

Initialization rules accept a certified input expression. Registering the existing raw/framed-bit
conversions lets the same program use either input encoding without a manual hint. A reusable
`List.replicate` certificate also covers the form to which Aesop normalizes constant `List.ofFn`;
tests exercise both spellings and a runtime unary count. These are semantic closure rules, with
each copied value charged, rather than new syntax cases in either tactic.

The configuration modules contain 23 theorem bodies / 106 body lines, including their shared
product views and encoding equations, versus 19 / 109 in crypto's original configuration module.
The shared replication rule adds another body / 3 lines. Counting that helper, this batch costs
109 body lines; there is no net reduction against the original configuration module. The current
inventory is 5,480 / 37,223 in 501 source modules. Statements, definitions, instances and tests
are excluded, so these counts do not measure total source size or kernel proof-term size.

Selected Lean 4.35 tactic measurements use the raw heartbeat counter (1,000 raw units per reported
Lean heartbeat). They measure elaborator work, not runtime of the certified program or wall time:

| Client | Tactic | Raw heartbeats |
| --- | --- | ---: |
| Symbolic fixed tuple of reversed words | `fun_prop` | 7,952 |
| Same tuple | `polytime` | 128,171 |
| Runtime unary-count replication | `polytime` | 86,829 |
| Configuration initialization from framed bits | `fun_prop` | 42,324 |
| Reply installation, local step and two projections | `fun_prop` | 136,131 |

An independent review rejected a composition-first tactic experiment: removing one required
local certificate made the speculative `fun_prop` exhaust the default budget even with
`maxSteps := 16`, while the existing Aesop tactic failed promptly. The macros remain unchanged.
The negative test is retained; any future speculative search needs an actual execution budget,
not just a recursion/search-step bound. Finite-control dispatch and efficient stateful simulation
remain the next interpreter obligations.

### Finite-control dispatch (2026-10-16)

The deterministic and closed probabilistic `finite_cases` rules now select among a fixed finite
family of certified branches, retaining the original input. Tag and result encodings are arbitrary;
empty tags and empty result types require no default inhabitant. Both proofs share the same list
selection identity. The probabilistic rule preserves the selected branch's output distribution,
including state explicitly returned as part of that output; this does not yet certify substitution
into an open oracle program.

Computed table updates and lookup from a stored table/index pair use `fun_prop`. Tests cover two
encodings of Boolean indices, unbounded entry words, an equivalent let-based program through
`polytime`, empty control, and a concrete selector returning correlated output/state. Separately
computed higher-order lookup still requires `hvalues.pi_apply' hindex`: upstream `fun_prop`
decomposes `values a (index a)` into a different uncurried premise and does not accept this general
application closure theorem as a registered rule. A computed-index update test uses the explicit
API. No tactic matcher or heartbeat override was added to hide that limitation.

The two dispatch proofs and shared selector cost 3 bodies / 43 lines, equal to the corresponding
three proofs in crypto's original finite-control module. Supporting arbitrary deterministic result
types requires an empty-tag case; the PPT proof now reuses the deterministic empty-domain rule
instead of unpacking a machine witness. Three computed-table access rules add 3 bodies / 3 lines.
The complete batch adds 6 / 46, for 5,486 bodies / 37,269 lines in 504 source modules, with the same
source-layout exclusions as above. The efficient stateful interpreter is the next obligation.

### Efficient stateful oracle substitution (2026-10-16)

`IsOraclePPTOn.run_interpret_preprocess` now certifies the ordinary `OracleComp.interpret`
expression against a closed PPT handler. Its output contains both the original result and final
private state. The client provides input preparation, the handler certificate, initial state,
one meaningful invariant and an efficiently computed allowance for replies and added storage.
The machine, clock-derived query budgets and configuration invariant remain internal.

The proof charges captured inputs, copying, requests, replies and the entire retained finite
configuration and private state. Bounds hold on every supported transition. An additive allowance
depending only on the caller and request prevents repeated state doubling from hiding exponential
storage; a negative test makes that obligation explicit. Neither the oracle contract nor this
proof assumes that the source machine has halted when its clock expires.

Checked clients retain the correlation between a sampled reply bit and the final state, receive
replies whose length grows with caller length, and use a different framed-bit caller encoding. That alternate
encoding requires an explicit `listToBits` composition for the handler and preprocessing; it is
supported without a tactic patch, but inference does not insert every representation conversion.
A generic adaptive client runs against a lazy random-function cache with runtime-length replies.
Its proof uses `memoize_call_size_le` for the full entry/list framing bound and preserves the whole
cache in the result. This completes the substitution infrastructure, not adaptive GGM security.

The three interpreter proofs and public rule cost 4 bodies / 165 body lines, compared with
4 / 156 for the matching crypto-branch proofs. The single-step efficiency proof falls from
47 to 42 lines; the exact shared-interpreter bridge and bounded run offset that saving. Two
shared interpretation helpers add 13 lines and shorten the existing randomized-cache bridge
from 13 to 5 lines. Including those helpers and that reuse, this batch adds 6 bodies / 170 lines,
for 5,492 / 37,439 in 506 source modules (median 3, P90 17). These are the same source-layout
counts as above, excluding definitions, statements and tests; this batch does not claim a net
proof-length reduction against the matched crypto implementation.

The generic memoized-oracle client proof uses 649,052 raw tactic heartbeats with Mathlib's
`#count_heartbeats` tactic on this checkout. It includes the substitution rule, handler and
resource certificates, and cache preservation. This is a baseline, not a speedup comparison.
The complete interpreter module passes `lean --profile`; its import loading dominates the
observed wall time, so it does not support a claim about tactic speed. All six project checks
and the four new headline axiom guards pass.

### Parameterized oracle adversaries and PRF experiments (2026-10-16)

`IsOraclePPT` specializes the existing word-oracle certificate to the same encoded unary parameter
and auxiliary word used by `IsPPT`. Named channels and the joint output/state semantics remain
unchanged. One machine and polynomial work for every parameter and auxiliary input. The PRF real
and ideal games invoke the adversary with empty auxiliary input; the class still requires its
uniform guarantee on all auxiliary inputs. The query bound absorbs pair framing into its constant.

The PRF interface uses `Game.Indistinguishable`, with an actual tidy evaluator certificate and
an exact output-width obligation. Eager tables, semantic lazy caches and executable list caches
have the same law for randomized adaptive adversaries. The new cache-representation rule handles
injective keys and mapped values without mixing private samples with external queries. Its
proof reuses the generic memoizer transport and state-simulation rules.

`isPPT_prfIdealGame` certifies the full ideal experiment for any oracle-PPT adversary. The realizing
program uses an ordinary list cache and fair-bit words; the exponentially large eager table is
only a specification. The single local invariant bounds cached reply lengths. The shared
substitution theorem and `memoize_call_size_le` account for every query, reply and retained entry,
including pair/list framing. Malformed queries leave the cache intact.

Tests cover functional parameter-dependent code, an actual parameterized querying machine,
repeated private-random queries with an intervening fresh bit, malformed inputs, duplicate keys,
and the output-width obligation. All source and client files pass MCP checks without a tactic
patch or heartbeat override. The current upstream sync reports the pinned main and all copied
modules CURRENT. GGM prefix hybrids, expansion, reduction and security remain to be ported.

This batch adds 14 proof bodies / 135 body lines: 14 for the parameter interface, 40 for shared
interpretation/cache helpers, 49 for PRF semantic equivalences, and 32 for the cache and full-game
PPT certificates. The three matched PRF semantic proofs cost 49 lines versus 35 in crypto; their
new private-randomness helpers are charged separately in the 40 lines above. The existing closed
memoizer bridge now reuses the shared lemma at unchanged length. Total: 5,506 bodies / 37,574
lines in 509 source modules, with the same scanner exclusions and median 3 / P90 17. This is new
functionality and a compatible interface, without a claimed net proof reduction.

The complete `isPPT_prfIdealGame` proof uses 1,595,142 raw tactic heartbeats in a fresh
single-file Lean check using Mathlib's `#count_heartbeats` tactic. This includes handler/resource
certificates and the cache invariant. All six project checks and six new headline axiom guards
pass. Independent API and correctness reviews approved the published batch without material
findings; the correctness reviewer ran targeted Lean and boundary checks, not all six gates.

### GGM prefix hybrids and a shared cache simplification (2026-10-16)

`GGM.Hybrid` ports the prefix experiments using ordinary list caches, memoized sampling and the
existing functional tree evaluator. At depth zero the exact distribution is the real PRF game,
including clients that never make a valid query; at depth `n` it is the ideal game. Both endpoint
laws hold for arbitrary adaptive randomized programs without an efficiency or security assumption.

The complete hybrid is strict PPT for every oracle-PPT adversary and efficient generator,
uniformly in the unary parameter and depth. The generator need not preserve length: truncating
evaluation bounds replies anyway. Clients supply only the cached-label invariant and local
encoded-storage growth bound; the common substitution theorem accounts for the rest. The handler
certificate is three lines and is registered for computed inputs. Functional and inlined monadic
spellings use existing `fun_prop`/`ppt` rules without tactic changes.

The narrow `ProbComp.eval_memoize` rule costs one body / two lines and removes eight lines from
four existing library proofs, a net six-line reduction in that shared bookkeeping. The six hybrid
proofs cost 66 body lines versus 65 in the source crypto module. This includes all local helpers;
the function-level final-handler equality avoids a repeated extensionality wrapper. The total
batch adds seven bodies / 60 lines, and the library has 5,513 bodies / 37,634 lines in 511 source
modules, median 3 / P90 17 under the same scanner exclusions.

Tests cover computed inputs, direct `do` notation, shrinking expansions, empty seeds and queries,
malformed-query state preservation, duplicate cache entries, depths beyond the query length and
deferred root sampling with private randomness. The concrete full-game PPT inhabitant makes no
external calls; query behavior is tested at the handler level and the full-game theorem applies
to all certified adaptive clients. Expansion, adjacent-hybrid reductions and final GGM security
remain open.

The complete `isPPTOn_hybridGame` proof uses 718,836 raw tactic heartbeats in a fresh single-file
Lean check with Mathlib's `#count_heartbeats` tactic. This counts handler/resource certification and
the cache invariant together. It is a measurement of this client, not a cross-version speedup.
All six project checks and four new headline axiom guards pass. Independent API review approved
the source, helper reuse and client design. The adversarial correctness review approved the
published batch without material findings, checking targeted Lean diagnostics and five axioms.

### GGM expansions and encoding inference (2026-10-16)

`GGM.Expansion` caches a sampled expansion at each queried parent prefix, truncates it to two
labels and evaluates the selected child's suffix. Generated expansions reproduce the preceding
prefix hybrid; uniform expansions reproduce the next one. Both equalities hold for arbitrary
randomized adaptive clients when `depth < n`. The generated case transports the whole cache under
an exact label-width invariant. The uniform case uses the existing eager/lazy cache theorem and
an equivalence regrouping the complete random table. Neither identity assumes a secure generator.

The complete expansion experiment is strict PPT whenever the generator, sampler and captured
parameters are certified. Its handler proof remains three lines with `fun_prop`. Truncation
bounds stored values and replies for short, long or malformed challenges. The supportwise growth
allowance charges every prefix, two labels and list/pair framing; computation and copying use the
shared stateful substitution theorem. Efficiency remains total at zero width and at arbitrary
depth, separately from the adjacent-level identities.

This client exposed an inference gap between `list.getD index fallback` and
`list[index]?.getD fallback`. Optional head now supports every `ListEncoding`, including empty
element types. Computed optional lookup asks for the list certificate before the operation/size
instances, so `fun_prop` determines the encoding before typeclass search. The raw-bit rule fixes
the element encoding without converting the word into a framed list. These rules remove the old
syntax-restoration rewrite from `polytime`; regressions cover both spellings, raw and framed bits,
unary naturals, abstract custom encodings and an empty element type.

The module adds 11 bodies / 184 proof lines versus 11 / 170 in the source crypto module. The shared
invariant-preserving state map adds 15 lines and replaces an existing four-line proof with two;
lookup rules cost three lines and the generalized head rule adds four. Net batch: 14 new bodies /
204 lines, counting every helper and local proof. The whole library has 5,527 bodies / 37,838 lines
in 512 source modules, median 3 / P90 17 under the existing scanner exclusions. This adds semantic
and machine certificates without a claimed net proof reduction.
The complete expansion-game PPT proof measures 761,388 raw tactic heartbeats, including the
captured sampler, handler inference and local storage invariant.

Tests exercise computed/captured samplers, cache hits and duplicates, malformed queries, long and
short challenges, and a private-random query order whose answer comparison detects correlated
siblings. The semantic client is not itself assigned an oracle-PPT certificate. Source/API review
approved the generalized lookup contract after catching and resolving a regression for custom
encodings; the same review strengthened the sibling test to avoid masking correlations.
All six project checks pass, including the five new standard-axiom guards. The independent
adversarial correctness review approved the published batch without material findings; targeted
diagnostics, axiom checks and additional empty-type, zero-width and sibling-correlation probes
passed.
This batch leaves the single-challenge PRG reduction and final security assembly to the next one.

### Saved samples and complete adaptive GGM security (2026-10-16)

The remaining GGM reduction and security assembly are now ported from crypto `5ff69ca`.
`GGM.reduction` is one uniform strict PPT program: it samples a padded dyadic tree level and query
coordinate, inserts the supplied generator challenge and simulates the adaptive adversary. Its
exact signed gap, and hence nonnegative advantage, loses precisely
`dyadicSize n * dyadicSize (count n)`. Padding rejects. The identity includes zero width and zero
query budget; the security proof fixes each adversary and its polynomial budget before varying
the parameter. Existing polynomial stretch then gives `PseudorandomGenerator.exists_pseudorandomFunction`.
This completes PRG → PRF. General OWF → PRG and its OWF → PRF consequence still need pseudoentropy.

The shared support comprises ordinary list repetition, sequence hybrids and saved-sample
substitution. `OracleComp.replicate` is `List.mapM` over a replicated unit list; its PPT certificate
uses the existing flat-seed evaluator and row traversal, with no new machine or loop syntax.
The exact seed law applies to arbitrary discrete output types, including infinite ones. Each
saved value belongs to an external query; private draws neither consume it nor share its coins.
An online supported-transcript bound suffices to transfer the joint output/ordinary-private-state
distribution. The distribution theorem projects away the unused suffix, which can be correlated
with the run. The efficiency theorem retains and charges that entire suffix along with the output
and ordinary state. It accepts arbitrary encodings and short supplied lists, with the fallback
subject to the same reply/growth contract as every supplied value.

The GGM saved-list game uses the common stateful interpreter and the existing cache invariant.
Its strict PPT proof is 16 body lines; the whole reduction's is five. No syntax-specific tactic
patch was needed. An explicit tuple at one deterministic preprocessing boundary resolves encoding
inference; ordinary constructor, projection, lookup and captured-input certificates do the rest.

| Proof scope | Crypto source body lines | V2 body lines |
| --- | ---: | ---: |
| Repetition laws used here, including the flat-seed law | 40 | 32 |
| Complete saved-sample distribution API | 72 | 83 |
| General repetition PPT certificate | 22 | 17 |
| Saved-sample PPT API, including the new encoded-caller generalization | 24 | 29 |
| Sequence hybrids | 31 | 31 |
| GGM reduction | 59 | 59 |
| GGM security and PRG → PRF | 37 | 36 |
| Total matched scope, including helpers | 285 | 287 |

The complete addition is 35 bodies / 287 lines across seven source modules. The matched source
scope has 36 bodies; its unported count-true and empirical-test APIs are excluded from both sides.
The whole library now has 5,562 bodies / 38,125 lines in 519 source modules, median 3 / P90 17.
These remain layout counts, excluding definitions, statements, tests, instances and generated
declarations. They show comparable proof burden under the shared typed machine API, not a net
proof reduction.

The complete single-challenge reduction's PPT proof measures 11,696,757 raw tactic heartbeats,
including the captured level-test certificate and outer sampler/conditional. This is a source
proof elaboration measurement, not execution time or the extracted machine's polynomial bound.

Tests compute all four joint masses of two independent fair bits and a nonzero single-coordinate
gap with exact padding loss. An adaptive client makes one or two external calls around a private
draw and retains arbitrary initial ordinary state. Separate tests cover exhausted-list fallback,
exact suffix preservation, arbitrary challenge lengths and depths, and an actual querying-machine
witness for the full-state efficiency certificate. The sibling-comparison GGM client exercises the
exact reduction identity but is not itself assigned an oracle-PPT certificate. Ten new headline
axiom guards cover the shared laws, efficiency and final security theorems.
Source/API review approves the seven modules and independently confirms the axiom and proof-count
accounting. All six project checks pass. The independent adversarial correctness review approves
the published batch without material findings; its Lean checks include the security module, three
regression modules, zero-width/zero-budget probes and headline axiom checks.

### Complete Cook–Levin and computed clause parameters (2026-10-16)

The existing reduction now has a full tidy polynomial-time certificate. Input/read and step
clauses complete the clause-family API; `unfold tableau; polytime` certifies the entire tableau,
and two lines compose it with the exact parameter computation and binary variable relabelling.
`SAT_npHard`, `SAT_npComplete` and `UNSAT_coNPComplete` are unconditional. The conditional
local-only staging module is removed. No tableau, feature-step or reduction definition changed.
The machine, finite state type, tape count and polynomial bounds are fixed parameters; each
result supplies one machine and polynomial valid for all encoded inputs.

The difficult step family enumerates its five existing constructor templates explicitly, then
uses ordinary list and arithmetic certificates. This retains list order, repeated entries,
halted-state persistence and clipping at the input boundary. Private constructor helpers are
selected explicitly: registering them made `fun_prop` search through irrelevant constructors.
No tactic patch, global transition simplification or heartbeat-limit override was needed.

Shared additions certify filtering and mapping a fixed parameter list without an encoding or
finiteness instance for its elements, signed window membership and total input-head movement.
Computed-argument clause and comparison rules pin the intermediate encodings before search.
The one-line computed window rule also removes one line of explicit composition from the real
step-clause client. Tests cover equivalent filtered-map/conditional-flatMap expressions, computed
tableau bounds, raw-bit and generic-list input encodings, zero work tapes, and out-of-range head
positions. Seven new axiom guards supplement the now-unconditional completeness guards.

Relative to `f47f424`, all source helpers and clients together add 18 bodies / 74 body lines:
Cook–Levin moves from 40 / 176 to 52 / 233, and the shared machine calculus from 365 / 2,220 to
371 / 2,237. The whole library has 5,580 bodies / 38,199 lines in 520 modules, median 3 / P90 17.
These are source-layout counts under the same exclusions as above; the short final assembly
does not conceal the helper cost. Source/API review approves the implementation and independently
checks minimal downstream imports and the completeness theorems' standard axiom dependencies.
The full tableau proof measures 1,087,931 raw tactic heartbeats; the reduction's final certificate
composition measures 101,881. These measure proof elaboration, not machine runtime; the imported
clause and parameter proofs are not re-elaborated in those measurements. All six project checks
pass. The independent adversarial correctness review approves `fa6e514` without material findings:
MCP diagnostics, regressions, axiom guards and independent probes check all five templates,
ordering and duplicates, halted persistence, total clipping and the unconditional assembly.

### OWF output normalization and shared framing (2026-10-16)

The general OWF port now normalizes variable-length images to a width determined by the input
length. The fixed-width theorem derives one polynomial output bound from the original tidy
machine certificate; evaluation and the width function are uniformly polynomial-time. Its
inversion reduction is an ordinary functional call with a padded challenge, certified by `ppt`.
The underlying security theorem accepts arbitrary supplied bounds, including bounds smaller
than the image, and arbitrary-length inverter candidates. Only the fixed-width conclusion
requires the output-size bound. General OWF → PRG and its pseudoentropy argument remain open.

`Computability/BitString/Padding.lean` bridges pure bit strings to the existing machine frame
encoding; it is definitionally the crypto branch's framed-pair expression. Longer words retain
their whole frame, and equal padded words have equal original words even across distinct bounds.
The general `bitsFrame` certificate works directly on any input encoding. It certifies padding
and reduces the existing Cook–Levin parameter proof from five body lines to
`unfold parameters; fun_prop`. A shared supported-bind monotonicity lemma is used at both levels
of the inversion experiment and shortens the existing maximum-outcome lemma.

The matched padding/normalization source, including the padding certificate, has 9 bodies /
44 body lines; the port has 9 / 46. The additional `bitsFrame` and supported-bind rules add
2 bodies / 7 lines, and the two existing clients lose 7 lines. Thus the entire batch, including
all helpers and refactors, adds 11 bodies / 46 lines relative to `fa6e514`. This is an API/reuse
improvement, not a reduction in the matched normalization proof length.
The library total is 5,591 bodies / 38,245 lines in 522 modules, median 3 / P90 17. As above,
these are layout measurements, excluding definitions, statements, tests and generated code.

Regressions check exact framing, empty and overlong words, raw-bit and generic-list input
encodings, equivalent functional expressions, and a genuinely variable-output-length function.
A concrete wrong-length inverter has success zero after normalization and one before it,
guarding the inequality and unrestricted-candidate contract. Six new axiom guards cover the
security reduction, fixed-width existence, padding and supported-bind monotonicity. Source/API
review approves the implementation, and all six project checks pass. Raw tactic heartbeat counts
are 18,135 for the normalization certificate and 307,318 for its PPT inverter wrapper. Under the
same current imports and registered rules, the old/new Cook–Levin parameter proof bodies measure
345,463 / 316,591; these are elaboration costs, not machine runtime or a comparison against the old
registration environment. Independent adversarial correctness review follows publication.

### Implementation priorities (2026-10-16)

1. Efficient closed stateful substitution is implemented through finite tables, encoded
   configurations and simulation, preserving the joint result/private-state law and charging
   computation, copying, queries, replies and storage growth. Use it in the crypto reductions.
2. Make constructor, projection, lookup and composition certificates infer encodings predictably;
   test equivalent functional expressions and alternative encodings instead of adding syntax
   cases to tactics.
3. Improve reusable loop size and invariant rules for lists, bounded tables, caches and nested
   loops, leaving clients the meaningful invariant and automating routine encoding arithmetic.
4. Centralize configuration views, tape partitions, handoff identities and preservation lemmas,
   using oriented simplification without globally simplifying machine transitions.
5. Factor repeated good-event, indicator-expectation and cardinality/logarithm bookkeeping when
   multiple clients demonstrate reuse; include the helper API in proof-burden comparisons.
6. The entire existing Cook–Levin reduction is certified polynomial-time; SAT NP-completeness
   and UNSAT coNP-completeness are unconditional. Reuse its construction rules in further reductions.
7. Complete general OWF → PRG through the remaining pseudoentropy and security reductions,
   reusing Goldreich–Levin, the OWP result and polynomial stretch.
8. Adaptive GGM security and PRG → PRF are implemented over the shared oracle calculus. Derive
   general OWF → PRF once the pseudoentropy-based OWF → PRG theorem is complete.
9. Keep PCP polynomial-time constructibility and explicit expander construction distinct from
   combinatorial correctness and polynomial output-size bounds.
10. Validate each abstraction against demanding clients, total proof burden and elaboration
    behavior; run both independent reviews and all six project checks, then commit and push
    coherent batches. Prioritize abstractions that unblock these developments.

### Next design experiments

1. **Repeat trials and certify oracle programs.** Closed adaptive loops now have resource and
   semantic invariant rules with functional clients; independent repetition and the complete
   adaptive GGM reduction use them. Port the empirical probability tests and collection helpers
   needed by pseudoentropy. General open-program composition remains separate work.
2. **Gaussian sampling.** `Layouts/Gaussian/Sample.lean` and `Layouts/MultiGaussian.lean`
   repeat finite union bounds, construction of a bad event and extraction of a good sample.
   Trial a shared finite-family existence lemma using Mathlib's existing measure union bounds;
   retain concentration estimates and layout geometry in the applications.
3. **Configuration algebra.** In `Combinators/TidyNormalForm.lean`, add narrowly oriented
   preservation/composition lemmas for `PairReady` and `clearedCfg` if they shorten both
   recursive clearing and final assembly. Use `simp` for these identities, keeping machine
   step functions out of the simp set. The visited-interval and resource arguments remain.
4. **Indicator and cardinality calculations.** PCP's second-moment proof repeatedly expands
   indicator sums and moves expectations through finite sums; start with a local lemma and
   promote it to `Foundations/Data/Finset/Expect.lean` only with a second useful client.
   The existing second-moment inequality is already there. Frontier bounds likewise deserve
   common cardinality-to-real estimate lemmas where two clients currently repeat conversions.

These remaining items are reviewed candidates, not measured savings or completed refactors. Prefer
`fun_prop` for composition, curated `simp` normal forms for structural identities, and a small
domain-specific Aesop rule set for choosing specification rules. Broad search does not replace
uniformity, invariant, concentration, or asymptotic arguments. Judge each experiment on client
readability, total reusable API cost, and elaboration behavior as well as body-line counts.

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
   as *components*: a general configuration is `{ tapes : Turing.Cfg k Symbol State input,
   channels : Oracle → Channel }` and a general action is upstream's action plus per-channel
   query/answer actions. Then the effect-free step *is* upstream's `Action.apply` on the
   `tapes` field, and `MultiTapeTM.toMachine`/`MultiTapeMachine.toTM` are step-for-step bisimulations
   (one step = one step; the same work cells visited). Time and space therefore transfer
   *exactly*, not up to constants — unlike v1's interop (3× time, space one-way).
2. **Recover both upstream machines.** Make the choice functor cover nondeterminism too:
   `Tr : State → Option Symbol → (Fin k → Option Symbol) → Choose (Action …)` with
   `Choose := Id` (= `MultiTapeTM`), `Choose := Set` (= `MultiTapeNTM.Tr … → Action → Prop`),
   `Choose := (Bool → ·)` (fair coin, PTM). Prove `MultiTapeNTM ≃ Machine … Empty Set` and
   `MultiTapeTM ≃ Machine … Empty Id` as definitional-as-possible equivalences (now present as
   `MultiTapeMachine.ntmEquiv` and `tmEquiv`, oriented from the common machine), so
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

## Status (2026-10-16)

Milestone 1 (Cook–Levin) is complete, including the reduction's polynomial-time bound:

| Piece | Module | State |
|---|---|---|
| CNF over any variables, relabelling, exactly-one | `Logics/Propositional/CNF*.lean` | proved |
| Polynomial-time implication clauses, relabelling and exactly-one constraints | `Logics/Propositional/CNF/PolyTime.lean` | proved for arbitrary variable encodings, including repeated variables |
| `P`, `NP` (verifiers, `Polynomial ℕ` certificate length), reductions, `NPHard` | `Computability/Complexity/{Classes,Reduction}` | defined |
| `SAT`, `encCNF`, verifier correctness | `Problems/SAT.lean` | proved |
| Tableau of a multi-tape run and its correctness | `CookLevin/{Tableau,Correctness}.lean` | proved (`tableau_satisfiable_iff`) |
| The reduction and its correctness | `CookLevin/Reduction.lean` | proved (`reduce_mem_SAT_iff`) |
| Polynomial-time SAT verifier, `SAT ∈ NP`, `UNSAT ∈ coNP` | `Problems/SAT/PolyTime.lean` | proved, using the vendored calculus and reusable polynomial-time list rules |
| Parameterized maps, flat-maps and filtering, unary lengths and ranges | `MultiTape/Complexity/PolyTime/List.lean` | proved, allowing polynomial-sized intermediate lists for tableau enumeration |
| Unary arithmetic, pairing, polynomial evaluation and conversion to binary | `MultiTape/Complexity/PolyTime/Nat.lean` | proved |
| Signed unary positions, integer numbering and tape-window enumeration | `MultiTape/Complexity/PolyTime/{Int,Window}.lean` | proved using the existing signed encoding and `windowList` |
| Polynomial-time input prefix, certificate length and time bound | `CookLevin/Parameters.lean` | proved for the parameter function shared with `reduce`; both bounds are in unary |
| Polynomial-time variable construction and binary relabelling | `CookLevin/Encoding.lean` | proved using the existing indices in unary as an intermediate representation |
| All clause families, including input/read and step construction | `CookLevin/Clauses.lean` | proved for the existing clause definitions; computed parameters compose through `fun_prop` |
| Complete tableau and `ComputableTidilyInPolyTime (reduce tm p c d enc) …` | `CookLevin/PolyTime.lean` | proved, including parameter computation and binary relabelling |
| `NPComplete encCNF SAT` and `coNPComplete encCNF UNSAT` | `CookLevin/Completeness.lean` | proved unconditionally; local-only staging removed |
| `ThreeSAT` and correctness of `SAT ≤ 3SAT` | `Problems/ThreeSAT.lean`, `CNF/ThreeCNF.lean` | proved (polynomial time open) |

Circuit track (independent of the calculus): `P/poly` over upstream circuits and `Language.slice`,
and **`P ⊆ P/poly` proved** (`Cslib.Circuits.Boolean.PPoly.of_mem_P`) by a feature-by-feature
simulation built from upstream `Synthesis` (state, heads, cells and output view at step `t + 1` as
Boolean combinations of step-`t` features, `O(n + T)` gates per feature, `fun_prop` for the
polynomial bound). This redoes the withdrawn cslib PRs #1100/#1101 without frame encodings. Also proved: some
language is not in `P/poly` (from upstream Shannon), and Karp's reductions `SAT ≤ IndependentSet`
and `IndependentSet ≤ Clique` are correct (their polynomial-time certificates remain open).
The simulation is stated over `Turing.MultiTapeTM.Feature` (`MultiTape/Feature.lean`): finite
observations of a configuration with one lemma per kind describing how a step changes it, meant
to be shared with the Cook–Levin tableau. `Threshold.lean` synthesises the threshold and majority functions (defined with the Hamming
weight in `Foundations/Data/BitString/Weight.lean`) with quadratic cost, the ingredient for amplification in `BPP ⊆ P/poly`. A non-vacuity
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

**The first levels and complement duality of PH are proved** (`Classes/PH.lean`):
`Σ₀ = Π₀ = P`, `Σ₁ = NP`, `Π₁ = coNP`, `Πₖ = coΣₖ`, and `P, NP, coNP ⊆ PH`.
The polynomial-time calculus discharges the former assumptions about ignoring a certificate,
supplying the empty certificate, and negating the verifier's output.

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
(`Cslib.Logic.PL.DNF.card_switching_le`, `Cslib.BitString.PartialAssignment.card_withFree`).
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

**Fourier analysis on the Boolean cube** (`Foundations/BooleanAnalysis/Fourier.lean`, from v1's
`BooleanAnalysis/FourierExpansion` without its inner-product-space type synonym): characters
`χ_S` on `ι → Bool`, orthonormality under Mathlib's `𝔼`, the Fourier expansion and
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
mentioned but did not contain it): the Fourier weight on sets of at least `k` coordinates of a
function computed by an unbounded fan-in circuit of depth `d` with `g` gates is at most
`2 g / 2 ^ s` once `max 8 (2 s) n ≤ k ⌊n / (16 s + 1) ^ d⌋`. It combines the counted stages of
Håstad's argument (`Circuit/Boolean/Hastad.lean`, from which Håstad's theorem now follows),
Fourier coefficients of restrictions, decision-tree degree, and Chebyshev's inequality for random
subsets (`Foundations/Combinatorics/Hypergeometric.lean`).

**Korten's top-down lower bounds** (`Circuit/Boolean/TopDown.lean`, over the round protocols of
`Communication/RoundProtocol.lean`, the adversary of `Communication/TopDown/` and the sampling
lemmas of `Foundations/BooleanAnalysis/`): a circuit of AND/OR depth `d` (negations free,
`Circuit.depthWith` in `Circuit/Depth.lean`) with `g` gates gives a Karchmer–Wigderson protocol
with `d` messages from its `n + g` wires, and parity has no such protocol unless
`n + g > 2 ^ (ε n ^ (1 / (d - 1)))`, so parity needs more than `n ^ k` gates at every fixed depth;
the same for majority. In AND/OR depth this is the optimal exponent, against `1 / (d + 1)` from
Håstad's argument above.

**Shallow circuits for symmetric functions** (`Circuit/Boolean/ShallowSymmetric.lean`, over
alternating formulas in `Circuit/Boolean/AltFormula.lean`): the theorem of Lecomte and
Ramakrishnan, every symmetric function has depth-`d` circuits of size `2 ^ O(n ^ (1 / (d - 1)))`,
with negations free at the inputs, and so unbounded fan-in circuits of AND/OR depth `d` (depth
`d + 1` counting negations). By Korten's bounds for alternating formulas
(`Circuit/Boolean/AltFormula/TopDown.lean`) and for circuits of AND/OR depth `d`, this is optimal
for majority.

**Resolution** (`Logics/Propositional/Resolution.lean`): soundness and refutation completeness.

**Exponential-time SAT combinatorics.** The satisfiability coding lemma of Paturi, Pudlák and Zane
(`Logics/Propositional/CNF/Coding.lean`): a solution isolated in `ι` directions of a width-`k`
formula is coded in `N - ι / k` bits on average over orders, so `∑ₓ 2 ^ (ι(x) / k) ≤ 2 ^ N`. The
**sparsification lemma** of Impagliazzo, Paturi and Zane (`Logics/Propositional/ClauseSet/
Sparsification.lean`, over clause sets in `ClauseSet/Basic.lean`, with the proof of Calabro,
Impagliazzo and Paturi in `ClauseSet/Sparsification/{Step,Path,Tree,Bounds}.lean`):
every width-`k` CNF over `N` variables is the disjunction of at most `2 ^ (ε N)` width-`k` CNFs in
which every variable occurs in at most `c(k, ε)` clauses. Normal forms have a term per isolated
input, so those of parity have at least `2 ^ (n - 1)` terms (`Logics/Propositional/Parity.lean`).
By the coding lemma, an OR of width-`k` CNFs for parity has at least `2 ^ (n / k - 1)` of them,
which is attained when `k ∣ n`, and by its weighted version (PPZ's Lemma 5) any OR of CNFs for
parity on `n ≥ 4` bits has at least `n ^ (1 / 4) 2 ^ (√n - 1)` CNFs and distinct clauses
together, and so does any AND of DNFs: PPZ's Theorem 6 in full
(`Logics/Propositional/Parity/DepthThree.lean`, beyond v1). With both lemmas, a width-`k` CNF
whose solutions contain no subcube of dimension `D` has at most `2 ^ ((1 - 1 / k + ε) N + C D)`
solutions (`Logics/Propositional/ClauseSet/SubcubeFree.lean`), so subcube dispersers need
`Σ₃^k ≥ 2 ^ ((1 / k - ε) n)` (`Logics/Propositional/SigmaThree.lean`).

**Razborov–Smolensky** (`Circuit/Boolean/Smolensky.lean`, over `Smolensky/{Gates,Approximation}`,
`Foundations/BooleanAnalysis/LowDegree{,Parity}.lean` and `Foundations/Combinatorics/CentralBinomial.lean`):
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

## Porting queue toward parity (2026-10-15)

From an inventory of v1's headline results that v2 lacks (excluding v1's `Algebraic/` tree and
the OpenAI-sourced modules listed in v1's `docs/OpenAIMath.md`), ported by parallel agents in
worktrees and reviewed before merging. Ported on 2026-10-15: influences, noise stability,
convolution and BLR (O'Donnell chapters 1 and 2), PPZ's Theorem 6 in full, `ACⁱ ⊆ NCⁱ⁺¹`, the
Hadamard code and tester, Nisan–Wigderson (reconstruction and designs), sparse corrections,
Cheeger's inequality, graph products, relative-error approximate counting.

| Target | v1 source | State |
|---|---|---|
| Monotone Karchmer–Wigderson | `Circuits/KarchmerWigderson*`, `Circuits/Monotone*` | done (`Circuit/Monotone/KarchmerWigderson.lean`) |
| Barrington: NC¹ = width-5 permutation programs | `Circuits/Barrington{Typed,Family,Converse}`, `CircuitFormula/*` | done (`Circuit/Boolean/BarringtonClass.lean`) |
| Yao's hybrid argument (distinguisher to next-bit predictor) | `Metacomplexity/StatisticalTest/Hybrid*` | done (`Crypto/Primitives/PRG/NextBit.lean`, over cslib's PRG game) |
| Lautemann's covering lemma | `Classes/PH/SipserLautemann/Covering` | done (`Foundations/Combinatorics/Lautemann.lean`) |
| Expander mixing lemma, edge expansion | `Classes/PCP/Internal/{RegularGraph,Mixing,EdgeExpansion}` | done (`Foundations/Combinatorics/Expander/`) |
| Pairwise-independent hashing, approximate counting | `Classes/Randomized/Hashing*`, `ApproximateCounting/**` | done (`Probability/`, relative error in `ApproximateCounting/Relative`) |
| Exponential correlation bounds for GF(2) polynomials (CHLLTV) | `BooleanAnalysis/PolynomialCorrelation*` | done (`BooleanAnalysis/PolynomialCorrelation`) |
| Sparse corrections, square-root continuity of circuit complexity | `Circuits/SparseSynthesis*`, `Cslib/Circuit/Boolean/Correction*` | done (`Circuit/Boolean/{Correction,SparseSynthesis}`) |
| Hadamard decoding and testing, local correctability | `Classes/PCP/Internal/{Hadamard,CubeBlocks,HadamardTester}` | done (`BooleanAnalysis/{Hadamard,HadamardTester}`) |
| Cheeger's inequality (hard direction), constant-degree expanders | `PCP/Internal/{Cheeger,ExpanderRandom,…}` | done (`Expander/{Cheeger,Loops,Perm,Random,Family,Tower,TowerBase}`); the fully explicit RVW recursion open |
| Zig-zag product | `PCP/Internal/ZigZag` | done (`Expander/{Power,Products}`, with tensor and balanced replacement products; the tower in `Expander/{Tower,TowerBase}`) |
| Nisan–Wigderson reconstruction | `Metacomplexity/NisanWigderson/**` | done: reconstruction, designs, circuits, sampling and the list-decoding reconstruction (`Crypto/Primitives/PRG/NisanWigderson{,/Design,/Circuit,/Sampling,/Reconstruction}`), the `Kᵗ` bound (`Computability/Kolmogorov/NisanWigderson`); open: a concrete list-decodable code family |
| Dinur's gap theorem | `PCP/Internal/GapTheorem` and its closure (Bolton Bailey) | done: constraint graphs, the 3-SAT reduction, degree reduction and preprocessing (`Computability/PCP/`), walks and killed walks (`Expander/{Walk,KilledWalk}`), the assignment tester and composition (`PCP/{LocalTest,AssignmentTester,Composition}`), powering (`PCP/{Power,PoweringBound}`), the amplification round, amplifiers and the gap theorem (`PCP/{Amplification,Amplifier,GapTheorem}`); next: polynomial-time constructibility, which needs explicit expanders and the poly-time calculus |
| Multi-tape to single-tape simulation, time `O((T + n)²)` | `Models/TuringMachine/SingleTape` | queued (machine level, over upstream `MultiTapeTM`) |
| Machine-relative Kolmogorov complexity, incompressibility, invariance | `Metacomplexity/Kolmogorov/**` | done (`Computability/Kolmogorov/`, on Mathlib's `Computation`, with a universal partial recursive method and the invariance theorem); machine clocks wait for crei's UTM |
| Nisan–Wigderson sampling layer and the Kt step | `Metacomplexity/NisanWigderson/Reconstruction/**`, `ListDecoding` | done (machine-relative; the decoder machine waits for a UTM) |
| Second-order logic, FO interpretations and reductions, order independence | `DescriptiveComplexity/{SecondOrder,Interpretation,…}` | done (`Logics/{FirstOrder,SecondOrder}`); order-invariant queries and congruences open |
| Logarithmic-cost RAM and the unsoundness of unit cost | `Models/RandomAccessMachine/{Defs,Soundness}` | done (`Computability/RAM/`) |
| Finite cores of Savitch and of inductive counting | `Classes/Containments/Internal/ReachIn`, `InductiveCounting`, `CountingCert` | done (`Foundations/Relation/`) |
| Depth-two threshold circuit for parity | `Circuits/Threshold/Parity` | done (`Circuit/Boolean/Threshold{,/Parity}`): `n + 1` threshold gates, threshold depth two; TC⁰ = `ConstDepth Threshold.interpretation` |
| Frontier method, correlation with quadratic forms | `Circuits/Frontier/**`, `Circuits/Correlation*` | batches 1 and 2 done (`Circuit/Frontier/`; the lower bound conditional on `LayoutBound`); spanning-tree layouts and the unconditional `(2 − ε) n` bound done (`Frontier/{Layouts/*,Unconditional}`); the Gaussian toolkit done (Sheppard's bound, second moments, kernel rows); extensions done: linear maps (`Frontier/Linear/*`), hidden inputs, nondeterministic circuits and decomposable DAGs (`Frontier/{Projection,Nondeterministic,Decomposable}`), ledgers for aggregate gates of unbounded fan-in (`Frontier/{Components,Ledger/*}`); the Gaussian layouts and the fan-in-two bounds `(L − ε) n`, `L ≈ 4.5625`, `(4.56 − ε) n` and `(4 − ε) n` done (`Frontier/{Layouts/*,FanInTwo}`, from the independent formalization `circuit-lb-4.56-lean`); the core aligned with `circuit-lb-4.56-lean` (read-once branching programs, `Frontier/{BranchingProgram,AverageCase}`), and its six headline claims (`CircuitLowerBound` and `AverageCaseBound` with `L`, `114/25`, `4`) done; correlation `2^{-γ n}` with nonconstructively chosen bilinear forms below `≈ 2.78 n` gates done (`Frontier/Correlation{,/*}`); the general fan-in bound via vertex-score layouts done (`Frontier/BoundedFanIn`) |
| Class-level results (Savitch, hierarchies, `PH ⊆ PSPACE`, Sipser–Lautemann, Cobham, `PCP = NP`, RAM-P = P, …) | `Classes/**`, `Models/**` | queued for machine and resource-bound certificates using the now-vendored calculus |

The polynomial-time calculus and UTM are now available. The class-level forms of the time
hierarchy, Savitch, `NL ⊆ P`, `PH ⊆ PSPACE`, Sipser–Lautemann and the PCP theorem still need their
machine and resource-bound certificates; PCP also needs explicit expander constructibility.

Second source: [karnseth/katz-lindell](https://github.com/karnseth/katz-lindell) (Apache 2.0).
Its proofs (`infra/`) are complete; its statements came from a Codex-generated layer, so they are
restated from Katz–Lindell rather than copied. Queued from it, after the Yao and hashing ports:
PRGs from one-way permutations with a hard-core bit and length extension (Theorems 8.6 and 8.7),
Blum–Micali (Exercise 8.10), PRGs give one-way functions (Proposition 8.27), closure of
computational indistinguishability under repetition, and pairwise-independent tail and birthday
bounds. Done: strongly universal hash families, the shift criterion and Toeplitz hashing
(Exercises 4.24–4.26, `Probability/PairwiseIndependentHash/{Shift,Toeplitz}`). Goldreich–Levin, the
switching lemma and Luby–Rackoff are planned as cslib PRs by the katz-lindell authors, so they
wait on coordination.

## Realignment with crei's `tidy-universal` branch (2026-10-13)

crei's fork branch `crei/tidy-universal` (39 commits, ~9.3k lines; not yet a PR) implements
most of L1, L3 and the UTM part of L4 in exactly the style this plan wanted:

* explicit encodings `α ↪ List Bool` with capability classes (`PairEncoding`, `ListEncoding`,
  `OptionEncoding`) and canonical instances `encPair` (framed first component), `encList`,
  `encOption`, `encNat` (`Nat.bits`), `encBool`, `encBits`;
* `ComputableTidilyInPolyTime f encIn encOut`, closed under composition, pairing, case
  distinctions and folds, **registered with `fun_prop`**;
* combinators (composition, iterate-while, folds, streaming folds, transducers) and arithmetic;
* a universal multi-tape simulator as ordinary Lean functions with explicit time and space bounds
  (`Universal/{Basic,Machine,Correct,Complexity,Bound}.lean`).

It merges into current cslib main with two trivial conflicts and the merge builds
(checked in a scratch clone). Consequences for v2:

1. v2's own `Encoding` typeclass is dropped in favour of crei's explicit encodings; problems are
   `Set α` with an explicit `enc : α ↪ List Bool`, as upstream `DecidableInTimeAndSpace` does.
2. `PolyTime` is crei's `ComputableTidilyInPolyTime`; v2 does not build its own calculus.
3. The universal simulation backend is crei's; v2's hierarchy work will build on `Universal/`.
   The free-monad interface and realization layer are separate from crei's backend; v2 now
   supplies the typed frontend, closed PPT contract, monadic composition, captured inputs and
   invariant-certified bounded probabilistic loops, and the word-oracle realization contract.
   Closed stateful substitution is certified; general open-program composition remains pending.
4. **Superseded (user, 2026-10-15): "unblock everything", and the calculus may be improved
   freely.** crei's calculus and universal machine are vendored in full as tracked local copies
   (`-- upstream: vendored crei:crei/tidy-universal @7f7c0696`, `submitted #1111`, `#1138`),
   adapted to the pinned upstream main; `scripts/upstream_sync.py` reports when they merge or
   move. Turing machines still come from upstream main (the pin is never crei's branch).
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
- `structure MultiTapeMachine (k) (Symbol State Oracle : Type*) (Choose : Type → Type)` with
  `initial : State`, `tr : State → Option Symbol → (Fin k → Option Symbol) → (Oracle → Option Symbol)
  → Choose (Action k Symbol State Oracle)`.
  `Action` = upstream `Turing.Action k Symbol State` + `channel : Oracle → ChannelAction Symbol`
  (write one query symbol / submit query / move answer head). `Cfg` = upstream `Turing.Cfg`
  + `channels : Oracle → Channel Symbol`. Exact definitions follow crypto-frontier
  `MultiTape/Machine.lean`, with upstream types as the `core`.
- Semantics now implemented: effect-free `step` / `Step`, and `runConfigFrom` as a typed
  `PFunctor.FreeM` program with explicit choice/query handlers. Pause/resume and substitution are
  equalities of programs. Arbitrary handlers are not automatically fair, efficient, or faithful
  resolvers of `Set` choices; the nondeterministic step relation preserves stuck configurations.
- Equivalences now implemented: `tmEquiv`, `ntmEquiv`, `step_toTM`, `step_toNTM_iff`, and
  `runConfigFrom_toTM`. Further resource-transfer lemmas and the probabilistic realization
  bridge to the tidy calculus remain to be supplied as needed.
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

- `lean-toolchain` **identical** to cslib's at the pinned SHA (currently `v4.35.0`). `[[require]] cslib` from git with `rev = <SHA>`;
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
**Exit criterion (met):** `CookLevin.SAT_npComplete` axiom-clean; the tableau's complexity proof
is `unfold tableau; polytime`, composed with the parameter and relabelling certificates, with no
hand-built machine beyond the L3 primitives.

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

- Every phase: `lake build --wfail --iofail`, `lake exe mk_all --check`, `lake test --wfail --iofail`,
  `lake lint`, `lake exe lint-style`, `lake exe checkInitImports` (same commands as cslib's CI),
  no `sorry` in `Complexity`, and the axiom tests pass (only `propext`, `Classical.choice`,
  `Quot.sound` on headline theorems).
- Ergonomics check (phase 2/3): `ComplexityTests/Reductions.lean` contains ≥10 realistic
  reduction functions each proven `PolyTime` by `by fun_prop` or `by polytime` in one line;
  `ComplexityTests/Programs.lean` writes a small oracle/coin program in `do` notation and
  obtains its certificate by closure rules only.
- Upstream rehearsal (every phase): run `scripts/upstream.py` on at least one module into a
  fresh cslib worktree at the pinned SHA and pass cslib's gates there.
- Milestone 1 acceptance: `CookLevin.SAT_npComplete` compiles axiom-clean; the reduction's
  polynomial-time certificate uses `fun_prop`/`polytime` and composition, with no bespoke machine.
- Blocker log: cslib PR #1111 and crei's calculus are vendored. Cook–Levin is complete.
  General OWF → PRG, PCP polynomial-time constructibility and explicit expanders remain open.

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
