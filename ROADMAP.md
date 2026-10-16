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
oracle PPT remains to be integrated into v2.
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
| Shared effectful machine and clocked programs | `Id` / `Set` equivalences to upstream, exact deterministic runs, one program interpreter with pause/resume and substitution laws; Boolean-indexed tables and closed fair-coin runs; shared-tape sequencing with additive actual halting bounds and exact agreement with upstream deterministic sequencing |
| GGM tree evaluation | ported, including truncation and size laws; uniform TM certificate through the existing tidy fold calculus |
| Uniform PPT and oracle PPT, `ppt` automation | closed `IsPPTOn`, deterministic bridge, fair bits and runtime-length uniform words, monadic bind, deterministic preprocessing/postprocessing, captured inputs and conditionals registered with `fun_prop`; `ppt` combines these with named/local certificates and `polytime`; total saved-seed evaluation certifies bounded adaptive loops, with one invariant for resources and postconditions; `ppt` handles constant growth. Machine composition charges preparation and has intrinsically halting finite witnesses; oracle PPT remains pending |
| OWP → PRG | queue `OneWay`, `HardCore`, `GoldreichLevin/*`, then length extension |
| General OWF → PRG | queue `OneWay/Normalize`, `Pseudoentropy/*`, entropy-grid and uniform-length conversion, then `OneWayToPRG` |
| PRG → PRF and OWF → PRF | queue GGM expansion, hybrid, reduction and security, then `OneWayToPRF` |

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
theorem still requires the remaining reductions; evaluation alone does not establish it.

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

### Next design experiments

1. **Repeat trials and certify oracle programs.** Closed adaptive loops now have resource and
   semantic invariant rules with functional clients. Port the independent repetition, empirical
   probability tests and collection helpers used by Goldreich–Levin and pseudoentropy, then the
   stateful oracle realization contract required for adaptive GGM security. Preserve the joint
   result/private-state distribution and charge query and reply lengths.
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

## Status (2026-10-15)

Milestone 1 (Cook–Levin) is complete except for the reduction's polynomial-time bound:

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
| Initial, accepting, situation and one-hot clause construction | `CookLevin/Clauses.lean` | proved for the existing clause definitions; composed clients close with `fun_prop` |
| `NPComplete encCNF SAT` from the reduction's polynomial-time bound | `CookLevin/Staging.lean` | proved (local-only staging) |
| `ComputableTidilyInPolyTime (reduce tm p c d enc) …` | — | **open**: input/read and step clauses, then full tableau assembly; the one-hot family is certified |
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
   invariant-certified bounded probabilistic loops, while oracle PPT remains pending.
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
- Blocker log: cslib PR #1111 and crei's calculus are vendored. SAT verifier certification is
  complete; the remaining Cook–Levin blocker is the reduction's polynomial-time certificate.

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
