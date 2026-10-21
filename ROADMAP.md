# Development roadmap

Outstanding work and the rationale needed to guide it. See the [README](README.md) for
completed reference developments.

## Long-term coverage and reuse

The long-term bar is to support formalizing every paper appearing in the
[Electronic Colloquium on Computational Complexity](https://eccc.weizmann.ac.il/colloquium/call_for_papers/).
Across successive papers, the additional work should increasingly be their new mathematics:
standard models, representation changes, reductions, resource certificates and proof techniques
should come from the library. This is an amortized goal. A new method may require substantial
infrastructure once; later developments should reuse it instead of rebuilding it. Count that
infrastructure's implementation and maintenance cost when assessing the improvement.

### Catalogue the classes and theorems

Build an auditable coverage index spanning the complete
[Complexity Zoo](https://complexityzoo.net/Complexity_Zoo), including its hierarchies, nonuniform
and communication classes, and extend it with the canonical problems and theorems needed by ECCC
papers. The Zoo supplies a catalogue and references; verify definitions and results against their
primary sources. This is a coverage target, not a claim that the catalogue is already formalized.

Each entry should record its source and aliases, precise model and conventions, existing Lean
declarations, missing prerequisites, and status: unassessed, definition only, partial development,
or verified theorem. Track containments, separations, closure properties, complete problems and
reductions separately. A defined class or a combinatorial lemma does not establish its advertised
machine characterization, completeness theorem or efficient construction.

Cover decision, function, search, counting, promise, distributional and parameterized problems.
Keep uniformity, advice, oracle access, error gaps, resource measures and reduction types explicit.
Share class operators and their closure theorems where they derive families of variants. Keep
canonical definitions in their mathematical modules; the index should link to them rather than
maintain a second set of definitions. Existing module docstrings, source markers and the detailed
milestones below remain the authority for their respective facts.

### Next steps after basic class closure

The verifier-based `UP` and `CeqP` developments, basic Boolean closures, exact-count
polynomial-time precomposition, and generic DP/SAT–UNSAT completeness are implemented.
The forward machine-to-verifier direction is proved for `#P` and `GapP`: accepting and
rejecting terminal counts of fixed finite-control list-choice machines under polynomial clocks
have actual certified binary verifiers. The actual reverse guess-and-verify construction and
[#P machine characterization](Complexity/Computability/Complexity/Classes/SharpP/Characterization.lean)
are now proved. The [signed GapP construction and characterization](Complexity/Computability/Complexity/Classes/SharpP/GapMachine.lean)
are also proved, using balanced verdict routing and an actual selector between independent witness
families. The [UP](Complexity/Computability/Complexity/Classes/UP/Machine.lean) and
[FewP](Complexity/Computability/Complexity/Classes/FewP/Machine.lean) native characterizations
are also proved: the exact #P bridge preserves the bound of one or a polynomial on accepting
occurrence traces, independently of the all-branches clock. SPP, FewP, fixed-modulus ModP, coUP and coC=P
now have verifier-based definitions and basic closure/containment developments. FewP ⊆ SPP and
PH ⊆ P^#P = P^PP are proved, with uniform simulations under the function-bit oracle convention.
Exact #P/GapP counts now have certified binary-output polynomial-space evaluators, yielding
PP ⊆ PSPACE and P^PP = P^#P ⊆ PSPACE, including arbitrary injective oracle encodings via
total clocked counting-machine extensions
([counting space](Complexity/Computability/Complexity/Classes/Counting/OracleSpace.lean)).
Extend these with counting reductions and further oracle results, preserving exact
multiplicities when required. The current modular Boolean closures require a prime modulus. The complementary modular class is
implemented, with equality to ModP for prime moduli. Fixed positive moduli admit GapP
zero/nonzero-residue characterizations; SPP (hence FewP) is in both modular classes for every
modulus at least two, including composite moduli. Both modular classes lie in PSPACE for every
fixed natural modulus. US, coDP, the finite Boolean
hierarchy (`BH` and `coBH`, base-class Boolean operations on `BH`, and the finite-hierarchy
level-collapse equivalences `BH_{k+1} = BH_k ↔ BH_k = coBH_k ⇒ BH = BH_k`), WPP and LWPP now have
definitions and elementary containments/closures. Full Boolean-hierarchy Boolean closure is
proved with explicit finite-level upper bounds, as is BH ⊆ Σ₂ ∩ Π₂ using same-level union and
intersection closure of every Σₖ and Πₖ
([hierarchy connection](Complexity/Computability/Complexity/Classes/BooleanHierarchy/PH.lean)).
Further proved results include LWPP many-one
reduction closure, unary-indexed target normalization, and full one-sided polynomial-family
multiple-target robustness: Poly-WPP = WPP and Poly-LWPP = LWPP, and the full two-sided
(Poly,Poly)-WPP/WPP and (Poly,Poly)-LWPP/LWPP characterizations with disjoint uniformly computed
accepting/rejecting binary target lists. Original targets may be zero; neither index must be
computable ([WPP.TwoSided](Complexity/Computability/Complexity/Classes/WPP/TwoSided.lean)).
Uniform bounded conjunction and disjunction also preserve both classes for a single jointly
uniform language on instances and unary indices, with any polynomial-time unary input-dependent
bound. The LWPP proof normalizes all possible prefix targets at each length
([WPP.Bounded](Complexity/Computability/Complexity/Classes/WPP/Bounded.lean)); it does not
establish adaptive oracle closure. Polynomial-time truth-table reductions now preserve both
WPP and LWPP, using an arbitrary polynomial-time Boolean combiner on a uniform batch of
queries ([WPP.TruthTable](Complexity/Computability/Complexity/Classes/WPP/TruthTable.lean)).
Query lengths and unary query counts may vary at fixed input length; LWPP normalizes both.
Adaptive WPP closure, UP-oracle containment, and oracle lowness are not claimed by this result.
The binary-output FP-to-#P/GapP bridge is available. Parsimonious Cook–Levin gives #P-completeness of #SAT and SAT-based complete problems for ⊕P, US, ModₖP/coModₖP, PP (both threshold #SAT and MAJSAT) and C=P/coC=P ([CountingSAT](Complexity/Computability/Complexity/Problems/CountingSAT.lean)). Remaining extensions include
permanent completeness, Kadin's polynomial-hierarchy collapse from a Boolean-hierarchy
collapse, and WPP/LWPP oracle lowness.
SBP and AWPP now have verifier-based definitions, the elementary NP/BPP/SPP-to-PP
containments, many-one reduction closure, SBP union closure and AWPP Boolean closure.
WPP ⊆ AWPP is proved, including signed binary-output targets. Uniform AWPP
amplification achieves error at most `2^(-r(x))` for every requested exponent polynomially
bounded in encoded input length, using one GapP numerator and a length-polynomial
dyadic denominator. The requested rate need not be computable: the construction
uses a fixed dominating polynomial. The explicit construction uses `12q(n)` majority
trials and denominator exponent `12q(n)p(n)`; see
[AWPP amplification](Complexity/Computability/Complexity/Classes/AWPP/Amplification.lean).
[Uniform SBP amplification](Complexity/Computability/Complexity/Classes/SBP/Amplification.lean)
achieves multiplicative gap `2^r(x)` for every polynomially bounded requested exponent,
with a #P count and positive binary-output polynomial-time threshold. Intersecting an SBP
language with a BPP language stays in SBP. MA ⊆ SBP is proved with the Arthur–Merlin classes.
The [set lower bound protocol](Complexity/Computability/Complexity/Classes/ArthurMerlin/SetLowerBound.lean)
already proves SBP ⊆ AM. [Uniform indexed #P/GapP products](Complexity/Computability/Complexity/Classes/SharpP/Products.lean)
provide a counting-algebra foundation for future oracle simulations.
[Relativized counting and majority verifiers](Complexity/Computability/Complexity/Classes/PP/Oracle.lean)
now provide the positive-GapP characterization and elimination of P-decidable oracles;
AWPP PP-lowness remains an approximate-counting milestone.
These definitions retain the verifier-model boundary stated above.

### Extend the mathematical canon

This map adds long-term directions to the concrete developments below. It follows the breadth of
[ECCC's scope](https://eccc.weizmann.ac.il/colloquium/call_for_papers/) and the Zoo, rather than the
contents of the original port. Entries are targets for coverage audits and substantial theorem
developments, not assertions that every prerequisite is missing or assignments to current workers.

| Area | Coverage to establish or extend |
| --- | --- |
| Structural complexity | Time/space and exponential hierarchies; oracle and advice classes; unambiguous and promise classes; completeness, padding, self-reducibility, Ladner's theorem, relativization and oracle separations. Preserve each reduction's resource bound. |
| Space and alternation | Build on native `NPSPACE = PSPACE`, TQBF completeness, `NL ⊆ P`, [PH ⊆ PSPACE](Complexity/Computability/Complexity/Classes/Inclusions.lean) and [AP = PSPACE](Complexity/Computability/Complexity/Classes/Alternation/Savitch.lean). Extend the [machine-class milestones](#machine-class-milestones), alternating time/space classes and bounded-alternation characterizations of PH. Distinguish polynomial-space simulation from sharp bounds for sublinear space. |
| Counting and modular classes | Build on `#P`, `GapP`, `PP`, [parity-P](Complexity/Computability/Complexity/Classes/ParityP.lean) and [Toda's PH ⊆ P^#P theorem](Complexity/Computability/Complexity/Classes/Toda.lean), with a fixed polynomial-time program correct against every oracle answering the counting function's bits. Extend counting reductions and machine characterizations, permanent completeness, modular/counting hierarchies and the oracle-algorithm form of Stockmeyer approximate counting. |
| Interactive and probabilistic proofs | [IP ⊆ PSPACE](Complexity/Computability/Complexity/Classes/IP/PSPACE.lean) is proved for the strict polynomial-time, private-coin verifier model. [IP = PSPACE](Complexity/Computability/Complexity/Classes/IP/Shamir.lean) is proved, with a machine-certified Shamir–Shen-style verifier for TQBF; develop Arthur–Merlin classes, public/private-coin transformations, multiprover systems, zero knowledge and simulation. Reuse the existing PCP and probabilistic foundations. |
| Boolean circuits and parallel computation | Complete the [Jukna coverage](#jukna-coverage), uniform/nonuniform NC/AC/TC and related classes, circuit-to-machine bridges, algorithm-to-lower-bound arguments and barriers such as natural proofs and algebrization. |
| Algebraic and arithmetic complexity | Build on [VP and p-projections](Complexity/Computability/Circuit/Arithmetic/VP.lean), [VNP and VP ⊆ VNP](Complexity/Computability/Circuit/Arithmetic/VNP.lean), and [determinant ∈ VP](Complexity/Computability/Circuit/Arithmetic/Determinant.lean) over commutative rings. Prove permanent VNP-completeness with its characteristic assumptions, extend formula/branching-program models, identity testing, hitting sets, tensor and rank methods, and certify uniform construction costs separately from gate counts. |
| Approximation and constraint satisfaction | Gap and approximation-preserving reductions, APX/PTAS/FPTAS, canonical inapproximability consequences of PCP, CSP classifications and relaxation gaps. State assumptions such as the Unique Games Conjecture explicitly. |
| Pseudorandomness and coding | Hardness versus randomness, space-bounded generators, extractors/condensers, limited independence, explicit expanders, and list/local decoding. Separate finite combinatorial guarantees from uniform construction and decoding costs. |
| Complexity-theoretic cryptography | One-way functions imply SAT ∉ P and SAT ∉ BPP, and MCSP ∈ BPP rules them out (Kabanets–Cai; [OneWay/MCSP](Complexity/Crypto/Computational/OneWay/MCSP.lean)). Extend the existing OWF/PRG/PRF results with reusable adaptive reductions, commitments, zero knowledge, hard-core and hardness-amplification methods, and connections to learning and average-case hardness. |
| Communication, queries and data structures | Randomized and multiparty protocols, discrepancy and information complexity, direct-sum/product results, lifting theorems, and reductions to streaming, sketching and cell-probe lower bounds. Reuse upstream query models. |
| Proof complexity | Build on [Cook–Reckhow systems and simulations](Complexity/Logics/Propositional/ProofSystem.lean), including the polynomially bounded-system characterization of NP = coNP, the [resolution size–width tradeoff](Complexity/Logics/Propositional/Resolution/SizeWidth.lean) and [tree-like resolution/DPLL search-tree certificates](Complexity/Logics/Propositional/Resolution/TreeLike.lean). Extend proof-space and pigeonhole lower bounds (Tseitin formulas on expanders are [proved](Complexity/Logics/Propositional/Resolution/TseitinExpander.lean) hard for resolution), Frege, cutting planes, polynomial calculus and sum-of-squares. The certificate correspondence does not certify a DPLL solver's runtime. |
| Average-case complexity and learning | Uniform-distribution learning on CSLib's PAC API, the LMN low-degree algorithm and Kushilevitz–Mansour with membership queries are [proved](Complexity/MachineLearning/UniformLearning/KushilevitzMansour.lean); running times are not machine-certified. Distributional problems and reductions, samplability, average-to-worst-case connections, PAC/agnostic/SQ learning, learning lower bounds, compression and refutation. Existing cryptographic learners are starting points, not coverage of learning theory. |
| Property and distribution testing | Distance and access models, one/two-sided and tolerant testing, query/sample bounds, canonical graph/algebraic/distribution testers and lower bounds. |
| Fine-grained and parameterized complexity | Under ETH, 3-coloring, independent set, vertex cover and Hamiltonian cycle and path have no 2^{o(\|V\|+\|E\|)} algorithms and clique none in 2^{o(\|V\|)} ([GraphProblems](Complexity/Computability/Complexity/FineGrained/GraphProblems.lean)); the Hamiltonian bounds (directed and undirected) use linear-size diamond reductions. [FPT and XP](Complexity/Computability/Complexity/Parameterized.lean) are defined with arbitrary (not necessarily computable) `f`; `P ⊆ FPT ⊆ XP`, Boolean closure of FPT (complement for XP), closure under fpt-reductions and `FPT = XP = P` for bounded parameters are proved, and SAT is in FPT for the number of variables. [Kernelization](Complexity/Computability/Complexity/Parameterized/Kernelization.lean) (`IsKernelization`, `HasKernel`, `HasPolyKernel`) and the Cai–Chen–Downey–Fellows equivalence (`A ∈ FPT enc κ ↔ HasKernel enc κ A` for `A ∈ DTIME enc t` over a nonempty instance type) are proved, and [VertexCover](Complexity/Computability/Complexity/Parameterized/VertexCover.lean) is in FPT parameterized by target size `k` in time `O(2^k (|x|+1)^e)` by a bounded search tree. Further fine-grained reductions and consequences conditional on ETH/SETH and other named hypotheses; strongly uniform (computable `f`) variants, explicit polynomial kernels (e.g. Buss's kernel for Vertex Cover), W/A hierarchies and parameterized lower bounds. |
| Total search and computational games | Build on [FNP, FP and TFNP with search reductions](Complexity/Computability/Complexity/Classes/TFNP.lean), including `FP = FNP` exactly when `P = NP` ([search to decision](Complexity/Computability/Complexity/Classes/TFNP/SearchToDecision.lean)), `TFNP ⊆ FP → NP ∩ coNP ⊆ P`, and the canonical subclasses [PLS, PPP, PPAD and PPA](Complexity/Computability/Complexity/Classes/TFNP/Subclasses.lean) with their combinatorial totality principles ([Principles](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Principles.lean)), inclusions `PLS, PPP, PPAD, PPA ⊆ TFNP`, `PPAD ⊆ PPP`, and `PPAD ⊆ PPA`, and De Morgan circuit problems (`LocalOpt ∈ PLS`, `Pigeon ∈ PPP`, `EndOfLine ∈ PPAD`, `Leaf ∈ PPA`). Their [completeness](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Completeness.lean) now follows from polynomial-time construction of function-family circuit codes, preserving binary local-search costs. Develop CLS, further local search, fixed-point and equilibrium problems. |
| Logic and descriptive complexity | Building on [Fagin's theorem](Complexity/Computability/Complexity/Fagin/Converse.lean): logical characterizations of additional resource classes, fixed-point and order-invariant queries, and uniform translations between syntax, structures and algorithms. |
| Kolmogorov complexity and metacomplexity | Machine-backed descriptions/decoders and invariance, resource-bounded descriptions, MCSP variants and connections to learning, cryptography and lower bounds. Revisit deferred results through independently reviewed developments. |
| Quantum complexity | Reusable circuit/channel/measurement semantics, uniformity and approximation costs, BQP/QMA and related query, communication and interactive classes, amplification, containments and complete problems. Reuse suitable quantum foundations rather than create incompatible models. |

### Measure reuse across papers

Use a growing, source-pinned sample of papers across these areas as demanding clients, including
papers chosen after an API was designed. For each, identify the exact claims and assumptions,
reused declarations, genuinely new mathematics, missing standard dependencies, and representation
or automation friction. Promote recurring obligations into shared APIs only after demonstrating
reuse; a framework is not successful merely because its first client compiles.

Measure the whole sequence of developments: shared code plus clients, proof and interface size,
elaboration/checking cost, and remaining manual machine or encoding work. The desired trend is
less repeated foundational work per paper while preserving readable proofs and exact quantitative
statements. Novel arguments will still require novel proofs. Keep this catalogue and evidence
linked to declarations and reviewed revisions, rather than adding parallel narrative inventories.

## Community handover

Prepare the existing library as a usable successor to the original Complexitylib. Keep the
public identity **Complexitylib**: computational complexity theory built on CSLib. AI assistance
is a development method, and community participation includes mathematical review, API design,
documentation and maintenance as well as proving new theorems.

The handover covers the existing documented developments, with these acceptance criteria:

* **Auditable claims.** Check each README result against its public statement, definitions,
  assumptions, encodings and resource model. Preserve nonconstructive and conditional boundaries;
  passing Lean does not establish that a statement matches its prose or literature source.
* **Reproducible validation and review.** Run all six checks on the handover revision, retain the
  full-library axiom audit and representative clients, and record independent review with that
  revision in the PR or commit description, following
  [CONTRIBUTING.md](CONTRIBUTING.md#ai-assistance-and-review).
* **A usable contribution path.** A new contributor can find a bounded task, the relevant APIs,
  source references, validation commands and review expectations without private conversation
  history or a maintainer's agent installation.
* **An agreed handover.** Before announcing community hosting, agree the repository name,
  maintainers and merge responsibilities with CSLib Community. Verify CI and repository links
  after transfer, then point the original repository to its successor. Organizational hosting
  does not imply acceptance into upstream CSLib.

Completing every V1 port, Jukna chapter, or future resource-bound improvement is not a condition
of the handover. The work below remains available for subsequent, independently reviewed batches.

## Continuing priorities

1. **First-order reductions and projections, with machine and uniformity bridges.** Complete
   these milestones in order of their dependencies. Each requires public Lean results, a
   nonvacuous client, a theorem-index entry, and independent mathematical, API and
   statement-index reviews of the completed revision.

   - [ ] **Ordered first-order complexity, in standard terminology.** Decided 2026-10-19: the
     library's first-order complexity follows the usual convention of descriptive complexity
     [Immerman][Immerman1999]. Structures are ordered, on `{0, …, n-1}` with `n ≥ 2`, and FO
     means FO(≤, BIT). The lower bound follows
     [Proviso 1.15, p. 16](https://people.cs.umass.edu/~immerman/pub/ch0_1_2.pdf):
     the numeric constants 0 and 1 are distinct. This corrects the handoff's `n ≥ 1`.
     First-order reductions are first-order queries on lexicographically
     ordered k-tuples, and `≤_fo`, `≤_fop` and `≤_qfp` keep their standard meanings. The
     order-free `FO.Reduces`, `FO.QFReduces` and `FO.Definable` remain as a general layer of
     interpretations without built-in order. The ordered notions get their own names. Restate
     the headline results in the ordered setting: SAT, 3SAT, 3COL, IS, clique and VC
     NP-complete under first-order or quantifier-free projections; FO(≤, BIT) ⊆ L; first-order
     reductions are logspace reductions; REACH NL-complete; Circuit Value P-complete under
     first-order reductions. The order-free versions cannot reach several of these: SAT → 3SAT
     appears to need an order, and SAT-hardness without order needs an empty-structure
     hypothesis.
     The ordered query layer allows dependence on the canonical order; it does not impose
     invariance under arbitrary permutations of the input relations. Numeric predicates are
     computed from the universe size, not supplied as unverified input tables.
     **Canonical-structure prerequisite completed (#33):**
     [Ordered/Basic](Complexity/Logics/FirstOrder/Ordered/Basic.lean) supplies canonical
     `≤`/`BIT` and numeric `0`/`1`/`max` on `Fin n`, `n ≥ 2`, using native Mathlib
     terms/formulas and language sums. Input formulas, including constants and quantifiers,
     preserve truth. [Ordered/Interpretation](Complexity/Logics/FirstOrder/Ordered/Interpretation.lean)
     realizes forgetting the numeric expansion through the existing relational interpretation
     API, with an isomorphism to the input.
     **Target-constant prerequisite completed (#38):**
     [Interpretation/Constants](Complexity/Logics/FirstOrder/Interpretation/Constants.lean)
     adds finitely many formula-defined target constants, with explicit existence and uniqueness
     inside the interpreted domain, and native formula/sentence truth-preserving pullback.
     [Ordered/Constants](Complexity/Logics/FirstOrder/Ordered/Constants.lean) supplies valid
     target `0`/`1`/`max` for every canonical structure with `n ≥ 2`.
     **Full-domain tuple-order prerequisite completed (#43):**
     [Ordered/Tuple](Complexity/Logics/FirstOrder/Ordered/Tuple.lean) gives the arbitrary-base
     lexicographic rank bijection and exact first-difference order, reusing the existing
     colexicographic index by coordinate reversal.
     [Ordered/TupleInterpretation](Complexity/Logics/FirstOrder/Ordered/TupleInterpretation.lean)
     defines quantifier-free strict/weak order and the canonical full-domain constants, with
     proved unique selection and ranks `0`, `1`, `n^k - 1` for positive dimension.
     **Full-domain successor prerequisite completed (#54):**
     [Ordered/TupleSuccessor](Complexity/Logics/FirstOrder/Ordered/TupleSuccessor.lean)
     proves that the carry formula holds exactly at consecutive arbitrary-base lexicographic
     ranks, with explicit zero-dimension and maximum/no-wrap boundaries. Its generic compiler
     preserves quantifier-freeness when the supplied source successor is quantifier-free.
     The canonical `≤`/BIT instance uses a universal adjacency formula; no unconditional
     quantifier-free successor claim is made for this basis.
     **Canonical addition prerequisite completed (#64):**
     [Ordered/Addition](Complexity/Logics/FirstOrder/Ordered/Addition.lean) defines one native
     formula over `≤` and BIT whose semantics on every `Fin n`, `n ≥ 2`, is exact natural-number
     addition `x + y = z`. Out-of-range sums have no satisfying result; this is not modular
     addition. It formalizes the PLUS part of Immerman's Theorem 1.17(1), using the carry
     characterization of Proposition 1.9.
     **Canonical Bit Sum prerequisite completed (#91):**
     [Ordered/BitSum](Complexity/Logics/FirstOrder/Ordered/BitSum.lean) defines one native
     formula whose semantics on every `Fin n`, `n ≥ 2`, is `y = x.bitIndices.length`, with
     exactly one output for each input. This proves Immerman's Lemma 1.18, historically due to
     Barrington, Immerman and Straubing, using a balanced addition-tree variant of the source's
     packed running-sum proof. Eight bounded words encode all node bits; their native decoder
     uses exact shifts and fixed PLUS chains, with no assumed semantic certificate or variable
     multiplication predicate. A fixed finite disjunction handles small numerals.
     **Canonical multiplication completed (#102):**
     [Ordered/Multiplication](Complexity/Logics/FirstOrder/Ordered/Multiplication.lean) defines
     one native TIMES formula with exact ordinary-product semantics `x * y = z` on every
     canonical `Fin n`, `n ≥ 2`. Every candidate is rejected on overflow. This completes the
     PLUS/TIMES endpoint of Immerman's Theorem 1.17(1), using the proved native Bit Sum and
     a carry-table variant of the source's packed short sums. Eight words store global
     boundary carries; sixteen words store each local block. Both block endpoints agree with
     the global words, all decoders constrain high bits, and the final carry vanishes from the
     input-width bound. The witnesses fit for arbitrary universe sizes; a fixed finite branch
     handles small inputs. No multiplication relation or semantic certificate is assumed.
     **Full-tuple BIT lifting completed (#112):**
     [Ordered/TupleBit](Complexity/Logics/FirstOrder/Ordered/TupleBit.lean) supplies an actual
     native formula for every fixed dimension `k`, with exact `lexRank x`/`lexRank y` BIT
     semantics on every canonical `Fin n`, `n ≥ 2`. It handles arbitrary bases, indices larger
     than the source universe, high-index rejection and explicitly false dimension zero.
     Native affine word arithmetic, multiplication and radix conversion represent the source
     cardinality in seven digits and each tuple rank in `7k` digits. The formula witnesses a
     positive binary radix with its cube below `n`; no out-of-domain scalar or supplied numeric
     certificate is assumed. A fixed finite disjunction covers sizes two through eight.
     This proves the full-domain BIT endpoint of Immerman's Exercise 1.33(3), with no
     formula-size efficiency claim.
     **Numeric-preserving full-tuple composition completed (#121):**
     [Ordered/FullTuple](Complexity/Logics/FirstOrder/Ordered/FullTuple.lean) constructs the
     actual canonical numeric interpretation from the proved native order, BIT and constant
     formulas; clients supply only the target input-relation definitions. For `n ≥ 2` and
     positive dimension `k`, ranking is an isomorphism of the entire ordered language to
     `Fin (n^k)`, including genuine numeric constants, and native pullback preserves every
     formula and sentence. Source input vocabularies may have functions; target input
     vocabularies are relational.
     [Ordered/FullTuple/Composition](Complexity/Logics/FirstOrder/Ordered/FullTuple/Composition.lean)
     composes positive dimensions `k` and `l` with coordinate `(j,i)` mapped to `j*k+i`.
     The proved rank identity compares the flattened base-`n` tuple with the outer base-`n^k`
     tuple of inner ranks. The composite is isomorphic to the successive canonical targets,
     and all formula/sentence pullbacks agree. No full-tuple numeric certificate is assumed.
     This is the full-domain case of Immerman's Proposition 1.28 for relational intermediate
     and output input vocabularies, with Remark 1.32's canonical numerics. It does not identify
     base-`n` digits with binary strings.
     **Native ordered model checking completed (#128):**
     [FirstOrder/Ordered](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered.lean)
     proves that every fixed sentence over a finite relational input vocabulary expanded by
     canonical `0`, `1`, `max`, order and BIT has its actual encoded query language in L.
     Numeric atoms, including quantified ones, use proved native expressions; the input retains
     unary cardinality and the existing framed input tables in `tupleIndex` order. Invalid table
     shapes and sizes zero/one reject. Work space is logarithmic in the full encoded input length,
     with no combined-complexity or arbitrary-raw-word claim. This is the relational-input case
     of Immerman's Theorem 3.1. The original order-free empty-universe behavior is preserved.
     **Canonical full-tuple interpretation transducer completed (#137):**
     [Ordered/FullTuple/Encoding](Complexity/Logics/FirstOrder/Ordered/FullTuple/Encoding.lean)
     and
     [FirstOrder/Ordered/Reduction](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Reduction.lean)
     prove that every fixed canonical full-tuple interpretation between finite relational
     input vocabularies computes its encoded target structure in logarithmic space. Admissible
     sources of size `n ≥ 2` map to the canonical rank universe `Fin (n^k)` numbered by
     `lexRank`, serializing only the target input relations in `tupleIndex` order; invalid
     shapes and sizes zero and one map to a fixed malformed target outside every target query
     language. For positive dimension `k > 0`, the decoded target with its own canonical
     numerics is isomorphic to the interpreted full ordered structure preserving every
     natural rank, and `encodedMap` is a logspace many-one reduction from the pulled-back
     ordered query language to the target ordered query language. This is the full-domain
     canonical transducer of Immerman's Proposition 3.5; isomorphism-closed class-level
     reduction closure, restricted domains, projections and NL/P completeness remain open.
     **Ordered NP-to-ESO converse recovered (#173):**
     [Fagin/Ordered](Complexity/Computability/Complexity/Fagin/Ordered.lean) defines every
     arbitrary ordered query whose source-only encoding language is in NP by one ESO sentence
     over the current canonical language. It retains the fixed `Fin n` order, requires `n ≥ 2`,
     rejects malformed source tables, and imposes no permutation-invariance hypothesis.
     The existing strict-verifier/tableau construction is reused through a shared power-sentence
     lemma; the order-free characterization is unchanged. The ordered ESO-to-NP direction
     remains open.
     **Next milestones:** ordered reduction closure for structure classes, then projections and
     NL/P completeness. These remain open.
     The full-domain hypothesis matters: the paragraph after Exercise 1.33 warns that canonical
     BIT on an arbitrary definable restricted domain need not be first-order definable.
     Restricted-domain numeric preservation therefore requires its own explicit definitions
     and certificate.

   - [x] **Order-free SAT reductions.** [SAT completeness](Complexity/Computability/Complexity/Fagin/SAT.lean)
     is proved for isomorphism-closed classes in NP containing every empty structure, with a
     nonempty-input variant. Order-free 3SAT and 3COL are interreducible; SAT reduces to
     independent set on universes of at least two elements, and independent set, clique and
     vertex cover are ESO-definable. The singleton obstruction to unrestricted SAT-to-independent-set
     reducibility is proved. SAT-to-3SAT, graph-property hardness in this framework, and bridges
     to the separately encoded problems remain outstanding. These are order-free variants;
     the standard ordered completeness statements above remain open.

   - [ ] **FO reductions and projections.** The vocabulary-parametric, relativized core is
     implemented in [ProjectionFormula](Complexity/Logics/FirstOrder/ProjectionFormula.lean) and
     [Projection](Complexity/Logics/FirstOrder/Projection.lean): selection of one literal before
     quantifying over input structures, mutually exclusive numeric cases, truth-preserving
     substitution, identity/composition isomorphisms, and quantifier-free composition. The
     [graph-complement client](Complexity/Logics/FirstOrder/Projection/Graph.lean) and tests cover
     nonvacuity, empty universes, nullary relations and the failure of two-bit conjunction to be
     a projection. Quantifier-free reducibility
     ([QFReduces](Complexity/Logics/FirstOrder/Reduction/QuantifierFree.lean)) and the tactics
     `fo_qf`, `fo_iso_closed`, `fo_simp` and `fo_reduction`
     ([Tactic/FirstOrder](Complexity/Tactic/FirstOrder.lean)) are implemented, with independent
     set, clique and vertex cover as quantifier-free reducible
     [structure classes](Complexity/Logics/FirstOrder/Problems/SizedGraph.lean); `fo_reduction`
     does not yet simplify the relations of composite or higher-dimensional interpretations.
     **Still outstanding:** the classical positive-dimensional full-universe
     specialization and canonical numeric preservation, projection reducibility on finite
     structure classes, and the standard ordered machine encoding bridge. Reuse
     [FO.Interpretation](Complexity/Logics/FirstOrder/Interpretation.lean) and
     [FO.Reduces](Complexity/Logics/FirstOrder/Reduction.lean) for the semantic interfaces. State
     the canonical order/`BIT` convention on `Fin n` explicitly; the classical qfp convention
     excludes BIT ([Immerman–Landau, Definition 3.6](https://people.cs.umass.edu/~immerman/pub/mult.pdf)).
     Arbitrary quantifier-free Boolean combinations of input relations are not projections.
     [First-order model checking in L](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder.lean)
     is proved for relational FO without order or BIT, and
     [canonical ordered model checking](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered.lean)
     now includes genuine numeric constants, order and BIT for source sizes at least two.

   - [x] **Order-free interpretations as logspace reductions.** The
     [machine-certified transducer](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Reduction.lean)
     streams interpreted relation tables using tuple ranks. Every order-free interpretation
     reduction to an isomorphism-closed target induces a logspace many-one reduction of encoded
     query languages, with L/P closure. Empty universes and domains, nullary relations,
     dimension zero, and invalid parsed table shapes are handled. Canonical full-tuple ordered
     interpretations now have their own logspace transducer in
     [FirstOrder/Ordered/Reduction](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Reduction.lean);
     restricted-domain ordered transducers and isomorphism-closed class-level ordered reduction
     closure remain open.

   - [x] **Circuit Value logspace completeness.** [Circuit Value is P-complete](Complexity/Computability/Complexity/Problems/CircuitValue/Completeness.lean)
     under logarithmic-space many-one reductions, via a machine-certified tableau writer.
     The theorem covers every injective instance encoding and implies membership in L exactly
     when P equals L for every encoding. Work space excludes read-only input and write-only
     output, and correctness is required on encoded instances.

   - [x] **Monotone Circuit Value logspace completeness.**
     [Monotone Circuit Value is P-complete](Complexity/Computability/Complexity/Problems/MonotoneCircuitValue/Completeness.lean)
     under logarithmic-space many-one reductions, using a dual-rail tableau and a shared
     streaming writer. General Circuit Value reduces to it. No planarity restriction or
     first-order completeness theorem is established by this construction.

   - [ ] **Circuit Value completeness under first-order reductions.** Prove P-hardness under
     the standard ordered reduction via `REACHa → MCVP → CVP`, following
     [Immerman, Chapter 3, Theorem 3.26 and Exercise 3.28](https://people.cs.umass.edu/~immerman/book/ch3.pdf).
     Supply the alternating-logspace simulation of polynomial-time machines and the translation
     from relational circuits to `encCircuitValue`. The logspace tableau theorem above does not
     supply this stronger reduction or the ordered relational-to-machine encoding bridge.

   - [ ] **Uniform circuit families.** The current
     [NC/AC/TC hierarchies](Complexity/Computability/Circuit/Boolean/DepthClasses.lean) are
     nonuniform, and [FO model checking in AC⁰](Complexity/Computability/Circuit/Boolean/FirstOrder.lean)
     constructs nonuniform circuits over relational atomic inputs, without order/`BIT`.
     [Polynomial-time function-family compilation](Complexity/Computability/Complexity/Problems/CircuitValue/Compilation.lean)
     now certifies construction of circuit codes from encoded instances, with separately
     prescribed unary input/output widths. Its proof reuses the uniform tableau writer,
     prefix hardwiring and shared-input circuit composition; it establishes no depth bound.
     Define logspace and DLOGTIME uniformity with explicit gate-address, direct-connection and
     input encodings. Certify circuit generation and evaluation and the relevant machine-to-
     circuit simulations, preserving size, depth and construction-resource bounds. Prove
     FO with order and `BIT` equals DLOGTIME-uniform AC⁰ under explicit input-access and encoding
     conventions; an unqualified
     nonuniform class definition or simulation is insufficient.

   - [ ] **Counting-machine characterizations.** The current
     [#P/GapP definitions](Complexity/Computability/Complexity/Classes/SharpP.lean) use verifier
     witness counts and differences of such counts. The
     [occurrence-labelled terminal branch semantics](Complexity/Computability/Machines/Turing/MultiTape/Counting.lean)
     and [canonical index-certificate bijection](Complexity/Computability/Machines/Turing/MultiTape/Counting/Certificate.lean)
     now preserve accepting and rejecting counts separately, including equal-effect choices and
     early halting. Increasing a sufficient all-branches clock preserves the counts; the time
     predicate explicitly excludes stuck states (#93). The
     [actual binary checker](Complexity/Computability/Machines/Turing/MultiTape/Counting/Checker.lean)
     now has a tidy polynomial-time proof through existing finite storage and the loop calculus.
     Its exact binary/index correspondence proves
     [both terminal counts in #P and their difference in GapP](Complexity/Computability/Complexity/Classes/SharpP/Machine.lean)
     for every polynomial clock (#92). With fixed finite control, a fixed number of tapes and
     Boolean alphabet, the certificate length is `b * p(|enc a|)` for a machine-dependent fixed
     width `b > 0`; invalid codes contribute to neither verdict. This counts only branches
     halted by the clock. `HaltsWithin` additionally supplies full termination without stuck
     branches. Runtime is polynomial in the input/certificate pair, with the machine fixed,
     not uniform in a supplied machine description.
     The [binary-guess scanner](Complexity/Computability/Machines/Turing/MultiTape/Counting/Guess.lean)
     supplies one terminal branch per Boolean word of the input length, with an exact `n + 1`
     clock and singleton halt. Its shared FreeM/List execution preserves each word's multiplicity.
     The [List/native execution bridge](Complexity/Computability/Machines/Turing/MultiTape/Counting/Execution.lean),
     [singleton deterministic lift](Complexity/Computability/Machines/Turing/MultiTape/Counting/Deterministic.lean)
     and [shared-tape sequencing laws](Complexity/Computability/Machines/Turing/MultiTape/Counting/Sequential.lean)
     now preserve exact occurrence multiplicities and add actual all-branches clocks (#110).
     The sequencing bound explicitly assumes nonempty transition lists at every local view;
     the actual scanner and singleton lift satisfy this condition. This is shared-tape
     sequencing, without preparing or resetting a continuation's input. The
     [closed buffered compiler](Complexity/Computability/Machines/Turing/MultiTape/Counting/Composition.lean)
     now feeds each source output to a consumer with separately reserved blank work tapes,
     retaining source scratch and the real input head (#113). Output redirection emits into
     the buffer in each source transition; singleton deterministic preparation rewinds and
     marks it in `word.length + 4` transitions, including the empty word. Exact full-configuration
     and native count laws preserve every List occurrence. From initialized empty output,
     nonblocking components with clocks `T₀` and `T₁` have native composite clock
     `T₀ + (T₀ + 4 + T₁)`; the consumer bound must hold for every produced word.
     The [actual guess-and-verify pipeline](Complexity/Computability/Machines/Turing/MultiTape/Counting/Verifier.lean)
     now computes the witness length in unary, generates each witness once, retains the framed
     instance, and runs the singleton-lifted tidy verifier (#116). Its fixed finite machine has
     a polynomial all-branches clock in the original encoded input length, including framing,
     both buffers and workspace restoration. The output List retains one occurrence per witness,
     even when Boolean outcomes coincide. The
     [#P characterization](Complexity/Computability/Complexity/Classes/SharpP/Characterization.lean)
     combines this construction with the forward checker and preserves accepting and rejecting
     counts separately. All constructed transition tables are globally nonblocking; the halting
     contract is on encoded instances, hence all binary inputs when the encoding is `encBits`.
     The [signed construction and GapP characterization](Complexity/Computability/Complexity/Classes/SharpP/GapMachine.lean)
     now realize every difference of two #P counts by one native machine (#120, completing the
     endpoint of #106). The [one-step verdict router](Complexity/Computability/Machines/Turing/MultiTape/Counting/Verdict.lean)
     gives a successful witness one chosen-sign leaf and an unsuccessful witness one accepting
     plus one rejecting leaf. A [two-occurrence selector](Complexity/Computability/Machines/Turing/MultiTape/Counting/Alternative.lean)
     adds independently prepared families, with disjoint reserved work tapes and their original,
     possibly unequal witness lengths. Routing a verifier of clock `T` costs `T + (T + 4 + 1)`;
     combining routed clocks `S₊, S₋` costs `S₊ + S₋ + 1`. Extra clock time uses first-halt stability,
     not extra choices. Zero, odd and negative gaps are included, with no oracle channels or
     input-dependent machine advice.
     The [UP](Complexity/Computability/Complexity/Classes/UP/Machine.lean) and
     [FewP](Complexity/Computability/Complexity/Classes/FewP/Machine.lean) native iff endpoints
     now transport their accepting-count bounds through the actual parsimonious #P bridge (#131).
     Fixed finite parameters and a polynomial all-branches clock precede every encoded input;
     the ambiguity bound is one for UP and a separate polynomial in encoded input length for
     FewP. Rejecting and total branch counts are not bounded by the ambiguity polynomial.
     Duplicate accepting occurrences remain distinct, while first-halt clock padding preserves
     their multiplicities.
     [Native oracle occurrence replay](Complexity/Computability/Machines/Turing/MultiTape/Counting/Oracle/Replay.lean)
     now gives exact ordered equality between the shared FreeM run and canonical fixed-clock
     index certificates (#136), under an explicit positive uniform local-list length bound.
     It retains consumed indices, complete configurations and branch-local private oracle state;
     live cutoffs are retained, with terminal filtering and both verdict counts proved separately.
     Trace erasure recovers the ordinary shared interpretation, and the Empty-channel cases
     recover raw closed List execution and the existing terminal certificate decoder.
     This is semantic replay, without a nonblocking or halting hypothesis. A later oracle clock
     contract must be nonvacuous and uniform over admissible handlers; the generic total-PMF
     predicate cannot be instantiated blindly at an occurrence interface containing `Fin 0`.
     Closed counting clocks and characterizations are unaffected. Efficient encoded oracle
     checking, response-access costs, and native oracle-machine characterizations remain open;
     resource bounds must be uniform over admissible oracles, while correctness may specialize
     to one fixed language oracle.

2. **Complete theorem ports using the existing certificate APIs.** Extend automation when a
   concrete port is blocked or several clients repeat the same proof burden. Constructor, projection,
   lookup and composition rules should infer encodings for ordinary functional expressions.
   Test equivalent spellings and alternative encodings before adding tactic cases. Generalize
   reusable list, bounded-table, cache and nested-loop invariants where clients need them;
   callers supply the meaningful invariant, and automation handles routine encoding arithmetic.
   Use Cook–Levin and GGM as demanding regression clients. General open-program composition
   remains separate from the implemented
   [closed stateful substitution](Complexity/Computability/Probabilistic/OracleSimulation.lean).
   Extend quantitative certificates to retain separate time, workspace and output-size bounds
   through composition. Apply cumulative streaming contracts to captured iteration and nested
   loops, discharging routine encoding arithmetic automatically. Certify PRG stretching with
   seed length, round count and generator cost kept separate.

3. **Practical PCP and expander constructions.** The
   [PCP theorem](Complexity/Computability/PCP/Completeness.lean) includes certified construction
   and verification, but the fixed parameters are enormous. Develop a reasonably runnable
   construction and measure complete reductions. The
   [six-query tester](Complexity/Computability/PCP/SelectedComposition.lean) now feeds the shared
   executable composition compiler and the full reduction, with a 128-symbol output alphabet and
   a certified amplification gap of `2^-61`. The final binary verifier also encodes labels and
   repeats its check, so it does not have a six-query bound. The existing rotation certificate is
   polynomial in the number of vertices; polynomial time in the bit length of a vertex name
   remains a stronger, separate target. The [expander-walk hitting bound](Complexity/Foundations/Combinatorics/Expander/Hitting.lean)
   now gives a finite probability estimate for avoiding sets, including changing sets along the
   walk. Derive machine-level error reduction and extractor guarantees with certified seed and
   evaluation costs; the hitting estimate alone does not supply those algorithms.

4. **Reduce repeated proof bookkeeping.** Improve configuration views, tape partitions, handoff
   identities and preservation rules when they simplify multiple clients. Keep simplification
   narrowly oriented and machine transitions out of global simp. Share mathematical bookkeeping
   only with demonstrated reuse, counting helper proofs as part of the total cost.

## Remaining theorem developments

The port still includes substantial mathematical developments beyond the completed reference
results. Track these by their public theorems, rather than by source-file counts.
Jukna coverage below is an additional target beyond the V1 port:

* **Mass-production constructor runtime.** Certify runtime separately from the native gate-cost
  bounds in [Uhlig](Complexity/Computability/Circuit/Boolean/MassProduction/Uhlig.lean) and
  [fine mass production](Complexity/Computability/Circuit/Boolean/MassProduction/Fine.lean).
  The current constructions choose information sets and line menus nonconstructively.
* **Iterated-function circuits.** Port the
  [existing Lean development](https://github.com/SamuelSchlesinger/iterating-functions/blob/main/lean/README.md):
  input-time and batched iteration, navigation and hitting times, sparse-counter and
  affine-controller bounds, and hard-power counting. It already uses CSLib
  circuits and some mass-production infrastructure. The
  [functional-graph foundations](Complexity/Foundations/Combinatorics/FunctionalGraph.lean)
  (transient and cycle structure, checkpoint packing, exact distinct-power counts,
  [cycle-spectrum reduction and canonical hitting-time identities](Complexity/Foundations/Combinatorics/FunctionalGraph/Spectrum.lean),
  [min-max duality for required paths in in-forests](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestDuality.lean),
  [semantic correctness of the six-step distinguished-point procedure](Complexity/Foundations/Combinatorics/FunctionalGraph/DistinguishedPoints.lean),
  [checkpoint forests](Complexity/Foundations/Combinatorics/FunctionalGraph/CheckpointForest.lean),
  [interval labels](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestIntervals.lean),
  [compressed segments](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestSegments.lean)
  and [compressed-forest navigation](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestNavigation.lean)) and
  [native circuit iteration](Complexity/Computability/Circuit/Iteration.lean) with retained
  orbits are in place, as are the [fixed-power theorem](Complexity/Computability/Circuit/Boolean/Iteration.lean),
  its encoded and burn-in forms, the optimized square-root bounds and permutation inversion; the
  [input-time](Complexity/Computability/Circuit/Boolean/Iteration/InputTime.lean) and
  [batched iteration](Complexity/Computability/Circuit/Boolean/Iteration/Batch.lean), cycle labels,
  transient depths, additive long-time bounds,
  [compressed-forest reachability](Complexity/Computability/Circuit/Boolean/Iteration/ForestCircuits.lean),
  [hitting-time navigation](Complexity/Computability/Circuit/Boolean/Iteration/NavigationCircuits.lean),
  [complete visit-schedule circuits](Complexity/Computability/Circuit/Boolean/Iteration/VisitScheduleCircuits.lean),
  [sparse-counter navigation, visit schedules and hitting-time bounds](Complexity/Computability/Circuit/Boolean/Iteration/SparseNavigation.lean),
  [autonomous-controller / affine-payload iteration bounds](Complexity/Computability/Circuit/Boolean/Iteration/AffineController.lean),
  [universal-map simulation and hardwiring](Complexity/Computability/Circuit/Boolean/Iteration/UniversalMap.lean),
  [in-place multi-head machine bounds](Complexity/Computability/Circuit/Boolean/Iteration/InPlace.lean),
  [sequential-squaring exponent reduction](Complexity/Computability/Circuit/Boolean/Iteration/SequentialSquaring.lean),
  [hard-power counting, modular-counter lower bounds, and prime-cycle permutations](Complexity/Computability/Circuit/Boolean/Iteration/ModulusCounter.lean),
  and [batched modular-counter upper and lower bounds](Complexity/Computability/Circuit/Boolean/Iteration/CounterBatch.lean)
  are also implemented. Nonuniform circuit
  existence does not certify the preprocessing algorithm's runtime.
* **Rational hitting-list runtime.** The [rational-matrix hitting lists](Complexity/Computability/Circuit/Rational.lean)
  are ported; certify the generator's polynomial runtime, charging all arithmetic and storage
  growth. Carry over the remaining extractor developments, recording each endpoint's hypotheses.
* **Weighted threshold representations.** Complete the remaining results in
  [Threshold Circuits as Decision Trees and Finite-State Programs](https://github.com/SamuelSchlesinger/threshold-circuits).
  The [separable and bi-monotone comparison tree rectangle bounds](Complexity/Computability/DecisionTree/Separable.lean),
  [decision-tree node-count, rank, decision-list, and energy bounds for inner product](Complexity/Computability/DecisionTree/InnerProduct.lean),
  exact [inner-product and rectangle-density activity bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/InnerProduct.lean)
  (including [shifted-baseline activity](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Activity.lean)
  and [decision-tree affine leaf scores](Complexity/Computability/DecisionTree/AffineScore.lean)),
  [native scalar-capacity bound](Complexity/Computability/Circuit/Boolean/WeightedThreshold/CapacityCircuit.lean)
  (including the single-direction, direction-run, and multilevel threshold capacity corollaries),
  [mixed-activation capacity bound](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Activation.lean),
  [median-cut rectangle and cut bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Cut.lean),
  [fan-in-two component and block-excess bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Components.lean),
  [direction-menu capacity bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Menus.lean)
  (including bounded internal fan-in and bounded integer internal-weight corollaries),
  [pending-bias state simulation and input-summary / phased-cut lower bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/PendingBias.lean),
  [scalar query-activity run capacity and Cover enumerative coding bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/ScalarActivity.lean),
  and [unambiguous transcript cells and quadratic-potential unique-sink representations](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Potential.lean)
  are proved. Port v1's explicit source-reduction family.
  Further manuscript work includes universal scalar circuit synthesis,
  entropy and asymptotic activity bounds, and geometric cutting.

* **Worst-case hardness and derandomization.** The
  [worst-case-hardness implication P = BPP](Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean)
  is proved for hardness at all large lengths, by the Sudan–Trevisan–Vadhan encoding and
  Nisan–Wigderson. Remaining: the infinitely-often variant and the EXP ⊄ P/poly endpoint of
  Babai, Fortnow, Nisan and Wigderson.
* **Further PCP consequences.** Constant-factor NP-hardness of approximating Independent Set,
  Clique and Vertex Cover is [proved](Complexity/Computability/PCP/Approximation/IndependentSet.lean)
  via Karp's occurrence graph. Build the FGLSS clique-hardness reduction and amplification on the existing
  [gap-preserving reductions](Complexity/Computability/PCP/Approximation.lean) and certified PCP
  construction; retain the exact gap and reduction runtime.
* **Randomized communication and information.** The `Ω(n)` bounded-error randomized disjointness
  lower bound is [proved](Complexity/Computability/Communication/Disjointness.lean); Raz–Wigderson's
  monotone depth bound is [proved](Complexity/Computability/Circuit/Monotone/BipartiteMatching.lean)
  for bipartite matching (general graphs remain). Develop
  information complexity and its reductions to streaming and sketching lower bounds.
* **List decoding.** Extend [Sudan's Reed–Solomon list-decoding theorem](Complexity/Foundations/Data/Code/Sudan.lean)
  to Guruswami–Sudan list decoding. Keep interpolation, list-size/agreement guarantees and
  uniform decoding runtime as separate obligations.
* **Hypercontractivity and formula lower bounds.** KKL, Talagrand's inequality and Friedgut's junta
  theorem are [proved](Complexity/Foundations/BooleanAnalysis/KahnKalaiLinial.lean). Extend the existing
  [hypercontractivity results for p ≤ 2 ≤ q](Complexity/Foundations/BooleanAnalysis/Hypercontractivity.lean)
  and their Boolean-analysis applications. Continue formula lower bounds beyond the existing
  [Khrapchenko bound](Complexity/Computability/Circuit/Boolean/Khrapchenko.lean), following the
  Jukna coverage below.
* **Search and parameterized complexity.** [FNP, FP and TFNP](Complexity/Computability/Complexity/Classes/TFNP.lean)
  are defined with polynomial-time search reductions, `FP = FNP` exactly when `P = NP` is
  [proved](Complexity/Computability/Complexity/Classes/TFNP/SearchToDecision.lean), and `TFNP ⊆ FP`
  implies `NP ∩ coNP ⊆ P`. PLS, PPP, PPAD and PPA and their
  [canonical complete circuit problems](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Completeness.lean)
  are proved (#151, #168). Develop CLS and further complete search problems. Building on
  [FPT, XP and fpt-reductions](Complexity/Computability/Complexity/Parameterized.lean), prove the
  kernelization characterization of FPT and a bounded-search-tree algorithm for vertex cover
  (#152), then strongly uniform variants and the W hierarchy.
  The long-term coverage table identifies the broader class families.

The current V1 port excludes the circuitized anti-checker, hardness-magnification argument and
MINKT/MINCKT developments. The long-term canon above includes metacomplexity; those results should
return as independently scoped, reviewed developments rather than automatic legacy ports. Retain
existing checked [MCSP definitions](Complexity/Computability/MCSP/Basic.lean),
[succinct variants](Complexity/Computability/MCSP/Succinct.lean),
[Shannon bounds](Complexity/Computability/MCSP/Shannon.lean) and
[anti-checker existence](Complexity/Computability/MCSP/AntiChecker.lean).
These do not include an efficient anti-checker generator or a hardness-magnification theorem.

## Finishing the recovered developments

Complete bounded endpoints on ordinary branches, with the six checks and independent API,
correctness and statement-index reviews before closing a milestone. Retain the FO-reduction
and machine-characterization priorities above. Continue with the native NL complement theorem. The Arthur–Merlin
and hardness-amplification developments have their own prerequisites and should be split at the
following endpoints, rather than submitted as class definitions or conditional wrappers alone.

| Development | First independently useful endpoint | Remaining endpoint and dependencies |
| --- | --- | --- |
| Iterated functions M2b | Sparse-counter centralizers and signed fixed powers are in [SparseDisplacement](Complexity/Computability/Circuit/Boolean/Iteration/SparseDisplacement.lean). Interval charts, encoding/decoding, canonical labels and additive variable-time circuits are in [SparseTime](Complexity/Computability/Circuit/Boolean/Iteration/SparseTime.lean), including both charged coordinate conversions. General compressed-forest reachability, first-hitting-time navigation, and complete visit-schedule circuits are in [ForestCircuits](Complexity/Computability/Circuit/Boolean/Iteration/ForestCircuits.lean), [NavigationCircuits](Complexity/Computability/Circuit/Boolean/Iteration/NavigationCircuits.lean), and [VisitScheduleCircuits](Complexity/Computability/Circuit/Boolean/Iteration/VisitScheduleCircuits.lean), with combinatorial checkpoint forests, interval labels, nonmerging segments, and compressed-forest navigation in [CheckpointForest](Complexity/Foundations/Combinatorics/FunctionalGraph/CheckpointForest.lean), [ForestIntervals](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestIntervals.lean), [ForestSegments](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestSegments.lean) and [ForestNavigation](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestNavigation.lean), and sparse-counter specializations in [SparseNavigation](Complexity/Computability/Circuit/Boolean/Iteration/SparseNavigation.lean), [ResidueAdd](Complexity/Computability/Circuit/Boolean/Iteration/ResidueAdd.lean) and [HittingTime](Complexity/Foundations/Combinatorics/FunctionalGraph/HittingTime.lean). Autonomous controllers and affine-payload iteration bounds are in [AffineController](Complexity/Computability/Circuit/Boolean/Iteration/AffineController.lean). Universal-map simulation, product/group-action hardwiring, in-place multi-head machine bounds, and sequential-squaring reduction are in [UniversalMap](Complexity/Computability/Circuit/Boolean/Iteration/UniversalMap.lean), [InPlace](Complexity/Computability/Circuit/Boolean/Iteration/InPlace.lean) and [SequentialSquaring](Complexity/Computability/Circuit/Boolean/Iteration/SequentialSquaring.lean). Ordered circuit-description counting, modular-counter $\tilde\Omega(2^{n/2})$ power lower bounds, remainder reductions, subexponential-horizon barriers, hash-class prime-cycle permutations, and batched modular-counter upper and lower bounds are in [CircuitCounting](Complexity/Computability/Circuit/Boolean/Iteration/CircuitCounting.lean), [ModulusCounter](Complexity/Computability/Circuit/Boolean/Iteration/ModulusCounter.lean), [PrimeCycles](Complexity/Computability/Circuit/Boolean/Iteration/PrimeCycles.lean) and [CounterBatch](Complexity/Computability/Circuit/Boolean/Iteration/CounterBatch.lean). All ports follow source `c4cfa198`. | Done: all M2b iteration endpoints are proved. Nonuniform circuit existence does not certify preprocessing runtime. |
| NL = coNL | A streaming inductive-counting algorithm with soundness/completeness and logarithmic-size counters and state, reusing [InductiveCounting](Complexity/Foundations/Relation/InductiveCounting.lean). Its certificates must be checked without retaining a whole reachable set. | Compile the procedure to the native NTM model, certify every computation prefix's logspace bound, and prove complement closure. Explicitly handle configuration enumeration and input access. `NL` follows the textbook convention that every branch halts (`DecidesInSpace`), so the complement machine must halt on every branch, for instance by bounding its loops with logarithmic counters. Proving that logspace recognizers whose branches may loop (`RecognizesInSpace`) recognize only problems in `NL` is a separate clock-construction item; general space-constructible Savitch bounds are separate. |
| Arthur–Merlin | Done: verifier-based MA and AM, error reduction, NP ∪ BPP ⊆ MA ⊆ AM ⊆ Π₂ᵖ, MA ⊆ Σ₂ᵖ ∩ Π₂ᵖ and MA ⊆ SBP ([ArthurMerlin](Complexity/Computability/Complexity/Classes/ArthurMerlin.lean)); the [set lower bound protocol and SBP ⊆ AM](Complexity/Computability/Complexity/Classes/ArthurMerlin/SetLowerBound.lean), [public-coin GNI in AM](Complexity/Computability/Complexity/Classes/ArthurMerlin/GraphNonIsomorphism.lean), and [PH = Σ₂ᵖ from coNP ⊆ AM for every encoding](Complexity/Computability/Complexity/Classes/ArthurMerlin/Collapse.lean). | Interactive-machine characterizations, AM[k] = AM and private-to-public-coin transformations remain separate endpoints. |
| Worst-case-hardness derandomization | Done for eventual hardness: [P = BPP from 2^(γn) De Morgan circuit hardness of a language in E](Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean), with the explicit field, the encoding in E and the parameter schedule certified. | The infinitely-often variant; the EXP-not-in-P/poly endpoint of Babai, Fortnow, Nisan and Wigderson. |

Do not mark the last three rows complete from an abstract algorithm, a class definition, or an
assumed reconstruction theorem: their machine/resource and quantitative conclusions are part of
acceptance. The theorem index records completed statements with their assumptions and scope.

## Jukna coverage

Formalize the established theorems, lemmas, constructions and exercise results throughout
[Jukna's *Boolean Function Complexity: Advances and Frontiers* (2012)](https://web.vu.lt/mif/s.jukna/boolean/index.html),
using the author's [errata](https://web.vu.lt/mif/s.jukna/boolean/misprints-BFC.html).
The target is all useful established results and constructions, including supporting lemmas and
worthwhile exercises. Open problems are separate research opportunities, not completion
requirements. Reuse Mathlib and CSLib for the supporting mathematics.

Complete and review developments individually; book-wide coverage is a long-term program, not
a prerequisite for using the library. Organize modules by mathematical subject rather than book
chapter.

The [almost-injective binary linear map](Complexity/Probability/BitString/LinearHash/Collisions.lean)
implements Lemma 1.17, including its unordered-pair collision bound and an injective-map
corollary. Its matrix selection is existential; the partial-function circuit upper bounds that
use it remain outstanding.

This initial map follows the [contents](https://web.vu.lt/mif/s.jukna/boolean/TOC.pdf).
The linked modules are starting points, not evidence of complete chapter coverage. Audit exact
statements and hypotheses against each numbered result, including circuit bases, cost conventions,
uniformity, explicitness and quantitative strength; a citation or related theorem is insufficient.

| Chapters | Existing entry points | Next coverage work |
| --- | --- | --- |
| 1–2: foundations and Boolean analysis | [Circuit hierarchy](Complexity/Computability/Circuit/Boolean/Hierarchy.lean), [Shannon synthesis](Complexity/Computability/Circuit/Boolean/ShannonSynthesis.lean), [Fourier analysis](Complexity/Foundations/BooleanAnalysis/Fourier.lean) | Audit counting, graph complexity, degree and approximation results. |
| 3–5: communication | [Protocols](Complexity/Computability/Communication/Protocol.lean), [Karchmer–Wigderson](Complexity/Computability/Communication/KarchmerWigderson.lean) | Complete matrix, randomized and multiparty results. |
| 6–10: formulas and circuits | [Spira](Complexity/Computability/Circuit/Boolean/Spira.lean), [Khrapchenko](Complexity/Computability/Circuit/Boolean/Khrapchenko.lean), [monotone clique](Complexity/Computability/Circuit/Monotone/Clique/LowerBound.lean) | Audit remaining formula and monotone bounds; develop span programs and negation complexity. |
| 11–13: depth restrictions and general gates | [Håstad](Complexity/Computability/Circuit/Boolean/Hastad.lean), [Smolensky](Complexity/Computability/Circuit/Boolean/Smolensky.lean), [symmetric gates](Complexity/Computability/Circuit/Boolean/ShallowSymmetric.lean) | Audit depth-three, threshold, entropy, wire and linear-operator bounds. |
| 14–17: trees and branching programs | [Decision-tree certificates](Complexity/Computability/DecisionTree/Certificate.lean), [Barrington](Complexity/Computability/Circuit/Boolean/BarringtonClass.lean) | Complete bounded-read and bounded-time lower bounds and remaining tree results. |
| 18–19: proof complexity | [Resolution size–width](Complexity/Logics/Propositional/Resolution/SizeWidth.lean), [tree-like resolution](Complexity/Logics/Propositional/Resolution/TreeLike.lean), [Cook–Reckhow systems](Complexity/Logics/Propositional/ProofSystem.lean) | Develop pigeonhole/Tseitin lower bounds, proof space and cutting-plane proofs. |
| 20: barriers and further methods | [Fusion API](Complexity/Computability/Circuit/Fusion/Basic.lean), [Nisan–Wigderson core](Complexity/Computability/Kolmogorov/NisanWigderson.lean) | Match the book's generator, natural-proof, fusion and indirect lower-bound results. |
| Appendix A: mathematical prerequisites | Mathlib and `Complexity/Foundations/` | Reuse existing statements and fill dependencies as clients require them. |

## Approximation and Fusion milestones

These milestones extend the existing [semifilter covers](Complexity/Computability/Circuit/Fusion/Semifilter.lean)
and [cyclic characterization](Complexity/Computability/Circuit/Fusion/Cyclic/Compiler.lean)
using [Oliveira's approximation-method notes (2018)](https://www.dcs.warwick.ac.uk/~igorcarb/documents/papers/approximation-method-fusion-note.pdf)
and [Cavalar–Oliveira, ECCC TR25-033 (2025)](https://eccc.weizmann.ac.il/report/2025/033/).
Credit the earlier results of Razborov, Karchmer, Wigderson, and Nakayama–Maruoka where used.
The issues carry ownership and review history. Circuit bounds use the native basis with free
constants and binary unions; the theorem index records the precise scope of each result.

| Milestone | Proved result and scope |
| --- | --- |
| [Quadratic completeness #12](https://github.com/SamuelSchlesinger/complexitylib2/issues/12) | **Proved:** [quadratic compiler](Complexity/Computability/Circuit/Fusion/Quadratic.lean) uses exactly `t²` AND gates for a `t`-pair cover and gives the minimum source-cost bound, including arbitrary carriers, empty input families and trivial targets (TR25-033, Theorem 24; PR #19). |
| [Approximation bridge and counting barrier #13](https://github.com/SamuelSchlesinger/complexitylib2/issues/13) | **Proved:** [exact consistency and local observation errors](Complexity/Computability/Circuit/Fusion/Consistency.lean), the [fixed pair sampler, weighted averaging and `8n + 8` certificate barrier](Complexity/Computability/Circuit/Fusion/Sampling.lean) (Oliveira, Lemma 3 and Theorem 6; PRs #20 and #22). This is a local observation bridge, not a formal equivalence of all approximation models. |
| [Graph transfer and inequality #14](https://github.com/SamuelSchlesinger/complexitylib2/issues/14) | **Proved:** [row/column-to-literal transfer](Complexity/Computability/Circuit/Fusion/Graph.lean) for any admissible witness subclass, including semi-ultrafilters, and [exact canonical/full cover and intersection cost `n`](Complexity/Computability/Circuit/Fusion/Graph/Inequality.lean) for inequality on `2^n` vertices per side (TR25-033, Lemmas 39/48 and Proposition 40; PR #21). |
| [Random graph covers #15](https://github.com/SamuelSchlesinger/complexitylib2/issues/15) | **Proved:** [finite inclusion-pattern counting](Complexity/Computability/Circuit/Fusion/Encoding.lean) and [random graph hardness](Complexity/Computability/Circuit/Fusion/Graph/Random.lean): for `N ≥ 16`, probability at least `1 - 2⁻ᴺ` of `⌊N/16⌋ < ρ(G) ≤ N` under the uniform distribution on all labelled bipartite graphs (TR25-033, Theorem 37; PR #23). |
| [Conondeterministic complexity #16](https://github.com/SamuelSchlesinger/complexitylib2/issues/16) | **Proved:** [universal-verifier cover extraction](Complexity/Computability/Circuit/Fusion/Conondeterministic.lean) and the [converse compiler](Complexity/Computability/Circuit/Fusion/Converse.lean) give `ρ_ultra(f) ≤ C_forall,AND(f) ≤ 5ρ_ultra(f)`. The [extended-natural circuit measure](Complexity/Computability/Circuit/Boolean/Conondeterministic.lean) minimizes over all finite auxiliary counts and verifiers; a `t`-pair cover gives exactly `3t` auxiliary bits and `5t` AND gates, including zero and constant cases (TR25-033, Theorem 45, credited there to Karchmer; PRs #25 and #28). The explicit factor five comes from the formalized certificate construction. The graph transfer above specializes to semi-ultrafilters (Lemma 48). |

Keep the source models explicit: constants, zero-gate constructions, exact versus one-sided
literal consistency, and AND versus total gate costs. The counting barrier requires a capacity
bound over every pair; it does not apply to a bound restricted to a particular circuit's gate
pairs and is not an upper bound on unrestricted cover complexity. The sampling and reconstruction
lemmas are proved, not assumed. These are
formalizations of established results, not claims of new explicit superlinear circuit lower bounds.

## Machine-class milestones

Polynomial efficiency is sufficient for many reductions, but does not establish tight time or
space bounds. Further class-level work needs resource certificates for the actual algorithms:

* Tree Evaluation: the [Cook–Mertz machine](Complexity/Computability/TreeEval/Space.lean)
  has a proved parameterized space bound on valid encoded instances and an
  `O(log n · log log n)` input-size space corollary on nontrivial instances (`1 ≤ ℓ` and
  `1 ≤ H`); malformed-input handling and the refined `O(ℓ + H log(ℓ + 2))` parameter bound
  remain outstanding;
* the space hierarchy, which needs a space-budgeted universal simulation; the
  [time hierarchy](Complexity/Computability/Complexity/Classes/Hierarchy/Time.lean) and `P ⊊ EXP`
  are proved with a polynomial simulation gap, so a tight tape-indexed hierarchy needs a
  linear-overhead simulation and an `f log f` time hierarchy the corresponding simulation bound;
* Reingold's theorem: [USTCON ∈ L and SL = L](Complexity/Computability/Complexity/Classes/LogSpace/USTCON.lean)
  are proved for the adjacency-matrix encoding (with `SL` defined by logspace many-one reducibility
  to `USTCON`, completeness of `USTCON` for `SL` and `L`, and the unary-header injectivity lemma
  shared with `TreeEval` in [List/Basic.lean](Complexity/Foundations/Data/List/Basic.lean)); a
  symmetric-Turing-machine model of `SL` and an edge-list variant of `USTCON` by a logspace
  reduction remain;
* `NL = coNL`, building on logspace composition, `NL ⊆ P` and Savitch; `PH ⊆ PSPACE` is
  already proved by evaluating quantified predicates in
  [polynomial space](Complexity/Computability/Complexity/Classes/Inclusions.lean);
* alternating time/space classes and bounded-alternation characterizations of `PH`, beyond the
  proved [AP = PSPACE](Complexity/Computability/Complexity/Classes/Alternation/Savitch.lean);
* the ordered logarithmic-space FO encoding bridge and first-order Circuit Value completeness in the
  [first continuing priority](#continuing-priorities), together with uniform circuit-family and
  counting-machine characterizations;
* RAM models: the [bounded-word RAM](Complexity/Computability/WordRAM/Defs.lean), adapted from the
  Lean formalization accompanying the tromino undecidability paper, has [linear and polynomial
  instruction bounds](Complexity/Computability/WordRAM/Time.lean) uniform over all fitting widths
  above a logarithmic lower threshold,
  [structured programs](Complexity/Computability/WordRAM/Structured.lean) compiling with exact
  instruction counts, [allocation and arrays](Complexity/Computability/WordRAM/Allocation.lean) and
  a [linear-time element-distinctness client](Complexity/Algorithms/WordRAM/ElementDistinctness.lean)
  whose promised inputs provably fit at that threshold. The generic classes alone do not supply
  this input-fit guarantee. The [additive-memory compiler](Complexity/Computability/WordRAM/RAM.lean)
  now forward-simulates successful fitting runs in the existing
  [`Cslib.RAM`](Complexity/Computability/RAM/Defs.lean) with logarithmic cost
  `8 * (bitLength (r + 5) + 1) * (t + 1) * (w + 1)`, including its two register initializers
  and final output copy/jump, from an explicitly supplied padded input. A separate
  [input preparer](Complexity/Computability/RAM/Input.lean) now charges the backward relocation and
  prefix clearing from five zero scratch cells followed by a length header and the input words.
  It reaches the exact padded register state before arbitrary appended code in logarithmic cost
  `(24 + R) * (bitLength (R + 5) + 2) * (input.length + 1) * b` for `R ≥ 5`, given bit-length
  bound `b` on the header and words; external input installation remains uncharged. The
  [composed bridge](Complexity/Computability/WordRAM/RAMInput.lean) now includes that preparation
  in `C_r * (t + input.length + 1) * (w + 1)`, for an explicit constant depending only on the
  source register count. The same fixed compiler gives a
  [bounded-universe element-distinctness decider](Complexity/Algorithms/WordRAM/ElementDistinctnessRAM.lean)
  of logarithmic RAM cost `2735 * (n + 1) * (Nat.log 2 (n + 1) + 1)`, including preparation;
  the separately supplied padded-input bound is `2448 * (n + 1) * (Nat.log 2 (n + 1) + 1)`.
  These statements retain the explicit preloaded length-bearing convention and entry promise.
  Wider-fragment and Turing-machine simulations remain open. The unrestricted converse
  from prescribed-width to uniform decision is false: width can supply instance-dependent advice.
  A useful conversion must specify an input-fit guarantee, a size-based width-selection procedure
  with computability and resource bounds, encoding conventions, and simulation overhead. Transfer
  of cell-probe lower bounds and the source's Horn-SAT, 2SAT, matching and domino-tiling clients
  also remain open;
* single-tape simulation and machine-backed Kolmogorov and Nisan–Wigderson decoding results;
* concrete list-decodable codes for Nisan–Wigderson and order-invariant descriptive-complexity
  queries.

Check upstream work before starting these developments. The existing combinatorial or
machine-relative cores do not by themselves establish the missing uniform resource guarantees.

## Candidate proof improvements

These are experiments to validate, not claimed savings:

* Share simultaneous-good-event and union-bound arguments between Gaussian layout clients.
* Simplify `PairReady` and `clearedCfg` composition/preservation in tidy normal form without
  unfolding machine transitions globally.
* Factor indicator-expectation identities from PCP's second-moment calculation and recurring
  cardinality/logarithm conversions only when a second client benefits.

Judge changes on client readability, total proof burden and elaboration cost. Count proof fields
and helper APIs, and distinguish source-line counts from runtime or proof-term size.
[scripts/proof_lengths.py](scripts/proof_lengths.py) supports comparison against a Git revision.

Past measurements, reviews and proposals remain in the
[historical roadmap](https://github.com/SamuelSchlesinger/complexitylib2/blob/c88395234575284c2fe1e9e3619ead1c2f6fd7f3/ROADMAP.md).
