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
The next counting milestones remain the nondeterministic-machine characterizations of
`#P` and `GapP`, and machine characterizations of `UP` and polynomially bounded ambiguity;
none is implied by the verifier definitions. SPP, FewP, fixed-modulus ModP, coUP and coC=P
now have verifier-based definitions and basic closure/containment developments. Extend these
with stronger fewness containments, counting reductions and oracle results, preserving exact
multiplicities when required. The current modular Boolean closures require a prime modulus. The complementary modular class is
implemented, with equality to ModP for prime moduli. US, coDP, the finite Boolean
hierarchy, WPP and LWPP now have definitions and elementary containments/closures.
The binary-output FP-to-#P/GapP bridge is available. Remaining extensions include
US/Unique-SAT completeness, stronger Boolean-hierarchy closure and collapse results,
LWPP reduction closure and multiple-target robustness, and WPP/LWPP oracle lowness.
SBP and AWPP now have verifier-based definitions, the elementary NP/BPP/SPP-to-PP
containments, many-one reduction closure, SBP union closure and AWPP complement closure.
Remaining approximate-counting milestones include MA ⊆ SBP ⊆ AM, AWPP amplification,
AWPP union/intersection closure, WPP ⊆ AWPP and AWPP PP-lowness.
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
| Interactive and probabilistic proofs | [IP ⊆ PSPACE](Complexity/Computability/Complexity/Classes/IP/PSPACE.lean) is proved for the strict polynomial-time, private-coin verifier model. Prove the converse through sumcheck and arithmetization; develop Arthur–Merlin classes, public/private-coin transformations, multiprover systems, zero knowledge and simulation. Reuse the existing PCP and probabilistic foundations. |
| Boolean circuits and parallel computation | Complete the [Jukna coverage](#jukna-coverage), uniform/nonuniform NC/AC/TC and related classes, circuit-to-machine bridges, algorithm-to-lower-bound arguments and barriers such as natural proofs and algebrization. |
| Algebraic and arithmetic complexity | Build on [VP and p-projections](Complexity/Computability/Circuit/Arithmetic/VP.lean), [VNP and VP ⊆ VNP](Complexity/Computability/Circuit/Arithmetic/VNP.lean), and [determinant ∈ VP](Complexity/Computability/Circuit/Arithmetic/Determinant.lean) over commutative rings. Prove permanent VNP-completeness with its characteristic assumptions, extend formula/branching-program models, identity testing, hitting sets, tensor and rank methods, and certify uniform construction costs separately from gate counts. |
| Approximation and constraint satisfaction | Gap and approximation-preserving reductions, APX/PTAS/FPTAS, canonical inapproximability consequences of PCP, CSP classifications and relaxation gaps. State assumptions such as the Unique Games Conjecture explicitly. |
| Pseudorandomness and coding | Hardness versus randomness, space-bounded generators, extractors/condensers, limited independence, explicit expanders, and list/local decoding. Separate finite combinatorial guarantees from uniform construction and decoding costs. |
| Complexity-theoretic cryptography | Extend the existing OWF/PRG/PRF results with reusable adaptive reductions, commitments, zero knowledge, hard-core and hardness-amplification methods, and connections to learning and average-case hardness. |
| Communication, queries and data structures | Randomized and multiparty protocols, discrepancy and information complexity, direct-sum/product results, lifting theorems, and reductions to streaming, sketching and cell-probe lower bounds. Reuse upstream query models. |
| Proof complexity | Build on [Cook–Reckhow systems and simulations](Complexity/Logics/Propositional/ProofSystem.lean), including the polynomially bounded-system characterization of NP = coNP, the [resolution size–width tradeoff](Complexity/Logics/Propositional/Resolution/SizeWidth.lean) and [tree-like resolution/DPLL search-tree certificates](Complexity/Logics/Propositional/Resolution/TreeLike.lean). Extend proof-space and pigeonhole/Tseitin lower bounds, Frege, cutting planes, polynomial calculus and sum-of-squares. The certificate correspondence does not certify a DPLL solver's runtime. |
| Average-case complexity and learning | Distributional problems and reductions, samplability, average-to-worst-case connections, PAC/agnostic/SQ learning, learning lower bounds, compression and refutation. Existing cryptographic learners are starting points, not coverage of learning theory. |
| Property and distribution testing | Distance and access models, one/two-sided and tolerant testing, query/sample bounds, canonical graph/algebraic/distribution testers and lower bounds. |
| Fine-grained and parameterized complexity | Fine-grained reductions and consequences conditional on ETH/SETH and other named hypotheses; FPT/XP, W/A hierarchies, kernelization, parameter-preserving reductions and lower bounds. |
| Total search and computational games | FNP/TFNP and canonical subclasses such as PLS, PPAD, PPA, PPP and CLS; local search, fixed-point and equilibrium problems, with explicit totality and solution-preserving reductions. |
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

   - [ ] **FO reductions and projections.** The vocabulary-parametric, relativized core is
     implemented in [ProjectionFormula](Complexity/Logics/FirstOrder/ProjectionFormula.lean) and
     [Projection](Complexity/Logics/FirstOrder/Projection.lean): selection of one literal before
     quantifying over input structures, mutually exclusive numeric cases, truth-preserving
     substitution, identity/composition isomorphisms, and quantifier-free composition. The
     [graph-complement client](Complexity/Logics/FirstOrder/Projection/Graph.lean) and tests cover
     nonvacuity, empty universes, nullary relations and the failure of two-bit conjunction to be
     a projection. **Still outstanding:** the classical positive-dimensional full-universe
     specialization and canonical numeric preservation, projection reducibility on finite
     structure classes, and the machine-certified encoding bridge described below. Reuse
     [FO.Interpretation](Complexity/Logics/FirstOrder/Interpretation.lean) and
     [FO.Reduces](Complexity/Logics/FirstOrder/Reduction.lean) for the semantic interfaces. State
     the canonical order/`BIT` convention on `Fin n` explicitly; the classical qfp convention
     excludes BIT ([Immerman–Landau, Definition 3.6](https://people.cs.umass.edu/~immerman/pub/mult.pdf)).
     Arbitrary quantifier-free Boolean combinations of input relations are not projections. Connect these
     maps to the [finite-structure encoding](Complexity/Logics/FirstOrder/Encoding.lean) by a
     machine-certified logarithmic-space transducer. Account for tuple enumeration, relation
     access, output representation, malformed inputs and the empty structure; the semantic APIs
     alone do not provide this resource bound.

   - [ ] **Circuit Value completeness.** Membership in `P` is already
     [proved](Complexity/Computability/Complexity/Problems/CircuitValue.lean). Prove `P`-hardness
     under the selected FO reduction via `REACHa → MCVP → CVP`, following
     [Immerman, Chapter 3, Theorem 3.26 and Exercise 3.28](https://people.cs.umass.edu/~immerman/book/ch3.pdf).
     Supply the alternating-logspace simulation of polynomial-time machines and the translation
     from relational circuits to `encCircuitValue`. Combine the FO-to-machine bridge above with
     `CircuitValue.mem_P` to obtain standard logarithmic-space many-one `P`-completeness.
     Neither the reduction chain nor that bridge follows from having `FO.Reduces`;
     polynomial-time reductions alone do not establish the desired completeness theorem.

   - [ ] **Uniform circuit families.** The current
     [NC/AC/TC hierarchies](Complexity/Computability/Circuit/Boolean/DepthClasses.lean) are
     nonuniform, and [FO model checking in AC⁰](Complexity/Computability/Circuit/Boolean/FirstOrder.lean)
     constructs nonuniform circuits over relational atomic inputs, without order/`BIT`.
     Define logspace and DLOGTIME uniformity with explicit gate-address, direct-connection and
     input encodings. Certify circuit generation and evaluation and the relevant machine-to-
     circuit simulations, preserving size, depth and construction-resource bounds. Prove
     FO with order and `BIT` equals DLOGTIME-uniform AC⁰ under explicit input-access and encoding
     conventions; an unqualified
     nonuniform class definition or simulation is insufficient.

   - [ ] **Counting-machine characterizations.** The current
     [#P/GapP definitions](Complexity/Computability/Complexity/Classes/SharpP.lean) use verifier
     witness counts and differences of such counts. Prove both directions of their equivalence
     with polynomial-time NTMs counting accepting branches and accepting-minus-rejecting branches,
     respectively. Reuse the
     [NP machine/verifier bridge](Complexity/Computability/Complexity/Classes/NP/Nondeterministic.lean),
     but preserve exact path multiplicities through choices, halting and padding. Do not collapse
     distinct nondeterministic branches with the same successor; existential witness equivalence
     is insufficient.

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
  [sharp mass production](Complexity/Computability/Circuit/Boolean/MassProduction/Sharp.lean).
  The current constructions choose information sets and line menus nonconstructively.
* **Iterated-function circuits.** Port the
  [existing Lean development](https://github.com/SamuelSchlesinger/iterating-functions/blob/main/lean/README.md):
  input-time and batched iteration, navigation and hitting times, sparse-counter and
  affine-controller bounds, and hard-power counting. It already uses CSLib
  circuits and some mass-production infrastructure. The
  [functional-graph foundations](Complexity/Foundations/Combinatorics/FunctionalGraph.lean)
  (transient and cycle structure, checkpoint packing, exact distinct-power counts) and
  [native circuit iteration](Complexity/Computability/Circuit/Iteration.lean) with retained
  orbits are in place, as are the [fixed-power theorem](Complexity/Computability/Circuit/Boolean/Iteration.lean),
  its encoded and burn-in forms, the optimized square-root bounds and permutation inversion; the
  [input-time](Complexity/Computability/Circuit/Boolean/Iteration/InputTime.lean) and
  [batched iteration](Complexity/Computability/Circuit/Boolean/Iteration/Batch.lean), cycle labels,
  transient depths and additive long-time bounds are also implemented. The sparse-counter
  continuation and later controller/counting developments are listed below. Nonuniform circuit
  existence does not certify the preprocessing algorithm's runtime.
* **Rational hitting-list runtime.** The [rational-matrix hitting lists](Complexity/Computability/Circuit/Rational.lean)
  are ported; certify the generator's polynomial runtime, charging all arithmetic and storage
  growth. Carry over the remaining extractor developments, recording each endpoint's hypotheses.
* **Weighted threshold representations.** Complete the remaining results in
  [Threshold Circuits as Decision Trees and Finite-State Programs](https://github.com/SamuelSchlesinger/threshold-circuits).
  The exact [inner-product activity bound](Complexity/Computability/Circuit/Boolean/WeightedThreshold/InnerProduct.lean)
  and [native scalar-capacity bound](Complexity/Computability/Circuit/Boolean/WeightedThreshold/CapacityCircuit.lean)
  are proved. Port v1's remaining gate-count consequences and explicit source-reduction family.
  Further manuscript work includes scalar enumerative coding, pending-bias simulation,
  entropy and asymptotic activity bounds, geometric cutting, integer-summary counting,
  and quadratic-potential representations.

* **Worst-case hardness and derandomization.** The
  [uniform average-case-hardness implication P = BPP](Complexity/Computability/Complexity/Classes/BPP/Derandomization.lean)
  is proved. Complete the worst-case-to-average-case amplification needed to obtain this
  conclusion from exponential worst-case circuit hardness in `E`.
* **Further PCP consequences.** Build the FGLSS clique-hardness reduction on the existing
  [gap-preserving reductions](Complexity/Computability/PCP/Approximation.lean) and certified PCP
  construction; retain the exact gap and reduction runtime.
* **Randomized communication and information.** Prove the `Ω(n)` bounded-error randomized
  disjointness lower bound, building on [Yao's minimax principle](Complexity/Computability/Communication/Distributional.lean)
  and [corruption bounds](Complexity/Computability/Communication/Corruption.lean). Develop
  information complexity and its reductions to streaming and sketching lower bounds.
* **List decoding.** Extend [Sudan's Reed–Solomon list-decoding theorem](Complexity/Foundations/Data/Code/Sudan.lean)
  to Guruswami–Sudan list decoding. Keep interpolation, list-size/agreement guarantees and
  uniform decoding runtime as separate obligations.
* **Hypercontractivity and formula lower bounds.** Extend the existing
  [hypercontractivity results for p ≤ 2 ≤ q](Complexity/Foundations/BooleanAnalysis/Hypercontractivity.lean)
  and their Boolean-analysis applications. Continue formula lower bounds beyond the existing
  [Khrapchenko bound](Complexity/Computability/Circuit/Boolean/Khrapchenko.lean), following the
  Jukna coverage below.
* **Search and parameterized complexity.** Develop TFNP and its subclasses with explicit totality
  and solution-preserving reductions, and FPT/XP, parameterized reductions and kernelization.
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
and machine-characterization priorities above. Continue with sparse-counter
navigation from the existing source proofs; then close the native NL complement theorem. The Arthur–Merlin
and hardness-amplification developments have their own prerequisites and should be split at the
following endpoints, rather than submitted as class definitions or conditional wrappers alone.

| Development | First independently useful endpoint | Remaining endpoint and dependencies |
| --- | --- | --- |
| Iterated functions M2b | Sparse-counter centralizers and signed fixed powers are in [SparseDisplacement](Complexity/Computability/Circuit/Boolean/Iteration/SparseDisplacement.lean). Interval charts, encoding/decoding, canonical labels and additive variable-time circuits are in [SparseTime](Complexity/Computability/Circuit/Boolean/Iteration/SparseTime.lean), including both charged coordinate conversions. Both ports follow source `c4cfa198`. | Port sparse-counter navigation, visit schedules and hitting-time bounds using the new charts. General input-time and batch results already exist. Affine controllers and hard-power counting are later milestones; these results do not close the whole M2b scope. |
| NL = coNL | A streaming inductive-counting algorithm with soundness/completeness and logarithmic-size counters and state, reusing [InductiveCounting](Complexity/Foundations/Relation/InductiveCounting.lean). Its certificates must be checked without retaining a whole reachable set. | Compile the procedure to the native NTM model, certify every computation prefix's logspace bound, and prove complement closure. Explicitly handle configuration enumeration, input access and the existing potentially nonhalting-branch convention. Close the clocked/textbook-model bridge; general space-constructible Savitch bounds are separate. |
| Arthur–Merlin | Native polynomial-time MA and AM verifier semantics, error reduction and the basic NP/BPP/MA/AM inclusions, with concrete protocols. | Prove AM containment in the second universal PH level; implement the set-size lower-bound protocol and derive GNI in AM. Existing private-coin GNI in IP does not provide the public-coin protocol. |
| Worst-case-hardness derandomization | A quantitative worst-case-to-average-case reconstruction theorem, with explicit input-length and circuit-size losses and an efficiently evaluable amplified function. Select and justify a complete amplification route; the existing small-error line decoder is not a local list decoder. | Preserve membership in E, instantiate the existing average-case-hardness derandomization theorem and prove the worst-case-hardness implication P = BPP. Specify eventual versus infinitely-often hardness. The EXP-not-in-P/poly BFNW endpoint is a later milestone. |

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

## Machine-class milestones

Polynomial efficiency is sufficient for many reductions, but does not establish tight time or
space bounds. Further class-level work needs resource certificates for the actual algorithms:

* the space hierarchy, which needs a space-budgeted universal simulation; the
  [time hierarchy](Complexity/Computability/Complexity/Classes/Hierarchy/Time.lean) and `P ⊊ EXP`
  are proved with a polynomial simulation gap, so a tight tape-indexed hierarchy needs a
  linear-overhead simulation and an `f log f` time hierarchy the corresponding simulation bound;
* `NL = coNL`, building on logspace composition, `NL ⊆ P` and Savitch; `PH ⊆ PSPACE` is
  already proved by evaluating quantified predicates in
  [polynomial space](Complexity/Computability/Complexity/Classes/Inclusions.lean);
* alternating time/space classes and bounded-alternation characterizations of `PH`, beyond the
  proved [AP = PSPACE](Complexity/Computability/Complexity/Classes/Alternation/Savitch.lean);
* the logarithmic-space FO encoding bridge and Circuit Value completeness in the
  [first continuing priority](#continuing-priorities), together with uniform circuit-family and
  counting-machine characterizations;
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
