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
now have verifier-based definitions and basic closure/containment developments. FewP ⊆ SPP and
PH ⊆ P^#P = P^PP are proved, with uniform simulations under the function-bit oracle convention.
Extend these with counting reductions and further oracle results, preserving exact
multiplicities when required. The current modular Boolean closures require a prime modulus. The complementary modular class is
implemented, with equality to ModP for prime moduli. US, coDP, the finite Boolean
hierarchy, WPP and LWPP now have definitions, elementary containments/closures, LWPP many-one
reduction closure, unary-indexed target normalization, and full one-sided polynomial-family
multiple-target robustness: Poly-WPP = WPP and Poly-LWPP = LWPP, and the full two-sided
(Poly,Poly)-WPP/WPP and (Poly,Poly)-LWPP/LWPP characterizations with disjoint uniformly computed
accepting/rejecting binary target lists. Original targets may be zero; neither index must be
computable ([WPP.TwoSided](Complexity/Computability/Complexity/Classes/WPP/TwoSided.lean)).
The binary-output FP-to-#P/GapP bridge is available. Parsimonious Cook–Levin gives #P-completeness of #SAT and SAT-based complete problems for ⊕P, US, ModₖP/coModₖP, PP (threshold #SAT) and C=P/coC=P ([CountingSAT](Complexity/Computability/Complexity/Problems/CountingSAT.lean)). Remaining extensions include
MAJSAT and permanent completeness, stronger Boolean-hierarchy closure and collapse results,
and WPP/LWPP oracle lowness.
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
provide a counting-algebra foundation for future oracle simulations; AWPP PP-lowness
remains an approximate-counting milestone.
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
| Fine-grained and parameterized complexity | Under ETH, 3-coloring, independent set, vertex cover and Hamiltonian cycle and path have no 2^{o(\|V\|+\|E\|)} algorithms and clique none in 2^{o(\|V\|)} ([GraphProblems](Complexity/Computability/Complexity/FineGrained/GraphProblems.lean)); the Hamiltonian bounds (directed and undirected) use linear-size diamond reductions. Further fine-grained reductions and consequences conditional on ETH/SETH and other named hypotheses; FPT/XP, W/A hierarchies, kernelization, parameter-preserving reductions and lower bounds. |
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
     **Next milestones:** successor and arbitrary-base BIT lifting; numeric-preserving
     composition; the ordered logspace encoding bridge; then projections and NL/P completeness.
     Numeric interpretations must preserve
     canonical BIT for arbitrary base `n`, and composition must preserve that certificate
     (Immerman, Remark 1.32). A general constructor supplying numeric definitions on the full
     tuple universe in every dimension still needs Exercise 1.33(3); base-`n` tuples
     cannot simply be identified with concatenated binary strings. The full-domain hypothesis
     matters: the paragraph after Exercise 1.33 warns that canonical BIT on an arbitrary
     definable restricted domain need not be first-order definable. Restricted-domain numeric
     preservation therefore requires its own explicit definitions and certificate.

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
     is proved for relational FO without order or BIT.

   - [x] **Order-free interpretations as logspace reductions.** The
     [machine-certified transducer](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Reduction.lean)
     streams interpreted relation tables using tuple ranks. Every order-free interpretation
     reduction to an isomorphism-closed target induces a logspace many-one reduction of encoded
     query languages, with L/P closure. Empty universes and domains, nullary relations,
     dimension zero, and invalid parsed table shapes are handled. Numeric predicates computed
     from the universe and canonical lexicographic ordered outputs remain part of the ordered
     milestone; they are not supplied by this theorem.

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
  [fine mass production](Complexity/Computability/Circuit/Boolean/MassProduction/Fine.lean).
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
and machine-characterization priorities above. Continue with the native NL complement theorem. The Arthur–Merlin
and hardness-amplification developments have their own prerequisites and should be split at the
following endpoints, rather than submitted as class definitions or conditional wrappers alone.

| Development | First independently useful endpoint | Remaining endpoint and dependencies |
| --- | --- | --- |
| Iterated functions M2b | Sparse-counter centralizers and signed fixed powers are in [SparseDisplacement](Complexity/Computability/Circuit/Boolean/Iteration/SparseDisplacement.lean). Interval charts, encoding/decoding, canonical labels and additive variable-time circuits are in [SparseTime](Complexity/Computability/Circuit/Boolean/Iteration/SparseTime.lean), including both charged coordinate conversions. Sparse-counter navigation, visit schedules, hitting-time bounds and bounded visit counts are in [SparseNavigation](Complexity/Computability/Circuit/Boolean/Iteration/SparseNavigation.lean), [ResidueAdd](Complexity/Computability/Circuit/Boolean/Iteration/ResidueAdd.lean) and [HittingTime](Complexity/Foundations/Combinatorics/FunctionalGraph/HittingTime.lean). All ports follow source `c4cfa198`. | General input-time and batch results already exist. Affine controllers and hard-power counting are later milestones; these results do not close the whole M2b scope. |
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
  has a proved parameterized space bound on valid encoded instances; a separate
  `O(log n · log log n)` corollary, malformed-input handling and the refined
  `O(ℓ + H log(ℓ + 2))` parameter bound remain outstanding;
* the space hierarchy, which needs a space-budgeted universal simulation; the
  [time hierarchy](Complexity/Computability/Complexity/Classes/Hierarchy/Time.lean) and `P ⊊ EXP`
  are proved with a polynomial simulation gap, so a tight tape-indexed hierarchy needs a
  linear-overhead simulation and an `f log f` time hierarchy the corresponding simulation bound;
* Reingold's theorem: [USTCON ∈ L](Complexity/Computability/Complexity/Classes/LogSpace/USTCON.lean)
  is proved for the adjacency-matrix encoding; an edge-list variant by a logspace reduction, a
  definition of SL with SL = L, and sharing the unary-header injectivity lemma with TreeEval remain;
* `NL = coNL`, building on logspace composition, `NL ⊆ P` and Savitch; `PH ⊆ PSPACE` is
  already proved by evaluating quantified predicates in
  [polynomial space](Complexity/Computability/Complexity/Classes/Inclusions.lean);
* alternating time/space classes and bounded-alternation characterizations of `PH`, beyond the
  proved [AP = PSPACE](Complexity/Computability/Complexity/Classes/Alternation/Savitch.lean);
* the ordered logarithmic-space FO encoding bridge and first-order Circuit Value completeness in the
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
