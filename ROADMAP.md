# Development roadmap

Outstanding work and the rationale needed to guide it. Proved results live in module docstrings,
the [theorem index](paper/README.md) (`paper/main.tex`), and the [README](README.md); when a pull
request completes a milestone or prerequisite here, graduate it out of `ROADMAP.md` following
[AGENTS.md](AGENTS.md#working-on-changes).

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

* **Completed Foundation:** Verifier-based and native finite-machine characterizations of
  [`#P`](Complexity/Computability/Complexity/Classes/SharpP/Characterization.lean),
  [`GapP`](Complexity/Computability/Complexity/Classes/SharpP/GapMachine.lean),
  [`UP`](Complexity/Computability/Complexity/Classes/UP/Machine.lean), and
  [`FewP`](Complexity/Computability/Complexity/Classes/FewP/Machine.lean); `SPP`, `CeqP`/`coCeqP`,
  `US`, `ModP`/`coModP` (with `GapP` residue characterizations and `SPP ⊆ ModP k` for all `k ≥ 2` in
  [ModP/GapP](Complexity/Computability/Complexity/Classes/ModP/GapP.lean)), `WPP`/`LWPP` two-sided,
  bounded-connective, and truth-table closures ([WPP/TwoSided](Complexity/Computability/Complexity/Classes/WPP/TwoSided.lean),
  [WPP/Bounded](Complexity/Computability/Complexity/Classes/WPP/Bounded.lean),
  [WPP/TruthTable](Complexity/Computability/Complexity/Classes/WPP/TruthTable.lean)), and `SBP`/`AWPP`
  with uniform amplification and `MA ⊆ SBP ⊆ AM`
  ([AWPP/Amplification](Complexity/Computability/Complexity/Classes/AWPP/Amplification.lean),
  [SBP/Amplification](Complexity/Computability/Complexity/Classes/SBP/Amplification.lean),
  [SetLowerBound](Complexity/Computability/Complexity/Classes/ArthurMerlin/SetLowerBound.lean));
  Boolean-hierarchy closure and `BH ⊆ Σ₂^P ∩ Π₂^P`
  ([BooleanHierarchy/Closure](Complexity/Computability/Complexity/Classes/BooleanHierarchy/Closure.lean),
  [BooleanHierarchy/PH](Complexity/Computability/Complexity/Classes/BooleanHierarchy/PH.lean));
  `PH ⊆ P^#P = P^PP ⊆ PSPACE` and relativized `PP`/`GapP` verifiers
  ([Toda](Complexity/Computability/Complexity/Classes/Toda.lean),
  [Counting/OracleSpace](Complexity/Computability/Complexity/Classes/Counting/OracleSpace.lean),
  [PP/Oracle](Complexity/Computability/Complexity/Classes/PP/Oracle.lean)); and parsimonious
  `#SAT` / counting-SAT completeness ([CountingSAT](Complexity/Computability/Complexity/Problems/CountingSAT.lean)).
  Current modular Boolean closures require a prime modulus, and bounded/truth-table `WPP`/`LWPP`
  closures do not claim adaptive oracle closure.
* **Open Milestones (dependency-ordered):**
  1. **Permanent completeness (Valiant's theorem).**
     - *Scope boundaries:* `#P`-completeness of the 0–1 matrix permanent under polynomial-time
       counting reductions and `VNP`-completeness of the algebraic permanent with explicit
       characteristic assumptions.
     - *Prerequisites / dependencies:* [CountingSAT](Complexity/Computability/Complexity/Problems/CountingSAT.lean),
       [VP](Complexity/Computability/Circuit/Arithmetic/VP.lean),
       [VNP](Complexity/Computability/Circuit/Arithmetic/VNP.lean), and
       [Determinant](Complexity/Computability/Circuit/Arithmetic/Determinant.lean).
     - *Completion criteria:* Certified polynomial-time gadget reductions preserving exact or
       modular counts, nonvacuous matrix instances in `ComplexityTests/`, theorem-index entry, and
       all six `scripts/check.sh` gates.
  2. **Kadin's Boolean-hierarchy collapse.**
     - *Scope boundaries:* Prove that a finite-level collapse `BH_k = coBH_k` of the Boolean
       hierarchy collapses the polynomial hierarchy `PH`.
     - *Prerequisites / dependencies:* Finite-level equivalences `BH_{k+1} = BH_k ↔ BH_k = coBH_k`
       in [BooleanHierarchy/Closure](Complexity/Computability/Complexity/Classes/BooleanHierarchy/Closure.lean)
       and [BooleanHierarchy/PH](Complexity/Computability/Complexity/Classes/BooleanHierarchy/PH.lean).
     - *Completion criteria:* Public collapse theorem over arbitrary injective encodings, test
       client, and theorem-index entry.
  3. **Stockmeyer approximate counting and counting-class lowness.**
     - *Scope boundaries:* Oracle-algorithm form of Stockmeyer approximate counting, `AWPP`
       `PP`-lowness, and `WPP`/`LWPP` adaptive oracle closure, `UP`-oracle containment, and oracle
       lowness.
     - *Prerequisites / dependencies:* [AWPP/Amplification](Complexity/Computability/Complexity/Classes/AWPP/Amplification.lean),
       [PP/Oracle](Complexity/Computability/Complexity/Classes/PP/Oracle.lean),
       [SharpP/Products](Complexity/Computability/Complexity/Classes/SharpP/Products.lean), and
       pairwise-independent hashing ([PairwiseIndependentHash](Complexity/Probability/PairwiseIndependentHash.lean)).
     - *Completion criteria:* Certified oracle reductions with explicit query/error bounds,
       nonvacuous test client, and theorem-index entry.

### Extend the mathematical canon

This map adds long-term directions to the concrete developments below. It follows the breadth of
[ECCC's scope](https://eccc.weizmann.ac.il/colloquium/call_for_papers/) and the Zoo, rather than the
contents of the original port. Entries are targets for coverage audits and substantial theorem
developments, not assertions that every prerequisite is missing or assignments to current workers.

| Area | Coverage to establish or extend |
| --- | --- |
| Structural complexity | Time/space and exponential hierarchies ([Time](Complexity/Computability/Complexity/Classes/Hierarchy/Time.lean), [Space](Complexity/Computability/Complexity/Classes/Hierarchy/Space.lean)); oracle and advice classes; unambiguous and promise classes; completeness, padding, self-reducibility, [Ladner's theorem](Complexity/Computability/Complexity/Classes/Ladner.lean), relativization and oracle separations. Preserve each reduction's resource bound. |
| Space and alternation | Build on native `NPSPACE = PSPACE`, TQBF completeness, `L ⊊ PSPACE` ([Hierarchy/Space](Complexity/Computability/Complexity/Classes/Hierarchy/Space.lean)), `NL ⊆ P`, [PH ⊆ PSPACE](Complexity/Computability/Complexity/Classes/Inclusions.lean) and [AP = PSPACE](Complexity/Computability/Complexity/Classes/Alternation/Savitch.lean). Extend the [machine-class milestones](#machine-class-milestones), sublinear space hierarchies, alternating time/space classes and bounded-alternation characterizations of PH. Distinguish polynomial-space simulation from sharp bounds for sublinear space. |
| Counting and modular classes | Build on `#P`, `GapP`, `PP`, [parity-P](Complexity/Computability/Complexity/Classes/ParityP.lean) and [Toda's PH ⊆ P^#P theorem](Complexity/Computability/Complexity/Classes/Toda.lean), with a fixed polynomial-time program correct against every oracle answering the counting function's bits. Extend counting reductions and relativized machine characterizations, permanent completeness, modular/counting hierarchies and the oracle-algorithm form of Stockmeyer approximate counting. |
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

Complete these milestones in order of their dependencies. Each requires public Lean results, a
nonvacuous client in `ComplexityTests/`, a [theorem-index](paper/README.md) entry, and independent
mathematical, API, and statement-index reviews of the completed revision.

1. **Ordered first-order complexity, projections, and Circuit Value completeness (`Complexity/Logics/FirstOrder/Ordered/`, `Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/`)**
   - *Completed Foundation:* Following [Immerman][Immerman1999] ([Proviso 1.15, p. 16](https://people.cs.umass.edu/~immerman/pub/ch0_1_2.pdf)), ordered structures live on `{0, …, n-1}` with `n ≥ 2` and `FO` means `FO(≤, BIT)`. Canonical `0`, `1`, `max`, `≤`, `BIT`, `PLUS`, `BitSum`, `TIMES`, full-tuple `lexRank`/`BIT`, and positive-dimensional full-tuple interpretation composition on `Fin n` (`n ≥ 2`) are proved in [Ordered/Basic](Complexity/Logics/FirstOrder/Ordered/Basic.lean), [Ordered/Addition](Complexity/Logics/FirstOrder/Ordered/Addition.lean), [Ordered/BitSum](Complexity/Logics/FirstOrder/Ordered/BitSum.lean), [Ordered/Multiplication](Complexity/Logics/FirstOrder/Ordered/Multiplication.lean), [Ordered/TupleBit](Complexity/Logics/FirstOrder/Ordered/TupleBit.lean), [Ordered/FullTuple](Complexity/Logics/FirstOrder/Ordered/FullTuple.lean), and [Ordered/FullTuple/Composition](Complexity/Logics/FirstOrder/Ordered/FullTuple/Composition.lean). Native ordered model checking `FO(≤, BIT) ⊆ L` is proved in [LogSpace/FirstOrder/Ordered](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered.lean), and the canonical full-tuple logspace interpretation transducer is proved in [Ordered/FullTuple/Encoding](Complexity/Logics/FirstOrder/Ordered/FullTuple/Encoding.lean) and [LogSpace/FirstOrder/Ordered/Reduction](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Reduction.lean). The ordered `NP ⊆ ESO` converse is proved in [Fagin/Ordered](Complexity/Computability/Complexity/Fagin/Ordered.lean). In the order-free setting, `SAT` completeness ([Fagin/SAT](Complexity/Computability/Complexity/Fagin/SAT.lean)), quantifier-free/projection cores and `fo_*` tactics ([Projection](Complexity/Logics/FirstOrder/Projection.lean), [QFReduces](Complexity/Logics/FirstOrder/Reduction/QuantifierFree.lean), [Tactic/FirstOrder](Complexity/Tactic/FirstOrder.lean), [SizedGraph](Complexity/Logics/FirstOrder/Problems/SizedGraph.lean)), the order-free logspace interpretation transducer ([LogSpace/FirstOrder/Reduction](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Reduction.lean)), and logspace `P`-completeness of [Circuit Value](Complexity/Computability/Complexity/Problems/CircuitValue/Completeness.lean) and [Monotone Circuit Value](Complexity/Computability/Complexity/Problems/MonotoneCircuitValue/Completeness.lean) are proved.
   - *Open Milestones (dependency-ordered):*
     1. **Ordered `ESO ⊆ NP` and full ordered Fagin equivalence.**
        - *Scope boundaries:* Prove the forward `ESO ⊆ NP` direction on canonical ordered encodings (`n ≥ 2`, rejecting malformed tables and imposing no permutation-invariance hypothesis) to complete `NP = ESO` in the ordered setting.
        - *Prerequisites / dependencies:* [Fagin/Ordered](Complexity/Computability/Complexity/Fagin/Ordered.lean) and [LogSpace/FirstOrder/Ordered](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered.lean).
        - *Completion criteria:* Public equivalence theorem `mem_NP_iff_esoDefinable` for ordered queries, nonvacuous test client, and theorem-index entry.
     2. **Class-level ordered FO reduction closure and restricted domains.**
        - *Scope boundaries:* Prove isomorphism-closed class-level closure of `L`, `NL`, `P`, and `NP` under ordered first-order reductions (`≤_fo`), and extend ordered interpretations and logspace transducers from full universes `Fin (n^k)` to definable restricted domains using explicit restricted-domain numeric preservation certificates (since canonical `BIT` on an arbitrary definable restricted domain need not be FO-definable per Immerman, Exercise 1.33).
        - *Prerequisites / dependencies:* [Ordered/FullTuple/Composition](Complexity/Logics/FirstOrder/Ordered/FullTuple/Composition.lean) and [LogSpace/FirstOrder/Ordered/Reduction](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Reduction.lean).
        - *Completion criteria:* Class-closure theorems for `L`, `NL`, `P`, `NP`, restricted-domain transducer certificate, and checked client.
     3. **Ordered first-order and quantifier-free projections (`≤_fop`, `≤_qfp`) and canonical completeness.**
        - *Scope boundaries:* Specialize [Projection](Complexity/Logics/FirstOrder/Projection.lean) and [QFReduces](Complexity/Logics/FirstOrder/Reduction/QuantifierFree.lean) to positive-dimensional ordered structures (keeping the classical `qfp` exclusion of `BIT` explicit per [Immerman–Landau, Definition 3.6](https://people.cs.umass.edu/~immerman/pub/mult.pdf)), extend `fo_reduction` ([Tactic/FirstOrder](Complexity/Tactic/FirstOrder.lean)) to simplify relations of composite or higher-dimensional interpretations, and prove ordered projection completeness of `SAT`, `3SAT`, `3COL`, `IndependentSet`, `Clique`, and `VertexCover` for `NP` and `REACH` for `NL` (plus remaining order-free `SAT → 3SAT` and graph-property bridges).
        - *Prerequisites / dependencies:* Milestones 1.1 and 1.2 above, [Projection/Graph](Complexity/Logics/FirstOrder/Projection/Graph.lean), and [SizedGraph](Complexity/Logics/FirstOrder/Problems/SizedGraph.lean).
        - *Completion criteria:* Public `≤_fop`/`≤_qfp` definitions, composite `fo_reduction` tactic support, completeness theorems, and theorem-index entries.
     4. **Circuit Value completeness under ordered first-order reductions.**
        - *Scope boundaries:* Prove `P`-completeness of `CircuitValue` and `MonotoneCircuitValue` under ordered `≤_fo` / `≤_fop` via `REACHa → MCVP → CVP` ([Immerman, Chapter 3, Theorem 3.26 and Exercise 3.28](https://people.cs.umass.edu/~immerman/book/ch3.pdf)), supplying the alternating-logspace simulation of polynomial-time machines and the relational-to-`encCircuitValue` bridge.
        - *Prerequisites / dependencies:* Milestones 1.2 and 1.3 above, [CircuitValue/Completeness](Complexity/Computability/Complexity/Problems/CircuitValue/Completeness.lean), and [MonotoneCircuitValue/Completeness](Complexity/Computability/Complexity/Problems/MonotoneCircuitValue/Completeness.lean).
        - *Completion criteria:* Public ordered FO-completeness theorems for `MCVP` and `CVP`, test client, and theorem-index entry.

2. **Uniform circuit families (`Complexity/Computability/Circuit/Boolean/`)**
   - *Completed Foundation:* Nonuniform `NC`/`AC`/`TC` hierarchies ([DepthClasses](Complexity/Computability/Circuit/Boolean/DepthClasses.lean)), nonuniform `FO` model checking in `AC⁰` without order/`BIT` ([Boolean/FirstOrder](Complexity/Computability/Circuit/Boolean/FirstOrder.lean)), and polynomial-time function-family circuit compilation without depth bounds ([CircuitValue/Compilation](Complexity/Computability/Complexity/Problems/CircuitValue/Compilation.lean)).
   - *Open Milestones:*
     - *Scope boundaries:* Define logspace-uniform and `DLOGTIME`-uniform circuit families with explicit gate-address, direct-connection, and input encodings; certify circuit generation, evaluation, and machine-to-circuit simulations preserving size, depth, and construction-resource bounds; prove `FO(≤, BIT) = DLOGTIME-uniform AC⁰` under explicit input-access and encoding conventions.
     - *Prerequisites / dependencies:* Ordered `FO(≤, BIT)` model checking and encodings (Priority 1 above) and [DepthClasses](Complexity/Computability/Circuit/Boolean/DepthClasses.lean).
     - *Completion criteria:* Uniform class definitions, certified simulation theorems, `FO(≤, BIT) = DLOGTIME-uniform AC⁰` equivalence, nonvacuous test client, and theorem-index entry.

3. **Relativized counting-machine characterizations (`Complexity/Computability/Machines/Turing/MultiTape/Counting/Oracle/`)**
   - *Completed Foundation:* Closed native finite-machine characterizations of [`#P`](Complexity/Computability/Complexity/Classes/SharpP/Characterization.lean), [`GapP`](Complexity/Computability/Complexity/Classes/SharpP/GapMachine.lean), [`UP`](Complexity/Computability/Complexity/Classes/UP/Machine.lean), and [`FewP`](Complexity/Computability/Complexity/Classes/FewP/Machine.lean) (built on [Counting](Complexity/Computability/Machines/Turing/MultiTape/Counting.lean), [Certificate](Complexity/Computability/Machines/Turing/MultiTape/Counting/Certificate.lean), [Checker](Complexity/Computability/Machines/Turing/MultiTape/Counting/Checker.lean), [Composition](Complexity/Computability/Machines/Turing/MultiTape/Counting/Composition.lean), and [Verifier](Complexity/Computability/Machines/Turing/MultiTape/Counting/Verifier.lean)), semantic native oracle occurrence replay ([Counting/Oracle/Replay](Complexity/Computability/Machines/Turing/MultiTape/Counting/Oracle/Replay.lean)), and relativized `PP`/`GapP` verifiers ([PP/Oracle](Complexity/Computability/Complexity/Classes/PP/Oracle.lean)).
   - *Open Milestones:*
     - *Scope boundaries:* Certify efficient encoded oracle checking, response-access costs, and nonvacuous oracle counting clocks uniform over admissible handlers (without instantiating total-PMF predicates at `Fin 0`), and prove native oracle-machine characterizations for `#P^A` and `GapP^A` (resource bounds uniform over admissible oracles, correctness specialized to a fixed language oracle).
     - *Prerequisites / dependencies:* [Counting/Oracle/Replay](Complexity/Computability/Machines/Turing/MultiTape/Counting/Oracle/Replay.lean), [Probabilistic/Oracle/Composition](Complexity/Computability/Probabilistic/Oracle/Composition.lean), and [PP/Oracle](Complexity/Computability/Complexity/Classes/PP/Oracle.lean).
     - *Completion criteria:* Public `#P^A` and `GapP^A` native machine equivalence theorems, nonvacuous oracle test client, and theorem-index entry.

4. **Certificate calculus, nested streaming, and proof bookkeeping (`Complexity/Computability/Machines/Turing/MultiTape/Complexity/`, `Complexity/Tactic/`)**
   - *Completed Foundation:* Strict open-program oracle PPT composition ([Probabilistic/Oracle/Composition](Complexity/Computability/Probabilistic/Oracle/Composition.lean)) and open stateful oracle substitution ([Probabilistic/Oracle/Substitution](Complexity/Computability/Probabilistic/Oracle/Substitution.lean), extending [OracleSimulation](Complexity/Computability/Probabilistic/OracleSimulation.lean)); quantitative degree composition retaining separate output-size bounds ([Complexity/Quantitative](Complexity/Computability/Machines/Turing/MultiTape/Complexity/Quantitative.lean)); single-pass and paired cumulative streaming folds and unary streaming iteration ([Complexity/Streaming](Complexity/Computability/Machines/Turing/MultiTape/Complexity/Streaming.lean), [Encodings/StreamFold](Complexity/Computability/Machines/Turing/MultiTape/Encodings/StreamFold.lean)); and quantitative cumulative-time, workspace, and degree certificates for PRG stretching ([Crypto/Computational/Stretch](Complexity/Crypto/Computational/Stretch.lean)).
   - *Open Milestones:*
     - *Scope boundaries:* Extend cumulative streaming contracts and `fun_prop`/`polytime` automation to nested multi-pass streaming loops and reusable bounded-table/cache invariants when multiple clients share the proof burden; improve configuration views, tape partitions, and `PairReady`/`clearedCfg` preservation rules without unfolding machine transitions globally.
     - *Prerequisites / dependencies:* [Complexity/Streaming](Complexity/Computability/Machines/Turing/MultiTape/Complexity/Streaming.lean) and [Complexity/Quantitative](Complexity/Computability/Machines/Turing/MultiTape/Complexity/Quantitative.lean).
     - *Completion criteria:* Reusable combinator/tactic rules validated against demanding regression clients (such as Cook–Levin, GGM, or rational hitting-list runtime) with reduced proof burden.

5. **Runnable PCP, expander-walk algorithms, and FGLSS amplification (`Complexity/Computability/PCP/`, `Complexity/Foundations/Combinatorics/Expander/`)**
   - *Completed Foundation:* Certified [PCP theorem](Complexity/Computability/PCP/Completeness.lean), [six-query tester](Complexity/Computability/PCP/SelectedComposition.lean) (128-symbol alphabet, `2^-61` amplification gap), vertex-count-polynomial rotation certificate, combinatorial [expander-walk hitting bound](Complexity/Foundations/Combinatorics/Expander/Hitting.lean), and constant-factor NP-hardness of approximating Independent Set, Clique, and Vertex Cover ([PCP/Approximation/IndependentSet](Complexity/Computability/PCP/Approximation/IndependentSet.lean) via [PCP/Approximation](Complexity/Computability/PCP/Approximation.lean)).
   - *Open Milestones (dependency-ordered):*
     1. **Bit-length-polynomial expander rotation:** Certify expander rotation in time polynomial in the bit length of a vertex name rather than the vertex count.
     2. **Machine-certified expander-walk error reduction and extractors:** Turn [Expander/Hitting](Complexity/Foundations/Combinatorics/Expander/Hitting.lean) into machine-certified error reduction for `RP`/`BPP` and explicit extractor guarantees with certified seed and evaluation costs.
     3. **FGLSS clique-hardness and gap amplification:** Build the FGLSS reduction and expander-walk gap amplification on [PCP/Approximation](Complexity/Computability/PCP/Approximation.lean) and [PCP/Completeness](Complexity/Computability/PCP/Completeness.lean).
     - *Completion criteria:* Certified polynomial-time reductions with explicit gap and runtime bounds, test clients, and theorem-index entries.

## Remaining theorem developments

Track these developments by their public theorems, explicit scope boundaries, prerequisites, and
completion criteria:

* **Circuit constructor and hitting-list runtimes (`Complexity/Computability/Circuit/`).**
  - *Completed Foundation:*
    - Mass production gate-cost bounds in [Uhlig](Complexity/Computability/Circuit/Boolean/MassProduction/Uhlig.lean) and [Fine](Complexity/Computability/Circuit/Boolean/MassProduction/Fine.lean).
    - Iterated-function circuit upper and lower bounds (all M2b nonuniform endpoints complete): [FunctionalGraph](Complexity/Foundations/Combinatorics/FunctionalGraph.lean) (with [Spectrum](Complexity/Foundations/Combinatorics/FunctionalGraph/Spectrum.lean), [ForestDuality](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestDuality.lean), [DistinguishedPoints](Complexity/Foundations/Combinatorics/FunctionalGraph/DistinguishedPoints.lean), [CheckpointForest](Complexity/Foundations/Combinatorics/FunctionalGraph/CheckpointForest.lean), [ForestIntervals](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestIntervals.lean), [ForestSegments](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestSegments.lean), [ForestNavigation](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestNavigation.lean)), [Circuit/Iteration](Complexity/Computability/Circuit/Iteration.lean), [Boolean/Iteration](Complexity/Computability/Circuit/Boolean/Iteration.lean) (with [InputTime](Complexity/Computability/Circuit/Boolean/Iteration/InputTime.lean), [Batch](Complexity/Computability/Circuit/Boolean/Iteration/Batch.lean), [ForestCircuits](Complexity/Computability/Circuit/Boolean/Iteration/ForestCircuits.lean), [NavigationCircuits](Complexity/Computability/Circuit/Boolean/Iteration/NavigationCircuits.lean), [VisitScheduleCircuits](Complexity/Computability/Circuit/Boolean/Iteration/VisitScheduleCircuits.lean), [SparseNavigation](Complexity/Computability/Circuit/Boolean/Iteration/SparseNavigation.lean), [AffineController](Complexity/Computability/Circuit/Boolean/Iteration/AffineController.lean), [UniversalMap](Complexity/Computability/Circuit/Boolean/Iteration/UniversalMap.lean), [InPlace](Complexity/Computability/Circuit/Boolean/Iteration/InPlace.lean), [SequentialSquaring](Complexity/Computability/Circuit/Boolean/Iteration/SequentialSquaring.lean), [ModulusCounter](Complexity/Computability/Circuit/Boolean/Iteration/ModulusCounter.lean), and [CounterBatch](Complexity/Computability/Circuit/Boolean/Iteration/CounterBatch.lean)).
    - Rational-matrix hitting lists ([Circuit/Rational](Complexity/Computability/Circuit/Rational.lean)) and runtime parameter/bit-length bounds ([Runtime/Parameters](Complexity/Computability/Circuit/Rational/Runtime/Parameters.lean), [Runtime/Determinant](Complexity/Computability/Circuit/Rational/Runtime/Determinant.lean), [Runtime/Lift](Complexity/Computability/Circuit/Rational/Runtime/Lift.lean)); explicit Ben-Sasson–Kopparty affine disperser and Mishra–Santhanam `3.5N - O(N / log N)` `B₂` lower bound in `P` ([Complexity/AffineDisperser](Complexity/Computability/Complexity/AffineDisperser.lean)); and three-source pseudoentropy extraction ([Pseudoentropy/ThreeSource](Complexity/Crypto/Computational/Pseudoentropy/ThreeSource.lean)).
  - *Open Milestones:*
    1. **Rational hitting-list generator polynomial-time certificate:** Certify `ComputableTidilyInPolyTime` for `detRows` ([Runtime/Determinant](Complexity/Computability/Circuit/Rational/Runtime/Determinant.lean)), `liftRows` ([Runtime/Lift](Complexity/Computability/Circuit/Rational/Runtime/Lift.lean)), adjugate/rational entry normalization, and the full grid-enumeration generator `hittingList` ([Rational/Generator](Complexity/Computability/Circuit/Rational/Generator.lean)), and port any remaining v1 extractor modules.
    2. **Uniform preprocessing runtime for mass production and iterated-function circuits:** Certify constructor/preprocessing runtime separately from nonuniform circuit existence in [MassProduction/Fine](Complexity/Computability/Circuit/Boolean/MassProduction/Fine.lean) and [Boolean/Iteration](Complexity/Computability/Circuit/Boolean/Iteration.lean).
    - *Completion criteria:* `ComputableTidilyInPolyTime` (or subexponential-time) certificates for the constructors, test clients, and theorem-index entries.

* **Weighted threshold representations (`Complexity/Computability/Circuit/Boolean/WeightedThreshold/`).**
  - *Completed Foundation:* Separable/bi-monotone comparison trees and inner-product tree bounds ([DecisionTree/Separable](Complexity/Computability/DecisionTree/Separable.lean), [DecisionTree/InnerProduct](Complexity/Computability/DecisionTree/InnerProduct.lean), [DecisionTree/AffineScore](Complexity/Computability/DecisionTree/AffineScore.lean)); activity, capacity, mixed-activation, median-cut, component, direction-menu, pending-bias, scalar-activity, and quadratic-potential bounds ([WeightedThreshold/InnerProduct](Complexity/Computability/Circuit/Boolean/WeightedThreshold/InnerProduct.lean), [Activity](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Activity.lean), [CapacityCircuit](Complexity/Computability/Circuit/Boolean/WeightedThreshold/CapacityCircuit.lean), [Activation](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Activation.lean), [Cut](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Cut.lean), [Components](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Components.lean), [Menus](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Menus.lean), [PendingBias](Complexity/Computability/Circuit/Boolean/WeightedThreshold/PendingBias.lean), [ScalarActivity](Complexity/Computability/Circuit/Boolean/WeightedThreshold/ScalarActivity.lean), [Potential](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Potential.lean)); and relative source complexity ([Circuit/SourceComplexity](Complexity/Computability/Circuit/SourceComplexity.lean)).
  - *Open Milestones:*
    - *Scope boundaries:* Formalize universal scalar circuit synthesis, entropy and asymptotic activity bounds, and geometric cutting from [Threshold Circuits as Decision Trees and Finite-State Programs](https://github.com/SamuelSchlesinger/threshold-circuits), plus any remaining explicit source-reduction families from v1.
    - *Prerequisites / dependencies:* [CapacityCircuit](Complexity/Computability/Circuit/Boolean/WeightedThreshold/CapacityCircuit.lean), [ScalarActivity](Complexity/Computability/Circuit/Boolean/WeightedThreshold/ScalarActivity.lean), and [SourceComplexity](Complexity/Computability/Circuit/SourceComplexity.lean).
    - *Completion criteria:* Proved synthesis and asymptotic bounds with nonvacuous instances and theorem-index entries.

* **Search and parameterized complexity (`Complexity/Computability/Complexity/Classes/TFNP/`, `Complexity/Computability/Complexity/Parameterized/`).**
  - *Completed Foundation:* `FNP`, `FP`, `TFNP` ([TFNP](Complexity/Computability/Complexity/Classes/TFNP.lean)), `FP = FNP ↔ P = NP` ([SearchToDecision](Complexity/Computability/Complexity/Classes/TFNP/SearchToDecision.lean)), and `PLS`, `PPP`, `PPAD`, `PPA` with their [combinatorial principles](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Principles.lean) and [canonical complete circuit problems](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Completeness.lean); `FPT`, `XP`, and fpt-reductions ([Parameterized](Complexity/Computability/Complexity/Parameterized.lean)), the Cai–Chen–Downey–Fellows kernelization equivalence `A ∈ FPT enc κ ↔ HasKernel enc κ A` ([Kernelization](Complexity/Computability/Complexity/Parameterized/Kernelization.lean)), bounded-search-tree `VertexCover ∈ FPT` in time `O(2^k (|x|+1)^e)` ([VertexCover](Complexity/Computability/Complexity/Parameterized/VertexCover.lean)), and ETH lower-bound transfers ([FineGrained/GraphProblems](Complexity/Computability/Complexity/FineGrained/GraphProblems.lean)).
  - *Open Milestones:*
    - *Scope boundaries:* Formalize `CLS` (`CLS ⊆ PPAD ∩ PLS`) and further complete total search problems; develop strongly uniform `FPT` and kernelization (requiring computable parameter-bound functions `f`), explicit polynomial kernels (`HasPolyKernel`, e.g., Buss's `O(k^2)` kernel for `VertexCover`), and the `W[1]`/`W[2]`/`W[t]` hierarchy with canonical reductions.
    - *Prerequisites / dependencies:* [Subclasses/Completeness](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Completeness.lean), [Kernelization](Complexity/Computability/Complexity/Parameterized/Kernelization.lean), and [VertexCover](Complexity/Computability/Complexity/Parameterized/VertexCover.lean).
    - *Completion criteria:* Public class/kernel theorems with certified polynomial-time reductions, test instances, and theorem-index entries.

* **Randomized communication, monotone depth, list decoding, and Boolean analysis.**
  - *Completed Foundation:* `Ω(n)` bounded-error randomized disjointness ([Communication/Disjointness](Complexity/Computability/Communication/Disjointness.lean)), bipartite-matching monotone depth ([Monotone/BipartiteMatching](Complexity/Computability/Circuit/Monotone/BipartiteMatching.lean)), Sudan Reed–Solomon list decoding ([Code/Sudan](Complexity/Foundations/Data/Code/Sudan.lean)), KKL, Talagrand, and Friedgut junta theorems ([KahnKalaiLinial](Complexity/Foundations/BooleanAnalysis/KahnKalaiLinial.lean)), hypercontractivity for `p ≤ 2 ≤ q` ([Hypercontractivity](Complexity/Foundations/BooleanAnalysis/Hypercontractivity.lean)), and Khrapchenko's formula bound ([Khrapchenko](Complexity/Computability/Circuit/Boolean/Khrapchenko.lean)).
  - *Open Milestones:*
    1. **Communication and monotone depth:** General-graph Raz–Wigderson monotone depth lower bound; information complexity and reductions to streaming and sketching lower bounds.
    2. **Guruswami–Sudan multiplicity list decoding:** Extend [Code/Sudan](Complexity/Foundations/Data/Code/Sudan.lean) keeping interpolation, list-size/agreement guarantees, and uniform decoding runtime as separate certified obligations.
    3. **Hypercontractivity applications and formula lower bounds:** Extend [Hypercontractivity](Complexity/Foundations/BooleanAnalysis/Hypercontractivity.lean) and formula lower bounds per [Jukna coverage](#jukna-coverage).
    - *Completion criteria:* Public theorems separating combinatorial bounds from uniform algorithmic runtime, test clients, and theorem-index entries.

* **Metacomplexity scope note.** The current V1 port retains checked [MCSP definitions](Complexity/Computability/MCSP/Basic.lean), [succinct variants](Complexity/Computability/MCSP/Succinct.lean), [Shannon bounds](Complexity/Computability/MCSP/Shannon.lean), [anti-checker existence](Complexity/Computability/MCSP/AntiChecker.lean), and Kabanets–Cai [OneWay/MCSP](Complexity/Crypto/Computational/OneWay/MCSP.lean); it excludes the legacy circuitized anti-checker, hardness-magnification argument, and `MINKT`/`MINCKT` developments, which should return only as independently scoped, reviewed milestones.

## Finishing the recovered developments

Complete bounded endpoints on ordinary branches, with the six checks (`scripts/check.sh`) and
independent API, correctness, and statement-index reviews before closing a milestone. Do not mark
these rows complete from an abstract algorithm, a class definition, or an assumed reconstruction
theorem: their machine/resource and quantitative conclusions are part of acceptance.

| Development | Completed foundation and first endpoint | Open endpoint, prerequisites, and completion criteria |
| --- | --- | --- |
| `NL = coNL` (Immerman–Szelepcsényi) | Combinatorial inductive counting ([InductiveCounting](Complexity/Foundations/Relation/InductiveCounting.lean)), `NL ⊆ P` ([LogSpace/PolyTime](Complexity/Computability/Complexity/Classes/LogSpace/PolyTime.lean)), `USTCON ∈ L` ([LogSpace/USTCON](Complexity/Computability/Complexity/Classes/LogSpace/USTCON.lean)), and Savitch's theorem ([Space/Savitch](Complexity/Computability/Complexity/Classes/Space/Savitch.lean)). | **Target:** Compile streaming inductive counting to the native `MultiTapeNTM` model (`DecidesInSpace`, where every branch halts via logarithmic loop counters), certify every computation prefix's logspace bound without retaining a whole reachable set, and prove `compl_mem_NL` (`NL = coNL`). Separately prove that logspace recognizers whose branches may loop (`RecognizesInSpace`) recognize only problems in `NL`. |
| Arthur–Merlin protocols | Verifier-based `MA` and `AM`, amplification, `NP ∪ BPP ⊆ MA ⊆ AM ⊆ Π₂^P`, `MA ⊆ Σ₂^P ∩ Π₂^P`, `MA ⊆ SBP ⊆ AM` ([ArthurMerlin](Complexity/Computability/Complexity/Classes/ArthurMerlin.lean), [SetLowerBound](Complexity/Computability/Complexity/Classes/ArthurMerlin/SetLowerBound.lean)), [public-coin GNI in AM](Complexity/Computability/Complexity/Classes/ArthurMerlin/GraphNonIsomorphism.lean), and Boppana–Håstad–Zachos [`coNP ⊆ AM ⇒ PH = Σ₂^P`](Complexity/Computability/Complexity/Classes/ArthurMerlin/Collapse.lean). | **Target:** Interactive-machine characterizations of `MA` and `AM`, Goldwasser–Sipser private-to-public-coin transformation (`IP[k] ⊆ AM[k+2]`), and Babai–Moran round collapse (`AM[k] = AM` for constant `k`), with certified verifier/prover transcripts. |
| Worst-case-hardness derandomization | Eventual-hardness derandomization `P = BPP` from `2^(γn)` De Morgan circuit hardness of a language in `E` via Sudan–Trevisan–Vadhan and Nisan–Wigderson ([BPP/WorstCaseHardness](Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean) and [BPP/Derandomization](Complexity/Computability/Complexity/Classes/BPP/Derandomization.lean)). | **Target:** Infinitely-often worst-case-to-average-case derandomization, Meyer's theorem (`EXP ⊆ P/poly ⇒ EXP = Σ₂^P`), and the Babai–Fortnow–Nisan–Wigderson theorem (`EXP ⊈ P/poly ⇒ io-BPP ⊆ SUBEXP`). |

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

* **Completed Foundations in Specific Chapters:**
  - *Chapter 1 (Lemma 1.17):* The [almost-injective binary linear map](Complexity/Probability/BitString/LinearHash/Collisions.lean) implements Lemma 1.17 (unordered-pair collision bound and injective-map corollary); its matrix selection is existential, and the partial-function circuit upper bounds using it remain open.
  - *Chapter 20 (Approximation and Fusion method):* Extending [semifilter covers](Complexity/Computability/Circuit/Fusion/Semifilter.lean) and the [cyclic characterization](Complexity/Computability/Circuit/Fusion/Cyclic/Compiler.lean) via [Oliveira (2018)](https://www.dcs.warwick.ac.uk/~igorcarb/documents/papers/approximation-method-fusion-note.pdf) and [Cavalar–Oliveira, ECCC TR25-033 (2025)](https://eccc.weizmann.ac.il/report/2025/033/), the [quadratic compiler](Complexity/Computability/Circuit/Fusion/Quadratic.lean), [local observation consistency](Complexity/Computability/Circuit/Fusion/Consistency.lean) and [`8n + 8` pair-capacity counting barrier](Complexity/Computability/Circuit/Fusion/Sampling.lean), [graph row/column-to-literal transfer](Complexity/Computability/Circuit/Fusion/Graph.lean) and [inequality cover cost `n`](Complexity/Computability/Circuit/Fusion/Graph/Inequality.lean), [inclusion-pattern counting](Complexity/Computability/Circuit/Fusion/Encoding.lean) and [random bipartite graph hardness](Complexity/Computability/Circuit/Fusion/Graph/Random.lean), and Karchmer's [conondeterministic circuit characterization `ρ_ultra(f) ≤ C_∀,AND(f) ≤ 5ρ_ultra(f)`](Complexity/Computability/Circuit/Fusion/Conondeterministic.lean) ([converse](Complexity/Computability/Circuit/Fusion/Converse.lean), [Boolean measure](Complexity/Computability/Circuit/Boolean/Conondeterministic.lean)) are proved. Keep source models explicit (free constants, zero-gate constructions, exact vs. one-sided literal consistency, AND vs. total gate costs, and pair-capacity barrier scope over all pairs).

This map follows the [contents](https://web.vu.lt/mif/s.jukna/boolean/TOC.pdf).
The linked modules are starting points, not evidence of complete chapter coverage. Audit exact
statements and hypotheses against each numbered result, including circuit bases, cost conventions,
uniformity, explicitness and quantitative strength; a citation or related theorem is insufficient.

| Chapters | Existing entry points | Next coverage work |
| --- | --- | --- |
| 1–2: foundations and Boolean analysis | [Circuit hierarchy](Complexity/Computability/Circuit/Boolean/Hierarchy.lean), [Shannon synthesis](Complexity/Computability/Circuit/Boolean/ShannonSynthesis.lean), [Fourier analysis](Complexity/Foundations/BooleanAnalysis/Fourier.lean) | Audit counting, graph complexity, degree and approximation results; complete partial-function upper bounds from Lemma 1.17. |
| 3–5: communication | [Protocols](Complexity/Computability/Communication/Protocol.lean), [Karchmer–Wigderson](Complexity/Computability/Communication/KarchmerWigderson.lean) | Complete matrix, randomized and multiparty results. |
| 6–10: formulas and circuits | [Spira](Complexity/Computability/Circuit/Boolean/Spira.lean), [Khrapchenko](Complexity/Computability/Circuit/Boolean/Khrapchenko.lean), [monotone clique](Complexity/Computability/Circuit/Monotone/Clique/LowerBound.lean) | Audit remaining formula and monotone bounds; develop span programs and negation complexity. |
| 11–13: depth restrictions and general gates | [Håstad](Complexity/Computability/Circuit/Boolean/Hastad.lean), [Smolensky](Complexity/Computability/Circuit/Boolean/Smolensky.lean), [symmetric gates](Complexity/Computability/Circuit/Boolean/ShallowSymmetric.lean) | Audit depth-three, threshold, entropy, wire and linear-operator bounds. |
| 14–17: trees and branching programs | [Decision-tree certificates](Complexity/Computability/DecisionTree/Certificate.lean), [Barrington](Complexity/Computability/Circuit/Boolean/BarringtonClass.lean) | Complete bounded-read and bounded-time lower bounds and remaining tree results. |
| 18–19: proof complexity | [Resolution size–width](Complexity/Logics/Propositional/Resolution/SizeWidth.lean), [tree-like resolution](Complexity/Logics/Propositional/Resolution/TreeLike.lean), [Cook–Reckhow systems](Complexity/Logics/Propositional/ProofSystem.lean) | Develop pigeonhole/Tseitin lower bounds, proof space and cutting-plane proofs. |
| 20: barriers and further methods | [Fusion API](Complexity/Computability/Circuit/Fusion/Basic.lean), [Nisan–Wigderson core](Complexity/Computability/Kolmogorov/NisanWigderson.lean), [Affine disperser `B₂` bound](Complexity/Computability/Complexity/AffineDisperser.lean) | Match the book's remaining generator, natural-proof, fusion and indirect lower-bound results. |
| Appendix A: mathematical prerequisites | Mathlib and `Complexity/Foundations` | Reuse existing statements and fill dependencies as clients require them. |

## Stateful algorithms and data structures prototype

* **Completed Foundation:** The [stateful interface calculus](Complexity/Foundations/Semantics/Stateful/Basic.lean) separates mathematical operations, [semantic modules](Complexity/Foundations/Semantics/Stateful/Composition.lean), [native realizations](Complexity/Foundations/Semantics/Stateful/Realization.lean), and [resource certificates](Complexity/Foundations/Semantics/Stateful/Resource.lean), with checked [two-stack queue](Complexity/Algorithms/Lean/Queue.lean) and [reset-and-replay timeline editing](Complexity/Algorithms/Lean/Retroactive.lean) constructions (counting backend calls without compiling pure client controllers to Word-RAM). The [fixed-program bridge](Complexity/Computability/WordRAM/Dynamic.lean) certifies persistent bounded [stack](Complexity/Algorithms/WordRAM/Stack.lean) and [dynamic prefix-sum](Complexity/Algorithms/WordRAM/PrefixSums/Dynamic.lean) clients over power-of-two aggregation trees (excluding initial construction and external argument encoding/decoding).
* **Open Milestones:**
  - *Scope boundaries:* Charged initialization and caller/linking compilation; a concrete shared-heap queue using two bounded stacks; reusable allocation and deallocation, live/peak space accounting, doubling-array amortization, richer ownership, and recursive procedures; independent model realizations for cell probes, caches, and randomness; and present/historical queries for the retroactive interface.
  - *Prerequisites / dependencies:* [Stateful/Realization](Complexity/Foundations/Semantics/Stateful/Realization.lean), [WordRAM/Dynamic](Complexity/Computability/WordRAM/Dynamic.lean), and upstream CSLib coordination ([UPSTREAM.md](UPSTREAM.md)).
  - *Completion criteria:* Certified machine/amortized contracts with nonvacuous client histories and coordinator review.

## Machine-class milestones

Polynomial efficiency is sufficient for many reductions, but does not establish tight time or
space bounds. Further class-level work needs resource certificates for the actual algorithms:

* **Tree Evaluation (`Complexity/Computability/TreeEval/`):**
  - *Completed Foundation:* The [Cook–Mertz machine](Complexity/Computability/TreeEval/Space.lean) has a proved parameterized space bound on valid encoded instances and an `O(log n · log log n)` input-size space corollary on nontrivial instances (`1 ≤ ℓ` and `1 ≤ H`).
  - *Open target & completion criteria:* Certify malformed-input rejection and tighten the parameterized space bound to `O(ℓ + H log(ℓ + 2))`.
* **Space and time hierarchies (`Complexity/Computability/Complexity/Classes/Hierarchy/`):**
  - *Completed Foundation:* The [space-budgeted universal simulator](Complexity/Computability/Complexity/Classes/Hierarchy/SpaceUniversal.lean) (`budgetedUniversal`) and linear/superlinear [deterministic space hierarchy](Complexity/Computability/Complexity/Classes/Hierarchy/Space.lean) (`DSPACE f ⊊ DSPACE g` for space-constructible `g` with `n ≤ g n` and `f = o(g)`, `DSPACE(n^k) ⊊ DSPACE(n^{k+1})`, and `L ⊊ PSPACE`) are proved, alongside the polynomial-gap [time hierarchy](Complexity/Computability/Complexity/Classes/Hierarchy/Time.lean) and [`P ⊊ EXP`](Complexity/Computability/Complexity/Classes/EXP.lean).
  - *Open target & completion criteria:* Extend the deterministic space hierarchy to **sublinear space bounds** (`log n ≤ g n` down to `o(n)`, reading the machine description directly from the read-only input tape without linear work-tape copying), prove the **nondeterministic space hierarchy**, and establish a linear-overhead simulation for a tight tape-indexed/`f log f` time hierarchy.
* **Reingold's theorem and symmetric logspace (`Complexity/Computability/Complexity/Classes/LogSpace/`):**
  - *Completed Foundation:* [`USTCON ∈ L` and `SL = L`](Complexity/Computability/Complexity/Classes/LogSpace/USTCON.lean) are proved for the adjacency-matrix encoding (with `SL` defined by logspace many-one reducibility to `USTCON` and unary-header injectivity in [List/Basic.lean](Complexity/Foundations/Data/List/Basic.lean)).
  - *Open target & completion criteria:* Define a native symmetric-Turing-machine model of `SL` and prove equivalence with `USTCON` reductions, plus an edge-list `USTCON` variant via logspace reduction.
* **`NL = coNL` and alternating characterizations of `PH`:**
  - *Completed Foundation:* `NL ⊆ P` ([LogSpace/PolyTime](Complexity/Computability/Complexity/Classes/LogSpace/PolyTime.lean)), `PH ⊆ PSPACE` ([Inclusions](Complexity/Computability/Complexity/Classes/Inclusions.lean)), and [`AP = PSPACE`](Complexity/Computability/Complexity/Classes/Alternation/Savitch.lean).
  - *Open target & completion criteria:* Complete native `NL = coNL` (see `Finishing the recovered developments` above) and formalize alternating time/space classes with bounded-alternation characterizations of `Σ_k^P` / `Π_k^P` / `PH`.
* **Descriptive complexity, uniform circuits, and relativized counting bridges:**
  - *Completed Foundation:* Canonical full-tuple ordered FO logspace transducer ([LogSpace/FirstOrder/Ordered/Reduction](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Reduction.lean)) and closed `#P`/`GapP`/`UP`/`FewP` machine characterizations ([SharpP/Characterization](Complexity/Computability/Complexity/Classes/SharpP/Characterization.lean), [SharpP/GapMachine](Complexity/Computability/Complexity/Classes/SharpP/GapMachine.lean), [UP/Machine](Complexity/Computability/Complexity/Classes/UP/Machine.lean), [FewP/Machine](Complexity/Computability/Complexity/Classes/FewP/Machine.lean)).
  - *Open target & completion criteria:* Complete restricted-domain/class-level ordered FO bridges, first-order `CVP` completeness, `DLOGTIME`-uniform circuit families, and relativized counting-machine characterizations (`#P^A`, `GapP^A`) in the [first continuing priority](#continuing-priorities).
* **Word-RAM and register-RAM models (`Complexity/Computability/WordRAM/`, `Complexity/Computability/RAM/`):**
  - *Completed Foundation:* The [bounded-word RAM](Complexity/Computability/WordRAM/Defs.lean) has [uniform instruction bounds](Complexity/Computability/WordRAM/Time.lean), [structured programs](Complexity/Computability/WordRAM/Structured.lean), [allocation/arrays](Complexity/Computability/WordRAM/Allocation.lean), a [linear-time element-distinctness client](Complexity/Algorithms/WordRAM/ElementDistinctness.lean), an [additive-memory compiler](Complexity/Computability/WordRAM/RAM.lean) into [`Cslib.RAM`](Complexity/Computability/RAM/Defs.lean) with [charged input preparation](Complexity/Computability/RAM/Input.lean) ([composed bridge](Complexity/Computability/WordRAM/RAMInput.lean)), and a [logarithmic-cost `Cslib.RAM` element-distinctness decider](Complexity/Algorithms/WordRAM/ElementDistinctnessRAM.lean) under the explicit preloaded length-bearing convention.
  - *Open target & completion criteria:* Certify wider-fragment and Turing-machine simulations; build a uniform width-selection conversion specifying an input-fit guarantee, computable size-based width selection, encoding conventions, and simulation overhead (noting the unrestricted converse is false because width can carry advice); transfer cell-probe lower bounds; and port the source's Horn-SAT, 2SAT, matching, and domino-tiling clients.
* **Single-tape simulations, Kolmogorov complexity, and Nisan–Wigderson codes:**
  - *Open target & completion criteria:* Certify quadratic single-tape Turing-machine simulations, machine-backed Kolmogorov and Nisan–Wigderson decoding results, concrete list-decodable codes for Nisan–Wigderson, and order-invariant descriptive-complexity queries.

Check [UPSTREAM.md](UPSTREAM.md) before starting these developments. The existing combinatorial or
machine-relative cores do not by themselves establish the missing uniform resource guarantees.

## Candidate proof improvements

These are experiments to validate, not claimed savings:

* Simplify `PairReady` and `clearedCfg` composition/preservation in tidy normal form without
  unfolding machine transitions globally.
* Factor indicator-expectation identities from PCP's second-moment calculation and recurring
  cardinality/logarithm conversions only when a second client benefits.

Judge changes on client readability, total proof burden and elaboration cost. Count proof fields
and helper APIs, and distinguish source-line counts from runtime or proof-term size.
[scripts/proof_lengths.py](scripts/proof_lengths.py) supports comparison against a Git revision.

Past measurements, reviews and proposals remain in the
[historical roadmap](https://github.com/SamuelSchlesinger/complexitylib2/blob/c88395234575284c2fe1e9e3619ead1c2f6fd7f3/ROADMAP.md).

