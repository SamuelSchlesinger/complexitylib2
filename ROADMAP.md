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

### Extend the mathematical canon

This map adds long-term directions to the concrete developments below. It follows the breadth of
[ECCC's scope](https://eccc.weizmann.ac.il/colloquium/call_for_papers/) and the Zoo, rather than the
contents of the original port. Entries are targets for coverage audits and substantial theorem
developments, not assertions that every prerequisite is missing or assignments to current workers.

| Area | Coverage to establish or extend |
| --- | --- |
| Structural complexity | Time/space and exponential hierarchies; oracle and advice classes; unambiguous and promise classes; completeness, padding, self-reducibility, Ladner's theorem, relativization and oracle separations. Preserve each reduction's resource bound. |
| Space and alternation | Building on native `NPSPACE = PSPACE`, TQBF completeness and `NL ⊆ P`: the [machine-class milestones](#machine-class-milestones), alternation and `AP = PSPACE`. Distinguish polynomial-space simulation from sharp bounds for sublinear space. |
| Counting and modular classes | Extend `#P`, `GapP` and `PP` with counting reductions and machine characterizations, permanent completeness, parity/modular and counting hierarchies, Toda's theorem, and the oracle-algorithm form of Stockmeyer approximate counting. |
| Interactive and probabilistic proofs | Efficient interactive verifier semantics, sumcheck and arithmetization, MA/AM and public/private coins, `IP = PSPACE`, multiprover systems, zero knowledge and simulation. Reuse the existing PCP and probabilistic foundations. |
| Boolean circuits and parallel computation | Complete the [Jukna coverage](#jukna-coverage), uniform/nonuniform NC/AC/TC and related classes, circuit-to-machine bridges, algorithm-to-lower-bound arguments and barriers such as natural proofs and algebrization. |
| Algebraic and arithmetic complexity | VP/VNP, algebraic reductions and complete polynomials; determinant/permanent and formula/branching-program models; identity testing and hitting sets; tensor and rank methods, including explicit field and characteristic assumptions. |
| Approximation and constraint satisfaction | Gap and approximation-preserving reductions, APX/PTAS/FPTAS, canonical inapproximability consequences of PCP, CSP classifications and relaxation gaps. State assumptions such as the Unique Games Conjecture explicitly. |
| Pseudorandomness and coding | Hardness versus randomness, space-bounded generators, extractors/condensers, limited independence, explicit expanders, and list/local decoding. Separate finite combinatorial guarantees from uniform construction and decoding costs. |
| Complexity-theoretic cryptography | Extend the existing OWF/PRG/PRF results with reusable adaptive reductions, commitments, zero knowledge, hard-core and hardness-amplification methods, and connections to learning and average-case hardness. |
| Communication, queries and data structures | Randomized and multiparty protocols, discrepancy and information complexity, direct-sum/product results, lifting theorems, and reductions to streaming, sketching and cell-probe lower bounds. Reuse upstream query models. |
| Proof complexity | Extend resolution soundness/completeness with proof length, width and space, pigeonhole/Tseitin lower bounds, Cook–Reckhow systems and simulations, Frege, cutting planes, polynomial calculus and sum-of-squares. |
| Average-case complexity and learning | Distributional problems and reductions, samplability, average-to-worst-case connections, PAC/agnostic/SQ learning, learning lower bounds, compression and refutation. Existing cryptographic learners are starting points, not coverage of learning theory. |
| Property and distribution testing | Distance and access models, one/two-sided and tolerant testing, query/sample bounds, canonical graph/algebraic/distribution testers and lower bounds. |
| Fine-grained and parameterized complexity | Fine-grained reductions and consequences conditional on ETH/SETH and other named hypotheses; FPT/XP, W/A hierarchies, kernelization, parameter-preserving reductions and lower bounds. |
| Total search and computational games | FNP/TFNP and canonical subclasses such as PLS, PPAD, PPA, PPP and CLS; local search, fixed-point and equilibrium problems, with explicit totality and solution-preserving reductions. |
| Logic and descriptive complexity | Building on [Fagin's theorem](Complexity/Computability/Complexity/Fagin/Converse.lean): logical characterizations of additional resource classes, fixed-point and order-invariant queries, and uniform translations between syntax, structures and algorithms. |
| Kolmogorov complexity and metacomplexity | Machine-backed descriptions/decoders and invariance, resource-bounded descriptions, MCSP variants and connections to learning, cryptography and lower bounds. Revisit deferred results through independently reviewed developments. |
| Quantum complexity | Reusable circuit/channel/measurement semantics, uniformity and approximation costs, BQP/QMA and related query, communication and interactive classes, amplification, containments and complete problems. Reuse suitable quantum foundations rather than create incompatible models. |

### Coverage priorities

A weighted audit of the results that complexity papers most often cite in their preliminaries
(October 2026) ranks the following developments by citation gain per unit of work. Each entry
names its endpoints; verify statements against the primary sources when starting one.

1. **Probability toolkit.** Multiplicative Chernoff bounds, k-wise independence and its moment
   tail bound, the Lovász Local Lemma, KL divergence with Pinsker and Shearer, min-entropy and
   flat sources, and McDiarmid's inequality.
2. **Resource-class spine.** Parametric `DTIME`, `NTIME`, `DSPACE`, `NSPACE` and `BPTIME`; `E`,
   `NEXP` and `ZPP`; the standard inclusions; class-level error reduction; padding; and the
   polynomial-hierarchy collapse lemmas.
3. **Circuits as data.** A binary circuit encoding with certified evaluation, CircuitSAT
   NP-completeness and `MCSP ∈ NP`, search-to-decision for SAT, Karp–Lipton, Kannan and Meyer.
4. **Natural proofs.** Natural properties and the Razborov–Rudich barrier from pseudorandom
   function families.
5. **Communication complexity.** Rectangles, fooling sets and the rank bound; randomized protocols
   and Newman's theorem; discrepancy and inner product; set disjointness.
6. **Query complexity.** Exact and approximate degree, the Nisan–Szegedy relations, symmetrization,
   Huang's sensitivity theorem and randomized query complexity.
7. **Algebraic codes.** Reed–Solomon and Reed–Muller distance, the Singleton and Johnson bounds,
   unique and list decoding, concatenation and local decoding.
8. **Fine-grained hypotheses.** ETH, SETH and the orthogonal-vectors hypothesis, with the
   consequences that follow from the formalized sparsification lemma.
9. **Isolation and counting.** Valiant–Vazirani, the isolation lemma, `⊕P`, Toda's theorem and
   Stockmeyer's approximate counting at class level.
10. **Hardness amplification.** The hard-core lemma, Yao's XOR lemma and the
    Impagliazzo–Wigderson derandomization endpoints, building on Nisan–Wigderson.

Further priorities are small-bias spaces, expander walks and extractors; `NL = coNL` and the
space hierarchy; sumcheck, Arthur–Merlin protocols and `IP = PSPACE`; hypercontractivity and
influence theorems; and inapproximability consequences of the PCP theorem.

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

1. **Complete theorem ports using the existing certificate APIs.** Extend automation when a
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

2. **Practical PCP and expander constructions.** The
   [PCP theorem](Complexity/Computability/PCP/Completeness.lean) includes certified construction
   and verification, but the fixed parameters are enormous. Develop a reasonably runnable
   construction and measure complete reductions. The
   [six-query tester](Complexity/Computability/PCP/SelectedComposition.lean) now feeds the shared
   executable composition compiler and the full reduction, with a 128-symbol output alphabet and
   a certified amplification gap of `2^-61`. The final binary verifier also encodes labels and
   repeats its check, so it does not have a six-query bound. The existing rotation certificate is
   polynomial in the number of vertices; polynomial time in the bit length of a vertex name
   remains a stronger, separate target.

3. **Reduce repeated proof bookkeeping.** Improve configuration views, tape partitions, handoff
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
  square-root fixed-power bounds, input-time and batched iteration, navigation and hitting times,
  sparse-counter and affine-controller bounds, and hard-power counting. It already uses CSLib
  circuits and some mass-production infrastructure. The
  [functional-graph foundations](Complexity/Foundations/Combinatorics/FunctionalGraph.lean)
  (transient and cycle structure, checkpoint packing, exact distinct-power counts) and
  [native circuit iteration](Complexity/Computability/Circuit/Iteration.lean) with retained
  orbits are in place, as is the [fixed-power theorem](Complexity/Computability/Circuit/Boolean/Iteration.lean)
  with its encoded and record forms; the remaining source developments build on it. Nonuniform
  circuit existence does not certify the preprocessing algorithm's runtime.
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

The current V1 port excludes the circuitized anti-checker, hardness-magnification argument and
MINKT/MINCKT developments. The long-term canon above includes metacomplexity; those results should
return as independently scoped, reviewed developments rather than automatic legacy ports. Retain
existing checked [MCSP definitions](Complexity/Computability/MCSP/Basic.lean),
[succinct variants](Complexity/Computability/MCSP/Succinct.lean),
[Shannon bounds](Complexity/Computability/MCSP/Shannon.lean) and
[anti-checker existence](Complexity/Computability/MCSP/AntiChecker.lean).
These do not include an efficient anti-checker generator or a hardness-magnification theorem.

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
| 18–19: proof complexity | [Resolution soundness and completeness](Complexity/Logics/Propositional/Resolution.lean) | Add resolution complexity bounds and cutting-plane proofs. |
| 20: barriers and further methods | [Fusion API](Complexity/Computability/Circuit/Fusion/Basic.lean), [Nisan–Wigderson core](Complexity/Computability/Kolmogorov/NisanWigderson.lean) | Match the book's generator, natural-proof, fusion and indirect lower-bound results. |
| Appendix A: mathematical prerequisites | Mathlib and `Complexity/Foundations/` | Reuse existing statements and fill dependencies as clients require them. |

## Machine-class milestones

Polynomial efficiency is sufficient for many reductions, but does not establish tight time or
space bounds. Further class-level work needs resource certificates for the actual algorithms:

* the space hierarchy, building on the [time hierarchy](Complexity/Computability/Complexity/Classes/Hierarchy/Time.lean)
  and `P ⊊ EXP`; a tight tape-indexed hierarchy needs a separate linear-overhead simulation, and
  an `f log f` time hierarchy needs the corresponding simulation bound;
* `NL = coNL` and `PH ⊆ PSPACE`, building on the landed logspace composition, `NL ⊆ P`, Savitch
  and Sipser–Lautemann;
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
