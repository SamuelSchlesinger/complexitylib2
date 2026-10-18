# Development roadmap

Outstanding work and the rationale needed to guide it. See the [README](README.md) for
completed reference developments.

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

* **Circuit mass production.** Integrate the existing constructions from
  [algebraic-circuits](https://github.com/SamuelSchlesinger/algebraic-circuits/blob/main/Algebraic/MassProduction.lean):
  the exponential copy range, sharp real-rate coefficient `1 / (1 - gamma) + o(1)`, and
  coefficient-one subexponential range. Preserve the exact gate-cost conventions and share
  sorting, lookup and routing with other circuit clients. Start from
  [padding](Complexity/Computability/Circuit/Boolean/MassProduction/Padding.lean),
  [synthesis](Complexity/Computability/Circuit/Boolean/MassProduction/Synthesis.lean), and
  [batched lookup](Complexity/Computability/Circuit/Boolean/BatchLookup.lean); their module
  documentation records the shared constructions and exact gate-cost contracts.
  Constructor runtime remains uncertified. The three mass-production results above remain to
  be ported.
* **Iterated-function circuits.** Port the
  [existing Lean development](https://github.com/SamuelSchlesinger/iterating-functions/blob/main/lean/README.md):
  square-root fixed-power bounds, input-time and batched iteration, navigation and hitting times,
  sparse-counter and affine-controller bounds, and hard-power counting. It already uses CSLib
  circuits and some mass-production infrastructure. Nonuniform circuit existence does not
  certify the preprocessing algorithm's runtime.
* **Fagin's theorem.** Complete the connection between ESO-definable queries on finite relational
  structures and NP. V2 currently has the logical semantics and closure results. V1 supplies the
  [ESO-to-NP direction](https://github.com/SamuelSchlesinger/complexitylib/blob/dev/Complexitylib/DescriptiveComplexity/SecondOrder/PolynomialTime.lean);
  port its encoded structures and efficient certificate checker, then construct the converse
  tableau interpretation. The converse is new work even relative to V1.
* **Further algebraic results.** Carry over the existing extractor and rational-matrix
  hitting-list developments, recording each endpoint's remaining hypotheses.
* **Weighted threshold representations.** Complete the remaining results in
  [Threshold Circuits as Decision Trees and Finite-State Programs](https://github.com/SamuelSchlesinger/threshold-circuits).
  The exact [inner-product activity bound](Complexity/Computability/Circuit/Boolean/WeightedThreshold/InnerProduct.lean)
  and [native scalar-capacity bound](Complexity/Computability/Circuit/Boolean/WeightedThreshold/CapacityCircuit.lean)
  are proved. Port v1's remaining gate-count consequences and explicit source-reduction family.
  Further manuscript work includes scalar enumerative coding, pending-bias simulation,
  entropy and asymptotic activity bounds, geometric cutting, integer-summary counting,
  and quadratic-potential representations.

Further metacomplexity ports are outside the current scope: the circuitized anti-checker,
hardness-magnification argument and MINKT/MINCKT developments will not be carried over. Retain
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

* machine-level hierarchy theorems and `P ⊊ EXP`; a tight tape-indexed hierarchy needs a separate
  linear-overhead simulation, and an `f log f` hierarchy needs the corresponding simulation bound;
* logspace composition, Savitch, `NL ⊆ P`, `NL = coNL`, `PH ⊆ PSPACE` and Sipser–Lautemann;
* nondeterministic-machine/verifier equivalence, efficient `SAT ≤ 3SAT`, single-tape simulation,
  and machine-backed Kolmogorov and Nisan–Wigderson decoding results;
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
