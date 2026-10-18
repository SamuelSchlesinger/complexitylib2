# Development roadmap

Outstanding work and the rationale needed to guide it. See the [README](README.md) for
completed reference developments.

## Current priorities

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
   construction and measure complete reductions. The existing rotation certificate is
   polynomial in the number of vertices; polynomial time in the bit length of a vertex name
   remains a stronger, separate target.

3. **Reduce repeated proof bookkeeping.** Improve configuration views, tape partitions, handoff
   identities and preservation rules when they simplify multiple clients. Keep simplification
   narrowly oriented and machine transitions out of global simp. Share mathematical bookkeeping
   only with demonstrated reuse, counting helper proofs as part of the total cost.

## Remaining theorem developments

The port still includes substantial mathematical developments beyond the completed reference
results. Track these by their public theorems, rather than by source-file counts:

* **Circuit mass production.** Integrate the existing constructions from
  [algebraic-circuits](https://github.com/SamuelSchlesinger/algebraic-circuits/blob/main/Algebraic/MassProduction.lean):
  the exponential copy range, sharp real-rate coefficient `1 / (1 - gamma) + o(1)`, and
  coefficient-one subexponential range. Preserve the exact gate-cost conventions and share
  sorting, lookup and routing with other circuit clients. The native replication and weighted-cost
  interface, including the [eventual-to-all-length padding theorem](Complexity/Computability/Circuit/Boolean/MassProduction/Padding.lean),
  [finite Shannon synthesis](Complexity/Computability/Circuit/Boolean/MassProduction/Synthesis.lean),
  [stable compare-exchange](Complexity/Computability/Circuit/Boolean/CompareSwap.lean),
  and [Batcher sorting](Complexity/Computability/Circuit/Boolean/Sorting.lean) are in place.
  Sorting has key-order, complete-record permutation and exact weighted-cost theorems; its
  [computed-key wrapper](Complexity/Computability/Circuit/Boolean/KeyedSort.lean) preserves
  complete records and charges key computation once per record. The shared
  [segmented propagation circuit](Complexity/Computability/Circuit/Boolean/Propagation.lean)
  has exact linear gate cost and connected-source semantics, including sorted equal-key runs.
  The [record broadcast circuit](Complexity/Computability/Circuit/Boolean/Broadcast.lean)
  preserves headers and routing metadata, shares adjacent-key tests across value bits, and
  copies a unique matching source to each sorted destination. The
  [two-sort router](Complexity/Computability/Circuit/Boolean/Routing.lean) preserves headers,
  restores uniquely keyed requests to their input-determined ranks, and has exact gate costs.
  Constructor runtime is not certified. Concrete batched lookup layouts, padding and bounds,
  and the three mass-production results above remain to be ported.
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
* **Further metacomplexity and algebraic results.** Carry over the existing extractor,
  circuitized anti-checker, MINKT/MINCKT and rational-matrix hitting-list developments, recording
  each endpoint's remaining hypotheses. The current anti-checker existence theorem does not
  include the efficient generator or complete hardness-magnification argument; the latter also
  has unfinished quantitative counting work in V1.

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
