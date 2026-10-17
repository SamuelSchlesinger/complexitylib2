# Development roadmap

Outstanding work and the rationale needed to guide it. See the [README](README.md) for
completed reference developments.

## Current priorities

1. **Certified PCP construction.** The
   [gap theorem](Complexity/Computability/PCP/GapTheorem.lean) establishes combinatorial correctness
   and polynomial output size. Complete the executable reduction and its resource certificate:

   * connect the [certified initial 3-SAT graph](Complexity/Computability/PCP/Encoded/ThreeSAT.lean)
     to an efficient SAT-to-3CNF conversion and the
     [concrete gap amplifier](Complexity/Computability/PCP/Encoded/Amplification/Arithmetic.lean);
   * prove the final verifier's randomness, query and indexing bounds.

   The rotation certificate is polynomial in the number of vertices, which can suffice here.
   Polynomial time in the bit length of a vertex name is a stronger, separate target. The
   certified family has enormous constants; practical execution remains a separate milestone.

2. **Improve certificate inference and loop contracts through clients.** Constructor, projection,
   lookup and composition rules should infer encodings for ordinary functional expressions.
   Test equivalent spellings and alternative encodings before adding tactic cases. Generalize
   reusable list, bounded-table, cache and nested-loop invariants where clients need them;
   callers supply the meaningful invariant, and automation handles routine encoding arithmetic.
   Use Cook–Levin and GGM as demanding regression clients. General open-program composition
   remains separate from the implemented
   [closed stateful substitution](Complexity/Computability/Probabilistic/OracleSimulation.lean).

3. **Reduce repeated proof bookkeeping.** Improve configuration views, tape partitions, handoff
   identities and preservation rules when they simplify multiple clients. Keep simplification
   narrowly oriented and machine transitions out of global simp. Share mathematical bookkeeping
   only with demonstrated reuse, counting helper proofs as part of the total cost.

## Later milestones

Polynomial efficiency is sufficient for many reductions, but does not establish tight time or
space bounds. Further class-level work needs resource certificates for the actual algorithms:

* machine-level hierarchy theorems and `P ⊊ EXP`; a tight tape-indexed hierarchy needs a separate
  linear-overhead simulation, and an `f log f` hierarchy needs the corresponding simulation bound;
* logspace composition, Savitch, `NL ⊆ P`, `PH ⊆ PSPACE` and Sipser–Lautemann;
* nondeterministic-machine/verifier equivalence, efficient `SAT ≤ 3SAT`, single-tape simulation,
  and machine-backed Kolmogorov and Nisan–Wigderson decoding results;
* concrete list-decodable codes for Nisan–Wigderson, order-invariant descriptive-complexity
  queries, and the remaining algebraic results.

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
