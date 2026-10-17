# Development roadmap

This file records outstanding work and the rationale needed to guide it. The
[README](README.md) introduces the library and links to completed reference developments;
[AGENTS.md](AGENTS.md) holds repository rules and design commitments;
[UPSTREAM.md](UPSTREAM.md) records upstream coordination and integration decisions.
Mathematical contracts and limitations belong beside their declarations.

## Current priorities

1. **General OWF → PRG.** Continue from the
   [pseudoentropy pair construction](Complexity/Crypto/Computational/Pseudoentropy/OneWay.lean)
   through amplification, extraction and the remaining security reductions. Reuse Goldreich–Levin,
   polynomial stretch and the adaptive oracle machinery. Once this is complete, compose with GGM
   to obtain general OWF → PRF. Individual efficient samplers do not settle the security theorem.

2. **Certified PCP construction.** The
   [gap theorem](Complexity/Computability/PCP/GapTheorem.lean) establishes combinatorial correctness
   and polynomial output size. Complete the executable reduction and its resource certificate:

   * give encoded graphs concrete indices, executable constraints and efficient enumeration,
     with a proved interpretation into the existing mathematical graphs;
   * parameterize the full preprocessing–powering–composition pipeline by an expander contract,
     carrying degree, spectral gap and construction certificates;
   * certify the [arithmetic expander family](Complexity/Foundations/Combinatorics/Expander/AffineFamily.lean)
     and one preprocessing transformation, with small executable clients, before extending the
     certificate to an amplification round and logarithmically many rounds;
   * charge copying, intermediate storage, lookup and every iteration, then prove the final
     verifier's randomness, query and indexing bounds.

   A rotation algorithm polynomial in the number of vertices can suffice here. Polynomial time
   in the bit length of a vertex name is a stronger, separate target. The current executable
   family has enormous constants; certified polynomial time and practical execution are distinct
   milestones.

3. **Improve certificate inference and loop contracts through clients.** Constructor, projection,
   lookup and composition rules should infer encodings for ordinary functional expressions.
   Test equivalent spellings and alternative encodings before adding tactic cases. Generalize
   reusable list, bounded-table, cache and nested-loop invariants where clients need them;
   callers supply the meaningful invariant, and automation handles routine encoding arithmetic.
   Use Cook–Levin and GGM as demanding regression clients. General open-program composition
   remains separate from the implemented
   [closed stateful substitution](Complexity/Computability/Probabilistic/OracleSimulation.lean).

4. **Reduce repeated proof bookkeeping.** Improve configuration views, tape partitions, handoff
   identities and preservation rules when they simplify multiple clients. Keep simplification
   narrowly oriented and machine transitions out of global simp. Share mathematical bookkeeping
   only with demonstrated reuse, counting helper proofs as part of the total cost.

## Architecture and later milestones

The deterministic backend is Christian Reitwiessner's tidy calculus, using explicit encodings
and upstream Turing machines. Typed functional programs and their computational certificates
build on it; the effectful machine reuses upstream configurations and actions. See the
[design commitments](AGENTS.md#design-commitments-do-not-re-litigate-casually) and module docstrings
for the contracts, and the upstream ledger for the status of copied dependencies.

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

## Historical evidence

Previous proof measurements, review records, port inventories and superseded design proposals
remain in the [roadmap at c883952](https://github.com/SamuelSchlesinger/complexitylib2/blob/c88395234575284c2fe1e9e3619ead1c2f6fd7f3/ROADMAP.md).
Record new batch-specific measurements, validation and review scope in commit or PR descriptions;
update this file when the remaining work or architectural decisions change.
