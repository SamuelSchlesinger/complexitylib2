/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Crypto.Computational.GMW.Simulator
public import Complexity.Crypto.Computational.GMW.Soundness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# Computational zero-knowledge interactive proofs for NP

Goldreich, Micali, and Wigderson [GoldreichMicaliWigderson1991] proved that if one-way functions
exist, then every language in `NP` has a computational zero-knowledge interactive proof system.
This module defines computational zero-knowledge interactive proofs (`ZeroKnowledgeProof`) and
constructs such a proof system for `ThreeSAT` and hence for every language in `NP` via
`ThreeSAT_npHard` and Naor's bit commitment scheme [Naor1991]
(`Complexity.Crypto.Computational.Commitment`).

### Protocol design and source credit

While the theorem that every language in `NP` has a computational zero-knowledge interactive proof
system from one-way functions is due to Goldreich, Micali, and Wigderson
[GoldreichMicaliWigderson1991] using Naor's commitment scheme [Naor1991], the concrete underlying
`ThreeSAT` protocol formalized in `Complexity.Crypto.Computational.GMW` is a direct **3-copy
masked-3SAT truth-table commitment protocol** rather than GMW's original 3-coloring protocol:
each of 3 parallel copies commits to a random variable mask, the XOR-masked assignment, and the
8-entry masked truth table of each clause, and a random 3-bit challenge selects for each copy
whether to open the mask and full truth tables or the masked assignment and the active truth-table
entries.

### Uniform zero-knowledge and witness-relation conventions

* **Uniform zero-knowledge (`ZeroKnowledgeProof.zero_knowledge`).** Matching the library's uniform
  strict-PPT cryptographic conventions (`ComputationallyIndistinguishable`), `zero_knowledge`
  quantifies over uniform strict oracle PPT malicious verifiers `Vstar` and deterministic
  polynomial-time-generable families of instances `a : ℕ → α`, valid witnesses
  `w : ℕ → List Bool` (`∀ n, isWitness (a n) (w n) = true`), and auxiliary inputs
  `z : ℕ → List Bool` (`ComputableTidilyInPolyTime · encUnary _`), rather than non-uniformly over
  arbitrary sequences `(x, w) ∈ R_L` and `z ∈ {0, 1}^*`. Fixed-instance zero-knowledge
  (`ZeroKnowledgeProof.zero_knowledge_const`) is an immediate corollary for constant families
  `fun _ => a` and `fun _ => w`.
  The separate finite theorem `GMW.gmwView_advantage_le` applies pointwise without generation
  assumptions. Its full-input clock and `GMW.gmwView_negligible_of_advice_prg` expose the stronger
  advice-PRG premise needed for arbitrary polynomially bounded families; they do not strengthen
  this bundled uniform-family field or derive that premise from uniform one-wayness.
* **Bundled witness relation (`ZeroKnowledgeProof.isWitness`).** `ZeroKnowledgeProof` bundles its
  own polynomial-time witness predicate `isWitness : α → List Bool → Bool` characterizing `A`
  (`mem_iff_exists_witness`). No witness-length bound is imposed, so `isWitness` by itself need not
  be an `NP` relation; membership in `IP` (`mem_IP`) does not need one, and in `zero_knowledge`
  the witness family `w : ℕ → List Bool` is polynomial-time-generable in `1^n`. In
  `PseudorandomGenerator.zeroKnowledgeProofOfReduction` and
  `PseudorandomGenerator.exists_zeroKnowledgeProof_of_mem_NP`, the bundled predicate
  `isWitness a w := ThreeSAT.verifier (f a, w)` checks a `ThreeSAT` witness for the Karp-reduced
  formula `f a` rather than a witness for the original `NP` verifier of `A`.

## Main definitions

* `Cslib.Crypto.ZeroKnowledgeProof`: a computational zero-knowledge interactive proof system for a
  language `A`, bundling a uniform strict oracle PPT verifier, an honest prover with a uniform
  strict PPT interaction realization, perfect completeness, soundness `1 / 3` against unbounded
  provers, and uniform zero-knowledge with poly-time-generable auxiliary input.
* `Cslib.Crypto.PseudorandomGenerator.zeroKnowledgeProofOfReduction`,
  `Cslib.Crypto.PseudorandomGenerator.zeroKnowledgeProofThreeSAT`: GMW zero-knowledge proof
  systems for any language Karp-reducible to `ThreeSAT` and for `ThreeSAT` itself.

## Main results

* `Cslib.Crypto.ZeroKnowledgeProof.isInteractiveProof`, `Cslib.Crypto.ZeroKnowledgeProof.mem_IP`:
  every language with a `ZeroKnowledgeProof` belongs to `IP`.
* `Cslib.Crypto.ZeroKnowledgeProof.zero_knowledge_const`: fixed-instance computational
  zero-knowledge for any fixed instance and valid witness.
* `Cslib.Crypto.PseudorandomGenerator.exists_zeroKnowledgeProof_of_mem_NP`: any pseudorandom
  generator with stretch at least `3 * k + 1` yields a computational zero-knowledge proof system
  for every language in `NP`.
* `Cslib.Crypto.OneWay.exists_zeroKnowledgeProof_of_mem_NP`: if a one-way function exists, every
  language in `NP` has a computational zero-knowledge proof system.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001], Chapter 4.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Complexity Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime
open scoped NNReal ENNReal

/-- A computational zero-knowledge interactive proof system for a language `A : Set α` (with
instance encoding `enc : α ↪ List Bool`), indexed by a security parameter `n : ℕ` [Goldreich,
Micali, and Wigderson][GoldreichMicaliWigderson1991].

* `verifier n a`: the honest verifier's interactive program on security parameter `n` and
  instance `a`, certified uniform strict oracle PPT in `(1^n, a)` by `isOraclePPT_verifier`.
* `prover n a w`: the honest prover strategy on security parameter `n`, instance `a`, and
  witness `w`, certified efficient by `interact`, `eval_interact`, and `isPPT_interact`.
* `isWitness a w`: the bundled polynomial-time witness predicate characterizing membership in `A`
  (`mem_iff_exists_witness`). No witness-length bound is imposed, so `isWitness` by itself need
  not be an `NP` relation (in `zero_knowledge`, `w` is polynomial-time-generable in `1^n`). When
  constructed via a Karp reduction `f : α → CNF ℕ` to `ThreeSAT`
  (`PseudorandomGenerator.zeroKnowledgeProofOfReduction`),
  `isWitness a w` is `ThreeSAT.verifier (f a, w)`, checking a `ThreeSAT` witness for `f a`.
* `complete` and `sound`: completeness `1` for valid witnesses and soundness error at most `1 / 3`
  against all computationally unbounded stateful provers `P : Prover Unit`.
* `zero_knowledge`: **uniform zero-knowledge with poly-time-generable auxiliary input**. For every
  uniform strict oracle PPT malicious verifier `Vstar` (taking security parameter `n`, instance `a`,
  and auxiliary input `z`), there is a uniform strict PPT simulator `S` (taking `(1^n, a, z)`
  without any witness) whose output ensemble is computationally indistinguishable from the real
  interaction output across all deterministic polynomial-time-generable families of instances
  `a : ℕ → α`, valid witnesses `w : ℕ → List Bool`, and auxiliary inputs `z : ℕ → List Bool`
  (`ComputableTidilyInPolyTime · encUnary _`). -/
structure ZeroKnowledgeProof {α : Type} (enc : α ↪ List Bool) (A : Set α) where
  /-- The honest verifier, indexed by security parameter `n` and instance `a`. -/
  verifier : ℕ → α → WordOracleComp Unit Bool
  /-- The honest prover strategy, taking security parameter `n`, instance `a`, and witness `w`. -/
  prover : ℕ → α → List Bool → Prover Unit
  /-- The polynomial-time witness check used by the honest prover. -/
  isWitness : α → List Bool → Bool
  /-- `isWitness` is computable in polynomial time. -/
  polyTime_isWitness :
    ComputableTidilyInPolyTime (fun p : α × List Bool => isWitness p.1 p.2)
      (encPair enc encBits) encBool
  /-- `a ∈ A` if and only if some witness `w` satisfies `isWitness a w = true`. -/
  mem_iff_exists_witness : ∀ a, a ∈ A ↔ ∃ w, isWitness a w = true
  /-- The honest verifier is uniform strict oracle PPT in `(1^n, a)`. -/
  isOraclePPT_verifier :
    IsOraclePPTOn (encPair encUnary enc) encBool (fun p : ℕ × α => verifier p.1 p.2)
  /-- The PPT program realizing the honest prover's interaction with a verifier program. -/
  interact : ℕ → α → List Bool → WordOracleComp Unit (List Bool) → ProbComp (List Bool)
  /-- `interact` has the exact output distribution of `prover.run`. -/
  eval_interact : ∀ n a w prog,
    ProbComp.eval (interact n a w prog) =
      ((prover n a w).run prog (prover n a w).init).map Prod.fst
  /-- Running any uniform strict oracle PPT verifier against the honest prover is uniform strict
  PPT in `(1^n, a, w, z)`. -/
  isPPT_interact :
    ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
      IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2) →
      IsPPTOn (encPair encUnary (encPair enc (encPair encBits encBits))) encBits
        (fun p : ℕ × α × List Bool × List Bool =>
          interact p.1 p.2.1 p.2.2.1 (Vstar p.1 p.2.1 p.2.2.2))
  /-- Perfect completeness: for every valid witness `w` of `a`, the honest prover convinces the
  honest verifier with probability `1`. -/
  complete : ∀ n a w, isWitness a w = true → acceptProb (verifier n a) (prover n a w) = 1
  /-- Soundness: for every `a ∉ A` and every computationally unbounded stateful prover `P`, the
  verifier accepts with probability at most `1 / 3`. -/
  sound : ∀ n, ∀ a ∉ A, ∀ P : Prover Unit, acceptProb (verifier n a) P ≤ 1 / 3
  /-- Uniform computational zero-knowledge with poly-time-generable auxiliary input against all
  uniform strict oracle PPT malicious verifiers, quantified over polynomial-time-generable
  families of instances `a`, valid witnesses `w`, and auxiliary inputs `z`. -/
  zero_knowledge :
    ∀ Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool),
      IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2) →
      ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
        IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
          (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
        ∀ (a : ℕ → α) (w z : ℕ → List Bool),
          ComputableTidilyInPolyTime a encUnary enc →
          ComputableTidilyInPolyTime w encUnary encBits →
          ComputableTidilyInPolyTime z encUnary encBits →
          (∀ n, isWitness (a n) (w n) = true) →
          ComputationallyIndistinguishable
            (fun n => ((prover n (a n) (w n)).run (Vstar n (a n) (z n))
              (prover n (a n) (w n)).init).map Prod.fst)
            (fun n => ProbComp.eval (S n (a n) (z n)))

namespace ZeroKnowledgeProof

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- At every security parameter `n`, the honest verifier of a zero-knowledge proof system is an
interactive proof for `A` with completeness `2 / 3` and soundness `1 / 3`. -/
theorem isInteractiveProof (zk : ZeroKnowledgeProof enc A) (n : ℕ) :
    IsInteractiveProof (zk.verifier n) A (2 / 3) (1 / 3) where
  complete a ha := by
    obtain ⟨w, hw⟩ := (zk.mem_iff_exists_witness a).mp ha
    refine ⟨zk.prover n a w, ?_⟩
    rw [zk.complete n a w hw]
    exact ENNReal.div_le_of_le_mul (by norm_num)
  sound a ha P := zk.sound n a ha P

/-- Every language with a zero-knowledge interactive proof system belongs to `IP`. -/
theorem mem_IP (zk : ZeroKnowledgeProof enc A) : A ∈ IP enc := by
  refine ⟨zk.verifier 0, ?_, zk.isInteractiveProof 0⟩
  have h := zk.isOraclePPT_verifier
  fun_prop

/-- Fixed-instance computational zero-knowledge: for every fixed instance `a` and valid witness `w`
(`zk.isWitness a w = true`), and every polynomial-time auxiliary input family `z : ℕ → List Bool`,
the real interaction output and simulator output are computationally indistinguishable. -/
theorem zero_knowledge_const (zk : ZeroKnowledgeProof enc A)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool => Vstar p.1 p.2.1 p.2.2)) :
    ∃ S : ℕ → α → List Bool → ProbComp (List Bool),
      IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
        (fun p : ℕ × α × List Bool => S p.1 p.2.1 p.2.2) ∧
      ∀ a w (z : ℕ → List Bool),
        zk.isWitness a w = true →
        ComputableTidilyInPolyTime z encUnary encBits →
        ComputationallyIndistinguishable
          (fun n => ((zk.prover n a w).run (Vstar n a (z n))
            (zk.prover n a w).init).map Prod.fst)
          (fun n => ProbComp.eval (S n a (z n))) := by
  obtain ⟨S, hS_ppt, hS_zk⟩ := zk.zero_knowledge Vstar hV
  exact ⟨S, hS_ppt, fun a w z hw hz =>
    hS_zk (fun _ => a) (fun _ => w) z (const a) (const w) hz (fun _ => hw)⟩

end ZeroKnowledgeProof

/-- Construct the Goldreich–Micali–Wigderson zero-knowledge proof system for any language `A` with
a polynomial-time many-one reduction `f : α → CNF ℕ` to `ThreeSAT`, using a pseudorandom generator
with stretch at least `3 * k + 1` and the 3-copy masked-3SAT commitment protocol in
`Cslib.Crypto.GMW`. The bundled witness check `isWitness a w` is `ThreeSAT.verifier (f a, w)` on
the reduced formula `f a`. -/
noncomputable def PseudorandomGenerator.zeroKnowledgeProofOfReduction
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    {f : α → CNF ℕ} (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hred : ∀ a, a ∈ A ↔ f a ∈ ThreeSAT) :
    ZeroKnowledgeProof enc A where
  verifier := GMW.gmwVerifier generator length f
  prover n a w := GMW.gmwProver generator (n + 7) (length (n + 7)) (f a) w
  isWitness a w := ThreeSAT.verifier (f a, w)
  polyTime_isWitness := by fun_prop
  mem_iff_exists_witness a := by
    rw [hred a]
    refine ⟨fun ha => ?_, fun ⟨w, hw⟩ => ?_⟩
    · obtain ⟨w, _, hw⟩ := (ThreeSAT.isVerifier (f a)).mp ha
      exact ⟨w, hw⟩
    · simp only [ThreeSAT.verifier, SAT.verifier, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] at hw
      exact ⟨hw.1, SAT.assignment (f a) w, hw.2⟩
  isOraclePPT_verifier := GMW.isOraclePPTOn_gmwVerifier hG.polyTime hG.length_eq hf
  interact n a w prog := GMW.gmwInteract generator (n + 7) (length (n + 7)) (f a) w prog
  eval_interact n a w prog := GMW.eval_gmwInteract generator (n + 7) (length (n + 7)) (f a) w prog
  isPPT_interact _ hV := GMW.isPPTOn_gmwInteract hG.polyTime hG.length_eq hf hV
  complete n a _ hw := GMW.acceptProb_gmwVerifier_gmwProver hG.length_eq f n a hw
  sound n a ha P :=
    GMW.acceptProb_gmwVerifier_le hG.length_eq hstretch f n a (mt (hred a).mpr ha) P
  zero_knowledge Vstar hV :=
    ⟨GMW.gmwSimulator generator length f Vstar,
      GMW.isPPTOn_gmwSimulator hG.polyTime hG.length_eq hf hV,
      fun _ _ _ ha hw_comp hz hw_sat =>
        GMW.gmwView_indistinguishable_gmwSimulator hG hf hV ha hw_comp hz hw_sat⟩

/-- The Goldreich–Micali–Wigderson computational zero-knowledge proof system for `ThreeSAT`, built
from any pseudorandom generator with stretch at least `3 * k + 1` via the 3-copy masked-3SAT
commitment protocol in `Cslib.Crypto.GMW`. -/
noncomputable def PseudorandomGenerator.zeroKnowledgeProofThreeSAT
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k) :
    ZeroKnowledgeProof encCNF ThreeSAT :=
  hG.zeroKnowledgeProofOfReduction hstretch (by fun_prop) (fun _ => Iff.rfl)

/-- **Goldreich–Micali–Wigderson theorem (from a pseudorandom generator).** Given a pseudorandom
generator with stretch at least `3 * k + 1` (such as `fun k => 3 * k + 1`), every language
`A ∈ NP enc` has a computational zero-knowledge interactive proof system
[Goldreich, Micali, and Wigderson][GoldreichMicaliWigderson1991]. -/
theorem PseudorandomGenerator.exists_zeroKnowledgeProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hstretch : ∀ k, 3 * k + 1 ≤ length k)
    (hA : A ∈ NP enc) :
    Nonempty (ZeroKnowledgeProof enc A) := by
  obtain ⟨f, hf, hred⟩ := ThreeSAT_npHard enc A hA
  exact ⟨hG.zeroKnowledgeProofOfReduction hstretch hf.tidy hred⟩

/-- **Goldreich–Micali–Wigderson theorem (from a one-way function).** If a one-way function exists,
then every language `A ∈ NP enc` has a computational zero-knowledge interactive proof system
[Goldreich, Micali, and Wigderson][GoldreichMicaliWigderson1991], in the uniform-family sense of
`ZeroKnowledgeProof.zero_knowledge`: instances, witnesses and auxiliary inputs range over
polynomial-time-generable families rather than arbitrary ones. -/
theorem OneWay.exists_zeroKnowledgeProof_of_mem_NP
    {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {f : List Bool → List Bool} (hf : OneWay f) (hA : A ∈ NP enc) :
    Nonempty (ZeroKnowledgeProof enc A) := by
  obtain ⟨G, hG⟩ := hf.exists_pseudorandomGenerator_three_mul
  exact hG.exists_zeroKnowledgeProof_of_mem_NP (fun _ => le_rfl) hA

end Cslib.Crypto
