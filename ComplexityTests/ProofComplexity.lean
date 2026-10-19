/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.ProofSystem
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-!
# Tests: proof systems

A concrete proof system on all words and its simulations; the proof system of the `SAT` verifier
on a concrete proof and a malformed word; the existence of a polynomially bounded proof system for
`SAT`; and the axioms of the headline theorems.
-/

namespace ComplexityTests.ProofComplexity

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Proof systems and simulations -/

/-- Every word proves itself: a polynomially bounded proof system for the set of all words. -/
def wordsProofSystem : ProofSystem encBits Set.univ where
  toFun π := π
  computable := .id'
  range_eq := Set.range_id

example : wordsProofSystem [true, false] = [true, false] := rfl

example : wordsProofSystem.PolynomiallyBounded :=
  ⟨.X, fun a _ => ⟨a, rfl, by simp [encBits]⟩⟩

example : wordsProofSystem.PSimulates wordsProofSystem := .refl

example : wordsProofSystem.Simulates wordsProofSystem := ProofSystem.PSimulates.refl.simulates

/-! ### The proof system of the `SAT` verifier -/

/-- Formulas in conjunctive normal form are decoded along their encoding. -/
private def cnfDecoder : Decoder encCNF := .list (.list (.pair .nat .bool))

/-- `(x₀ ∨ ¬x₁) ∧ x₁`. -/
private def φ : CNF ℕ := [[(0, true), (1, false)], [(1, true)]]

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- Proofs of satisfiability: a formula followed by an assignment, in order of first occurrence,
padded to the length of the encoded formula. A proof the verifier rejects proves `φ`. -/
private noncomputable def satProofSystem : ProofSystem encCNF SAT :=
  .ofVerifier cnfDecoder SAT.computableTidilyInPolyTime_verifier SAT.isVerifier
    (a₀ := φ) ⟨fun _ => true, rfl⟩

/-- The assignment `x₀ ↦ true`, `x₁ ↦ true`, padded, proves `φ`. -/
example : satProofSystem (frame (encCNF φ) ++
    ([true, true] ++ List.replicate ((encCNF φ).length - 2) false)) = φ :=
  ProofSystem.ofVerifier_frame_append _ _ _ _ (by simp [encCNF]; decide) rfl

/-- No certificate satisfies `ψ`, so a word starting with `ψ` proves the default formula `φ`. -/
example (w : List Bool) : satProofSystem (frame (encCNF ψ) ++ w) = φ := by
  have hψ : ¬ ψ.Satisfiable := fun ⟨σ, h⟩ => by
    cases h0 : σ 0 <;> simp [ψ, CNF.eval, Clause.eval, Literal.eval, h0] at h
  change (if _ then _ else _) = φ
  rw [ite_eq_right_iff]
  simp only [ProofSystem.verifierAccepts, ProofSystem.verifierInstance, unframe_frame_append,
    cnfDecoder.decode_enc, dropFrame_frame_append, Bool.and_eq_true]
  exact fun h => absurd ⟨_, h.1⟩ hψ

/-- `SAT` has a polynomially bounded proof system. -/
example : ∃ P : ProofSystem encCNF SAT, P.PolynomiallyBounded :=
  (ProofSystem.exists_polynomiallyBounded_iff_mem_NP (L := SAT) cnfDecoder
    ⟨φ, fun _ => true, rfl⟩).2
    SAT.mem_NP

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded

/--
info: 'Cslib.Complexity.ProofSystem.coNP_subset_NP_iff_exists_polynomiallyBounded' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.coNP_subset_NP_iff_exists_polynomiallyBounded

/--
info: 'Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_mem_NP

/--
info: 'Cslib.Complexity.ProofSystem.PolynomiallyBounded.of_simulates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.PolynomiallyBounded.of_simulates

/--
info: 'Cslib.Complexity.ProofSystem.PSimulates.simulates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ProofSystem.PSimulates.simulates

end ComplexityTests.ProofComplexity
