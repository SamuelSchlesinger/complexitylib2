/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Bootstrapping

/-!
# Tests for Gentry's bootstrapping theorem

Provides a concrete non-vacuous instantiation of `EncryptionScheme` and `Bootstrappable`, tests
fixed-key and leveled homomorphic evaluation on De Morgan formulas and circuits, and audits the
axiom dependencies of the headline theorems in `Complexity.Crypto.Computational.Bootstrapping`.
-/

namespace ComplexityTests.Crypto.Bootstrapping

open Cslib Cslib.Crypto Cslib.Circuits Cslib.Probability Turing.MultiTapeTM

/-- Concrete noiseless bit-framing scheme instantiating `EncryptionScheme` and `Bootstrappable`
to witness that all structure and typeclass hypotheses are non-vacuous and jointly satisfiable. -/
noncomputable def trivialScheme : EncryptionScheme where
  keyGen _ := pure ([], [false])
  encrypt _ b := pure [b]
  decrypt _ c := c.headD false
  skLength _ := 1
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by polytime
  skLength_polyTime := by polytime
  length_sk := by
    intro n keys hkeys
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hkeys
    subst hkeys
    rfl
  decrypt_encrypt := by
    intro n keys hkeys b c hc
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hkeys hc
    subst hkeys hc
    rfl

noncomputable instance : Bootstrappable trivialScheme where
  evalAugDecrypt op _ _ c₁ c₂ := [evalOp2 op (c₁.headD false) (c₂.headD false)]
  cipherBound _ := 1
  evalAugDecrypt_polyTime := by polytime
  cipherBound_polyTime := by polytime
  decrypt_evalAugDecrypt := by
    intro n keys₁ keys₂ _ _ ek _ op c₁ c₂
    rfl
  length_encrypt_le := by
    intro n keys _ b c hc
    simp only [trivialScheme, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
    subst hc
    exact le_rfl
  length_evalAugDecrypt_le := by
    intro n keys _ ek op c₁ c₂
    exact le_rfl
  length_evalAugDecrypt_le_pk := by
    intro op pk ek c₁ c₂
    exact le_rfl

/-- Concrete depth-2 De Morgan formula `(x₀ ∧ ¬x₁) ∨ x₀` for testing homomorphic evaluation. -/
def sampleFormula : Formula Boolean.signature 2 :=
  Formula.gate₂ (σ := Boolean.signature) Boolean.Op.or rfl
    (Formula.gate₂ (σ := Boolean.signature) Boolean.Op.and rfl (.input 0)
      (.gate Boolean.Op.not fun _ => .input 1))
    (.input 0)

example (x : Fin 2 → Bool) :
    let keys := ([], [false])
    let ek := [[false]]
    let cs₀ : Fin 2 → List Bool := fun i => [x i]
    trivialScheme.decrypt keys.2
      (trivialScheme.evalHomOutput keys.1 ek (List.ofFn cs₀) sampleFormula.toCircuit.code.1
        (sampleFormula.toCircuit.outputs 0).toNat) =
      sampleFormula.eval Boolean.interpretation x := by
  intro keys ek cs₀
  have hkeys : keys ∈ (ProbComp.eval (trivialScheme.keyGen 0)).support := by
    simp [trivialScheme, keys]
  have hek : ek ∈ (ProbComp.eval (trivialScheme.encryptKey keys.1 keys.2)).support := by
    simp [trivialScheme, EncryptionScheme.encryptKey, keys, ek]
  have hcs₀ : ∀ i, cs₀ i ∈ (ProbComp.eval (trivialScheme.encrypt keys.1 (x i))).support := by
    intro i
    simp [trivialScheme, cs₀]
  exact trivialScheme.decrypt_evalHomOutput_formula hkeys hek sampleFormula x cs₀ hcs₀

/--
info: 'Cslib.Crypto.EncryptionScheme.isPPTOn_encryptKey' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.isPPTOn_encryptKey

/--
info: 'Cslib.Crypto.EncryptionScheme.encryptKeyTest_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.encryptKeyTest_gap

/--
info: 'Cslib.Crypto.EncryptionScheme.leveledSemanticSecure_of_semanticSecure' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.leveledSemanticSecure_of_semanticSecure

/--
info: 'Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalHomCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalHomCode

/--
info: 'Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalHomOutput' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalHomOutput

/--
info: 'Cslib.Crypto.EncryptionScheme.decrypt_evalHomOutput_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.decrypt_evalHomOutput_circuit

/--
info: 'Cslib.Crypto.EncryptionScheme.decrypt_evalHomOutput_formula' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.decrypt_evalHomOutput_formula

/--
info: 'Cslib.Crypto.EncryptionScheme.length_evalHomOutput_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.length_evalHomOutput_le

/--
info: 'Cslib.Crypto.EncryptionScheme.fixedKeyFHE_of_circularSecure' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.fixedKeyFHE_of_circularSecure

/--
info: 'Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalLeveledCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalLeveledCode

/--
info: 'Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalLeveledOutput' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalLeveledOutput

/--
info: 'Cslib.Crypto.EncryptionScheme.decrypt_evalLeveledOutput_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.decrypt_evalLeveledOutput_circuit

/--
info: 'Cslib.Crypto.EncryptionScheme.decrypt_evalLeveledOutput_formula' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.decrypt_evalLeveledOutput_formula

/--
info: 'Cslib.Crypto.EncryptionScheme.length_evalLeveledOutput_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.length_evalLeveledOutput_le

/--
info: 'Cslib.Crypto.EncryptionScheme.leveledFHE_of_bootstrappable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.EncryptionScheme.leveledFHE_of_bootstrappable

end ComplexityTests.Crypto.Bootstrapping
