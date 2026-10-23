/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.Efficiency
import Complexity.Computability.Circuit.Boolean.EvaluationTime

/-!
An explicitly insecure bit-encryption example checks the refresh construction. A ciphertext has
a masked message bit and a tag. Fresh encryption always sets the tag to `false`, while evaluation
always sets it to `true` and deliberately returns a wrong answer on evaluated inputs.
Thus evaluation outputs lie outside every fresh-encryption support.
The public key reveals the masking bit; no security claim is made for this test scheme.
-/

namespace ComplexityTests.HomomorphicRefresh

open Cslib Cslib.Circuits Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM

private def decode (key ciphertext : List Bool) : Bool :=
  ciphertext.getD 0 false ^^ key.getD 0 false

private def evaluatedBit (pk : List Bool) (C : Σ n, Circuit Boolean.signature n 1)
    (inputs : List (List Bool)) : Bool :=
  if inputs.any (fun c => c.getD 1 false) then false
  else C.2.eval Boolean.interpretation (BitString.ofList C.1 (inputs.map (decode pk))) 0

private noncomputable def tagged : Scheme where
  keyGen _ := (fun b : Bool => ([b], [b])) <$> ProbComp.uniform Bool
  encrypt _ pk b := pure [b ^^ pk.getD 0 false, false]
  decrypt _ := decode
  evaluate _ pk C inputs := pure
    [evaluatedBit pk C inputs ^^ pk.getD 0 false, true]
  permitted _ _ := True

private theorem decode_encrypt (pk : List Bool) (b tag : Bool) :
    decode pk [b ^^ pk.getD 0 false, tag] = b := by
  change ((b ^^ pk.getD 0 false) ^^ pk.getD 0 false) = b
  cases b <;> cases pk.getD 0 false <;> rfl

private theorem decode_fresh {n : ℕ} {pk bits : List Bool} {inputs : List (List Bool)}
    (h : tagged.FreshInputs n pk bits inputs) : inputs.map (decode pk) = bits := by
  induction h with
  | nil => rfl
  | @cons b c bits inputs hc _ ih =>
    have heq : c = [b ^^ pk.getD 0 false, false] := by simpa [tagged] using hc
    subst c
    simp only [List.map_cons, decode_encrypt, ih]

private theorem tags_fresh {n : ℕ} {pk bits : List Bool} {inputs : List (List Bool)}
    (h : tagged.FreshInputs n pk bits inputs) :
    inputs.any (fun c => c.getD 1 false) = false := by
  induction h with
  | nil => rfl
  | @cons b c bits inputs hc _ ih =>
    have heq : c = [b ^^ pk.getD 0 false, false] := by simpa [tagged] using hc
    subst c
    change inputs.any (fun c => c.getD 1 false) = false
    exact ih

private theorem keys_supported (n : ℕ) (keys : List Bool × List Bool) :
    keys ∈ (ProbComp.eval (tagged.keyGen n)).support ↔
      ∃ b : Bool, keys = ([b], [b]) := by
  have h : (0 : ENNReal) ≠ 2⁻¹ := (ENNReal.inv_ne_zero.mpr (by norm_num)).symm
  simp [tagged, eq_comm, h]

private theorem tagged_correct : tagged.Correct where
  decrypt_encrypt n keys hkeys b c hc := by
    obtain ⟨k, rfl⟩ := (keys_supported n keys).1 hkeys
    have hc' : c = [b ^^ k, false] := by simpa [tagged] using hc
    subst c
    exact decode_encrypt [k] b false
  decrypt_evaluate n keys hkeys C _ bits inputs _ hfresh c hc := by
    obtain ⟨k, rfl⟩ := (keys_supported n keys).1 hkeys
    have hc' : c = [evaluatedBit [k] C inputs ^^ k, true] := by
      simpa [tagged] using hc
    subst c
    change decode [k] [evaluatedBit [k] C inputs ^^ k, true] = _
    exact (decode_encrypt [k] (evaluatedBit [k] C inputs) true).trans (by
      simp only [evaluatedBit, tags_fresh hfresh, Bool.false_eq_true, ite_false,
        decode_fresh hfresh])

private theorem tagged_width : tagged.FixedWidth (fun _ => 1) (fun _ => 2) where
  secret_length n keys hkeys := by
    obtain ⟨k, rfl⟩ := (keys_supported n keys).1 hkeys
    rfl
  encrypt_length n keys _ b c hc := by
    have hc' : c = [b ^^ keys.1.getD 0 false, false] := by simpa [tagged] using hc
    simp [hc']
  evaluate_length n keys _ C _ bits inputs _ _ c hc := by
    have hc' : c = [evaluatedBit keys.1 C inputs ^^ keys.1.getD 0 false, true] := by
      simpa [tagged] using hc
    simp [hc']

private def xorCircuit : Circuit Boolean.signature 3 1 :=
  (Circuit.oneGate (σ := Boolean.signature) .and id).comp
    ((Circuit.oneGate (σ := Boolean.signature) .or ![0, 1]).append
      ((Circuit.oneGate (σ := Boolean.signature) .not (fun _ => 0)).comp
        (Circuit.oneGate (σ := Boolean.signature) .and ![0, 1])))

private theorem eval_xorCircuit (x : Fin 3 → Bool) :
    xorCircuit.eval Boolean.interpretation x 0 = (x 1 ^^ x 0) := by
  change ((x 0 || x 1) && !(x 0 && x 1)) = (x 1 ^^ x 0)
  cases x 0 <;> cases x 1 <;> rfl

private def decryptionCircuits : DecryptionCircuits tagged (fun _ => 1) (fun _ => 2) where
  circuit _ := xorCircuit
  correct n sk c hsk hc := by
    rw [eval_xorCircuit]
    rcases sk with _ | ⟨s, sk⟩
    · simp at hsk
    rcases sk with _ | ⟨s', sk⟩
    · cases c with
      | nil => simp at hc
      | cons b rest => rfl
    · simp at hsk

private theorem tagged_bootstrappable : Scheme.Bootstrappable decryptionCircuits where
  decrypt_mem _ := trivial
  nand_mem _ := trivial

private theorem decode_poly : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => decode p.1 p.2) (encPair encBits encBits) encBool := by
  unfold decode
  fun_prop

private theorem evaluatedBit_poly : ComputableTidilyInPolyTime
    (fun p : List Bool × (Σ n, Circuit Boolean.signature n 1) × List (List Bool) =>
      evaluatedBit p.1 p.2.1 p.2.2)
    (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))) encBool := by
  have hdecoded : ComputableTidilyInPolyTime
      (fun p : List Bool × (Σ n, Circuit Boolean.signature n 1) × List (List Bool) =>
        p.2.2.map (decode p.1))
      (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))) encBits := by
    apply ComputableTidilyInPolyTime.mapToBitsWithInput
    · fun_prop
    · exact decode_poly.comp (show ComputableTidilyInPolyTime
        (fun p : (List Bool × (Σ n, Circuit Boolean.signature n 1) × List (List Bool)) ×
          List Bool => (p.1.1, p.2))
        (encPair (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))) encBits)
        (encPair encBits encBits) by fun_prop)
  unfold evaluatedBit
  fun_prop

private theorem encrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => tagged.encrypt p.1 p.2.1 p.2.2) := by
  apply ComputableTidilyInPolyTime.isPPTOn
  change ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool × Bool => [p.2.2 ^^ p.2.1.getD 0 false, false]) _ _
  fun_prop

private theorem evaluate_ppt : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
    encBits (fun p => tagged.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply ComputableTidilyInPolyTime.isPPTOn
  change ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool × (Σ n, Circuit Boolean.signature n 1) × List (List Bool) =>
      [evaluatedBit p.2.1 p.2.2.1 p.2.2.2 ^^ p.2.1.getD 0 false, true]) _ _
  have heval := evaluatedBit_poly.comp
    (ComputableTidilyInPolyTime.snd encUnary
      (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
  fun_prop

private theorem circuits_poly : ComputableTidilyInPolyTime
    (fun n => (⟨_, decryptionCircuits.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
    encUnary (Boolean.encCircuit 1) := by
  exact ComputableTidilyInPolyTime.const
    (⟨3, xorCircuit⟩ : Σ n, Circuit Boolean.signature n 1)

-- The functional instance also inhabits every efficiency hypothesis of NAND refresh.
example : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (encList encBits) (encPair encBits encBits))))
    encBits (fun p =>
      Scheme.refreshNand decryptionCircuits p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  apply Scheme.isPPTOn_refreshNand encrypt_ppt evaluate_ppt decryptionCircuits circuits_poly
  all_goals fun_prop

-- These bundled hypotheses have an actual instance.
example : tagged.Correct ∧ tagged.FixedWidth (fun _ => 1) (fun _ => 2) ∧
    Scheme.Bootstrappable decryptionCircuits :=
  ⟨tagged_correct, tagged_width, tagged_bootstrappable⟩

-- Every evaluation-tagged ciphertext is outside the support of every fresh encryption.
example (n : ℕ) (pk : List Bool) (b message : Bool) :
    [b, true] ∉ (ProbComp.eval (tagged.encrypt n pk message)).support := by
  simp [tagged]

-- The same encrypted key bit is reused in both halves of the augmented circuit.
private theorem encrypted_key : tagged.FreshInputs 0 [true] [true] [[false, false]] := by
  simp [Scheme.FreshInputs, tagged]

-- Refresh consumes an evaluated ciphertext and preserves its decrypted bit and width.
example (result : List Bool)
    (h : result ∈ (ProbComp.eval
      (Scheme.refresh decryptionCircuits 0 [true] [[false, false]] [false, true])).support) :
    tagged.decrypt 0 [true] result = true ∧ result.length = 2 := by
  constructor
  · exact Scheme.decrypt_refresh decryptionCircuits tagged_correct tagged_bootstrappable 0
      ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
      [true] [false, true] rfl rfl
      [[false, false]] encrypted_key result h
  · exact Scheme.length_refresh decryptionCircuits tagged_width tagged_bootstrappable 0
      ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
      [true] [false, true] rfl rfl
      [[false, false]] encrypted_key result h

-- Both NAND inputs may be evaluated ciphertexts. This computes NAND(true, false) = true.
example (result : List Bool)
    (h : result ∈ (ProbComp.eval
      (Scheme.refreshNand decryptionCircuits 0 [true] [[false, false]]
        [false, true] [true, true])).support) :
    tagged.decrypt 0 [true] result = true ∧ result.length = 2 := by
  constructor
  · exact Scheme.decrypt_refreshNand decryptionCircuits tagged_correct tagged_bootstrappable 0
      ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
      [true] [false, true] [true, true] rfl rfl rfl
      [[false, false]] encrypted_key result h
  · exact Scheme.length_refreshNand decryptionCircuits tagged_width tagged_bootstrappable 0
      ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
      [true] [false, true] [true, true] rfl rfl rfl
      [[false, false]] encrypted_key result h

-- Switch from the old key [false] to [true]. The encrypted old key is shared by both inputs.
example (result : List Bool)
    (h : result ∈ (ProbComp.eval
      (Scheme.refreshNand decryptionCircuits 0 [true] [[true, false]]
        [true, true] [false, true])).support) :
    tagged.decrypt 0 [true] result = true := by
  exact Scheme.decrypt_refreshNand decryptionCircuits tagged_correct tagged_bootstrappable 0
    ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
    [false] [true, true] [false, true] rfl rfl rfl [[true, false]]
    (by simp [Scheme.FreshInputs, tagged]) result h

-- Applying the base evaluator directly to an evaluated encryption of true gives false.
example : ProbComp.eval
    (tagged.evaluate 0 [true] ⟨1, Circuit.wiring Boolean.signature id⟩ [[false, true]]) =
    PMF.pure [true, true] := by
  simp [tagged, evaluatedBit]

-- Refresh can be repeated even though the first output is outside fresh-encryption support.
example : ProbComp.eval (do
    let c ← Scheme.refresh decryptionCircuits 0 [true] [[false, false]] [false, true]
    Scheme.refresh decryptionCircuits 0 [true] [[false, false]] c) = PMF.pure [false, true] := by
  simp [Scheme.refresh, Scheme.encryptBits, tagged, evaluatedBit, decryptionCircuits,
    eval_xorCircuit, decode, BitString.ofList]

-- Empty plaintext words are encrypted without introducing a ciphertext.
example : ProbComp.eval (tagged.encryptBits 0 [true] []) = PMF.pure [] := rfl

/--
info: 'Cslib.Crypto.Homomorphic.Scheme.decrypt_refresh' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.decrypt_refresh

/--
info: 'Cslib.Crypto.Homomorphic.Scheme.decrypt_refreshNand' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.decrypt_refreshNand

/--
info: 'Cslib.Crypto.Homomorphic.Scheme.length_refresh' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.length_refresh

/--
info: 'Cslib.Crypto.Homomorphic.Scheme.length_refreshNand' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.length_refreshNand

/--
info: 'Cslib.Crypto.Homomorphic.Scheme.isPPTOn_refresh' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.isPPTOn_refresh

/--
info: 'Cslib.Crypto.Homomorphic.Scheme.isPPTOn_refreshNand' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.isPPTOn_refreshNand

end ComplexityTests.HomomorphicRefresh
