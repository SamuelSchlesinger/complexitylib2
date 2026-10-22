/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Circuit.Formula
public import Complexity.Crypto.Computational.Bootstrapping.KeyEncryption
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Tactic.PPT

/-!
# Bootstrappability, homomorphic gate evaluation, and fixed-key FHE

This module defines the assumed bootstrappability interface (`Cslib.Crypto.Bootstrappable`) for
augmented De Morgan decryption gates `Dec(·, c₁) op Dec(·, c₂)`, gate-by-gate homomorphic circuit
evaluation under a single evaluation key (`evalHomCode`, `evalHomOutput`), and Gentry's fixed-key
(pure) FHE composition under circular security (`fixedKeyFHE_of_circularSecure`) [Gentry2009].

## Main definitions

* `Cslib.Crypto.evalOp2`: two-argument semantics of a De Morgan gate operation.
* `Cslib.Crypto.Bootstrappable`: assumed interface for an augmented De Morgan decryption gate
  with key switching (`evalAugDecrypt`), whose correctness and compactness bound `cipherBound`
  are fields rather than consequences of a homomorphic evaluation of the decryption circuit.
* `Cslib.Crypto.EncryptionScheme.evalGateOp`, `Cslib.Crypto.EncryptionScheme.homInterpretation`:
  homomorphic De Morgan gate operation and `Circuits.Interpretation` on ciphertexts.
* `Cslib.Crypto.EncryptionScheme.evalHomCode`, `Cslib.Crypto.EncryptionScheme.evalHomOutput`:
  fixed-key gate-by-gate homomorphic circuit evaluation.
* `Cslib.Crypto.EncryptionScheme.fixedKeyGen`, `Cslib.Crypto.EncryptionScheme.CircularSecure`:
  fixed-key circular evaluation key generation and circular security.

## Main results

* `Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalHomCode`,
  `Cslib.Crypto.EncryptionScheme.computableTidilyInPolyTime_evalHomOutput`: polynomial-time
  certificates for fixed-key homomorphic circuit evaluation.
* `Cslib.Crypto.EncryptionScheme.decrypt_evalHomOutput_circuit`,
  `Cslib.Crypto.EncryptionScheme.decrypt_evalHomOutput_formula`: correctness of fixed-key
  homomorphic evaluation for arbitrary-depth De Morgan circuits and formulas.
* `Cslib.Crypto.EncryptionScheme.length_evalHomOutput_le`: compactness of fixed-key homomorphic
  evaluation.
* `Cslib.Crypto.EncryptionScheme.fixedKeyFHE_of_circularSecure`: Gentry's pure/fixed-key FHE
  composition for circuits and formulas of arbitrary depth, assuming the `Bootstrappable` interface
  and circular security.

## References

* [C. Gentry, *Fully Homomorphic Encryption Using Ideal Lattices*][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM Circuits
open scoped NNReal

/-! ### Bootstrappability and augmented decryption gates -/

/-- Evaluate a De Morgan gate operation on two Boolean arguments (ignoring unused arguments for
constants and negation). -/
def evalOp2 : Boolean.Op → Bool → Bool → Bool
  | .const b, _, _ => b
  | .not, b₁, _ => !b₁
  | .and, b₁, b₂ => b₁ && b₂
  | .or, b₁, b₂ => b₁ || b₂

@[simp]
theorem evalOp2_const (b x y : Bool) : evalOp2 (.const b) x y = b := rfl

@[simp]
theorem evalOp2_not (x y : Bool) : evalOp2 .not x y = !x := rfl

@[simp]
theorem evalOp2_and (x y : Bool) : evalOp2 .and x y = (x && y) := rfl

@[simp]
theorem evalOp2_or (x y : Bool) : evalOp2 .or x y = (x || y) := rfl

@[program_certificate]
theorem computableTidilyInPolyTime_evalOp2 {γ : Type} {encIn : γ ↪ List Bool}
    {op : γ → Boolean.Op} {b₁ b₂ : γ → Bool}
    (hop : ComputableTidilyInPolyTime op encIn Boolean.encOp)
    (hb₁ : ComputableTidilyInPolyTime b₁ encIn encBool)
    (hb₂ : ComputableTidilyInPolyTime b₂ encIn encBool) :
    ComputableTidilyInPolyTime (fun a => evalOp2 (op a) (b₁ a) (b₂ a)) encIn encBool :=
  (ComputableTidilyInPolyTime.of_finite
    (encA := encPair Boolean.encOp (encPair encBool encBool))
    (fun p : Boolean.Op × Bool × Bool => evalOp2 p.1 p.2.1 p.2.2)).comp
    (hop.prod (hb₁.prod hb₂))

/-- The **bootstrappability interface** for a public-key bit encryption scheme `S`, modelled on
Gentry's notion [Gentry2009]. This class is an *assumption*, not a theorem: it does not require
`evalAugDecrypt` to arise from homomorphically evaluating the decryption circuit of `S`, and its
correctness and compactness are taken as fields. It asks for a deterministic polynomial-time
gate-plus-key-switch operation `evalAugDecrypt` playing the role of Gentry's augmented De Morgan
decryption gates `Dec(·, c₁) op Dec(·, c₂)`: given an operation `op`, a target
public key `pk₂`, an evaluation key `ek ← S.encryptKey pk₂ sk₁` encrypting `sk₁` bit-by-bit under
`pk₂`, and two ciphertexts `c₁, c₂` under `sk₁`, `evalAugDecrypt op pk₂ ek c₁ c₂` outputs a
refreshed ciphertext under `sk₂` that decrypts to `evalOp2 op (S.decrypt sk₁ c₁) (S.decrypt sk₁ c₂)`
and whose bit-length is bounded by a polynomial `cipherBound` independent of `c₁`, `c₂`, and the
evaluated circuit's size or depth. -/
class Bootstrappable (S : EncryptionScheme) where
  /-- The assumed gate-plus-key-switch operation, standing in for the homomorphic evaluation of
  the augmented decryption circuit `Dec(·, c₁) op Dec(·, c₂)` on the encrypted secret key `ek`
  under target public key `pk₂`. -/
  evalAugDecrypt : Boolean.Op → List Bool → List (List Bool) → List Bool → List Bool → List Bool
  /-- Compactness bound on the bit-length of fresh and refreshed ciphertexts. -/
  cipherBound : ℕ → ℕ
  /-- `evalAugDecrypt` is computable tidily in polynomial time. -/
  evalAugDecrypt_polyTime : ComputableTidilyInPolyTime
    (fun p : ((Boolean.Op × List Bool) × List (List Bool)) × (List Bool × List Bool) =>
      evalAugDecrypt p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2)
    (encPair (encPair (encPair Boolean.encOp encBits) (encList encBits)) (encPair encBits encBits))
    encBits
  /-- The compactness bound `cipherBound` is computable tidily in polynomial time in unary
  (and hence polynomially bounded). -/
  cipherBound_polyTime : ComputableTidilyInPolyTime cipherBound encUnary encUnary
  /-- Recryption and gate correctness: for any supported key pairs `keys₁, keys₂` at security
  parameter `n` and any evaluation key `ek` encrypting `keys₁.2` under `keys₂.1`, decrypting
  `evalAugDecrypt op keys₂.1 ek c₁ c₂` under `keys₂.2` yields
  `evalOp2 op (S.decrypt keys₁.2 c₁) (S.decrypt keys₁.2 c₂)`. -/
  decrypt_evalAugDecrypt : ∀ n keys₁ keys₂,
    keys₁ ∈ (ProbComp.eval (S.keyGen n)).support →
    keys₂ ∈ (ProbComp.eval (S.keyGen n)).support →
    ∀ ek, ek ∈ (ProbComp.eval (S.encryptKey keys₂.1 keys₁.2)).support →
    ∀ op c₁ c₂,
      S.decrypt keys₂.2 (evalAugDecrypt op keys₂.1 ek c₁ c₂) =
        evalOp2 op (S.decrypt keys₁.2 c₁) (S.decrypt keys₁.2 c₂)
  /-- Compactness for fresh ciphertexts at security parameter `n`. -/
  length_encrypt_le : ∀ n keys, keys ∈ (ProbComp.eval (S.keyGen n)).support →
    ∀ b c, c ∈ (ProbComp.eval (S.encrypt keys.1 b)).support → c.length ≤ cipherBound n
  /-- Compactness for refreshed ciphertexts at security parameter `n`. -/
  length_evalAugDecrypt_le : ∀ n keys, keys ∈ (ProbComp.eval (S.keyGen n)).support →
    ∀ ek op c₁ c₂, (evalAugDecrypt op keys.1 ek c₁ c₂).length ≤ cipherBound n
  /-- Structural compactness: for any public key `pk`, the output length of `evalAugDecrypt` is
  bounded by `cipherBound pk.length`, independently of the input ciphertexts `c₁, c₂`. -/
  length_evalAugDecrypt_le_pk : ∀ op pk ek c₁ c₂,
    (evalAugDecrypt op pk ek c₁ c₂).length ≤ cipherBound pk.length

namespace EncryptionScheme

variable (S : EncryptionScheme) [Bootstrappable S]

/-- Abbreviation for `Bootstrappable.evalAugDecrypt`. -/
abbrev evalAugDecrypt :
    Boolean.Op → List Bool → List (List Bool) → List Bool → List Bool → List Bool :=
  Bootstrappable.evalAugDecrypt (S := S)

/-- Abbreviation for `Bootstrappable.cipherBound`. -/
abbrev cipherBound : ℕ → ℕ :=
  Bootstrappable.cipherBound (S := S)

@[program_certificate]
theorem computableTidilyInPolyTime_evalAugDecrypt {γ : Type} {encIn : γ ↪ List Bool}
    {op : γ → Boolean.Op} {pk : γ → List Bool} {ek : γ → List (List Bool)}
    {c₁ c₂ : γ → List Bool}
    (hop : ComputableTidilyInPolyTime op encIn Boolean.encOp)
    (hpk : ComputableTidilyInPolyTime pk encIn encBits)
    (hek : ComputableTidilyInPolyTime ek encIn (encList encBits))
    (hc₁ : ComputableTidilyInPolyTime c₁ encIn encBits)
    (hc₂ : ComputableTidilyInPolyTime c₂ encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => S.evalAugDecrypt (op a) (pk a) (ek a) (c₁ a) (c₂ a))
      encIn encBits :=
  Bootstrappable.evalAugDecrypt_polyTime.comp (((hop.prod hpk).prod hek).prod (hc₁.prod hc₂))

@[program_certificate]
theorem computableTidilyInPolyTime_cipherBound {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun a => S.cipherBound (n a)) encIn encUnary :=
  Bootstrappable.cipherBound_polyTime.comp hn

/-- The compactness bound `cipherBound` is polynomially bounded. -/
theorem polynomiallyBounded_cipherBound : PolynomiallyBounded S.cipherBound :=
  Bootstrappable.cipherBound_polyTime.polynomiallyBounded

/-- Homomorphic gate evaluation under `(pk, ek)`, dispatching on the De Morgan operation. -/
def evalGateOp (op : Boolean.Op) (pk : List Bool) (ek : List (List Bool))
    (c₁ c₂ : List Bool) : List Bool :=
  S.evalAugDecrypt op pk ek
    (if op = .const false ∨ op = .const true then [] else c₁)
    (if op = .and ∨ op = .or then c₂ else [])

@[program_certificate]
theorem computableTidilyInPolyTime_evalGateOp {γ : Type} {encIn : γ ↪ List Bool}
    {op : γ → Boolean.Op} {pk : γ → List Bool} {ek : γ → List (List Bool)}
    {c₁ c₂ : γ → List Bool}
    (hop : ComputableTidilyInPolyTime op encIn Boolean.encOp)
    (hpk : ComputableTidilyInPolyTime pk encIn encBits)
    (hek : ComputableTidilyInPolyTime ek encIn (encList encBits))
    (hc₁ : ComputableTidilyInPolyTime c₁ encIn encBits)
    (hc₂ : ComputableTidilyInPolyTime c₂ encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => S.evalGateOp (op a) (pk a) (ek a) (c₁ a) (c₂ a))
      encIn encBits := by
  unfold evalGateOp
  polytime

theorem length_evalGateOp_le {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support)
    (ek : List (List Bool)) (op : Boolean.Op) (c₁ c₂ : List Bool) :
    (S.evalGateOp op keys.1 ek c₁ c₂).length ≤ S.cipherBound n :=
  Bootstrappable.length_evalAugDecrypt_le n keys hkeys ek op _ _

theorem length_evalGateOp_le_pk (op : Boolean.Op) (pk : List Bool) (ek : List (List Bool))
    (c₁ c₂ : List Bool) :
    (S.evalGateOp op pk ek c₁ c₂).length ≤ S.cipherBound pk.length :=
  Bootstrappable.length_evalAugDecrypt_le_pk op pk ek _ _

theorem decrypt_evalGateOp {n : ℕ} {keys₁ keys₂ : List Bool × List Bool}
    (hkeys₁ : keys₁ ∈ (ProbComp.eval (S.keyGen n)).support)
    (hkeys₂ : keys₂ ∈ (ProbComp.eval (S.keyGen n)).support)
    {ek : List (List Bool)} (hek : ek ∈ (ProbComp.eval (S.encryptKey keys₂.1 keys₁.2)).support)
    (op : Boolean.Op) (c₁ c₂ : List Bool) :
    S.decrypt keys₂.2 (S.evalGateOp op keys₂.1 ek c₁ c₂) =
      evalOp2 op (S.decrypt keys₁.2 c₁) (S.decrypt keys₁.2 c₂) := by
  unfold evalGateOp
  rw [Bootstrappable.decrypt_evalAugDecrypt n keys₁ keys₂ hkeys₁ hkeys₂ ek hek]
  cases op <;> rfl

/-- The homomorphic `Interpretation Boolean.signature (List Bool)` on ciphertexts induced by a
target public key `pk` and evaluation key `ek`. -/
def homInterpretation (pk : List Bool) (ek : List (List Bool)) :
    Interpretation Boolean.signature (List Bool)
  | .const b, _ => S.evalAugDecrypt (.const b) pk ek [] []
  | .not, args => S.evalAugDecrypt .not pk ek (args 0) []
  | .and, args => S.evalAugDecrypt .and pk ek (args 0) (args 1)
  | .or, args => S.evalAugDecrypt .or pk ek (args 0) (args 1)

theorem homInterpretation_eq_evalGateOp (pk : List Bool) (ek : List (List Bool))
    (op : Boolean.Op) (f : ℕ → List Bool) :
    (S.homInterpretation pk ek op fun a => f a.val) = S.evalGateOp op pk ek (f 0) (f 1) := by
  cases op with
  | const b => cases b <;> rfl
  | not | and | or => rfl

theorem decrypt_homInterpretation {n : ℕ} {keys₁ keys₂ : List Bool × List Bool}
    (hkeys₁ : keys₁ ∈ (ProbComp.eval (S.keyGen n)).support)
    (hkeys₂ : keys₂ ∈ (ProbComp.eval (S.keyGen n)).support)
    {ek : List (List Bool)} (hek : ek ∈ (ProbComp.eval (S.encryptKey keys₂.1 keys₁.2)).support)
    (op : Boolean.Op) (args : Fin (Boolean.signature.Arity op) → List Bool) :
    S.decrypt keys₂.2 (S.homInterpretation keys₂.1 ek op args) =
      Boolean.interpretation op (S.decrypt keys₁.2 ∘ args) := by
  cases op <;>
    simp [homInterpretation, Bootstrappable.decrypt_evalAugDecrypt n keys₁ keys₂ hkeys₁ hkeys₂
      ek hek, Boolean.interpretation]

/-- When `ek` encrypts `keys.2` under `keys.1` (a circular evaluation key), decryption under
`keys.2` is a `Circuits.Homomorphism` from `S.homInterpretation keys.1 ek` to
`Boolean.interpretation`. -/
def decryptHomomorphism {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support)
    {ek : List (List Bool)} (hek : ek ∈ (ProbComp.eval (S.encryptKey keys.1 keys.2)).support) :
    Homomorphism (S.homInterpretation keys.1 ek) Boolean.interpretation where
  map := S.decrypt keys.2
  homomorphic := S.decrypt_homInterpretation hkeys hkeys hek

/-! ### Fixed-key homomorphic gate-list evaluation (`evalHomCode`, `evalHomOutput`) -/

/-- Homomorphically evaluate a De Morgan gate list `gates` on input ciphertexts `cs₀` using a
single evaluation key `(pk, ek)`. -/
def evalHomCode (pk : List Bool) (ek : List (List Bool))
    (cs₀ : List (List Bool)) (gates : List (Boolean.Op × List ℕ)) : List (List Bool) :=
  Circuits.evalCode (S.homInterpretation pk ek) [] cs₀ gates

/-- Read output wire `o` after homomorphically evaluating `gates` on `cs₀` under `(pk, ek)`. -/
def evalHomOutput (pk : List Bool) (ek : List (List Bool))
    (cs₀ : List (List Bool)) (gates : List (Boolean.Op × List ℕ)) (o : ℕ) : List Bool :=
  (S.evalHomCode pk ek cs₀ gates).getD o []

private theorem computableTidilyInPolyTime_evalHomStep :
    ComputableTidilyInPolyTime
      (fun p : ((List Bool × List (List Bool)) × List (List Bool)) × (Boolean.Op × List ℕ) =>
        p.1.2 ++ [S.homInterpretation p.1.1.1 p.1.1.2 p.2.1
          fun a => p.2.2[a.val]?.elim [] (p.1.2.getD · [])])
      (encPair (encPair (encPair encBits (encList encBits)) (encList encBits)) Boolean.encGate)
      (encList encBits) := by
  have heq :
      (fun p : ((List Bool × List (List Bool)) × List (List Bool)) × (Boolean.Op × List ℕ) =>
        p.1.2 ++ [S.homInterpretation p.1.1.1 p.1.1.2 p.2.1
          fun a => p.2.2[a.val]?.elim [] (p.1.2.getD · [])]) =
      fun p => p.1.2 ++ [S.evalGateOp p.2.1 p.1.1.1 p.1.1.2
        (p.2.2[0]?.elim [] (p.1.2.getD · []))
        (p.2.2[1]?.elim [] (p.1.2.getD · []))] :=
    funext fun p => by
      rw [S.homInterpretation_eq_evalGateOp p.1.1.1 p.1.1.2 p.2.1
        fun i => p.2.2[i]?.elim [] (p.1.2.getD · [])]
  rw [heq]
  have harg (i : ℕ) :
      ComputableTidilyInPolyTime
        (fun p : ((List Bool × List (List Bool)) × List (List Bool)) × (Boolean.Op × List ℕ) =>
          p.2.2[i]?.elim [] (p.1.2.getD · []))
        (encPair (encPair (encPair encBits (encList encBits)) (encList encBits)) Boolean.encGate)
        encBits :=
    ComputableTidilyInPolyTime.optionElimWithInput
      (ComputableTidilyInPolyTime.getElem? (ComputableTidilyInPolyTime.snd _ _).snd'
        (ComputableTidilyInPolyTime.const i))
      (ComputableTidilyInPolyTime.const [])
      (ComputableTidilyInPolyTime.listGetD_binary []
        (ComputableTidilyInPolyTime.fst _ _).fst'.snd'
        (ComputableTidilyInPolyTime.snd _ _))
  have h0 := harg 0
  have h1 := harg 1
  polytime

/-- **Polynomial-time fixed-key homomorphic evaluation** of a De Morgan gate list `gates` on input
ciphertexts `cs₀` under `(pk, ek)`. Compactness (`length_evalGateOp_le_pk`) ensures that each gate
adds at most `2 * S.cipherBound pk.length + 2` bits to the encoded wire list. -/
@[program_certificate]
theorem computableTidilyInPolyTime_evalHomCode :
    ComputableTidilyInPolyTime
      (fun p : ((List Bool × List (List Bool)) × List (List Bool)) × List (Boolean.Op × List ℕ) =>
        S.evalHomCode p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encBits (encList encBits)) (encList encBits))
        (encList Boolean.encGate))
      (encList encBits) := by
  unfold evalHomCode Circuits.evalCode
  refine ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (par := fun p : ((List Bool × List (List Bool)) × List (List Bool)) ×
      List (Boolean.Op × List ℕ) => p.1.1)
    (list := fun p => p.2)
    (init := fun p => p.1.2)
    (step := fun key values g =>
      values ++ [S.homInterpretation key.1 key.2 g.1
        fun a => g.2[a.val]?.elim [] (values.getD · [])])
    (by polytime) (by polytime) (by polytime)
    S.computableTidilyInPolyTime_evalHomStep
    (growth := fun p => 2 * S.cipherBound p.1.1.1.length + 2)
    (show ComputableTidilyInPolyTime
      (fun p : ((List Bool × List (List Bool)) × List (List Bool)) × List (Boolean.Op × List ℕ) =>
        2 * S.cipherBound p.1.1.1.length + 2)
      (encPair (encPair (encPair encBits (encList encBits)) (encList encBits))
        (encList Boolean.encGate))
      encUnary by polytime).polyBounded ?_
  intro p values g _
  rw [S.homInterpretation_eq_evalGateOp p.1.1.1 p.1.1.2 g.1
    fun i => g.2[i]?.elim [] (values.getD · [])]
  have hlen := S.length_evalGateOp_le_pk g.1 p.1.1.1 p.1.1.2
    (g.2[0]?.elim [] (values.getD · [])) (g.2[1]?.elim [] (values.getD · []))
  simp only [encList_append, encList_cons, encList_nil, List.length_append, List.length_nil,
    length_frame, encBits_apply]
  omega

/-- **Polynomial-time fixed-key homomorphic output evaluation** of wire `o` after evaluating a
De Morgan gate list `gates` on input ciphertexts `cs₀`. -/
@[program_certificate]
theorem computableTidilyInPolyTime_evalHomOutput :
    ComputableTidilyInPolyTime
      (fun p : (((List Bool × List (List Bool)) × List (List Bool)) ×
          List (Boolean.Op × List ℕ)) × ℕ =>
        S.evalHomOutput p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair
        (encPair (encPair (encPair encBits (encList encBits)) (encList encBits))
          (encList Boolean.encGate))
        encNat)
      encBits :=
  ComputableTidilyInPolyTime.listGetD_binary []
    (S.computableTidilyInPolyTime_evalHomCode.comp (ComputableTidilyInPolyTime.fst _ _))
    (ComputableTidilyInPolyTime.snd _ _)

/-- Evaluating a circuit's gate code under `evalHomOutput` agrees with `Circuit.eval` under
`S.homInterpretation pk ek`. -/
theorem evalHomOutput_circuit {m o : ℕ} (pk : List Bool) (ek : List (List Bool))
    (c : Circuit Boolean.signature m o) (cs₀ : Fin m → List Bool) (j : Fin o) :
    S.evalHomOutput pk ek (List.ofFn cs₀) c.code.1 (c.outputs j).toNat =
      c.eval (S.homInterpretation pk ek) cs₀ j :=
  (c.eval_eq_getD (S.homInterpretation pk ek) [] cs₀ j).symm

/-- **Correctness of fixed-key homomorphic evaluation for arbitrary-depth circuits**:
for any self-encrypted evaluation key `ek ∈ (S.encryptKey keys.1 keys.2).support`, any De Morgan
circuit `c : Circuit Boolean.signature m o` (of arbitrary depth and size), and any input
ciphertexts `cs₀` encrypting `x : Fin m → Bool`, decrypting the homomorphically evaluated output
wire `j` recovers `c.eval Boolean.interpretation x j`. -/
theorem decrypt_evalHomOutput_circuit {n m o : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support)
    {ek : List (List Bool)} (hek : ek ∈ (ProbComp.eval (S.encryptKey keys.1 keys.2)).support)
    (c : Circuit Boolean.signature m o) (x : Fin m → Bool) (cs₀ : Fin m → List Bool)
    (hcs₀ : ∀ i, cs₀ i ∈ (ProbComp.eval (S.encrypt keys.1 (x i))).support) (j : Fin o) :
    S.decrypt keys.2 (S.evalHomOutput keys.1 ek (List.ofFn cs₀) c.code.1 (c.outputs j).toNat) =
      c.eval Boolean.interpretation x j := by
  rw [S.evalHomOutput_circuit]
  have hhom := congrFun (c.map_eval (S.decryptHomomorphism hkeys hek) cs₀) j
  simp only [Function.comp_apply, decryptHomomorphism] at hhom
  rw [hhom]
  congr 1
  funext i
  exact S.decrypt_encrypt n keys hkeys (x i) (cs₀ i) (hcs₀ i)

/-- **Correctness of fixed-key homomorphic evaluation for arbitrary-depth Boolean formulas**:
evaluating the compiled circuit `F.toCircuit` of any De Morgan formula `F` (of arbitrary depth)
and decrypting recovers `F.eval Boolean.interpretation x`. -/
theorem decrypt_evalHomOutput_formula {n m : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support)
    {ek : List (List Bool)} (hek : ek ∈ (ProbComp.eval (S.encryptKey keys.1 keys.2)).support)
    (F : Formula Boolean.signature m) (x : Fin m → Bool) (cs₀ : Fin m → List Bool)
    (hcs₀ : ∀ i, cs₀ i ∈ (ProbComp.eval (S.encrypt keys.1 (x i))).support) :
    S.decrypt keys.2
      (S.evalHomOutput keys.1 ek (List.ofFn cs₀) F.toCircuit.code.1
        (F.toCircuit.outputs 0).toNat) =
      F.eval Boolean.interpretation x := by
  rw [S.decrypt_evalHomOutput_circuit hkeys hek F.toCircuit x cs₀ hcs₀ 0, F.eval_toCircuit]

/-- Every wire ciphertext in `evalHomCode` has length bounded by `S.cipherBound n` whenever the
initial input ciphertexts do. -/
theorem length_mem_evalHomCode_le {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support)
    (ek : List (List Bool)) (cs₀ : List (List Bool))
    (hcs₀ : ∀ c ∈ cs₀, c.length ≤ S.cipherBound n)
    (gates : List (Boolean.Op × List ℕ)) :
    ∀ c ∈ S.evalHomCode keys.1 ek cs₀ gates, c.length ≤ S.cipherBound n := by
  induction gates using List.reverseRecOn with
  | nil => exact hcs₀
  | append_singleton gates g ih =>
    intro c hc
    rw [evalHomCode, evalCode_append_singleton, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact ih c hc
    · rw [S.homInterpretation_eq_evalGateOp keys.1 ek g.1
        fun i => g.2[i]?.elim []
          ((evalCode (S.homInterpretation keys.1 ek) [] cs₀ gates).getD · [])]
      exact S.length_evalGateOp_le hkeys ek g.1 _ _

/-- **Compactness of fixed-key homomorphic evaluation**: the output ciphertext has bit-length at
most `S.cipherBound n`, independent of the circuit size and depth. -/
theorem length_evalHomOutput_le {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support)
    (ek : List (List Bool)) (cs₀ : List (List Bool))
    (hcs₀ : ∀ c ∈ cs₀, c.length ≤ S.cipherBound n)
    (gates : List (Boolean.Op × List ℕ)) (o : ℕ) :
    (S.evalHomOutput keys.1 ek cs₀ gates o).length ≤ S.cipherBound n := by
  unfold evalHomOutput
  rw [List.getD_eq_getElem?_getD]
  rcases h : (S.evalHomCode keys.1 ek cs₀ gates)[o]? with _ | c
  · simp
  · exact S.length_mem_evalHomCode_le hkeys ek cs₀ hcs₀ gates c (List.mem_of_getElem? h)

/-! ### Fixed-key (pure) FHE under circular security (`fixedKeyFHE_of_circularSecure`) -/

/-- A fixed-key FHE public key consists of a base public key `pk` together with a circular
evaluation key `ek ← S.encryptKey pk sk` encrypting `sk` bit-by-bit under `pk`. -/
abbrev FixedPK := List Bool × List (List Bool)

/-- Framed encoding of a fixed-key FHE public key. -/
def encFixedPK : FixedPK ↪ List Bool :=
  encPair encBits (encList encBits)

/-- Distinguisher for the fixed-key FHE scheme. -/
abbrev FixedDistinguisher := ℕ → FixedPK × List Bool → ProbComp Bool

/-- Uniform strict PPT admissibility for fixed-key FHE distinguishers. -/
def IsFixedPKPPT (adversary : FixedDistinguisher) : Prop :=
  IsPPTOn (encPair encUnary (encPair encFixedPK encBits)) encBool (fun p => adversary p.1 p.2)

attribute [aesop norm unfold (rule_sets := [PPT])] IsFixedPKPPT encFixedPK
attribute [aesop norm unfold (rule_sets := [PolyTime])] encFixedPK

/-- Fixed-key FHE key generation at security parameter `n`: sample `(pk, sk) ← S.keyGen n` and a
circular evaluation key `ek ← S.encryptKey pk sk`, returning `((pk, ek), sk)`. -/
noncomputable def fixedKeyGen (S : EncryptionScheme) (n : ℕ) :
    ProbComp (FixedPK × List Bool) := do
  let keys ← S.keyGen n
  let ek ← S.encryptKey keys.1 keys.2
  return ((keys.1, ek), keys.2)

@[program_certificate]
theorem isPPTOn_fixedKeyGen (S : EncryptionScheme) :
    IsPPTOn encUnary (encPair encFixedPK encBits) S.fixedKeyGen := by
  unfold fixedKeyGen
  ppt

/-- The fixed-key (circular) encryption game at security parameter `n` and challenge bit `b`:
sample a fixed-key FHE key pair and encrypt `b` under `pk`. -/
noncomputable def fixedEncryptGame (S : EncryptionScheme) (b : Bool) (n : ℕ) :
    ProbComp (FixedPK × List Bool) := do
  let (fpk, _) ← S.fixedKeyGen n
  let c ← S.encrypt fpk.1 b
  return (fpk, c)

/-- **Circular security**: encryptions of `false` and `true` under `pk` remain computationally
indistinguishable even when the distinguisher is given a self-encrypted evaluation key
`ek ← S.encryptKey pk sk`. -/
def CircularSecure (S : EncryptionScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.fixedEncryptGame false n >>= adversary n))
    (fun adversary n => ProbComp.eval (S.fixedEncryptGame true n >>= adversary n))
    IsFixedPKPPT

/-- **Gentry's fixed-key bootstrapping theorem (`fixedKeyFHE_of_circularSecure`)**:
any encryption scheme `S` equipped with the assumed `Bootstrappable` interface that is circularly
secure yields a compact, pure fully homomorphic encryption scheme (`fixedKeyGen`, `encrypt`,
`evalHomOutput`, `decrypt`) that homomorphically evaluates De Morgan Boolean circuits and formulas
of arbitrary depth and size in deterministic polynomial time [Gentry2009]. -/
theorem fixedKeyFHE_of_circularSecure (hcir : S.CircularSecure) :
    IsPPTOn encUnary (encPair encFixedPK encBits) S.fixedKeyGen ∧
    ComputableTidilyInPolyTime
      (fun p : (((List Bool × List (List Bool)) × List (List Bool)) ×
          List (Boolean.Op × List ℕ)) × ℕ =>
        S.evalHomOutput p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair
        (encPair (encPair (encPair encBits (encList encBits)) (encList encBits))
          (encList Boolean.encGate))
        encNat)
      encBits ∧
    S.CircularSecure ∧
    PolynomiallyBounded S.cipherBound ∧
    (∀ n fpk sk, (fpk, sk) ∈ (ProbComp.eval (S.fixedKeyGen n)).support →
      ∀ {m o : ℕ} (c : Circuit Boolean.signature m o) (x : Fin m → Bool)
        (cs₀ : Fin m → List Bool),
        (∀ i, cs₀ i ∈ (ProbComp.eval (S.encrypt fpk.1 (x i))).support) →
        ∀ j : Fin o,
          S.decrypt sk
            (S.evalHomOutput fpk.1 fpk.2 (List.ofFn cs₀) c.code.1 (c.outputs j).toNat) =
            c.eval Boolean.interpretation x j ∧
          (S.evalHomOutput fpk.1 fpk.2 (List.ofFn cs₀) c.code.1 (c.outputs j).toNat).length ≤
            S.cipherBound n) ∧
    (∀ n fpk sk, (fpk, sk) ∈ (ProbComp.eval (S.fixedKeyGen n)).support →
      ∀ {m : ℕ} (F : Formula Boolean.signature m) (x : Fin m → Bool)
        (cs₀ : Fin m → List Bool),
        (∀ i, cs₀ i ∈ (ProbComp.eval (S.encrypt fpk.1 (x i))).support) →
        S.decrypt sk
          (S.evalHomOutput fpk.1 fpk.2 (List.ofFn cs₀) F.toCircuit.code.1
            (F.toCircuit.outputs 0).toNat) =
          F.eval Boolean.interpretation x ∧
        (S.evalHomOutput fpk.1 fpk.2 (List.ofFn cs₀) F.toCircuit.code.1
          (F.toCircuit.outputs 0).toNat).length ≤ S.cipherBound n) := by
  refine ⟨S.isPPTOn_fixedKeyGen, S.computableTidilyInPolyTime_evalHomOutput, hcir,
    S.polynomiallyBounded_cipherBound, ?_, ?_⟩
  · intro n fpk sk hfpk m o c x cs₀ hcs₀ j
    simp only [fixedKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfpk
    rcases hfpk with ⟨keys, hkeys, ek, hek, rfl, rfl⟩
    refine ⟨S.decrypt_evalHomOutput_circuit hkeys hek c x cs₀ hcs₀ j,
      S.length_evalHomOutput_le hkeys ek (List.ofFn cs₀) ?_ c.code.1 (c.outputs j).toNat⟩
    intro ct hct
    rcases List.mem_ofFn.mp hct with ⟨i, rfl⟩
    exact Bootstrappable.length_encrypt_le n keys hkeys (x i) (cs₀ i) (hcs₀ i)
  · intro n fpk sk hfpk m F x cs₀ hcs₀
    simp only [fixedKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfpk
    rcases hfpk with ⟨keys, hkeys, ek, hek, rfl, rfl⟩
    refine ⟨S.decrypt_evalHomOutput_formula hkeys hek F x cs₀ hcs₀,
      S.length_evalHomOutput_le hkeys ek (List.ofFn cs₀) ?_ F.toCircuit.code.1
        (F.toCircuit.outputs 0).toNat⟩
    intro ct hct
    rcases List.mem_ofFn.mp hct with ⟨i, rfl⟩
    exact Bootstrappable.length_encrypt_le n keys hkeys (x i) (cs₀ i) (hcs₀ i)

end EncryptionScheme

end Cslib.Crypto
