/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Circuit.Depth
public import Complexity.Computability.Circuit.Formula
public import Complexity.Computability.Probabilistic.Adaptive
public import Complexity.Computability.Probabilistic.Repeat
public import Complexity.Computability.Probabilistic.UniformNat
public import Complexity.Crypto.Computational.Basic
public import Complexity.Crypto.Game.Hybrid
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# Gentry's bootstrapping theorem

In Gentry's work, a public-key bit encryption scheme is **bootstrappable** when its homomorphic
evaluation algorithm can evaluate the scheme's own augmented decryption circuits
`Dec(·, c₁) op Dec(·, c₂)` (for each De Morgan gate `op`) on an encrypted secret key, producing
refreshed ciphertexts whose length is bounded by a polynomial in the security parameter
independently of the evaluated circuit's size and depth [Gentry2009].

This module does **not** construct such a homomorphic evaluation of the decryption circuit, nor
does it prove that any concrete scheme is bootstrappable. Instead, `Bootstrappable` is an
**assumed interface**: an opaque deterministic polynomial-time gate-plus-key-switch operation
`evalAugDecrypt op pk₂ ek c₁ c₂`, whose recryption/gate correctness and compactness are taken as
fields of the class. From this interface (together with semantic or circular security, also
assumed as hypotheses) the module proves Gentry's bootstrapping *composition*: chaining the
assumed gate operations yields leveled, respectively fixed-key, fully homomorphic encryption.

We formalize two main theorems:

1. **Leveled bootstrapping (`leveledFHE_of_bootstrappable`)**: Any semantically secure encryption
   scheme `S` equipped with the `Bootstrappable` interface and any unary polynomial-time depth
   bound `D : ℕ → ℕ` yield a compact leveled fully homomorphic encryption scheme evaluating all
   De Morgan circuits (and formulas) of depth at most `D n`. Key generation samples an acyclic
   chain of `D n + 1` key pairs `(pk_0, sk_0), …, (pk_{D n}, sk_{D n})` and publishes the
   evaluation keys
   `ek_ℓ ← S.encryptKey pk_{ℓ+1} sk_ℓ` for `0 ≤ ℓ < D n`. Semantic security follows by a uniform
   two-level hybrid reduction (across the `D n` levels from top to bottom and across the
   `S.skLength n` secret-key bits within each level) replacing each `ek_ℓ` with encryptions of
   all-zero dummy keys `0^{S.skLength n}`.

2. **Fixed-key FHE under circular security (`fixedKeyFHE_of_circularSecure`)**: If publishing a
   single self-encrypted evaluation key `ek ← S.encryptKey pk sk` preserves semantic security
   (`CircularSecure`), the same homomorphic gate evaluation using the single key `(pk, ek)`
   evaluates De Morgan circuits and formulas of **arbitrary** depth (with no depth bound fixed at
   key generation), while maintaining polynomial-time evaluation and compactness.

## Main definitions

* `Cslib.Crypto.EncryptionScheme`: uniform public-key bit encryption scheme with tidy efficiency
  and correctness on the support of `keyGen`.
* `Cslib.Crypto.EncryptionScheme.SemanticSecure`: semantic security against uniform strict PPT
  distinguishers (`IsPKPPT`).
* `Cslib.Crypto.EncryptionScheme.encryptKey`: bit-by-bit encryption of a secret key word.
* `Cslib.Crypto.Bootstrappable`: assumed interface for an augmented De Morgan decryption gate
  with key switching (`evalAugDecrypt`), whose correctness and compactness bound `cipherBound`
  are fields rather than consequences of a homomorphic evaluation of the decryption circuit.
* `Cslib.Crypto.EncryptionScheme.leveledKeyGen`, `evalLeveledCode`, `evalLeveledOutput`:
  leveled key-chain generation and synchronous level-by-level homomorphic circuit evaluation.
* `Cslib.Crypto.EncryptionScheme.fixedKeyGen`, `evalHomCode`, `evalHomOutput`:
  fixed-key circular evaluation key generation and gate-by-gate homomorphic circuit evaluation.
* `Cslib.Crypto.EncryptionScheme.CircularSecure`: semantic security in the presence of a
  self-encrypted secret key `ek ← S.encryptKey pk sk`.

## Main results

* `Cslib.Crypto.EncryptionScheme.isPPTOn_encryptKey`: uniform strict PPT certificate for
  bit-by-bit key encryption.
* `Cslib.Crypto.EncryptionScheme.encryptKeyTest_gap`: exact signed hybrid gap for replacing an
  encrypted secret key with an encryption of `0^m`.
* `Cslib.Crypto.EncryptionScheme.leveledSemanticSecure_of_semanticSecure`: semantic security of the
  acyclic key chain of length `D n`.
* `Cslib.Crypto.EncryptionScheme.leveledFHE_of_bootstrappable`: Gentry's leveled bootstrapping
  composition (efficiency, correctness up to depth `D n`, compactness, and semantic security),
  assuming the `Bootstrappable` interface and semantic security.
* `Cslib.Crypto.EncryptionScheme.fixedKeyFHE_of_circularSecure`: Gentry's pure/fixed-key FHE
  composition for circuits of arbitrary depth, assuming the `Bootstrappable` interface and
  circular security.

## References

* [C. Gentry, *Fully Homomorphic Encryption Using Ideal Lattices*][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM Circuits
open scoped NNReal

/-! ### Public-key bit encryption schemes -/

/-- A distinguisher for a public-key bit encryption scheme receives the unary security parameter,
a public key, and a challenge ciphertext. -/
abbrev PKDistinguisher := ℕ → List Bool × List Bool → ProbComp Bool

/-- Uniform strict polynomial-time admissibility for public-key distinguishers. -/
def IsPKPPT (adversary : PKDistinguisher) : Prop :=
  IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool (fun p => adversary p.1 p.2)

attribute [aesop norm unfold (rule_sets := [PPT])] IsPKPPT

/-- A uniform public-key bit encryption scheme with tidy polynomial-time key generation, encryption,
and deterministic decryption, fixed secret-key bit length `skLength n` at security parameter `n`,
and perfect decryption correctness on supported key pairs and ciphertexts. -/
structure EncryptionScheme where
  /-- Sample a public/secret key pair `(pk, sk)` at unary security parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Encrypt a single bit `b` under public key `pk`. -/
  encrypt : List Bool → Bool → ProbComp (List Bool)
  /-- Deterministically decrypt a ciphertext `c` using secret key `sk`. -/
  decrypt : List Bool → List Bool → Bool
  /-- Bit length of secret keys generated at security parameter `n`. -/
  skLength : ℕ → ℕ
  /-- Key generation is uniformly strict PPT in the unary parameter. -/
  keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) keyGen
  /-- Encryption is uniformly strict PPT in the public key and plaintext bit. -/
  encrypt_ppt : IsPPTOn (encPair encBits encBool) encBits (fun p => encrypt p.1 p.2)
  /-- Decryption is computable tidily in polynomial time. -/
  decrypt_polyTime : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => decrypt p.1 p.2) (encPair encBits encBits) encBool
  /-- The secret-key length function is computable tidily in polynomial time in unary. -/
  skLength_polyTime : ComputableTidilyInPolyTime skLength encUnary encUnary
  /-- Every secret key sampled at parameter `n` has length `skLength n`. -/
  length_sk : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support → keys.2.length = skLength n
  /-- Decryption recovers the encrypted bit for every supported key pair and ciphertext. -/
  decrypt_encrypt : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
    ∀ b c, c ∈ (ProbComp.eval (encrypt keys.1 b)).support → decrypt keys.2 c = b

namespace EncryptionScheme

attribute [program_certificate]
  keyGen_ppt encrypt_ppt decrypt_polyTime skLength_polyTime

@[program_certificate]
theorem isPPTOn_keyGen_comp (S : EncryptionScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    IsPPTOn encIn (encPair encBits encBits) (fun a => S.keyGen (n a)) :=
  S.keyGen_ppt.preprocess hn

@[program_certificate]
theorem isPPTOn_encrypt_comp (S : EncryptionScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {pk : γ → List Bool} {b : γ → Bool}
    (hpk : ComputableTidilyInPolyTime pk encIn encBits)
    (hb : ComputableTidilyInPolyTime b encIn encBool) :
    IsPPTOn encIn encBits (fun a => S.encrypt (pk a) (b a)) :=
  S.encrypt_ppt.preprocess (hpk.prod hb)

@[program_certificate]
theorem computableTidilyInPolyTime_decrypt_comp (S : EncryptionScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {sk c : γ → List Bool}
    (hsk : ComputableTidilyInPolyTime sk encIn encBits)
    (hc : ComputableTidilyInPolyTime c encIn encBits) :
    ComputableTidilyInPolyTime (fun a => S.decrypt (sk a) (c a)) encIn encBool :=
  S.decrypt_polyTime.comp (hsk.prod hc)

@[program_certificate]
theorem computableTidilyInPolyTime_skLength_comp (S : EncryptionScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun a => S.skLength (n a)) encIn encUnary :=
  S.skLength_polyTime.comp hn

/-- Sample a key pair and encrypt the challenge bit `b` under the public key. -/
noncomputable def encryptGame (S : EncryptionScheme) (b : Bool) (n : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let keys ← S.keyGen n
  let c ← S.encrypt keys.1 b
  return (keys.1, c)

@[program_certificate]
theorem isPPTOn_encryptGame (S : EncryptionScheme) (b : Bool) :
    IsPPTOn encUnary (encPair encBits encBits) (S.encryptGame b) := by
  unfold encryptGame
  ppt

/-- Semantic security (IND-CPA for single-bit public-key encryption): no uniform strict PPT
distinguisher can distinguish encryptions of `false` from encryptions of `true`. -/
def SemanticSecure (S : EncryptionScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.encryptGame false n >>= adversary n))
    (fun adversary n => ProbComp.eval (S.encryptGame true n >>= adversary n))
    IsPKPPT

/-! ### Bit-by-bit key encryption (`encryptKey`) -/

/-- Encrypt a bit string `msg` bit-by-bit under public key `pk`. Used to produce evaluation keys
encrypting a secret key `sk : List Bool`. -/
noncomputable def encryptKey (S : EncryptionScheme) (pk : List Bool) :
    List Bool → ProbComp (List (List Bool))
  | [] => pure []
  | b :: bs => do
    let c ← S.encrypt pk b
    let cs ← S.encryptKey pk bs
    return c :: cs

@[simp]
theorem encryptKey_nil (S : EncryptionScheme) (pk : List Bool) :
    S.encryptKey pk [] = pure [] := rfl

@[simp]
theorem encryptKey_cons (S : EncryptionScheme) (pk : List Bool) (b : Bool) (bs : List Bool) :
    S.encryptKey pk (b :: bs) = do
      let c ← S.encrypt pk b
      let cs ← S.encryptKey pk bs
      return c :: cs := rfl

/-- Encrypting a concatenated bit string is equivalent in distribution to encrypting both halves
independently and concatenating the resulting ciphertext lists. -/
theorem eval_encryptKey_append (S : EncryptionScheme) (pk : List Bool) (u v : List Bool) :
    ProbComp.eval (S.encryptKey pk (u ++ v)) =
      ProbComp.eval (do
        let cu ← S.encryptKey pk u
        let cv ← S.encryptKey pk v
        return cu ++ cv) := by
  induction u with
  | nil => simp
  | cons b u ih =>
    simp only [List.cons_append, encryptKey_cons, ProbComp.eval_bind, ProbComp.eval_pure,
      ih, PMF.bind_bind, PMF.pure_bind]

/-- Every ciphertext list in the support of `encryptKey pk msg` has the same length as `msg`. -/
theorem length_of_mem_support_encryptKey (S : EncryptionScheme) (pk : List Bool) (msg : List Bool)
    {cs : List (List Bool)} (hcs : cs ∈ (ProbComp.eval (S.encryptKey pk msg)).support) :
    cs.length = msg.length := by
  induction msg generalizing cs with
  | nil =>
    simp only [encryptKey_nil, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hcs
    simp [hcs]
  | cons b bs ih =>
    simp only [encryptKey_cons, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.support_pure, Set.mem_singleton_iff] at hcs
    rcases hcs with ⟨c, _, cs', hcs', rfl⟩
    simp [ih hcs']

/-- Decrypting each ciphertext in `encryptKey keys.1 msg` under `keys.2` recovers `msg`. -/
theorem map_decrypt_of_mem_support_encryptKey (S : EncryptionScheme) {n : ℕ}
    {keys : List Bool × List Bool} (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support)
    (msg : List Bool) {cs : List (List Bool)}
    (hcs : cs ∈ (ProbComp.eval (S.encryptKey keys.1 msg)).support) :
    cs.map (S.decrypt keys.2) = msg := by
  induction msg generalizing cs with
  | nil =>
    simp only [encryptKey_nil, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hcs
    simp [hcs]
  | cons b bs ih =>
    simp only [encryptKey_cons, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.support_pure, Set.mem_singleton_iff] at hcs
    rcases hcs with ⟨c, hc, cs', hcs', rfl⟩
    simp [S.decrypt_encrypt n keys hkeys b c hc, ih hcs']

/-- One step of iterative bit-by-bit encryption, consuming the head of the remaining plaintext bits
and appending its encryption to the accumulated ciphertext list. -/
noncomputable def encryptKeyStep (S : EncryptionScheme) (pk : List Bool)
    (state : List Bool × List (List Bool)) : ProbComp (List Bool × List (List Bool)) := do
  let c ← S.encrypt pk (state.1.headD false)
  return (state.1.tail, state.2 ++ [c])

private theorem encryptKey_eq_iterate_aux (S : EncryptionScheme) (pk : List Bool)
    (msg : List Bool) (acc : List (List Bool)) :
    Prod.snd <$> OracleComp.iterate msg.length (S.encryptKeyStep pk) (msg, acc) =
      (fun cs => acc ++ cs) <$> S.encryptKey pk msg := by
  induction msg generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.length_cons, OracleComp.iterate_succ_bind, encryptKeyStep, List.headD_cons,
      List.tail_cons, bind_assoc, pure_bind, map_bind, ih, encryptKey_cons]
    simp only [map_eq_bind_pure_comp, Function.comp_def, pure_bind,
      List.append_assoc, List.singleton_append]

/-- `encryptKey` is realized by a bounded `OracleComp.iterate` loop of length `msg.length`. -/
theorem encryptKey_eq_iterate (S : EncryptionScheme) (pk : List Bool) (msg : List Bool) :
    S.encryptKey pk msg =
      Prod.snd <$> OracleComp.iterate msg.length (S.encryptKeyStep pk) (msg, []) := by
  simpa using (S.encryptKey_eq_iterate_aux pk msg []).symm

@[program_certificate]
theorem isPPTOn_encryptKeyStep (S : EncryptionScheme) :
    IsPPTOn (encPair encBits (encPair encBits (encList encBits)))
      (encPair encBits (encList encBits))
      (fun p => S.encryptKeyStep p.1 p.2) := by
  unfold encryptKeyStep
  ppt

/-- Bit-by-bit key encryption is uniformly strict PPT in the public key and message bit string. -/
@[program_certificate]
theorem isPPTOn_encryptKey (S : EncryptionScheme) :
    IsPPTOn (encPair encBits encBits) (encList encBits) (fun p => S.encryptKey p.1 p.2) := by
  have heq : (fun p : List Bool × List Bool => S.encryptKey p.1 p.2) =
      fun p => Prod.snd <$> OracleComp.iterate p.2.length (S.encryptKeyStep p.1) (p.2, []) := by
    funext p
    exact S.encryptKey_eq_iterate p.1 p.2
  rw [heq]
  obtain ⟨k, d, hlen⟩ := S.encrypt_ppt.length_le
  have hiter : IsPPTOn (encPair encBits encBits) (encPair encBits (encList encBits))
      (fun p : List Bool × List Bool =>
        OracleComp.iterate p.2.length (S.encryptKeyStep p.1) (p.2, [])) := by
    refine IsPPTOn.iterateWith_of_bounded_growth
      (count := fun p : List Bool × List Bool => p.2.length)
      (initial := fun p : List Bool × List Bool => (p.2, []))
      (step := fun (p : List Bool × List Bool) state => S.encryptKeyStep p.1 state)
      (by polytime) (by polytime) (by ppt)
      (growth := fun p : List Bool × List Bool =>
        2 * (k * (2 * p.1.length + 4) ^ d) + 2)
      (show ComputableTidilyInPolyTime
        (fun p : List Bool × List Bool => 2 * (k * (2 * p.1.length + 4) ^ d) + 2)
        (encPair encBits encBits) encUnary by polytime).polyBounded ?_
    intro p state next hnext
    simp only [encryptKeyStep, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.support_pure, Set.mem_singleton_iff] at hnext
    rcases hnext with ⟨c, hc, rfl⟩
    have hc_bound := hlen (p.1, state.1.headD false) c hc
    have hpair_len : (encPair encBits encBool (p.1, state.1.headD false)).length + 1 ≤
        2 * p.1.length + 4 := by
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton]
      omega
    have hc_le : c.length ≤ k * (2 * p.1.length + 4) ^ d := by
      simpa only [encBits_apply] using
        hc_bound.trans (Nat.mul_le_mul_left k (Nat.pow_le_pow_left hpair_len d))
    have htail : state.1.tail.length ≤ state.1.length := by simp
    simp only [length_encPair, encBits_apply, encList_append, encList_cons, encList_nil,
      List.length_append, List.length_nil, length_frame]
    omega
  exact hiter.map (ComputableTidilyInPolyTime.snd _ _)

@[program_certificate]
theorem isPPTOn_encryptKey_comp (S : EncryptionScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {pk msg : γ → List Bool}
    (hpk : ComputableTidilyInPolyTime pk encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits) :
    IsPPTOn encIn (encList encBits) (fun a => S.encryptKey (pk a) (msg a)) :=
  S.isPPTOn_encryptKey.preprocess (hpk.prod hmsg)

/-! ### Hybrid reduction for `encryptKey` -/

variable {α : Type}

/-- Replace the first `j` bits of `word a` with `false` when encrypting under a fresh public key. -/
noncomputable def encryptKeyHybrid (S : EncryptionScheme) (n : ℕ) (P : ProbComp α)
    (word : α → List Bool) (F : α → List Bool → List (List Bool) → ProbComp Bool) (j : ℕ) :
    ProbComp Bool := do
  let a ← P
  let keys ← S.keyGen n
  let ek ← S.encryptKey keys.1 (List.replicate j false ++ (word a).drop j)
  F a keys.1 ek

/-- Select `c` when `b = true`, or a fresh encryption of `false` under `pk` when `b = false`. -/
noncomputable def selectBitCiphertext (S : EncryptionScheme) (pk c : List Bool) (b : Bool) :
    ProbComp (List Bool) :=
  if b then pure c else S.encrypt pk false

@[program_certificate]
theorem isPPTOn_selectBitCiphertext (S : EncryptionScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {pk c : γ → List Bool} {b : γ → Bool}
    (hpk : ComputableTidilyInPolyTime pk encIn encBits)
    (hc : ComputableTidilyInPolyTime c encIn encBits)
    (hb : ComputableTidilyInPolyTime b encIn encBool) :
    IsPPTOn encIn encBits (fun a => S.selectBitCiphertext (pk a) (c a) (b a)) :=
  IsPPTOn.cond hb hc.isPPTOn
    (S.encrypt_ppt.preprocess (hpk.prod (ComputableTidilyInPolyTime.const false)))

/-- Single-bit hybrid test at bit coordinate `j`: if bit `j` of `word a` is `true`, insert the
challenge ciphertext `challenge.2`; if bit `j` is `false`, encrypt `false` directly under
`challenge.1`. -/
noncomputable def encryptKeyBitTest (S : EncryptionScheme) (P : ProbComp α)
    (word : α → List Bool) (F : α → List Bool → List (List Bool) → ProbComp Bool) (j : ℕ)
    (challenge : List Bool × List Bool) : ProbComp Bool := do
  let a ← P
  let cMid ← S.selectBitCiphertext challenge.1 challenge.2 ((word a).getD j false)
  let cPrefix ← S.encryptKey challenge.1 (List.replicate j false)
  let cSuffix ← S.encryptKey challenge.1 ((word a).drop (j + 1))
  F a challenge.1 (cPrefix ++ cMid :: cSuffix)

@[simp]
theorem encryptKeyHybrid_zero (S : EncryptionScheme) (n : ℕ) (P : ProbComp α)
    (word : α → List Bool) (F : α → List Bool → List (List Bool) → ProbComp Bool) :
    S.encryptKeyHybrid n P word F 0 = (do
      let a ← P
      let keys ← S.keyGen n
      let ek ← S.encryptKey keys.1 (word a)
      F a keys.1 ek) := by
  simp [encryptKeyHybrid]

theorem eval_encryptKeyHybrid_self (S : EncryptionScheme) (n : ℕ) (P : ProbComp α)
    (word : α → List Bool) (F : α → List Bool → List (List Bool) → ProbComp Bool) (m : ℕ)
    (hword : ∀ a ∈ (ProbComp.eval P).support, (word a).length = m) :
    ProbComp.eval (S.encryptKeyHybrid n P word F m) =
      ProbComp.eval (do
        let a ← P
        let keys ← S.keyGen n
        let ek ← S.encryptKey keys.1 (List.replicate m false)
        F a keys.1 ek) := by
  simp only [encryptKeyHybrid, ProbComp.eval_bind]
  apply PMF.bind_congr_on_support
  intro a ha
  have hdrop : (word a).drop m = [] := List.drop_eq_nil_of_le (hword a ha).le
  simp [hdrop]

private theorem eval_encrypt_ite_true (S : EncryptionScheme) (pk : List Bool) (b : Bool)
    (G : List Bool → ProbComp Bool) :
    ProbComp.eval (do
      let c ← S.encrypt pk true
      let cMid ← S.selectBitCiphertext pk c b
      G cMid) =
    ProbComp.eval (S.encrypt pk b >>= G) := by
  cases b <;> simp [selectBitCiphertext, ProbComp.eval_bind, PMF.bind_const]

private theorem eval_encrypt_ite_false (S : EncryptionScheme) (pk : List Bool) (b : Bool)
    (G : List Bool → ProbComp Bool) :
    ProbComp.eval (do
      let c ← S.encrypt pk false
      let cMid ← S.selectBitCiphertext pk c b
      G cMid) =
    ProbComp.eval (S.encrypt pk false >>= G) := by
  cases b <;> simp [selectBitCiphertext, ProbComp.eval_bind, PMF.bind_const]

/-- Splicing a single encrypted bit between two `encryptKey` segments is equivalent in distribution
to `encryptKey` on the concatenated bit string `u ++ b :: v`. -/
theorem eval_encryptKey_splice (S : EncryptionScheme) (pk : List Bool) (u : List Bool)
    (b : Bool) (v : List Bool) (G : List (List Bool) → ProbComp Bool) :
    ProbComp.eval (do
      let cMid ← S.encrypt pk b
      let cPrefix ← S.encryptKey pk u
      let cSuffix ← S.encryptKey pk v
      G (cPrefix ++ cMid :: cSuffix)) =
    ProbComp.eval (S.encryptKey pk (u ++ b :: v) >>= G) := by
  have h := congrArg (fun μ => μ.bind fun cs => ProbComp.eval (G cs))
    (S.eval_encryptKey_append pk u (b :: v))
  simp only [encryptKey_cons, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind] at h ⊢
  rw [h]
  exact PMF.bind_comm _ _ _

/-- When challenged with an encryption of `true`, `encryptKeyBitTest` at coordinate `j < m`
reproduces `encryptKeyHybrid` at `j`. -/
theorem eval_encryptKeyBitTest_true (S : EncryptionScheme) (n : ℕ) (P : ProbComp α)
    (word : α → List Bool) (F : α → List Bool → List (List Bool) → ProbComp Bool) {m j : ℕ}
    (hj : j < m) (hword : ∀ a ∈ (ProbComp.eval P).support, (word a).length = m) :
    ProbComp.eval (S.encryptGame true n >>= S.encryptKeyBitTest P word F j) =
      ProbComp.eval (S.encryptKeyHybrid n P word F j) := by
  have hcomm : ProbComp.eval (S.encryptGame true n >>= S.encryptKeyBitTest P word F j) =
      ProbComp.eval (do
        let a ← P
        let keys ← S.keyGen n
        let c ← S.encrypt keys.1 true
        let cMid ← S.selectBitCiphertext keys.1 c ((word a).getD j false)
        let cPrefix ← S.encryptKey keys.1 (List.replicate j false)
        let cSuffix ← S.encryptKey keys.1 ((word a).drop (j + 1))
        F a keys.1 (cPrefix ++ cMid :: cSuffix)) := by
    simp only [encryptKeyBitTest, ProbComp.eval_bind]
    rw [PMF.bind_comm (ProbComp.eval (S.encryptGame true n)) (ProbComp.eval P)]
    simp only [encryptGame, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  rw [hcomm]
  simp only [encryptKeyHybrid, ProbComp.eval_bind]
  apply PMF.bind_congr_on_support
  intro a ha
  congr 1
  funext keys
  have hite := S.eval_encrypt_ite_true keys.1 ((word a).getD j false) (fun cMid => do
    let cPrefix ← S.encryptKey keys.1 (List.replicate j false)
    let cSuffix ← S.encryptKey keys.1 ((word a).drop (j + 1))
    F a keys.1 (cPrefix ++ cMid :: cSuffix))
  simp only [ProbComp.eval_bind] at hite
  rw [hite]
  have hsplice := S.eval_encryptKey_splice keys.1 (List.replicate j false)
    ((word a).getD j false) ((word a).drop (j + 1)) (F a keys.1)
  simp only [ProbComp.eval_bind] at hsplice
  rw [hsplice]
  have hj_lt : j < (word a).length := hj.trans_eq (hword a ha).symm
  have hdrop : (word a).getD j false :: (word a).drop (j + 1) = (word a).drop j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_lt, Option.getD_some,
      ← List.drop_eq_getElem_cons hj_lt]
  rw [hdrop]

/-- When challenged with an encryption of `false`, `encryptKeyBitTest` at coordinate `j`
reproduces `encryptKeyHybrid` at `j + 1`. -/
theorem eval_encryptKeyBitTest_false (S : EncryptionScheme) (n : ℕ) (P : ProbComp α)
    (word : α → List Bool) (F : α → List Bool → List (List Bool) → ProbComp Bool) (j : ℕ) :
    ProbComp.eval (S.encryptGame false n >>= S.encryptKeyBitTest P word F j) =
      ProbComp.eval (S.encryptKeyHybrid n P word F (j + 1)) := by
  have hcomm : ProbComp.eval (S.encryptGame false n >>= S.encryptKeyBitTest P word F j) =
      ProbComp.eval (do
        let a ← P
        let keys ← S.keyGen n
        let c ← S.encrypt keys.1 false
        let cMid ← S.selectBitCiphertext keys.1 c ((word a).getD j false)
        let cPrefix ← S.encryptKey keys.1 (List.replicate j false)
        let cSuffix ← S.encryptKey keys.1 ((word a).drop (j + 1))
        F a keys.1 (cPrefix ++ cMid :: cSuffix)) := by
    simp only [encryptKeyBitTest, ProbComp.eval_bind]
    rw [PMF.bind_comm (ProbComp.eval (S.encryptGame false n)) (ProbComp.eval P)]
    simp only [encryptGame, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  rw [hcomm]
  simp only [encryptKeyHybrid, ProbComp.eval_bind]
  congr 1
  funext a
  congr 1
  funext keys
  have hite := S.eval_encrypt_ite_false keys.1 ((word a).getD j false) (fun cMid => do
    let cPrefix ← S.encryptKey keys.1 (List.replicate j false)
    let cSuffix ← S.encryptKey keys.1 ((word a).drop (j + 1))
    F a keys.1 (cPrefix ++ cMid :: cSuffix))
  simp only [ProbComp.eval_bind] at hite
  rw [hite]
  have hsplice := S.eval_encryptKey_splice keys.1 (List.replicate j false)
    false ((word a).drop (j + 1)) (F a keys.1)
  simp only [ProbComp.eval_bind] at hsplice
  rw [hsplice, List.replicate_succ', List.append_assoc, List.singleton_append]

/-- Uniformly sample a bit coordinate `j` from a dyadic range of size `dyadicSize m` and run
`encryptKeyBitTest` when `j < m`. -/
noncomputable def encryptKeyTest (S : EncryptionScheme) (P : ProbComp α)
    (word : α → List Bool) (F : α → List Bool → List (List Bool) → ProbComp Bool) (m : ℕ)
    (challenge : List Bool × List Bool) : ProbComp Bool := do
  let j ← sampleDyadicIndex m
  if j < m then S.encryptKeyBitTest P word F j challenge else pure false

/-- The single-challenge test `encryptKeyTest` captures the signed gap between encrypting `word a`
and encrypting `0^m`, with loss `dyadicSize m`. -/
theorem encryptKeyTest_gap (S : EncryptionScheme) (n : ℕ) (P : ProbComp α)
    (word : α → List Bool) (F : α → List Bool → List (List Bool) → ProbComp Bool) (m : ℕ)
    (hword : ∀ a ∈ (ProbComp.eval P).support, (word a).length = m) :
    (Game.succProbability (ProbComp.eval (do
        let a ← P
        let keys ← S.keyGen n
        let ek ← S.encryptKey keys.1 (word a)
        F a keys.1 ek)) : ℝ) -
      Game.succProbability (ProbComp.eval (do
        let a ← P
        let keys ← S.keyGen n
        let ek ← S.encryptKey keys.1 (List.replicate m false)
        F a keys.1 ek)) =
      (dyadicSize m : ℝ) *
        ((Game.succProbability
            (ProbComp.eval (S.encryptGame true n >>= S.encryptKeyTest P word F m)) : ℝ) -
          Game.succProbability
            (ProbComp.eval (S.encryptGame false n >>= S.encryptKeyTest P word F m))) := by
  unfold encryptKeyTest
  have htrue := eval_bind_sampleDyadicIndex_guard (S.encryptGame true n) m
    (fun j => S.encryptKeyBitTest P word F j) false
  have hfalse := eval_bind_sampleDyadicIndex_guard (S.encryptGame false n) m
    (fun j => S.encryptKeyBitTest P word F j) false
  simp only [eval_encryptKeyBitTest_false] at hfalse
  have htrue' :
      ProbComp.eval (S.encryptGame true n >>= fun challenge => do
        let j ← sampleDyadicIndex m
        if j < m then S.encryptKeyBitTest P word F j challenge else pure false) =
      (PMF.uniformOfFintype (Fin (dyadicSize m))).bind fun j =>
        if j.val < m then ProbComp.eval (S.encryptKeyHybrid n P word F j.val)
        else PMF.pure false := by
    rw [htrue]
    congr 1
    funext j
    split_ifs with hj
    · exact S.eval_encryptKeyBitTest_true n P word F hj hword
    · rfl
  have h := Game.succProbability_hybrid_average
    (fun j => ProbComp.eval (S.encryptKeyHybrid n P word F j))
    m (dyadicSize m) (lt_dyadicSize m).le
  simpa only [encryptKeyHybrid_zero, eval_encryptKeyHybrid_self S n P word F m hword,
    htrue', hfalse] using h

theorem isPPTOn_encryptKeyBitTest (S : EncryptionScheme) {Caller : Type}
    {input : Caller ↪ List Bool} {encA : α ↪ List Bool}
    {P : Caller → ProbComp α} {word : α → List Bool}
    {F : Caller → α → List Bool → List (List Bool) → ProbComp Bool}
    {j : Caller → ℕ} {challenge : Caller → List Bool × List Bool}
    (hP : IsPPTOn input encA P)
    (hword : ComputableTidilyInPolyTime word encA encBits)
    (hF : IsPPTOn (encPair (encPair input encA) (encPair encBits (encList encBits))) encBool
      (fun p => F p.1.1 p.1.2 p.2.1 p.2.2))
    (hj : ComputableTidilyInPolyTime j input encUnary)
    (hchallenge : ComputableTidilyInPolyTime challenge input (encPair encBits encBits)) :
    IsPPTOn input encBool
      (fun caller =>
        S.encryptKeyBitTest (P caller) word (F caller) (j caller) (challenge caller)) := by
  have hpk : ComputableTidilyInPolyTime (fun c => (challenge c).1) input encBits :=
    (ComputableTidilyInPolyTime.fst _ _).comp hchallenge
  have hc : ComputableTidilyInPolyTime (fun c => (challenge c).2) input encBits :=
    (ComputableTidilyInPolyTime.snd _ _).comp hchallenge
  have hMid : IsPPTOn (encPair input encA) encBits
      (fun p : Caller × α =>
        S.selectBitCiphertext (challenge p.1).1 (challenge p.1).2
          ((word p.2).getD (j p.1) false)) :=
    S.isPPTOn_selectBitCiphertext (by polytime) (by polytime) (by polytime)
  have hF' :
      IsPPTOn
        (encPair (encPair (encPair (encPair input encA) encBits) (encList encBits))
          (encList encBits))
        encBool
        (fun p : (((Caller × α) × List Bool) × List (List Bool)) × List (List Bool) =>
          F p.1.1.1.1 p.1.1.1.2 (challenge p.1.1.1.1).1
            (p.1.2 ++ p.1.1.2 :: p.2)) :=
    hF.preprocess
      (prepare := fun p : (((Caller × α) × List Bool) × List (List Bool)) × List (List Bool) =>
        ((p.1.1.1.1, p.1.1.1.2), ((challenge p.1.1.1.1).1, p.1.2 ++ p.1.1.2 :: p.2)))
      (by polytime)
  unfold encryptKeyBitTest
  refine hP.bind_with (hMid.bind_with ?_)
  refine (S.isPPTOn_encryptKey_comp (by polytime) (by polytime)).bind_with ?_
  exact (S.isPPTOn_encryptKey_comp (by polytime) (by polytime)).bind_with hF'

theorem isPPTOn_encryptKeyTest (S : EncryptionScheme) {Caller : Type}
    {input : Caller ↪ List Bool} {encA : α ↪ List Bool}
    {P : Caller → ProbComp α} {word : α → List Bool}
    {F : Caller → α → List Bool → List (List Bool) → ProbComp Bool}
    {m : Caller → ℕ} {challenge : Caller → List Bool × List Bool}
    (hP : IsPPTOn input encA P)
    (hword : ComputableTidilyInPolyTime word encA encBits)
    (hF : IsPPTOn (encPair (encPair input encA) (encPair encBits (encList encBits))) encBool
      (fun p => F p.1.1 p.1.2 p.2.1 p.2.2))
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (hchallenge : ComputableTidilyInPolyTime challenge input (encPair encBits encBits)) :
    IsPPTOn input encBool
      (fun caller =>
        S.encryptKeyTest (P caller) word (F caller) (m caller) (challenge caller)) := by
  have hbit : IsPPTOn (encPair input encUnary) encBool
      (fun p : Caller × ℕ =>
        S.encryptKeyBitTest (P p.1) word (F p.1) p.2 (challenge p.1)) :=
    S.isPPTOn_encryptKeyBitTest (by ppt) hword (by ppt) (by polytime) (by polytime)
  unfold encryptKeyTest
  ppt

/-! ### Acyclic key-chain generation and leveled semantic security -/

/-- An evaluation key chain is a list of `(pk_{ℓ+1}, ek_ℓ)` pairs where `ek_ℓ` encrypts `sk_ℓ`
bit-by-bit under `pk_{ℓ+1}`. -/
abbrev EvalChain := List (List Bool × List (List Bool))

/-- Framed encoding of an evaluation key chain. -/
def encEvalChain : EvalChain ↪ List Bool :=
  encList (encPair encBits (encList encBits))

/-- A leveled public key consists of the level-0 public key `pk_0` together with the evaluation
key chain `[(pk_1, ek_0), …, (pk_L, ek_{L-1})]`. -/
abbrev LeveledPK := List Bool × EvalChain

/-- Framed encoding of a leveled public key. -/
def encLeveledPK : LeveledPK ↪ List Bool :=
  encPair encBits encEvalChain

/-- A distinguisher for the leveled encryption scheme receives the unary security parameter, a
leveled public key, and a challenge ciphertext. -/
abbrev LeveledDistinguisher := ℕ → LeveledPK × List Bool → ProbComp Bool

/-- Uniform strict polynomial-time admissibility for leveled public-key distinguishers. -/
def IsLeveledPKPPT (adversary : LeveledDistinguisher) : Prop :=
  IsPPTOn (encPair encUnary (encPair encLeveledPK encBits)) encBool (fun p => adversary p.1 p.2)

attribute [aesop norm unfold (rule_sets := [PPT])] IsLeveledPKPPT encLeveledPK encEvalChain
attribute [aesop norm unfold (rule_sets := [PolyTime])] encLeveledPK encEvalChain

/-- One step of real key-chain generation at security parameter `n`: sample a fresh key pair
`(pk, sk)`, encrypt the current secret key (truncated to `skLength n` so that state growth is
uniformly bounded on all inputs) under `pk`, and append `(pk, ek)` to the chain. -/
noncomputable def genRealStep (S : EncryptionScheme) (n : ℕ)
    (state : EvalChain × List Bool) : ProbComp (EvalChain × List Bool) := do
  let keys ← S.keyGen n
  let ek ← S.encryptKey keys.1 (state.2.take (S.skLength n))
  return (state.1 ++ [(keys.1, ek)], keys.2)

/-- Generate `r` real evaluation-key levels starting from initial secret key `sk₀`. -/
noncomputable def genRealChain (S : EncryptionScheme) (n r : ℕ) (sk₀ : List Bool) :
    ProbComp (EvalChain × List Bool) :=
  OracleComp.iterate r (S.genRealStep n) ([], sk₀)

@[simp]
theorem genRealChain_zero (S : EncryptionScheme) (n : ℕ) (sk₀ : List Bool) :
    S.genRealChain n 0 sk₀ = pure ([], sk₀) := rfl

theorem genRealChain_succ (S : EncryptionScheme) (n r : ℕ) (sk₀ : List Bool) :
    S.genRealChain n (r + 1) sk₀ = S.genRealChain n r sk₀ >>= S.genRealStep n := rfl

@[program_certificate]
theorem isPPTOn_genRealStep (S : EncryptionScheme) :
    IsPPTOn (encPair encUnary (encPair encEvalChain encBits))
      (encPair encEvalChain encBits)
      (fun p => S.genRealStep p.1 p.2) := by
  unfold genRealStep
  ppt

/-- Real key-chain generation is uniformly strict PPT in the security parameter, chain length,
and initial secret key. -/
@[program_certificate]
theorem isPPTOn_genRealChain (S : EncryptionScheme) :
    IsPPTOn (encPair (encPair encUnary encUnary) encBits)
      (encPair encEvalChain encBits)
      (fun p => S.genRealChain p.1.1 p.1.2 p.2) := by
  unfold genRealChain
  obtain ⟨k₁, d₁, hlen₁⟩ := S.keyGen_ppt.length_le
  obtain ⟨k₂, d₂, hlen₂⟩ := S.isPPTOn_encryptKey.length_le
  refine IsPPTOn.iterateWith_of_bounded_growth
    (count := fun p : (ℕ × ℕ) × List Bool => p.1.2)
    (initial := fun p : (ℕ × ℕ) × List Bool => ([], p.2))
    (step := fun (p : (ℕ × ℕ) × List Bool) state => S.genRealStep p.1.1 state)
    (by polytime) (by polytime) (by ppt)
    (growth := fun p : (ℕ × ℕ) × List Bool =>
      let B₁ := k₁ * (p.1.1 + 1) ^ d₁
      let B₂ := k₂ * (2 * B₁ + S.skLength p.1.1 + 2) ^ d₂
      4 * (2 * B₁ + B₂ + 1) + B₁ + 4)
    (show ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × List Bool =>
        let B₁ := k₁ * (p.1.1 + 1) ^ d₁
        let B₂ := k₂ * (2 * B₁ + S.skLength p.1.1 + 2) ^ d₂
        4 * (2 * B₁ + B₂ + 1) + B₁ + 4)
      (encPair (encPair encUnary encUnary) encBits) encUnary by polytime).polyBounded ?_
  intro p state next hnext
  simp only [genRealStep, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hnext
  rcases hnext with ⟨keys, hkeys, ek, hek, rfl⟩
  have hkeys_bound := hlen₁ p.1.1 keys hkeys
  simp only [encUnary_apply, List.length_replicate, length_encPair, encBits_apply] at hkeys_bound
  have hpk_le : keys.1.length ≤ k₁ * (p.1.1 + 1) ^ d₁ := by omega
  have hsk_le : keys.2.length ≤ k₁ * (p.1.1 + 1) ^ d₁ := by omega
  have hek_bound := hlen₂ (keys.1, state.2.take (S.skLength p.1.1)) ek hek
  have htake_le : (state.2.take (S.skLength p.1.1)).length ≤ S.skLength p.1.1 :=
    List.length_take_le _ _
  have hpair_le :
      (encPair encBits encBits (keys.1, state.2.take (S.skLength p.1.1))).length + 1 ≤
        2 * (k₁ * (p.1.1 + 1) ^ d₁) + S.skLength p.1.1 + 2 := by
    simp only [length_encPair, encBits_apply]
    omega
  have hek_le :
      (encList encBits ek).length ≤
        k₂ * (2 * (k₁ * (p.1.1 + 1) ^ d₁) + S.skLength p.1.1 + 2) ^ d₂ :=
    hek_bound.trans (Nat.mul_le_mul_left k₂ (Nat.pow_le_pow_left hpair_le d₂))
  simp only [encEvalChain, length_encPair, encBits_apply, encList_append, encList_cons,
    encList_nil, List.length_append, List.length_nil, length_frame]
  omega

@[program_certificate]
theorem isPPTOn_genRealChain_comp (S : EncryptionScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n r : γ → ℕ} {sk₀ : γ → List Bool}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hr : ComputableTidilyInPolyTime r encIn encUnary)
    (hsk₀ : ComputableTidilyInPolyTime sk₀ encIn encBits) :
    IsPPTOn encIn (encPair encEvalChain encBits)
      (fun a => S.genRealChain (n a) (r a) (sk₀ a)) :=
  S.isPPTOn_genRealChain.preprocess ((hn.prod hr).prod hsk₀)

/-- Every supported result of `genRealChain n r keys₀.2` has a final secret key coming from a
supported key pair of `S.keyGen n`. -/
theorem exists_mem_support_keyGen_of_genRealChain (S : EncryptionScheme) {n : ℕ}
    {keys₀ : List Bool × List Bool} (hkeys₀ : keys₀ ∈ (ProbComp.eval (S.keyGen n)).support)
    (r : ℕ) {res : EvalChain × List Bool}
    (hres : res ∈ (ProbComp.eval (S.genRealChain n r keys₀.2)).support) :
    ∃ pk, (pk, res.2) ∈ (ProbComp.eval (S.keyGen n)).support := by
  induction r generalizing res with
  | zero =>
    simp only [genRealChain_zero, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hres
    subst hres
    exact ⟨keys₀.1, hkeys₀⟩
  | succ r ih =>
    simp only [genRealChain_succ, genRealStep, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hres
    rcases hres with ⟨prev, _, keys, hkeys, ek, _, rfl⟩
    exact ⟨keys.1, hkeys⟩

/-- Every supported result of `genRealChain n r keys₀.2` has final secret key length
`skLength n`. -/
theorem length_snd_of_mem_support_genRealChain (S : EncryptionScheme) {n : ℕ}
    {keys₀ : List Bool × List Bool} (hkeys₀ : keys₀ ∈ (ProbComp.eval (S.keyGen n)).support)
    (r : ℕ) {res : EvalChain × List Bool}
    (hres : res ∈ (ProbComp.eval (S.genRealChain n r keys₀.2)).support) :
    res.2.length = S.skLength n := by
  obtain ⟨pk, hpk⟩ := S.exists_mem_support_keyGen_of_genRealChain hkeys₀ r hres
  exact S.length_sk n (pk, res.2) hpk

/-- One dummy evaluation-key level: sample `(pk, sk) ← S.keyGen n` and encrypt the all-zero
bit string `0^{S.skLength n}` under `pk`. -/
noncomputable def genDummyStep (S : EncryptionScheme) (n : ℕ) :
    ProbComp (List Bool × List (List Bool)) := do
  let keys ← S.keyGen n
  let ek ← S.encryptKey keys.1 (List.replicate (S.skLength n) false)
  return (keys.1, ek)

@[program_certificate]
theorem isPPTOn_genDummyStep (S : EncryptionScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    IsPPTOn encIn (encPair encBits (encList encBits)) (fun a => S.genDummyStep (n a)) := by
  unfold genDummyStep
  ppt

/-- Generate `d` independent dummy evaluation-key levels. -/
noncomputable def genDummyChain (S : EncryptionScheme) (n d : ℕ) : ProbComp EvalChain :=
  OracleComp.replicate d (S.genDummyStep n)

@[program_certificate]
theorem isPPTOn_genDummyChain (S : EncryptionScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n d : γ → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hd : ComputableTidilyInPolyTime d encIn encUnary) :
    IsPPTOn encIn encEvalChain (fun a => S.genDummyChain (n a) (d a)) := by
  unfold genDummyChain encEvalChain
  ppt

/-- Leveled FHE key generation for depth bound `L` at security parameter `n`: sample a base key
pair `(pk_0, sk_0)` and an acyclic chain of `L` evaluation keys
`[(pk_1, ek_0), …, (pk_L, ek_{L-1})]`, returning the leveled public key `(pk_0, chain)` and final
decryption key `sk_L`. -/
noncomputable def leveledKeyGen (S : EncryptionScheme) (L n : ℕ) :
    ProbComp (LeveledPK × List Bool) := do
  let keys₀ ← S.keyGen n
  let res ← S.genRealChain n L keys₀.2
  return ((keys₀.1, res.1), res.2)

@[program_certificate]
theorem isPPTOn_leveledKeyGen (S : EncryptionScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {L n : γ → ℕ}
    (hL : ComputableTidilyInPolyTime L encIn encUnary)
    (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    IsPPTOn encIn (encPair encLeveledPK encBits) (fun a => S.leveledKeyGen (L a) (n a)) := by
  unfold leveledKeyGen
  ppt

/-- The leveled encryption experiment at depth bound `L` and challenge bit `b`: generate a leveled
key pair and encrypt `b` under the initial public key `pk_0`. -/
noncomputable def leveledEncryptGame (S : EncryptionScheme) (L : ℕ) (b : Bool) (n : ℕ) :
    ProbComp (LeveledPK × List Bool) := do
  let (lpk, _) ← S.leveledKeyGen L n
  let c ← S.encrypt lpk.1 b
  return (lpk, c)

/-- Semantic security of the leveled FHE scheme with depth bound `D : ℕ → ℕ`: no uniform strict PPT
distinguisher can distinguish encryptions of `false` from encryptions of `true` even given the
entire evaluation key chain of length `D n`. -/
def LeveledSemanticSecure (S : EncryptionScheme) (D : ℕ → ℕ) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.leveledEncryptGame (D n) false n >>= adversary n))
    (fun adversary n => ProbComp.eval (S.leveledEncryptGame (D n) true n >>= adversary n))
    IsLeveledPKPPT

/-- Hybrid distribution `k` (`0 ≤ k ≤ L`) for the leveled key chain: the first `L - k` evaluation
keys encrypt the real secret keys `sk_0, …, sk_{L - k - 1}`, while the last `k` evaluation keys
encrypt the all-zero dummy key `0^{S.skLength n}`. -/
noncomputable def leveledHybrid (S : EncryptionScheme) (L : ℕ) (b : Bool) (n k : ℕ) :
    ProbComp (LeveledPK × List Bool) := do
  let keys₀ ← S.keyGen n
  let res ← S.genRealChain n (L - k) keys₀.2
  let dummy ← S.genDummyChain n k
  let c ← S.encrypt keys₀.1 b
  return ((keys₀.1, res.1 ++ dummy), c)

theorem eval_leveledHybrid_zero (S : EncryptionScheme) (L : ℕ) (b : Bool) (n : ℕ) :
    ProbComp.eval (S.leveledHybrid L b n 0) =
      ProbComp.eval (S.leveledEncryptGame L b n) := by
  simp [leveledHybrid, leveledEncryptGame, leveledKeyGen, genDummyChain, ProbComp.eval_bind]

theorem eval_leveledHybrid_self (S : EncryptionScheme) (L : ℕ) (b : Bool) (n : ℕ) :
    ProbComp.eval (S.leveledHybrid L b n L) =
      ProbComp.eval (do
        let pair ← S.encryptGame b n
        let dummy ← S.genDummyChain n L
        return ((pair.1, dummy), pair.2)) := by
  simp only [leveledHybrid, Nat.sub_self, genRealChain_zero, List.nil_append, encryptGame,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext keys₀
  exact PMF.bind_comm _ _ _

/-- Prefix sampled at outer hybrid level `k < L`: samples `(pk_0, sk_0)` and the first `L - 1 - k`
real evaluation keys `(realChain, sk_r)`. -/
noncomputable def leveledPrefix (S : EncryptionScheme) (L n k : ℕ) :
    ProbComp (List Bool × EvalChain × List Bool) := do
  let keys₀ ← S.keyGen n
  let res ← S.genRealChain n (L - 1 - k) keys₀.2
  return (keys₀.1, res.1, res.2.take (S.skLength n))

@[program_certificate]
theorem isPPTOn_leveledPrefix (S : EncryptionScheme) {γ : Type}
    {encIn : γ ↪ List Bool} {L n k : γ → ℕ}
    (hL : ComputableTidilyInPolyTime L encIn encUnary)
    (hn : ComputableTidilyInPolyTime n encIn encUnary)
    (hk : ComputableTidilyInPolyTime k encIn encUnary) :
    IsPPTOn encIn (encPair encBits (encPair encEvalChain encBits))
      (fun a => S.leveledPrefix (L a) (n a) (k a)) := by
  unfold leveledPrefix
  ppt

/-- Suffix continuation at outer hybrid level `k < L`: given the prefix `(pk_0, realChain, sk_r)`
and the critical level `(pk, ek)`, samples `k` dummy evaluation keys and the challenge ciphertext
`c ← S.encrypt pk_0 b`, and invokes `adversary`. -/
noncomputable def leveledSuffix (S : EncryptionScheme) (adversary : LeveledDistinguisher)
    (b : Bool) (n k : ℕ) (ctx : List Bool × EvalChain × List Bool)
    (pk : List Bool) (ek : List (List Bool)) : ProbComp Bool := do
  let dummy ← S.genDummyChain n k
  let c ← S.encrypt ctx.1 b
  adversary n ((ctx.1, ctx.2.1 ++ (pk, ek) :: dummy), c)

theorem length_word_of_mem_support_leveledPrefix (S : EncryptionScheme) (L n k : ℕ)
    {ctx : List Bool × EvalChain × List Bool}
    (hctx : ctx ∈ (ProbComp.eval (S.leveledPrefix L n k)).support) :
    ctx.2.2.length = S.skLength n := by
  simp only [leveledPrefix, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hctx
  rcases hctx with ⟨keys₀, hkeys₀, res, hres, rfl⟩
  have hlen := S.length_snd_of_mem_support_genRealChain hkeys₀ (L - 1 - k) hres
  simp [hlen]

theorem eval_leveledPrefix_real (S : EncryptionScheme) (L : ℕ) (b : Bool) (n k : ℕ)
    (hk : k < L) (adversary : LeveledDistinguisher) :
    ProbComp.eval (do
      let ctx ← S.leveledPrefix L n k
      let keys ← S.keyGen n
      let ek ← S.encryptKey keys.1 ctx.2.2
      S.leveledSuffix adversary b n k ctx keys.1 ek) =
    ProbComp.eval (S.leveledHybrid L b n k >>= adversary n) := by
  have hsub : L - k = (L - 1 - k) + 1 := by omega
  simp [leveledPrefix, leveledSuffix, leveledHybrid, hsub, genRealChain_succ, genRealStep,
    ProbComp.eval_bind, List.append_assoc]

theorem eval_leveledPrefix_dummy (S : EncryptionScheme) (L : ℕ) (b : Bool) (n k : ℕ)
    (adversary : LeveledDistinguisher) :
    ProbComp.eval (do
      let ctx ← S.leveledPrefix L n k
      let keys ← S.keyGen n
      let ek ← S.encryptKey keys.1 (List.replicate (S.skLength n) false)
      S.leveledSuffix adversary b n k ctx keys.1 ek) =
    ProbComp.eval (S.leveledHybrid L b n (k + 1) >>= adversary n) := by
  have hsub : L - (k + 1) = L - 1 - k := by omega
  simp [leveledPrefix, leveledSuffix, leveledHybrid, hsub, genDummyChain, OracleComp.replicate_succ,
    genDummyStep, ProbComp.eval_bind]

/-- Single-level test at outer hybrid index `k`: runs `encryptKeyTest` on `leveledPrefix` and
`leveledSuffix`. -/
noncomputable def leveledLevelTest (S : EncryptionScheme) (adversary : LeveledDistinguisher)
    (L : ℕ) (b : Bool) (n k : ℕ) (challenge : List Bool × List Bool) : ProbComp Bool :=
  S.encryptKeyTest (S.leveledPrefix L n k)
    (fun ctx => ctx.2.2)
    (S.leveledSuffix adversary b n k)
    (S.skLength n) challenge

theorem leveledLevelTest_gap (S : EncryptionScheme) (adversary : LeveledDistinguisher)
    (L : ℕ) (b : Bool) (n k : ℕ) (hk : k < L) :
    (Game.succProbability (ProbComp.eval (S.leveledHybrid L b n k >>= adversary n)) : ℝ) -
      Game.succProbability (ProbComp.eval (S.leveledHybrid L b n (k + 1) >>= adversary n)) =
    (dyadicSize (S.skLength n) : ℝ) *
      ((Game.succProbability
          (ProbComp.eval (S.encryptGame true n >>=
            S.leveledLevelTest adversary L b n k)) : ℝ) -
        Game.succProbability
          (ProbComp.eval (S.encryptGame false n >>=
            S.leveledLevelTest adversary L b n k))) := by
  unfold leveledLevelTest
  have h := S.encryptKeyTest_gap n (S.leveledPrefix L n k)
    (fun ctx => ctx.2.2)
    (S.leveledSuffix adversary b n k)
    (S.skLength n)
    (fun _ hctx => S.length_word_of_mem_support_leveledPrefix L n k hctx)
  simpa only [S.eval_leveledPrefix_real L b n k hk adversary,
    S.eval_leveledPrefix_dummy L b n k adversary] using h

/-- Uniform two-level hybrid reduction replacing the real key chain of length `D n` with the
all-dummy key chain: samples a level `k ← sampleDyadicIndex (D n)` and runs `leveledLevelTest`. -/
noncomputable def leveledChainReduction (S : EncryptionScheme) (D : ℕ → ℕ) (b : Bool)
    (adversary : LeveledDistinguisher) : PKDistinguisher := fun n challenge => do
  let k ← sampleDyadicIndex (D n)
  if k < D n then S.leveledLevelTest adversary (D n) b n k challenge else pure false

theorem isPKPPT_leveledChainReduction (S : EncryptionScheme) {D : ℕ → ℕ}
    (hD : ComputableTidilyInPolyTime D encUnary encUnary) (b : Bool)
    {adversary : LeveledDistinguisher} (hadversary : IsLeveledPKPPT adversary) :
    IsPKPPT (S.leveledChainReduction D b adversary) := by
  have hlevel :
      IsPPTOn (encPair (encPair encUnary (encPair encBits encBits)) encUnary) encBool
        (fun p => S.leveledLevelTest adversary (D p.1.1) b p.1.1 p.2 p.1.2) := by
    unfold leveledLevelTest leveledSuffix
    exact S.isPPTOn_encryptKeyTest (by ppt) (by polytime) (by ppt) (by polytime) (by polytime)
  unfold leveledChainReduction
  ppt

theorem leveledChainReduction_gap (S : EncryptionScheme) (D : ℕ → ℕ) (b : Bool)
    (adversary : LeveledDistinguisher) (n : ℕ) :
    (Game.succProbability
        (ProbComp.eval (S.leveledEncryptGame (D n) b n >>= adversary n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval (S.leveledHybrid (D n) b n (D n) >>= adversary n)) =
    (dyadicSize (D n) : ℝ) * dyadicSize (S.skLength n) *
      ((Game.succProbability
          (ProbComp.eval (S.encryptGame true n >>=
            S.leveledChainReduction D b adversary n)) : ℝ) -
        Game.succProbability
          (ProbComp.eval (S.encryptGame false n >>=
            S.leveledChainReduction D b adversary n))) := by
  unfold leveledChainReduction
  have h := Game.succProbability_hybrid_reduction
    (fun k => ProbComp.eval (S.leveledHybrid (D n) b n k >>= adversary n))
    (fun k => ProbComp.eval (S.encryptGame true n >>= S.leveledLevelTest adversary (D n) b n k))
    (fun k => ProbComp.eval (S.encryptGame false n >>= S.leveledLevelTest adversary (D n) b n k))
    (D n) (dyadicSize (D n)) (lt_dyadicSize (D n)).le (dyadicSize (S.skLength n))
    (fun k hk => S.leveledLevelTest_gap adversary (D n) b n k hk)
  have hzero :
      ProbComp.eval (S.leveledHybrid (D n) b n 0 >>= adversary n) =
        ProbComp.eval (S.leveledEncryptGame (D n) b n >>= adversary n) := by
    rw [ProbComp.eval_bind, S.eval_leveledHybrid_zero (D n) b n, ← ProbComp.eval_bind]
  simpa only [eval_bind_sampleDyadicIndex_guard, hzero] using h

theorem leveledChainReduction_advantage (S : EncryptionScheme) (D : ℕ → ℕ) (b : Bool)
    (adversary : LeveledDistinguisher) (n : ℕ) :
    Game.advantage
        (ProbComp.eval (S.leveledEncryptGame (D n) b n >>= adversary n))
        (ProbComp.eval (S.leveledHybrid (D n) b n (D n) >>= adversary n)) =
      (dyadicSize (D n) * dyadicSize (S.skLength n) : ℕ) *
        Game.advantage
          (ProbComp.eval (S.encryptGame false n >>= S.leveledChainReduction D b adversary n))
          (ProbComp.eval (S.encryptGame true n >>= S.leveledChainReduction D b adversary n)) := by
  rw [Game.advantage_comm (ProbComp.eval (S.encryptGame false n >>= _))]
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_mul,
    Game.coe_advantage, Game.coe_advantage, S.leveledChainReduction_gap D b adversary n,
    abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]

/-- Reduction from the all-dummy hybrid game (`k = D n`) to single-bit semantic security on
`pk_0`. -/
noncomputable def leveledDummyReduction (S : EncryptionScheme) (D : ℕ → ℕ)
    (adversary : LeveledDistinguisher) : PKDistinguisher := fun n challenge => do
  let dummy ← S.genDummyChain n (D n)
  adversary n ((challenge.1, dummy), challenge.2)

theorem isPKPPT_leveledDummyReduction (S : EncryptionScheme) {D : ℕ → ℕ}
    (hD : ComputableTidilyInPolyTime D encUnary encUnary)
    {adversary : LeveledDistinguisher} (hadversary : IsLeveledPKPPT adversary) :
    IsPKPPT (S.leveledDummyReduction D adversary) := by
  unfold leveledDummyReduction
  ppt

theorem eval_leveledDummyReduction (S : EncryptionScheme) (D : ℕ → ℕ) (b : Bool)
    (adversary : LeveledDistinguisher) (n : ℕ) :
    ProbComp.eval (S.encryptGame b n >>= S.leveledDummyReduction D adversary n) =
      ProbComp.eval (S.leveledHybrid (D n) b n (D n) >>= adversary n) := by
  rw [ProbComp.eval_bind, ProbComp.eval_bind, S.eval_leveledHybrid_self (D n) b n]
  simp [leveledDummyReduction, ProbComp.eval_bind, PMF.bind_bind, Function.comp_def]

/-- **Leveled semantic security from base semantic security**: if `S` is semantically secure and
`D : ℕ → ℕ` is computable tidily in polynomial time in unary, then the leveled scheme with key
chain length `D n` is semantically secure. -/
theorem leveledSemanticSecure_of_semanticSecure (S : EncryptionScheme)
    (hsec : S.SemanticSecure) {D : ℕ → ℕ}
    (hD : ComputableTidilyInPolyTime D encUnary encUnary) :
    S.LeveledSemanticSecure D := by
  have hchain (b : Bool) :
      Game.Indistinguishable
        (fun adversary n => ProbComp.eval (S.leveledEncryptGame (D n) b n >>= adversary n))
        (fun adversary n => ProbComp.eval (S.leveledHybrid (D n) b n (D n) >>= adversary n))
        IsLeveledPKPPT := by
    intro adversary hadversary
    have hred := hsec (S.leveledChainReduction D b adversary)
      (S.isPKPPT_leveledChainReduction hD b hadversary)
    have hloss : PolynomiallyBounded (fun n => dyadicSize (D n) * dyadicSize (S.skLength n)) := by
      have := hD.polynomiallyBounded
      have := S.skLength_polyTime.polynomiallyBounded
      fun_prop
    apply negligible_of_le (hred.polynomiallyBounded_mul hloss)
    intro n
    exact (S.leveledChainReduction_advantage D b adversary n).le
  have hdummy :
      Game.Indistinguishable
        (fun adversary n => ProbComp.eval (S.leveledHybrid (D n) false n (D n) >>= adversary n))
        (fun adversary n => ProbComp.eval (S.leveledHybrid (D n) true n (D n) >>= adversary n))
        IsLeveledPKPPT := by
    intro adversary hadversary
    have hred := hsec (S.leveledDummyReduction D adversary)
      (S.isPKPPT_leveledDummyReduction hD hadversary)
    simpa only [S.eval_leveledDummyReduction D false adversary,
      S.eval_leveledDummyReduction D true adversary] using hred
  exact (hchain false).trans (hdummy.trans (hchain true).symm)

end EncryptionScheme

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

/-! ### Leveled homomorphic evaluation and Gentry's leveled bootstrapping theorem -/

@[simp]
private theorem toNat_castSucc_wire {m k : ℕ} (w : Wire m k) :
    w.castSucc.toNat = w.toNat := by
  cases w <;> rfl

private theorem code_mapWires_castSucc {σ : Signature} {m k : ℕ} (line : Line σ m k) :
    (line.mapWires Wire.Renaming.castSucc).code = line.code := by
  simp [Line.code]

private theorem code_eq_ofFn_lines {σ : Signature} {m g : ℕ} (p : Program σ m g) :
    p.code = List.ofFn (fun j : Fin g => (p.lines j).code) := by
  induction p with
  | empty => simp
  | gate q line ih =>
    rw [Program.code_gate, ih, List.ofFn_succ' (fun j => ((q.gate line).lines j).code)]
    simp [code_mapWires_castSucc, List.concat_eq_append]

/-- One synchronous level step of leveled homomorphic evaluation: given `(m, gates)`, the previous
level's wire ciphertexts `values`, and the current level's evaluation key `(pk, ek)`, refresh the
first `m` input wire ciphertexts using `.and` self-recryption and evaluate each gate in `gates` on
`values` under `(pk, ek)`. -/
def evalLevelStep (par : ℕ × List (Boolean.Op × List ℕ))
    (values : List (List Bool)) (levelKey : List Bool × List (List Bool)) : List (List Bool) :=
  (List.range par.1).map (fun i =>
      S.evalAugDecrypt .and levelKey.1 levelKey.2 (values.getD i []) (values.getD i [])) ++
    par.2.map (fun g =>
      S.evalGateOp g.1 levelKey.1 levelKey.2
        (g.2[0]?.elim [] (values.getD · []))
        (g.2[1]?.elim [] (values.getD · [])))

/-- Leveled homomorphic evaluation of a De Morgan gate list `gates` on initial input ciphertexts
`cs₀` across an evaluation key chain `chain`. -/
def evalLeveledCode (chain : EvalChain) (cs₀ : List (List Bool))
    (gates : List (Boolean.Op × List ℕ)) : List (List Bool) :=
  chain.foldl (S.evalLevelStep (cs₀.length, gates)) cs₀

/-- Read output wire `o` after leveled homomorphic evaluation of `gates` on `cs₀` across `chain`. -/
def evalLeveledOutput (chain : EvalChain) (cs₀ : List (List Bool))
    (gates : List (Boolean.Op × List ℕ)) (o : ℕ) : List Bool :=
  (S.evalLeveledCode chain cs₀ gates).getD o []

@[simp]
theorem evalLeveledCode_nil (cs₀ : List (List Bool)) (gates : List (Boolean.Op × List ℕ)) :
    S.evalLeveledCode [] cs₀ gates = cs₀ := rfl

theorem evalLeveledCode_append_singleton (chain : EvalChain)
    (levelKey : List Bool × List (List Bool)) (cs₀ : List (List Bool))
    (gates : List (Boolean.Op × List ℕ)) :
    S.evalLeveledCode (chain ++ [levelKey]) cs₀ gates =
      S.evalLevelStep (cs₀.length, gates) (S.evalLeveledCode chain cs₀ gates) levelKey := by
  simp [evalLeveledCode, List.foldl_append]

@[simp]
theorem length_evalLevelStep (par : ℕ × List (Boolean.Op × List ℕ))
    (values : List (List Bool)) (levelKey : List Bool × List (List Bool)) :
    (S.evalLevelStep par values levelKey).length = par.1 + par.2.length := by
  simp [evalLevelStep]

theorem length_mem_evalLevelStep_le_pk (par : ℕ × List (Boolean.Op × List ℕ))
    (values : List (List Bool)) (levelKey : List Bool × List (List Bool)) :
    ∀ c ∈ S.evalLevelStep par values levelKey, c.length ≤ S.cipherBound levelKey.1.length := by
  intro c hc
  simp only [evalLevelStep, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨i, _, rfl⟩ | ⟨g, _, rfl⟩
  · exact Bootstrappable.length_evalAugDecrypt_le_pk .and levelKey.1 levelKey.2 _ _
  · exact S.length_evalGateOp_le_pk g.1 levelKey.1 levelKey.2 _ _

theorem length_mem_evalLevelStep_le {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (S.keyGen n)).support)
    (par : ℕ × List (Boolean.Op × List ℕ)) (values : List (List Bool))
    (ek : List (List Bool)) :
    ∀ c ∈ S.evalLevelStep par values (keys.1, ek), c.length ≤ S.cipherBound n := by
  intro c hc
  simp only [evalLevelStep, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨i, _, rfl⟩ | ⟨g, _, rfl⟩
  · exact Bootstrappable.length_evalAugDecrypt_le n keys hkeys ek .and _ _
  · exact S.length_evalGateOp_le hkeys ek g.1 _ _

private theorem length_encList_encBits_le {l : List (List Bool)} {B : ℕ}
    (hl : ∀ c ∈ l, c.length ≤ B) :
    (encList encBits l).length ≤ l.length * (2 * B + 1) := by
  rw [length_encList]
  have hsum := List.sum_le_length_nsmul (l.map fun c => 2 * (encBits c).length + 1) (2 * B + 1)
    (fun x hx => by
      rcases List.mem_map.mp hx with ⟨c, hc, rfl⟩
      have := hl c hc
      simp only [encBits_apply]
      omega)
  simpa using hsum

private theorem length_pk_le_of_mem_chain {levelKey : List Bool × List (List Bool)}
    {chain : EvalChain} (hmem : levelKey ∈ chain) :
    levelKey.1.length ≤ (encEvalChain chain).length := by
  have hsum := sum_length_le_length_encList (encPair encBits (encList encBits)) chain
  have hle : (encPair encBits (encList encBits) levelKey).length ≤
      (chain.map fun a => (encPair encBits (encList encBits) a).length).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hmem)
  have hpk : levelKey.1.length ≤ (encPair encBits (encList encBits) levelKey).length := by
    simp only [length_encPair, encBits_apply]
    omega
  exact hpk.trans (hle.trans hsum)

private theorem computableTidilyInPolyTime_evalLevelStep :
    ComputableTidilyInPolyTime
      (fun p : ((ℕ × List (Boolean.Op × List ℕ)) × List (List Bool)) ×
          (List Bool × List (List Bool)) =>
        S.evalLevelStep p.1.1 p.1.2 p.2)
      (encPair (encPair (encPair encUnary (encList Boolean.encGate)) (encList encBits))
        (encPair encBits (encList encBits)))
      (encList encBits) := by
  unfold evalLevelStep
  have harg (i : ℕ) :
      ComputableTidilyInPolyTime
        (fun q : (((ℕ × List (Boolean.Op × List ℕ)) × List (List Bool)) ×
            (List Bool × List (List Bool))) × (Boolean.Op × List ℕ) =>
          q.2.2[i]?.elim [] (q.1.1.2.getD · []))
        (encPair
          (encPair (encPair (encPair encUnary (encList Boolean.encGate)) (encList encBits))
            (encPair encBits (encList encBits)))
          Boolean.encGate)
        encBits :=
    ComputableTidilyInPolyTime.optionElimWithInput
      (ComputableTidilyInPolyTime.getElem? (ComputableTidilyInPolyTime.snd _ _).snd'
        (ComputableTidilyInPolyTime.const i))
      (ComputableTidilyInPolyTime.const [])
      (ComputableTidilyInPolyTime.listGetD_binary []
        (ComputableTidilyInPolyTime.fst _ _).fst'.fst'.snd'
        (ComputableTidilyInPolyTime.snd _ _))
  have h0 := harg 0
  have h1 := harg 1
  polytime

/-- **Polynomial-time leveled homomorphic evaluation** of a De Morgan gate list `gates` on initial
ciphertexts `cs₀` across an evaluation key chain `chain`. -/
@[program_certificate]
theorem computableTidilyInPolyTime_evalLeveledCode :
    ComputableTidilyInPolyTime
      (fun p : (EvalChain × List (List Bool)) × List (Boolean.Op × List ℕ) =>
        S.evalLeveledCode p.1.1 p.1.2 p.2)
      (encPair (encPair encEvalChain (encList encBits)) (encList Boolean.encGate))
      (encList encBits) := by
  unfold evalLeveledCode encEvalChain
  obtain ⟨c₀, d₀, hcb⟩ := polynomiallyBounded_iff_le.mp S.polynomiallyBounded_cipherBound
  have hpoly : PolyBounded
      (fun p : (EvalChain × List (List Bool)) × List (Boolean.Op × List ℕ) =>
        (encPair (encPair (encList (encPair encBits (encList encBits))) (encList encBits))
          (encList Boolean.encGate) p).length)
      (fun p : (EvalChain × List (List Bool)) × List (Boolean.Op × List ℕ) =>
        (p.1.2.length + p.2.length) *
          (2 * (c₀ * ((encEvalChain p.1.1).length + 1) ^ d₀) + 1)) := by
    refine ⟨fun n => n * (2 * (c₀ * (n + 1) ^ d₀) + 1), by fun_prop, fun p => ?_⟩
    dsimp only
    have h1 : p.1.2.length ≤ (encList encBits p.1.2).length := length_le_length_encList _ _
    have h2 : p.2.length ≤ (encList Boolean.encGate p.2).length := length_le_length_encList _ _
    have hsum : p.1.2.length + p.2.length ≤
        (encPair (encPair (encList (encPair encBits (encList encBits))) (encList encBits))
          (encList Boolean.encGate) p).length := by
      simp only [length_encPair]
      omega
    have hchain : (encEvalChain p.1.1).length + 1 ≤
        (encPair (encPair (encList (encPair encBits (encList encBits))) (encList encBits))
          (encList Boolean.encGate) p).length + 1 := by
      simp only [encEvalChain, length_encPair]
      omega
    have hpow : c₀ * ((encEvalChain p.1.1).length + 1) ^ d₀ ≤
        c₀ * ((encPair (encPair (encList (encPair encBits (encList encBits))) (encList encBits))
          (encList Boolean.encGate) p).length + 1) ^ d₀ :=
      Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left hchain d₀)
    exact Nat.mul_le_mul hsum (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hpow) 1)
  refine ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (par := fun p : (EvalChain × List (List Bool)) × List (Boolean.Op × List ℕ) =>
      (p.1.2.length, p.2))
    (list := fun p => p.1.1)
    (init := fun p => p.1.2)
    (step := S.evalLevelStep)
    (((ComputableTidilyInPolyTime.length encBits).comp
      (ComputableTidilyInPolyTime.fst _ _).snd').prod (ComputableTidilyInPolyTime.snd _ _))
    (ComputableTidilyInPolyTime.fst _ _).fst'
    (ComputableTidilyInPolyTime.fst _ _).snd'
    S.computableTidilyInPolyTime_evalLevelStep
    hpoly ?_
  intro p values levelKey hmem
  have hpk := length_pk_le_of_mem_chain hmem
  have hcb_le : S.cipherBound levelKey.1.length ≤
      c₀ * ((encEvalChain p.1.1).length + 1) ^ d₀ :=
    (hcb levelKey.1.length).trans
      (Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left (Nat.add_le_add_right hpk 1) d₀))
  have hstep_le := length_encList_encBits_le
    (l := S.evalLevelStep (p.1.2.length, p.2) values levelKey)
    (B := c₀ * ((encEvalChain p.1.1).length + 1) ^ d₀)
    (fun c hc => (S.length_mem_evalLevelStep_le_pk _ _ _ c hc).trans hcb_le)
  rw [S.length_evalLevelStep] at hstep_le
  exact hstep_le.trans (Nat.le_add_left _ _)

/-- **Polynomial-time leveled homomorphic output evaluation** of wire `o` after evaluating `gates`
on `cs₀` across `chain`. -/
@[program_certificate]
theorem computableTidilyInPolyTime_evalLeveledOutput :
    ComputableTidilyInPolyTime
      (fun p : ((EvalChain × List (List Bool)) × List (Boolean.Op × List ℕ)) × ℕ =>
        S.evalLeveledOutput p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair
        (encPair (encPair encEvalChain (encList encBits)) (encList Boolean.encGate))
        encNat)
      encBits :=
  ComputableTidilyInPolyTime.listGetD_binary []
    (S.computableTidilyInPolyTime_evalLeveledCode.comp (ComputableTidilyInPolyTime.fst _ _))
    (ComputableTidilyInPolyTime.snd _ _)

/-- Wire-lookup formula for a single level step `evalLevelStep` on a well-formed program `p`. -/
theorem getD_evalLevelStep_program {m g : ℕ} (p : Program Boolean.signature m g)
    (values : List (List Bool)) (levelKey : List Bool × List (List Bool)) (w : Wire m g) :
    (S.evalLevelStep (m, p.code) values levelKey).getD w.toNat [] =
      match w with
      | .input i =>
        S.evalAugDecrypt .and levelKey.1 levelKey.2 (values.getD i.val []) (values.getD i.val [])
      | .gate j =>
        S.homInterpretation levelKey.1 levelKey.2 (p.lines j).op
          (fun a => values.getD ((p.lines j).wires a).toNat []) := by
  have hrange :
      (List.range m).map (fun i =>
        S.evalAugDecrypt .and levelKey.1 levelKey.2 (values.getD i []) (values.getD i [])) =
      List.ofFn (fun i : Fin m =>
        S.evalAugDecrypt .and levelKey.1 levelKey.2
          (values.getD i.val []) (values.getD i.val [])) :=
    List.ext_getElem (by simp) (fun i _ _ => by simp)
  have heq : S.evalLevelStep (m, p.code) values levelKey =
      List.ofFn (fun i : Fin m =>
        S.evalAugDecrypt .and levelKey.1 levelKey.2
          (values.getD i.val []) (values.getD i.val [])) ++
      List.ofFn (fun j : Fin g =>
        S.homInterpretation levelKey.1 levelKey.2 (p.lines j).op
          (fun a => values.getD ((p.lines j).wires a).toNat [])) := by
    unfold evalLevelStep
    rw [hrange, code_eq_ofFn_lines p, List.map_ofFn]
    congr 2
    funext j
    simp only [Function.comp_apply, Line.code]
    rw [← S.homInterpretation_eq_evalGateOp levelKey.1 levelKey.2 (p.lines j).op
      (fun k => (List.ofFn fun a => ((p.lines j).wires a).toNat)[k]?.elim []
        (values.getD · []))]
    simp
  rw [heq, Wire.getD_append_toNat]
  cases w <;> rfl

/-- **Level-by-level wire correctness invariant**: after `L` synchronous level steps along a real
evaluation key chain `res ∈ (S.genRealChain n L keys₀.2).support`, every wire `w : Wire m g` of
depth `p.wireDepths w ≤ L` decrypts under `res.2` to `p.trace Boolean.interpretation x w`. -/
theorem decrypt_evalLeveledCode_wire {n m g : ℕ} {keys₀ : List Bool × List Bool}
    (hkeys₀ : keys₀ ∈ (ProbComp.eval (S.keyGen n)).support)
    (p : Program Boolean.signature m g) (x : Fin m → Bool) (cs₀ : Fin m → List Bool)
    (hcs₀ : ∀ i, cs₀ i ∈ (ProbComp.eval (S.encrypt keys₀.1 (x i))).support) :
    ∀ (L : ℕ) {res : EvalChain × List Bool},
      res ∈ (ProbComp.eval (S.genRealChain n L keys₀.2)).support →
      ∀ (w : Wire m g), p.wireDepths w ≤ L →
        S.decrypt res.2 ((S.evalLeveledCode res.1 (List.ofFn cs₀) p.code).getD w.toNat []) =
          p.trace Boolean.interpretation x w := by
  intro L
  induction L with
  | zero =>
    intro res hres w hw
    simp only [genRealChain_zero, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hres
    subst hres
    cases w with
    | input i =>
      simp only [evalLeveledCode_nil, Wire.toNat_input, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, Fin.is_lt, dite_true, Option.getD_some, Program.trace_input]
      exact S.decrypt_encrypt n keys₀ hkeys₀ (x i) (cs₀ i) (hcs₀ i)
    | gate j =>
      rw [Program.wireDepths_gateWire] at hw
      exact absurd hw (not_le_of_gt (p.depths_pos j))
  | succ r ih =>
    intro res hres w hw
    simp only [genRealChain_succ, genRealStep, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hres
    rcases hres with ⟨prev, hprev, keys, hkeys, ek, hek, rfl⟩
    obtain ⟨pk₁, hkeys₁⟩ := S.exists_mem_support_keyGen_of_genRealChain hkeys₀ r hprev
    have hlen_prev := S.length_snd_of_mem_support_genRealChain hkeys₀ r hprev
    rw [← hlen_prev, List.take_length] at hek
    rw [evalLeveledCode_append_singleton, List.length_ofFn, getD_evalLevelStep_program]
    cases w with
    | input i =>
      rw [Bootstrappable.decrypt_evalAugDecrypt n (pk₁, prev.2) keys hkeys₁ hkeys ek hek,
        evalOp2_and, Bool.and_self]
      have hih := ih hprev (.input i) (by simp)
      simpa using hih
    | gate j =>
      rw [Program.wireDepths_gateWire, p.depths_eq_depth_lines, Line.depth_le_add_one_iff] at hw
      rw [S.decrypt_homInterpretation hkeys₁ hkeys hek]
      have hargs :
          (S.decrypt prev.2 ∘ fun a =>
            (S.evalLeveledCode prev.1 (List.ofFn cs₀) p.code).getD
              ((p.lines j).wires a).toNat []) =
          p.trace Boolean.interpretation x ∘ (p.lines j).wires := by
        funext a
        exact ih hprev ((p.lines j).wires a) (hw a)
      rw [hargs]
      exact p.lines_eval Boolean.interpretation x j

/-- **Correctness of leveled homomorphic evaluation for bounded-depth circuits**:
for any supported leveled key pair `(lpk, skL) ∈ (S.leveledKeyGen L n).support`, any De Morgan
circuit `c : Circuit Boolean.signature m o` of depth `c.depth ≤ L`, and any input ciphertexts
`cs₀` encrypting `x : Fin m → Bool` under `lpk.1`, decrypting the homomorphically evaluated output
wire `j` under `skL` recovers `c.eval Boolean.interpretation x j`. -/
theorem decrypt_evalLeveledOutput_circuit {n L m o : ℕ} {lpk : LeveledPK} {skL : List Bool}
    (hlpk : (lpk, skL) ∈ (ProbComp.eval (S.leveledKeyGen L n)).support)
    (c : Circuit Boolean.signature m o) (hc : c.depth ≤ L)
    (x : Fin m → Bool) (cs₀ : Fin m → List Bool)
    (hcs₀ : ∀ i, cs₀ i ∈ (ProbComp.eval (S.encrypt lpk.1 (x i))).support) (j : Fin o) :
    S.decrypt skL (S.evalLeveledOutput lpk.2 (List.ofFn cs₀) c.code.1 (c.outputs j).toNat) =
      c.eval Boolean.interpretation x j := by
  simp only [leveledKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hlpk
  rcases hlpk with ⟨keys₀, hkeys₀, res, hres, rfl, rfl⟩
  have hw : c.program.wireDepths (c.outputs j) ≤ L :=
    (c.outputDepths_le_depth j).trans hc
  exact S.decrypt_evalLeveledCode_wire hkeys₀ c.program x cs₀ hcs₀ L hres (c.outputs j) hw

/-- **Correctness of leveled homomorphic evaluation for bounded-depth Boolean formulas**:
evaluating the compiled circuit `F.toCircuit` of any De Morgan formula `F` of depth `F.depth ≤ L`
and decrypting under `skL` recovers `F.eval Boolean.interpretation x`. -/
theorem decrypt_evalLeveledOutput_formula {n L m : ℕ} {lpk : LeveledPK} {skL : List Bool}
    (hlpk : (lpk, skL) ∈ (ProbComp.eval (S.leveledKeyGen L n)).support)
    (F : Formula Boolean.signature m) (hF : F.depth ≤ L)
    (x : Fin m → Bool) (cs₀ : Fin m → List Bool)
    (hcs₀ : ∀ i, cs₀ i ∈ (ProbComp.eval (S.encrypt lpk.1 (x i))).support) :
    S.decrypt skL
      (S.evalLeveledOutput lpk.2 (List.ofFn cs₀) F.toCircuit.code.1
        (F.toCircuit.outputs 0).toNat) =
      F.eval Boolean.interpretation x := by
  have hc : F.toCircuit.depth ≤ L := F.depth_toCircuit_le.trans hF
  rw [S.decrypt_evalLeveledOutput_circuit hlpk F.toCircuit hc x cs₀ hcs₀ 0, F.eval_toCircuit]

/-- Every wire ciphertext in `evalLeveledCode` along a supported real key chain has bit-length
at most `S.cipherBound n` whenever the initial input ciphertexts do. -/
theorem length_mem_evalLeveledCode_le {n L : ℕ} {keys₀ : List Bool × List Bool}
    {res : EvalChain × List Bool}
    (hres : res ∈ (ProbComp.eval (S.genRealChain n L keys₀.2)).support)
    (cs₀ : List (List Bool)) (hcs₀ : ∀ c ∈ cs₀, c.length ≤ S.cipherBound n)
    (gates : List (Boolean.Op × List ℕ)) :
    ∀ c ∈ S.evalLeveledCode res.1 cs₀ gates, c.length ≤ S.cipherBound n := by
  cases L with
  | zero =>
    simp only [genRealChain_zero, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hres
    subst hres
    exact hcs₀
  | succ r =>
    simp only [genRealChain_succ, genRealStep, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hres
    rcases hres with ⟨prev, _, keys, hkeys, ek, _, rfl⟩
    rw [evalLeveledCode_append_singleton]
    exact S.length_mem_evalLevelStep_le hkeys (cs₀.length, gates) _ ek

/-- **Compactness of leveled homomorphic evaluation**: the output ciphertext has bit-length at most
`S.cipherBound n`, independent of the circuit size and depth bound `L`. -/
theorem length_evalLeveledOutput_le {n L : ℕ} {lpk : LeveledPK} {skL : List Bool}
    (hlpk : (lpk, skL) ∈ (ProbComp.eval (S.leveledKeyGen L n)).support)
    (cs₀ : List (List Bool)) (hcs₀ : ∀ c ∈ cs₀, c.length ≤ S.cipherBound n)
    (gates : List (Boolean.Op × List ℕ)) (o : ℕ) :
    (S.evalLeveledOutput lpk.2 cs₀ gates o).length ≤ S.cipherBound n := by
  simp only [leveledKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hlpk
  rcases hlpk with ⟨keys₀, _, res, hres, rfl, rfl⟩
  unfold evalLeveledOutput
  rw [List.getD_eq_getElem?_getD]
  rcases h : (S.evalLeveledCode res.1 cs₀ gates)[o]? with _ | c
  · simp
  · exact S.length_mem_evalLeveledCode_le hres cs₀ hcs₀ gates c (List.mem_of_getElem? h)

/-- **Gentry's leveled bootstrapping theorem (`leveledFHE_of_bootstrappable`)**:
for any semantically secure encryption scheme `S` equipped with the assumed `Bootstrappable`
interface and any unary polynomial-time depth bound `D : ℕ → ℕ`, the leveled scheme
(`leveledKeyGen (D n) n`, `encrypt`, `evalLeveledOutput`, `decrypt`) is:
1. **Efficient**: key generation is uniform strict PPT and homomorphic evaluation is computable
   tidily in deterministic polynomial time.
2. **Semantically secure (`LeveledSemanticSecure`)**: encryptions of `false` and `true` remain
   indistinguishable given the entire evaluation key chain of length `D n`, proved from base
   semantic security of `S` alone (without circular security).
3. **Correct for all circuits and formulas of depth at most `D n`**: homomorphically evaluating
   any De Morgan circuit `c` with `c.depth ≤ D n` (or formula `F` with `F.depth ≤ D n`) and
   decrypting under `sk_{D n}` recovers the plaintext output.
4. **Compact**: every output ciphertext has bit-length at most `S.cipherBound n`, which is
   polynomially bounded in `n` and independent of the circuit size and depth bound `D n`
   [Gentry2009]. -/
theorem leveledFHE_of_bootstrappable (hsec : S.SemanticSecure) {D : ℕ → ℕ}
    (hD : ComputableTidilyInPolyTime D encUnary encUnary) :
    IsPPTOn encUnary (encPair encLeveledPK encBits) (fun n => S.leveledKeyGen (D n) n) ∧
    ComputableTidilyInPolyTime
      (fun p : ((EvalChain × List (List Bool)) × List (Boolean.Op × List ℕ)) × ℕ =>
        S.evalLeveledOutput p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair
        (encPair (encPair encEvalChain (encList encBits)) (encList Boolean.encGate))
        encNat)
      encBits ∧
    S.LeveledSemanticSecure D ∧
    PolynomiallyBounded S.cipherBound ∧
    (∀ n lpk skL, (lpk, skL) ∈ (ProbComp.eval (S.leveledKeyGen (D n) n)).support →
      ∀ {m o : ℕ} (c : Circuit Boolean.signature m o), c.depth ≤ D n →
        ∀ (x : Fin m → Bool) (cs₀ : Fin m → List Bool),
          (∀ i, cs₀ i ∈ (ProbComp.eval (S.encrypt lpk.1 (x i))).support) →
          ∀ j : Fin o,
            S.decrypt skL
              (S.evalLeveledOutput lpk.2 (List.ofFn cs₀) c.code.1 (c.outputs j).toNat) =
              c.eval Boolean.interpretation x j ∧
            (S.evalLeveledOutput lpk.2 (List.ofFn cs₀) c.code.1 (c.outputs j).toNat).length ≤
              S.cipherBound n) ∧
    (∀ n lpk skL, (lpk, skL) ∈ (ProbComp.eval (S.leveledKeyGen (D n) n)).support →
      ∀ {m : ℕ} (F : Formula Boolean.signature m), F.depth ≤ D n →
        ∀ (x : Fin m → Bool) (cs₀ : Fin m → List Bool),
          (∀ i, cs₀ i ∈ (ProbComp.eval (S.encrypt lpk.1 (x i))).support) →
          S.decrypt skL
            (S.evalLeveledOutput lpk.2 (List.ofFn cs₀) F.toCircuit.code.1
              (F.toCircuit.outputs 0).toNat) =
            F.eval Boolean.interpretation x ∧
          (S.evalLeveledOutput lpk.2 (List.ofFn cs₀) F.toCircuit.code.1
            (F.toCircuit.outputs 0).toNat).length ≤ S.cipherBound n) := by
  refine ⟨S.isPPTOn_leveledKeyGen hD ComputableTidilyInPolyTime.id',
    S.computableTidilyInPolyTime_evalLeveledOutput,
    S.leveledSemanticSecure_of_semanticSecure hsec hD,
    S.polynomiallyBounded_cipherBound, ?_, ?_⟩
  · intro n lpk skL hlpk m o c hc x cs₀ hcs₀ j
    have hkeys₀ : ∃ sk₀, (lpk.1, sk₀) ∈ (ProbComp.eval (S.keyGen n)).support := by
      simp only [leveledKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
        PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hlpk
      rcases hlpk with ⟨keys₀, hkeys₀, _, _, rfl, _⟩
      exact ⟨keys₀.2, hkeys₀⟩
    obtain ⟨sk₀, hkeys₀⟩ := hkeys₀
    refine ⟨S.decrypt_evalLeveledOutput_circuit hlpk c hc x cs₀ hcs₀ j,
      S.length_evalLeveledOutput_le hlpk (List.ofFn cs₀) ?_ c.code.1 (c.outputs j).toNat⟩
    intro ct hct
    rcases List.mem_ofFn.mp hct with ⟨i, rfl⟩
    exact Bootstrappable.length_encrypt_le n (lpk.1, sk₀) hkeys₀ (x i) (cs₀ i) (hcs₀ i)
  · intro n lpk skL hlpk m F hF x cs₀ hcs₀
    have hkeys₀ : ∃ sk₀, (lpk.1, sk₀) ∈ (ProbComp.eval (S.keyGen n)).support := by
      simp only [leveledKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
        PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hlpk
      rcases hlpk with ⟨keys₀, hkeys₀, _, _, rfl, _⟩
      exact ⟨keys₀.2, hkeys₀⟩
    obtain ⟨sk₀, hkeys₀⟩ := hkeys₀
    refine ⟨S.decrypt_evalLeveledOutput_formula hlpk F hF x cs₀ hcs₀,
      S.length_evalLeveledOutput_le hlpk (List.ofFn cs₀) ?_ F.toCircuit.code.1
        (F.toCircuit.outputs 0).toNat⟩
    intro ct hct
    rcases List.mem_ofFn.mp hct with ⟨i, rfl⟩
    exact Bootstrappable.length_encrypt_le n (lpk.1, sk₀) hkeys₀ (x i) (cs₀ i) (hcs₀ i)

end EncryptionScheme

end Cslib.Crypto
