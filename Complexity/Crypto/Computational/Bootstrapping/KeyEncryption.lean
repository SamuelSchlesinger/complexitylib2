/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Repeat
public import Complexity.Computability.Probabilistic.UniformNat
public import Complexity.Crypto.Computational.Basic
public import Complexity.Crypto.Game.Hybrid
public import Complexity.Languages.Probabilistic.Iteration
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# Public-key bit encryption and bit-by-bit key encryption

This module defines uniform public-key bit encryption schemes (`Cslib.Crypto.EncryptionScheme`),
their single-bit semantic security (`Cslib.Crypto.EncryptionScheme.SemanticSecure`), and
bit-by-bit encryption of secret-key words (`Cslib.Crypto.EncryptionScheme.encryptKey`), together
with the uniform single-challenge hybrid reduction (`encryptKeyTest_gap`,
`isPPTOn_encryptKeyTest`) replacing an encrypted secret key with an encryption of `0^m`
[Gentry2009].

## Main definitions

* `Cslib.Crypto.PKDistinguisher`, `Cslib.Crypto.IsPKPPT`: uniform strict PPT distinguishers for
  public-key bit encryption.
* `Cslib.Crypto.EncryptionScheme`: uniform public-key bit encryption scheme with tidy efficiency
  and correctness on the support of `keyGen`.
* `Cslib.Crypto.EncryptionScheme.SemanticSecure`: semantic security against uniform strict PPT
  distinguishers (`IsPKPPT`).
* `Cslib.Crypto.EncryptionScheme.encryptKey`: bit-by-bit encryption of a secret key word.
* `Cslib.Crypto.EncryptionScheme.encryptKeyTest`: single-challenge hybrid test for replacing an
  encrypted secret key with an encryption of `0^m`.

## Main results

* `Cslib.Crypto.EncryptionScheme.isPPTOn_encryptKey`: uniform strict PPT certificate for
  bit-by-bit key encryption.
* `Cslib.Crypto.EncryptionScheme.encryptKeyTest_gap`: exact signed hybrid gap for replacing an
  encrypted secret key with an encryption of `0^m`.
* `Cslib.Crypto.EncryptionScheme.isPPTOn_encryptKeyTest`: uniform strict PPT certificate for
  `encryptKeyTest`.

## References

* [C. Gentry, *Fully Homomorphic Encryption Using Ideal Lattices*][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
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

end EncryptionScheme

end Cslib.Crypto
