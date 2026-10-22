/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Bootstrapping.KeyEncryption
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# Acyclic key-chain generation and leveled semantic security

This module defines acyclic evaluation key chains (`Cslib.Crypto.EncryptionScheme.EvalChain`),
leveled public keys (`Cslib.Crypto.EncryptionScheme.LeveledPK`), and leveled key generation
(`Cslib.Crypto.EncryptionScheme.leveledKeyGen`), and proves that any semantically secure
public-key bit encryption scheme `S` and any unary polynomial-time depth bound `D : ℕ → ℕ` yield a
semantically secure leveled key chain of length `D n`
(`Cslib.Crypto.EncryptionScheme.leveledSemanticSecure_of_semanticSecure`) via a uniform two-level
hybrid reduction [Gentry2009].

## Main definitions

* `Cslib.Crypto.EncryptionScheme.EvalChain`, `Cslib.Crypto.EncryptionScheme.LeveledPK`:
  acyclic evaluation key chains and leveled public keys.
* `Cslib.Crypto.EncryptionScheme.genRealChain`, `Cslib.Crypto.EncryptionScheme.genDummyChain`:
  real and all-zero dummy evaluation key-chain generators.
* `Cslib.Crypto.EncryptionScheme.leveledKeyGen`,
  `Cslib.Crypto.EncryptionScheme.leveledEncryptGame`: leveled key-chain generation and the
  leveled IND-CPA game.
* `Cslib.Crypto.EncryptionScheme.LeveledSemanticSecure`: semantic security in the presence of an
  evaluation key chain of length `D n`.

## Main results

* `Cslib.Crypto.EncryptionScheme.isPPTOn_genRealChain`,
  `Cslib.Crypto.EncryptionScheme.isPPTOn_leveledKeyGen`: uniform strict PPT certificates for real
  key-chain and leveled key generation.
* `Cslib.Crypto.EncryptionScheme.leveledChainReduction_advantage`: hybrid advantage bound for
  replacing the real key chain with the all-dummy key chain.
* `Cslib.Crypto.EncryptionScheme.leveledSemanticSecure_of_semanticSecure`: semantic security of the
  acyclic key chain of length `D n` from base semantic security alone.

## References

* [C. Gentry, *Fully Homomorphic Encryption Using Ideal Lattices*][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

namespace EncryptionScheme

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

end Cslib.Crypto
