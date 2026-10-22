/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Depth
public import Complexity.Crypto.Computational.Bootstrapping.KeyEncryption
public import Complexity.Crypto.Computational.Bootstrapping.KeyChain
public import Complexity.Crypto.Computational.Bootstrapping.HomomorphicEval
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
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
assumed as hypotheses) this module and its submodules `KeyEncryption`, `KeyChain`, and
`HomomorphicEval` prove Gentry's bootstrapping *composition*: chaining the assumed gate operations
yields leveled, respectively fixed-key, fully homomorphic encryption.

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

namespace EncryptionScheme

variable (S : EncryptionScheme) [Bootstrappable S]

/-! ### Leveled homomorphic evaluation and Gentry's leveled bootstrapping theorem -/

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
  have hpk : levelKey.1.length ≤ (encEvalChain p.1.1).length := by
    have hle := length_le_encList_of_mem (encPair encBits (encList encBits)) hmem
    have hfst : levelKey.1.length ≤ (encPair encBits (encList encBits) levelKey).length := by
      simp only [length_encPair, encBits_apply]
      omega
    exact hfst.trans hle
  have hcb_le : S.cipherBound levelKey.1.length ≤
      c₀ * ((encEvalChain p.1.1).length + 1) ^ d₀ :=
    (hcb levelKey.1.length).trans
      (Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left (Nat.add_le_add_right hpk 1) d₀))
  have hstep_le := length_encList_le encBits (S.evalLevelStep (p.1.2.length, p.2) values levelKey)
    (b := c₀ * ((encEvalChain p.1.1).length + 1) ^ d₀)
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
    rw [hrange, Program.code_eq_ofFn_lines p, List.map_ofFn]
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
