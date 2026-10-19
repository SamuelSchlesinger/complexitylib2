/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Randomized
public import Complexity.Probability.IID
import Complexity.Probability.PMF

/-!
# Amplification of public-coin protocols

A public-coin protocol computing a Boolean function `f` with error `ε ≤ 1 / 2` can be run `2 r`
times with independent coins, answering with the majority of the outputs
[Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997]. The majority is wrong only if at least
`r` of the runs err, which happens with probability at most `(4 ε (1 - ε)) ^ r` by the majority
tail bound `Probability.PMF.toOuterMeasure_iid_le_card_filter_toReal_le`, applied to the
indicators of the runs that err. The repeated protocol sends at most `2 r` times as many bits
(`PublicCoin.ecomplexity_le_two_mul_mul`, `PublicCoin.ecomplexityFun_le_two_mul_mul`). For error
`1 / 3`, `2 r` runs reduce the error to `(8 / 9) ^ r`
(`PublicCoin.ecomplexityFun_le_two_mul_mul_one_third`).

The runs are sequenced by substituting a protocol for each leaf (`Protocol.bind`), and a tuple of
protocols is run one after another before combining the outputs (`Protocol.runAll`). The
protocols are drawn independently with `Probability.PMF.iid`, which unlike the product
`Probability.PMF.pi` applies to the infinite type of protocols.

## Main definitions

* `Cslib.Communication.Protocol.bind`: run a protocol, then a protocol depending on its output.
* `Cslib.Communication.Protocol.runAll`: run a tuple of protocols one after another.
* `Cslib.Communication.PublicCoin.amplify`: the majority of `2 r` independent runs.

## Main results

* `Cslib.Communication.PublicCoin.Solves.amplify`: the error of the majority of `2 r` runs.
* `Cslib.Communication.PublicCoin.ecomplexity_le_two_mul_mul`,
  `Cslib.Communication.PublicCoin.ecomplexityFun_le_two_mul_mul`: amplification of public-coin
  protocols for Boolean functions.
* `Cslib.Communication.PublicCoin.ecomplexityFun_le_two_mul_mul_one_third`: amplification from
  error `1 / 3`.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Probability

variable {X Y Z W : Type*}

namespace Protocol

/-- Run `p`, then the protocol `q z` for the output `z` of `p`: each leaf of `p` labelled `z` is
replaced by `q z`. -/
def bind : Protocol X Y Z → (Z → Protocol X Y W) → Protocol X Y W
  | output z, q => q z
  | alice send p₀ p₁, q => alice send (p₀.bind q) (p₁.bind q)
  | bob send p₀ p₁, q => bob send (p₀.bind q) (p₁.bind q)

@[simp] theorem run_bind (p : Protocol X Y Z) (q : Z → Protocol X Y W) (x : X) (y : Y) :
    (p.bind q).run x y = (q (p.run x y)).run x y := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ => cases h : send x <;> simp [bind, h, ih₀, ih₁]
  | bob send p₀ p₁ ih₀ ih₁ => cases h : send y <;> simp [bind, h, ih₀, ih₁]

theorem depth_bind_le {p : Protocol X Y Z} {q : Z → Protocol X Y W} {d : ℕ}
    (hq : ∀ z, (q z).depth ≤ d) : (p.bind q).depth ≤ p.depth + d := by
  induction p with
  | output z => simpa [bind] using hq z
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ =>
    simp only [bind, depth_alice, depth_bob]
    omega

/-- Run the protocols `ps 0`, …, `ps (k - 1)` one after another and output `g` of their
outputs. -/
def runAll : {k : ℕ} → (Fin k → Protocol X Y Z) → ((Fin k → Z) → W) → Protocol X Y W
  | 0, _, g => output (g Fin.elim0)
  | _ + 1, ps, g => (ps 0).bind fun z => runAll (Fin.tail ps) fun v => g (Fin.cons z v)

@[simp] theorem run_runAll {k : ℕ} (ps : Fin k → Protocol X Y Z) (g : (Fin k → Z) → W) (x : X)
    (y : Y) : (runAll ps g).run x y = g fun i => (ps i).run x y := by
  induction k generalizing W with
  | zero =>
    simp only [runAll, run_output]
    congr 1
    funext i
    exact i.elim0
  | succ k ih =>
    rw [runAll, run_bind, ih]
    congr 1
    funext i
    induction i using Fin.cases <;> rfl

theorem depth_runAll_le {k : ℕ} {ps : Fin k → Protocol X Y Z} {g : (Fin k → Z) → W} {d : ℕ}
    (hps : ∀ i, (ps i).depth ≤ d) : (runAll ps g).depth ≤ k * d := by
  induction k generalizing W with
  | zero => simp [runAll]
  | succ k ih =>
    rw [runAll]
    refine (depth_bind_le fun z => ih (fun i => hps i.succ)).trans ?_
    have := hps 0
    rw [Nat.succ_mul]
    omega

end Protocol

namespace PublicCoin

/-- The majority of `k` bits: `true` when more than half of them are `true`. -/
def majority {k : ℕ} (v : Fin k → Bool) : Bool :=
  decide (k < 2 * (Finset.univ.filter fun i => v i = true).card)

/-- If the majority of `2 r` bits is not `b`, then at least `r` of them are not `b`. -/
theorem le_card_filter_ne_of_majority_ne {r : ℕ} {v : Fin (2 * r) → Bool} {b : Bool}
    (h : majority v ≠ b) : r ≤ (Finset.univ.filter fun i => v i ≠ b).card := by
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun i => v i = true
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  simp only [Bool.not_eq_true] at hcard
  cases b
  · simp only [majority, ne_eq, decide_eq_false_iff_not, not_lt, Bool.not_eq_false] at h ⊢
    omega
  · simp only [majority, ne_eq, decide_eq_true_eq, not_lt, Bool.not_eq_true] at h ⊢
    omega

/-- The majority of `2 r` independent runs of `μ`. -/
noncomputable def amplify (μ : PublicCoin X Y Bool) (r : ℕ) : PublicCoin X Y Bool :=
  (PMF.iid μ (2 * r)).map fun ps => Protocol.runAll ps majority

variable {μ : PublicCoin X Y Bool} {f : X → Y → Bool} {A : Set X} {B : Set Y} {ε : ℝ}

/-- The majority of `2 r` runs sends at most `2 r` times as many bits. -/
theorem depth_amplify_le {c : ℕ} (hμ : μ.depth ≤ c) (r : ℕ) : (μ.amplify r).depth ≤ 2 * r * c := by
  refine depth_le_iff.mpr fun p hp => ?_
  obtain ⟨ps, hps, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  have hd : ∀ i, (ps i).depth ≤ c := fun i => by
    exact_mod_cast (depth_le_depth (PMF.mem_support_iid hps i)).trans hμ
  exact_mod_cast Protocol.depth_runAll_le hd

/-- **Amplification**: if `μ` computes `f` on `A × B` with error `ε ≤ 1 / 2`, then the majority of
`2 r` independent runs computes it with error `(4 ε (1 - ε)) ^ r`. -/
theorem Solves.amplify (hμ : μ.Solves ε (fun x y b => f x y = b) A B) (hε : ε ≤ 1 / 2)
    (r : ℕ) : (μ.amplify r).Solves ((4 * ε * (1 - ε)) ^ r) (fun x y b => f x y = b) A B := by
  intro x hx y hy
  set e : Protocol X Y Bool → Bool := fun p => decide (p.run x y ≠ f x y)
  have he : ((μ.map e) true).toReal ≤ ε := by
    have h := hμ x hx y hy
    rw [errorProb] at h
    rwa [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      show e ⁻¹' {true} = {p | ¬f x y = p.run x y} by
        ext p
        simp only [e, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
          Set.mem_ofPred_eq]
        exact ne_comm]
  refine le_trans ?_ (PMF.toOuterMeasure_iid_le_card_filter_toReal_le he hε r)
  rw [errorProb, PublicCoin.amplify, PMF.toOuterMeasure_map_apply, ← PMF.iid_map,
    PMF.toOuterMeasure_map_apply]
  refine ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
    (PMF.toOuterMeasure_mono _ fun ps hps => ?_)
  replace hps := hps.1
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Protocol.run_runAll] at hps ⊢
  simpa [e] using le_card_filter_ne_of_majority_ne (Ne.symm hps)

/-- **Amplification** of public-coin protocols: for error `ε ≤ 1 / 2`, computing a Boolean function
on `A × B` with error `(4 ε (1 - ε)) ^ r` costs at most `2 r` times as much as with error `ε`. -/
theorem ecomplexity_le_two_mul_mul (hε : ε ≤ 1 / 2) (r : ℕ) :
    ecomplexity ((4 * ε * (1 - ε)) ^ r) (fun x y b => f x y = b) A B ≤
      2 * r * ecomplexity ε (fun x y b => f x y = b) A B := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- With no runs, the error `1` is achieved by any deterministic answer.
    rw [pow_zero, Nat.cast_zero, mul_zero, zero_mul]
    exact (ecomplexity_le_depth (μ := PMF.pure (.output true))
      fun x _ y _ => errorProb_le_one).trans (by simp)
  cases h : ecomplexity ε (fun x y b => f x y = b) A B using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by exact_mod_cast (Nat.mul_pos two_pos hr).ne')]
    exact le_top
  | coe c =>
    obtain ⟨μ, hμ, hc⟩ := ecomplexity_le_iff.mp h.le
    exact (ecomplexity_le_depth (hμ.amplify hε r)).trans
      (depth_amplify_le hc r)

/-- **Amplification** of public-coin protocols for Boolean functions: for error `ε ≤ 1 / 2`,
computing `f` with error `(4 ε (1 - ε)) ^ r` costs at most `2 r` times as much as with error
`ε`. -/
theorem ecomplexityFun_le_two_mul_mul (hε : ε ≤ 1 / 2) (r : ℕ) :
    ecomplexityFun ((4 * ε * (1 - ε)) ^ r) f ≤ 2 * r * ecomplexityFun ε f :=
  ecomplexity_le_two_mul_mul hε r

/-- **Amplification** from error `1 / 3`: `2 r` runs reduce the error to `(8 / 9) ^ r`. -/
theorem ecomplexityFun_le_two_mul_mul_one_third (r : ℕ) :
    ecomplexityFun ((8 / 9) ^ r) f ≤ 2 * r * ecomplexityFun (1 / 3) f := by
  have h := ecomplexityFun_le_two_mul_mul (f := f) (ε := 1 / 3) (by norm_num) r
  rwa [show (4 * (1 / 3) * (1 - 1 / 3) : ℝ) = 8 / 9 by norm_num] at h

end PublicCoin

end Cslib.Communication
