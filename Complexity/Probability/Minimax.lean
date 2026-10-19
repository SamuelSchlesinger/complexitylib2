/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Sion

/-!
# Averaging and the minimax principle for finite distributions

Think of a two-player game in which one player picks a strategy `a` and the other an input `b`,
with loss `loss a b`; for an algorithm, `loss a b` may be whether `a` errs on `b`. Drawing the
strategy from a distribution `μ` and the input from a distribution `ν` relates the two classical
guarantees of randomized algorithms [Yao1977].

* *The averaging argument*: some outcome of a distribution is at most the mean
  (`exists_mem_support_le_tsum_mul`). So if a strategy drawn from `μ` has expected loss at most
  `ε` on every input, then for every `ν` some single strategy has expected loss at most `ε` on
  inputs drawn from `ν` (`exists_mem_support_tsum_mul_le`; for the probability of failing,
  `exists_mem_support_toOuterMeasure_le`). This is the easy direction of Yao's principle; the
  sample spaces may be infinite.
* *The minimax theorem* [vonNeumann1928]: for finitely many strategies and inputs, the converse
  holds. If against every distribution `ν` on the inputs some strategy has expected loss at most
  `ε`, then some distribution `μ` on the strategies has expected loss at most `ε` on every input
  (`exists_forall_sum_mul_le`). It follows from Sion's minimax theorem
  (`Sion.exists_isSaddlePointOn`) applied to the expected loss on the standard simplices
  [Sion1958]. For the probability of failing, only the inputs need to be finite: strategies
  failing on the same inputs are interchangeable, so `μ` can be taken with finite support
  (`exists_forall_toOuterMeasure_le`). This is the hard direction of Yao's principle.

## Main results

* `Cslib.Probability.PMF.exists_mem_support_le_tsum_mul`: some outcome is at most the mean.
* `Cslib.Probability.PMF.exists_mem_support_tsum_mul_le`,
  `Cslib.Probability.PMF.exists_mem_support_toOuterMeasure_le`: the averaging argument.
* `Cslib.Probability.PMF.exists_forall_sum_mul_le`: the minimax theorem for finite games.
* `Cslib.Probability.PMF.exists_forall_toOuterMeasure_le`: the minimax theorem for failure
  probabilities on finitely many inputs.

## References

* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
* [M. Sion, *On general minimax theorems*][Sion1958]
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal
open Finset

variable {α β : Type*}

/-- **Some possible outcome is at most the mean**: for every distribution `μ` and every function
`g` with values in `[0, ∞]`, some outcome `a` that `μ` can produce has `g a` at most the mean of `g`
under `μ`. The sample space may be infinite. -/
theorem exists_mem_support_le_tsum_mul (μ : PMF α) (g : α → ℝ≥0∞) :
    ∃ a ∈ μ.support, g a ≤ ∑' a, μ a * g a := by
  by_contra! hlt
  obtain ⟨a₀, ha₀⟩ := μ.support_nonempty
  have htop : ∑' a, μ a * g a ≠ ⊤ := ne_top_of_lt (hlt a₀ ha₀)
  have := ENNReal.tsum_lt_tsum (f := fun a => μ a * ∑' a, μ a * g a)
    (g := fun a => μ a * g a) (i := a₀)
    (by rwa [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul])
    (fun a => by
      by_cases ha : a ∈ μ.support
      · gcongr
        exact (hlt a ha).le
      · simp [(PMF.apply_eq_zero_iff μ a).mpr ha])
    (ENNReal.mul_lt_mul_right ((PMF.mem_support_iff μ a₀).mp ha₀) (PMF.apply_ne_top μ a₀)
      (hlt a₀ ha₀))
  rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul] at this
  exact lt_irrefl _ this

/-- **The averaging argument**, the easy direction of Yao's principle. Let `loss a b` be the loss
of a strategy `a` on an input `b`. If drawing the strategy from `μ` has expected loss at most `ε` on
every input that `ν` can produce, then some strategy that `μ` can produce has expected loss at most
`ε` on inputs drawn from `ν`. The sample spaces may be infinite. -/
theorem exists_mem_support_tsum_mul_le (μ : PMF α) (ν : PMF β) (loss : α → β → ℝ≥0∞)
    {ε : ℝ≥0∞} (h : ∀ b ∈ ν.support, ∑' a, μ a * loss a b ≤ ε) :
    ∃ a ∈ μ.support, ∑' b, ν b * loss a b ≤ ε := by
  obtain ⟨a, ha, hle⟩ := exists_mem_support_le_tsum_mul μ fun a => ∑' b, ν b * loss a b
  refine ⟨a, ha, hle.trans ?_⟩
  calc ∑' a, μ a * ∑' b, ν b * loss a b
      = ∑' b, ν b * ∑' a, μ a * loss a b := by
        simp only [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun b => tsum_congr fun a => by ring
    _ ≤ ∑' b, ν b * ε := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        by_cases hb : b ∈ ν.support
        · gcongr
          exact h b hb
        · simp [(PMF.apply_eq_zero_iff ν b).mpr hb]
    _ = ε := by rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]

/-- **The averaging argument** for events, the easy direction of Yao's principle: if a strategy
drawn from `μ` fails on every input that `ν` can produce with probability at most `ε`, then some
strategy that `μ` can produce fails on an input drawn from `ν` with probability at most `ε`. The
sample spaces may be infinite. -/
private theorem toOuterMeasure_eq_tsum_mul_ite {γ : Type*} (π : PMF γ) (s : Set γ)
    [DecidablePred (· ∈ s)] : π.toOuterMeasure s = ∑' c, π c * if c ∈ s then 1 else 0 := by
  rw [PMF.toOuterMeasure_apply]
  exact tsum_congr fun c => by by_cases hc : c ∈ s <;> simp [hc]

theorem exists_mem_support_toOuterMeasure_le (μ : PMF α) (ν : PMF β) (E : α → β → Prop)
    {ε : ℝ} (h : ∀ b ∈ ν.support, (μ.toOuterMeasure {a | E a b}).toReal ≤ ε) :
    ∃ a ∈ μ.support, (ν.toOuterMeasure {b | E a b}).toReal ≤ ε := by
  classical
  obtain ⟨b₀, hb₀⟩ := ν.support_nonempty
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg.trans (h b₀ hb₀)
  obtain ⟨a, ha, hle⟩ := exists_mem_support_tsum_mul_le μ ν
    (fun a b => if E a b then 1 else 0) (ε := ENNReal.ofReal ε) fun b hb => by
      have := h b hb
      rw [← ENNReal.ofReal_le_ofReal_iff hε, ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top μ _),
        toOuterMeasure_eq_tsum_mul_ite] at this
      simpa only [Set.mem_ofPred_eq] using this
  refine ⟨a, ha, ENNReal.toReal_le_of_le_ofReal hε ?_⟩
  rw [toOuterMeasure_eq_tsum_mul_ite]
  simpa only [Set.mem_ofPred_eq] using hle

/-! ### The minimax theorem for finite games -/

section Minimax

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The probability vectors on a finite type: the standard simplex in `I → ℝ`. -/
private def simplex (I : Type*) [Fintype I] : Set (I → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

private theorem convex_simplex : Convex ℝ (simplex I) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hf.1 x)) (mul_nonneg hb (hg.1 x))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hf.2, hg.2,
      mul_one, hab]

private theorem isCompact_simplex : IsCompact (simplex I) := by
  have hclosed : IsClosed (simplex I) := by
    have : simplex I = (⋂ i, {w : I → ℝ | 0 ≤ w i}) ∩ {w | ∑ i, w i = 1} := by
      ext w
      simp [simplex]
    rw [this]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  refine (isCompact_Icc (a := (0 : I → ℝ)) (b := 1)).of_isClosed_subset hclosed
    fun w hw => ⟨fun i => hw.1 i, fun i => ?_⟩
  rw [Pi.one_apply, ← hw.2]
  exact single_le_sum (fun j _ => hw.1 j) (mem_univ i)

private theorem single_mem_simplex [DecidableEq I] (i : I) : Pi.single i 1 ∈ simplex I :=
  ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩

/-- The probability vector of a distribution. -/
private theorem toReal_mem_simplex (π : PMF I) : (fun i => (π i).toReal) ∈ simplex I :=
  ⟨fun _ => ENNReal.toReal_nonneg, sum_toReal π⟩

/-- The distribution of a probability vector. -/
private noncomputable def ofSimplex (w : I → ℝ) (hw : w ∈ simplex I) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw.1 i, hw.2, ENNReal.ofReal_one])

private theorem toReal_ofSimplex (w : I → ℝ) (hw : w ∈ simplex I) (i : I) :
    (ofSimplex w hw i).toReal = w i :=
  ENNReal.toReal_ofReal (hw.1 i)

/-- The expected loss `∑ i j, x i y j M i j` is linear in `x` for fixed `y`. -/
private noncomputable def payoffLeft (M : I → J → ℝ) (y : J → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, ∑ j, x i * y j * M i j
  map_add' x x' := by simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc, RingHom.id_apply]

/-- The expected loss `∑ i j, x i y j M i j` is linear in `y` for fixed `x`. -/
private noncomputable def payoffRight (M : I → J → ℝ) (x : I → ℝ) : (J → ℝ) →ₗ[ℝ] ℝ where
  toFun y := ∑ i, ∑ j, x i * y j * M i j
  map_add' y y' := by simp only [Pi.add_apply, mul_add, add_mul, sum_add_distrib]
  map_smul' c y := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_sum, RingHom.id_apply]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- **The minimax theorem for finite games** [von Neumann]. Let `M i j` be the loss of a strategy
`i` on an input `j`. If against every distribution `ν` on the inputs some strategy has expected
loss at most `ε`, then some distribution `μ` on the strategies has expected loss at most `ε` on
every input. This is the hard direction of Yao's principle; it follows from Sion's theorem
(`Sion.exists_isSaddlePointOn`). -/
theorem exists_forall_sum_mul_le [Nonempty I] (M : I → J → ℝ) {ε : ℝ}
    (h : ∀ ν : PMF J, ∃ i, ∑ j, (ν j).toReal * M i j ≤ ε) :
    ∃ μ : PMF I, ∀ j, ∑ i, (μ i).toReal * M i j ≤ ε := by
  classical
  cases isEmpty_or_nonempty J with
  | inl _ => exact ⟨PMF.pure (Classical.arbitrary I), fun j => isEmptyElim j⟩
  | inr _ =>
  set f : (I → ℝ) → (J → ℝ) → ℝ := fun x y => ∑ i, ∑ j, x i * y j * M i j with hf
  have hcont : Continuous fun p : (I → ℝ) × (J → ℝ) => f p.1 p.2 := by
    simp only [hf]
    fun_prop
  obtain ⟨a, ha, b, hb, hab⟩ := Sion.exists_isSaddlePointOn (f := f)
    ⟨_, single_mem_simplex (Classical.arbitrary I)⟩ convex_simplex isCompact_simplex
    (fun y _ =>
      (hcont.comp (Continuous.prodMk_left y)).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun y _ => ((payoffLeft M y).convexOn convex_simplex).quasiconvexOn)
    convex_simplex ⟨_, single_mem_simplex (Classical.arbitrary J)⟩ isCompact_simplex
    (fun x _ =>
      (hcont.comp (Continuous.prodMk_right x)).upperSemicontinuous.upperSemicontinuousOn _)
    (fun x _ => ((payoffRight M x).concaveOn convex_simplex).quasiconcaveOn)
  obtain ⟨i, hi⟩ := h (ofSimplex b hb)
  refine ⟨ofSimplex a ha, fun j => ?_⟩
  have hle := hab _ (single_mem_simplex i) _ (single_mem_simplex j)
  simp only [hf, Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    sum_ite_eq', mem_univ, ite_true] at hle
  rw [sum_comm] at hle
  simp only [sum_ite_eq', mem_univ, ite_true] at hle
  simp only [toReal_ofSimplex] at hi ⊢
  exact hle.trans hi

/-- The probability of an event in a finite space as a sum. -/
private theorem toReal_toOuterMeasure_eq_sum {γ : Type*} [Fintype γ] (π : PMF γ) (s : Set γ)
    [DecidablePred (· ∈ s)] :
    (π.toOuterMeasure s).toReal = ∑ c, (π c).toReal * if c ∈ s then 1 else 0 := by
  rw [toOuterMeasure_apply_toReal]
  exact sum_congr rfl fun c _ => by by_cases hc : c ∈ s <;> simp [hc]

/-- **Yao's minimax principle** for finite sets of inputs. Let `E i j` say that a strategy `i`
fails on an input `j`, where there may be infinitely many strategies but only finitely many inputs.
If against every distribution `ν` on the inputs some strategy fails with probability at most `ε`,
then some distribution `μ` on finitely many strategies fails with probability at most `ε` on every
input. -/
theorem exists_forall_toOuterMeasure_le {I J : Type*} [Finite J] [Nonempty I] (E : I → J → Prop)
    {ε : ℝ} (h : ∀ ν : PMF J, ∃ i, (ν.toOuterMeasure {j | E i j}).toReal ≤ ε) :
    ∃ μ : PMF I, μ.support.Finite ∧ ∀ j, (μ.toOuterMeasure {i | E i j}).toReal ≤ ε := by
  classical
  have := Fintype.ofFinite J
  -- Strategies with the same failures are interchangeable: play on the finitely many sets of
  -- failures, each represented by one strategy.
  let r : I → Set J := fun i => {j | E i j}
  have := Fintype.ofFinite (Set.range r)
  have : Nonempty (Set.range r) := ⟨⟨r (Classical.arbitrary I), _, rfl⟩⟩
  let rep : Set.range r → I := fun s => s.2.choose
  have hrep (s : Set.range r) (j : J) : E (rep s) j ↔ j ∈ s.1 := by
    rw [← s.2.choose_spec]
    rfl
  obtain ⟨μ, hμ⟩ := exists_forall_sum_mul_le (fun (s : Set.range r) j => if j ∈ s.1 then 1 else 0)
    (ε := ε) fun ν => by
      obtain ⟨i, hi⟩ := h ν
      refine ⟨⟨r i, i, rfl⟩, ?_⟩
      rwa [toReal_toOuterMeasure_eq_sum] at hi
  refine ⟨μ.map rep, by rw [PMF.support_map]; exact (Set.toFinite _).image _, fun j => ?_⟩
  rw [PMF.toOuterMeasure_map_apply, toReal_toOuterMeasure_eq_sum]
  refine le_of_eq_of_le (sum_congr rfl fun s _ => ?_) (hμ j)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hrep]

end Minimax

end Cslib.Probability.PMF
