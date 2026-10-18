/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.MatrixEval.Defs
public import Complexity.Computability.Circuit.Rational.Eval

/-!
# Correctness of finite matrix tests

The executable matrix evaluation `Formula.evalMatrix?` returns exactly the values of the relational
semantics. The domain test uses the extension `f + 1`, two nodes larger: at a defined point,
either `f` or `f + 1` is nonzero. A hitting list for both therefore contains a point in the
domain of `f`, even if `f` is identically zero.

## Main results

* `Cslib.Circuits.Rational.Internal.evalMatrix_sound`,
  `Cslib.Circuits.Rational.Internal.evalMatrix_complete`: the executable evaluation is correct.
* `Cslib.Circuits.Rational.Internal.hits_admissible_iff`,
  `Cslib.Circuits.Rational.Internal.hits_nonzero_iff`: hitting lists detect the domain and the
  support of formulas.

## References

* From the complexitylib port [Schlesinger2026RationalHitting] at revision
  add0aca8ee0d71e68969f2cb45cf91554a50f787 (file
  Complexitylib/RationalHitting/Internal/Detection.lean), built on OpenAI's formalization
  [OpenAI2026RationalHitting] at revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

public section

namespace Cslib.Circuits.Rational.Internal

open Rational.Formula Rational.Output

theorem matrix_inverse_left {d : ℕ} (a : Mat d) (ha : a.det ≠ 0) :
    a * (a.det⁻¹ • a.adjugate) = 1 := by
  rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem matrix_inverse_right {d : ℕ} (a : Mat d) (ha : a.det ≠ 0) :
    (a.det⁻¹ • a.adjugate) * a = 1 := by
  rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem evalMatrix_sound {n d : ℕ} (f : Formula n) (X : Tuple n d)
    {v : Mat d} (h : f.evalMatrix? X = some v) : Evaluates f X v := by
  induction f using inductionOn generalizing v with
  | var i =>
    obtain rfl : X i = v := Option.some.inj h
    exact .var i
  | const q =>
    obtain rfl : algebraMap ℚ (Mat d) q = v := Option.some.inj h
    exact .const q
  | add f g ihf ihg =>
    obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a, f.evalMatrix? X = some a ∧
        ∃ b, g.evalMatrix? X = some b ∧ a + b = v := by
      simpa only [evalMatrix?_add, Option.bind_eq_some_iff, Option.some.injEq] using h
    exact Eval.add (ihf ha) (ihg hb)
  | mul f g ihf ihg =>
    obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a, f.evalMatrix? X = some a ∧
        ∃ b, g.evalMatrix? X = some b ∧ a * b = v := by
      simpa only [evalMatrix?_mul, Option.bind_eq_some_iff, Option.some.injEq] using h
    exact Eval.mul (ihf ha) (ihg hb)
  | inv f ih =>
    rw [evalMatrix?_inv, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, hb⟩ := h
    by_cases hd : a.det = 0
    · simp [hd] at hb
    · have hv : a.det⁻¹ • a.adjugate = v := by simpa [hd] using hb
      exact hv ▸ Eval.inv (ih ha) (matrix_inverse_left a hd) (matrix_inverse_right a hd)

theorem evalMatrix_complete {n d : ℕ} {f : Formula n} {X : Tuple n d}
    {v : Mat d} (h : Evaluates f X v) : f.evalMatrix? X = some v := by
  induction f using inductionOn generalizing v with
  | var i => rw [eval_var_iff.mp h]; rfl
  | const q => rw [eval_const_iff.mp h]; rfl
  | add f g ihf ihg =>
    obtain ⟨a, b, ha, hb, rfl⟩ := eval_add_iff.mp h
    simp [ihf ha, ihg hb]
  | mul f g ihf ihg =>
    obtain ⟨a, b, ha, hb, rfl⟩ := eval_mul_iff.mp h
    simp [ihf ha, ihg hb]
  | inv f ih =>
    obtain ⟨a, ha, hab, hba⟩ := eval_inv_iff.mp h
    have hd : a.det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det a).mp ⟨⟨a, v, hab, hba⟩, rfl⟩).ne_zero
    have hi : Evaluates (.inv f) X (a.det⁻¹ • a.adjugate) :=
      Eval.inv ha (matrix_inverse_left a hd) (matrix_inverse_right a hd)
    have he := Eval.unique hi h
    simp [ih ha, hd, he]

theorem nonzero_admissible {n : ℕ} {f : Formula n} (hf : Nonzero f) : Admissible f := by
  obtain ⟨d, hd, X, v, he, _⟩ := hf
  exact ⟨d, hd, X, v, he⟩

theorem hits_nonzero_iff {n s : ℕ} {H : Output n} (hH : Hits s H)
    (f : Formula n) (hf : f.nodeCount ≤ s) :
    Nonzero f ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v := by
  have : NeZero H.dimension := ⟨H.dimension_pos.ne'⟩
  constructor
  · intro h
    exact hH f hf (nonzero_admissible h) h
  · rintro ⟨X, _, v, he, hu⟩
    exact ⟨H.dimension, H.dimension_pos, X, v, he, hu.ne_zero⟩

theorem admissible_nonzero_or_add_one {n : ℕ} (f : Formula n) (hf : Admissible f) :
    Nonzero f ∨ Nonzero (.add f (.const 1)) := by
  obtain ⟨d, hd, X, v, he⟩ := hf
  by_cases hv : v = 0
  · have : NeZero d := ⟨hd.ne'⟩
    right
    refine ⟨d, hd, X, v + 1, ?_, ?_⟩
    · simpa only [Evaluates, map_one] using Eval.add he (Eval.const 1)
    · simpa only [hv, zero_add] using (one_ne_zero : (1 : Mat d) ≠ 0)
  · exact Or.inl ⟨d, hd, X, v, he, hv⟩

theorem hits_admissible_iff {n s : ℕ} {H : Output n} (hH : Hits (s + 2) H)
    (f : Formula n) (hf : f.nodeCount ≤ s) :
    Admissible f ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v := by
  constructor
  · intro ha
    rcases admissible_nonzero_or_add_one f ha with hn | hn
    · obtain ⟨X, hX, v, he, _⟩ := hH f (by lia) ha hn
      exact ⟨X, hX, v, he⟩
    · have hsize : (Formula.add f (.const 1)).nodeCount ≤ s + 2 := by
        simp only [nodeCount_add, nodeCount_const]
        lia
      obtain ⟨X, hX, v, he, _⟩ := hH (.add f (.const 1)) hsize (nonzero_admissible hn) hn
      obtain ⟨a, _, hleft, _⟩ := eval_add_iff.mp he
      exact ⟨X, hX, a, hleft⟩
  · rintro ⟨X, _, v, he⟩
    exact ⟨H.dimension, H.dimension_pos, X, v, he⟩

theorem hits_admissible_inv_iff_nonzero {n s : ℕ} {H : Output n} (hH : Hits s H)
    (f : Formula n) (hf : f.nodeCount ≤ s) : Admissible (.inv f) ↔ Nonzero f := by
  constructor
  · rintro ⟨d, hd, X, v, he⟩
    have : NeZero d := ⟨hd.ne'⟩
    obtain ⟨a, he, hab, hba⟩ := eval_inv_iff.mp he
    exact ⟨d, hd, X, a, he, IsUnit.ne_zero ⟨⟨a, v, hab, hba⟩, rfl⟩⟩
  · intro hn
    obtain ⟨X, _, v, he, ⟨u, rfl⟩⟩ := (hits_nonzero_iff hH f hf).mp hn
    exact ⟨H.dimension, H.dimension_pos, X, ↑u⁻¹, Eval.inv he u.mul_inv u.inv_mul⟩

theorem admissibilityTest_iff {n : ℕ} (H : Output n) (f : Formula n) :
    H.admissibilityTest f = true ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v := by
  simp only [admissibilityTest, List.any_eq_true, Option.isSome_iff_exists]
  constructor
  · rintro ⟨X, hX, v, hv⟩
    exact ⟨X, hX, v, evalMatrix_sound f X hv⟩
  · rintro ⟨X, hX, v, hv⟩
    exact ⟨X, hX, v, evalMatrix_complete hv⟩

theorem nonzeroTest_iff {n : ℕ} (H : Output n) (f : Formula n) :
    H.nonzeroTest f = true ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v := by
  simp only [nonzeroTest, List.any_eq_true, Option.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨X, hX, v, hv, hd⟩
    exact ⟨X, hX, v, evalMatrix_sound f X hv,
      (Matrix.isUnit_iff_isUnit_det v).mpr (isUnit_iff_ne_zero.mpr hd)⟩
  · rintro ⟨X, hX, v, hv, hu⟩
    exact ⟨X, hX, v, evalMatrix_complete hv,
      ((Matrix.isUnit_iff_isUnit_det v).mp hu).ne_zero⟩

theorem hits_admissibilityTest_eq_true_iff {n s : ℕ} {H : Output n}
    (hH : Hits (s + 2) H) (f : Formula n) (hf : f.nodeCount ≤ s) :
    H.admissibilityTest f = true ↔ Admissible f := by
  rw [admissibilityTest_iff H f, hits_admissible_iff hH f hf]

theorem hits_nonzeroTest_eq_true_iff {n s : ℕ} {H : Output n}
    (hH : Hits s H) (f : Formula n) (hf : f.nodeCount ≤ s) :
    H.nonzeroTest f = true ↔ Nonzero f := by
  rw [nonzeroTest_iff H f, hits_nonzero_iff hH f hf]

end Cslib.Circuits.Rational.Internal
