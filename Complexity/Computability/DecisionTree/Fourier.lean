/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic
public import Complexity.Foundations.BooleanAnalysis.Fourier
import Mathlib.Tactic.Ring

/-!
# Decision trees have low Fourier degree

A function computed by a decision tree of depth `d` has no Fourier weight above degree `d`
(`DecisionTree.fourierCoeff_eq_zero_of_depth_lt`) [O'Donnell, Chapter 3][ODonnell2014]: the
function of a node querying `i` is `(f₀ + f₁) / 2 + χ_{i} (f₀ - f₁) / 2` in terms of the functions
`f₀` and `f₁` of its subtrees, and multiplying by `χ_{i}` moves a coefficient by at most one in
degree.

## Main results

* `Cslib.DecisionTree.fourierCoeff_eq_zero_of_depth_lt`: decision trees of depth `d` have Fourier
  degree at most `d`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.DecisionTree

open Finset BitString

variable {n : ℕ} {β : Type*}

/-- Toggling one coordinate changes the size of a set by at most one. -/
private theorem card_le_card_symmDiff_singleton_add_one (i : Fin n) (S : Finset (Fin n)) :
    #S ≤ #(symmDiff {i} S) + 1 := by
  refine (card_le_card fun j hj => ?_).trans (card_union_le _ {i})
  by_cases hji : j = i
  · simp [hji]
  · simp [mem_symmDiff, hji, hj]

/-- **Decision trees have low Fourier degree**: a function of the output of a decision tree of
depth `d` has no Fourier weight on sets of more than `d` coordinates. -/
theorem fourierCoeff_eq_zero_of_depth_lt (g : β → ℝ) (t : DecisionTree (Fin n) β)
    {S : Finset (Fin n)} (hS : t.depth < #S) : fourierCoeff (fun x => g (t.eval x)) S = 0 := by
  induction t generalizing S with
  | leaf b =>
    have hne : S ≠ ∅ := by
      rintro rfl
      simp at hS
    simp [fourierCoeff_const, hne]
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [depth_node] at hS
    -- the function of the node in terms of the functions of the subtrees
    have h : (fun x => g ((node i t₀ t₁).eval x)) = fun x =>
        (1 / 2 : ℝ) * (g (t₀.eval x) + g (t₁.eval x)) +
          chi {i} x * ((1 / 2 : ℝ) * (g (t₀.eval x) - g (t₁.eval x))) := by
      funext x
      cases hx : x i <;>
        simp only [eval_node, chi, prod_singleton, hx, signVal_false, signVal_true, Bool.cond_false,
          Bool.cond_true] <;> ring
    have hi := card_le_card_symmDiff_singleton_add_one i S
    rw [h, fourierCoeff_add, fourierCoeff_const_mul, fourierCoeff_add, fourierCoeff_chi_mul,
      fourierCoeff_const_mul, fourierCoeff_sub, ih₀ (by omega), ih₁ (by omega), ih₀ (by omega),
      ih₁ (by omega)]
    simp

end Cslib.DecisionTree
