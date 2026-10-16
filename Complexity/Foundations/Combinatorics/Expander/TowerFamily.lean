/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Contraction
public import Complexity.Foundations.Combinatorics.Expander.Reindex
public import Complexity.Foundations.Combinatorics.Expander.Tower
public import Mathlib.Data.Nat.Log

/-!
# Zig-zag expanders on every vertex count

An explicitly numbered base gives explicit numberings of every level of the zig-zag tower.
For a requested size `n ≥ 2`, choose the first tower with at least `n` vertices. Its size is at most
`b*n`, where `b` is the base size. Bounded-fiber contraction and laziness then give a graph
on exactly `Fin n`, with degree and spectral gap independent of `n`. Sizes zero and one use loops.

The rotation is an executable definition given the base rotation and numbering. This is not yet
a uniform machine-time certificate. The contraction also increases the already large degree;
asymptotic constructibility and practical enumeration are separate questions.

## Main definitions

* `Cslib.RotationMap.ZigzagTowerVertex.equivFin`: recursive numbering from a numbered base.
* `Cslib.RotationMap.zigzagTowerFamily`: the contracted lazy tower on every `Fin n`.

## Main results

* `Cslib.RotationMap.zigzagTower_size_bounds`: the selected tower has size between `n` and `b*n`.
* `Cslib.RotationMap.spectralExpansion_zigzagTowerFamily_le`: the uniform spectral bound.

## References

The underlying tower is the construction of [O. Reingold, S. Vadhan, A. Wigderson,
*Entropy waves, the zig-zag graph product, and new constant-degree expanders*,
Section 1.2][ReingoldVadhanWigderson2002]. The size adjustment uses bounded-fiber contraction.
-/

@[expose] public section

namespace Cslib.RotationMap

variable {B D : Type*} {b : ℕ}

/-- Number a tower vertex by recursively pairing the explicit base indices. -/
def ZigzagTowerVertex.equivFin (numbering : B ≃ Fin b) :
    (n : ℕ) → ZigzagTowerVertex B n ≃ Fin (b ^ (n + 1))
  | 0 => numbering.trans (finCongr (pow_one b).symm)
  | n + 1 => (((equivFin numbering n).prodCongr numbering).trans finProdFinEquiv).trans
      (finCongr (pow_succ b (n + 1)).symm)

/-- The first tower size at least `n` is bounded by `b*n`, independently of its depth. -/
theorem zigzagTower_size_bounds (hb : 1 < b) {n : ℕ} (hn : 2 ≤ n) :
    n ≤ b ^ (Nat.clog b n - 1 + 1) ∧ b ^ (Nat.clog b n - 1 + 1) ≤ b * n := by
  have hp := Nat.clog_pos hb hn
  have he : Nat.clog b n - 1 + 1 = Nat.clog b n := by lia
  refine ⟨by rw [he]; exact Nat.le_pow_clog hb n, ?_⟩
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left b (Nat.le_of_lt (Nat.pow_pred_clog_lt_self hb hn))

/-- A constant-degree graph on every vertex count, from a numbered zig-zag base. -/
def zigzagTowerFamily (H : RotationMap B D) (e : B ≃ (Fin 2 → D × D))
    (numbering : B ≃ Fin b) (hb : 1 < b) (n : ℕ) :
    RotationMap (Fin n) ((Fin b × (D × D)) ⊕ (Fin b × (D × D))) :=
  if hn : 2 ≤ n then
    (((zigzagTower H e (Nat.clog b n - 1)).reindex
      (ZigzagTowerVertex.equivFin numbering (Nat.clog b n - 1))).contractFin
      (zigzagTower_size_bounds hb hn).2).lazy
  else loops (Fin n) _

variable [Fintype B] [Fintype D] [Nonempty D]

/-- A tower with expansion at most `c ≤ 1` gives expansion at most
`1 - (1-c)²/(16*b²)` on every vertex count after contraction and laziness. -/
theorem spectralExpansion_zigzagTowerFamily_le (H : RotationMap B D)
    (e : B ≃ (Fin 2 → D × D)) (numbering : B ≃ Fin b) (hb : 1 < b)
    {c : ℝ} (hc : c ^ 2 + H.spectralExpansion + H.spectralExpansion ^ 2 ≤ c)
    (hc1 : c ≤ 1) (n : ℕ) :
    (zigzagTowerFamily H e numbering hb n).spectralExpansion ≤
      1 - (1 - c) ^ 2 / (16 * b ^ 2) := by
  have hc0 : 0 ≤ c := by nlinarith [H.spectralExpansion_nonneg, sq_nonneg c]
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hgap : 0 ≤ 1 - c := sub_nonneg.mpr hc1
  unfold zigzagTowerFamily
  split
  · rename_i hn
    have h := spectralExpansion_contractFin_lazy_le
      ((zigzagTower H e (Nat.clog b n - 1)).reindex
        (ZigzagTowerVertex.equivFin numbering (Nat.clog b n - 1)))
      (zigzagTower_size_bounds hb hn).2 (zigzagTower_size_bounds hb hn).1 hn
    rw [spectralExpansion_reindex] at h
    have hG := spectralExpansion_zigzagTower_le H e hc (Nat.clog b n - 1)
    refine h.trans ?_
    gcongr
  · rename_i hn
    have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by lia)
    rw [spectralExpansion_eq_zero_of_subsingleton]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : 0 < (16 : ℝ) * b ^ 2)).mpr
    nlinarith

end Cslib.RotationMap
