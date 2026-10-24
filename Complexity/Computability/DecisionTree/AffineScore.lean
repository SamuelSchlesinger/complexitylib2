/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Leaves
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Affine leaf scores for decision trees

Every structural leaf `p ∈ t.paths` of a decision tree `t` of depth at most `d` has a linear score
`leafScore B d q t p` in the real query margins `q : ι → ℝ`, summing `B ^ (d - 1 - depth) * q i`
over the nodes along `p` where `p` takes the `true` branch.

When every query margin has magnitude at most `M ≥ 1` and the Boolean oracle `x : ι → Bool` agrees
with the sign of `q` with margin at least `1` (`x i = true → 1 ≤ q i` and `x i = false → q i ≤ -1`),
choosing base `B = 2 * M + 1` ensures that the score of the reached leaf `t.path x` exceeds the
score of every other structural leaf `p ∈ t.paths` by at least `1` (Theorem 2.9).

## Main definitions

* `Cslib.DecisionTree.paths`: the structural list of root-to-leaf paths in a decision tree.
* `Cslib.DecisionTree.leafScore`: the weighted sum of `true`-branch query margins along a path.

## Main results

* `Cslib.DecisionTree.length_paths`, `Cslib.DecisionTree.path_mem_paths`,
  `Cslib.DecisionTree.nodup_paths`: structural properties of `paths`.
* `Cslib.DecisionTree.leafScore_zero`, `Cslib.DecisionTree.leafScore_add`,
  `Cslib.DecisionTree.leafScore_smul`: linearity of `leafScore` in the query margins.
* `Cslib.DecisionTree.two_mul_abs_leafScore_le`: uniform magnitude bound
  `2 * |leafScore (2 * M + 1) d q t p| ≤ (2 * M + 1) ^ d - 1`.
* `Cslib.DecisionTree.leafScore_add_one_le_leafScore_path`,
  `Cslib.DecisionTree.leafScore_add_one_le_leafScore_path_decide`: Theorem 2.9, strict unit-margin
  separation of the reached leaf from all other structural leaves.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Theorem 2.9]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.DecisionTree

variable {ι β : Type*}

/-! ### Structural root-to-leaf paths -/

/-- The structural list of root-to-leaf paths in a decision tree. -/
def paths : DecisionTree ι β → List (List Bool)
  | .leaf _ => [[]]
  | .node _ left right => left.paths.map (false :: ·) ++ right.paths.map (true :: ·)

@[simp]
theorem paths_leaf (b : β) : (leaf b : DecisionTree ι β).paths = [[]] :=
  rfl

@[simp]
theorem paths_node (i : ι) (left right : DecisionTree ι β) :
    (node i left right).paths = left.paths.map (false :: ·) ++ right.paths.map (true :: ·) :=
  rfl

/-- The number of structural root-to-leaf paths equals `leafCount`. -/
@[simp]
theorem length_paths (t : DecisionTree ι β) : t.paths.length = t.leafCount := by
  induction t with
  | leaf _ => rfl
  | node _ left right ihl ihr => simp [paths, leafCount, ihl, ihr]

/-- The path followed by any input belongs to `t.paths`. -/
theorem path_mem_paths (t : DecisionTree ι β) (x : ι → Bool) : t.path x ∈ t.paths := by
  induction t with
  | leaf _ => simp [path, paths]
  | node i left right ihl ihr =>
    rw [path, paths, List.mem_append, List.mem_map, List.mem_map]
    cases hx : x i
    · left
      exact ⟨left.path x, ihl, by simp⟩
    · right
      exact ⟨right.path x, ihr, by simp⟩

/-- The structural paths of a decision tree are pairwise distinct. -/
theorem nodup_paths (t : DecisionTree ι β) : t.paths.Nodup := by
  induction t with
  | leaf _ => simp [paths]
  | node _ left right ihl ihr =>
    rw [paths, List.nodup_append]
    refine ⟨ihl.map List.cons_injective, ihr.map List.cons_injective, ?_⟩
    rintro p hp₁ _ hp₂ rfl
    obtain ⟨p₁, _, rfl⟩ := List.mem_map.mp hp₁
    obtain ⟨p₂, _, h⟩ := List.mem_map.mp hp₂
    exact Bool.noConfusion (List.cons.inj h).1

/-- Relabelling queries preserves the structural path list. -/
@[simp]
theorem paths_mapQueries {κ : Type*} (f : ι → κ) (t : DecisionTree ι β) :
    (t.mapQueries f).paths = t.paths := by
  induction t with
  | leaf _ => rfl
  | node _ left right ihl ihr => simp [mapQueries, paths, ihl, ihr]

/-! ### Affine leaf scores and separation -/

/-- Score of a root-to-leaf path `p` in `t` at depth budget `d` with base `B` and real query
margins `q : ι → ℝ`, summing `B ^ (d - 1 - depth) * q i` over nodes along `p` where `p`
takes the `true` branch. -/
def leafScore (B : ℝ) : ℕ → (ι → ℝ) → DecisionTree ι β → List Bool → ℝ
  | _, _, .leaf _, _ => 0
  | _, _, .node _ _ _, [] => 0
  | d, q, .node _ left _, false :: p => leafScore B (d - 1) q left p
  | d, q, .node i _ right, true :: p => B ^ (d - 1) * q i + leafScore B (d - 1) q right p

@[simp]
theorem leafScore_zero (B : ℝ) (d : ℕ) (t : DecisionTree ι β) (p : List Bool) :
    leafScore B d 0 t p = 0 := by
  induction t generalizing d p with
  | leaf _ => rfl
  | node _ left right ihl ihr =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> simp [leafScore, ihl, ihr]

theorem leafScore_add (B : ℝ) (d : ℕ) (q₁ q₂ : ι → ℝ) (t : DecisionTree ι β) (p : List Bool) :
    leafScore B d (q₁ + q₂) t p = leafScore B d q₁ t p + leafScore B d q₂ t p := by
  induction t generalizing d p with
  | leaf _ => simp [leafScore]
  | node i left right ihl ihr =>
    cases p with
    | nil => simp [leafScore]
    | cons b p =>
      cases b with
      | false => exact ihl (d - 1) p
      | true =>
        simp only [leafScore, Pi.add_apply, ihr (d - 1) p]
        ring

theorem leafScore_smul (B c : ℝ) (d : ℕ) (q : ι → ℝ) (t : DecisionTree ι β) (p : List Bool) :
    leafScore B d (c • q) t p = c * leafScore B d q t p := by
  induction t generalizing d p with
  | leaf _ => simp [leafScore]
  | node i left right ihl ihr =>
    cases p with
    | nil => simp [leafScore]
    | cons b p =>
      cases b with
      | false => exact ihl (d - 1) p
      | true =>
        simp only [leafScore, Pi.smul_apply, smul_eq_mul, ihr (d - 1) p]
        ring

theorem leafScore_mapQueries {κ : Type*} (f : ι → κ) (B : ℝ) (d : ℕ) (q : κ → ℝ)
    (t : DecisionTree ι β) (p : List Bool) :
    leafScore B d q (t.mapQueries f) p = leafScore B d (q ∘ f) t p := by
  induction t generalizing d p with
  | leaf _ => rfl
  | node _ left right ihl ihr =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> simp [mapQueries, leafScore, ihl, ihr]

/-- For base `B = 2 * M + 1` and query margins bounded in magnitude by `M ≥ 0`, every leaf score at
depth budget `d ≥ t.depth` has magnitude at most `((2 * M + 1) ^ d - 1) / 2`. -/
theorem two_mul_abs_leafScore_le {M : ℝ} {d : ℕ} {q : ι → ℝ} (t : DecisionTree ι β)
    (p : List Bool) (ht : t.depth ≤ d) (hM : 0 ≤ M) (hq : ∀ i, |q i| ≤ M) :
    2 * |leafScore (2 * M + 1) d q t p| ≤ (2 * M + 1) ^ d - 1 := by
  induction t generalizing d p with
  | leaf _ =>
    have hpow : (1 : ℝ) ≤ (2 * M + 1) ^ d := one_le_pow₀ (by linarith)
    simp only [leafScore, abs_zero, mul_zero]
    linarith
  | node i left right ihl ihr =>
    have hd : 1 ≤ d := by rw [depth_node] at ht; omega
    have hleft : left.depth ≤ d - 1 := by rw [depth_node] at ht; omega
    have hright : right.depth ≤ d - 1 := by rw [depth_node] at ht; omega
    have hpow_pos : (0 : ℝ) ≤ (2 * M + 1) ^ (d - 1) := pow_nonneg (by linarith) _
    have hpow_eq : (2 * M + 1) ^ d = (2 * M + 1) ^ (d - 1) * (2 * M + 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ]
    cases p with
    | nil =>
      have hpow : (1 : ℝ) ≤ (2 * M + 1) ^ d := one_le_pow₀ (by linarith)
      simp only [leafScore, abs_zero, mul_zero]
      linarith
    | cons b p =>
      cases b with
      | false =>
        have hrec := ihl p hleft
        have hmul : 0 ≤ (2 * M + 1) ^ (d - 1) * (2 * M) := mul_nonneg hpow_pos (by linarith)
        simp only [leafScore]
        linarith
      | true =>
        have hrec := ihr p hright
        have hterm : |(2 * M + 1) ^ (d - 1) * q i| ≤ (2 * M + 1) ^ (d - 1) * M := by
          rw [abs_mul, abs_of_nonneg hpow_pos]
          exact mul_le_mul_of_nonneg_left (hq i) hpow_pos
        have htri := abs_add_le ((2 * M + 1) ^ (d - 1) * q i)
          (leafScore (2 * M + 1) (d - 1) q right p)
        simp only [leafScore]
        linarith

/-- **Affine leaf scores** (Theorem 2.9): if `t` has depth at most `d`, every query margin `q i`
has magnitude at most `M` (`1 ≤ M`), and `x : ι → Bool` agrees with the sign of `q` with margin at
least `1` (`x i = true → 1 ≤ q i` and `x i = false → q i ≤ -1`), then with base `B = 2 * M + 1`,
the score of the reached leaf `t.path x` exceeds the score of every other structural leaf
`p ∈ t.paths` (`p ≠ t.path x`) by at least `1`. -/
theorem leafScore_add_one_le_leafScore_path {M : ℝ} {d : ℕ} {q : ι → ℝ} {x : ι → Bool}
    (t : DecisionTree ι β) {p : List Bool} (ht : t.depth ≤ d) (hM : 1 ≤ M)
    (hq : ∀ i, |q i| ≤ M) (htrue : ∀ i, x i = true → 1 ≤ q i)
    (hfalse : ∀ i, x i = false → q i ≤ -1) (hp : p ∈ t.paths) (hne : p ≠ t.path x) :
    leafScore (2 * M + 1) d q t p + 1 ≤ leafScore (2 * M + 1) d q t (t.path x) := by
  induction t generalizing d p with
  | leaf _ =>
    rw [paths_leaf, List.mem_singleton] at hp
    exact (hne (hp.trans rfl)).elim
  | node i left right ihl ihr =>
    have hleft : left.depth ≤ d - 1 := by rw [depth_node] at ht; omega
    have hright : right.depth ≤ d - 1 := by rw [depth_node] at ht; omega
    have hpow_pos : (0 : ℝ) ≤ (2 * M + 1) ^ (d - 1) := pow_nonneg (by linarith) _
    rw [paths_node, List.mem_append, List.mem_map, List.mem_map] at hp
    rcases hp with ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
    · cases hx : x i with
      | false =>
        have hp'ne : p' ≠ left.path x := fun h => by
          apply hne
          simp [path, hx, h]
        simpa [path, hx, leafScore] using ihl hleft hp' hp'ne
      | true =>
        have hlp := two_mul_abs_leafScore_le left p' hleft (by linarith) hq
        have hrp := two_mul_abs_leafScore_le right (right.path x) hright (by linarith) hq
        have hle_abs_l := le_abs_self (leafScore (2 * M + 1) (d - 1) q left p')
        have hneg_abs_r := neg_le_abs (leafScore (2 * M + 1) (d - 1) q right (right.path x))
        have hqi : (2 * M + 1) ^ (d - 1) * 1 ≤ (2 * M + 1) ^ (d - 1) * q i :=
          mul_le_mul_of_nonneg_left (htrue i hx) hpow_pos
        simp only [path, hx, Bool.cond_true, leafScore]
        linarith
    · cases hx : x i with
      | false =>
        have hrp := two_mul_abs_leafScore_le right p' hright (by linarith) hq
        have hlp := two_mul_abs_leafScore_le left (left.path x) hleft (by linarith) hq
        have hle_abs_r := le_abs_self (leafScore (2 * M + 1) (d - 1) q right p')
        have hneg_abs_l := neg_le_abs (leafScore (2 * M + 1) (d - 1) q left (left.path x))
        have hqi : (2 * M + 1) ^ (d - 1) * q i ≤ (2 * M + 1) ^ (d - 1) * (-1) :=
          mul_le_mul_of_nonneg_left (hfalse i hx) hpow_pos
        simp only [path, hx, Bool.cond_false, leafScore]
        linarith
      | true =>
        have hp'ne : p' ≠ right.path x := fun h => by
          apply hne
          simp [path, hx, h]
        have hrec := ihr hright hp' hp'ne
        simp only [path, hx, Bool.cond_true, leafScore]
        linarith

/-- Specialization of `leafScore_add_one_le_leafScore_path` to the threshold query oracle
`fun i => decide (0 ≤ q i)` when every query margin has magnitude between `1` and `M`. -/
theorem leafScore_add_one_le_leafScore_path_decide {M : ℝ} {d : ℕ} {q : ι → ℝ}
    (t : DecisionTree ι β) {p : List Bool} (ht : t.depth ≤ d) (hM : 1 ≤ M)
    (hq_min : ∀ i, 1 ≤ |q i|) (hq_max : ∀ i, |q i| ≤ M) (hp : p ∈ t.paths)
    (hne : p ≠ t.path (fun i => decide (0 ≤ q i))) :
    leafScore (2 * M + 1) d q t p + 1 ≤
      leafScore (2 * M + 1) d q t (t.path (fun i => decide (0 ≤ q i))) := by
  refine leafScore_add_one_le_leafScore_path t ht hM hq_max ?_ ?_ hp hne
  · intro i hi
    have h0 : 0 ≤ q i := of_decide_eq_true hi
    have habs := hq_min i
    rwa [abs_of_nonneg h0] at habs
  · intro i hi
    have h0 : ¬ 0 ≤ q i := of_decide_eq_false hi
    have habs := hq_min i
    rw [abs_of_neg (lt_of_not_ge h0)] at habs
    linarith

end Cslib.DecisionTree
