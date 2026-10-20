/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Numbering tuples over finite universes

These generic helpers number finite tuples without depending on machine encodings. The index
uses the first coordinate as the least significant digit, as in Mathlib's `finFunctionFinEquiv`.
The public names and numbering convention are unchanged from their original location in
`Complexity.Logics.FirstOrder.Encoding`, which publicly imports this module.

## Main definitions

* `Cslib.Logic.tupleIndex`: the colexicographic index of a tuple of natural-number digits.
* `Cslib.Logic.tupleEquiv`: number tuples along an enumeration of their coordinates.

## Main results

* `Cslib.Logic.tupleIndex_lt_iff`: numerical order agrees with the highest differing coordinate.
* `Cslib.Logic.tupleIndex_lt_pow_iff`: indices below a power have zero higher digits.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32, for the distinct
  lexicographic convention required by ordered first-order queries.
-/

@[expose] public section

namespace Cslib.Logic

/-! ### Tuples -/

/-- The index of a tuple of `Fin n` in the truth table of a relation of arity `k`: the number
`∑ i, x i * n ^ i` below `n ^ k`, the order of `finFunctionFinEquiv`. -/
def tupleIndex {n k : ℕ} (x : Fin k → Fin n) : ℕ :=
  finFunctionFinEquiv x

theorem tupleIndex_apply {n k : ℕ} (x : Fin k → Fin n) :
    tupleIndex x = ∑ i : Fin k, (x i : ℕ) * n ^ (i : ℕ) :=
  finFunctionFinEquiv_apply x

theorem tupleIndex_lt {n k : ℕ} (x : Fin k → Fin n) : tupleIndex x < n ^ k :=
  (finFunctionFinEquiv x).2

theorem tupleIndex_injective {n k : ℕ} : Function.Injective (tupleIndex (n := n) (k := k)) :=
  fun _ _ h => finFunctionFinEquiv.injective (Fin.ext h)

/-- Number tuples whose coordinates are enumerated by `e`, using the same colexicographic
indexing as `tupleIndex`. -/
def tupleEquiv {ι : Type*} {n d : ℕ} (e : ι ≃ Fin d) : (ι → Fin n) ≃ Fin (n ^ d) :=
  (e.arrowCongr (Equiv.refl (Fin n))).trans finFunctionFinEquiv

@[simp]
theorem tupleEquiv_apply_val {ι : Type*} {n d : ℕ} (e : ι ≃ Fin d) (x : ι → Fin n) :
    (tupleEquiv e x).val = tupleIndex (x ∘ e.symm) := rfl

@[simp]
theorem tupleEquiv_symm_apply {ι : Type*} {n d : ℕ} (e : ι ≃ Fin d) (u : Fin (n ^ d))
    (i : ι) : (tupleEquiv e).symm u i = finFunctionFinEquiv.symm u (e i) := rfl

theorem tupleEquiv_symm_apply_val {ι : Type*} {n d : ℕ} (e : ι ≃ Fin d)
    (u : Fin (n ^ d)) (i : ι) :
    ((tupleEquiv e).symm u i : ℕ) = u / n ^ (e i : ℕ) % n := by
  rw [tupleEquiv_symm_apply, finFunctionFinEquiv_symm_apply_val]

/-- The tuple with a given index. -/
theorem tupleIndex_symm {n k : ℕ} (i : Fin (n ^ k)) :
    tupleIndex (finFunctionFinEquiv.symm i) = i := by
  simp [tupleIndex]

theorem tupleIndex_comp_cast {n k l : ℕ} (h : k = l) (x : Fin l → Fin n) :
    tupleIndex (x ∘ Fin.cast h) = tupleIndex x := by
  subst h
  rfl

theorem tupleIndex_snoc {n k : ℕ} (x : Fin (k + 1) → Fin n) :
    tupleIndex x = tupleIndex (x ∘ Fin.castSucc) + (x (Fin.last k) : ℕ) * n ^ k := by
  simp only [tupleIndex_apply, Fin.sum_univ_castSucc, Function.comp_apply, Fin.val_castSucc,
    Fin.val_last]

/-- When all coordinates of `x : Fin k → Fin n` at indices `≥ a` are zero, `tupleIndex x` equals
the index of its prefix of length `a`. -/
theorem tupleIndex_eq_of_high_zero {n a : ℕ} :
    ∀ {k : ℕ} (ha : a ≤ k) {x : Fin k → Fin n}
      (_ : ∀ i : Fin k, a ≤ (i : ℕ) → (x i : ℕ) = 0),
      tupleIndex x = tupleIndex (fun j : Fin a => x (Fin.castLE ha j))
  | k, ha, x, hx => by
    obtain rfl | hlt := eq_or_lt_of_le ha
    · rfl
    · cases k with
      | zero => omega
      | succ k =>
        rw [tupleIndex_snoc x, hx (Fin.last k) (by simp; omega), Nat.zero_mul, Nat.add_zero]
        exact tupleIndex_eq_of_high_zero (x := x ∘ Fin.castSucc) (Nat.lt_succ_iff.1 hlt)
          (fun i hi => hx i.castSucc (by simpa using hi))

/-- For `a ≤ k`, a `k`-tuple has index `< n ^ a` iff all coordinates at indices `≥ a` are zero. -/
theorem tupleIndex_lt_pow_iff {n a : ℕ} :
    ∀ {k : ℕ} (_ : a ≤ k) (x : Fin k → Fin n),
      tupleIndex x < n ^ a ↔ ∀ i : Fin k, a ≤ (i : ℕ) → (x i : ℕ) = 0
  | k, ha, x => by
    obtain rfl | hlt := eq_or_lt_of_le ha
    · exact ⟨fun _ i hi => absurd i.2 (by omega), fun _ => tupleIndex_lt x⟩
    · cases k with
      | zero => omega
      | succ k =>
        have ha' : a ≤ k := Nat.lt_succ_iff.1 hlt
        constructor
        · intro hlt' i hi
          rw [tupleIndex_snoc x] at hlt'
          have hlast : (x (Fin.last k) : ℕ) = 0 := by
            by_contra hne
            have hn : 1 ≤ n := by have := (x (Fin.last k)).2; omega
            have h1 : n ^ a ≤ n ^ k := Nat.pow_le_pow_right hn ha'
            have h2 : n ^ k ≤ (x (Fin.last k) : ℕ) * n ^ k :=
              Nat.le_mul_of_pos_left _ (by omega)
            omega
          induction i using Fin.lastCases with
          | last => exact hlast
          | cast i =>
            rw [hlast, Nat.zero_mul, Nat.add_zero] at hlt'
            exact (tupleIndex_lt_pow_iff ha' (x ∘ Fin.castSucc)).1 hlt' i (by simpa using hi)
        · intro hx
          rw [tupleIndex_eq_of_high_zero ha hx]
          exact tupleIndex_lt _

/-- The numerical order on `tupleIndex` is the colexicographic order on `Fin k → Fin n`
(comparing at the most significant coordinate where the tuples differ). -/
theorem tupleIndex_lt_iff {n : ℕ} :
    ∀ {k : ℕ} (x y : Fin k → Fin n),
      tupleIndex x < tupleIndex y ↔
        ∃ i : Fin k, x i < y i ∧ ∀ j : Fin k, i < j → x j = y j
  | 0, x, y => by simp [tupleIndex_apply]
  | k + 1, x, y => by
    rw [tupleIndex_snoc x, tupleIndex_snoc y]
    have hx := tupleIndex_lt (x ∘ Fin.castSucc)
    have hy := tupleIndex_lt (y ∘ Fin.castSucc)
    have hsplit : tupleIndex (x ∘ Fin.castSucc) + (x (Fin.last k) : ℕ) * n ^ k <
        tupleIndex (y ∘ Fin.castSucc) + (y (Fin.last k) : ℕ) * n ^ k ↔
        x (Fin.last k) < y (Fin.last k) ∨
          (x (Fin.last k) = y (Fin.last k) ∧
            tupleIndex (x ∘ Fin.castSucc) < tupleIndex (y ∘ Fin.castSucc)) := by
      rcases lt_trichotomy (x (Fin.last k)) (y (Fin.last k)) with hlt | heq | hgt
      · have hle : ((x (Fin.last k) : ℕ) + 1) * n ^ k ≤ (y (Fin.last k) : ℕ) * n ^ k :=
          Nat.mul_le_mul_right (n ^ k) hlt
        rw [Nat.add_mul, Nat.one_mul] at hle
        exact ⟨fun _ => Or.inl hlt, fun _ => by omega⟩
      · simp [heq]
      · have hle : ((y (Fin.last k) : ℕ) + 1) * n ^ k ≤ (x (Fin.last k) : ℕ) * n ^ k :=
          Nat.mul_le_mul_right (n ^ k) hgt
        rw [Nat.add_mul, Nat.one_mul] at hle
        have hnot1 : ¬ (x (Fin.last k) < y (Fin.last k)) := by omega
        have hnot2 : x (Fin.last k) ≠ y (Fin.last k) := by omega
        exact ⟨fun h => by omega, fun h => h.elim (fun h => absurd h hnot1)
          (fun ⟨h, _⟩ => absurd h hnot2)⟩
    rw [hsplit, tupleIndex_lt_iff (x ∘ Fin.castSucc) (y ∘ Fin.castSucc)]
    constructor
    · rintro (hlt | ⟨heq, i, hi, hj⟩)
      · exact ⟨Fin.last k, hlt, fun j hj => absurd (Fin.le_last j) (not_le_of_gt hj)⟩
      · refine ⟨i.castSucc, hi, fun j hjlt => ?_⟩
        induction j using Fin.lastCases with
        | last => exact heq
        | cast j => exact hj j (Fin.castSucc_lt_castSucc_iff.1 hjlt)
    · rintro ⟨i, hi, hj⟩
      induction i using Fin.lastCases with
      | last => exact Or.inl hi
      | cast i =>
        refine Or.inr ⟨hj (Fin.last k) (Fin.castSucc_lt_last i), i, hi, fun j hlt => ?_⟩
        exact hj j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hlt)

end Cslib.Logic
