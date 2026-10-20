/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
import Mathlib.Data.List.GetD

/-!
# The bits of a framed word

`frame w` doubles every bit `b` of `w` into `true, b` and ends with `false`
(`Turing.MultiTapeTM.frame`). Its bits are therefore constants or bits of `w`
(`Turing.MultiTapeTM.getElem_frame`), which is what makes framed inputs easy to feed to circuits.

## Main definitions

* `Turing.MultiTapeTM.dbl`: the framed bits without the terminator.
* `Turing.MultiTapeTM.dblT`: a finite-state transducer for these framed bits.

## Main results

* `Turing.MultiTapeTM.getElem_frame`: the bit at each position of `frame w`.
* `Turing.MultiTapeTM.getElem?_frame_two_mul`, `Turing.MultiTapeTM.getElem?_frame_two_mul_add_one`,
  `Turing.MultiTapeTM.getElem?_frame_two_mul_length`: the marker, data, and terminator bits of
  `frame w` by position.
* `Turing.MultiTapeTM.forall_getElem?_frame_iff`: a predicate agrees with `frame w` placed at offset
  `base` iff it agrees with the markers, the bits of `w`, and the terminator.
* `Turing.MultiTapeTM.forall_getElem?_append_iff`: a predicate agrees with the bits of `u ++ w` iff
  it agrees with `u` and with `w` shifted by `u.length`.
* `Turing.MultiTapeTM.length_flatMap_frame`: the length of a list of framed words.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The bit at position `j` of `frame w`: `true` at even positions below `2 |w|`, the bit `w[j / 2]`
at odd ones, and the final `false`. -/
theorem getElem_frame (w : List Bool) (j : ℕ) (hj : j < (frame w).length) :
    (frame w)[j] = if h : j < 2 * w.length then
      (if j % 2 = 0 then true else w[j / 2]'(by omega)) else false := by
  induction w generalizing j with
  | nil =>
    simp only [frame_nil, List.length_singleton, Nat.lt_one_iff] at hj
    subst hj
    rfl
  | cons b w ih =>
    match j, hj with
    | 0, _ => simp
    | 1, _ => simp [show 1 < 2 * (w.length + 1) by omega]
    | j + 2, hj =>
      simp only [frame_cons, List.getElem_cons_succ, length_frame, List.length_cons] at hj ⊢
      rw [ih j (by simpa using (by omega : j < 2 * w.length + 1))]
      by_cases h : j < 2 * w.length
      · simp only [h, show j + 2 < 2 * (w.length + 1) by omega, dite_true, Nat.add_mod_right,
          show (j + 2) / 2 = j / 2 + 1 by omega, List.getElem_cons_succ]
      · simp only [h, show ¬j + 2 < 2 * (w.length + 1) by omega, dite_false]

/-! ### Indexed bit access -/

/-- The terminator of `frame w` sits at position `2 * w.length`. -/
theorem getElem?_frame_two_mul_length (w : List Bool) :
    (frame w)[2 * w.length]? = some false := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hidx : 2 * (b :: w).length = 2 * w.length + 2 := by
      rw [List.length_cons]; omega
    rw [hidx, frame_cons]
    exact ih

/-- Each bit of `w` is preceded in `frame w` by a `true` marker at an even position. -/
theorem getElem?_frame_two_mul {w : List Bool} {j : ℕ} (hj : j < w.length) :
    (frame w)[2 * j]? = some true := by
  induction w generalizing j with
  | nil => simp at hj
  | cons b w ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j < w.length := by simpa using hj
      have hidx : 2 * (j + 1) = 2 * j + 2 := by omega
      rw [hidx, frame_cons]
      exact ih hj'

/-- The bit `w[j]` sits at the odd position `2 * j + 1` of `frame w`. -/
theorem getElem?_frame_two_mul_add_one {w : List Bool} {j : ℕ} (hj : j < w.length) :
    (frame w)[2 * j + 1]? = w[j]? := by
  induction w generalizing j with
  | nil => simp at hj
  | cons b w ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j < w.length := by simpa using hj
      have hidx : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
      rw [hidx, frame_cons]
      exact ih hj'

/-- A predicate `P : ℕ → Prop` agrees with `frame w` shifted by `base` on
`[base, base + (frame w).length)` iff it is `false` at `base + 2 * w.length` and, for each
`j < w.length`, is `true` at `base + 2 * j` and agrees with `w[j]` at `base + 2 * j + 1`. -/
theorem forall_getElem?_frame_iff (w : List Bool) (base : ℕ) (P : ℕ → Prop) :
    (∀ p, base ≤ p → p < base + (frame w).length →
        (P p ↔ (frame w)[p - base]? = some true)) ↔
      (¬ P (base + 2 * w.length) ∧
        ∀ j < w.length, P (base + 2 * j) ∧ (P (base + 2 * j + 1) ↔ w[j]? = some true)) := by
  rw [length_frame]
  constructor
  · intro h
    refine ⟨?_, fun j hj => ⟨?_, ?_⟩⟩
    · have h0 := h (base + 2 * w.length) (by omega) (by omega)
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul_length] at h0
      simpa using h0
    · have h1 := h (base + 2 * j) (by omega) (by omega)
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul hj] at h1
      simpa using h1
    · have h2 := h (base + 2 * j + 1) (by omega) (by omega)
      have hsub : base + 2 * j + 1 - base = 2 * j + 1 := by omega
      rw [hsub, getElem?_frame_two_mul_add_one hj] at h2
      exact h2
  · rintro ⟨hend, hstep⟩ p hlo hhi
    by_cases hlast : p = base + 2 * w.length
    · subst hlast
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul_length]
      simp [hend]
    · have hd : p - base < 2 * w.length := by omega
      let j := (p - base) / 2
      have hj : j < w.length := by omega
      rcases Nat.mod_two_eq_zero_or_one (p - base) with hmod | hmod
      · have hp : p = base + 2 * j := by omega
        have hsub : p - base = 2 * j := by omega
        rw [hsub, getElem?_frame_two_mul hj, hp]
        simp [(hstep j hj).1]
      · have hp : p = base + 2 * j + 1 := by omega
        have hsub : p - base = 2 * j + 1 := by omega
        rw [hsub, getElem?_frame_two_mul_add_one hj, hp]
        exact (hstep j hj).2

/-- A predicate `P : ℕ → Prop` agrees with the bits of `u ++ w` iff it agrees with `u` below
`u.length` and with `w` shifted by `u.length` on `[u.length, u.length + w.length)`. -/
theorem forall_getElem?_append_iff (u w : List Bool) (P : ℕ → Prop) :
    (∀ p < (u ++ w).length, (P p ↔ (u ++ w)[p]? = some true)) ↔
      (∀ p < u.length, (P p ↔ u[p]? = some true)) ∧
        (∀ p, u.length ≤ p → p < u.length + w.length →
          (P p ↔ w[p - u.length]? = some true)) := by
  rw [List.length_append]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hlo hhi => ?_⟩
    · have hp' := h p (by omega)
      rwa [List.getElem?_append_left hp] at hp'
    · have hp' := h p hhi
      rwa [List.getElem?_append_right hlo] at hp'
  · rintro ⟨hu, hw⟩ p hp
    by_cases hlt : p < u.length
    · rw [List.getElem?_append_left hlt]
      exact hu p hlt
    · have hle : u.length ≤ p := by omega
      rw [List.getElem?_append_right hle]
      exact hw p hle hp

/-- A list of framed words spends `2 * |t| + 1` bits on each word `t`. -/
theorem length_flatMap_frame (l : List (List Bool)) :
    (l.flatMap frame).length = (l.map fun t => 2 * t.length + 1).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [List.flatMap_cons, List.length_append, length_frame, ih,
      List.map_cons, List.sum_cons]

/-! ### Framed words -/

/-- Each bit preceded by `true`: `frame` without its closing `false`. -/
def dbl (l : List Bool) : List Bool := l.flatMap fun b => [true, b]

theorem frame_eq_dbl (l : List Bool) : frame l = dbl l ++ [false] := rfl

@[simp] theorem dbl_append (l l' : List Bool) : dbl (l ++ l') = dbl l ++ dbl l' :=
  List.flatMap_append

@[simp] theorem dbl_false : dbl [false] = [true, false] := rfl

theorem dbl_flatten (L : List (List Bool)) : dbl L.flatten = (L.map dbl).flatten := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

theorem dbl_dbl_replicate (n : ℕ) :
    dbl (dbl (List.replicate n true)) = (List.replicate n [true, true, true, true]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, dbl, ← ih]

theorem getD_frame_two_mul (w : List Bool) (i : ℕ) :
    (frame w).getD (2 * i) false = decide (i < w.length) := by
  induction w generalizing i with
  | nil => rcases i with _ | i <;> simp [frame_nil, List.getD_eq_getElem?_getD]
  | cons b w ih =>
    rcases i with _ | i
    · simp [frame_cons]
    · rw [frame_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getD_cons_succ,
        List.getD_cons_succ, ih]
      simp

theorem getD_frame_two_mul_add_one (w : List Bool) (i : ℕ) :
    (frame w).getD (2 * i + 1) false = w.getD i false := by
  induction w generalizing i with
  | nil => rcases i with _ | i <;> simp [frame_nil, List.getD_eq_getElem?_getD]
  | cons b w ih =>
    rcases i with _ | i
    · simp [frame_cons]
    · rw [frame_cons, show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega, List.getD_cons_succ,
        List.getD_cons_succ, ih, List.getD_cons_succ]

/-- Doubles each bit after a `true`. -/
def dblT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [true, b])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

theorem dblT_run (l : List Bool) : dblT.run () l = dbl l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [Transducer.run_cons]
    change [true, b] ++ dblT.run () l = [true, b] ++ dbl l
    rw [ih]

end Turing.MultiTapeTM
