/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to crei/tidy-universal `Encodings/Basic.lean`)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic

/-!
# The bits of a framed word

`frame w` doubles every bit `b` of `w` into `true, b` and ends with `false`
(`Turing.MultiTapeTM.frame`). Its bits are therefore constants or bits of `w`
(`Turing.MultiTapeTM.getElem_frame`), which is what makes framed inputs easy to feed to circuits.
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

end Turing.MultiTapeTM
