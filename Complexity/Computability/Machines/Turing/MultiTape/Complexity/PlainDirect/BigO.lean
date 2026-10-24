/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (spike for #862, not for merge)

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas
import Complexity.Computability.Machines.Turing.MultiTape.Deterministic
import Mathlib.Tactic.Linarith

/-!
# Plain bounds up to constants without a tidy calculus (spike)

The composition and case distinction of `Turing.MultiTapeTM.ComputableInO`, proved directly from
plain hypotheses, with the same bounds as the tidy rules `ComputableTidilyInO.comp` and
`ComputableTidilyInO.ite`. No tidy asymptotic predicate is imported or used.

The tidy normal form turns a machine within time `t` and space `s` into a tidy machine within time
`2 t + 3 s + O(1)` and space `O(s + 1)`. The `3 s` in the time bound would break a bound `O(T)` when
the space bound `S` exceeds `T`; it is absorbed because a machine within time `t` visits at most
`k t + k` cells, so the normal form is applied with space `min s (k t + k)`
(the private `exists_computesTidily`). The overhead is then a
constant factor in each bound separately, which `ComputableInO` absorbs: the bounds of the direct
rules are exactly those of the tidy rules.

## Main results

* `Turing.MultiTapeTM.PlainDirect.ComputableInO.comp`: composition, within time
  `O(T₁ a + T₂ (g a))` and space `O(S₁ a + S₂ (g a))`.
* `Turing.MultiTapeTM.PlainDirect.ComputableInO.ite`: case distinction, within the bounds of the
  test plus those of the branch taken.
-/

@[expose] public section

namespace Turing.MultiTapeTM.PlainDirect

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- A computation within `t` steps visits at most `k t + k` work-tape cells. A copy of
`Turing.MultiTapeTM.ComputesInTimeAndSpace.space_linear`, which today sits in a module above the
tidy polynomial-time calculus. -/
theorem space_linear {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State}
    {input output : List Symbol} {t s : ℕ} (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output t (k * t + k) :=
  ⟨h.1, h.2.1, runsInSpace_of_halted (runsInTime_iff_halted.mp h.2.1) (tm.space_linear _ t)⟩

/-- Absorb an additive constant into the factor of `n + 1`. -/
theorem le_mul_succ {u A B C n : ℕ} (h : u ≤ A * (n + 1) + B) (hC : A + B ≤ C) :
    u ≤ C * (n + 1) := by
  have hB : B ≤ B * (n + 1) := Nat.le_mul_of_pos_right B (Nat.succ_pos n)
  have : A * (n + 1) + B ≤ (A + B) * (n + 1) := by rw [Nat.add_mul]; omega
  exact h.trans (this.trans (Nat.mul_le_mul_right _ hC))

namespace ComputableInO

/-- A plain certificate within time `O(T)` and space `O(S)` gives a tidy machine within the same
bounds up to a constant. -/
private theorem exists_computesTidily {f : α → β} {T S : α → ℕ}
    (h : ComputableInO f encIn encMid T S) :
    ∃ c, (∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encMid (f a)) (c * (T a + 1))
        (c * (S a + 1))) ∧ ∀ a, (encMid (f a)).length ≤ c * (S a + 1) := by
  obtain ⟨c, ⟨k, State, hfin, tm, htm⟩, hl⟩ := h
  refine ⟨(2 + 3 * k) * c + (5 * k + 4) + ((2 + 6 * k) * c + 2 * k * (2 * k + 3)) + c,
    ⟨k + k, _, inferInstance, tidy false true tm, fun a => ?_⟩, fun a => ?_⟩
  · -- the space of the run is at most the smaller of the two space bounds
    set t := c * (T a + 1) with ht
    set s := min (c * (S a + 1)) (k * t + k) with hs
    have hrun : tm.ComputesInTimeAndSpace (encIn a) (encMid (f a)) t s := by
      rcases min_cases (c * (S a + 1)) (k * t + k) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [hs, he]
      exacts [htm a, space_linear (htm a)]
    refine (hrun.computesTidily_tidy Bool.false_ne_true).mono ?_ ?_
    · -- time: `2 t + 3 s + O(1)` with `s ≤ k t + k`
      have h₁ : s ≤ k * t + k := min_le_right _ _
      have e : (2 + 3 * k) * c * (T a + 1) = 2 * t + 3 * (k * t) := by rw [ht]; ring
      exact le_mul_succ (A := (2 + 3 * k) * c) (B := 5 * k + 4) (by omega) (by omega)
    · -- space: `O(s + 1)` with `s ≤ c (S + 1)`
      have h₁ : s ≤ c * (S a + 1) := min_le_left _ _
      have h₂ := Nat.mul_le_mul_left k h₁
      have e₁ : 2 * k * (3 * s + 2 * k + 3) = 6 * (k * s) + 2 * k * (2 * k + 3) := by ring
      have e₂ : (2 + 6 * k) * c * (S a + 1) = 2 * (c * (S a + 1)) + 6 * (k * (c * (S a + 1))) := by
        ring
      exact le_mul_succ (A := (2 + 6 * k) * c) (B := 2 * k * (2 * k + 3)) (by omega) (by omega)
  · exact (hl a).trans (Nat.mul_le_mul_right _ (by omega))

/-- **Composition** within time `O(T₁ a + T₂ (g a))` and space `O(S₁ a + S₂ (g a))`, through the
machine-level composition of tidy machines. -/
theorem comp {f : β → γ} {g : α → β} {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInO f encMid encOut T₂ S₂) (hg : ComputableInO g encIn encMid T₁ S₁) :
    ComputableInO (fun a => f (g a)) encIn encOut (fun a => T₁ a + T₂ (g a))
      (fun a => S₁ a + S₂ (g a)) := by
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, h₁⟩, l₁⟩ := exists_computesTidily hg
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, h₂⟩, l₂⟩ := exists_computesTidily hf
  refine ⟨6 * c₁ + c₂ + (6 * max k₁ k₂ + 20), ⟨_, _, inferInstance, tm₂.comp tm₁ true,
    fun a => (((h₁ a).comp (h₂ (g a)) true).mono ?_ ?_).computesInTimeAndSpace⟩, fun a => ?_⟩
  · -- the intermediate word is no longer than the time of `g`
    have hm := (h₁ a).length_output_le
    have := Nat.mul_le_mul_left c₁ (by omega : T₁ a + 1 ≤ T₁ a + T₂ (g a) + 1)
    have := Nat.mul_le_mul_left c₂ (by omega : T₂ (g a) + 1 ≤ T₁ a + T₂ (g a) + 1)
    have e : (6 * c₁ + c₂) * (T₁ a + T₂ (g a) + 1) =
        6 * (c₁ * (T₁ a + T₂ (g a) + 1)) + c₂ * (T₁ a + T₂ (g a) + 1) := by ring
    beta_reduce
    exact le_mul_succ (A := 6 * c₁ + c₂) (B := 6 * max k₁ k₂ + 20) (by omega) le_rfl
  · -- the intermediate word is within the space bound of `g`
    have hm := l₁ a
    have := Nat.mul_le_mul_left c₁ (by omega : S₁ a + 1 ≤ S₁ a + S₂ (g a) + 1)
    have := Nat.mul_le_mul_left c₂ (by omega : S₂ (g a) + 1 ≤ S₁ a + S₂ (g a) + 1)
    have e : (6 * c₁ + c₂) * (S₁ a + S₂ (g a) + 1) =
        6 * (c₁ * (S₁ a + S₂ (g a) + 1)) + c₂ * (S₁ a + S₂ (g a) + 1) := by ring
    beta_reduce
    exact le_mul_succ (A := 6 * c₁ + c₂) (B := 6 * max k₁ k₂ + 20) (by omega) le_rfl
  · have := Nat.mul_le_mul_left c₂ (by omega : S₂ (g a) + 1 ≤ S₁ a + S₂ (g a) + 1)
    exact (l₂ (g a)).trans (this.trans (Nat.mul_le_mul_right _ (by omega)))

/-- **Case distinction** within the bounds of the test plus those of the branch taken, through the
explicit-bound case-distinction combinator. -/
theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    {Tc Tf Tg Sc Sf Sg : α → ℕ} (hc : ComputableInO c encIn encC Tc Sc)
    (hf : ComputableInO f encIn encMid Tf Sf) (hg : ComputableInO g encIn encMid Tg Sg) :
    ComputableInO (fun x => if c x then f x else g x) encIn encMid
      (fun x => Tc x + if c x then Tf x else Tg x)
      (fun x => Sc x + if c x then Sf x else Sg x) := by
  obtain ⟨c₀, ⟨k₀, Q₀, _, tm₀, h₀⟩, -⟩ := exists_computesTidily hc
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, h₁⟩, l₁⟩ := exists_computesTidily hf
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, h₂⟩, l₂⟩ := exists_computesTidily hg
  obtain ⟨k, K, Q, _, tm, h⟩ := ComputableTidilyInTimeAndSpace.ite (encOut := encMid)
    (f := f) (g := g)
    (tc := fun a => c₀ * (Tc a + 1)) (sc := fun a => c₀ * (Sc a + 1))
    (tf := fun a => c₁ * (Tf a + 1)) (sf := fun a => c₁ * (Sf a + 1))
    (tg := fun a => c₂ * (Tg a + 1)) (sg := fun a => c₂ * (Sg a + 1))
    ⟨k₀, Q₀, inferInstance, tm₀, h₀⟩ ⟨k₁, Q₁, inferInstance, tm₁, fun x => h₁ x.1⟩
    ⟨k₂, Q₂, inferInstance, tm₂, fun x => h₂ x.1⟩
  -- each bound is a sum of two terms, each at most a constant times their sum plus one
  have key (c' d' X Y : ℕ) (u : ℕ) (hu : u ≤ c₀ * (X + 1) + c' * (Y + 1) + d')
      (hc' : c' + d' ≤ c₁ + c₂ + k) : u ≤ (c₀ + c₁ + c₂ + k) * (X + Y + 1) := by
    have := Nat.mul_le_mul_left c₀ (by omega : X + 1 ≤ X + Y + 1)
    have := Nat.mul_le_mul_left c' (by omega : Y + 1 ≤ X + Y + 1)
    have e : (c₀ + c') * (X + Y + 1) = c₀ * (X + Y + 1) + c' * (X + Y + 1) := by ring
    exact le_mul_succ (A := c₀ + c') (B := d') (by omega) (by omega)
  refine ⟨c₀ + c₁ + c₂ + k, ⟨K, Q, inferInstance, tm,
    fun x => ((h x).mono ?_ ?_).computesInTimeAndSpace⟩, fun x => ?_⟩
  · beta_reduce
    split_ifs
    · exact key c₁ k _ _ _ le_rfl (by omega)
    · exact key c₂ k _ _ _ le_rfl (by omega)
  · beta_reduce
    split_ifs
    · exact key c₁ k _ _ _ le_rfl (by omega)
    · exact key c₂ k _ _ _ le_rfl (by omega)
  · beta_reduce
    split_ifs
    · exact key c₁ 0 _ _ _ (by have := l₁ x; omega) (by omega)
    · exact key c₂ 0 _ _ _ (by have := l₂ x; omega) (by omega)

end ComputableInO

end Turing.MultiTapeTM.PlainDirect
