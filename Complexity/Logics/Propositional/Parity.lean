/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Logics.Propositional.DNF
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Normal forms for parity

An input `x` of a Boolean function `g` is an *isolated true input* when `g x` is true and `g` is
false at every neighbour of `x`. A term of a formula in disjunctive normal form computing `g` that
holds at an isolated true input mentions every variable, since flipping an unmentioned variable
would keep it true; so it holds at no other input. Hence such a formula has at least as many terms
as `g` has isolated true inputs (`DNF.card_filter_isolated_le_length`), and dually a formula in
conjunctive normal form has at least as many clauses as isolated false inputs. Every input is
isolated for parity, so its normal forms on `n ≥ 1` bits have at least `2 ^ (n - 1)` terms or
clauses (`DNF.two_pow_le_length_of_eval_eq_parity`, `CNF.two_pow_le_length_of_eval_eq_parity`).

ORs of formulas in conjunctive normal form for parity, of depth three, are in
`Parity/DepthThree.lean`.

## Main results

* `Cslib.Logic.PL.DNF.card_filter_isolated_le_length`,
  `Cslib.Logic.PL.CNF.card_filter_isolated_le_length`: normal forms have a term or clause per
  isolated input.
* `Cslib.Logic.PL.DNF.two_pow_le_length_of_eval_eq_parity`,
  `Cslib.Logic.PL.CNF.two_pow_le_length_of_eval_eq_parity`: normal forms of parity have at least
  `2 ^ (n - 1)` terms or clauses.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Function

variable {n : ℕ}

/-- **A formula in disjunctive normal form has a term per isolated true input** of the function it
computes. -/
theorem DNF.card_filter_isolated_le_length {g : BitString n → Bool} {D : DNF (Fin n)}
    (hD : ∀ x, D.eval x = g x) :
    #{x : BitString n | g x = true ∧ ∀ i, g (update x i !x i) = false} ≤ D.length := by
  set S : Finset (BitString n) := {x | g x = true ∧ ∀ i, g (update x i !x i) = false}
  -- an isolated true input chooses a term holding there
  have hchoose : ∀ x ∈ S, ∃ t ∈ D, t.eval x = true :=
    fun x hx => (DNF.eval_eq_true_iff x D).1 ((hD x).trans (mem_filter.1 hx).2.1)
  choose! T hT hTx using hchoose
  -- such a term mentions every variable, so it determines the input
  have hall : ∀ x ∈ S, ∀ i : Fin n, ∃ b, (i, b) ∈ T x := fun x hx i => by
    by_contra h'
    have h := not_exists.1 h'
    have hflip : (T x).eval (update x i !x i) = true := by
      have hx' := (Term.eval_eq_true_iff x _).1 (hTx x hx)
      refine (Term.eval_eq_true_iff _ _).2 fun l hl => ?_
      have hli : l.1 ≠ i := fun hli => h l.2 (hli ▸ hl)
      rw [update_of_ne hli]
      exact hx' l hl
    have h1 := (hD _).symm.trans ((DNF.eval_eq_true_iff _ D).2 ⟨T x, hT x hx, hflip⟩)
    rw [(mem_filter.1 hx).2.2 i] at h1
    exact Bool.false_ne_true h1
  have hinj : Set.InjOn T S := by
    intro x hx y hy hxy
    funext i
    obtain ⟨b, hb⟩ := hall x hx i
    have h₁ := (Term.eval_eq_true_iff x _).1 (hTx x hx) _ hb
    have h₂ := (Term.eval_eq_true_iff y _).1 (hTx y hy) _ (hxy ▸ hb)
    exact h₁.trans h₂.symm
  calc #S
      = #(S.image T) := (card_image_of_injOn hinj).symm
    _ ≤ #D.toFinset := card_le_card fun t ht => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 ht
        exact List.mem_toFinset.2 (hT x hx)
    _ ≤ D.length := List.toFinset_card_le D

/-- **A formula in conjunctive normal form has a clause per isolated false input** of the function
it computes: its negation is a formula in disjunctive normal form for the negated function. -/
theorem CNF.card_filter_isolated_le_length {g : BitString n → Bool} {φ : CNF (Fin n)}
    (hφ : ∀ x, φ.eval x = g x) :
    #{x : BitString n | g x = false ∧ ∀ i, g (update x i !x i) = true} ≤ φ.length := by
  have h := DNF.card_filter_isolated_le_length (g := fun x => !g x) (D := φ.negate) fun x => by
    rw [CNF.eval_negate, hφ]
  rw [CNF.negate, List.length_map] at h
  simpa using h

/-- **Formulas in disjunctive normal form for parity** of `n ≥ 1` bits have at least
`2 ^ (n - 1)` terms. -/
theorem DNF.two_pow_le_length_of_eval_eq_parity (hn : 1 ≤ n) {D : DNF (Fin n)}
    (hD : ∀ x, D.eval x = parity n x) : 2 ^ (n - 1) ≤ D.length := by
  refine le_of_eq_of_le ?_ (DNF.card_filter_isolated_le_length hD)
  rw [← card_filter_parity_eq_true hn]
  congr 1
  ext x
  simp +contextual [parity_update_not]

/-- **Formulas in conjunctive normal form for parity** of `n ≥ 1` bits have at least
`2 ^ (n - 1)` clauses. -/
theorem CNF.two_pow_le_length_of_eval_eq_parity (hn : 1 ≤ n) {φ : CNF (Fin n)}
    (hφ : ∀ x, φ.eval x = parity n x) : 2 ^ (n - 1) ≤ φ.length := by
  refine le_of_eq_of_le ?_ (CNF.card_filter_isolated_le_length hφ)
  rw [← card_filter_parity_eq_false hn]
  congr 1
  ext x
  simp +contextual [parity_update_not]

end Cslib.Logic.PL
