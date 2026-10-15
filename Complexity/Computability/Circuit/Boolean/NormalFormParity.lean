/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Logics.Propositional.DNF
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Normal forms of parity are large

A Boolean function is *sensitive everywhere* when flipping any input bit of any input flips
its value; parity is (`parity_update_not`). A term of a formula in disjunctive normal form
computing such a function that holds somewhere mentions every variable, since flipping an
unmentioned variable would keep the term true and flip the function; so it holds at only one
input. Hence such a formula has at least as many terms as the function has true inputs
(`DNF.card_filter_le_length_of_sensitive`), and dually a formula in conjunctive normal form has at
least as many clauses as false inputs. For parity of `n ≥ 1` bits both are `2 ^ (n - 1)`
(`DNF.two_pow_le_length_of_eval_eq_parity`, `CNF.two_pow_le_length_of_eval_eq_parity`).

## Main results

* `Cslib.Logic.PL.DNF.card_filter_le_length_of_sensitive`: formulas in disjunctive normal form for
  functions sensitive everywhere.
* `Cslib.Logic.PL.DNF.two_pow_le_length_of_eval_eq_parity`,
  `Cslib.Logic.PL.CNF.two_pow_le_length_of_eval_eq_parity`: normal forms of parity have at least
  `2 ^ (n - 1)` terms or clauses.
-/

@[expose] public section

namespace Cslib

open Finset

variable {n : ℕ}

/-- Flipping any bit flips the parity. -/
theorem parity_update_not (x : BitString n) (i : Fin n) :
    parity n (Function.update x i (!x i)) = !parity n x :=
  parityOn_update_not (mem_univ i) x

/-- Parity of `n ≥ 1` bits is true on half of the inputs. -/
theorem card_filter_parity (hn : 1 ≤ n) :
    #{x : BitString n | parity n x = true} = 2 ^ (n - 1) := by
  -- flipping the first bit exchanges the true and the false inputs
  set i : Fin n := ⟨0, hn⟩
  let e : BitString n ≃ BitString n := ⟨fun x => Function.update x i (!x i),
    fun x => Function.update x i (!x i), fun x => by simp, fun x => by simp⟩
  have hswap :
      #{x : BitString n | parity n x = true} = #{x : BitString n | parity n x = false} := by
    refine card_nbij' e e.symm (fun x hx => ?_) (fun x hx => ?_) (fun x _ => e.left_inv x)
      (fun x _ => e.right_inv x)
    · simpa [e, parity_update_not] using hx
    · simpa [e, parity_update_not] using hx
  have htotal := card_filter_add_card_filter_not (s := (univ : Finset (BitString n)))
    (fun x => parity n x = true)
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at htotal
  rw [← hswap] at htotal
  have : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  omega

namespace Logic.PL

/-- **Formulas in disjunctive normal form for functions sensitive everywhere** have at least as many
terms as the function has true inputs. -/
theorem DNF.card_filter_le_length_of_sensitive {g : BitString n → Bool}
    (hg : ∀ x i, g (Function.update x i (!x i)) = !g x) {D : DNF (Fin n)}
    (hD : ∀ x, D.eval x = g x) : #{x : BitString n | g x = true} ≤ D.length := by
  classical
  -- a true input chooses a term holding there
  have hchoose : ∀ x ∈ ({x : BitString n | g x = true} : Finset _), ∃ t ∈ D, t.eval x = true :=
    fun x hx => (DNF.eval_eq_true_iff x D).1 ((hD x).trans (mem_filter.1 hx).2)
  choose! T hT hTx using hchoose
  -- such a term mentions every variable, so it determines the input
  have hall : ∀ x ∈ ({x : BitString n | g x = true} : Finset _), ∀ i : Fin n,
      ∃ b, (i, b) ∈ T x := fun x hx i => by
    by_contra h'
    have h := not_exists.1 h'
    have hflip : (T x).eval (Function.update x i (!x i)) = true := by
      have hx' := (Term.eval_eq_true_iff x _).1 (hTx x hx)
      refine (Term.eval_eq_true_iff _ _).2 fun l hl => ?_
      have hli : l.1 ≠ i := fun hli => h l.2 (hli ▸ hl)
      rw [Function.update_of_ne hli]
      exact hx' l hl
    have h1 := (hD _).symm.trans ((DNF.eval_eq_true_iff _ D).2 ⟨T x, hT x hx, hflip⟩)
    rw [hg, (mem_filter.1 hx).2] at h1
    exact Bool.false_ne_true h1
  have hinj : Set.InjOn T ({x : BitString n | g x = true} : Finset _) := by
    intro x hx y hy hxy
    funext i
    obtain ⟨b, hb⟩ := hall x hx i
    have h₁ := (Term.eval_eq_true_iff x _).1 (hTx x hx) _ hb
    have h₂ := (Term.eval_eq_true_iff y _).1 (hTx y hy) _ (hxy ▸ hb)
    exact h₁.trans h₂.symm
  calc #{x : BitString n | g x = true}
      = #(({x : BitString n | g x = true} : Finset _).image T) := (card_image_of_injOn hinj).symm
    _ ≤ #D.toFinset := card_le_card fun t ht => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 ht
        exact List.mem_toFinset.2 (hT x hx)
    _ ≤ D.length := List.toFinset_card_le D

/-- **Formulas in disjunctive normal form for parity** of `n ≥ 1` bits have at least
`2 ^ (n - 1)` terms. -/
theorem DNF.two_pow_le_length_of_eval_eq_parity (hn : 1 ≤ n) {D : DNF (Fin n)}
    (hD : ∀ x, D.eval x = parity n x) : 2 ^ (n - 1) ≤ D.length :=
  card_filter_parity hn ▸ DNF.card_filter_le_length_of_sensitive parity_update_not hD

/-- **Formulas in conjunctive normal form for parity** of `n ≥ 1` bits have at least
`2 ^ (n - 1)` clauses: the negation of one is a formula in disjunctive normal form for the
negation of parity, which is sensitive everywhere and true on half of the inputs. -/
theorem CNF.two_pow_le_length_of_eval_eq_parity (hn : 1 ≤ n) {φ : CNF (Fin n)}
    (hφ : ∀ x, φ.eval x = parity n x) : 2 ^ (n - 1) ≤ φ.length := by
  have h := DNF.card_filter_le_length_of_sensitive (g := fun x => !parity n x)
    (fun x i => by simp [parity_update_not]) (D := φ.negate) fun x => by
      rw [CNF.eval_negate, hφ]
  rw [CNF.negate, List.length_map] at h
  refine le_trans (le_of_eq ?_) h
  rw [← card_filter_parity hn]
  -- the false inputs are as many as the true inputs
  refine card_nbij' (fun x => Function.update x ⟨0, hn⟩ (!x ⟨0, hn⟩))
    (fun x => Function.update x ⟨0, hn⟩ (!x ⟨0, hn⟩)) (fun x hx => ?_) (fun x hx => ?_)
    (fun x _ => by simp) (fun x _ => by simp)
  · simpa [parity_update_not] using hx
  · simpa [parity_update_not] using hx

end Logic.PL

end Cslib
