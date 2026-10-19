/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Chain
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bookkeeping for the potential

The potential `W = 2 s + 3 q + ∑ wt(x)` of [Mishra and Santhanam, Section 2.6][MishraSanthanam2026]
sums the weights of the unpaired parameters. Writing `State.wt S x` for the weight of `x` when it
is an unpaired parameter of `S` and `0` otherwise, the sum runs over any finite set of names
containing the parameters (`State.W_eq_sum`), so the potentials of two states compare pointwise
over a common set of names (`State.W_add_le`).

## Main definitions

* `Cslib.Circuits.Boolean.B2.State.wt`: the weight contributed by a name.

## Main results

* `Cslib.Circuits.Boolean.B2.State.W_add_le`: comparing potentials name by name.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-- The weight contributed by the name `x`: its weight if it is an unpaired parameter, and `0`
otherwise. -/
def wt (S : State n) (x : ℕ) : ℕ :=
  if x ∈ S.unpaired then weight (S.deg x) else 0

theorem wt_le_seven (S : State n) (x : ℕ) : S.wt x ≤ 7 := by
  unfold wt; split_ifs
  · exact weight_le_seven _
  · omega

theorem mem_unpaired {S : State n} {x : ℕ} : x ∈ S.unpaired ↔ x ∈ S.params ∧ ¬ S.Paired x := by
  simp [unpaired]

theorem wt_of_mem {S : State n} {x : ℕ} (hx : x ∈ S.unpaired) : S.wt x = weight (S.deg x) := by
  simp [wt, hx]

theorem wt_of_notMem {S : State n} {x : ℕ} (hx : x ∉ S.unpaired) : S.wt x = 0 := by
  simp [wt, hx]

theorem wt_of_paired {S : State n} {x : ℕ} (hx : S.Paired x) : S.wt x = 0 :=
  wt_of_notMem fun h => (mem_unpaired.1 h).2 hx

theorem wt_of_notMem_params {S : State n} {x : ℕ} (hx : x ∉ S.params) : S.wt x = 0 :=
  wt_of_notMem fun h => hx (mem_unpaired.1 h).1

theorem sum_wt (S : State n) {N : Finset ℕ} (hN : S.params ⊆ N) :
    ∑ x ∈ N, S.wt x = ∑ x ∈ S.unpaired, weight (S.deg x) := by
  have hU : S.unpaired ⊆ N := (Finset.filter_subset _ _).trans hN
  unfold wt
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hU]

theorem W_eq_sum (S : State n) {N : Finset ℕ} (hN : S.params ⊆ N) :
    S.W = 2 * S.s + 3 * S.q + ∑ x ∈ N, S.wt x := by
  rw [sum_wt S hN]; rfl

/-- Potentials compare name by name: if every name of a common set loses `loss x` and gains at
most `gain x` in weight, the sums of losses and gains bound the change of potential. -/
theorem W_add_le {S S' : State n} {N : Finset ℕ} (hN : S.params ⊆ N) (hN' : S'.params ⊆ N)
    (loss gain : ℕ → ℕ) (h : ∀ x ∈ N, S'.wt x + loss x ≤ S.wt x + gain x) :
    S'.W + 2 * S.s + 3 * S.q + ∑ x ∈ N, loss x ≤
      S.W + 2 * S'.s + 3 * S'.q + ∑ x ∈ N, gain x := by
  rw [W_eq_sum S hN, W_eq_sum S' hN']
  have := Finset.sum_le_sum h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
  omega

/-- The sum of an indicator. -/
theorem sum_ite_eq_of_mem {N : Finset ℕ} {a : ℕ} (ha : a ∈ N) (c : ℕ) :
    ∑ x ∈ N, (if x = a then c else 0) = c := by
  rw [Finset.sum_ite_eq' N a, ite_eq_left ha]

/-- Unpaired parameters of a state with the same pairs and fewer parameters were unpaired. -/
theorem mem_unpaired_of {S S' : State n} {x : ℕ} (hx : x ∈ S'.unpaired) (hp : x ∈ S.params)
    (hpairs : S.pairs ⊆ S'.pairs) : x ∈ S.unpaired :=
  mem_unpaired.2 ⟨hp, fun ⟨pr, hpr, h⟩ => (mem_unpaired.1 hx).2 ⟨pr, hpairs hpr, h⟩⟩

/-- A name keeps or lowers its weight when it stays an unpaired parameter of a state with at
least the same pairs and does not gain children. -/
theorem wt_le_of_children_subset {S S' : State n} {x : ℕ} (hparams : S'.params ⊆ S.params)
    (hpairs : S.pairs ⊆ S'.pairs) (hc : S'.children x ⊆ S.children x) : S'.wt x ≤ S.wt x := by
  by_cases hx : x ∈ S'.unpaired
  · rw [wt_of_mem hx, wt_of_mem (mem_unpaired_of hx (hparams (mem_unpaired.1 hx).1) hpairs)]
    exact weight_mono (Finset.card_le_card hc)
  · rw [wt_of_notMem hx]; omega

end State

end Cslib.Circuits.Boolean.B2
