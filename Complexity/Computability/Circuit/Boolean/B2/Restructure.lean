/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Prelim

/-!
# Preparatory operations of gate elimination

The operations of [Mishra and Santhanam, Sections 4.1 and 4.2][MishraSanthanam2026] that keep
`m`, `s` and `a` and do not increase the potential:

* moving an affine gate reading no gates into the affine system (`State.Valid.prep_move`);
* exchanging an unpaired parameter of degree at least two with an auxiliary variable of degree
  at least two depending on it (`State.Valid.prep_swap`), to turn an input of the minimal AND into
  a parameter;
* rewiring a gate reading only parameters of degree at least two (`State.Valid.prep_rewire`),
  to reroute a child of the minimal AND reading one of its inputs.

They terminate because each decreases, in lexicographic order, the number of gates, the number
of auxiliary inputs of the minimal gate, and the number of children of the minimal gate reading
one of its parameter inputs.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Valid.prep_move`, `prep_swap`, `prep_rewire`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset Cslib.BitString

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Moving affine gates -/

/-- A name larger than every equation name. -/
def freshEqn (S : State n) : ℕ :=
  S.eqns.sup id + 1

theorem freshEqn_notMem (S : State n) : S.freshEqn ∉ S.eqns := fun h => by
  have := Finset.le_sup (f := id) h
  simp only [id, freshEqn] at this
  omega

/-- Moving a movable gate into the affine system keeps `m`, `s`, `q` and `a`, does not increase
`W` and lowers the number of gates. -/
theorem Valid.prep_move {S : State n} (hS : S.Valid f) {J : ℕ} (hJ : S.Movable J) :
    ∃ S₁ : State n, S₁.Valid f ∧ S₁.gates.card < S.gates.card ∧ S₁.m = S.m ∧ S₁.s = S.s ∧
      S₁.q = S.q ∧ S₁.W ≤ S.W := by
  have hok : S.MoveOK J S.freshEqn := ⟨hJ.1, S.freshEqn_notMem, hJ.2.1, hJ.2.2⟩
  refine ⟨_, hS.moveAffine hok, by have := moveAffine_gates_card hok; omega, rfl,
    moveAffine_size hok, rfl, ?_⟩
  have hpt : ∀ u ∈ S.params, (S.moveAffine J S.freshEqn).wt u + 0 ≤ S.wt u + 0 := by
    intro u hu
    by_cases hu' : u ∈ S.unpaired
    · have hu₁ : u ∈ (S.moveAffine J S.freshEqn).unpaired := by
        rwa [unpaired_congr rfl rfl]
      rw [wt_of_mem hu₁, wt_of_mem hu']
      exact Nat.add_le_add_right (weight_mono (moveAffine_deg_le hS hok hu)) _
    · rw [wt_of_notMem (by rwa [unpaired_congr rfl rfl]), wt_of_notMem hu']
  have hW := W_add_le (S := S) (S' := S.moveAffine J S.freshEqn) le_rfl le_rfl _ _ hpt
  have hs : (S.moveAffine J S.freshEqn).s = S.s := moveAffine_size hok
  have hq : (S.moveAffine J S.freshEqn).q = S.q := rfl
  simp only [Finset.sum_const_zero] at hW
  omega

/-! ### Exchanging a parameter and an auxiliary variable -/

/-- An auxiliary variable of a valid state occurs in some equation: otherwise the affine system
would not determine it. -/
theorem Valid.exists_eqn_of_aux {S : State n} (hS : S.Valid f) {v : ℕ} (hv : v ∈ S.aux) :
    ∃ e ∈ S.eqns, v ∈ (S.eqn e).terms := by
  by_contra hne
  push Not at hne
  obtain ⟨val, -, heq⟩ := hS.wf.solvable 0
  have hvp : v ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp hv
  have heq' : S.EqnsHold (Function.update val v (!val v)) := fun e he =>
    (Equation.holds_congr fun i hi =>
      Function.update_of_ne (show i ≠ v from fun h => hne e he (h ▸ hi)) _ _).2 (heq e he)
  have := hS.wf.unique val _ (fun j hj => (Function.update_of_ne
    (show j ≠ v from fun h => hvp (h ▸ hj)) _ _).symm) heq heq' v hv
  rw [Function.update_self] at this
  cases h : val v <;> simp [h] at this

/-- The affine reparameterisation of an unpaired parameter `x` of degree at least two and an
auxiliary variable `Q` of degree at least two depending on it keeps `m`, `s`, `q`, `a` and every
child, and does not increase `W`: both weights are `7`. -/
theorem Valid.prep_swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (hx : x ∈ S.unpaired) (hxdeg : 2 ≤ S.deg x) (hQ : Q ∈ S.aux) (hQdeg : 2 ≤ S.deg Q)
    (haff : S.AffineIn Q c T) (hxT : x ∈ T) :
    (S.swap x Q c T).Valid f ∧ (S.swap x Q c T).m = S.m ∧ (S.swap x Q c T).s = S.s ∧
      (S.swap x Q c T).q = S.q ∧ (S.swap x Q c T).W ≤ S.W := by
  obtain ⟨hxp, hxu⟩ := mem_unpaired.1 hx
  have hok : S.SwapOK x Q c T := ⟨hxp, hxu, hQ, haff, hxT⟩
  have hQp : Q ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp hQ
  have hQx : Q ≠ x := fun h => hQp (h ▸ hxp)
  set S₁ := S.swap x Q c T
  have hm : S₁.m = S.m := by
    show (insert Q (S.params.erase x)).card = S.params.card
    rw [Finset.card_insert_of_notMem fun h => hQp (Finset.mem_of_mem_erase h),
      Finset.card_erase_add_one hxp]
  refine ⟨hS.swap hok, hm, rfl, rfl, ?_⟩
  have hN : S.params ⊆ insert Q S.params := Finset.subset_insert _ _
  have hN' : S₁.params ⊆ insert Q S.params :=
    Finset.insert_subset_insert _ (Finset.erase_subset _ _)
  have hpt : ∀ u ∈ insert Q S.params, S₁.wt u + (if u = x then 7 else 0) ≤
      S.wt u + (if u = Q then 7 else 0) := by
    intro u _
    by_cases hux : u = x
    · subst hux
      rw [wt_of_notMem_params (by simp [S₁, hQx.symm]), wt_of_mem hx, weight_of_two_le hxdeg,
        ite_eq_left rfl, ite_eq_right hQx.symm]
    · rw [ite_eq_right hux]
      by_cases huQ : u = Q
      · subst huQ
        rw [ite_eq_left rfl, wt_of_notMem_params hQp]
        have := S₁.wt_le_seven u
        omega
      · rw [ite_eq_right huQ]
        by_cases hu₁ : u ∈ S₁.unpaired
        · have hus : u ∈ S.unpaired := by
            obtain ⟨hup, hun⟩ := mem_unpaired.1 hu₁
            simp only [S₁, swap_params, Finset.mem_insert, Finset.mem_erase] at hup
            exact mem_unpaired.2 ⟨(hup.resolve_left huQ).2, hun⟩
          rw [wt_of_mem hu₁, wt_of_mem hus]
          rfl
        · rw [wt_of_notMem hu₁]; omega
  have hW := W_add_le hN hN' _ _ hpt
  rw [sum_ite_eq_of_mem (Finset.mem_insert_of_mem hxp),
    sum_ite_eq_of_mem (Finset.mem_insert_self _ _)] at hW
  have hs : S₁.s = S.s := rfl
  have hq : S₁.q = S.q := rfl
  omega

/-! ### Rewiring a gate -/

/-- Rewiring a gate to a gate reading only parameters of degree at least two keeps `m`, `s`, `q`
and `a` and does not increase `W`: only those parameters may gain a child, and their weight is
already `7`. -/
theorem Valid.prep_rewire {S : State n} (hS : S.Valid f) {J : ℕ} {g : Gate}
    (h : S.RewireOK J g) (hdeg : ∀ t, g.Reads t → t ∈ S.unpaired → 2 ≤ S.deg t) :
    (S.rewire J g).Valid f ∧ (S.rewire J g).m = S.m ∧ (S.rewire J g).s = S.s ∧
      (S.rewire J g).q = S.q ∧ (S.rewire J g).W ≤ S.W := by
  refine ⟨hS.rewire h, rfl, rfl, rfl, ?_⟩
  have hpt : ∀ u ∈ S.params, (S.rewire J g).wt u + 0 ≤ S.wt u + 0 := by
    intro u hu
    by_cases hu' : u ∈ S.unpaired
    · have hu₁ : u ∈ (S.rewire J g).unpaired := by rwa [unpaired_congr rfl rfl]
      rw [wt_of_mem hu₁, wt_of_mem hu']
      by_cases hgu : g.Reads u
      · rw [weight_of_two_le (hdeg u hgu hu')]
        have := weight_le_seven ((S.rewire J g).deg u)
        omega
      · refine Nat.add_le_add_right (weight_mono (Finset.card_le_card fun w hw => ?_)) _
        rcases w with K | e
        · rw [inl_mem_children_rewire] at hw
          obtain ⟨hK, hr⟩ := hw
          by_cases hKJ : K = J
          · rw [ite_eq_left hKJ] at hr; exact absurd hr hgu
          · rw [ite_eq_right hKJ] at hr
            exact (SemiCircuit.inl_mem_children _).2 ⟨hK, hr⟩
        · rwa [inr_mem_children_rewire] at hw
    · rw [wt_of_notMem (by rwa [unpaired_congr rfl rfl]), wt_of_notMem hu']
  have hW := W_add_le (S := S) (S' := S.rewire J g) le_rfl le_rfl _ _ hpt
  have hs : (S.rewire J g).s = S.s := rfl
  have hq : (S.rewire J g).q = S.q := rfl
  simp only [Finset.sum_const_zero] at hW
  omega

end State

end Cslib.Circuits.Boolean.B2
