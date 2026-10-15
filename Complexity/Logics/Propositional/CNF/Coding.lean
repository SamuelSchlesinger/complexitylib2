/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities

/-!
# The satisfiability coding lemma

The coding lemma of Paturi, Pudlák and Zane [PaturiPudlakZane1999], with exact sums over all
orders of the variables in place of probabilities. Fix a formula `φ` in conjunctive normal form
over `N` variables and an order `σ` of the variables. A variable `v` is *forced* on a solution `x`
(`CNF.forced`) when some clause contains the literal of `v` true under `x` and all its other
literals are on earlier variables and false under `x`. The words agreeing with a solution `x`
off its forced variables are disjoint for distinct solutions: at the first variable where two
solutions differ, a clause forcing it in one of them is false under the other
(`CNF.disjoint_agreeOffForced`). Hence `∑ₓ 2 ^ |forced σ x| ≤ 2 ^ N` for every order
(`CNF.sum_two_pow_card_forced_le`), and by the inequality of arithmetic and geometric means the
same holds with the average number of forced variables over all orders in the exponent
(`CNF.sum_two_rpow_average_card_forced_le`).

If every clause has at most `k` literals and `x` is isolated in direction `i` (flipping bit `i`
of `x` gives no solution), some clause is *critical* for `i` (`CNF.exists_critical`), and `i` is
forced whenever it comes last among the variables of that clause, for at least a `1 / k` fraction
of the orders (`CNF.factorial_le_mul_card_filter_mem_forced`). Hence
`∑ₓ 2 ^ (ι(x) / k) ≤ 2 ^ N`, where `ι(x)` is the number of directions in which `x` is isolated
(`CNF.sum_two_rpow_card_isolated_div_le`), and a `k`-CNF has at most `2 ^ ((1 - 1 / k) N)`
solutions isolated in every direction (`CNF.card_isolated_mul_two_rpow_le`).

## Main definitions

* `Cslib.Logic.PL.CNF.forced`: the variables forced on a solution for an order of the variables.

## Main results

* `Cslib.Logic.PL.CNF.sum_two_pow_card_forced_le`: the coding bound for one order.
* `Cslib.Logic.PL.CNF.sum_two_rpow_average_card_forced_le`: the coding lemma.
* `Cslib.Logic.PL.CNF.sum_two_rpow_card_isolated_div_le`: the coding lemma for `k`-CNFs.
* `Cslib.Logic.PL.CNF.card_isolated_mul_two_rpow_le`: few isolated solutions.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability coding lemma*][PaturiPudlakZane1999]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset

variable {N : ℕ}

namespace CNF

/-- The clause `c` forces `v` on `x` for the order `σ`: it contains the literal of `v` true under
`x`, and all its other literals are on variables before `v` (in the order `σ`) and false under
`x`. This is the deletion rule of Paturi, Pudlák and Zane: such a clause is critical for `v` at `x`
and `v` comes last among its variables, so the decoder meets it as a unit clause on `v`. A clause
also containing the literal of `v` false under `x` forces nothing, as the decoder would not see a
unit clause there; the definition rules it out, since that literal would need `σ v < σ v`. -/
def Forces (σ : Equiv.Perm (Fin N)) (x : BitString N) (c : Clause (Fin N)) (v : Fin N) : Prop :=
  (v, x v) ∈ c ∧ ∀ l ∈ c, l ≠ (v, x v) → σ l.1 < σ v ∧ x l.1 ≠ l.2

instance (σ : Equiv.Perm (Fin N)) (x : BitString N) (c : Clause (Fin N)) (v : Fin N) :
    Decidable (Forces σ x c v) :=
  inferInstanceAs (Decidable (_ ∧ ∀ l ∈ c, _))

/-- The variables forced on `x` for the order `σ`: those forced by some clause. -/
def forced (φ : CNF (Fin N)) (σ : Equiv.Perm (Fin N)) (x : BitString N) : Finset (Fin N) :=
  univ.filter fun v => ∃ c ∈ φ, Forces σ x c v

variable {φ : CNF (Fin N)} {σ : Equiv.Perm (Fin N)}

@[simp] theorem mem_forced {φ : CNF (Fin N)} {σ : Equiv.Perm (Fin N)} {x : BitString N}
    {v : Fin N} : v ∈ φ.forced σ x ↔ ∃ c ∈ φ, Forces σ x c v := by
  simp [forced]

/-- The words agreeing with `x` outside the variables forced on `x`. -/
def agreeOffForced (φ : CNF (Fin N)) (σ : Equiv.Perm (Fin N)) (x : BitString N) :
    Finset (BitString N) :=
  univ.filter fun y => ∀ v ∉ φ.forced σ x, y v = x v

/-- **The words agreeing with distinct solutions off their forced variables are disjoint**: at the
first variable, in the order `σ`, where two solutions differ, one of them is forced, and the clause
forcing it is false under the other solution. -/
theorem disjoint_agreeOffForced {x x' : BitString N} (hx : φ.eval x = true) (hx' : φ.eval x' = true)
    (hne : x ≠ x') : Disjoint (φ.agreeOffForced σ x) (φ.agreeOffForced σ x') := by
  refine disjoint_left.2 fun y hy hy' => ?_
  -- the first variable where `x` and `x'` differ
  have hdiff : (univ.filter fun v => x v ≠ x' v).Nonempty := by
    obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
    exact ⟨v, mem_filter.2 ⟨mem_univ v, hv⟩⟩
  obtain ⟨v, hv, hmin⟩ := exists_min_image _ (fun v => σ v) hdiff
  have hxv : x v ≠ x' v := (mem_filter.1 hv).2
  have hagree : ∀ u, σ u < σ v → x u = x' u := fun u hu => by
    by_contra h
    exact absurd (hmin u (mem_filter.2 ⟨mem_univ u, h⟩)) (not_le.2 hu)
  -- `v` is forced on one of them, by a clause false under the other
  have key : ∀ {a b : BitString N}, φ.eval b = true → a v ≠ b v →
      (∀ u, σ u < σ v → a u = b u) → v ∉ φ.forced σ a := by
    intro a b hb hab hagr hforced
    obtain ⟨c, hc, hvc, hrest⟩ := (mem_filter.1 hforced).2
    obtain ⟨l, hl, hle⟩ := (Clause.eval_eq_true_iff b c).1 ((CNF.eval_eq_true_iff b φ).1 hb c hc)
    obtain ⟨u, e⟩ := l
    by_cases hl' : (u, e) = (v, a v)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl'
      exact hab hle.symm
    · obtain ⟨hlt, hne'⟩ := hrest (u, e) hl hl'
      exact hne' ((hagr u hlt).trans hle)
  by_cases hfx : v ∈ φ.forced σ x
  · exact key hx' hxv hagree hfx
  · by_cases hfx' : v ∈ φ.forced σ x'
    · exact key hx (Ne.symm hxv) (fun u hu => (hagree u hu).symm) hfx'
    · exact hxv (((mem_filter.1 hy).2 v hfx).symm.trans ((mem_filter.1 hy').2 v hfx'))

/-- `2 ^ |forced σ x|` words agree with `x` off its forced variables. -/
theorem card_agreeOffForced (x : BitString N) :
    (φ.agreeOffForced σ x).card = 2 ^ (φ.forced σ x).card := by
  have h : (φ.agreeOffForced σ x).card =
      Fintype.card (∀ v, {b : Bool // v ∉ φ.forced σ x → b = x v}) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr ((Equiv.subtypeEquivRight fun y => by simp [agreeOffForced]).trans
      Equiv.subtypePiEquivPi)
  rw [h, Fintype.card_pi]
  have hv (v : Fin N) : Fintype.card {b : Bool // v ∉ φ.forced σ x → b = x v} =
      if v ∈ φ.forced σ x then 2 else 1 := by
    by_cases hvF : v ∈ φ.forced σ x
    · simp [hvF]
    · simp only [hvF, not_false_eq_true, forall_const, ↓reduceIte]
      exact Fintype.card_subtype_eq (x v)
  simp only [hv]
  rw [prod_ite, prod_const, prod_const_one, mul_one, filter_mem_eq_inter, univ_inter]

/-- **The coding bound for one order**: the solutions `x` of `φ` satisfy
`∑ₓ 2 ^ |forced σ x| ≤ 2 ^ N`. -/
theorem sum_two_pow_card_forced_le (φ : CNF (Fin N)) (σ : Equiv.Perm (Fin N)) :
    ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true, 2 ^ (φ.forced σ x).card ≤ 2 ^ N := by
  calc ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true, 2 ^ (φ.forced σ x).card
      = ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true, (φ.agreeOffForced σ x).card :=
        sum_congr rfl fun x _ => (card_agreeOffForced x).symm
    _ = ((univ.filter fun x : BitString N => φ.eval x = true).biUnion (φ.agreeOffForced σ)).card :=
        (card_biUnion fun x hx x' hx' hne => disjoint_agreeOffForced (mem_filter.1 hx).2
          (mem_filter.1 hx').2 hne).symm
    _ ≤ (univ : Finset (BitString N)).card := card_le_univ _
    _ = 2 ^ N := by simp

/-! ### Isolated directions are forced often -/

/-- At least a `1 / #S` fraction of the orders put a given `i ∈ S` last among `S`: every order puts
some element of `S` last, and composing with the transposition of `i` and `j` moves the orders
putting `j` last to orders putting `i` last. -/
theorem factorial_le_card_mul_card_filter_le {S : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) :
    N.factorial ≤ S.card * (univ.filter fun σ : Equiv.Perm (Fin N) => ∀ u ∈ S, σ u ≤ σ i).card := by
  set M : Fin N → Finset (Equiv.Perm (Fin N)) := fun j =>
    univ.filter fun σ => ∀ u ∈ S, σ u ≤ σ j
  have hcover : (univ : Finset (Equiv.Perm (Fin N))) ⊆ S.biUnion M := fun σ _ => by
    obtain ⟨j, hj, hmax⟩ := exists_max_image S (fun u => σ u) ⟨i, hi⟩
    exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨mem_univ σ, hmax⟩⟩
  have hle : ∀ j ∈ S, (M j).card ≤ (M i).card := fun j hj => by
    refine card_le_card_of_injOn (fun σ => σ * Equiv.swap i j) (fun σ hσ => ?_)
      (fun σ _ τ _ h => mul_right_cancel h)
    refine mem_filter.2 ⟨mem_univ _, fun u hu => ?_⟩
    have hmax := (mem_filter.1 hσ).2
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
    refine hmax _ ?_
    rcases eq_or_ne u i with rfl | hui
    · rw [Equiv.swap_apply_left]; exact hj
    rcases eq_or_ne u j with rfl | huj
    · rw [Equiv.swap_apply_right]; exact hi
    rw [Equiv.swap_apply_of_ne_of_ne hui huj]
    exact hu
  calc N.factorial = (univ : Finset (Equiv.Perm (Fin N))).card := by
        rw [card_univ, Fintype.card_perm, Fintype.card_fin]
    _ ≤ (S.biUnion M).card := card_le_card hcover
    _ ≤ ∑ j ∈ S, (M j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ S, (M i).card := sum_le_sum hle
    _ = S.card * (M i).card := by rw [sum_const, Nat.nsmul_eq_mul]

/-- A direction `i` in which a solution `x` is isolated has a *critical clause*: it contains the
literal of `i` true under `x`, and all its other literals are on other variables and false under
`x`. -/
theorem exists_critical {x : BitString N} {i : Fin N} (hx : φ.eval x = true)
    (hi : φ.eval (Function.update x i (!x i)) = false) :
    ∃ c ∈ φ, (i, x i) ∈ c ∧ ∀ l ∈ c, l ≠ (i, x i) → l.1 ≠ i ∧ x l.1 ≠ l.2 := by
  obtain ⟨c, hc, hcf⟩ : ∃ c ∈ φ, c.eval (Function.update x i (!x i)) = false := by
    by_contra h
    push Not at h
    rw [← Bool.not_eq_true, CNF.eval_eq_true_iff] at hi
    exact hi fun c hc => Bool.eq_true_of_not_eq_false (h c hc)
  have hfalse : ∀ l ∈ c, Function.update x i (!x i) l.1 ≠ l.2 := fun l hl h => by
    have := (Clause.eval_eq_true_iff _ c).2 ⟨l, hl, h⟩
    rw [hcf] at this
    exact Bool.false_ne_true this
  obtain ⟨⟨u, e⟩, hl, hle⟩ := (Clause.eval_eq_true_iff x c).1 ((CNF.eval_eq_true_iff x φ).1 hx c hc)
  -- the true literal is on `i`
  have hu : u = i := by
    by_contra hui
    exact hfalse _ hl (by rw [Function.update_of_ne hui]; exact hle)
  subst hu
  refine ⟨c, hc, hle ▸ hl, fun l hl' hne => ?_⟩
  have hli : l.1 ≠ u := by
    intro hli
    apply hfalse l hl'
    rw [hli, Function.update_self]
    -- `l = (u, !x u)`, as `l ≠ (u, x u)`
    obtain ⟨v, b⟩ := l
    simp only at hli
    subst hli
    cases b <;> cases hxv : x v <;> simp_all
  exact ⟨hli, fun h => hfalse l hl' (by rw [Function.update_of_ne hli]; exact h)⟩

/-- **Isolated directions are forced often.** If every clause of `φ` has at most `k` literals,
every direction `i` in which a solution `x` is isolated is forced for at least a `1 / k` fraction
of the orders. -/
theorem factorial_le_mul_card_filter_mem_forced {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {x : BitString N} {i : Fin N} (hx : φ.eval x = true)
    (hi : φ.eval (Function.update x i (!x i)) = false) :
    N.factorial ≤ k * (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ φ.forced σ x).card := by
  obtain ⟨c, hc, hic, hrest⟩ := exists_critical hx hi
  set S := (c.map Prod.fst).toFinset
  have hiS : i ∈ S := List.mem_toFinset.2 (List.mem_map.2 ⟨_, hic, rfl⟩)
  have hS : S.card ≤ k := (List.toFinset_card_le _).trans ((List.length_map _).trans_le (hk c hc))
  refine (factorial_le_card_mul_card_filter_le hiS).trans (Nat.mul_le_mul hS (card_le_card ?_))
  intro σ hσ
  refine mem_filter.2 ⟨mem_univ σ, mem_filter.2 ⟨mem_univ i, c, hc, hic, fun l hl hne => ?_⟩⟩
  obtain ⟨hli, hxl⟩ := hrest l hl hne
  have hle := (mem_filter.1 hσ).2 l.1 (List.mem_toFinset.2 (List.mem_map.2 ⟨l, hl, rfl⟩))
  exact ⟨lt_of_le_of_ne hle fun h => hli (σ.injective h), hxl⟩

/-! ### Averaging over the orders -/

/-- **The coding lemma** [Paturi, Pudlák and Zane, Lemma 2 and Fact 3][PaturiPudlakZane1999]: with
`E(x)` the average, over all `N!` orders, of the number of variables forced on a solution `x`, the
solutions satisfy `∑ₓ 2 ^ E(x) ≤ 2 ^ N`. -/
theorem sum_two_rpow_average_card_forced_le (φ : CNF (Fin N)) :
    ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
        (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ)) / N.factorial) ≤
      2 ^ N := by
  have hF : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hP : ((univ : Finset (Equiv.Perm (Fin N))).card : ℝ) = N.factorial := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
  -- `2 ^ (average) ≤ average of 2 ^ ·`, by the weighted inequality of arithmetic and geometric
  -- means
  have hamgm (x : BitString N) :
      (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ)) / N.factorial) ≤
        ∑ σ : Equiv.Perm (Fin N), 1 / N.factorial * (2 : ℝ) ^ (φ.forced σ x).card := by
    have h := Real.geom_mean_le_arith_mean_weighted (s := univ) (fun _ => 1 / (N.factorial : ℝ))
      (fun σ : Equiv.Perm (Fin N) => (2 : ℝ) ^ (φ.forced σ x).card) (fun _ _ => by positivity)
      (by rw [sum_const, nsmul_eq_mul, hP]; field_simp) (fun _ _ => by positivity)
    refine le_trans (le_of_eq ?_) h
    rw [div_eq_mul_one_div, sum_mul, Real.rpow_sum_of_pos (by norm_num)]
    refine prod_congr rfl fun σ _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  calc ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
        (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ)) / N.factorial)
      ≤ ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
          ∑ σ : Equiv.Perm (Fin N), 1 / N.factorial * (2 : ℝ) ^ (φ.forced σ x).card :=
        sum_le_sum fun x _ => hamgm x
    _ = ∑ σ : Equiv.Perm (Fin N), 1 / N.factorial *
          ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
            (2 : ℝ) ^ (φ.forced σ x).card := by
        rw [sum_comm]
        simp only [mul_sum]
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), 1 / N.factorial * (2 : ℝ) ^ N := by
        refine sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast sum_two_pow_card_forced_le φ σ
    _ = 2 ^ N := by
        rw [sum_const, nsmul_eq_mul, hP]
        field_simp

/-- **The coding lemma for formulas of width `k`**
[Paturi, Pudlák and Zane, Lemma 2][PaturiPudlakZane1999]: if every clause has at most `k ≥ 1`
literals, the solutions `x` satisfy `∑ₓ 2 ^ (ι(x) / k) ≤ 2 ^ N`, where `ι(x)` is the number of
directions in which `x` is isolated. -/
theorem sum_two_rpow_card_isolated_div_le {k : ℕ} (hk1 : 1 ≤ k) (hk : ∀ c ∈ φ, c.length ≤ k) :
    ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
        (2 : ℝ) ^ (((univ.filter fun i => φ.eval (Function.update x i (!x i)) = false).card : ℝ) /
          k) ≤ 2 ^ N := by
  refine le_trans (sum_le_sum fun x hx => ?_) (sum_two_rpow_average_card_forced_le φ)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hx' := (mem_filter.1 hx).2
  -- `ι(x) N! ≤ k ∑_σ |forced σ x|`
  have hcount : (univ.filter fun i => φ.eval (Function.update x i (!x i)) = false).card *
      N.factorial ≤ k * ∑ σ : Equiv.Perm (Fin N), (φ.forced σ x).card := by
    calc (univ.filter fun i => φ.eval (Function.update x i (!x i)) = false).card * N.factorial
        = ∑ i ∈ univ.filter fun i => φ.eval (Function.update x i (!x i)) = false,
            N.factorial := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ univ.filter fun i => φ.eval (Function.update x i (!x i)) = false,
            k * (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ φ.forced σ x).card :=
          sum_le_sum fun i hi => factorial_le_mul_card_filter_mem_forced hk hx' (mem_filter.1 hi).2
      _ ≤ k * ∑ i : Fin N, (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ φ.forced σ x).card := by
          rw [← mul_sum]
          exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset (filter_subset _ _))
      _ = k * ∑ σ : Equiv.Perm (Fin N), (φ.forced σ x).card := by
          congr 1
          simp only [card_eq_sum_ones, sum_filter]
          rw [sum_comm]
          simp [-mem_forced]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hF : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_div_iff₀ hkR hF]
  have : ((univ.filter fun i => φ.eval (Function.update x i (!x i)) = false).card : ℝ) *
      N.factorial ≤ k * ∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ) := by
    exact_mod_cast hcount
  linarith

/-- **Few isolated solutions** [Paturi, Pudlák and Zane, Lemma 4][PaturiPudlakZane1999]: a formula
whose clauses have at most `k ≥ 1` literals has at most `2 ^ ((1 - 1 / k) N)` solutions isolated in
every direction. -/
theorem card_isolated_mul_two_rpow_le {k : ℕ} (hk1 : 1 ≤ k) (hk : ∀ c ∈ φ, c.length ≤ k) :
    ((univ.filter fun x : BitString N => φ.eval x = true ∧
        ∀ i, φ.eval (Function.update x i (!x i)) = false).card : ℝ) * 2 ^ ((N : ℝ) / k) ≤
      2 ^ N := by
  refine le_trans ?_ (sum_two_rpow_card_isolated_div_le hk1 hk)
  rw [← nsmul_eq_mul, ← sum_const]
  refine (sum_le_sum_of_subset_of_nonneg (fun x hx => mem_filter.2 ⟨mem_univ x,
    (mem_filter.1 hx).2.1⟩) fun _ _ _ => by positivity).trans' (le_of_eq (sum_congr rfl
      fun x hx => ?_))
  congr 2
  rw [filter_true_of_mem fun i _ => (mem_filter.1 hx).2.2 i, card_univ, Fintype.card_fin]

end CNF

end Cslib.Logic.PL
