/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Parity
public import Complexity.Logics.Propositional.CNF.Coding
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators

/-!
# Depth-three formulas for parity

Each formula in an OR of formulas in conjunctive normal form computing a function `g` has its
solutions among the true inputs of `g`, so an isolated true input of `g` is an isolated solution of
one of the formulas. The satisfiability coding lemma bounds those, and so the formulas in an OR for
parity, whose `2 ^ (n - 1)` true inputs are all isolated.

*Bottom fan-in `k`.* A formula of width `k` has at most `2 ^ ((1 - 1 / k) n)` isolated solutions,
so an OR of such formulas needs a formula per `2 ^ ((1 - 1 / k) n)` isolated true inputs
(`CNF.card_filter_isolated_mul_two_rpow_le`), as in the proof of
[Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]. For parity this is `2 ^ (n / k - 1)`
(`CNF.two_rpow_le_length_of_any_eval_eq_parity`), and the bound is attained when `k` divides `n`:
split the variables into blocks of `k` and take one formula for each pattern of block parities
with odd total (`CNF.exists_any_eval_eq_parity`), as in the example after
[Paturi, Pudlák and Zane, Lemma 4][PaturiPudlakZane1999].

*Unbounded bottom fan-in* [Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]. Weigh a
solution `x` of a formula by `w(x) = ∑ᵢ 1 / ℓᵢ`, where `ℓᵢ` is the number of variables of a
shortest clause critical for the direction `i` at `x`. At most `2 ^ (n - μ)` solutions of a formula
have weight at least `μ` (`CNF.card_filter_le_sum_inv_critWidth_mul_two_rpow_le`). A clause with
`ℓ` variables is critical for at most `ℓ 2 ^ (n - ℓ)` pairs of an input and a direction
(`CNF.card_filter_critical_prod_le`), and `t ↦ t 2 ^ (1 / t)` is convex and decreasing up to
`log 2`, so the shortest critical clauses of the inputs of weight below `μ ≤ n log 2` number at
least `μ 2 ^ (n / μ) / 2 ^ n` per input. So an OR of `m` formulas for parity with `K` distinct
clauses has `2 ^ (n - 1) min (2 ^ μ) (μ 2 ^ (n / μ)) ≤ 2 ^ n (m + K)`
(`CNF.two_pow_mul_min_le_of_any_eval_eq_parity`), and with `μ = √n`, `m + K ≥ 2 ^ (√n - 1)` for
`n ≥ 3` (`CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity`). Paturi, Pudlák and Zane take
`μ = √n + (log n) / 4` for `Ω(n ^ (1 / 4) 2 ^ √n)`.

## Main results

* `Cslib.Logic.PL.CNF.card_filter_isolated_mul_two_rpow_le`: ORs of formulas of width `k` need a
  formula per `2 ^ ((1 - 1 / k) n)` isolated true inputs.
* `Cslib.Logic.PL.CNF.two_rpow_le_length_of_any_eval_eq_parity`,
  `Cslib.Logic.PL.CNF.exists_any_eval_eq_parity`: parity is an OR of `2 ^ (n / k - 1)` but no
  fewer formulas of width `k`, when `k` divides `n`.
* `Cslib.Logic.PL.CNF.two_pow_mul_min_le_of_any_eval_eq_parity`,
  `Cslib.Logic.PL.CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity`: ORs of formulas for parity
  need `2 ^ (√n - 1)` formulas and clauses.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PaturiPudlakZane1999]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Function

variable {n : ℕ}

/-! ### Bottom fan-in `k` -/

/-- **ORs of formulas of width `k` in conjunctive normal form need many formulas**, by the argument
of [Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]: if an OR of formulas whose clauses
have at most `k ≥ 1` literals computes `g`, then each isolated true input of `g` is a solution of
one of them, isolated in every direction, and each of them has at most `2 ^ ((1 - 1 / k) n)` such
solutions (`CNF.card_isolated_mul_two_rpow_le`). -/
theorem CNF.card_filter_isolated_mul_two_rpow_le {k : ℕ} (hk1 : 1 ≤ k) {g : BitString n → Bool}
    {Fs : List (CNF (Fin n))} (hk : ∀ φ ∈ Fs, ∀ c ∈ φ, c.length ≤ k)
    (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = g x) :
    (#{x : BitString n | g x = true ∧ ∀ i, g (update x i !x i) = false} : ℝ) *
      2 ^ ((n : ℝ) / k) ≤ Fs.length * 2 ^ n := by
  -- the solutions of `φ` isolated in every direction
  let I : CNF (Fin n) → Finset (BitString n) := fun φ =>
    {x | φ.eval x = true ∧ ∀ i, φ.eval (update x i !x i) = false}
  have hcover : ({x : BitString n | g x = true ∧ ∀ i, g (update x i !x i) = false} : Finset _) ⊆
      Fs.toFinset.biUnion I := by
    intro x hx
    obtain ⟨hgx, hiso⟩ := (mem_filter.1 hx).2
    obtain ⟨φ, hφ, hφx⟩ := List.any_eq_true.1 ((hFs x).trans hgx)
    refine mem_biUnion.2 ⟨φ, List.mem_toFinset.2 hφ, mem_filter.2 ⟨mem_univ _, hφx, fun i => ?_⟩⟩
    by_contra h
    have := (hFs _).symm.trans (List.any_eq_true.2 ⟨φ, hφ, Bool.eq_true_of_not_eq_false h⟩)
    rw [hiso i] at this
    exact Bool.false_ne_true this
  have hcard := card_le_card hcover |>.trans card_biUnion_le
  calc (#{x : BitString n | g x = true ∧ ∀ i, g (update x i !x i) = false} : ℝ) *
        2 ^ ((n : ℝ) / k)
      ≤ (∑ φ ∈ Fs.toFinset, (#(I φ) : ℝ)) * 2 ^ ((n : ℝ) / k) := by
        gcongr
        exact_mod_cast hcard
    _ = ∑ φ ∈ Fs.toFinset, (#(I φ) : ℝ) * 2 ^ ((n : ℝ) / k) := sum_mul ..
    _ ≤ ∑ _φ ∈ Fs.toFinset, (2 : ℝ) ^ n :=
        sum_le_sum fun φ hφ => CNF.card_isolated_mul_two_rpow_le hk1 (hk φ
          (List.mem_toFinset.1 hφ))
    _ = #Fs.toFinset * 2 ^ n := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Fs.length * 2 ^ n := by
        gcongr
        exact_mod_cast List.toFinset_card_le Fs

/-- **ORs of formulas of width `k` in conjunctive normal form for parity** of `n ≥ 1` bits have at
least `2 ^ (n / k - 1)` formulas. -/
theorem CNF.two_rpow_le_length_of_any_eval_eq_parity (hn : 1 ≤ n) {k : ℕ} (hk1 : 1 ≤ k)
    {Fs : List (CNF (Fin n))} (hk : ∀ φ ∈ Fs, ∀ c ∈ φ, c.length ≤ k)
    (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = parity n x) :
    (2 : ℝ) ^ ((n : ℝ) / k - 1) ≤ Fs.length := by
  have h := CNF.card_filter_isolated_mul_two_rpow_le hk1 hk hFs
  have hcard : #{x : BitString n | parity n x = true ∧
      ∀ i, parity n (update x i !x i) = false} = 2 ^ (n - 1) := by
    rw [← card_filter_parity_eq_true hn]
    congr 1
    ext x
    simp +contextual [parity_update_not]
  rw [hcard] at h
  have h2 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [Real.rpow_sub_one two_ne_zero]
  have hpos : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  push_cast at h
  rw [h2] at h
  rw [div_le_iff₀ two_pos]
  nlinarith

/-- The clause excluding the pattern of `y` on `B`: it holds when the input differs from `y` at
some position of `B`. -/
noncomputable def Clause.exclude (B : Finset (Fin n)) (y : BitString n) : Clause (Fin n) :=
  B.toList.map fun i => (i, !y i)

theorem Clause.eval_exclude_eq_true_iff (B : Finset (Fin n)) (y x : BitString n) :
    (Clause.exclude B y).eval x = true ↔ ∃ i ∈ B, x i ≠ y i := by
  simp [Clause.exclude, Clause.eval_eq_true_iff, Bool.eq_not_iff]

@[simp] theorem Clause.length_exclude (B : Finset (Fin n)) (y : BitString n) :
    (Clause.exclude B y).length = #B := by
  simp [Clause.exclude]

/-- A formula in conjunctive normal form saying that the parity of the bits in `B` is `c`: a
clause excludes each pattern on `B` of the other parity. -/
noncomputable def CNF.parityOnEq (B : Finset (Fin n)) (c : Bool) : CNF (Fin n) :=
  ({y : BitString n | (∀ i ∉ B, y i = false) ∧ parityOn B y ≠ c} : Finset _).toList.map
    (Clause.exclude B)

theorem CNF.eval_parityOnEq_eq_true_iff (B : Finset (Fin n)) (c : Bool) (x : BitString n) :
    (CNF.parityOnEq B c).eval x = true ↔ parityOn B x = c := by
  simp only [CNF.parityOnEq, CNF.eval_map_eq_true_iff, mem_toList, mem_filter, mem_univ,
    true_and, Clause.eval_exclude_eq_true_iff, and_imp]
  constructor
  · intro h
    by_contra hne
    -- the pattern of `x` on `B` is excluded
    have hpar : parityOn B (fun i => if i ∈ B then x i else false) = parityOn B x :=
      parityOn_congr fun j hj => by simp [hj]
    obtain ⟨i, hi, hxi⟩ := h (fun i => if i ∈ B then x i else false)
      (fun i hi => by simp [hi]) (hpar ▸ hne)
    simp [hi] at hxi
  · intro hx y _ hy
    by_contra h
    push Not at h
    exact hy ((parityOn_congr h).symm.trans hx)

/-- **Parity is an OR of `2 ^ (n / k - 1)` formulas of width `k` in conjunctive normal form** when
`k` divides `n`, after [Paturi, Pudlák and Zane, Lemma 4][PaturiPudlakZane1999]: split the variables
into `n / k` blocks of `k`; for each pattern of block parities with odd total, a formula of width
`k` says that the blocks have these parities. So `two_rpow_le_length_of_any_eval_eq_parity` is
attained. -/
theorem CNF.exists_any_eval_eq_parity {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ∣ n) (hn : 1 ≤ n) :
    ∃ Fs : List (CNF (Fin n)), Fs.length = 2 ^ (n / k - 1) ∧
      (∀ φ ∈ Fs, ∀ c ∈ φ, c.length ≤ k) ∧ ∀ x, (Fs.any fun φ => φ.eval x) = parity n x := by
  have hm : 1 ≤ n / k := (Nat.one_le_div_iff hk1).2 (Nat.le_of_dvd hn hkn)
  -- the blocks of `k` consecutive variables
  let B : Fin (n / k) → Finset (Fin n) := fun j => {i | i.val / k = j.val}
  have hBcard (j : Fin (n / k)) : #(B j) ≤ k := by
    calc #(B j)
        ≤ #(univ : Finset (Fin k)) := card_le_card_of_injOn
          (fun i => ⟨i.val % k, Nat.mod_lt _ hk1⟩) (fun _ _ => mem_univ _) fun i hi i' hi' h => by
            have hi := (mem_filter.1 hi).2
            have hi' := (mem_filter.1 hi').2
            have h' : i.val % k = i'.val % k := congrArg Fin.val h
            ext
            rw [← Nat.div_add_mod i.val k, ← Nat.div_add_mod i'.val k, hi, hi', h']
      _ = k := by simp
  have hBdisj : ((univ : Finset (Fin (n / k))) : Set (Fin (n / k))).PairwiseDisjoint B :=
    fun j _ j' _ hjj' => disjoint_left.2 fun i hi hi' =>
      hjj' (Fin.ext ((mem_filter.1 hi).2.symm.trans (mem_filter.1 hi').2))
  have hBunion : univ.biUnion B = univ := by
    refine eq_univ_of_forall fun i => mem_biUnion.2 ⟨⟨i.val / k, ?_⟩, mem_univ _, by simp [B]⟩
    exact Nat.div_lt_div_of_lt_of_dvd hkn i.isLt
  -- the formula saying that the blocks have the parities `b`
  let F : BitString (n / k) → CNF (Fin n) := fun b =>
    (List.finRange (n / k)).flatMap fun j => CNF.parityOnEq (B j) (b j)
  have hF (b : BitString (n / k)) (x : BitString n) :
      (F b).eval x = true ↔ ∀ j, parityOn (B j) x = b j := by
    simp [F, CNF.eval_flatMap_eq_true_iff, CNF.eval_parityOnEq_eq_true_iff]
  refine ⟨({b : BitString (n / k) | parity (n / k) b = true} : Finset _).toList.map F, ?_,
    fun φ hφ c hc => ?_, fun x => ?_⟩
  · rw [List.length_map, length_toList, card_filter_parity_eq_true hm]
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hφ
    obtain ⟨j, -, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hc
    rw [Clause.length_exclude]
    exact hBcard j
  · rw [Bool.eq_iff_iff, List.any_eq_true]
    simp only [List.mem_map, mem_toList, mem_filter, mem_univ, true_and]
    rw [show parity n x = parityOn (univ.biUnion B) x by rw [hBunion]; rfl,
      parityOn_biUnion hBdisj]
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, hx⟩
      rw [show (fun j => parityOn (B j) x) = b from funext ((hF b x).1 hx)]
      exact hb
    · intro h
      exact ⟨_, ⟨fun j => parityOn (B j) x, h, rfl⟩, (hF _ x).2 fun j => rfl⟩

/-! ### Unbounded bottom fan-in -/

/-- For positive `t₁, …, tₘ` summing to at most `m a` with `0 < a ≤ log 2`, the sum of the
`tᵢ 2 ^ (1 / tᵢ)` is at least `m a 2 ^ (1 / a)`: the tangent to the convex function
`t ↦ t 2 ^ (1 / t)` at `a` has slope `2 ^ (1 / a) (1 - log 2 / a) ≤ 0`. -/
private theorem card_mul_mul_two_rpow_inv_le_sum {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 < t i) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ Real.log 2)
    (hsum : ∑ i ∈ s, t i ≤ #s * a) :
    #s * a * 2 ^ (1 / a) ≤ ∑ i ∈ s, t i * 2 ^ (1 / t i) := by
  set L := Real.log 2
  -- the tangent at `a`, from `exp y ≥ 1 + y`
  have htan : ∀ i ∈ s, 2 ^ (1 / a) * (t i + L - L / a * t i) ≤ t i * 2 ^ (1 / t i) :=
    fun i hi => by
    have hti := ht i hi
    have h1 : (2 : ℝ) ^ (1 / t i) = 2 ^ (1 / a) * 2 ^ (1 / t i - 1 / a) := by
      rw [← Real.rpow_add two_pos]
      ring_nf
    have h2 : 1 + L * (1 / t i - 1 / a) ≤ (2 : ℝ) ^ (1 / t i - 1 / a) := by
      rw [Real.rpow_def_of_pos two_pos]
      linarith [Real.add_one_le_exp (L * (1 / t i - 1 / a))]
    have h3 : t i * (1 + L * (1 / t i - 1 / a)) = t i + L - L / a * t i := by
      field_simp
      ring
    rw [h1, ← h3]
    calc 2 ^ (1 / a) * (t i * (1 + L * (1 / t i - 1 / a)))
        ≤ 2 ^ (1 / a) * (t i * 2 ^ (1 / t i - 1 / a)) := by gcongr
      _ = t i * (2 ^ (1 / a) * 2 ^ (1 / t i - 1 / a)) := by ring
  have hLa : 0 ≤ L / a - 1 := by
    rw [sub_nonneg, le_div_iff₀ ha]
    linarith
  have hkey : (#s : ℝ) * a ≤ ∑ i ∈ s, t i + #s * L - L / a * ∑ i ∈ s, t i := by
    have h := mul_le_mul_of_nonneg_left hsum hLa
    have e : (L / a - 1) * (#s * a) = #s * L - #s * a := by
      field_simp
    nlinarith
  calc #s * a * 2 ^ (1 / a) ≤ 2 ^ (1 / a) * (∑ i ∈ s, t i + #s * L - L / a * ∑ i ∈ s, t i) := by
        rw [mul_comm]
        gcongr
    _ = ∑ i ∈ s, 2 ^ (1 / a) * (t i + L - L / a * t i) := by
        rw [← mul_sum, sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    _ ≤ _ := sum_le_sum htan

/-- **ORs of formulas in conjunctive normal form for parity need many gates**
[Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]: if an OR of `m` formulas with `K`
distinct clauses (as sets of literals) computes the parity of `n ≥ 1` bits, then
`2 ^ (n - 1) min (2 ^ μ) (μ 2 ^ (n / μ)) ≤ 2 ^ n (m + K)` for every `0 < μ ≤ n log 2`. -/
theorem CNF.two_pow_mul_min_le_of_any_eval_eq_parity (hn : 1 ≤ n) {μ : ℝ} (hμ : 0 < μ)
    (hμn : μ ≤ n * Real.log 2) {Fs : List (CNF (Fin n))}
    (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = parity n x) :
    (2 : ℝ) ^ (n - 1) * min (2 ^ μ) (μ * 2 ^ (n / μ)) ≤
      2 ^ n * (Fs.length + #(Fs.flatten.map List.toFinset).toFinset) := by
  set S : Finset (BitString n) := {x | parity n x = true}
  -- each true input is a solution of one of the formulas, isolated in every direction
  have hchoose : ∀ x ∈ S, ∃ φ ∈ Fs, φ.eval x = true := fun x hx =>
    List.any_eq_true.1 ((hFs x).trans (mem_filter.1 hx).2)
  choose! F hF hFx using hchoose
  have hiso : ∀ x ∈ S, ∀ i, (F x).eval (update x i !x i) = false := fun x hx i => by
    by_contra h
    have := (hFs _).symm.trans (List.any_eq_true.2 ⟨F x, hF x hx, Bool.eq_true_of_not_eq_false h⟩)
    rw [parity_update_not, (mem_filter.1 hx).2] at this
    exact Bool.false_ne_true this
  have hcrit : ∀ x ∈ S, ∀ i, ∃ c ∈ F x, CNF.Critical x c i := fun x hx i =>
    CNF.exists_critical (hFx x hx) (hiso x hx i)
  set w : BitString n → ℝ := fun x => ∑ i, 1 / ((F x).critWidth x i : ℝ)
  set S₁ := S.filter fun x => μ ≤ w x
  set S₂ := S.filter fun x => ¬ μ ≤ w x
  set Cl := (Fs.flatten.map List.toFinset).toFinset
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- inputs of weight at least `μ`: each formula has few solutions of large weight
  have h₁ : (#S₁ : ℝ) * 2 ^ μ ≤ Fs.length * 2 ^ n := by
    set A : CNF (Fin n) → Finset (BitString n) := fun φ =>
      {x | φ.eval x = true ∧ μ ≤ ∑ i, 1 / (φ.critWidth x i : ℝ)}
    have hsub : S₁ ⊆ Fs.toFinset.biUnion A := fun x hx => by
      obtain ⟨hxS, hxw⟩ := mem_filter.1 hx
      exact mem_biUnion.2 ⟨F x, List.mem_toFinset.2 (hF x hxS),
        mem_filter.2 ⟨mem_univ _, hFx x hxS, hxw⟩⟩
    calc (#S₁ : ℝ) * 2 ^ μ ≤ (∑ φ ∈ Fs.toFinset, (#(A φ) : ℝ)) * 2 ^ μ := by
          gcongr
          exact_mod_cast (card_le_card hsub).trans card_biUnion_le
      _ = ∑ φ ∈ Fs.toFinset, (#(A φ) : ℝ) * 2 ^ μ := sum_mul ..
      _ ≤ ∑ _φ ∈ Fs.toFinset, (2 : ℝ) ^ n :=
          sum_le_sum fun φ _ => CNF.card_filter_le_sum_inv_critWidth_mul_two_rpow_le φ μ
      _ = #Fs.toFinset * 2 ^ n := by rw [sum_const, nsmul_eq_mul]
      _ ≤ Fs.length * 2 ^ n := by
          gcongr
          exact_mod_cast List.toFinset_card_le Fs
  -- inputs of weight below `μ`: their shortest critical clauses are many
  have h₂ : (#S₂ : ℝ) * (μ * 2 ^ (n / μ)) ≤ #Cl * 2 ^ n := by
    set P := S₂ ×ˢ (univ : Finset (Fin n))
    have hcl : ∀ p ∈ P, ∃ c ∈ F p.1, CNF.Critical p.1 c p.2 ∧
        (c.map Prod.fst).toFinset.card = (F p.1).critWidth p.1 p.2 := fun p hp =>
      CNF.exists_critical_card_eq_critWidth (hcrit p.1 (mem_filter.1 (mem_product.1 hp).1).1 p.2)
    choose! cl hclF hclc hclw using hcl
    set ℓ : BitString n × Fin n → ℕ := fun p => (F p.1).critWidth p.1 p.2
    set wt : BitString n × Fin n → ℝ := fun p => 1 / ((ℓ p : ℝ) * 2 ^ (n - ℓ p))
    have hvars (c : Clause (Fin n)) : (c.map Prod.fst).toFinset = c.toFinset.image Prod.fst := by
      ext
      simp
    -- the weights of the pairs whose shortest critical clause is `C` sum to at most one
    have hmaps : ∀ p ∈ P, (cl p).toFinset ∈ Cl := fun p hp => by
      have hxS := (mem_filter.1 (mem_product.1 hp).1).1
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨cl p, List.mem_flatten.2 ⟨F p.1, hF p.1 hxS,
        hclF p hp⟩, rfl⟩)
    have ha : ∑ p ∈ P, wt p ≤ #Cl := by
      rw [← sum_fiberwise_of_maps_to hmaps]
      refine (sum_le_sum fun C _ => ?_).trans_eq (by rw [sum_const, nsmul_eq_mul, mul_one])
      rcases ({p ∈ P | (cl p).toFinset = C} : Finset _).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
      · rw [he, sum_empty]
        norm_num
      obtain ⟨hp₀P, hp₀C⟩ := mem_filter.1 hp₀
      set v := ((cl p₀).map Prod.fst).toFinset.card
      have hℓ : ∀ p ∈ ({p ∈ P | (cl p).toFinset = C} : Finset _), ℓ p = v := fun p hp => by
        obtain ⟨hpP, hpC⟩ := mem_filter.1 hp
        rw [show ℓ p = ((cl p).map Prod.fst).toFinset.card from (hclw p hpP).symm, hvars,
          hpC, ← hp₀C, ← hvars]
      have hv : 0 < v := by
        rw [← hℓ p₀ hp₀]
        exact CNF.critWidth_pos (hcrit p₀.1 (mem_filter.1 (mem_product.1 hp₀P).1).1 p₀.2)
      have hfib : #{p ∈ P | (cl p).toFinset = C} ≤ v * 2 ^ (n - v) := by
        refine (card_le_card fun p hp => ?_).trans (CNF.card_filter_critical_prod_le (cl p₀))
        obtain ⟨hpP, hpC⟩ := mem_filter.1 hp
        refine mem_filter.2 ⟨mem_univ _, (CNF.critical_congr fun l => ?_).1 (hclc p hpP)⟩
        rw [← List.mem_toFinset, ← List.mem_toFinset (l := cl p₀), hpC, hp₀C]
      rw [sum_congr rfl fun p hp => show wt p = 1 / ((v : ℝ) * 2 ^ (n - v)) by
        simp only [wt, hℓ p hp], sum_const, nsmul_eq_mul, mul_one_div,
        div_le_one (by positivity)]
      exact_mod_cast hfib
    -- each input of weight below `μ` contributes `μ 2 ^ (n / μ) / 2 ^ n`
    have hb : ∀ x ∈ S₂, μ * 2 ^ (n / μ) ≤ 2 ^ n * ∑ i, wt (x, i) := fun x hx => by
      obtain ⟨hxS, hxw⟩ := mem_filter.1 hx
      have hpos : ∀ i, 0 < (F x).critWidth x i := fun i => CNF.critWidth_pos (hcrit x hxS i)
      have hle : ∀ i, (F x).critWidth x i ≤ n := fun i => by
        obtain ⟨c, -, -, hc⟩ := CNF.exists_critical_card_eq_critWidth (hcrit x hxS i)
        rw [← hc]
        exact (card_le_univ _).trans_eq (Fintype.card_fin n)
      have htan := card_mul_mul_two_rpow_inv_le_sum (univ : Finset (Fin n))
        (fun i => 1 / ((F x).critWidth x i : ℝ)) (fun i _ => by
          have := hpos i
          positivity) (a := μ / n) (by positivity)
        (by rw [div_le_iff₀ hn0]; linarith)
        (by rw [card_univ, Fintype.card_fin, mul_div_cancel₀ _ hn0.ne']; exact (not_le.1 hxw).le)
      rw [card_univ, Fintype.card_fin] at htan
      have hterm : ∀ i, 1 / ((F x).critWidth x i : ℝ) * 2 ^ (1 / (1 / ((F x).critWidth x i : ℝ))) =
          2 ^ n * wt (x, i) := fun i => by
        have h2 : (2 : ℝ) ^ n = 2 ^ (F x).critWidth x i * 2 ^ (n - (F x).critWidth x i) := by
          rw [← pow_add, Nat.add_sub_cancel' (hle i)]
        have hp : (0 : ℝ) < (F x).critWidth x i := by exact_mod_cast hpos i
        simp only [wt, ℓ, one_div_one_div, Real.rpow_natCast, h2]
        field_simp
      calc μ * 2 ^ (n / μ) = n * (μ / n) * 2 ^ (1 / (μ / n)) := by
            rw [mul_div_cancel₀ _ hn0.ne', one_div_div]
        _ ≤ _ := htan
        _ = 2 ^ n * ∑ i, wt (x, i) := by
            rw [mul_sum]
            exact sum_congr rfl fun i _ => hterm i
    calc (#S₂ : ℝ) * (μ * 2 ^ (n / μ)) = ∑ _x ∈ S₂, μ * 2 ^ (n / μ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ S₂, 2 ^ n * ∑ i, wt (x, i) := sum_le_sum hb
      _ = 2 ^ n * ∑ p ∈ P, wt p := by rw [← mul_sum, sum_product]
      _ ≤ 2 ^ n * #Cl := by gcongr
      _ = #Cl * 2 ^ n := mul_comm _ _
  -- the true inputs split into the two kinds
  have hS : (#S₁ : ℝ) + #S₂ = 2 ^ (n - 1) := by
    have h := card_filter_add_card_filter_not (s := S) (fun x => μ ≤ w x)
    rw [card_filter_parity_eq_true hn] at h
    exact_mod_cast h
  have hm₁ : min (2 ^ μ) (μ * 2 ^ (n / μ)) ≤ (2 : ℝ) ^ μ := min_le_left _ _
  have hm₂ : min (2 ^ μ) (μ * 2 ^ (n / μ)) ≤ μ * 2 ^ (n / μ) := min_le_right _ _
  calc (2 : ℝ) ^ (n - 1) * min (2 ^ μ) (μ * 2 ^ (n / μ))
      = #S₁ * min (2 ^ μ) (μ * 2 ^ (n / μ)) + #S₂ * min (2 ^ μ) (μ * 2 ^ (n / μ)) := by
        rw [← hS, add_mul]
    _ ≤ #S₁ * 2 ^ μ + #S₂ * (μ * 2 ^ (n / μ)) := by gcongr
    _ ≤ Fs.length * 2 ^ n + #Cl * 2 ^ n := add_le_add h₁ h₂
    _ = 2 ^ n * (Fs.length + #Cl) := by ring

/-- **ORs of formulas in conjunctive normal form for parity need `2 ^ (√n - 1)` gates**
[Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]: an OR of `m` formulas with `K` distinct
clauses computing the parity of `n ≥ 3` bits has `2 ^ (√n - 1) ≤ m + K`. -/
theorem CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity (hn : 3 ≤ n)
    {Fs : List (CNF (Fin n))} (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = parity n x) :
    (2 : ℝ) ^ (√(n : ℝ) - 1) ≤ Fs.length + #(Fs.flatten.map List.toFinset).toFinset := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsqsq : √(n : ℝ) * √n = n := Real.mul_self_sqrt (by linarith)
  have h1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 (by linarith)
  -- `√n ≤ n log 2`, as `√n ≥ 1.7` and `log 2 > 0.69`
  have hμn : √(n : ℝ) ≤ n * Real.log 2 := by
    have hlog := Real.log_two_gt_d9
    have h17 : (1.7 : ℝ) ≤ √n := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
    nlinarith
  have h := CNF.two_pow_mul_min_le_of_any_eval_eq_parity (by omega) hsq hμn hFs
  rw [Real.div_sqrt, min_eq_left (le_mul_of_one_le_left (by positivity) h1)] at h
  have h2n : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h2n, mul_assoc] at h
  rw [Real.rpow_sub_one two_ne_zero, div_le_iff₀ two_pos]
  have hpos : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  nlinarith

end Cslib.Logic.PL
