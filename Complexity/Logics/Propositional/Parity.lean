/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Logics.Propositional.CNF.Coding
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

At depth three, the satisfiability coding lemma bounds the isolated true inputs of a formula of
width `k` in conjunctive normal form by `2 ^ ((1 - 1 / k) n)`. Every formula in an OR computing `g`
has its true inputs among those of `g`, so its solutions at isolated true inputs of `g` are isolated
too, and the OR needs at least `#(isolated true inputs) / 2 ^ ((1 - 1 / k) n)` formulas
(`CNF.card_filter_isolated_mul_two_rpow_le`), as in the proof of
[Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]. For parity this is `2 ^ (n / k - 1)`
(`CNF.two_rpow_le_length_of_any_eval_eq_parity`), and the bound is attained when `k` divides `n`:
split the variables into blocks of `k` and take one formula for each pattern of block parities with
odd total (`CNF.exists_any_eval_eq_parity`), as in the example after
[Paturi, Pudlák and Zane, Lemma 4][PaturiPudlakZane1999].

## Main results

* `Cslib.Logic.PL.DNF.card_filter_isolated_le_length`,
  `Cslib.Logic.PL.CNF.card_filter_isolated_le_length`: normal forms have a term or clause per
  isolated input.
* `Cslib.Logic.PL.DNF.two_pow_le_length_of_eval_eq_parity`,
  `Cslib.Logic.PL.CNF.two_pow_le_length_of_eval_eq_parity`: normal forms of parity have at least
  `2 ^ (n - 1)` terms or clauses.
* `Cslib.Logic.PL.CNF.card_filter_isolated_mul_two_rpow_le`: ORs of formulas of width `k` in
  conjunctive normal form need a formula per `2 ^ ((1 - 1 / k) n)` isolated true inputs.
* `Cslib.Logic.PL.CNF.two_rpow_le_length_of_any_eval_eq_parity`,
  `Cslib.Logic.PL.CNF.exists_any_eval_eq_parity`: parity is an OR of `2 ^ (n / k - 1)` but no
  fewer formulas of width `k` in conjunctive normal form, when `k` divides `n`.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PaturiPudlakZane1999]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Function

variable {n : ℕ}

/-! ### Depth two -/

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

/-! ### Depth three -/

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

end Cslib.Logic.PL
