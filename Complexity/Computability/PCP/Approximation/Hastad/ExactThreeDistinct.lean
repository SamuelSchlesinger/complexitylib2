/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Approximation.MaxExactThreeSAT
public import Complexity.Foundations.BooleanAnalysis.Fourier
import Complexity.Foundations.Data.Finset.Expect

/-!
# Exact 3-Clauses with Distinct Variables and the `7 / 8` Random Assignment Bound

For a clause of three literals on three distinct variables
(`Cslib.Logic.PL.Clause.IsExactThreeDistinct`), a uniform random assignment falsifies the clause
with probability `1 / 8` and satisfies it with probability `7 / 8`
(`Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_false`,
`Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_true`). By linearity of expectation,
every formula whose clauses each have three distinct variables
(`Cslib.Logic.PL.CNF.IsExactThreeDistinct`) has an assignment falsifying at most `1 / 8` of its
clauses (`Cslib.Logic.PL.CNF.IsExactThreeDistinct.unsatVal_le_one_eighth`). Note that
`Cslib.Logic.PL.CNF.IsExactThreeDistinct` requires three distinct variables per clause, unlike
`Cslib.Complexity.ExactThreeSAT` and `Cslib.Complexity.GapExactThreeSAT`, which only require each
clause to have length `3` and allow repeated literals.

## Main definitions

* `Cslib.Logic.PL.Clause.IsExactThreeDistinct`, `Cslib.Logic.PL.CNF.IsExactThreeDistinct`: clauses
  and CNF formulas with three distinct variables per clause.
* `Cslib.Complexity.GapExactThreeDistinctSAT`: the two-sided promise problem of MAX-E3SAT with
  completeness `c` and soundness `s` on formulas with three distinct variables per clause.

## Main results

* `Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_false`,
  `Cslib.Logic.PL.Clause.IsExactThreeDistinct.expect_eval_eq_true`: a uniform random assignment
  falsifies an exact 3-clause on distinct variables with probability `1 / 8` and satisfies it with
  probability `7 / 8`.
* `Cslib.Logic.PL.CNF.IsExactThreeDistinct.unsatVal_le_one_eighth`,
  `Cslib.Logic.PL.CNF.IsExactThreeDistinct.exists_countUnsat_le_div_eight`: every E3-CNF formula
  with three distinct variables per clause has `unsatVal ≤ 1 / 8`, and thus `no` is empty for
  `GapExactThreeDistinctSAT c s` whenever `s < 7 / 8`
  (`Cslib.Complexity.no_GapExactThreeDistinctSAT_eq_empty`).

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 22][AroraBarak09]
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Cslib.Logic.PL

open Cslib.BitString

variable {V ι : Type*}

/-! ### Exact 3-clauses with distinct variables and the `7 / 8` random assignment bound -/

/-- A clause has **three distinct variables** when it has length `3` and its variables have no
duplicates. -/
def Clause.IsExactThreeDistinct (c : Clause V) : Prop :=
  c.length = 3 ∧ (c.map Prod.fst).Nodup

/-- A formula is an **exact 3-CNF with distinct variables per clause** when every clause has three
distinct variables. -/
def CNF.IsExactThreeDistinct (φ : CNF V) : Prop :=
  ∀ c ∈ φ, c.IsExactThreeDistinct

instance [DecidableEq V] {c : Clause V} : Decidable c.IsExactThreeDistinct :=
  inferInstanceAs (Decidable (c.length = 3 ∧ (c.map Prod.fst).Nodup))

instance [DecidableEq V] {φ : CNF V} : Decidable φ.IsExactThreeDistinct :=
  inferInstanceAs (Decidable (∀ c ∈ φ, c.IsExactThreeDistinct))

theorem Clause.IsExactThreeDistinct.length_eq {c : Clause V} (hc : c.IsExactThreeDistinct) :
    c.length = 3 :=
  hc.1

theorem Clause.IsExactThreeDistinct.nodup_map_fst {c : Clause V} (hc : c.IsExactThreeDistinct) :
    (c.map Prod.fst).Nodup :=
  hc.2

/-- Every exact 3-clause with distinct variables is a list of three literals on pairwise distinct
variables. -/
theorem Clause.isExactThreeDistinct_iff {c : Clause V} :
    c.IsExactThreeDistinct ↔
      ∃ l₁ l₂ l₃ : Literal V,
        c = [l₁, l₂, l₃] ∧ l₁.1 ≠ l₂.1 ∧ l₁.1 ≠ l₃.1 ∧ l₂.1 ≠ l₃.1 := by
  constructor
  · rintro ⟨hlen, hnodup⟩
    match c, hlen with
    | [l₁, l₂, l₃], _ =>
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or, List.nodup_nil, and_true] at hnodup
      exact ⟨l₁, l₂, l₃, rfl, hnodup.1.1, hnodup.1.2, hnodup.2.1⟩
  · rintro ⟨l₁, l₂, l₃, rfl, h12, h13, h23⟩
    refine ⟨rfl, ?_⟩
    simp [h12, h13, h23]

/-- The falsification indicator of a literal `(v, b)` under `σ` is
`(1 - signVal b * signVal (σ v)) / 2`. -/
theorem Literal.if_eval_eq_zero_one (l : Literal V) (σ : V → Bool) :
    (if l.eval σ then (0 : ℝ) else 1) = (1 - signVal l.2 * signVal (σ l.1)) / 2 := by
  rcases l with ⟨v, b⟩
  cases b <;> cases h : σ v <;> simp [Literal.eval, signVal, h]

/-- A clause `l :: c` is falsified iff both `l` and `c` are falsified. -/
theorem Clause.if_eval_cons_eq_mul (l : Literal V) (c : Clause V) (σ : V → Bool) :
    (if Clause.eval σ (l :: c) then (0 : ℝ) else 1) =
      (if l.eval σ then (0 : ℝ) else 1) * (if c.eval σ then (0 : ℝ) else 1) := by
  rw [Clause.eval_cons]
  cases l.eval σ <;> cases c.eval σ <;> simp

section FintypeCube

variable [Fintype ι] [DecidableEq ι]

/-- Over a uniform random assignment `σ : ι → Bool`, a single variable has mean sign `0`. -/
private theorem expect_signVal_eval (v : ι) : (𝔼 σ : ι → Bool, signVal (σ v)) = 0 := by
  have h : (fun σ : ι → Bool => signVal (σ v)) = chi ℝ {v} := by
    funext σ
    exact (chi_singleton v σ).symm
  rw [h, expect_chi, ite_eq_right_iff.2 fun h0 => absurd h0 (singleton_ne_empty v)]

/-- Over a uniform random assignment `σ : ι → Bool`, two distinct variables have uncorrelated
signs. -/
private theorem expect_signVal_mul_of_ne {v₁ v₂ : ι} (h12 : v₁ ≠ v₂) :
    (𝔼 σ : ι → Bool, signVal (σ v₁) * signVal (σ v₂)) = 0 := by
  have h : (fun σ : ι → Bool => signVal (σ v₁) * signVal (σ v₂)) =
      fun σ => chi ℝ {v₁} σ * chi ℝ {v₂} σ := by
    funext σ
    rw [chi_singleton, chi_singleton]
  rw [h, expect_chi_mul_chi, ite_eq_right_iff.2 fun h0 => absurd h0 (singleton_injective.ne h12)]

/-- Over a uniform random assignment `σ : ι → Bool`, three pairwise distinct variables have zero
triple sign correlation. -/
private theorem expect_signVal_mul_three_of_ne {v₁ v₂ v₃ : ι} (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃)
    (h23 : v₂ ≠ v₃) :
    (𝔼 σ : ι → Bool, signVal (σ v₁) * signVal (σ v₂) * signVal (σ v₃)) = 0 := by
  have h : (fun σ : ι → Bool => signVal (σ v₁) * signVal (σ v₂) * signVal (σ v₃)) =
      chi ℝ ({v₁, v₂, v₃} : Finset ι) := by
    funext σ
    have hnot1 : v₁ ∉ ({v₂, v₃} : Finset ι) := by simp [h12, h13]
    have hnot2 : v₂ ∉ ({v₃} : Finset ι) := by simp [h23]
    rw [chi_eq_prod_signVal, prod_insert hnot1, prod_insert hnot2, prod_singleton, mul_assoc]
  rw [h, expect_chi, ite_eq_right_iff.2 fun h0 => absurd h0 (insert_ne_empty _ _)]

/-- **A uniform random assignment falsifies any 3-clause on three distinct variables with
probability `1 / 8`.** -/
theorem Clause.IsExactThreeDistinct.expect_eval_eq_false {c : Clause ι}
    (hc : c.IsExactThreeDistinct) :
    (𝔼 σ : ι → Bool, if c.eval σ then (0 : ℝ) else 1) = 1 / 8 := by
  obtain ⟨l₁, l₂, l₃, rfl, h12, h13, h23⟩ := Clause.isExactThreeDistinct_iff.1 hc
  have hexp (σ : ι → Bool) :
      (if Clause.eval σ [l₁, l₂, l₃] then (0 : ℝ) else 1) =
        1 / 8 -
        (signVal l₁.2 / 8) * signVal (σ l₁.1) -
        (signVal l₂.2 / 8) * signVal (σ l₂.1) -
        (signVal l₃.2 / 8) * signVal (σ l₃.1) +
        (signVal l₁.2 * signVal l₂.2 / 8) * (signVal (σ l₁.1) * signVal (σ l₂.1)) +
        (signVal l₁.2 * signVal l₃.2 / 8) * (signVal (σ l₁.1) * signVal (σ l₃.1)) +
        (signVal l₂.2 * signVal l₃.2 / 8) * (signVal (σ l₂.1) * signVal (σ l₃.1)) -
        (signVal l₁.2 * signVal l₂.2 * signVal l₃.2 / 8) *
          (signVal (σ l₁.1) * signVal (σ l₂.1) * signVal (σ l₃.1)) := by
    rw [Clause.if_eval_cons_eq_mul, Clause.if_eval_cons_eq_mul, Clause.if_eval_cons_eq_mul]
    simp only [Clause.eval_nil, Bool.false_eq_true, ↓reduceIte, mul_one,
      Literal.if_eval_eq_zero_one]
    ring
  simp only [hexp, expect_sub_distrib, expect_add_distrib, Fintype.expect_const, ← mul_expect,
    expect_signVal_eval, expect_signVal_mul_of_ne h12, expect_signVal_mul_of_ne h13,
    expect_signVal_mul_of_ne h23, expect_signVal_mul_three_of_ne h12 h13 h23]
  ring

/-- **A uniform random assignment satisfies any 3-clause on three distinct variables with
probability `7 / 8`.** -/
theorem Clause.IsExactThreeDistinct.expect_eval_eq_true {c : Clause ι}
    (hc : c.IsExactThreeDistinct) :
    (𝔼 σ : ι → Bool, if c.eval σ then (1 : ℝ) else 0) = 7 / 8 := by
  have h1 (σ : ι → Bool) :
      (if c.eval σ then (1 : ℝ) else 0) = 1 - (if c.eval σ then (0 : ℝ) else 1) := by
    cases c.eval σ <;> norm_num
  simp only [h1, expect_sub_distrib, Fintype.expect_const, hc.expect_eval_eq_false]
  ring

/-- Over the 3-bit cube `Fin 3 → Bool`, any 3-clause on three distinct variables is satisfied by
exactly `7` of the `8` truth assignments. -/
theorem Clause.IsExactThreeDistinct.card_eval_eq_true {c : Clause (Fin 3)}
    (hc : c.IsExactThreeDistinct) :
    #{σ : Fin 3 → Bool | c.eval σ = true} = 7 := by
  have h := hc.expect_eval_eq_true
  rw [Fintype.expect_eq_sum_div_card, sum_boole] at h
  have hcard : (Fintype.card (Fin 3 → Bool) : ℝ) = 8 := by norm_num
  rw [hcard] at h
  have h7 : ((#{σ : Fin 3 → Bool | c.eval σ = true} : ℕ) : ℝ) = 7 := by linarith
  exact_mod_cast h7

/-- The expected number of falsified clauses in an exact 3-CNF formula with distinct variables per
clause under a uniform random assignment is `φ.length / 8`. -/
theorem CNF.IsExactThreeDistinct.expect_countUnsat {φ : CNF ι} (hφ : φ.IsExactThreeDistinct) :
    (𝔼 σ : ι → Bool, (φ.countUnsat σ : ℝ)) = (φ.length : ℝ) / 8 := by
  induction φ with
  | nil => simp [CNF.countUnsat]
  | cons c φ ih =>
    have hc : c.IsExactThreeDistinct := hφ c List.mem_cons_self
    have hφ' : CNF.IsExactThreeDistinct φ := fun d hd => hφ d (List.mem_cons_of_mem _ hd)
    have hcons (σ : ι → Bool) :
        ((CNF.countUnsat σ (c :: φ) : ℕ) : ℝ) =
          (if c.eval σ then (0 : ℝ) else 1) + (CNF.countUnsat σ φ : ℝ) := by
      rw [CNF.countUnsat, List.countP_cons, ← CNF.countUnsat]
      cases c.eval σ <;> simp [add_comm]
    simp only [hcons, expect_add_distrib, hc.expect_eval_eq_false, ih hφ', List.length_cons,
      Nat.cast_add, Nat.cast_one]
    ring

end FintypeCube

/-- Relabelling a clause along a map that is injective on its variables preserves
`Clause.IsExactThreeDistinct`. -/
theorem Clause.IsExactThreeDistinct.relabel_of_injOn {f : V → ι} {c : Clause V}
    (hf : ∀ x ∈ c.map Prod.fst, ∀ y ∈ c.map Prod.fst, f x = f y → x = y)
    (hc : c.IsExactThreeDistinct) : (c.relabel f).IsExactThreeDistinct := by
  refine ⟨by rw [Clause.length_relabel, hc.1], ?_⟩
  have hmap : (c.relabel f).map Prod.fst = (c.map Prod.fst).map f := by
    simp [Clause.relabel, List.map_map, Function.comp_def]
  rw [hmap]
  exact hc.2.map_on hf

/-- **The `7 / 8` random-assignment bound**: in every exact 3-CNF formula `φ` with three distinct
variables per clause, some assignment falsifies at most `1 / 8` of the clauses
(`φ.unsatVal ≤ 1 / 8`), hence satisfies at least `7 / 8` of the clauses. -/
theorem CNF.IsExactThreeDistinct.unsatVal_le_one_eighth {φ : CNF V}
    (hφ : φ.IsExactThreeDistinct) : φ.unsatVal ≤ 1 / 8 := by
  classical
  let S : Finset V := φ.vars.toFinset
  let toVar (v : V) : Option S := if h : v ∈ S then some ⟨v, h⟩ else none
  have hφ' : (φ.relabel toVar).IsExactThreeDistinct := by
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    refine (hφ c hc).relabel_of_injOn fun x hx y hy hxy => ?_
    obtain ⟨lx, hlx, rfl⟩ := List.mem_map.1 hx
    obtain ⟨ly, hly, rfl⟩ := List.mem_map.1 hy
    have hxS : lx.1 ∈ S := List.mem_toFinset.2 (CNF.mem_vars.2 ⟨c, hc, lx.2, hlx⟩)
    have hyS : ly.1 ∈ S := List.mem_toFinset.2 (CNF.mem_vars.2 ⟨c, hc, ly.2, hly⟩)
    simp only [toVar, hxS, hyS, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hxy
    exact hxy
  have hle : φ.unsatVal ≤ (φ.relabel toVar).unsatVal := by
    refine le_ciInf fun τ => ?_
    rw [CNF.countUnsat_relabel, CNF.relabel, List.length_map]
    exact φ.unsatVal_le (τ ∘ toVar)
  refine hle.trans ?_
  rcases Nat.eq_zero_or_pos (φ.relabel toVar).length with h0 | hpos
  · have hsat : (φ.relabel toVar).Satisfiable :=
      ⟨fun _ => false, by rw [List.length_eq_zero_iff.1 h0]; rfl⟩
    rw [(CNF.unsatVal_eq_zero_iff _).2 hsat]
    norm_num
  · have hlen : (0 : ℝ) < (φ.relabel toVar).length := by exact_mod_cast hpos
    have hle' : (φ.relabel toVar).unsatVal ≤
        𝔼 σ : Option S → Bool, ((φ.relabel toVar).countUnsat σ : ℝ) / (φ.relabel toVar).length := by
      simpa only [Fintype.expect_const] using
        expect_le_expect (s := univ) fun σ _ => (φ.relabel toVar).unsatVal_le σ
    rw [← expect_div, hφ'.expect_countUnsat, div_right_comm, div_self hlen.ne'] at hle'
    exact hle'

/-- In every exact 3-CNF formula `φ` with three distinct variables per clause, there exists an
assignment falsifying at most `φ.length / 8` clauses (equivalently satisfying at least
`7 / 8 * φ.length` clauses). -/
theorem CNF.IsExactThreeDistinct.exists_countUnsat_le_div_eight {φ : CNF V}
    (hφ : φ.IsExactThreeDistinct) :
    ∃ σ : V → Bool, (φ.countUnsat σ : ℝ) ≤ (φ.length : ℝ) / 8 := by
  obtain ⟨σ, hσ⟩ := φ.exists_countUnsat_div_eq_unsatVal
  refine ⟨σ, ?_⟩
  rcases Nat.eq_zero_or_pos φ.length with h0 | hpos
  · have hc0 : φ.countUnsat σ = 0 := Nat.le_zero.1 ((φ.countUnsat_le_length σ).trans_eq h0)
    simp [hc0, h0]
  · have hlen : (0 : ℝ) < φ.length := by exact_mod_cast hpos
    have hle := hφ.unsatVal_le_one_eighth
    rw [← hσ, div_le_iff₀ hlen] at hle
    linarith

end Cslib.Logic.PL

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- The two-sided gap problem of **MAX-E3SAT on clauses with three distinct variables** with
completeness `c` and soundness `s`, restricted to formulas satisfying `CNF.IsExactThreeDistinct`
(unlike `GapExactThreeSAT`, which allows repeated variables in a clause). Yes-instances have
maximum satisfied clause fraction `1 - φ.unsatVal ≥ c`; no-instances have
`1 - φ.unsatVal ≤ s`. -/
noncomputable def GapExactThreeDistinctSAT (c s : ℝ) : PromiseProblem (CNF ℕ) :=
  (PromiseProblem.gapMax (fun φ : CNF ℕ => 1 - φ.unsatVal) (fun _ => c) (fun _ => s)).restrict
    {φ | φ.IsExactThreeDistinct}

/-- **The `7 / 8` random-assignment bound for MAX-E3SAT**: for every `s < 7 / 8`,
every E3-CNF formula with three distinct variables per clause has an assignment satisfying at least
`7 / 8 > s` of its clauses (`CNF.IsExactThreeDistinct.unsatVal_le_one_eighth`), so the no-instance
set of `GapExactThreeDistinctSAT c s` is empty. -/
theorem no_GapExactThreeDistinctSAT_eq_empty {c s : ℝ} (hs : s < 7 / 8) :
    (GapExactThreeDistinctSAT c s).no = ∅ := by
  ext φ
  simp only [GapExactThreeDistinctSAT, PromiseProblem.no_restrict,
    PromiseProblem.mem_no_gapMax, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro ⟨h1, _⟩ h3
  have h8 := h3.unsatVal_le_one_eighth
  linarith

end Cslib.Complexity
