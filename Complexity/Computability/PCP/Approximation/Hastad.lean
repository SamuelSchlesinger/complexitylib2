/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Approximation.LabelCover
public import Complexity.Computability.PCP.Approximation.MaxExactThreeSAT
public import Complexity.Foundations.BooleanAnalysis.Convolution
public import Complexity.Foundations.BooleanAnalysis.Hadamard
public import Complexity.Foundations.BooleanAnalysis.Noise
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.Chebyshev

/-!
# Håstad's 3-bit test and optimal MAX-E3SAT inapproximability

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

Håstad [Hastad2001] proved that this `7 / 8` threshold is optimal: for every `ε > 0`, no
polynomial-time algorithm can beat `7 / 8 + ε` unless `P = NP`. The core of the proof is Håstad's
noisy 3-bit linear test on folded Long Code tables over a Label Cover projection `π : β → γ`:

1. The **Long Code** of `x : α` (`Cslib.BitString.longCode`) evaluates each Boolean function
   `g : α → Bool` at `x`. A table `B : (γ → Bool) → Bool` is **folded**
   (`Cslib.PCP.Hastad.IsFolded`) when `B (f + fun _ => true) = !B f`, which forces its empty
   Fourier coefficient to vanish (`Cslib.PCP.Hastad.IsFolded.fourierCoeff_empty`).
2. Given tables `B : (γ → Bool) → Bool` and `A : (β → Bool) → Bool` and noise rate `δ`, Håstad's
   3-bit linear test draws `f : γ → Bool` and `g : β → Bool` uniformly and `μ : β → Bool` from the
   `δ`-biased Bernoulli distribution, and checks `B f ^^ A g ^^ A ((f ∘ π) + g + μ) = false`.
3. By Fourier inversion, the convolution theorem, and the noise operator identity on the Boolean
   cube, the correlation of the 3-bit test has the exact Walsh–Fourier expansion
   (`Cslib.PCP.Hastad.hastadLinearCorr_eq_sum`):
   `∑ T : Finset β, (1 - 2 * δ) ^ #T * fourierCoeff F_A T ^ 2 * fourierCoeff F_B (projectSet π T)`,
   where `projectSet π T` is the set of `y : γ` whose fiber in `T` under `π` has odd cardinality.
4. By the Cauchy–Schwarz inequality and Parseval's identity, splitting at degree `k` bounds the
   squared correlation by
   `(1 - 2 * δ) ^ (2 * k) + k ^ 2 * ∑ x, spectralWeight k A x * spectralWeight k B (π x)`
   (`Cslib.PCP.Hastad.hastadLinearCorr_sq_le`), where `spectralWeight k A` is a sub-probability
   distribution on `β`.
5. Converting each 3-bit XOR equation into four E3-CNF clauses (`Cslib.PCP.Hastad.xorThreeCNF`)
   satisfies all `4` clauses when the linear equation holds and `3` of the `4` clauses when it
   fails, mapping linear acceptance probability `1 / 2 + 4 * ε` to E3-CNF clause satisfaction
   `7 / 8 + ε`.

## Main definitions

* `Cslib.Logic.PL.Clause.IsExactThreeDistinct`, `Cslib.Logic.PL.CNF.IsExactThreeDistinct`: clauses
  and CNF formulas with three distinct variables per clause.
* `Cslib.PCP.Hastad.IsFolded`, `Cslib.PCP.Hastad.foldTable`: table folding over `(α → Bool) → Bool`
  (reusing `Cslib.BitString.longCode` for the Long Code).
* `Cslib.PCP.Hastad.projectSet`: mod-2 projection of a subset `T : Finset β` along `π : β → γ`.
* `Cslib.PCP.Hastad.hastadLinearCorr`, `Cslib.PCP.Hastad.hastadLinearProb`: correlation and
  acceptance probability of Håstad's 3-bit linear test on an edge `π : β → γ`.
* `Cslib.PCP.Hastad.spectralWeight`: low-degree Fourier decoding weights on `α`.
* `Cslib.PCP.Hastad.xorThreeCNF`, `Cslib.PCP.Hastad.hastadSATProb`: the 4-clause E3-CNF gadget for
  a 3-bit XOR equation and its expected clause satisfaction probability.
* `Cslib.PCP.Hastad.hastadGraphLinearCorr`, `Cslib.PCP.Hastad.hastadGraphLinearProb`,
  `Cslib.PCP.Hastad.hastadGraphSATProb`: multi-edge test averages over a Label Cover instance.
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
* `Cslib.PCP.Hastad.IsFolded.fourierCoeff_empty`,
  `Cslib.PCP.Hastad.IsFolded.fourierCoeff_of_even`: every even-degree Fourier coefficient of a
  folded table (and in particular at `∅`) vanishes.
* `Cslib.PCP.Hastad.hastadLinearCorr_longCode`, `Cslib.PCP.Hastad.hastadLinearProb_longCode`,
  `Cslib.PCP.Hastad.hastadSATProb_longCode`: completeness `1 - δ` for 3-bit linear tests and
  `1 - δ / 4` for 4-clause E3-CNF tests on valid Long Code tables.
* `Cslib.PCP.Hastad.hastadLinearCorr_eq_sum`: exact Walsh–Fourier expansion of Håstad's 3-bit test
  correlation.
* `Cslib.PCP.Hastad.sum_spectralWeight_le_one`: Parseval bound showing that `spectralWeight k B` is
  a sub-probability distribution on `γ`.
* `Cslib.PCP.Hastad.hastadLinearCorr_sq_le`, `Cslib.PCP.Hastad.hastadGraphLinearCorr_sq_le`:
  single-edge and multi-edge Cauchy–Schwarz + Parseval soundness bounds.
* `Cslib.PCP.Hastad.hastad_gapLabelCover_dichotomy`: two-sided `GapLabelCover` to MAX-E3LIN
  `(1 - δ, 1 / 2 + 4 * ε)` and MAX-E3SAT `(1 - δ / 4, 7 / 8 + ε)` gap reduction theorem.

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 22][AroraBarak09]
* [R. O'Donnell, *Analysis of Boolean Functions*, Chapter 7][ODonnell2014]
-/

@[expose] public section

open Finset
open scoped BigOperators symmDiff

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

/-- **Tightness of the `7 / 8` threshold**: in every exact 3-CNF formula `φ` with three distinct
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

namespace Cslib.PCP.Hastad

open Cslib.BitString Cslib.Logic.PL Cslib.Complexity

variable {α β γ : Type*}

/-! ### The Long Code and table folding -/

/-- In `±1` notation, the Long Code `Cslib.BitString.longCode x` is the singleton Walsh character
`chi ℝ {x}`. -/
theorem signVal_longCode (x : α) (f : α → Bool) :
    signVal (longCode x f) = chi ℝ {x} f :=
  (chi_singleton x f).symm

/-- A Long Code table `B : (α → Bool) → Bool` is **folded** when negating the input function
(`f + fun _ => true`) negates the output bit. -/
def IsFolded (B : (α → Bool) → Bool) : Prop :=
  ∀ f : α → Bool, B (f + fun _ => true) = !B f

/-- Every honest Long Code table `longCode x` is folded. -/
theorem isFolded_longCode (x : α) : IsFolded (longCode x) := fun f => by
  change (f x + true) = !(f x)
  cases f x <;> rfl

/-- **Folding a table** around coordinate `x₀ : α`: accesses `B f` when `f x₀ = false` and
`!B (f + fun _ => true)` when `f x₀ = true`. -/
def foldTable (x₀ : α) (B : (α → Bool) → Bool) (f : α → Bool) : Bool :=
  if f x₀ then !B (f + fun _ => true) else B f

/-- Folding any table produces a folded table. -/
theorem isFolded_foldTable (x₀ : α) (B : (α → Bool) → Bool) : IsFolded (foldTable x₀ B) := by
  intro f
  have h1 : (f + fun _ : α => true) x₀ = !f x₀ := by
    change (f x₀ + true) = !f x₀
    cases f x₀ <;> rfl
  have h2 : (f + fun _ : α => true) + (fun _ : α => true) = f := by
    funext x
    change (f x + true) + true = f x
    cases f x <;> rfl
  simp only [foldTable, h1, h2]
  cases f x₀ <;> simp

/-- Folding an already-folded table leaves it unchanged. -/
theorem IsFolded.foldTable_eq {B : (α → Bool) → Bool} (hB : IsFolded B) (x₀ : α) :
    foldTable x₀ B = B := by
  funext f
  simp only [foldTable, hB f, Bool.not_not, ite_self]

/-- **A folded table has zero empty Fourier coefficient**: its `±1` values cancel in pairs
`f` and `f + fun _ => true`. -/
theorem IsFolded.fourierCoeff_empty [Fintype α] [DecidableEq α] {B : (α → Bool) → Bool}
    (hB : IsFolded B) : fourierCoeff (fun f => signVal (B f)) ∅ = 0 := by
  rw [Cslib.BitString.fourierCoeff_empty]
  have h1 : (𝔼 f : α → Bool, signVal (B f)) =
      𝔼 f : α → Bool, signVal (B ((fun _ => true) + f)) :=
    (Fintype.expect_add_left (fun f : α → Bool => signVal (B f)) (fun _ => true)).symm
  have h2 (f : α → Bool) : signVal (B ((fun _ => true) + f)) = -signVal (B f) := by
    rw [add_comm (fun _ => true) f, hB f, signVal_not]
  simp only [h2, expect_neg_distrib] at h1
  linarith

/-- On a folded table, any character of even cardinality has Fourier coefficient `0`. -/
theorem IsFolded.fourierCoeff_of_even [Fintype α] [DecidableEq α] {B : (α → Bool) → Bool}
    (hB : IsFolded B) {S : Finset α} (hS : Even #S) :
    fourierCoeff (fun f => signVal (B f)) S = 0 := by
  rw [fourierCoeff]
  have hchi : chi ℝ S (fun _ : α => true) = 1 := by
    rw [chi_eq_prod_signVal, prod_const]
    obtain ⟨m, hm⟩ := hS
    rw [hm, pow_add, ← mul_pow]
    norm_num
  have h1 : (𝔼 f : α → Bool, signVal (B f) * chi ℝ S f) =
      𝔼 f : α → Bool, signVal (B ((fun _ => true) + f)) * chi ℝ S ((fun _ => true) + f) :=
    (Fintype.expect_add_left (fun f : α → Bool => signVal (B f) * chi ℝ S f)
      (fun _ => true)).symm
  have h2 (f : α → Bool) :
      signVal (B ((fun _ => true) + f)) * chi ℝ S ((fun _ => true) + f) =
        -(signVal (B f) * chi ℝ S f) := by
    rw [add_comm (fun _ => true) f, hB f, signVal_not, chi_add, hchi]
    ring
  simp only [h2, expect_neg_distrib] at h1
  linarith

/-! ### Mod-2 projection of subsets and character pullback -/

section Projection

variable [Fintype γ] [DecidableEq γ]

/-- The **mod-2 projection** `π₂(T)` of `T : Finset β` along `π : β → γ`: the set of `y : γ`
whose fiber in `T` under `π` has odd cardinality [Håstad][Hastad2001]. -/
def projectSet (π : β → γ) (T : Finset β) : Finset γ :=
  univ.filter fun y => Odd #{x ∈ T | π x = y}

@[simp]
theorem mem_projectSet {π : β → γ} {T : Finset β} {y : γ} :
    y ∈ projectSet π T ↔ Odd #{x ∈ T | π x = y} := by
  simp [projectSet]

@[simp]
theorem projectSet_empty (π : β → γ) : projectSet π ∅ = ∅ := by
  ext y
  simp [projectSet]

/-- Every element of `projectSet π T` lies in the image of `T` under `π`. -/
theorem exists_mem_of_mem_projectSet {π : β → γ} {T : Finset β} {y : γ}
    (hy : y ∈ projectSet π T) : ∃ x ∈ T, π x = y := by
  rw [mem_projectSet] at hy
  have hpos : 0 < #{x ∈ T | π x = y} := Nat.pos_of_ne_zero (by rintro h0; simp [h0] at hy)
  obtain ⟨x, hx⟩ := card_pos.1 hpos
  exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩

theorem projectSet_subset_image (π : β → γ) (T : Finset β) :
    projectSet π T ⊆ T.image π := fun y hy => by
  obtain ⟨x, hx, rfl⟩ := exists_mem_of_mem_projectSet hy
  exact mem_image_of_mem π hx

/-- The mod-2 projection never increases cardinality: `#(projectSet π T) ≤ #T`. -/
theorem card_projectSet_le (π : β → γ) (T : Finset β) : #(projectSet π T) ≤ #T :=
  (card_le_card (projectSet_subset_image π T)).trans card_image_le

variable [DecidableEq β]

/-- Inserting `x ∉ T` toggles `π x` in `projectSet π T`. -/
theorem projectSet_insert (π : β → γ) {x : β} {T : Finset β} (hx : x ∉ T) :
    projectSet π (insert x T) = symmDiff (projectSet π T) {π x} := by
  ext y
  rw [mem_projectSet, mem_symmDiff, mem_projectSet, mem_singleton, filter_insert]
  by_cases hxy : π x = y
  · subst hxy
    have hx' : x ∉ {z ∈ T | π z = π x} := fun h => hx (mem_filter.1 h).1
    simp only [↓reduceIte, card_insert_of_notMem hx', Nat.odd_add_one, not_true_eq_false,
      and_false, true_and, false_or]
  · have hyx : y ≠ π x := Ne.symm hxy
    simp [hxy, hyx]

omit [DecidableEq β] in
/-- **Pulling a character back along `π` projects the frequency set by `projectSet π`**:
`chi ℝ T (f ∘ π) = chi ℝ (projectSet π T) f`. -/
theorem chi_comp_eq_chi_projectSet (π : β → γ) (T : Finset β) (f : γ → Bool) :
    chi ℝ T (f ∘ π) = chi ℝ (projectSet π T) f := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    rw [projectSet_insert π hx, ← chi_mul_chi, chi_singleton, ← ih, chi_eq_prod_signVal,
      prod_insert hx, ← chi_eq_prod_signVal, Function.comp_apply, mul_comm]

end Projection

/-! ### Håstad's 3-bit linear test and its Fourier expansion -/

section LinearTest

variable [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The **correlation** of Håstad's 3-bit linear test on a projection `π : β → γ` at noise rate `δ`
between tables `B : (γ → Bool) → Bool` and `A : (β → Bool) → Bool` [Håstad, Section 5][Hastad2001]:
the expected product of the `±1` signs of `B f`, `A g`, and `A ((f ∘ π) + g + μ)` over uniform
`f : γ → Bool`, uniform `g : β → Bool`, and `δ`-biased Bernoulli noise `μ : β → Bool`. -/
noncomputable def hastadLinearCorr (π : β → γ) (δ : ℝ) (B : (γ → Bool) → Bool)
    (A : (β → Bool) → Bool) : ℝ :=
  𝔼 f : γ → Bool, 𝔼 g : β → Bool,
    bernoulliAverage δ fun μ =>
      signVal (B f) * signVal (A g) * signVal (A ((f ∘ π) + g + μ))

/-- The **acceptance probability** of Håstad's 3-bit linear test: the probability that
`(B f ^^ A g ^^ A ((f ∘ π) + g + μ)) = false` under uniform `f, g` and `δ`-biased noise `μ`. -/
noncomputable def hastadLinearProb (π : β → γ) (δ : ℝ) (B : (γ → Bool) → Bool)
    (A : (β → Bool) → Bool) : ℝ :=
  𝔼 f : γ → Bool, 𝔼 g : β → Bool,
    bernoulliAverage δ fun μ =>
      if (B f ^^ A g ^^ A ((f ∘ π) + g + μ)) = false then 1 else 0

/-- The acceptance probability of Håstad's 3-bit linear test is
`1 / 2 + 1 / 2 * hastadLinearCorr π δ B A`. -/
theorem hastadLinearProb_eq_add_hastadLinearCorr (π : β → γ) (δ : ℝ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) :
    hastadLinearProb π δ B A = 1 / 2 + 1 / 2 * hastadLinearCorr π δ B A := by
  have h (b₁ b₂ b₃ : Bool) :
      (if (b₁ ^^ b₂ ^^ b₃) = false then (1 : ℝ) else 0) =
        1 / 2 + 1 / 2 * (signVal b₁ * signVal b₂ * signVal b₃) := by
    cases b₁ <;> cases b₂ <;> cases b₃ <;> simp only [signVal] <;> norm_num
  simp only [hastadLinearProb, hastadLinearCorr, h, bernoulliAverage_add, bernoulliAverage_const,
    bernoulliAverage_const_mul, expect_add_distrib, Fintype.expect_const, mul_expect]

/-- **Completeness of Håstad's 3-bit linear test (correlation)**: on matching Long Code tables
`longCode (π x)` and `longCode x`, the correlation is `1 - 2 * δ`. -/
theorem hastadLinearCorr_longCode (π : β → γ) (δ : ℝ) (x : β) :
    hastadLinearCorr π δ (longCode (π x)) (longCode x) = 1 - 2 * δ := by
  have hsign (f : γ → Bool) (g μ : β → Bool) :
      signVal (longCode (π x) f) * signVal (longCode x g) *
        signVal (longCode x ((f ∘ π) + g + μ)) = chi ℝ {x} μ := by
    rw [chi_singleton]
    change signVal (f (π x)) * signVal (g x) * signVal (f (π x) + g x + μ x) = signVal (μ x)
    cases f (π x) <;> cases g x <;> cases μ x <;> simp [signVal, Bool.add_eq_xor]
  simp only [hastadLinearCorr, hsign, bernoulliAverage_chi, card_singleton, pow_one,
    Fintype.expect_const]

/-- **Completeness of Håstad's 3-bit linear test (probability)**: matching Long Code tables
`longCode (π x)` and `longCode x` pass the test with probability `1 - δ`. -/
theorem hastadLinearProb_longCode (π : β → γ) (δ : ℝ) (x : β) :
    hastadLinearProb π δ (longCode (π x)) (longCode x) = 1 - δ := by
  rw [hastadLinearProb_eq_add_hastadLinearCorr, hastadLinearCorr_longCode]
  ring

/-- **Walsh–Fourier expansion of Håstad's 3-bit linear test** [Håstad, Lemma 5.1][Hastad2001]:
the correlation equals
`∑ T : Finset β, (1 - 2 * δ) ^ #T * fourierCoeff F_A T ^ 2 * fourierCoeff F_B (projectSet π T)`. -/
theorem hastadLinearCorr_eq_sum (π : β → γ) (δ : ℝ) (B : (γ → Bool) → Bool)
    (A : (β → Bool) → Bool) :
    hastadLinearCorr π δ B A =
      ∑ T : Finset β,
        (1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
          fourierCoeff (fun f => signVal (B f)) (projectSet π T) := by
  have hδ : (1 - (1 - 2 * δ)) / 2 = δ := by ring
  have hinner (f : γ → Bool) (g : β → Bool) :
      (bernoulliAverage δ fun μ =>
          signVal (B f) * signVal (A g) * signVal (A ((f ∘ π) + g + μ))) =
        signVal (B f) *
          (signVal (A g) * noiseOp (1 - 2 * δ) (fun h => signVal (A h)) ((f ∘ π) + g)) := by
    simp only [mul_assoc, bernoulliAverage_const_mul, noiseOp, hδ]
  have hconv (f : γ → Bool) :
      (𝔼 g : β → Bool,
          signVal (B f) *
            (signVal (A g) * noiseOp (1 - 2 * δ) (fun h => signVal (A h)) ((f ∘ π) + g))) =
        signVal (B f) * ∑ T : Finset β,
          (1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            chi ℝ (projectSet π T) f := by
    rw [← mul_expect]
    congr 1
    change convolution (fun g => signVal (A g))
      (noiseOp (1 - 2 * δ) (fun h => signVal (A h))) (f ∘ π) = _
    rw [← sum_fourierCoeff_mul_chi
      (convolution (fun g => signVal (A g)) (noiseOp (1 - 2 * δ) (fun h => signVal (A h))))
      (f ∘ π)]
    refine sum_congr rfl fun T _ => ?_
    rw [fourierCoeff_convolution, fourierCoeff_noiseOp, chi_comp_eq_chi_projectSet]
    ring
  simp only [hastadLinearCorr, hinner, hconv, mul_sum]
  rw [expect_sum_comm]
  refine sum_congr rfl fun T _ => ?_
  have hterm (f : γ → Bool) :
      signVal (B f) *
          ((1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            chi ℝ (projectSet π T) f) =
        ((1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2) *
          (signVal (B f) * chi ℝ (projectSet π T) f) := by
    ring
  simp only [hterm, ← mul_expect]
  rfl

end LinearTest

/-! ### Spectral decoding weights and Cauchy–Schwarz soundness bound -/

section Soundness

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- Every Fourier coefficient of a `±1`-valued Boolean function has square at most `1`. -/
theorem fourierCoeff_sq_signVal_le_one (B : (α → Bool) → Bool) (S : Finset α) :
    fourierCoeff (fun f => signVal (B f)) S ^ 2 ≤ 1 := by
  rw [← sum_fourierCoeff_sq_signVal B]
  exact single_le_sum (fun T _ => sq_nonneg _) (mem_univ S)

/-- The **low-degree spectral decoding weight** of `x : α` for table `A : (α → Bool) → Bool` at
degree cutoff `k`: `∑_{T : #T < k, x ∈ T} fourierCoeff F_A T ^ 2 / #T`
[Håstad, Proof of Lemma 5.2][Hastad2001]. -/
noncomputable def spectralWeight (k : ℕ) (A : (α → Bool) → Bool) (x : α) : ℝ :=
  ∑ T ∈ univ.filter (fun T : Finset α => #T < k ∧ x ∈ T),
    fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T

theorem spectralWeight_nonneg (k : ℕ) (A : (α → Bool) → Bool) (x : α) :
    0 ≤ spectralWeight k A x :=
  sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **By Parseval's identity, the spectral decoding weights form a sub-probability distribution**:
`∑ x, spectralWeight k A x ≤ 1`. -/
theorem sum_spectralWeight_le_one (k : ℕ) (A : (α → Bool) → Bool) :
    ∑ x : α, spectralWeight k A x ≤ 1 := by
  simp only [spectralWeight, sum_filter]
  rw [sum_comm]
  rw [← sum_fourierCoeff_sq_signVal A]
  refine sum_le_sum fun T _ => ?_
  by_cases hTk : #T < k
  · by_cases hT0 : T = ∅
    · subst hT0
      simp only [notMem_empty, and_false, ↓reduceIte, sum_const_zero]
      exact sq_nonneg _
    · have hpos : (0 : ℝ) < #T := by
        exact_mod_cast card_pos.2 (nonempty_iff_ne_empty.2 hT0)
      have hsum :
          (∑ x : α, if #T < k ∧ x ∈ T then
            fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) =
          ∑ x ∈ T, fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T := by
        rw [← sum_filter]
        refine sum_congr ?_ fun _ _ => rfl
        ext x
        simp [hTk]
      rw [hsum, sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne']
  · simp only [hTk, false_and, ↓reduceIte, sum_const_zero]
    exact sq_nonneg _

/-- Low-degree terms in the Cauchy–Schwarz bound are controlled by the collision probability of the
spectral decoding distributions along `π`. -/
theorem sum_lowDegree_fourierCoeff_sq_le (π : β → γ) (k : ℕ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) :
    (∑ T ∈ univ.filter (fun T : Finset β => #T < k ∧ projectSet π T ≠ ∅),
      fourierCoeff (fun g => signVal (A g)) T ^ 2 *
        fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2) ≤
      (k : ℝ) ^ 2 * ∑ x : β, spectralWeight k A x * spectralWeight k B (π x) := by
  have hterm (T : Finset β) :
      (if #T < k ∧ projectSet π T ≠ ∅ then
        fourierCoeff (fun g => signVal (A g)) T ^ 2 *
          fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2
      else 0) ≤
        (k : ℝ) ^ 2 * ∑ x : β,
          (if #T < k ∧ x ∈ T then fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) *
            spectralWeight k B (π x) := by
    split_ifs with hT
    · obtain ⟨hTk, hne⟩ := hT
      obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hne
      obtain ⟨x₀, hx₀T, rfl⟩ := exists_mem_of_mem_projectSet hy
      have hcardT_pos : (0 : ℝ) < #T := by
        exact_mod_cast card_pos.2 ⟨x₀, hx₀T⟩
      have hcardT_le : (#T : ℝ) ≤ k := by exact_mod_cast hTk.le
      have hcardS_pos : (0 : ℝ) < #(projectSet π T) := by
        exact_mod_cast card_pos.2 ⟨π x₀, hy⟩
      have hcardS_lt : #(projectSet π T) < k := (card_projectSet_le π T).trans_lt hTk
      have hcardS_le : (#(projectSet π T) : ℝ) ≤ k := by exact_mod_cast hcardS_lt.le
      have hB_le :
          fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 / #(projectSet π T) ≤
            spectralWeight k B (π x₀) := by
        rw [spectralWeight]
        refine single_le_sum
          (f := fun S : Finset γ => fourierCoeff (fun f => signVal (B f)) S ^ 2 / #S)
          (fun S _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_
        simp [hcardS_lt, hy]
      have hB_le' :
          fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 ≤
            (k : ℝ) * spectralWeight k B (π x₀) := by
        have h1 : fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 =
            #(projectSet π T) *
              (fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 / #(projectSet π T)) := by
          rw [mul_div_cancel₀ _ hcardS_pos.ne']
        conv_lhs => rw [h1]
        exact mul_le_mul hcardS_le hB_le (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
          (Nat.cast_nonneg k)
      have hA_le' :
          fourierCoeff (fun g => signVal (A g)) T ^ 2 ≤
            (k : ℝ) * (fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) := by
        have h1 : fourierCoeff (fun g => signVal (A g)) T ^ 2 =
            #T * (fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) := by
          rw [mul_div_cancel₀ _ hcardT_pos.ne']
        conv_lhs => rw [h1]
        exact mul_le_mul_of_nonneg_right hcardT_le (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      have hprod :
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
              fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 ≤
            (k : ℝ) ^ 2 *
              ((fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) *
                spectralWeight k B (π x₀)) := by
        calc fourierCoeff (fun g => signVal (A g)) T ^ 2 *
              fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2
          _ ≤ ((k : ℝ) * (fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T)) *
                ((k : ℝ) * spectralWeight k B (π x₀)) :=
            mul_le_mul hA_le' hB_le' (sq_nonneg _) (by positivity)
          _ = (k : ℝ) ^ 2 *
                ((fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) *
                  spectralWeight k B (π x₀)) := by ring
      refine hprod.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
      have hsingle := single_le_sum
        (f := fun x : β =>
          (if #T < k ∧ x ∈ T then fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) *
            spectralWeight k B (π x))
        (fun x _ => by
          split_ifs
          · exact mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
              (spectralWeight_nonneg k B (π x))
          · simp)
        (mem_univ x₀)
      simpa [hTk, hx₀T] using hsingle
    · refine mul_nonneg (sq_nonneg _) (sum_nonneg fun x _ => ?_)
      split_ifs
      · exact mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
          (spectralWeight_nonneg k B (π x))
      · simp
  rw [sum_filter]
  calc (∑ T : Finset β,
        if #T < k ∧ projectSet π T ≠ ∅ then
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2
        else 0)
    _ ≤ ∑ T : Finset β, (k : ℝ) ^ 2 * ∑ x : β,
          (if #T < k ∧ x ∈ T then fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) *
            spectralWeight k B (π x) := sum_le_sum fun T _ => hterm T
    _ = (k : ℝ) ^ 2 * ∑ x : β, spectralWeight k A x * spectralWeight k B (π x) := by
      rw [← mul_sum, sum_comm]
      congr 1
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_mul]
      congr 1
      rw [spectralWeight, sum_filter]

/-- **Cauchy–Schwarz and Parseval soundness bound for Håstad's 3-bit linear test**
[Håstad, Lemma 5.2][Hastad2001]: for any folded table `B`, any table `A`, noise rate
`0 ≤ δ ≤ 1 / 2`, and degree cutoff `k`, the squared correlation `hastadLinearCorr π δ B A ^ 2` is
at most `(1 - 2 * δ) ^ (2 * k) + k ^ 2 * ∑ x, spectralWeight k A x * spectralWeight k B (π x)`. -/
theorem hastadLinearCorr_sq_le (π : β → γ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (k : ℕ) {B : (γ → Bool) → Bool} (hB : IsFolded B) (A : (β → Bool) → Bool) :
    hastadLinearCorr π δ B A ^ 2 ≤
      (1 - 2 * δ) ^ (2 * k) +
        (k : ℝ) ^ 2 * ∑ x : β, spectralWeight k A x * spectralWeight k B (π x) := by
  have hcs :
      hastadLinearCorr π δ B A ^ 2 ≤
        ∑ T : Finset β,
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2 := by
    rw [hastadLinearCorr_eq_sum]
    have hrewrite :
        (∑ T : Finset β,
          (1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            fourierCoeff (fun f => signVal (B f)) (projectSet π T)) =
        ∑ T : Finset β,
          fourierCoeff (fun g => signVal (A g)) T *
            (fourierCoeff (fun g => signVal (A g)) T *
              ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T))) :=
      sum_congr rfl fun T _ => by ring
    rw [hrewrite]
    have h1 := sum_mul_sq_le_sq_mul_sq univ
      (fun T : Finset β => fourierCoeff (fun g => signVal (A g)) T)
      (fun T : Finset β =>
        fourierCoeff (fun g => signVal (A g)) T *
          ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)))
    rw [sum_fourierCoeff_sq_signVal, one_mul] at h1
    refine h1.trans_eq (sum_congr rfl fun T _ => by ring)
  have hsplit :
      (∑ T : Finset β,
        fourierCoeff (fun g => signVal (A g)) T ^ 2 *
          ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2) ≤
      (1 - 2 * δ) ^ (2 * k) * (∑ T : Finset β, fourierCoeff (fun g => signVal (A g)) T ^ 2) +
        ∑ T ∈ univ.filter (fun T : Finset β => #T < k ∧ projectSet π T ≠ ∅),
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 := by
    rw [mul_sum, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun T _ => ?_
    have hρ0 : 0 ≤ 1 - 2 * δ := by linarith
    have hρ1 : 1 - 2 * δ ≤ 1 := by linarith
    by_cases hTk : #T < k
    · by_cases hne : projectSet π T ≠ ∅
      · simp only [hTk, hne, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        have hpow : ((1 - 2 * δ) ^ #T) ^ 2 ≤ 1 := by
          rw [← pow_mul]
          exact pow_le_one₀ hρ0 hρ1
        have hnonneg : 0 ≤ (1 - 2 * δ) ^ (2 * k) * fourierCoeff (fun g => signVal (A g)) T ^ 2 :=
          mul_nonneg (pow_nonneg hρ0 _) (sq_nonneg _)
        have hle1 :
            fourierCoeff (fun g => signVal (A g)) T ^ 2 *
                ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2 ≤
              fourierCoeff (fun g => signVal (A g)) T ^ 2 *
                fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 := by
          rw [mul_pow, ← mul_assoc, mul_comm (fourierCoeff _ T ^ 2), mul_assoc]
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hpow (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        linarith
      · push Not at hne
        simp only [hTk, hne, ne_eq, not_true_eq_false, and_false, ↓reduceIte, add_zero,
          hB.fourierCoeff_empty, mul_zero, sq (0 : ℝ)]
        exact mul_nonneg (pow_nonneg hρ0 _) (sq_nonneg _)
    · simp only [hTk, false_and, ↓reduceIte, add_zero]
      have hkT : 2 * k ≤ #T * 2 := by omega
      have hpow : ((1 - 2 * δ) ^ #T) ^ 2 ≤ (1 - 2 * δ) ^ (2 * k) := by
        rw [← pow_mul]
        exact pow_le_pow_of_le_one hρ0 hρ1 hkT
      have hFB : fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 ≤ 1 :=
        fourierCoeff_sq_signVal_le_one B (projectSet π T)
      calc fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2
        _ = fourierCoeff (fun g => signVal (A g)) T ^ 2 *
              (((1 - 2 * δ) ^ #T) ^ 2 *
                fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2) := by ring
        _ ≤ fourierCoeff (fun g => signVal (A g)) T ^ 2 * ((1 - 2 * δ) ^ (2 * k) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact mul_le_mul hpow hFB (sq_nonneg _) (pow_nonneg hρ0 _)
        _ = (1 - 2 * δ) ^ (2 * k) * fourierCoeff (fun g => signVal (A g)) T ^ 2 := by ring
  rw [sum_fourierCoeff_sq_signVal, mul_one] at hsplit
  have hlow := sum_lowDegree_fourierCoeff_sq_le π k B A
  linarith

end Soundness

/-! ### Four-clause E3-CNF gadget for 3-bit XOR equations -/

section Gadget

variable {V : Type*}

/-- The **4-clause E3-CNF gadget** [Håstad, Section 2][Hastad2001] expressing the 3-bit linear
equation `(σ v₁ ^^ σ v₂) ^^ σ v₃ = b`: each of the four assignments to `(v₁, v₂, v₃)` with
`(σ v₁ ^^ σ v₂) ^^ σ v₃ = !b` is forbidden by a distinct 3-literal clause. -/
def xorThreeCNF (v₁ v₂ v₃ : V) (b : Bool) : CNF V :=
  [ [⟨v₁, true⟩, ⟨v₂, true⟩, ⟨v₃, b⟩],
    [⟨v₁, true⟩, ⟨v₂, false⟩, ⟨v₃, !b⟩],
    [⟨v₁, false⟩, ⟨v₂, true⟩, ⟨v₃, !b⟩],
    [⟨v₁, false⟩, ⟨v₂, false⟩, ⟨v₃, b⟩] ]

/-- The 4-clause XOR gadget has exactly 4 clauses. -/
@[simp]
theorem length_xorThreeCNF (v₁ v₂ v₃ : V) (b : Bool) :
    (xorThreeCNF v₁ v₂ v₃ b).length = 4 := rfl

/-- When `v₁, v₂, v₃` are distinct variables, every clause of `xorThreeCNF v₁ v₂ v₃ b` has
3 literals on 3 distinct variables (`CNF.IsExactThreeDistinct`). -/
theorem isExactThreeDistinct_xorThreeCNF {v₁ v₂ v₃ : V} (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃)
    (h23 : v₂ ≠ v₃) (b : Bool) :
    (xorThreeCNF v₁ v₂ v₃ b).IsExactThreeDistinct := by
  intro C hC
  simp only [xorThreeCNF, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, by simp [List.nodup_cons, h12, h13, h23]⟩

/-- The 4-clause XOR gadget evaluates to `true` under `σ` iff `(σ v₁ ^^ σ v₂) ^^ σ v₃ = b`. -/
theorem eval_xorThreeCNF (v₁ v₂ v₃ : V) (b : Bool) (σ : V → Bool) :
    (xorThreeCNF v₁ v₂ v₃ b).eval σ = (((σ v₁ ^^ σ v₂) ^^ σ v₃) == b) := by
  simp only [xorThreeCNF, CNF.eval, List.all_cons, List.all_nil,
    Clause.eval, List.any_cons, List.any_nil, Literal.eval]
  cases σ v₁ <;> cases σ v₂ <;> cases σ v₃ <;> cases b <;> rfl

/-- **Exact clause-violation count of the 4-clause XOR gadget**: an assignment `σ` violates `0`
of the 4 clauses when `(σ v₁ ^^ σ v₂) ^^ σ v₃ = b` (all 4 clauses satisfied) and violates
exactly `1` of the 4 clauses when `(σ v₁ ^^ σ v₂) ^^ σ v₃ ≠ b` (3 of the 4 clauses satisfied). -/
theorem countUnsat_xorThreeCNF (v₁ v₂ v₃ : V) (b : Bool) (σ : V → Bool) :
    (xorThreeCNF v₁ v₂ v₃ b).countUnsat σ =
      if ((σ v₁ ^^ σ v₂) ^^ σ v₃) == b then 0 else 1 := by
  simp only [xorThreeCNF, CNF.countUnsat, List.countP_cons, List.countP_nil,
    Clause.eval, List.any_cons, List.any_nil, Literal.eval]
  obtain h1 | h1 := Bool.eq_false_or_eq_true (σ v₁) <;>
    obtain h2 | h2 := Bool.eq_false_or_eq_true (σ v₂) <;>
    obtain h3 | h3 := Bool.eq_false_or_eq_true (σ v₃) <;>
    cases b <;> simp [h1, h2, h3]

/-- The fraction of satisfied clauses in `xorThreeCNF v₁ v₂ v₃ false` is `1` (`4 / 4`) when
`(σ v₁ ^^ σ v₂) == σ v₃` and `3 / 4` otherwise:
`1 - countUnsat / 4 = 3 / 4 + 1 / 4 * (if (σ v₁ ^^ σ v₂) == σ v₃ then 1 else 0)`. -/
theorem one_sub_countUnsat_xorThreeCNF_div_four (v₁ v₂ v₃ : V) (σ : V → Bool) :
    1 - ((xorThreeCNF v₁ v₂ v₃ false).countUnsat σ : ℝ) / 4 =
      3 / 4 + 1 / 4 * (if (σ v₁ ^^ σ v₂) == σ v₃ then 1 else 0) := by
  rw [countUnsat_xorThreeCNF]
  obtain h1 | h1 := Bool.eq_false_or_eq_true (σ v₁) <;>
    obtain h2 | h2 := Bool.eq_false_or_eq_true (σ v₂) <;>
    obtain h3 | h3 := Bool.eq_false_or_eq_true (σ v₃) <;>
    simp only [h1, h2, h3] <;> norm_num

variable {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The **expected fraction of satisfied clauses in Håstad's 4-clause E3-CNF test** on edge
`π : β → γ` with noise rate `δ`: each 3-bit linear test `(B f ^^ A g) == A ((f ∘ π) + g + μ)` is
encoded by the 4-clause E3-CNF gadget `xorThreeCNF`, which satisfies all `4/4` clauses when the
linear test accepts and `3/4` clauses when the linear test rejects. -/
noncomputable def hastadSATProb (π : β → γ) (δ : ℝ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) : ℝ :=
  3 / 4 + 1 / 4 * hastadLinearProb π δ B A

/-- `hastadSATProb` expressed in terms of `hastadLinearCorr`:
`hastadSATProb π δ B A = 7 / 8 + 1 / 8 * hastadLinearCorr π δ B A`. -/
theorem hastadSATProb_eq_add_hastadLinearCorr (π : β → γ) (δ : ℝ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) :
    hastadSATProb π δ B A = 7 / 8 + 1 / 8 * hastadLinearCorr π δ B A := by
  rw [hastadSATProb, hastadLinearProb_eq_add_hastadLinearCorr]
  ring

/-- **Completeness of Håstad's 4-clause E3-CNF test**: on valid Long Code tables
`B = longCode (π x)` and `A = longCode x`, the expected fraction of satisfied clauses is
`1 - δ / 4`. -/
theorem hastadSATProb_longCode (π : β → γ) (δ : ℝ) (x : β) :
    hastadSATProb π δ (longCode (π x)) (longCode x) = 1 - δ / 4 := by
  rw [hastadSATProb, hastadLinearProb_longCode]
  ring

/-- Bounding `hastadLinearCorr π δ B A ≤ 8 * ε` bounds the linear test acceptance by
`1 / 2 + 4 * ε`. -/
theorem hastadLinearProb_le_of_hastadLinearCorr_le (π : β → γ) (δ : ℝ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) {ε : ℝ}
    (h : hastadLinearCorr π δ B A ≤ 8 * ε) :
    hastadLinearProb π δ B A ≤ 1 / 2 + 4 * ε := by
  rw [hastadLinearProb_eq_add_hastadLinearCorr]
  linarith

/-- Bounding `hastadLinearCorr π δ B A ≤ 8 * ε` bounds the E3-CNF test clause satisfaction by
`7 / 8 + ε`. -/
theorem hastadSATProb_le_of_hastadLinearCorr_le (π : β → γ) (δ : ℝ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) {ε : ℝ}
    (h : hastadLinearCorr π δ B A ≤ 8 * ε) :
    hastadSATProb π δ B A ≤ 7 / 8 + ε := by
  rw [hastadSATProb_eq_add_hastadLinearCorr]
  linarith

end Gadget

/-! ### Multi-edge Label Cover decoding and soundness -/

section LabelCoverSoundness

open Cslib.Complexity Cslib.PCP.Encoded

/-- **Deterministic vertex-choice lemma**: given a vertex map `v : I → ℕ`, nonnegative payoffs
`W : I → α → ℝ`, and vertex-wise sub-probability distributions `p : ℕ → α → ℝ` (`0 ≤ p u a` and
`∑ a, p u a ≤ 1`), choosing the best label at each vertex produces a deterministic assignment
`f : ℕ → α` whose payoff is at least the expected payoff under `p`. -/
theorem exists_choice_sum_le {I α : Type*} [Fintype I] [Fintype α] [Nonempty α]
    (v : I → ℕ) (W : I → α → ℝ) (hW : ∀ i a, 0 ≤ W i a)
    (p : ℕ → α → ℝ) (hp0 : ∀ u a, 0 ≤ p u a) (hp1 : ∀ u, ∑ a : α, p u a ≤ 1) :
    ∃ f : ℕ → α, (∑ i : I, ∑ a : α, p (v i) a * W i a) ≤ ∑ i : I, W i (f (v i)) := by
  let U (u : ℕ) (a : α) : ℝ := ∑ i : I, if v i = u then W i a else 0
  have hmax (u : ℕ) : ∃ b : α, ∀ a : α, U u a ≤ U u b := by
    obtain ⟨b, _, hb⟩ := univ.exists_max_image (U u) univ_nonempty
    exact ⟨b, fun a => hb a (mem_univ a)⟩
  choose f hf using hmax
  refine ⟨f, ?_⟩
  have hpart (F : I → ℕ → ℝ) :
      (∑ i : I, F i (v i)) =
        ∑ u ∈ univ.image v, ∑ i : I, if v i = u then F i u else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    simp [sum_ite_eq, mem_image_of_mem v (mem_univ i)]
  rw [hpart (fun i u => ∑ a : α, p u a * W i a), hpart (fun i u => W i (f u))]
  refine sum_le_sum fun u _ => ?_
  have hU_nonneg : 0 ≤ U u (f u) := by
    refine sum_nonneg fun i _ => ?_
    split_ifs
    · exact hW i (f u)
    · rfl
  have hswap :
      (∑ i : I, if v i = u then (∑ a : α, p u a * W i a) else 0) =
        ∑ a : α, p u a * U u a := by
    trans ∑ i : I, ∑ a : α, if v i = u then p u a * W i a else 0
    · refine sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · rw [sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
  rw [hswap]
  calc ∑ a : α, p u a * U u a
    _ ≤ ∑ a : α, p u a * U u (f u) :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hf u a) (hp0 u a)
    _ = (∑ a : α, p u a) * U u (f u) := by rw [← sum_mul]
    _ ≤ 1 * U u (f u) := mul_le_mul_of_nonneg_right (hp1 u) hU_nonneg
    _ = ∑ i : I, if v i = u then W i (f u) else 0 := one_mul _

/-- Any deterministic labelling `(ℓ, r)` of a Label Cover instance `g` satisfies at most
`g.edges.length * (1 - (g.toGraph projectionEval).unsatVal)` edges. -/
theorem sum_satisfies_le_unsatVal {β γ : Type} [DecidableEq γ]
    (g : Graph (β → γ)) (ℓ : ℕ → β) (r : ℕ → γ) :
    (∑ i : Fin g.edges.length,
      if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = r (g.edges.get i).dst then (1 : ℝ)
      else 0) ≤
    g.edges.length * (1 - (g.toGraph projectionEval).unsatVal) := by
  let σ : ℕ → β × γ := fun v => (ℓ v, r v)
  have hcompl (i : Fin g.edges.length) :
      (if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = r (g.edges.get i).dst then (1 : ℝ)
        else 0) +
      (if i ∈ (g.toGraph projectionEval).unsatEdges σ then (1 : ℝ) else 0) = 1 := by
    simp only [ConstraintGraph.mem_unsatEdges, satisfies_toGraph_projectionEval_iff, σ]
    split_ifs <;> ring
  have hsum :
      (∑ i : Fin g.edges.length,
        if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = r (g.edges.get i).dst then (1 : ℝ)
        else 0) +
      #((g.toGraph projectionEval).unsatEdges σ) = g.edges.length := by
    have h1 := sum_congr (s₁ := univ) rfl (fun i _ => hcompl i)
    have h2 :
        (∑ i : Fin g.edges.length,
          if i ∈ (g.toGraph projectionEval).unsatEdges σ then (1 : ℝ) else 0) =
        #((g.toGraph projectionEval).unsatEdges σ) := by
      rw [sum_boole, filter_mem_eq_inter, univ_inter]
    rw [sum_add_distrib, h2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1
    exact h1
  have hcard := (g.toGraph projectionEval).card_mul_unsatFrac σ
  simp only [Fintype.card_fin] at hcard
  have hle : (g.edges.length : ℝ) * (g.toGraph projectionEval).unsatVal ≤
      #((g.toGraph projectionEval).unsatEdges σ) := by
    rw [← hcard]
    exact mul_le_mul_of_nonneg_left ((g.toGraph projectionEval).unsatVal_le σ) (Nat.cast_nonneg _)
  linarith

variable {β γ : Type} [Fintype β] [DecidableEq β] [Nonempty β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ]

/-- **Spectral decoding of Label Cover tables**: for any Label Cover instance `g : Graph (β → γ)`,
degree cutoff `k`, left tables `A`, and right tables `B`, there exist deterministic labellings
`ℓ : ℕ → β` and `r : ℕ → γ` whose number of satisfied edges is at least the total spectral weight
agreement across all edges of `g`. -/
theorem exists_labelling_of_spectralWeight (g : Graph (β → γ)) (k : ℕ)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) :
    ∃ (ℓ : ℕ → β) (r : ℕ → γ),
      (∑ i : Fin g.edges.length, ∑ x : β,
        spectralWeight k (A (g.edges.get i).src) x *
          spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x)) ≤
      ∑ i : Fin g.edges.length,
        if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = r (g.edges.get i).dst then 1
        else 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_choice_sum_le
    (fun i : Fin g.edges.length => (g.edges.get i).src)
    (fun i x => spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x))
    (fun i x => spectralWeight_nonneg k _ _)
    (fun u x => spectralWeight k (A u) x)
    (fun u x => spectralWeight_nonneg k _ _)
    (fun u => sum_spectralWeight_le_one k (A u))
  obtain ⟨r, hr⟩ := exists_choice_sum_le
    (fun i : Fin g.edges.length => (g.edges.get i).dst)
    (fun i y => if (g.edges.get i).constraint (ℓ (g.edges.get i).src) = y then (1 : ℝ) else 0)
    (fun i y => by split_ifs <;> positivity)
    (fun w y => spectralWeight k (B w) y)
    (fun w y => spectralWeight_nonneg k _ _)
    (fun w => sum_spectralWeight_le_one k (B w))
  refine ⟨ℓ, r, hℓ.trans (le_trans ?_ hr)⟩
  refine le_of_eq (sum_congr rfl fun i _ => ?_)
  simp [mul_ite, mul_one, mul_zero, sum_ite_eq]

/-- Total spectral weight agreement across the edges of a Label Cover instance `g` is at most
`g.edges.length * (1 - (g.toGraph projectionEval).unsatVal)`. -/
theorem sum_spectralWeight_le_unsatVal (g : Graph (β → γ)) (k : ℕ)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) :
    (∑ i : Fin g.edges.length, ∑ x : β,
      spectralWeight k (A (g.edges.get i).src) x *
        spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x)) ≤
    g.edges.length * (1 - (g.toGraph projectionEval).unsatVal) := by
  obtain ⟨ℓ, r, hℓr⟩ := exists_labelling_of_spectralWeight g k B A
  exact hℓr.trans (sum_satisfies_le_unsatVal g ℓ r)

/-- Average correlation of Håstad's 3-bit linear test across the edges of a Label Cover instance
`g : Graph (β → γ)`. -/
noncomputable def hastadGraphLinearCorr (g : Graph (β → γ)) (δ : ℝ)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) : ℝ :=
  𝔼 i : Fin g.edges.length,
    hastadLinearCorr (g.edges.get i).constraint δ (B (g.edges.get i).dst) (A (g.edges.get i).src)

/-- Average acceptance probability of Håstad's 3-bit linear test across the edges of a Label Cover
instance `g : Graph (β → γ)`. -/
noncomputable def hastadGraphLinearProb (g : Graph (β → γ)) (δ : ℝ)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) : ℝ :=
  𝔼 i : Fin g.edges.length,
    hastadLinearProb (g.edges.get i).constraint δ (B (g.edges.get i).dst) (A (g.edges.get i).src)

/-- Average clause satisfaction probability of Håstad's 4-clause E3-CNF test across the edges of a
Label Cover instance `g : Graph (β → γ)`. -/
noncomputable def hastadGraphSATProb (g : Graph (β → γ)) (δ : ℝ)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) : ℝ :=
  𝔼 i : Fin g.edges.length,
    hastadSATProb (g.edges.get i).constraint δ (B (g.edges.get i).dst) (A (g.edges.get i).src)

omit [Nonempty β] [Nonempty γ] in
/-- For a Label Cover instance with at least one edge,
`hastadGraphLinearProb g δ B A = 1 / 2 + 1 / 2 * hastadGraphLinearCorr g δ B A`. -/
theorem hastadGraphLinearProb_eq_add_hastadGraphLinearCorr {g : Graph (β → γ)}
    (hg : g.edges ≠ []) (δ : ℝ) (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) :
    hastadGraphLinearProb g δ B A = 1 / 2 + 1 / 2 * hastadGraphLinearCorr g δ B A := by
  have hne : (univ : Finset (Fin g.edges.length)).Nonempty :=
    univ_nonempty_iff.2 ⟨⟨0, List.length_pos_of_ne_nil hg⟩⟩
  simp only [hastadGraphLinearProb, hastadGraphLinearCorr, hastadLinearProb_eq_add_hastadLinearCorr,
    expect_add_distrib, expect_const hne, ← mul_expect]

omit [Nonempty β] [Nonempty γ] in
/-- For a Label Cover instance with at least one edge,
`hastadGraphSATProb g δ B A = 7 / 8 + 1 / 8 * hastadGraphLinearCorr g δ B A`. -/
theorem hastadGraphSATProb_eq_add_hastadGraphLinearCorr {g : Graph (β → γ)}
    (hg : g.edges ≠ []) (δ : ℝ) (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) :
    hastadGraphSATProb g δ B A = 7 / 8 + 1 / 8 * hastadGraphLinearCorr g δ B A := by
  have hne : (univ : Finset (Fin g.edges.length)).Nonempty :=
    univ_nonempty_iff.2 ⟨⟨0, List.length_pos_of_ne_nil hg⟩⟩
  simp only [hastadGraphSATProb, hastadGraphLinearCorr, hastadSATProb_eq_add_hastadLinearCorr,
    expect_add_distrib, expect_const hne, ← mul_expect]

omit [Nonempty β] [Nonempty γ] in
/-- **Multi-edge completeness of Håstad's tests**: if `(ℓ, r)` satisfies every edge of a non-empty
Label Cover instance `g`, then the Long Code tables `B w = longCode (r w)` and
`A u = longCode (ℓ u)` are folded and achieve linear acceptance `1 - δ` and E3-CNF clause
satisfaction `1 - δ / 4`. -/
theorem hastadGraphProb_longCode_of_satisfies {g : Graph (β → γ)} (hg : g.edges ≠ []) (δ : ℝ)
    {ℓ : ℕ → β} {r : ℕ → γ} (hℓr : ∀ d ∈ g.edges, d.constraint (ℓ d.src) = r d.dst) :
    (∀ w, IsFolded (longCode (r w))) ∧
      hastadGraphLinearProb g δ (fun w => longCode (r w)) (fun u => longCode (ℓ u)) = 1 - δ ∧
      hastadGraphSATProb g δ (fun w => longCode (r w)) (fun u => longCode (ℓ u)) = 1 - δ / 4 := by
  have hne : (univ : Finset (Fin g.edges.length)).Nonempty :=
    univ_nonempty_iff.2 ⟨⟨0, List.length_pos_of_ne_nil hg⟩⟩
  refine ⟨fun w => isFolded_longCode (r w), ?_, ?_⟩
  · unfold hastadGraphLinearProb
    have hterm (i : Fin g.edges.length) :
        hastadLinearProb (g.edges.get i).constraint δ
          (longCode (r (g.edges.get i).dst)) (longCode (ℓ (g.edges.get i).src)) = 1 - δ := by
      rw [← hℓr (g.edges.get i) (List.get_mem _ _), hastadLinearProb_longCode]
    simp only [hterm, expect_const hne]
  · unfold hastadGraphSATProb
    have hterm (i : Fin g.edges.length) :
        hastadSATProb (g.edges.get i).constraint δ
          (longCode (r (g.edges.get i).dst)) (longCode (ℓ (g.edges.get i).src)) = 1 - δ / 4 := by
      rw [← hℓr (g.edges.get i) (List.get_mem _ _), hastadSATProb_longCode]
    simp only [hterm, expect_const hne]

/-- **Multi-edge soundness bound for Håstad's 3-bit test over Label Cover**
[Håstad, Theorem 5.6][Hastad2001]: for any Label Cover instance `g : Graph (β → γ)`, noise rate
`0 ≤ δ ≤ 1 / 2`, degree cutoff `k`, folded right tables `B`, and left tables `A`, the squared
average correlation `hastadGraphLinearCorr g δ B A ^ 2` is at most
`(1 - 2 * δ) ^ (2 * k) + k ^ 2 * (1 - (g.toGraph projectionEval).unsatVal)`. -/
theorem hastadGraphLinearCorr_sq_le (g : Graph (β → γ)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (k : ℕ) {B : ℕ → (γ → Bool) → Bool} (hB : ∀ w, IsFolded (B w))
    (A : ℕ → (β → Bool) → Bool) :
    hastadGraphLinearCorr g δ B A ^ 2 ≤
      (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * (1 - (g.toGraph projectionEval).unsatVal) := by
  have hρ0 : 0 ≤ 1 - 2 * δ := by linarith
  have hunsat1 : (g.toGraph projectionEval).unsatVal ≤ 1 :=
    (g.toGraph projectionEval).unsatVal_le_one
  rcases g.edges.eq_nil_or_concat with hnil | ⟨l, d, hconcat⟩
  · have hempty : IsEmpty (Fin g.edges.length) := by simp [hnil]
    have hcorr0 : hastadGraphLinearCorr g δ B A = 0 := by
      simp [hastadGraphLinearCorr]
    rw [hcorr0, sq, mul_zero]
    positivity
  · have hm_pos : (0 : ℝ) < g.edges.length := by
      rw [hconcat, List.length_concat]
      positivity
    have hjensen :
        hastadGraphLinearCorr g δ B A ^ 2 ≤
          𝔼 i : Fin g.edges.length,
            hastadLinearCorr (g.edges.get i).constraint δ
              (B (g.edges.get i).dst) (A (g.edges.get i).src) ^ 2 := by
      unfold hastadGraphLinearCorr
      rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
      have hcs := sum_mul_sq_le_sq_mul_sq univ (fun _ : Fin g.edges.length => (1 : ℝ))
        (fun i : Fin g.edges.length =>
          hastadLinearCorr (g.edges.get i).constraint δ
            (B (g.edges.get i).dst) (A (g.edges.get i).src))
      simp only [one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        one_mul] at hcs
      rw [div_pow, div_le_iff₀ (sq_pos_of_pos hm_pos)]
      calc (∑ i : Fin g.edges.length,
            hastadLinearCorr (g.edges.get i).constraint δ
              (B (g.edges.get i).dst) (A (g.edges.get i).src)) ^ 2
        _ ≤ g.edges.length * ∑ i : Fin g.edges.length,
              hastadLinearCorr (g.edges.get i).constraint δ
                (B (g.edges.get i).dst) (A (g.edges.get i).src) ^ 2 := hcs
        _ = (∑ i : Fin g.edges.length,
              hastadLinearCorr (g.edges.get i).constraint δ
                (B (g.edges.get i).dst) (A (g.edges.get i).src) ^ 2) /
              g.edges.length * (g.edges.length : ℝ) ^ 2 := by
          field_simp
    refine hjensen.trans ?_
    rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_le_iff₀ hm_pos]
    calc (∑ i : Fin g.edges.length,
          hastadLinearCorr (g.edges.get i).constraint δ
            (B (g.edges.get i).dst) (A (g.edges.get i).src) ^ 2)
      _ ≤ ∑ i : Fin g.edges.length,
            ((1 - 2 * δ) ^ (2 * k) +
              (k : ℝ) ^ 2 * ∑ x : β,
                spectralWeight k (A (g.edges.get i).src) x *
                  spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x)) :=
        sum_le_sum fun i _ =>
          hastadLinearCorr_sq_le (g.edges.get i).constraint hδ0 hδ1 k
            (hB (g.edges.get i).dst) (A (g.edges.get i).src)
      _ = g.edges.length * (1 - 2 * δ) ^ (2 * k) +
            (k : ℝ) ^ 2 * ∑ i : Fin g.edges.length, ∑ x : β,
              spectralWeight k (A (g.edges.get i).src) x *
                spectralWeight k (B (g.edges.get i).dst) ((g.edges.get i).constraint x) := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
      _ ≤ g.edges.length * (1 - 2 * δ) ^ (2 * k) +
            (k : ℝ) ^ 2 * (g.edges.length * (1 - (g.toGraph projectionEval).unsatVal)) := by
        gcongr
        exact sum_spectralWeight_le_unsatVal g k B A
      _ = ((1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * (1 - (g.toGraph projectionEval).unsatVal)) *
            g.edges.length := by ring

/-- When a Label Cover instance `g` has maximum satisfied edge fraction
`1 - (g.toGraph projectionEval).unsatVal ≤ η` and `(1 - 2 * δ) ^ (2 * k) + k ^ 2 * η ≤ (8 * ε) ^ 2`
(`0 ≤ ε`), every assignment of folded right tables `B` and left tables `A` has average linear
correlation at most `8 * ε`. -/
theorem hastadGraphLinearCorr_le_of_unsatVal (g : Graph (β → γ)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (k : ℕ) {η ε : ℝ} (hε : 0 ≤ ε)
    (hη : 1 - (g.toGraph projectionEval).unsatVal ≤ η)
    (hparam : (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * η ≤ (8 * ε) ^ 2)
    {B : ℕ → (γ → Bool) → Bool} (hB : ∀ w, IsFolded (B w)) (A : ℕ → (β → Bool) → Bool) :
    hastadGraphLinearCorr g δ B A ≤ 8 * ε := by
  have hsq : hastadGraphLinearCorr g δ B A ^ 2 ≤ (8 * ε) ^ 2 := by
    calc hastadGraphLinearCorr g δ B A ^ 2
      _ ≤ (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * (1 - (g.toGraph projectionEval).unsatVal) :=
        hastadGraphLinearCorr_sq_le g hδ0 hδ1 k hB A
      _ ≤ (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * η := by gcongr
      _ ≤ (8 * ε) ^ 2 := hparam
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-- For every `ε > 0` and `0 < δ < 1 / 2`, there exist a degree cutoff `k : ℕ` and a Label Cover
soundness threshold `η > 0` such that `(1 - 2 * δ) ^ (2 * k) + k ^ 2 * η ≤ (8 * ε) ^ 2`. -/
theorem exists_hastad_params {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ (k : ℕ) (η : ℝ), 0 < η ∧ (1 - 2 * δ) ^ (2 * k) + (k : ℝ) ^ 2 * η ≤ (8 * ε) ^ 2 := by
  have hρ0 : 0 ≤ 1 - 2 * δ := by linarith
  have hρ1 : 1 - 2 * δ < 1 := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < (8 * ε) ^ 2 / 2) hρ1
  refine ⟨N + 1, (8 * ε) ^ 2 / (2 * ((N + 1 : ℕ) : ℝ) ^ 2), by positivity, ?_⟩
  have hpow : (1 - 2 * δ) ^ (2 * (N + 1)) ≤ (1 - 2 * δ) ^ N :=
    pow_le_pow_of_le_one hρ0 hρ1.le (by omega)
  have hmul : ((N + 1 : ℕ) : ℝ) ^ 2 * ((8 * ε) ^ 2 / (2 * ((N + 1 : ℕ) : ℝ) ^ 2)) =
      (8 * ε) ^ 2 / 2 := by
    have hpos : ((N + 1 : ℕ) : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  linarith

/-- **Håstad's two-sided Label Cover to MAX-E3LIN `(1 - δ, 1 / 2 + 4 * ε)` and MAX-E3SAT
`(1 - δ / 4, 7 / 8 + ε)` gap reduction theorem** [Håstad, Theorems 5.6 and 6.5][Hastad2001]:
for every `ε > 0` and `0 < δ < 1 / 2`, there exists a Label Cover soundness parameter `η > 0`
such that for every Label Cover instance `g : Graph (β → γ)` with `g.edges ≠ []`:
1. (**Completeness**) If `g ∈ (GapLabelCover β γ 1 η).yes`, there exist folded tables `B` and `A`
   achieving `hastadGraphLinearProb g δ B A = 1 - δ` and
   `hastadGraphSATProb g δ B A = 1 - δ / 4`.
2. (**Soundness**) If `g ∈ (GapLabelCover β γ 1 η).no`, then for all folded right tables `B` and
   all left tables `A`, `hastadGraphLinearProb g δ B A ≤ 1 / 2 + 4 * ε` and
   `hastadGraphSATProb g δ B A ≤ 7 / 8 + ε`. -/
theorem hastad_gapLabelCover_dichotomy {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ {g : Graph (β → γ)}, g.edges ≠ [] →
      (g ∈ (GapLabelCover β γ 1 η).yes →
        ∃ (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool),
          (∀ w, IsFolded (B w)) ∧
            hastadGraphLinearProb g δ B A = 1 - δ ∧
            hastadGraphSATProb g δ B A = 1 - δ / 4) ∧
      (g ∈ (GapLabelCover β γ 1 η).no →
        ∀ (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool),
          (∀ w, IsFolded (B w)) →
            hastadGraphLinearProb g δ B A ≤ 1 / 2 + 4 * ε ∧
            hastadGraphSATProb g δ B A ≤ 7 / 8 + ε) := by
  obtain ⟨k, η, hη, hparam⟩ := exists_hastad_params hε hδ0 hδ1
  refine ⟨η, hη, fun {g} hg => ⟨?_, ?_⟩⟩
  · intro hyes
    simp only [GapLabelCover, PromiseProblem.mem_yes_gapMax] at hyes
    have hunsat0 : (g.toGraph projectionEval).unsatVal = 0 :=
      le_antisymm (by linarith) (g.toGraph projectionEval).unsatVal_nonneg
    have hsat : (g.toGraph projectionEval).Satisfiable :=
      (g.toGraph projectionEval).unsatVal_eq_zero_iff.1 hunsat0
    obtain ⟨ℓ, r, hℓr⟩ := (satisfiable_toGraph_projectionEval_iff g).1 hsat
    obtain ⟨hfold, hlin, hsatp⟩ := hastadGraphProb_longCode_of_satisfies hg δ hℓr
    exact ⟨fun w => longCode (r w), fun u => longCode (ℓ u), hfold, hlin, hsatp⟩
  · intro hno B A hB
    simp only [GapLabelCover, PromiseProblem.mem_no_gapMax] at hno
    have hcorr := hastadGraphLinearCorr_le_of_unsatVal g hδ0.le hδ1.le k hε.le hno.1 hparam hB A
    have hlin := hastadGraphLinearProb_eq_add_hastadGraphLinearCorr hg δ B A
    have hsatp := hastadGraphSATProb_eq_add_hastadGraphLinearCorr hg δ B A
    exact ⟨by linarith, by linarith⟩

end LabelCoverSoundness

end Cslib.PCP.Hastad

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

/-- **Tightness of the `7 / 8` random-assignment threshold for MAX-E3SAT**: for every `s < 7 / 8`,
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
