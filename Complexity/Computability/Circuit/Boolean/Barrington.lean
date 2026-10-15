/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BranchingProgram.MonoidProgram
public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Foundations.GroupTheory.Perm.FiveCycle
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.Ring

/-!
# Barrington's theorem

**Barrington's theorem**: a De Morgan formula of depth `d`, with negations free, becomes a
permutation branching program of width `5` and length at most `4 ^ d`, which is a fixed `5`-cycle
on the inputs where the formula is true and the identity elsewhere
(`Formula.exists_monoidProgram_computes`) [Barrington1989], [Jukna, Section 15.4][Jukna2012].

The construction works for every `5`-cycle `σ` at once. An input `xᵢ` reads `xᵢ` and selects `σ`
or the identity. A negation `σ⁻¹`-computes its argument and multiplies by `σ`. For a conjunction,
`σ` is the commutator `α β α⁻¹ β⁻¹` of two `5`-cycles (`Equiv.Perm.IsFiveCycle.exists_commutator`);
running the programs for the arguments with `α` and `β`, then their inverses, gives `σ` exactly
when both arguments are true. A disjunction is the negation of the conjunction of the negations.

Conversely, whether a branching program of width `w`, a program over `Function.End (Fin w)`, maps
`a` to `b` is a formula of depth `O(log w · log L)`: split the program in halves and take the
disjunction over the middle values (`MonoidProgram.entryFormula`). So a branching program of width
`w` and length `L` is a formula of depth `(⌈log₂ w⌉ + 1) ⌈log₂ L⌉ + ⌈log₂ w⌉`
(`MonoidProgram.exists_formula`), with negations only at the leaves, and constant-width
polynomial-length branching programs and logarithmic-depth formulas compute the same functions.

## Main definitions

* `Cslib.BranchingPrograms.MonoidProgram.entryFormula`: the formula saying that a branching
  program maps `a` to `b`.

## Main results

* `Cslib.Circuits.Formula.exists_monoidProgram_computes`: Barrington's theorem.
* `Cslib.BranchingPrograms.MonoidProgram.exists_formula`: branching programs give formulas of
  logarithmic depth.
* `Cslib.BranchingPrograms.MonoidProgram.Computes.exists_formula`: so do permutation branching
  programs.

## References

* [D. A. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

open Equiv Equiv.Perm Cslib.BranchingPrograms Cslib.Circuits.Boolean

variable {n w : ℕ}

/-! ### Barrington's theorem -/

namespace Cslib.Circuits.Formula

open MonoidProgram

/-- **Barrington's theorem.** For every `5`-cycle `σ`, a De Morgan formula of depth `d`, with
negations and constants free, has a permutation branching program of width `5` and length at most
`4 ^ d` that `σ`-computes it. -/
theorem exists_monoidProgram_computes [NeZero n] (F : Formula signature n) {σ : Perm (Fin 5)}
    (hσ : IsFiveCycle σ) :
    ∃ P : MonoidProgram n (Perm (Fin 5)), P.length ≤ 4 ^ F.depthWith binaryCost ∧
      P.Computes σ (F.eval interpretation) := by
  induction F generalizing σ with
  | input i =>
    refine ⟨FreeMonoid.of ⟨i, 1, σ⟩, by simp, fun x => ?_⟩
    cases h : x i <;> simp [Instruction.eval, h]
  | gate op args ih =>
    cases op with
    | const c =>
      cases c
      · exact ⟨1, by simp, fun x => by simp [interpretation]⟩
      · exact ⟨FreeMonoid.of ⟨0, σ, σ⟩, by simp, fun x => by
          simp [interpretation, Instruction.eval]⟩
    | not =>
      obtain ⟨P, hlen, hP⟩ := ih 0 hσ.inv
      refine ⟨mulLeft σ P, (length_mulLeft σ P).trans_le (max_le ?_ (hlen.trans ?_)),
        fun x => (hP.not x).trans (by simp [interpretation])⟩
      · exact Nat.one_le_pow _ _ (by decide)
      · exact Nat.pow_le_pow_right (by decide) (by simp)
    | and =>
      obtain ⟨α, β, hα, hβ, rfl⟩ := hσ.exists_commutator
      obtain ⟨P, hPlen, hP⟩ := ih 0 hα
      obtain ⟨Q, hQlen, hQ⟩ := ih 1 hβ
      refine ⟨P * Q * P.inv * Q.inv, ?_, fun x => (hP.and hQ x).trans rfl⟩
      set D : ℕ := max (depthWith (σ := signature) binaryCost (args 0))
        (depthWith (σ := signature) binaryCost (args 1))
      have hd : (gate (σ := signature) Op.and args).depthWith binaryCost = D + 1 := by
        simp [D, Fin.univ_succ]
      have h₀ : P.length ≤ 4 ^ D :=
        hPlen.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
      have h₁ : Q.length ≤ 4 ^ D :=
        hQlen.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
      calc (P * Q * P.inv * Q.inv).length = 2 * (P.length + Q.length) := by
            simp only [FreeMonoid.length_mul, length_inv]
            omega
        _ ≤ 2 * (4 ^ D + 4 ^ D) := Nat.mul_le_mul_left 2 (Nat.add_le_add h₀ h₁)
        _ = 4 ^ (D + 1) := by ring
        _ = 4 ^ (gate (σ := signature) Op.and args).depthWith binaryCost := by rw [hd]
    | or =>
      obtain ⟨α, β, hα, hβ, hαβ⟩ := hσ.inv.exists_commutator
      obtain ⟨P, hPlen, hP⟩ := ih 0 hα.inv
      obtain ⟨Q, hQlen, hQ⟩ := ih 1 hβ.inv
      let R := mulLeft α P * mulLeft β Q * (mulLeft α P).inv * (mulLeft β Q).inv
      have hR : R.Computes σ⁻¹ fun x => !(args 0).eval interpretation x &&
          !(args 1).eval interpretation x := by
        rw [← hαβ]
        exact hP.not.and hQ.not
      set D : ℕ := max (depthWith (σ := signature) binaryCost (args 0))
        (depthWith (σ := signature) binaryCost (args 1))
      have hd : (gate (σ := signature) Op.or args).depthWith binaryCost = D + 1 := by
        simp [D, Fin.univ_succ]
      have hD : 1 ≤ 4 ^ D := Nat.one_le_pow _ _ (by decide)
      have h₀ : (mulLeft α P).length ≤ 4 ^ D := (length_mulLeft α P).trans_le (max_le hD
        (hPlen.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))))
      have h₁ : (mulLeft β Q).length ≤ 4 ^ D := (length_mulLeft β Q).trans_le (max_le hD
        (hQlen.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))))
      have hRlen : R.length ≤ 4 ^ (gate (σ := signature) Op.or args).depthWith binaryCost :=
        calc R.length = 2 * ((mulLeft α P).length + (mulLeft β Q).length) := by
              simp only [R, FreeMonoid.length_mul, length_inv]
              omega
          _ ≤ 2 * (4 ^ D + 4 ^ D) := Nat.mul_le_mul_left 2 (Nat.add_le_add h₀ h₁)
          _ = 4 ^ (D + 1) := by ring
          _ = 4 ^ (gate (σ := signature) Op.or args).depthWith binaryCost := by rw [hd]
      refine ⟨mulLeft σ R, (length_mulLeft σ R).trans_le
        (max_le (Nat.one_le_pow _ _ (by decide)) hRlen), fun x => ?_⟩
      · rw [hR.not x]
        simp [interpretation]

end Cslib.Circuits.Formula

namespace Cslib.Circuits.Boolean

/-- A function of formula depth `d` is `σ`-computed, for every `5`-cycle `σ`, by a permutation
branching program of width `5` and length at most `4 ^ d`. -/
theorem exists_monoidProgram_computes_of_formulaDepth [NeZero n]
    (f : BooleanFunction n) {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) :
    ∃ P : MonoidProgram n (Perm (Fin 5)), P.length ≤ 4 ^ formulaDepth f ∧ P.Computes σ f := by
  obtain ⟨F, hF, hd⟩ := exists_computes_depthWith_eq_formulaDepth f
  obtain ⟨P, hlen, hP⟩ := F.exists_monoidProgram_computes hσ
  exact ⟨P, hd ▸ hlen, fun x => (hP x).trans (by rw [hF x])⟩

end Cslib.Circuits.Boolean

/-! ### The converse -/

namespace Cslib.BranchingPrograms

open Cslib.Circuits

/-- The formula saying that an instruction of a width-`w` branching program maps `a` to `b`: a
constant or a literal. -/
def Instruction.entryFormula (ι : Instruction n (Function.End (Fin w))) (a b : Fin w) :
    Formula signature n :=
  match decide (ι.ifFalse a = b), decide (ι.ifTrue a = b) with
  | true, true => .const true
  | false, true => .input ι.var
  | true, false => (Formula.input ι.var).not
  | false, false => .const false

@[simp] theorem Instruction.eval_entryFormula (ι : Instruction n (Function.End (Fin w)))
    (a b : Fin w) (x : BitString n) :
    (ι.entryFormula a b).eval interpretation x = decide ((ι.eval x) a = b) := by
  unfold entryFormula
  cases h₀ : decide (ι.ifFalse a = b) <;> cases h₁ : decide (ι.ifTrue a = b) <;>
    cases hx : x ι.var <;> simp_all [Instruction.eval]

@[simp] theorem Instruction.depthWith_entryFormula (ι : Instruction n (Function.End (Fin w)))
    (a b : Fin w) : (ι.entryFormula a b).depthWith binaryCost = 0 := by
  unfold entryFormula
  cases decide (ι.ifFalse a = b) <;> cases decide (ι.ifTrue a = b) <;> simp

/-- The formula saying that a list of instructions of a width-`w` branching program maps `a` to
`b`, by splitting the list in halves. -/
def entryFormulaList (l : List (Instruction n (Function.End (Fin w)))) (a b : Fin w) :
    Formula signature n :=
  match h : l with
  | [] => .const (decide (a = b))
  | [ι] => ι.entryFormula a b
  | _ :: _ :: _ =>
    Formula.orList ((List.finRange w).map fun c =>
      (entryFormulaList (l.drop (l.length / 2)) a c).and
        (entryFormulaList (l.take (l.length / 2)) c b))
termination_by l.length
decreasing_by
  all_goals subst h; simp only [List.length_take, List.length_drop, List.length_cons]; omega

private theorem eval_entryFormulaList (l : List (Instruction n (Function.End (Fin w))))
    (a b : Fin w) (x : BitString n) :
    (entryFormulaList l a b).eval interpretation x =
      decide (((l.map (·.eval x)).prod : Function.End (Fin w)) a = b) := by
  induction h : l.length using Nat.strong_induction_on generalizing l a b with
  | _ k ih =>
  match l with
  | [] =>
    simp only [entryFormulaList, Formula.eval_const, List.map_nil, List.prod_nil]
    rfl
  | [ι] => simp [entryFormulaList]
  | ι :: κ :: l =>
    rw [entryFormulaList, Formula.eval_orList]
    have hlen₁ : (List.take ((ι :: κ :: l).length / 2) (ι :: κ :: l)).length < k := by
      simp only [List.length_take, List.length_cons] at h ⊢; omega
    have hlen₂ : (List.drop ((ι :: κ :: l).length / 2) (ι :: κ :: l)).length < k := by
      simp only [List.length_drop, List.length_cons] at h ⊢; omega
    have hprod : ((ι :: κ :: l).map (·.eval x)).prod =
        ((List.take ((ι :: κ :: l).length / 2) (ι :: κ :: l)).map (·.eval x)).prod *
          ((List.drop ((ι :: κ :: l).length / 2) (ι :: κ :: l)).map (·.eval x)).prod := by
      rw [← List.prod_append, ← List.map_append, List.take_append_drop]
    simp only [List.any_map, Function.comp_def, Formula.eval_and, ih _ hlen₁ _ _ _ rfl,
      ih _ hlen₂ _ _ _ rfl]
    rw [hprod, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    simp only [List.mem_finRange, true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨c, hc, hcb⟩ => by subst hc; exact hcb, fun h => ⟨_, rfl, h⟩⟩

private theorem depthWith_entryFormulaList_le (l : List (Instruction n (Function.End (Fin w))))
    (a b : Fin w) :
    (entryFormulaList l a b).depthWith binaryCost ≤ (Nat.clog 2 w + 1) * Nat.clog 2 l.length := by
  induction h : l.length using Nat.strong_induction_on generalizing l a b with
  | _ k ih =>
  match l with
  | [] => simp [entryFormulaList]
  | [ι] => simp [entryFormulaList]
  | ι :: κ :: l =>
    rw [entryFormulaList, h]
    have hk : 2 ≤ k := by simp only [List.length_cons] at h; omega
    have hlen₁ : (List.take (k / 2) (ι :: κ :: l)).length ≤ (k + 2 - 1) / 2 := by
      simp only [List.length_take, List.length_cons] at h ⊢; omega
    have hlen₂ : (List.drop (k / 2) (ι :: κ :: l)).length ≤ (k + 2 - 1) / 2 := by
      simp only [List.length_drop, List.length_cons] at h ⊢; omega
    refine (Formula.depthWith_binaryCost_orList_le _ (d := (Nat.clog 2 w + 1) *
      Nat.clog 2 ((k + 2 - 1) / 2) + 1) fun F hF => ?_).trans ?_
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hF
      rw [Formula.depthWith_and, binaryCost_and]
      refine Nat.add_le_add_right (max_le ?_ ?_) 1
      · exact (ih _ (by simp only [List.length_drop, List.length_cons] at h ⊢; omega) _ _ _
          rfl).trans (Nat.mul_le_mul_left _ (Nat.clog_mono_right 2 hlen₂))
      · exact (ih _ (by simp only [List.length_take, List.length_cons] at h ⊢; omega) _ _ _
          rfl).trans (Nat.mul_le_mul_left _ (Nat.clog_mono_right 2 hlen₁))
    · rw [List.length_map, List.length_finRange, Nat.clog_of_two_le (by decide) hk, Nat.mul_succ]
      omega

namespace MonoidProgram

/-- The formula saying that a branching program of width `w` maps `a` to `b`: split the program in
halves, and say that the second half maps `a` to some `c` that the first half maps to `b`. -/
def entryFormula (P : MonoidProgram n (Function.End (Fin w))) (a b : Fin w) :
    Formula signature n :=
  entryFormulaList P.toList a b

@[simp] theorem eval_entryFormula (P : MonoidProgram n (Function.End (Fin w))) (a b : Fin w)
    (x : BitString n) :
    (P.entryFormula a b).eval interpretation x = decide ((P.eval x) a = b) := by
  rw [entryFormula, eval_entryFormulaList, eval_eq_prod]

theorem depthWith_entryFormula_le (P : MonoidProgram n (Function.End (Fin w))) (a b : Fin w) :
    (P.entryFormula a b).depthWith binaryCost ≤ (Nat.clog 2 w + 1) * Nat.clog 2 P.length :=
  depthWith_entryFormulaList_le _ a b

/-- **Branching programs give formulas.** A branching program of width `w` and length `L`, started
at `a` and accepting at the states of `acc`, is computed by a De Morgan formula of depth at most
`(⌈log₂ w⌉ + 1) ⌈log₂ L⌉ + ⌈log₂ w⌉`, with negations only at the leaves. -/
theorem exists_formula (P : MonoidProgram n (Function.End (Fin w))) (a : Fin w)
    (acc : Finset (Fin w)) :
    ∃ F : Formula signature n, (∀ x, F.eval interpretation x = decide ((P.eval x) a ∈ acc)) ∧
      F.depthWith binaryCost ≤ (Nat.clog 2 w + 1) * Nat.clog 2 P.length + Nat.clog 2 w := by
  classical
  refine ⟨Formula.orList (acc.toList.map (P.entryFormula a)), fun x => ?_, ?_⟩
  · rw [Formula.eval_orList, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    simp
  · refine (Formula.depthWith_binaryCost_orList_le _ fun F hF => ?_).trans (Nat.add_le_add_left
      (Nat.clog_mono_right 2 (by simpa using acc.card_le_univ)) _)
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hF
    exact depthWith_entryFormula_le P a b

/-- **Permutation branching programs give formulas.** A permutation branching program of width `w`
and length `L` that `σ`-computes `f`, with `σ ≠ 1`, is turned into a De Morgan formula computing
`f` of depth at most `(⌈log₂ w⌉ + 1) ⌈log₂ L⌉ + ⌈log₂ (w ^ 2)⌉`, with negations only at the
leaves: `f` is true where some `a` is mapped to some `b ≠ a`. -/
theorem Computes.exists_formula {P : MonoidProgram n (Perm (Fin w))} {σ : Perm (Fin w)}
    {f : BooleanFunction n} (hP : P.Computes σ f) (hσ : σ ≠ 1) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧
      F.depthWith binaryCost ≤ (Nat.clog 2 w + 1) * Nat.clog 2 P.length + Nat.clog 2 (w * w) := by
  let Q := P.map (MulAction.toEndHom (M := Perm (Fin w)) (α := Fin w))
  let pairs := (List.finRange w ×ˢ List.finRange w).filter fun p => p.1 ≠ p.2
  refine ⟨Formula.orList (pairs.map fun p => Q.entryFormula p.1 p.2), fun x => ?_, ?_⟩
  · rw [Formula.eval_orList, List.any_map, Bool.eq_iff_iff, List.any_eq_true]
    simp only [Function.comp_def, eval_entryFormula, Q, eval_map, hP x, pairs, List.mem_filter,
      List.mem_product, List.mem_finRange, true_and, decide_eq_true_eq, Prod.exists, ne_eq]
    cases hf : f x
    · simp only [MulAction.toEndHom, Bool.false_eq_true, ↓reduceIte, map_one, iff_false]
      simp only [not_exists, not_and]
      intro a b hab h
      exact hab h
    · simp only [↓reduceIte, iff_true]
      obtain ⟨a, ha⟩ := not_forall.1 fun h => hσ (Perm.ext h)
      exact ⟨a, σ a, fun h => ha h.symm, rfl⟩
  · refine (Formula.depthWith_binaryCost_orList_le _ fun F hF => ?_).trans (Nat.add_le_add_left
      (Nat.clog_mono_right 2 ?_) _)
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hF
      simpa [Q] using depthWith_entryFormula_le Q p.1 p.2
    · rw [List.length_map]
      exact (List.length_filter_le _ _).trans
        (by rw [List.length_product, List.length_finRange])

end MonoidProgram

end Cslib.BranchingPrograms
