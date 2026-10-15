/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Formula
public import Cslib.Computability.Circuit.Boolean.Basic
public import Complexity.Computability.Circuit.Boolean.BinaryCost
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Fin

/-!
# De Morgan formulas

A *De Morgan formula* is a formula over the De Morgan signature, `Formula Boolean.signature n`,
evaluated under `Boolean.interpretation`. Negations may appear anywhere. Pushing them to the
leaves by De Morgan's laws does not change the leaf size, so lower bounds on the leaf size of these
formulas are at least as strong as for formulas whose negations sit at the leaves
[Jukna, Chapter 6][Jukna2012].

## Main definitions

* `Cslib.Circuits.Formula.const`, `Cslib.Circuits.Formula.not`, `Cslib.Circuits.Formula.and`,
  `Cslib.Circuits.Formula.or`: De Morgan formulas built from constants and smaller formulas.
* `Cslib.Circuits.Formula.xor`: the exclusive or `(F ∧ ¬G) ∨ (¬F ∧ G)`.
* `Cslib.Circuits.Formula.orList`, `Cslib.Circuits.Formula.andList`: the disjunction and the
  conjunction of a list of formulas as balanced trees, whose depth grows by `⌈log₂⌉` of the length
  of the list (`Formula.depthWith_orList_le`).
* `Cslib.Circuits.Boolean.formulaDepth`: the least depth of a De Morgan formula for a function,
  with negations and constants free.

## Main results

* `Cslib.Circuits.Formula.exists_computes`: every Boolean function has a De Morgan formula.
* `Cslib.Circuits.Boolean.exists_computes_depthWith_eq_formulaDepth`: some formula attains the
  formula depth.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Formula

open Boolean

variable {n : ℕ} (F G : Formula signature n) (x : BitString n)

/-- The constant De Morgan formula. -/
def const (c : Bool) : Formula signature n :=
  gate (.const c) Fin.elim0

/-- The negation of a De Morgan formula. -/
def not : Formula signature n :=
  gate .not ![F]

/-- The conjunction of two De Morgan formulas. -/
def and : Formula signature n :=
  gate .and ![F, G]

/-- The disjunction of two De Morgan formulas. -/
def or : Formula signature n :=
  gate .or ![F, G]

/-- The exclusive or of two De Morgan formulas, `(F ∧ ¬G) ∨ (¬F ∧ G)`. -/
def xor : Formula signature n :=
  (F.and G.not).or (F.not.and G)

@[simp] theorem eval_const (c : Bool) : (const c : Formula signature n).eval interpretation x = c :=
  rfl

@[simp] theorem eval_not : F.not.eval interpretation x = !F.eval interpretation x :=
  rfl

@[simp] theorem eval_and :
    (F.and G).eval interpretation x = (F.eval interpretation x && G.eval interpretation x) :=
  rfl

@[simp] theorem eval_or :
    (F.or G).eval interpretation x = (F.eval interpretation x || G.eval interpretation x) :=
  rfl

@[simp] theorem eval_xor :
    (F.xor G).eval interpretation x = (F.eval interpretation x ^^ G.eval interpretation x) := by
  simp only [xor, eval_or, eval_and, eval_not]
  cases F.eval interpretation x <;> cases G.eval interpretation x <;> rfl

@[simp] theorem leafSize_not : F.not.leafSize = F.leafSize :=
  Fin.sum_univ_one _

@[simp] theorem leafSize_and : (F.and G).leafSize = F.leafSize + G.leafSize :=
  Fin.sum_univ_two _

@[simp] theorem leafSize_or : (F.or G).leafSize = F.leafSize + G.leafSize :=
  Fin.sum_univ_two _

@[simp] theorem leafSize_xor : (F.xor G).leafSize = 2 * F.leafSize + 2 * G.leafSize := by
  simp only [xor, leafSize_or, leafSize_and, leafSize_not]
  omega

@[simp] theorem leafSize_const (c : Bool) : (const c : Formula signature n).leafSize = 0 :=
  rfl

@[simp] theorem depthWith_const (cost : Op → ℕ) (c : Bool) :
    (const c : Formula signature n).depthWith cost = cost (.const c) := by
  simp [const]

@[simp] theorem depthWith_not (cost : Op → ℕ) :
    F.not.depthWith cost = F.depthWith cost + cost .not := by
  simp [not]

@[simp] theorem depthWith_and (cost : Op → ℕ) :
    (F.and G).depthWith cost = max (F.depthWith cost) (G.depthWith cost) + cost .and := by
  simp [and, Fin.univ_succ]

@[simp] theorem depthWith_or (cost : Op → ℕ) :
    (F.or G).depthWith cost = max (F.depthWith cost) (G.depthWith cost) + cost .or := by
  simp [or, Fin.univ_succ]

/-- The disjunction of a list of De Morgan formulas, as a balanced tree. -/
def orList (l : List (Formula signature n)) : Formula signature n :=
  match h : l with
  | [] => const false
  | [F] => F
  | _ :: _ :: _ =>
    (orList (l.take (l.length / 2))).or (orList (l.drop (l.length / 2)))
termination_by l.length
decreasing_by
  all_goals subst h; simp only [List.length_take, List.length_drop, List.length_cons]; omega

@[simp] theorem eval_orList (l : List (Formula signature n)) :
    (orList l).eval interpretation x = l.any fun F => F.eval interpretation x := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ k ih =>
  match l with
  | [] => simp [orList]
  | [F] => simp [orList]
  | F :: G :: l =>
    rw [orList, eval_or,
      ih _ (by simp only [List.length_take, List.length_cons] at h ⊢; omega) _ rfl,
      ih _ (by simp only [List.length_drop, List.length_cons] at h ⊢; omega) _ rfl,
      ← List.any_append, List.take_append_drop]

/-- A balanced disjunction is deeper than its disjuncts by `⌈log₂⌉` of their number. -/
theorem depthWith_orList_le (l : List (Formula signature n)) {d : ℕ}
    (hl : ∀ F ∈ l, F.depthWith binaryCost ≤ d) :
    (orList l).depthWith binaryCost ≤ d + Nat.clog 2 l.length := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ k ih =>
  match l with
  | [] => simp [orList]
  | [F] => simpa [orList] using (hl F (by simp)).trans (Nat.le_add_right _ _)
  | F :: G :: l =>
    rw [orList, h]
    have hk : 2 ≤ k := by simp only [List.length_cons] at h; omega
    have hlen₁ : (List.take (k / 2) (F :: G :: l)).length ≤ (k + 2 - 1) / 2 := by
      simp only [List.length_take, List.length_cons] at h ⊢; omega
    have hlen₂ : (List.drop (k / 2) (F :: G :: l)).length ≤ (k + 2 - 1) / 2 := by
      simp only [List.length_drop, List.length_cons] at h ⊢; omega
    have h₁ := ih _ (by simp only [List.length_take, List.length_cons] at h ⊢; omega)
      (List.take (k / 2) (F :: G :: l)) (fun F hF => hl F (List.mem_of_mem_take hF)) rfl
    have h₂ := ih _ (by simp only [List.length_drop, List.length_cons] at h ⊢; omega)
      (List.drop (k / 2) (F :: G :: l)) (fun F hF => hl F (List.mem_of_mem_drop hF)) rfl
    have hm₁ := Nat.clog_mono_right 2 hlen₁
    have hm₂ := Nat.clog_mono_right 2 hlen₂
    rw [depthWith_or, binaryCost_or, Nat.clog_of_two_le (by decide) hk]
    omega

/-- The conjunction of a list of De Morgan formulas, as a balanced tree of disjunctions under
negations. -/
def andList (l : List (Formula signature n)) : Formula signature n :=
  (orList (l.map not)).not

@[simp] theorem eval_andList (l : List (Formula signature n)) :
    (andList l).eval interpretation x = l.all fun F => F.eval interpretation x := by
  simp [andList, List.any_map, Function.comp_def, ← List.not_all_eq_any_not]

theorem depthWith_andList_le (l : List (Formula signature n)) {d : ℕ}
    (hl : ∀ F ∈ l, F.depthWith binaryCost ≤ d) :
    (andList l).depthWith binaryCost ≤ d + Nat.clog 2 l.length := by
  rw [andList, depthWith_not, binaryCost_not, add_zero, ← List.length_map (f := not)]
  exact depthWith_orList_le _ fun F hF => by
    obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hF
    simpa using hl G hG

/-- The literal of bit `i` that is true at `z`. -/
def literal (z : BitString n) (i : Fin n) : Formula signature n :=
  if z i then input i else (input i).not

@[simp] theorem eval_literal (z : BitString n) (i : Fin n) :
    (literal z i).eval interpretation x = (x i == z i) := by
  unfold literal
  cases z i <;> cases hx : x i <;> simp [hx]

theorem depthWith_literal (z : BitString n) (i : Fin n) :
    (literal z i).depthWith binaryCost = 0 := by
  unfold literal
  split <;> simp

/-- Every Boolean function has a De Morgan formula: its disjunctive normal form. -/
theorem exists_computes (f : BooleanFunction n) :
    ∃ F : Formula signature n, F.Computes interpretation f := by
  classical
  refine ⟨orList ((Finset.univ.filter fun z => f z = true).toList.map fun z =>
    andList ((List.finRange n).map (literal z))), fun x => ?_⟩
  rw [eval_orList, Bool.eq_iff_iff, List.any_eq_true]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
    have : x = z := funext (by simpa [List.all_eq_true] using h)
    rwa [this]
  · intro hx
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [List.all_eq_true]⟩

end Formula

namespace Boolean

/-- The least depth of a De Morgan formula computing `f`, with negations and constants free. -/
noncomputable def formulaDepth (f : BooleanFunction n) : ℕ :=
  sInf {d | ∃ F : Formula signature n, F.Computes interpretation f ∧ F.depthWith binaryCost ≤ d}

theorem formulaDepth_le {f : BooleanFunction n} {F : Formula signature n}
    (hF : F.Computes interpretation f) : formulaDepth f ≤ F.depthWith binaryCost :=
  Nat.sInf_le ⟨F, hF, le_rfl⟩

theorem exists_computes_depthWith_eq_formulaDepth (f : BooleanFunction n) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧
      F.depthWith binaryCost = formulaDepth f := by
  obtain ⟨F₀, hF₀⟩ := Formula.exists_computes f
  obtain ⟨F, hF, hle⟩ := Nat.sInf_mem (s := {d | ∃ F : Formula signature n,
    F.Computes interpretation f ∧ F.depthWith binaryCost ≤ d}) ⟨_, F₀, hF₀, le_rfl⟩
  exact ⟨F, hF, le_antisymm hle (formulaDepth_le hF)⟩

/-- Lower bounds on formula depth are lower bounds on the depth of every formula. -/
theorem le_formulaDepth_iff {f : BooleanFunction n} {d : ℕ} :
    d ≤ formulaDepth f ↔ ∀ F : Formula signature n, F.Computes interpretation f →
      d ≤ F.depthWith binaryCost := by
  refine ⟨fun h F hF => h.trans (formulaDepth_le hF), fun h => ?_⟩
  obtain ⟨F, hF, hd⟩ := exists_computes_depthWith_eq_formulaDepth f
  exact hd ▸ h F hF

end Boolean

end Cslib.Circuits
