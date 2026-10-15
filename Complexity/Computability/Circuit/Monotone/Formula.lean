/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Formula
public import Complexity.Computability.Circuit.Monotone.Basic
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/-!
# Monotone formulas

A *monotone formula* is a formula over the monotone basis, `Formula Monotone.signature n`,
evaluated under `Monotone.interpretation`: a tree of AND and OR gates of fan-in two whose leaves
are inputs and Boolean constants. Every function it computes is monotone (`monotone_eval`), and
every monotone function has one: the disjunction, over the inputs `z` where the function is true,
of the conjunction of the bits that are one in `z` (`exists_computes_of_monotone`). Unlike De
Morgan formulas, monotone formulas thus compute only some Boolean functions, so the least depth of
a monotone formula for `f` is extended-valued: `eformulaDepth f` is `⊤` when no monotone formula
computes `f`, that is, when `f` is not monotone (`eformulaDepth_ne_top_iff`). As for De Morgan
formulas (`Boolean.formulaDepth`), the depth counts the AND and OR gates on a path, and constants
are free (`binaryCost`).

## Main definitions

* `Cslib.Circuits.Monotone.binaryCost`: the cost function charging one for each AND and OR gate.
* `Cslib.Circuits.Monotone.eformulaDepth`: the least depth of a monotone formula for a function,
  or `⊤` if there is none.

## Main results

* `Cslib.Circuits.Monotone.exists_computes_iff_monotone`: a Boolean function has a monotone
  formula exactly when it is monotone.
* `Cslib.Circuits.Monotone.eformulaDepth_ne_top_iff`: monotone formula depth is finite exactly for
  monotone functions.
* `Cslib.Circuits.Monotone.eformulaDepth_le`, `Cslib.Circuits.Monotone.le_eformulaDepth_iff`:
  upper and lower bounds on monotone formula depth.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 7][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

variable {n : ℕ}

/-- The cost function charging one for each AND and OR gate and nothing for constants. -/
def binaryCost : Op → ℕ
  | .and | .or => 1
  | .const _ => 0

/-- An AND gate costs one level. -/
@[simp] theorem binaryCost_and : binaryCost .and = 1 :=
  rfl

/-- An OR gate costs one level. -/
@[simp] theorem binaryCost_or : binaryCost .or = 1 :=
  rfl

/-- Constants are free. -/
@[simp] theorem binaryCost_const (b : Bool) : binaryCost (.const b) = 0 :=
  rfl

/-- Monotone formulas compute monotone functions. -/
theorem monotone_eval (F : Formula signature n) : Monotone (F.eval interpretation) := by
  induction F with
  | input i => exact fun _ _ h => h i
  | gate op args ih => exact fun _ _ h => interpretation_mono op fun j => ih j h

variable {f : BooleanFunction n}

/-- Every monotone function has a monotone formula: the disjunction, over the inputs `z` where it
is true, of the conjunction of the bits that are one in `z`. -/
theorem exists_computes_of_monotone (hf : Monotone f) :
    ∃ F : Formula signature n, F.Computes interpretation f := by
  classical
  have hconj (s : Finset (Fin n)) : ∃ F : Formula signature n,
      F.Computes interpretation fun x => decide (∀ i ∈ s, x i = true) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨.gate (.const true) Fin.elim0, fun x => by simp⟩
    | insert i s _ ih =>
      obtain ⟨F, hF⟩ := ih
      exact ⟨.gate .and ![.input i, F], fun x => by simp [hF x]⟩
  have hdisj (T : Finset (BitString n)) : ∃ F : Formula signature n,
      F.Computes interpretation fun x => decide (∃ z ∈ T, ∀ i, z i = true → x i = true) := by
    induction T using Finset.induction_on with
    | empty => exact ⟨.gate (.const false) Fin.elim0, fun x => by simp⟩
    | insert z T _ ih =>
      obtain ⟨F, hF⟩ := ih
      obtain ⟨G, hG⟩ := hconj {i | z i = true}
      exact ⟨.gate .or ![G, F], fun x => by simp [hF x, hG x]⟩
  obtain ⟨F, hF⟩ := hdisj {z | f z = true}
  refine ⟨F, fun x => (hF x).trans ?_⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun ⟨z, hz, hzx⟩ => ?_, fun hx => ⟨x, hx, fun _ h => h⟩⟩
  exact Bool.eq_true_of_true_le (hz ▸ hf fun i => Bool.le_iff_imp.2 (hzx i))

/-- A Boolean function has a monotone formula exactly when it is monotone. -/
theorem exists_computes_iff_monotone :
    (∃ F : Formula signature n, F.Computes interpretation f) ↔ Monotone f :=
  ⟨fun ⟨F, hF⟩ => Formula.computes_iff.1 hF ▸ monotone_eval F, exists_computes_of_monotone⟩

/-- The least depth of a monotone formula computing `f`, with constants free, or `⊤` if no
monotone formula computes `f`. -/
noncomputable def eformulaDepth (f : BooleanFunction n) : ℕ∞ :=
  ⨅ F : {F : Formula signature n // F.Computes interpretation f}, (F.1.depthWith binaryCost : ℕ∞)

/-- The monotone formula depth of `f` is at most the depth of every monotone formula computing
`f`. -/
theorem eformulaDepth_le {F : Formula signature n} (hF : F.Computes interpretation f) :
    eformulaDepth f ≤ F.depthWith binaryCost :=
  iInf_le_of_le ⟨F, hF⟩ le_rfl

/-- The monotone formula depth of a function is finite exactly when the function is monotone. -/
theorem eformulaDepth_ne_top_iff : eformulaDepth f ≠ ⊤ ↔ Monotone f := by
  rw [eformulaDepth, ENat.iInf_natCast_ne_top, nonempty_subtype, exists_computes_iff_monotone]

/-- The least depth of a monotone formula for a monotone function is attained. -/
theorem exists_computes_depthWith_eq_eformulaDepth (hf : Monotone f) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧
      (F.depthWith binaryCost : ℕ∞) = eformulaDepth f := by
  have : Nonempty {F : Formula signature n // F.Computes interpretation f} :=
    nonempty_subtype.2 (exists_computes_of_monotone hf)
  obtain ⟨⟨F, hF⟩, hmin⟩ := ENat.exists_eq_iInf
    (fun F : {F : Formula signature n // F.Computes interpretation f} =>
      (F.1.depthWith binaryCost : ℕ∞))
  exact ⟨F, hF, hmin⟩

/-- Lower bounds on monotone formula depth are lower bounds on the depth of every monotone formula
computing the function, including when there is none. -/
theorem le_eformulaDepth_iff {k : ℕ∞} :
    k ≤ eformulaDepth f ↔
      ∀ F : Formula signature n, F.Computes interpretation f → k ≤ F.depthWith binaryCost := by
  simp only [eformulaDepth, le_iInf_iff, Subtype.forall]

end Cslib.Circuits.Monotone
