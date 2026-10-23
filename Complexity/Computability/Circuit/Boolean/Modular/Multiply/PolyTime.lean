/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Modular.Multiply
public import Complexity.Computability.Circuit.Boolean.Modular.PartialProduct.PolyTime
public import Complexity.Computability.Circuit.Boolean.CarrySave.Reduce.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native modular multiplier generation

All shifted partial products, balanced carry-save gates and the final adder are generated from
unary width. The output is the full existing circuit code, including unused fallback gates.

## Main results

* `Cslib.Circuits.Boolean.Modular.multiplyCode_eq_code`: exact code agreement.
* `Cslib.Circuits.Boolean.Modular.computableTidilyInPolyTime_multiply`: uniform native generation.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Modular

open Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- Generate the complete modular multiplier, preserving the half-split reduction topology. -/
def multiplyCode (w : ℕ) : List (Op × List ℕ) × List ℕ :=
  sumPairsCode (w + w) w ((List.range w).map fun i =>
    pairWithZeroCode (w + w) w (partialProductCode w i))

/-- Raw generation agrees gate-for-gate with the total typed modular multiplier. -/
theorem multiplyCode_eq_code (w : ℕ) : multiplyCode w = (multiply w).code := by
  have he : (List.range w).map (fun i =>
      pairWithZeroCode (w + w) w (partialProductCode w i)) =
      (List.ofFn fun i : Fin w => pairWithZero (partialProduct w i)).map Circuit.code := by
    rw [List.map_ofFn]
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [partialProductCode_eq_code ⟨i, by simpa using hi⟩, pairWithZeroCode_eq_code]
    rfl
  rw [multiplyCode, he, sumPairsCode_eq_code]
  rfl

/-- Generation is native polynomial-time in unary width, charging the complete binary code. -/
@[fun_prop] theorem computableTidilyInPolyTime_multiply :
    ComputableTidilyInPolyTime (fun w => (multiply w).code) encUnary encCode := by
  have hl : ComputableTidilyInPolyTime (fun p : ℕ × ℕ =>
      pairWithZeroCode (p.1 + p.1) p.1 (partialProductCode p.1 p.2))
      (encPair encUnary encUnary) encCode := by
    apply computableTidilyInPolyTime_pairWithZeroCode (by fun_prop) (by fun_prop)
    exact computableTidilyInPolyTime_partialProductCode
  have h := computableTidilyInPolyTime_sumPairsCode
    (show ComputableTidilyInPolyTime (fun w : ℕ => w + w) encUnary encNat by fun_prop)
    id' (mapWith hl id' range)
  simpa only [← multiplyCode_eq_code, multiplyCode] using h

end Cslib.Circuits.Boolean.Modular
