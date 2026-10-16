/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.List
public import Complexity.Probability.BitString

/-!
# Independent blocks of uniform bit lists

Reading a uniform list of `count * width` bits as fixed-width rows gives exactly `count`
independent uniform bit strings. This includes zero-width rows and zero rows.

## Main results

* `Cslib.BitString.uniformList_ofList`: a uniform list gives a uniform finite bit string.
* `Cslib.BitString.uniformList_blocks`: fixed-width blocks are jointly uniform.
* `Cslib.BitString.uniformList_listRows`: the same law for the ordinary list-of-lists program.

## References

Adapted from `Probability/WordBits.lean` on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared block representation.
-/

@[expose] public section

namespace Cslib.BitString

open Probability

/-- A uniform list gives exactly a uniform finite bit string. -/
theorem uniformList_ofList (n : ℕ) :
    (uniformList n).map (ofList n) = PMF.uniformOfFintype (BitString n) := by
  simp only [uniformList, PMF.map_comp, Function.comp_def, ofList_ofFn]
  exact PMF.map_id _

/-- Disjoint fixed-width blocks of a uniform list are jointly uniform. -/
theorem uniformList_blocks (count width : ℕ) :
    (uniformList (count * width)).map (fun word => block (ofList (count * width) word)) =
      PMF.uniformOfFintype (Fin count → BitString width) := by
  change (uniformList (count * width)).map (blocksEquiv ∘ ofList (count * width)) = _
  rw [← PMF.map_comp, uniformList_ofList]
  exact PMF.uniformOfFintype_map_equiv blocksEquiv

/-- Extracting fixed-width rows realizes the joint law of independent uniform seeds. -/
theorem uniformList_listRows (count width : ℕ) :
    (uniformList (count * width)).map (listRows count width) =
      (PMF.uniformOfFintype (Fin count → BitString width)).map
        (fun rows => List.ofFn (fun i => List.ofFn (rows i))) := by
  rw [← uniformList_blocks count width, PMF.map_comp]
  congr 1
  funext word
  exact listRows_eq_ofFn count width word

end Cslib.BitString
