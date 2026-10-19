/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.PH
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Complexity.Classes.PH.KarpLipton

/-!
# If NP is in BPP, the polynomial hierarchy collapses to its second level

By Adleman's theorem [Adleman][Adleman1978], [Arora and Barak, Theorem 7.14][AroraBarak09], a
problem decided with bounded error has circuits of polynomial size
(`Cslib.Circuits.Boolean.PPoly.exists_of_mem_BPP`). So `NP ⊆ BPP` gives `NP ⊆ P/poly`, and the
Karp–Lipton theorem [Karp and Lipton][KarpLipton1980], [Arora and Barak, Theorem
6.19][AroraBarak09] collapses the polynomial hierarchy to `Σ₂`
(`Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly`). As there, the hypothesis is stated for
problems with every encoding of their instances.

## Main results

* `Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP`: if `NP ⊆ BPP` for every encoding, then
  `PH = Σ₂`.

## References

* [L. Adleman, *Two theorems on random polynomial time*][Adleman1978]
* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- **`NP ⊆ BPP ⇒ PH = Σ₂`** (Karp–Lipton with Adleman's theorem). If every problem in `NP` is in
`BPP`, for every encoding of its instances, then the polynomial hierarchy collapses to its second
level: `PH = Σ₂`, for every encoding of instances. -/
theorem PH_eq_SigmaP_two_of_NP_subset_BPP
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ BPP encB) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_NP_subset_PPoly fun encB _ hB =>
    Circuits.Boolean.PPoly.exists_of_mem_BPP (h encB hB)

end Cslib.Complexity
