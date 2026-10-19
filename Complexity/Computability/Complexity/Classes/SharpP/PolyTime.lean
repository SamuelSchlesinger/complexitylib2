/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Closure
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Polynomial-time functions as counting functions

Binary-encoded natural outputs of polynomial-time functions are in #P; binary-encoded integer
outputs are in GapP [Fortnow, Theorem 3.5][Fortnow1997]. The verifier guesses a fixed-width
binary word and accepts just those representing values below the computed output. The witness
width bounds the binary output length, not its potentially exponential numeric value.

## Main results

* `SharpP.of_polyTime`: polynomial-time binary natural functions are in #P.
* `GapP.of_polyTime`: polynomial-time binary integer functions are in GapP.

## References

* [L. Fortnow, *Counting Complexity*][Fortnow1997], Theorem 3.5.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- A polynomial-time function with binary natural output is a #P function. -/
theorem SharpP.of_polyTime {f : α → ℕ} (hf : ComputableTidilyInPolyTime f enc encNat) :
    f ∈ SharpP enc := by
  obtain ⟨c, d, hb⟩ := hf.polyBounded_length.exists_le
  let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  refine ⟨p, fun x => decide (BitString.binaryValue x.2 < f x.1), ?_, fun a => ?_⟩
  · exact ComputableTidilyInPolyTime.binary_lt.comp
      ((ComputableTidilyInPolyTime.bitsBinaryValue.comp (.snd enc encBits)).prod
        (hf.comp (.fst enc encBits)))
  · symm
    unfold acceptCount
    simp only [decide_eq_true_eq]
    apply BitString.card_filter_binaryValue_lt
    have hsize : (f a).size ≤ p.eval (enc a).length := by
      simpa [p, encNat_apply, Nat.size_eq_bits_len] using hb a
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by lia) hsize)

/-- A polynomial-time function with binary integer output is a GapP function. -/
theorem GapP.of_polyTime {f : α → ℤ} (hf : ComputableTidilyInPolyTime f enc encIntBin) :
    f ∈ GapP enc := by
  have hp := SharpP.of_polyTime (ComputableTidilyInPolyTime.intBin_toNat.comp hf)
  have hn := SharpP.of_polyTime
    (ComputableTidilyInPolyTime.intBin_toNat.comp (ComputableTidilyInPolyTime.intBin_neg.comp hf))
  exact ⟨_, hp, _, hn, fun a => by simp only [Function.comp_apply]; lia⟩

end Cslib.Complexity
