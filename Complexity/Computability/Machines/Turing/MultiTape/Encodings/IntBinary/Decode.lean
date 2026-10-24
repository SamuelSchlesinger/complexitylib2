/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-!
# Total decoding of binary signed integers

Read a sign bit and a binary magnitude. Missing data is zero, surplus high zero bits are
ignored, and negative zero is normalized to zero. This reuses the existing natural-number
decoder and sign/magnitude arithmetic. The roundtrip applies to every canonical `encIntBin`
word; total decoding alone is not a canonical-input validator.

## Main definitions

* `Turing.MultiTapeTM.decodeIntBin`: total sign/magnitude decoding.

## Main results

* `Turing.MultiTapeTM.decodeIntBin_encIntBin`: exact roundtrip.
* `Turing.MultiTapeTM.computableInPolyTime_decodeIntBin`: the complete plain decoding contract.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Decode any sign/magnitude word; malformed and negative-zero words still decode totally. -/
def decodeIntBin (word : List Bool) : ℤ :=
  let magnitude := Decoder.nat.decode word.tail
  if word.headD false then -(magnitude : ℤ) else magnitude

/-- Every canonical signed binary word decodes to its original integer. -/
@[simp] theorem decodeIntBin_encIntBin (z : ℤ) : decodeIntBin (encIntBin z) = z := by
  simp only [decodeIntBin, encIntBin_apply, List.tail_cons, List.headD_cons]
  change (if decide (z < 0) then -((Decoder.nat.decode (encNat z.natAbs) : ℕ) : ℤ)
    else ((Decoder.nat.decode (encNat z.natAbs) : ℕ) : ℤ)) = z
  rw [Decoder.nat.decode_enc]
  by_cases h : z < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (by omega : 0 ≤ z)]

/-- Binary sign/magnitude decoding is uniformly plain polynomial time on arbitrary words. -/
@[fun_prop]
theorem computableInPolyTime_decodeIntBin :
    ComputableInPolyTime decodeIntBin encBits encIntBin := by
  apply ComputableInPolyTime.of_tidy
  have hsign : ComputableTidilyInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := ComputableTidilyInPolyTime.headD false
  have hmag := Decoder.nat.computableTidilyInPolyTime.comp ComputableTidilyInPolyTime.bitsTail
  exact ComputableTidilyInPolyTime.intBin_signMagnitude.comp (hsign.prod hmag)

end Turing.MultiTapeTM
