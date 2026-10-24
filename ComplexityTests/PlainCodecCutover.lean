/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-! Plain codec fields, independent exact bounds, and total decoder clients. -/

open Turing.MultiTapeTM

example : ComputableInLinearTimeAndSpace Prod.fst
    (encPair encBits encNat) encBits := PairEncoding.fst encNat

example : ComputableInLinearTimeAndSpace some encNat (encOption encNat) :=
  OptionEncoding.some

example : ComputableInLinearTimeAndSpace List.tail (encList encNat) (encList encNat) :=
  ListEncoding.tail (enc₁ := encNat)

-- Both input computations have zero workspace and arbitrarily long output. The pairing
-- contract charges the resulting encoded pair, without strengthening either input premise.
example : ∃ c, ComputableInTimeAndSpace (fun w : List Bool => (w, w)) encBits
    (encPair encBits encBits) (fun w => c * (w.length + 1 + 1))
      (fun w => c * (0 + (encPair encBits encBits (w, w)).length + 1)) :=
  PairEncoding.pair (computableInTimeAndSpace_id (enc := encBits))
    (computableInTimeAndSpace_id (enc := encBits))

example : (Decoder.list (Decoder.pair Decoder.nat Decoder.bool)).decode
    (encList (encPair encNat encBool) [(3, true), (7, false)]) = [(3, true), (7, false)] :=
  Decoder.decode_enc _ _

example (D : Decoder encNat) : ∃ d e, ComputableInDegree D.decode encBits encNat d e :=
  D.computable

example (D : Decoder encNat) : ComputableInPolyTime D.decode encBits encNat :=
  D.computableInPolyTime

run_meta do
  if (← Lean.getEnv).contains `Turing.MultiTapeTM.Decoder.computableTidilyInPolyTime then
    throwError "the superseded decoder certificate remains"


example {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : β → γ} {g : α → β}
    (hf : ComputableInLinearTimeAndSpace f encB encC)
    (hg : ComputableInLinearTimeAndSpace g encA encB) :
    ComputableInLinearTimeAndSpace (f ∘ g) encA encC := hf.comp hg

example : ComputableInLinearTimeAndSpace frame encBits encBits :=
  .of_frame fun _ => rfl

run_meta do
  if (← Lean.getEnv).contains `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace then
    throwError "the superseded tidy Linear predicate remains"
