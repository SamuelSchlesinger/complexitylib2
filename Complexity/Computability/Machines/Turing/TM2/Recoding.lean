/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Computability.Machines.Turing.TM2.PolyTime
public import Complexity.Computability.Machines.Turing.TM2.PolySpace

/-!
# Removing the stack-machine bridge's word recoding

Raw binary words and lists of encoded Boolean symbols convert in polynomial time. Applying
these word conversions after an arbitrary embedding requires no decoder for that embedding.
The list interface parses the frames; only the two Boolean symbols need a finite conversion.

## Main results

* `Turing.MultiTapeTM.bits_encList_polyTime`: raw and framed binary words are equivalent.
* `Turing.MultiTapeTM.trans_encList_polyTime`: the equivalence after any binary embedding.
* `Turing.TM2ComputableInPolyTime.computableInPolyTime`: forward polynomial-time transfer.
* `Turing.TM2Computable.computableInPolySpace`: forward polynomial-space transfer.

## References

The word conventions are those of the forward bridges `TM2.PolyTime` and `TM2.PolySpace`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open ComputableTidilyInPolyTime

private theorem foldl_snoc (word acc : List Bool) :
    word.foldl (fun acc bit => acc ++ [bit]) acc = acc ++ word := by
  induction word generalizing acc with
  | nil => simp
  | cons bit word ih => simp only [List.foldl_cons, ih, List.append_assoc, List.singleton_append]

/-- Framing a fixed Boolean encoding, or parsing its frames and converting each symbol, takes
polynomial time. The encodings of `false` and `true` can be arbitrary fixed words. -/
theorem bits_encList_polyTime (enc : Bool ↪ List Bool) :
    ComputableInPolyTime (fun word => word) encBits (encList enc) ∧
      ComputableInPolyTime (fun word => word) (encList enc) encBits := by
  let C := 2 * max (enc false).length (enc true).length + 1
  have hsymbol (bit : Bool) : (enc bit).length ≤ max (enc false).length (enc true).length := by
    cases bit
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hforward := foldl' (encA := encBool) (encL := encBits) (encB := encList enc)
    (step := fun acc bit => acc ++ [bit]) id' (const [])
    ((ComputableTidilyInDegree.snoc enc).computableTidilyInPolyTime.comp
      ((fst (encList enc) encBool).prod
        ((of_finite (id : Bool → Bool) (encA := encBool) (encB := enc)).comp
          (snd (encList enc) encBool))))
    (B := fun word : List Bool => word.length * C)
    (PolyBounded.self.mul (.const C)) (by
      intro word i hi
      simp only [foldl_snoc, List.nil_append]
      exact (length_encList_le enc _ (fun bit _ => hsymbol bit)).trans
        (Nat.mul_le_mul_right C (by simp only [List.length_take]; omega)))
  have hreverse := foldl' (encA := enc) (encL := encList enc) (encB := encBits)
    (step := fun acc bit => acc ++ [bit]) id' (const [])
    (bitsAppend (fst encBits enc)
      ((of_finite (fun bit : Bool => [bit]) (encA := enc) (encB := encBits)).comp
        (snd encBits enc)))
    (B := fun word : List Bool => (encList enc word).length)
    PolyBounded.self (by
      intro word i hi
      simp only [foldl_snoc, List.nil_append, encBits_apply, List.length_take]
      exact (Nat.min_le_right _ _).trans (length_le_length_encList enc word))
  constructor
  · simpa only [foldl_snoc, List.nil_append, id_eq] using ComputableInPolyTime.of_tidy hforward
  · simpa only [foldl_snoc, List.nil_append, id_eq] using ComputableInPolyTime.of_tidy hreverse

/-- The word conversion preserves an arbitrary caller-supplied encoding. No computable inverse
of `encIn` is assumed: expose its word, convert that word, and reuse the resulting encoding. -/
theorem trans_encList_polyTime {α : Type} (encIn : α ↪ List Bool)
    (enc : Bool ↪ List Bool) :
    ComputableInPolyTime (fun a => a) encIn (encIn.trans (encList enc)) ∧
      ComputableInPolyTime (fun a => a) (encIn.trans (encList enc)) encIn := by
  obtain ⟨hforward, hreverse⟩ := bits_encList_polyTime enc
  constructor
  · exact .of_tidy ((hforward.tidy.comp (encode encIn)).of_enc_eq fun _ => rfl)
  · have hexpose : ComputableTidilyInPolyTime encIn (encIn.trans (encList enc))
        (encList enc) := of_eq fun _ => rfl
    exact .of_tidy ((hreverse.tidy.comp hexpose).of_enc_eq fun _ => rfl)

end Turing.MultiTapeTM

namespace Turing.TM2ComputableInPolyTime

open MultiTapeTM

/-- The binary specialization of the forward bridge preserves the supplied encodings, without
requiring either encoding to have a computable inverse. -/
theorem computableInPolyTime {α β : Type}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime encIn encOut f) [∀ stack, Finite (h.tm.Γ stack)] :
    ComputableInPolyTime f encIn encOut := by
  apply ComputableInPolyTime.of_tidy
  have hf := h.computableTidilyInPolyTime encIn.injective encOut.injective
  obtain ⟨hinput, _⟩ := trans_encList_polyTime encIn (encFinite Bool)
  obtain ⟨_, houtput⟩ := trans_encList_polyTime encOut (encFinite Bool)
  simpa only [Function.comp_def] using houtput.tidy.comp (hf.comp hinput.tidy)

end Turing.TM2ComputableInPolyTime

namespace Turing.TM2Computable

open MultiTapeTM

/-- Termination and polynomially bounded stacks transfer to the original binary encodings.
All target stacks, including the input and output stacks, count towards the bound. -/
theorem computableInPolySpace {α β : Type}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (h : TM2Computable encIn encOut f) [∀ stack, Finite (h.tm.Γ stack)]
    {space : α → ℕ} (hspace : PolyBounded (fun a => (encIn a).length) space)
    (hstacks : ∀ a i stack,
      (((TM2.stepTotal h.tm.m)^[i]
        (initList h.tm (List.map h.inputAlphabet.symm (encIn a)))).stk stack).length ≤ space a) :
    ComputableInPolySpace f encIn encOut := by
  apply ComputableInPolySpace.of_tidy
  have hf := h.computableTidilyInPolySpace encIn.injective encOut.injective hspace hstacks
  obtain ⟨hinput, _⟩ := trans_encList_polyTime encIn (encFinite Bool)
  obtain ⟨_, houtput⟩ := trans_encList_polyTime encOut (encFinite Bool)
  simpa only [Function.comp_def] using
    (ComputableTidilyInPolySpace.of_polyTime houtput.tidy).comp
      (hf.comp (ComputableTidilyInPolySpace.of_polyTime hinput.tidy))

end Turing.TM2Computable
