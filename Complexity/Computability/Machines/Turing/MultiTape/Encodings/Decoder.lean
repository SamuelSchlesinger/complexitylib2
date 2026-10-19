/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Total decoders

A decoder for an encoding `enc : α ↪ List Bool` (`Turing.MultiTapeTM.Decoder`) is a function on
all words that inverts `enc` on its image and is tidily computable within bounds of fixed degrees.
On a malformed word it still returns a value, whose encoding has polynomial length.

Decoders are built along the structure of an encoding: unary numbers by their length, options by
testing for the empty word, pairs by reading the framed first component
(`Turing.MultiTapeTM.unframe`) and what follows it (`Turing.MultiTapeTM.dropFrame`), and lists by
splitting a word into framed words (`Turing.MultiTapeTM.frames`) and decoding each. The splitting
is done by a finite-state transducer that closes a final incomplete frame, so that every word
yields a valid encoded list, and the framed words of an encoded list are its encoded elements.

## Main definitions

* `Turing.MultiTapeTM.frames`: the framed words one after another in a word.
* `Turing.MultiTapeTM.Decoder`: total decoders with tidy certificates of fixed degrees.
* `Turing.MultiTapeTM.Decoder.unary`, `.option`, `.pair`, `.list`, `.map`: decoders of unary
  numbers, options, pairs and lists, and transport along an equivalence of encodings.

## Main results

* `Turing.MultiTapeTM.frames_encList`: the framed words of an encoded list are its encoded
  elements.
* `Turing.MultiTapeTM.computableTidilyInDegree_frames`: splitting into framed words is linear.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-! ### Framed words one after another -/

/-- Dropping a frame does not lengthen a word. -/
theorem length_dropFrame_le : ∀ w : List Bool, (dropFrame w).length ≤ w.length
  | [] | [true] => by simp [dropFrame]
  | false :: w => by simp [dropFrame]
  | true :: b :: w => by
    have := length_dropFrame_le w
    simp only [dropFrame, List.length_cons]
    omega

/-- Dropping a frame shortens a nonempty word. -/
theorem length_dropFrame_lt : ∀ {w : List Bool}, w ≠ [] → (dropFrame w).length < w.length
  | [true], _ => by simp [dropFrame]
  | false :: w, _ => by simp [dropFrame]
  | true :: b :: w, _ => by
    have := length_dropFrame_le w
    simp only [dropFrame, List.length_cons]
    omega

/-- The words framed one after another in `w`. A final incomplete frame is closed. -/
def frames (w : List Bool) : List (List Bool) :=
  if _h : w = [] then [] else unframe w :: frames (dropFrame w)
termination_by w.length
decreasing_by exact length_dropFrame_lt (by assumption)

@[simp] theorem frames_nil : frames [] = [] := by
  rw [frames]
  simp

theorem frames_of_ne_nil {w : List Bool} (h : w ≠ []) :
    frames w = unframe w :: frames (dropFrame w) := by
  rw [frames]
  simp [h]

/-- A framed word followed by another word. -/
theorem frames_frame_append (u v : List Bool) : frames (frame u ++ v) = u :: frames v := by
  rw [frames_of_ne_nil (by simp [frame]), unframe_frame_append, dropFrame_frame_append]

/-- **The framed words of an encoded list are its encoded elements.** -/
theorem frames_encList {α : Type*} (enc : α ↪ List Bool) (l : List α) :
    frames (encList enc l) = l.map enc := by
  induction l with
  | nil => exact frames_nil
  | cons a l ih =>
    rw [encList_cons, frames_frame_append, ih, List.map_cons]

/-- The states of the transducer splitting a word into framed words: between frames, inside a
frame after a marker, and inside a frame after a symbol. -/
inductive FramesState
  | between | marker | symbol
  deriving DecidableEq

instance : Finite FramesState :=
  Finite.of_surjective (fun i : Fin 3 => [FramesState.between, .marker, .symbol][i]) fun q => by
    cases q
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- Splits a word into framed words, closing a final incomplete frame. -/
@[simps q₀ step final]
def framesT : Transducer Bool FramesState where
  q₀ := .between
  step
    | .between, true => (.marker, [])
    | .between, false => (.between, [false])
    | .marker, b => (.symbol, [true, b])
    | .symbol, true => (.marker, [])
    | .symbol, false => (.between, [false])
  final
    | .between => []
    | _ => [false]
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le q := by cases q <;> simp

/-- Inside a frame, the transducer completes the frame at the start of its input and continues
with what follows. -/
theorem framesT_run_symbol : ∀ v : List Bool, framesT.run .symbol v =
    frame (unframe v) ++ framesT.run .between (dropFrame v)
  | [] => rfl
  | [true] => rfl
  | false :: v => by simp [unframe, dropFrame, frame]
  | true :: b :: v => by
    simp only [Transducer.run_cons, framesT_step, List.nil_append, unframe, dropFrame,
      frame_cons, List.cons_append, framesT_run_symbol v]

/-- **The transducer emits the encoded list of framed words.** -/
theorem framesT_run (w : List Bool) :
    framesT.run .between w = encList encBits (frames w) := by
  induction w using frames.induct with
  | case1 => rw [frames_nil]; rfl
  | case2 w h ih =>
    rw [frames_of_ne_nil h, encList_cons, ← ih]
    rcases w with _ | ⟨_ | _, v⟩
    · exact absurd rfl h
    · simp [unframe, dropFrame, frame]
    · rcases v with _ | ⟨b, v⟩
      · rfl
      · simp only [Transducer.run_cons, framesT_step, List.nil_append, framesT_run_symbol v,
          unframe, dropFrame, frame_cons, List.cons_append, encBits, Function.Embedding.refl_apply]

/-- **Splitting a word into framed words is linear.** -/
theorem computableTidilyInDegree_frames :
    ComputableTidilyInDegree frames encBits (encList encBits) 1 1 :=
  .of_linear (framesT.computableTidilyInLinearTimeAndSpace fun w => (framesT_run w).symm)

/-! ### Decoders -/

/-- A **total decoder** for the encoding `enc`: a function on all words that inverts `enc` and is
tidily computable within time, space and output length of fixed degrees in the length of the
word. -/
structure Decoder {α : Type} (enc : α ↪ List Bool) where
  /-- The decoded value of any word. -/
  decode : List Bool → α
  /-- Decoding inverts the encoding. -/
  decode_enc (a : α) : decode (enc a) = a
  /-- Decoding is tidily computable within bounds of fixed degrees. -/
  computable : ∃ d e, ComputableTidilyInDegree decode encBits enc d e

namespace Decoder

variable {α β : Type} {enc : α ↪ List Bool} {enc' : β ↪ List Bool}

/-- Unary numbers are decoded by the length of the word. -/
def unary : Decoder encUnary where
  decode w := w.length
  decode_enc n := by simp
  computable := ⟨1, 1, .of_linear (Transducer.computableTidilyInLinearTimeAndSpace
    (τ := ⟨(), fun _ _ => ((), [true]), fun _ => [], fun _ _ => by simp, fun _ => by simp⟩)
    fun w => by induction w <;> simp_all [List.replicate_succ])⟩

/-- Options are decoded as `none` from the empty word, and otherwise from the tail. -/
def option (D : Decoder enc) : Decoder (encOption enc) where
  decode w := if w.isEmpty then none else some (D.decode w.tail)
  decode_enc o := by cases o <;> simp [encOption, D.decode_enc]
  computable := by
    obtain ⟨d, e, hD⟩ := D.computable
    have hsome := (ComputableTidilyInDegree.optionSome (enc₁ := enc)
      (enc := encOption enc)).comp (hD.comp (ComputableTidilyInDegree.tail
        (enc₁ := encBool) (enc := encBits)))
    exact ⟨_, _, ComputableTidilyInDegree.ite (encC := encBool)
      (ComputableTidilyInDegree.isEmpty (enc₁ := encBool) (enc := encBits))
      ((ComputableTidilyInDegree.const none).restrict _) (hsome.restrict _)⟩

/-- Pairs are decoded from the framed first component and what follows it. -/
def pair {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} (D₁ : Decoder enc₁)
    (D₂ : Decoder enc₂) : Decoder (encPair enc₁ enc₂) where
  decode w := (D₁.decode (unframe w), D₂.decode (dropFrame w))
  decode_enc p := by
    simp [unframe_frame_append, dropFrame_frame_append, D₁.decode_enc, D₂.decode_enc]
  computable := by
    obtain ⟨d₁, e₁, h₁⟩ := D₁.computable
    obtain ⟨d₂, e₂, h₂⟩ := D₂.computable
    have hu : ComputableTidilyInDegree unframe encBits encBits 1 1 :=
      .of_linear (.of_unframe fun _ => rfl)
    have hd : ComputableTidilyInDegree dropFrame encBits encBits 1 1 :=
      .of_linear (.of_dropFrame fun _ => rfl)
    exact ⟨_, _, (h₁.comp hu).prod (h₂.comp hd)⟩

/-- Lists are decoded element by element from the framed words of a word. -/
def list (D : Decoder enc) : Decoder (encList enc) where
  decode w := (frames w).map D.decode
  decode_enc l := by
    rw [frames_encList, List.map_map]
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left fun a _ => D.decode_enc a
  computable := by
    obtain ⟨d, e, h⟩ := D.computable
    exact ⟨_, _, ComputableTidilyInDegree.mapWith (encP := encBool) (par := fun _ => false)
      (f := fun p : Bool × List Bool => D.decode p.2)
      (h.comp (ComputableTidilyInDegree.snd encBool encBits))
      ((ComputableTidilyInDegree.const false).mono le_rfl (Nat.zero_le 1))
      computableTidilyInDegree_frames⟩

/-- Transport a decoder to an encoding `enc'` agreeing with `enc` along `f`, where `g` is a right
inverse of `f`. -/
def map (D : Decoder enc) (f : α → β) (g : β → α) (hfg : ∀ b, f (g b) = b)
    (henc : ∀ a, enc' (f a) = enc a) : Decoder enc' where
  decode w := f (D.decode w)
  decode_enc b := by
    conv_lhs => rw [← hfg b, henc, D.decode_enc]
    exact hfg b
  computable :=
    let ⟨d, e, h⟩ := D.computable
    ⟨d, e, h.of_enc_eq fun w => henc _⟩

end Decoder

end Turing.MultiTapeTM
