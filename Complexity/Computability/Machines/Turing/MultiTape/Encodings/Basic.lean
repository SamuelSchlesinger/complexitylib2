/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Fintype.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding

/-!
# Word operations for encodings

The building blocks of concrete encodings of pairs, options and lists, and their tidy computability
in linear time and space (`Turing.MultiTapeTM.ComputableInLinearTimeAndSpace`).

A word `w` is *framed* by writing each symbol `b` as `[true, b]` and appending `[false]`. A framed
word marks its own end, so it can be followed by any word and still be read back.

## Main definitions

* `Turing.MultiTapeTM.frame`: the framed word.
* `Turing.MultiTapeTM.unframe`, `Turing.MultiTapeTM.dropFrame`: the word framed at the start of a
  word, and what follows the frame.

## Main results

* `Turing.MultiTapeTM.frame_append_inj`: a framed word followed by another word determines both.
* Functions that act on encoded values by `frame`, `unframe`, `dropFrame`, `List.cons true`,
  `List.tail` or `List.take 1`, or that test the encoded value for emptiness, are tidily computable
  in linear time and space.
-/

namespace Turing.MultiTapeTM

/-! ### Framed words -/

/-- Each symbol `b` of `w` as `[true, b]`, followed by `[false]`. -/
@[expose] public def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- The word framed at the start of `v`, see `Turing.MultiTapeTM.frame`. -/
@[expose] public def unframe : List Bool → List Bool
  | true :: b :: v => b :: unframe v
  | _ => []

/-- What follows the frame at the start of `v`, see `Turing.MultiTapeTM.frame`. -/
@[expose] public def dropFrame : List Bool → List Bool
  | true :: _ :: v => dropFrame v
  | false :: v => v
  | _ => []

@[simp]
public lemma frame_nil : frame [] = [false] := rfl

@[simp]
public lemma frame_cons (b : Bool) (w : List Bool) : frame (b :: w) = true :: b :: frame w := rfl

@[simp]
public lemma length_frame (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w <;> simp [*]; omega

@[simp]
public lemma unframe_frame_append (w u : List Bool) : unframe (frame w ++ u) = w := by
  induction w <;> simp [unframe, *]

@[simp]
public lemma unframe_frame (w : List Bool) : unframe (frame w) = w := by
  simpa using unframe_frame_append w []

@[simp]
public lemma dropFrame_frame_append (w u : List Bool) : dropFrame (frame w ++ u) = u := by
  induction w <;> simp [dropFrame, *]

/-- A framed word followed by another word determines both. -/
public theorem frame_append_inj {w w' u u' : List Bool} (h : frame w ++ u = frame w' ++ u') :
    w = w' ∧ u = u' :=
  ⟨by simpa using congrArg unframe h, by simpa using congrArg dropFrame h⟩

/-- Framing is injective. -/
public theorem frame_injective : Function.Injective frame := fun _ _ h =>
  (frame_append_inj (u := []) (u' := []) (by simpa using h)).1

@[simp]
public lemma frame_ne_nil (w : List Bool) : frame w ≠ [] := by simp [frame]

/-! ### Transducers for the word operations -/

namespace Encodings

/-- The states of a transducer reading a framed word: expecting a marker, expecting a symbol, or
past the frame. -/
inductive FrameState
  | marker
  | bit
  | done

instance : Finite FrameState :=
  Finite.of_surjective (fun b : Option Bool => b.elim .done fun b => if b then .marker else .bit)
    fun q => by cases q; exacts [⟨some true, rfl⟩, ⟨some false, rfl⟩, ⟨none, rfl⟩]

-- vendored: expose `frameT` and `frameT_run` for `computableInLogSpace_frame`; private upstream.
/-- Frames its input. -/
@[expose, simps q₀ step final]
public def frameT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [true, b])
  final _ := [false]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

public lemma frameT_run (v : List Bool) : frameT.run () v = frame v := by
  induction v <;> simp [*]

/-- Emits the word framed at the start of its input (`keep = true`), or what follows the frame
(`keep = false`). -/
@[simps q₀ step final]
def readFrameT (keep : Bool) : Transducer Bool FrameState where
  q₀ := .marker
  step
    | .marker, true => (.bit, [])
    | .marker, false => (.done, [])
    | .bit, b => (.marker, if keep then [b] else [])
    | .done, b => (.done, if keep then [] else [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> cases keep <;> simp
  length_final_le _ := by simp

lemma readFrameT_run_done (keep : Bool) (v : List Bool) :
    (readFrameT keep).run .done v = if keep then [] else v := by
  induction v <;> cases keep <;> simp_all

lemma readFrameT_run_true : ∀ v, (readFrameT true).run .marker v = unframe v
  | [] | [true] => rfl
  | false :: v => by simp [unframe, readFrameT_run_done]
  | true :: b :: v => by simp [unframe, readFrameT_run_true v]

lemma readFrameT_run_false : ∀ v, (readFrameT false).run .marker v = dropFrame v
  | [] | [true] => rfl
  | false :: v => by simp [dropFrame, readFrameT_run_done]
  | true :: b :: v => by simp [dropFrame, readFrameT_run_false v]

/-- Emits a word determined by its input's first symbol, if any, and by `drop`: `[true]` followed by
the input (`drop = none`), the input without its first symbol (`drop = some false`), or just the
first symbol (`drop = some true`). -/
@[simps q₀ step final]
def headT (drop : Option Bool) : Transducer Bool Bool where
  q₀ := false
  step
    | false, b => (true, match drop with | none => [true, b] | some false => [] | some true => [b])
    | true, b => (true, match drop with | none => [b] | some false => [b] | some true => [])
  final
    | false => match drop with | none => [true] | _ => []
    | true => []
  length_step_le q b := by cases q <;> rcases drop with _ | _ | _ <;> simp
  length_final_le q := by cases q <;> rcases drop with _ | _ | _ <;> simp

lemma headT_run_true (drop : Option Bool) (v : List Bool) :
    (headT drop).run true v = if drop = some true then [] else v := by
  induction v <;> rcases drop with _ | _ | _ <;> simp_all

/-- Emits `[true]` on the empty word and `[false]` on every other word. -/
@[simps q₀ step final]
def isEmptyT : Transducer Bool Bool where
  q₀ := false
  step q _ := (true, if q then [] else [false])
  final q := if q then [] else [true]
  length_step_le q _ := by cases q <;> simp
  length_final_le q := by cases q <;> simp

lemma isEmptyT_run_true (v : List Bool) : isEmptyT.run true v = [] := by
  induction v <;> simp [*]

end Encodings

open Encodings

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `encOfEquiv` below, from that revision's `Encodings/Basic`
/-- The encoding of `α` through an equivalence with `β`, such as that of a structure with the
tuple of its fields. -/
@[expose] public def encOfEquiv {α β : Type*} (e : α ≃ β) (enc : β ↪ List Bool) :
    α ↪ List Bool :=
  e.toEmbedding.trans enc

@[simp] public lemma encOfEquiv_apply {α β : Type*} (e : α ≃ β) (enc : β ↪ List Bool) (a : α) :
    encOfEquiv e enc a = enc (e a) := rfl

namespace ComputableInLinearTimeAndSpace

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}

/-- Framing an encoded value. -/
public theorem of_frame (h : ∀ a, encOut (f a) = frame (encIn a)) :
    ComputableInLinearTimeAndSpace f encIn encOut :=
  frameT.computableInLinearTimeAndSpace fun a => by rw [h, frameT_run]

/-- Reading the word framed at the start of an encoded value. -/
public theorem of_unframe (h : ∀ a, encOut (f a) = unframe (encIn a)) :
    ComputableInLinearTimeAndSpace f encIn encOut :=
  (readFrameT true).computableInLinearTimeAndSpace fun a =>
    (h a).trans (readFrameT_run_true _).symm

/-- Dropping the frame at the start of an encoded value. -/
public theorem of_dropFrame (h : ∀ a, encOut (f a) = dropFrame (encIn a)) :
    ComputableInLinearTimeAndSpace f encIn encOut :=
  (readFrameT false).computableInLinearTimeAndSpace fun a =>
    (h a).trans (readFrameT_run_false _).symm

/-- Prepending `true` to an encoded value. -/
public theorem of_cons_true (h : ∀ a, encOut (f a) = true :: encIn a) :
    ComputableInLinearTimeAndSpace f encIn encOut :=
  (headT none).computableInLinearTimeAndSpace fun a => by
    rw [h]
    cases encIn a <;> simp [headT_run_true]

/-- Dropping the first symbol of an encoded value. -/
public theorem of_tail (h : ∀ a, encOut (f a) = (encIn a).tail) :
    ComputableInLinearTimeAndSpace f encIn encOut :=
  (headT (some false)).computableInLinearTimeAndSpace fun a => by
    rw [h]
    cases encIn a <;> simp [headT_run_true]

/-- Keeping just the first symbol of an encoded value. -/
public theorem of_take_one (h : ∀ a, encOut (f a) = (encIn a).take 1) :
    ComputableInLinearTimeAndSpace f encIn encOut :=
  (headT (some true)).computableInLinearTimeAndSpace fun a => by
    rw [h]
    cases encIn a <;> simp [headT_run_true]

/-- Testing an encoded value for emptiness. -/
public theorem of_isEmpty {f : α → Bool} (h : ∀ a, f a = (encIn a).isEmpty) :
    ComputableInLinearTimeAndSpace f encIn encBool :=
  isEmptyT.computableInLinearTimeAndSpace fun a => by
    rw [h]
    cases encIn a <;> simp [isEmptyT_run_true]

/-- A function with a fixed value `d` on the input encoded by the empty word, and computable
in linear time and space on the other inputs. -/
public theorem of_isEmpty_ite (d : β) (hd : ∀ a, encIn a = [] → f a = d)
    (h : ComputableInLinearTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype fun a => (encIn a).isEmpty = false).trans encIn) encOut) :
    ComputableInLinearTimeAndSpace f encIn encOut := by
  convert ite (c := fun a => (encIn a).isEmpty) (of_isEmpty fun _ => rfl) ((const d).restrict _) h
    using 1
  funext a
  split_ifs with ha <;> simp_all

end ComputableInLinearTimeAndSpace

end Turing.MultiTapeTM
