/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Translate
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-! A bit-emitting translator preserves an unbounded accumulated word. -/
namespace ComplexityTests.PlainTranslatorCutover
open Turing.MultiTapeTM

private def emitsBits : Translator Unit Bool := ⟨(), fun _ b => ((), some b)⟩

example : ∃ T S, ComputableInO
    (emitsBits.lift fun p : List Bool × Bool => p.1 ++ [p.2])
    (encPair (encPair (encFinite Unit) (encList encBool)) encBool)
    (encPair (encFinite Unit) (encList encBool)) T S :=
  ⟨_, _, ComputableInO.lift emitsBits (ComputableInDegree.snoc encBool).inO_one⟩

example (s : List Bool) (b : Bool) :
    emitsBits.lift (fun p : List Bool × Bool => p.1 ++ [p.2]) (((), s), b) =
      ((), s ++ [b]) := rfl

private theorem run_eq (w : List Bool) : emitsBits.run () w = ((), w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change ((emitsBits.run () w).1, b :: (emitsBits.run () w).2) = ((), b :: w)
    rw [ih]

example (w : List Bool) : emitsBits.events w = w :=
  congrArg Prod.snd (run_eq w)

example (w : List Bool) (s : List Bool) :
    w.foldl (fun p b => emitsBits.lift (fun q : List Bool × Bool => q.1 ++ [q.2]) (p, b))
      ((), s) = ((), w.foldl (fun a b => a ++ [b]) s) := by
  rw [Translator.foldl_lift, run_eq]

end ComplexityTests.PlainTranslatorCutover
