/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.TreeEval.CookMertz

/-!
# Tree Evaluation

A small instance evaluated directly, and the Cook–Mertz procedure over `ZMod 7` on two-bit values:
the field-size hypothesis `2ℓ < |K| - 1` holds, as `4 < 6`, so the correctness theorem is not
vacuous.
-/

namespace ComplexityTests.TreeEval

open Cslib.TreeEval

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Bitwise exclusive or of two two-bit values. -/
def xorGate (x y : Fin 2 → Bool) : Fin 2 → Bool := fun i => x i ^^ y i

/-- Bitwise conjunction of two two-bit values. -/
def andGate (x y : Fin 2 → Bool) : Fin 2 → Bool := fun i => x i && y i

/-- A height-two instance: `(10 ⊕ 11) ∧ (01 ⊕ 00) = 01 ∧ 01`. -/
def sample : Tree 2 2 :=
  .node andGate (.node xorGate (.leaf ![true, false]) (.leaf ![true, true]))
    (.node xorGate (.leaf ![false, true]) (.leaf ![false, false]))

example : sample.eval = ![false, true] := by decide

/-- The Cook–Mertz procedure over `ZMod 7` computes the value of the sample instance. -/
example : proc (Finset.univ : Finset (ZMod 7)ˣ).toList sample 1 2 0 2 =
    embed ![false, true] := by
  rw [← embed_eval_eq_proc (by simp) sample 2]
  congr 1
  decide

/-- Any two-bit instance over `ZMod 7` is computed by the procedure, for every target register. -/
example {h : ℕ} (T : Tree 2 h) (t : Fin 3) :
    embed T.eval = proc (Finset.univ : Finset (ZMod 7)ˣ).toList T 1 t 0 t :=
  embed_eval_eq_proc (by simp) T t

end ComplexityTests.TreeEval
