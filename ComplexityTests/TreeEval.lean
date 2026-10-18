/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.TreeEval.Reader.Correct
import Complexity.Computability.TreeEval.Space

/-!
# Tree Evaluation

A small instance evaluated directly, and the Cook–Mertz procedure over `ZMod 7` on two-bit values:
the field-size hypothesis `2ℓ < |K| - 1` holds, as `4 < 6`, so the correctness theorem is not
vacuous. The iterative machine and the read machine compute the same value.
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

/-- The iterative machine over `ZMod 7` halts with the value of any two-bit instance in register
`2`, as `2 * 2 < 7 - 1`. -/
example {h : ℕ} (T : Tree 2 h) :
    ((Iter.step T 6 (Iter.zmodUnit 7))^[Iter.steps 6 h] Iter.init).regs 2 = embed T.eval := by
  rw [Iter.iterate_step_init_zmod (p := 7) (by decide)]
  simp

/-- The encoding of the sample instance starts with the header `11 0 11 0`. -/
example : sample.encode.take 6 = [true, true, false, true, true, false] := by decide

/-- The read machine halts on the encoding of the sample instance with its value. -/
example : ∃ n s, Reader.machine.run sample.encode n = ⟨s, [false, true]⟩ ∧
    Reader.machine.halt s = true := by
  obtain ⟨n, s, h, hs⟩ := Reader.exists_run_eq sample
  exact ⟨n, s, by rw [h]; congr 1, hs⟩

/-- The encoding of instances tells the sample instance apart from a leaf with its value. -/
example : encInstance ⟨2, 2, sample⟩ ≠ encInstance ⟨2, 0, .leaf ![false, true]⟩ :=
  encInstance.injective.ne (by simp)

open Turing MultiTapeTM Reader in
/-- **Tree Evaluation in small space**: `O((ℓ + H + 1) · log ℓ + log n)`. -/
example : ∃ t, ComputableTidilyInBigO (fun I : Instance => List.ofFn I.tree.eval) encInstance
    encBits t fun I => spaceBound I.ell I.height + (encNat ((encInstance I).length + 1)).length :=
  computableTidilyInSpace_eval

end ComplexityTests.TreeEval
