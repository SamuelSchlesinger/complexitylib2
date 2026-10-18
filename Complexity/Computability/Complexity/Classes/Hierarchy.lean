/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Decode
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# A decidable problem outside P

The diagonal function `Cslib.Complexity.diagonal` reads a description of a machine framed at the
start of its input `x` (`Turing.MultiTapeTM.Universal.decodeDesc`), runs the described machine on
the whole of `x`, symbol by symbol under the fixed coding `false ↦ 0`, `true ↦ 1`, for
`2 ^ x.length` steps with the universal function, and negates the verdict: it returns `false`
exactly when the described machine has halted with output `[true]` by then.

No machine computing a Boolean function in polynomial time decides the diagonal problem
[Arora and Barak, Theorem 3.1][AroraBarak09]. Its description, padded to a length where the machine
halts within the exponential clock, is an input on which the diagonal returns the negation of the
machine's answer (`Cslib.Complexity.diagonal_not_mem_P`).

## Main definitions

* `Cslib.Complexity.diagonal`: the diagonal function.

## Main results

* `Cslib.Complexity.diagonal_not_mem_P`: the diagonal problem is not in `P`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]

The padded diagonal argument follows the original Complexitylib's `Classes/Hierarchy` and
`UTM/Diagonal` (Samuel Schlesinger), here on the native universal interpreter of Christian
Reitwiessner.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- The fixed coding of Boolean symbols by numbers: `false ↦ 0` and `true ↦ 1`. -/
def boolSym : Bool ↪ ℕ := ⟨Bool.toNat, fun a b h => by cases a <;> cases b <;> simp_all⟩

/-- **The diagonal function.** Run the machine described at the start of `x` on `x` for
`2 ^ x.length` steps, and return `false` exactly when it has halted with output `[true]`. -/
def diagonal (x : List Bool) : Bool :=
  let r := universal (decodeDesc (unframe x), x.map boolSym, 2 ^ x.length)
  !(r.2 && r.1 == [boolSym true])

/-- On its padded description, the diagonal negates the answer of a machine that halts within the
exponential clock. -/
theorem diagonal_desc {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (pad : List Bool) {b : Bool}
    (hhalt : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS boolSym tm)) ++ pad))
      (2 ^ (frame (eDesc (desc eS boolSym tm)) ++ pad).length)).Halted)
    (hout : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS boolSym tm)) ++ pad))
      (2 ^ (frame (eDesc (desc eS boolSym tm)) ++ pad).length)).output = [b]) :
    diagonal (frame (eDesc (desc eS boolSym tm)) ++ pad) = !b := by
  rw [diagonal, decodeDesc_unframe_frame_append, universal_desc, hout]
  simp only [List.map_cons, List.map_nil, Cfg.Halted] at hhalt ⊢
  rw [hhalt]
  cases b <;> simp [boolSym]

/-- **The diagonal problem is not in `P`** [Arora and Barak, Theorem 3.1][AroraBarak09]. -/
theorem diagonal_not_mem_P : {x | diagonal x = true} ∉ P encBits := by
  rintro ⟨f, ⟨t, s, ht, -, k, State, hfinite, tm, htm⟩, hf⟩
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  -- a padding beyond which the machine halts within the exponential clock
  obtain ⟨c, d, hle⟩ := ht.exists_le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (PolynomiallyBounded.eventually_lt_two_pow (f := fun n => c * (n + 1) ^ d) (by fun_prop))
  set x := frame (eDesc (desc eS boolSym tm)) ++ List.replicate N false with hx
  have hlen : N ≤ x.length := by simp [x]
  have htime : t x ≤ 2 ^ x.length := (hle x).trans (hN _ hlen).le
  obtain ⟨hhalt, hout⟩ := ComputesTidilyInTimeAndSpace.runFrom_initCfg (htm x)
  have heq := MultiTapeTM.runFrom_eq_of_halt tm _ htime hhalt
  have hhalt' : (tm.runFrom (tm.initCfg x) (2 ^ x.length)).Halted :=
    (congrArg Cfg.Halted heq).mpr hhalt
  have hout' : (tm.runFrom (tm.initCfg x) (2 ^ x.length)).output = [f x] :=
    (congrArg Cfg.output heq).trans hout
  have hdiag := diagonal_desc eS tm _ hhalt' hout'
  have hfx : f x = diagonal x := by
    cases h : diagonal x
    · cases hfx : f x
      · rfl
      · exact absurd ((hf x).mpr hfx) (by simp [h])
    · exact (hf x).mp h
  rw [← hfx] at hdiag
  cases hb : f x <;> simp [hb] at hdiag

end Cslib.Complexity
