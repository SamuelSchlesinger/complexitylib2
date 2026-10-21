/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Compile
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Uniform computation of word-valued functions

These are the function-valued counterparts of `Program.DecidesInTime` and `PolynomialTime`.
One fixed program returns the specified natural word at every sufficiently large word size
that accommodates the input. Instruction counts include halt. The input convention is the
ordinary `State.init`; loading input words into registers and constructing a maintained
representation must be
part of the certified program. No cost is assigned to the mathematical description of an input
encoding, and no conversion to Turing-machine polynomial time is asserted.

As for `PolynomialTime`, the logarithmic threshold is not an input-fit guarantee. Applications
must separately prove fitting at a size-based width when they claim logarithmic-width execution.
The output must also fit, since it is returned in a bounded machine register.

## Main definitions

* `Program.ComputesInTime`: uniform time-bounded computation of a word-valued function.
* `ComputableInPolyTime`: existence of one program with a polynomial instruction bound.

## Main results

* `Code.computesInTime_program`: a structured certificate includes the final halt.
* `ComputableInPolyTime.of_code`: a structured execution bound proves polynomial RAM time.

## References

See `WordRAM.Time` for the uniform transdichotomous word-size convention and its sources.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ} {α : Type*}

/-- One program returns `f a` within `time a` instructions, uniformly over all fitting widths
above `bits a`. The final halt is counted; the mathematical input encoding is a convention. -/
def Program.ComputesInTime (p : Program B r) (encode : α → List ℕ)
    (time bits : α → ℕ) (f : α → ℕ) : Prop :=
  ∀ a w, bits a ≤ w → InputFits w (encode a) →
    ∃ n, Executes w p (.init (encode a)) (f a) n ∧ n ≤ time a

/-- A fixed program computes the word-valued function with a polynomial instruction bound
uniformly at every fitting width above a logarithmic size threshold. -/
@[fun_prop]
def ComputableInPolyTime (B : Basis) (encode : α → List ℕ) (size : α → ℕ)
    (f : α → ℕ) : Prop :=
  ∃ r, ∃ p : Program B r, ∃ T, PolynomiallyBounded T ∧ ∃ k,
    p.ComputesInTime encode (fun a => T (size a)) (fun a => logWidth k (size a)) f

/-- Increase a uniform time bound or word-size threshold. -/
theorem Program.ComputesInTime.mono {p : Program B r} {encode : α → List ℕ}
    {time time' bits bits' f : α → ℕ} (h : p.ComputesInTime encode time bits f)
    (ht : ∀ a, time a ≤ time' a) (hb : ∀ a, bits a ≤ bits' a) :
    p.ComputesInTime encode time' bits' f := by
  intro a w hw hi
  obtain ⟨n, he, hn⟩ := h a w ((hb a).trans hw) hi
  exact ⟨n, he, hn.trans (ht a)⟩

/-- Structured computation followed by halt gives the same word in one additional instruction. -/
theorem Code.computesInTime_program {encode : α → List ℕ} {time bits f : α → ℕ}
    (c : Code B r) (out : Fin r)
    (h : ∀ a w, bits a ≤ w → InputFits w (encode a) →
      ∃ y, ExecWithin w c (.init (encode a)) y (time a) ∧ y.regs out = f a) :
    (c.program out).ComputesInTime encode (fun a => time a + 1) bits f := by
  intro a w hw hi
  obtain ⟨y, ⟨n, hn, he⟩, hy⟩ := h a w hw hi
  exact ⟨n + 1, hy ▸ he.executes out, Nat.add_le_add_right hn 1⟩

/-- A supplied polynomial bound for complete flat execution yields a function certificate. -/
theorem ComputableInPolyTime.of_program {encode : α → List ℕ} {size f : α → ℕ}
    (p : Program B r) {T : ℕ → ℕ} (hT : PolynomiallyBounded T) (k : ℕ)
    (h : p.ComputesInTime encode (fun a => T (size a)) (fun a => logWidth k (size a)) f) :
    ComputableInPolyTime B encode size f := ⟨r, p, T, hT, k, h⟩

/-- A structured execution certificate yields polynomial RAM time, including the final halt. -/
theorem ComputableInPolyTime.of_code {encode : α → List ℕ} {size f : α → ℕ}
    (c : Code B r) (out : Fin r) {T : ℕ → ℕ} (hT : PolynomiallyBounded T) (k : ℕ)
    (h : ∀ a w, logWidth k (size a) ≤ w → InputFits w (encode a) →
      ∃ y, ExecWithin w c (.init (encode a)) y (T (size a)) ∧ y.regs out = f a) :
    ComputableInPolyTime B encode size f := by
  apply of_program (c.program out) (hT.add (.const 1)) k
  exact c.computesInTime_program out h

end Cslib.WordRAM
