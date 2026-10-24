/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Degree

/-!
# Plain computability within resource bounds

All notions use one machine for every input, with a binary alphabet and finitely many states.
Time and work-space bounds are independent functions of the input unless a common growth degree
is explicitly specified.

`ComputableInBigO` bounds time by `O(T)` and work space by `O(S)` without charging the output.
`ComputableInO` additionally bounds the encoded output length by `O(S)`. The space-only notions
`ComputableInSpace` and `ComputableInPolySpace` likewise charge the encoded value to their space
bound. Thus these value-charged predicates are stronger than transducer space at sublinear bounds;
`ComputableInLogSpace` and upstream `ComputableInTimeAndSpace` use the transducer convention.

`ComputableInLinearTimeAndSpace` uses a common linear bound in the encoded input length.
`ComputableInDegree` gives time and work space degree `d` and separately gives encoded output
growth degree `e`. Both degrees may be zero: bounds use `(n + 1) ^ d` and `(n + 1) ^ e`.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Chapter 4][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*, Section 2.5][Papadimitriou94]
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*}

/-- `f` is computable within time `O(T a)` and space `O(S a)` on the input `a`, and its encoded
value has length `O(S a)`: for a constant `c`, some machine computes `f` within time `c (T a + 1)`
and space `c (S a + 1)`, and `encOut (f a)` has length at most `c (S a + 1)`.

Unlike the textbook convention and `Turing.MultiTapeTM.ComputableInLogSpace`, the value is charged
to the space bound, as in `Turing.MultiTapeTM.ComputableTidilyInO`; see the module documentation.
-/
def ComputableInO (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (T S : α → ℕ) :
    Prop :=
  ∃ c, ComputableInTimeAndSpace f encIn encOut (fun a => c * (T a + 1)) (fun a => c * (S a + 1)) ∧
    ∀ a, (encOut (f a)).length ≤ c * (S a + 1)

/-- `f` is computable within space `O(S a)` on the input `a`, in some time, and its encoded value
has length `O(S a)`: for a constant `c`, some machine computes `f` within some time and space
`c (S a + 1)`, and `encOut (f a)` has length at most `c (S a + 1)`.

Unlike the textbook convention and `Turing.MultiTapeTM.ComputableInLogSpace`, the value is charged
to the space bound, as in `Turing.MultiTapeTM.ComputableTidilyInSpace`. At sublinear bounds this
notion is strictly stronger than transducer space: with the bound
`fun a => Nat.log2 (encIn a).length` it implies `Turing.MultiTapeTM.ComputableInLogSpace`, but
not conversely. See the module documentation.
-/
def ComputableInSpace (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (S : α → ℕ) :
    Prop :=
  ∃ (t : α → ℕ) (c : ℕ), ComputableInTimeAndSpace f encIn encOut t (fun a => c * (S a + 1)) ∧
    ∀ a, (encOut (f a)).length ≤ c * (S a + 1)

/-- `f` is computable within polynomial space, in some time, and its encoded value has polynomial
length: for a polynomially bounded `s`, some machine computes `f` within some time and space
`s n` on encoded inputs of length `n`, and `encOut (f a)` has length at most `s n`. -/
def ComputableInPolySpace (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) : Prop :=
  ∃ (t : α → ℕ) (s : ℕ → ℕ), Cslib.PolynomiallyBounded s ∧
    ComputableInTimeAndSpace f encIn encOut t (fun a => s (encIn a).length) ∧
    ∀ a, (encOut (f a)).length ≤ s (encIn a).length

/-- Linear-time and linear-work-space computability, with one existential constant and no
clean-tape requirement. The encoded output length is bounded by the time of the computation. -/
def ComputableInLinearTimeAndSpace (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ c, ComputableInTimeAndSpace f encIn encOut
    (fun a => c * ((encIn a).length + 1)) (fun a => c * ((encIn a).length + 1))

/-- Polynomial time and work space of degree `d`, and encoded output growth of degree `e`.
The realization is one machine for all inputs. Both degrees may be zero. -/
def ComputableInDegree (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (d e : ℕ) : Prop :=
  (∃ t s, DegreeBounded (fun a => (encIn a).length) t d ∧
    DegreeBounded (fun a => (encIn a).length) s d ∧
    ComputableInTimeAndSpace f encIn encOut t s) ∧
  DegreeBounded (fun a => (encIn a).length) (fun a => (encOut (f a)).length) e

/-- `f` is computable within time `O(T a)` and space `O(S a)` on the input `a`. -/
def ComputableInBigO {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (T S : α → ℕ) : Prop :=
  ∃ c, ComputableInTimeAndSpace f encIn encOut (fun a => c * (T a + 1)) fun a => c * (S a + 1)

end Turing.MultiTapeTM
