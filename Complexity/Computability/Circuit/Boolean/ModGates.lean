/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AC0

/-!
# AC⁰[q]

The basis of AC⁰ together with `MOD_q` gates of unbounded fan-in, which output `true` exactly when
the number of their true inputs is not divisible by `q`, and the class **AC⁰[q]** of languages
decided by such circuits of polynomial size and constant depth [Arora and Barak, Chapter 14]
[AroraBarak09].

## Main definitions

* `Cslib.Circuits.Boolean.ModBasis.signature`: the AC⁰ basis with `MOD_q` gates.
* `Cslib.Circuits.Boolean.ModBasis.AC0Mod`: the class AC⁰[q].

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.ModBasis

/-- The operations of the AC⁰ basis, and `MOD_q` of `m` arguments for every `m`. -/
inductive Op where
  /-- An operation of the AC⁰ basis. -/
  | ac (op : Unbounded.Op)
  /-- The `MOD_q` gate of `m` arguments. -/
  | mod (m : ℕ)
  deriving DecidableEq

/-- The arity of an operation. -/
abbrev Op.arity : Op → ℕ
  | .ac op => op.arity
  | .mod m => m

/-- The signature of the AC⁰ basis with `MOD_q` gates. It is reducible, so that case analysis on its
operations sees their arities. -/
abbrev signature : Signature :=
  ⟨Op, Op.arity⟩

/-- Whether the number of true bits of `x` is not divisible by `q`. -/
def modGate (q m : ℕ) (x : Fin m → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => x i = true).card % q ≠ 0)

/-- The Boolean meaning of the operations, with `MOD_q` gates. -/
def interpretation (q : ℕ) : Interpretation signature Bool
  | .ac op, x => Unbounded.interpretation op x
  | .mod m, x => modGate q m x

/-- The AC⁰ basis inside the basis with `MOD_q` gates. -/
def ofUnbounded : Unbounded.signature.Hom signature :=
  ⟨Op.ac, fun _ => rfl⟩

/-- **AC⁰[q]**: the languages over `Bool` decided, at every input length, by circuits with `MOD_q`
gates of polynomially bounded size and constant depth. -/
def AC0Mod (q : ℕ) : Set (Language Bool) :=
  ConstDepth (interpretation q)

/-- **AC⁰ ⊆ AC⁰[q]**: every AC⁰ circuit is a circuit with `MOD_q` gates. -/
theorem AC0_subset_AC0Mod (q : ℕ) : Unbounded.AC0 ⊆ AC0Mod q :=
  ConstDepth.mono (φ := ofUnbounded) fun _ _ => rfl

end Cslib.Circuits.Boolean.ModBasis
