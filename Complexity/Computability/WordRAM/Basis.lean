/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (after Circuit/SignatureHom)

public import Complexity.Init
public import Complexity.Computability.Circuit.SignatureHom

/-!
# Operation bases for word RAMs

Word-RAM models differ in their arithmetic and logical instructions. Hagerup distinguishes the
restricted RAM, without multiplication, from the multiplication RAM [Hagerup][Hagerup1998], and the
AC⁰ RAM allows only operations computed by polynomial-size constant-depth circuits, which excludes
multiplication [Andersson, Miltersen and Thorup][AnderssonMiltersenThorup1999]. Linear-time and
data-structure bounds can depend on this choice.

A *basis* (`Cslib.WordRAM.Basis`) fixes these operations, as a circuit basis does: a signature of
operation symbols with arities (`Cslib.Circuits.Signature`), and an interpretation of every symbol
on natural numbers at each word size `w`. The machine itself, its registers, memory, control flow
and overflow faults are the same for every basis; an operation whose value does not fit a word
faults like any other. A basis also marks the operations that may depend on the word size, so that
programs avoiding them run in the same way at every larger word size.

Bases are compared by meaning-preserving maps of their operations (`Cslib.WordRAM.Basis.Hom`),
built on `Cslib.Circuits.Signature.Hom`. A program over a basis runs instruction for instruction
over a larger one; `Cslib.WordRAM.Basis.restrict` gives the sub-bases of a basis.

## Main definitions

* `Cslib.WordRAM.Basis`: operation symbols, their meaning at each word size, and the symbols whose
  meaning depends on the word size.
* `Cslib.WordRAM.BinOp`, `Cslib.WordRAM.StandardOp`, `Cslib.WordRAM.Basis.standard`: the standard
  word-RAM operations: addition, subtraction, multiplication, bitwise operations and shifts as in
  [Hagerup][Hagerup1998], together with division, remainder and the word size.
* `Cslib.WordRAM.Basis.Hom`: a map of bases that keeps the meaning of every operation.
* `Cslib.WordRAM.Basis.restrict`: the sub-basis of the operations satisfying a predicate.
* `Cslib.WordRAM.Basis.additive`, `Cslib.WordRAM.Basis.arithmetic`: addition and subtraction; and
  these with multiplication, division and remainder, the operation symbols of the bounded-word RAM
  of [MIT–ULB CompGeom Group][Tromino2025], on unsigned words with truncated subtraction.

## Main results

* `Cslib.WordRAM.Basis.Hom.interp_map`: the image of an operation under a map of bases has the
  operation's value.
* `Cslib.WordRAM.Basis.arithmeticHomStandard_comp_additiveHomArithmetic`: the inclusions of the
  named bases commute.

## References

* [A. Andersson, P. B. Miltersen and M. Thorup, *Fusion trees can be implemented with AC⁰
  instructions only*][AnderssonMiltersenThorup1999]
* [M. L. Fredman and D. E. Willard, *Surpassing the information theoretic bound with fusion
  trees*][FredmanWillard1993]
* [T. Hagerup, *Sorting and searching on the word RAM*][Hagerup1998]
* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]
-/

@[expose] public section

namespace Cslib.WordRAM

open Cslib.Circuits

/-- A basis of word operations: a signature of operation symbols, the value of each operation at
each word size, and the operations that may read the word size. An operation that does not read
the word size has the same value at every word size. Whether a value fits a word is checked by the
machine, not by the basis. -/
structure Basis extends Signature.{0} where
  /-- Operation symbols have decidable equality, so that programs do. -/
  [decEq : DecidableEq Op]
  /-- The operations whose value may depend on the word size. -/
  ReadsWidth : Op → Prop
  /-- Whether an operation reads the word size is decidable. -/
  [decReadsWidth : DecidablePred ReadsWidth]
  /-- The value of every operation at word size `w`. -/
  interp : ℕ → Interpretation toSignature ℕ
  /-- An operation that does not read the word size has the same value at every word size. -/
  interp_eq_of_not_readsWidth (f : Op) (hf : ¬ReadsWidth f) (w w' : ℕ)
    (args : Fin (Arity f) → ℕ) : interp w f args = interp w' f args

attribute [instance] Basis.decEq Basis.decReadsWidth

/-! ## The standard basis -/

/-- The binary operations of the word RAM. -/
inductive BinOp where
  /-- Addition. -/
  | add
  /-- Truncated subtraction. -/
  | sub
  /-- Multiplication. -/
  | mul
  /-- Division, rounding down. -/
  | div
  /-- Remainder. -/
  | mod
  /-- Bitwise and. -/
  | and
  /-- Bitwise or. -/
  | or
  /-- Bitwise exclusive or. -/
  | xor
  /-- Shift left: `x <<< y = x * 2 ^ y`. -/
  | shiftLeft
  /-- Shift right: `x >>> y = x / 2 ^ y`. -/
  | shiftRight
  deriving DecidableEq, Repr

/-- The value of a binary operation on natural numbers. Subtraction is truncated, and division
and remainder by zero follow Lean's conventions `x / 0 = 0` and `x % 0 = x`. Whether the value
fits a word is checked by the instruction that writes it. -/
@[simp]
def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .mod, x, y => x % y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shiftLeft, x, y => x <<< y
  | .shiftRight, x, y => x >>> y

/-- The operations of the standard basis: the binary operations, and reading the word size. -/
inductive StandardOp where
  /-- A binary operation. -/
  | bin (f : BinOp)
  /-- The word size, an operation without arguments. -/
  | width
  deriving DecidableEq, Repr

/-- The number of arguments of a standard operation. -/
@[simp]
def StandardOp.arity : StandardOp → ℕ
  | .bin _ => 2
  | .width => 0

/-- The value of a standard operation at word size `w`. -/
def StandardOp.eval (w : ℕ) : (f : StandardOp) → (Fin f.arity → ℕ) → ℕ
  | .bin f, x => f.eval (x (0 : Fin 2)) (x (1 : Fin 2))
  | .width, _ => w

/-- The standard word-RAM basis: addition, subtraction, multiplication, bitwise operations and
shifts as in [Hagerup][Hagerup1998], together with division and remainder, and the word size, which
word-RAM algorithms may read [Fredman and Willard][FredmanWillard1993]. Only the word size reads
the word size. -/
abbrev Basis.standard : Basis where
  Op := StandardOp
  Arity := StandardOp.arity
  ReadsWidth f := f = .width
  interp := StandardOp.eval
  interp_eq_of_not_readsWidth f hf w w' args := by
    cases f with
    | bin => rfl
    | width => exact absurd rfl hf

theorem Basis.standard_op : Basis.standard.Op = StandardOp := rfl

@[simp]
theorem Basis.standard_interp_bin (w : ℕ) (f : BinOp) (x : Fin 2 → ℕ) :
    Basis.standard.interp w (.bin f) x = f.eval (x 0) (x 1) := rfl

@[simp]
theorem Basis.standard_interp_width (w : ℕ) (x : Fin 0 → ℕ) :
    Basis.standard.interp w .width x = w := rfl

@[simp]
theorem Basis.standard_readsWidth (f : StandardOp) :
    Basis.standard.ReadsWidth f ↔ f = .width := Iff.rfl

/-! ## Maps of bases -/

/-- A map of bases: a map of signatures (`Cslib.Circuits.Signature.Hom`) such that at each word
size the image of every operation has the operation's value, and that sends an operation not
marked as reading the word size to one not so marked. Programs over `B` then run instruction for
instruction over `B'`. -/
structure Basis.Hom (B B' : Basis) extends B.toSignature.Hom B'.toSignature where
  /-- At each word size, the image of each operation has the operation's value. -/
  preserves (w : ℕ) : toHom.Preserves (B.interp w) (B'.interp w)
  /-- An operation whose image reads the word size reads it itself. -/
  readsWidth_of_map (f : B.Op) : B'.ReadsWidth (toHom f) → B.ReadsWidth f

namespace Basis.Hom

variable {B B' B'' : Basis}

/-- The image of an operation under a map of bases. -/
abbrev map (φ : B.Hom B') (f : B.Op) : B'.Op := φ.toHom f

theorem arity_map (φ : B.Hom B') (f : B.Op) : B'.Arity (φ.map f) = B.Arity f :=
  φ.toHom.arity_eq f

/-- The image of an operation, applied to arguments reindexed along `arity_map`, has the value of
the operation. -/
theorem interp_map (φ : B.Hom B') (w : ℕ) (f : B.Op) (x : Fin (B.Arity f) → ℕ) :
    B'.interp w (φ.map f) (fun a => x (Fin.cast (φ.arity_map f) a)) = B.interp w f x :=
  (φ.preserves w).interpret_eq f x

/-- The identity map of a basis. -/
protected def id (B : Basis) : B.Hom B where
  toHom := Signature.Hom.id _
  preserves _ := ⟨fun _ _ => rfl⟩
  readsWidth_of_map _ h := h

/-- The composition of maps of bases. -/
def comp (ψ : B'.Hom B'') (φ : B.Hom B') : B.Hom B'' where
  toHom := ψ.toHom.comp φ.toHom
  preserves w := (ψ.preserves w).comp (φ.preserves w)
  readsWidth_of_map f h := φ.readsWidth_of_map f (ψ.readsWidth_of_map _ h)

@[simp]
theorem id_map (f : B.Op) : (Hom.id B).map f = f := rfl

@[simp]
theorem comp_map (ψ : B'.Hom B'') (φ : B.Hom B') (f : B.Op) :
    (ψ.comp φ).map f = ψ.map (φ.map f) := rfl

end Basis.Hom

/-! ## Sub-bases -/

/-- The sub-basis of `B` consisting of the operations satisfying `P`. -/
def Basis.restrict (B : Basis) (P : B.Op → Prop) : Basis where
  Op := Subtype P
  Arity f := B.Arity f.1
  ReadsWidth f := B.ReadsWidth f.1
  interp w f := B.interp w f.1
  interp_eq_of_not_readsWidth f hf := B.interp_eq_of_not_readsWidth f.1 hf

/-- The inclusion of a sub-basis. -/
def Basis.restrictHom (B : Basis) (P : B.Op → Prop) : (B.restrict P).Hom B where
  toHom := ⟨Subtype.val, fun _ => rfl⟩
  preserves _ := ⟨fun _ _ => rfl⟩
  readsWidth_of_map _ h := h

/-- Addition and truncated subtraction. -/
def Basis.additive : Basis :=
  Basis.standard.restrict (· ∈ [StandardOp.bin .add, .bin .sub])

/-- Addition, truncated subtraction, multiplication, division and remainder: the operation symbols
of the bounded-word RAM of [MIT–ULB CompGeom Group][Tromino2025], without bitwise operations, shifts
or the word size. Words here are unsigned and subtraction is truncated, whereas the source subtracts
signed words; on the other operations and nonnegative arguments the two agree. -/
def Basis.arithmetic : Basis :=
  Basis.standard.restrict (· ∈ [StandardOp.bin .add, .bin .sub, .bin .mul, .bin .div, .bin .mod])

/-- The additive operations are arithmetic. -/
def Basis.additiveHomArithmetic : Basis.additive.Hom Basis.arithmetic where
  toHom := ⟨fun f => ⟨f.1, by rcases f with ⟨f, hf⟩; simp only [List.mem_cons] at hf ⊢; tauto⟩,
    fun _ => rfl⟩
  preserves _ := ⟨fun _ _ => rfl⟩
  readsWidth_of_map _ h := h

/-- The arithmetic operations are standard. -/
def Basis.arithmeticHomStandard : Basis.arithmetic.Hom Basis.standard :=
  Basis.standard.restrictHom _

/-- The additive operations are standard. -/
def Basis.additiveHomStandard : Basis.additive.Hom Basis.standard :=
  Basis.standard.restrictHom _

/-- The two inclusions of the additive operations in the standard ones agree. -/
theorem Basis.arithmeticHomStandard_comp_additiveHomArithmetic (f : Basis.additive.Op) :
    (arithmeticHomStandard.comp additiveHomArithmetic).map f = additiveHomStandard.map f := rfl

end Cslib.WordRAM

end
