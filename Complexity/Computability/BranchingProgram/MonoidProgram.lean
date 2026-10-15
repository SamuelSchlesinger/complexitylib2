/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Monoid programs

For a monoid `M`, an *`M`-program* over `n` Boolean variables is a word of instructions, each of
which reads a variable and selects one of two elements of `M` (`MonoidProgram`). On an input it
computes the product of the selected elements, the first instruction leftmost
(`MonoidProgram.eval`); evaluation is a monoid homomorphism from programs under concatenation
(`MonoidProgram.eval_mul`). Branching programs of width `w` are the programs over
`Function.End (Fin w)`, and permutation branching programs those over `Equiv.Perm (Fin w)`; since
`(σ * τ) a = σ (τ a)`, the last instruction acts first. A program *`σ`-computes* a Boolean function
`f` when its value is `σ` where `f` is true and `1` elsewhere (`MonoidProgram.Computes`)
[Barrington1989].

Programs over groups can be inverted (`MonoidProgram.eval_inv`), and every program can be pushed
along a monoid homomorphism, for instance a conjugation (`MonoidProgram.eval_map`). So computed
functions can be negated (`MonoidProgram.Computes.not`) and combined by commutators
(`MonoidProgram.Computes.and`), the two steps of Barrington's theorem.

## Main definitions

* `Cslib.BranchingPrograms.Instruction`, `Cslib.BranchingPrograms.MonoidProgram`.
* `Cslib.BranchingPrograms.MonoidProgram.eval`, `Cslib.BranchingPrograms.MonoidProgram.Computes`.

## Main results

* `Cslib.BranchingPrograms.MonoidProgram.Computes.not`,
  `Cslib.BranchingPrograms.MonoidProgram.Computes.and`: negation and conjunction of computed
  functions.

## References

* [D. A. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

/-- An instruction: read variable `var` and select `ifFalse` or `ifTrue`. -/
structure Instruction (n : ℕ) (M : Type*) where
  /-- The variable read. -/
  var : Fin n
  /-- The element selected when the variable is false. -/
  ifFalse : M
  /-- The element selected when the variable is true. -/
  ifTrue : M

namespace Instruction

variable {n : ℕ} {M N : Type*}

/-- The element an instruction selects on an input. -/
def eval (ι : Instruction n M) (x : BitString n) : M :=
  cond (x ι.var) ι.ifTrue ι.ifFalse

/-- The instruction selecting `φ m` instead of each `m`. -/
def map (φ : M → N) (ι : Instruction n M) : Instruction n N :=
  ⟨ι.var, φ ι.ifFalse, φ ι.ifTrue⟩

@[simp] theorem eval_map (φ : M → N) (ι : Instruction n M) (x : BitString n) :
    (ι.map φ).eval x = φ (ι.eval x) := by
  cases h : x ι.var <;> simp [eval, map, h]

end Instruction

/-- An `M`-program over `n` Boolean variables: a word of instructions. -/
abbrev MonoidProgram (n : ℕ) (M : Type*) : Type _ :=
  FreeMonoid (Instruction n M)

namespace MonoidProgram

variable {n : ℕ} {M N G : Type*} [Monoid M] [Monoid N] [Group G]

/-- The product of the elements a program selects on an input, the first instruction leftmost. -/
def eval (P : MonoidProgram n M) (x : BitString n) : M :=
  FreeMonoid.lift (·.eval x) P

theorem eval_eq_prod (P : MonoidProgram n M) (x : BitString n) :
    P.eval x = (P.toList.map (·.eval x)).prod :=
  FreeMonoid.lift_apply _ P

@[simp] theorem eval_one (x : BitString n) : (1 : MonoidProgram n M).eval x = 1 :=
  map_one _

@[simp] theorem eval_of (ι : Instruction n M) (x : BitString n) :
    eval (FreeMonoid.of ι) x = ι.eval x :=
  FreeMonoid.lift_eval_of _ ι

@[simp] theorem eval_mul (P Q : MonoidProgram n M) (x : BitString n) :
    (P * Q).eval x = P.eval x * Q.eval x :=
  map_mul _ P Q

/-- A program `σ`-computes `f` when its value is `σ` on the inputs where `f` is true and `1`
elsewhere. -/
def Computes (P : MonoidProgram n M) (σ : M) (f : BooleanFunction n) : Prop :=
  ∀ x, P.eval x = if f x then σ else 1

/-- The program selecting `φ m` instead of each `m`. -/
def map (φ : M →* N) (P : MonoidProgram n M) : MonoidProgram n N :=
  FreeMonoid.map (Instruction.map φ) P

@[simp] theorem length_map (φ : M →* N) (P : MonoidProgram n M) :
    (P.map φ).length = P.length :=
  List.length_map _

@[simp] theorem eval_map (φ : M →* N) (P : MonoidProgram n M) (x : BitString n) :
    (P.map φ).eval x = φ (P.eval x) := by
  simp only [eval_eq_prod, map, FreeMonoid.toList_map, List.map_map, Function.comp_def,
    Instruction.eval_map]
  rw [map_list_prod, List.map_map]
  rfl

theorem Computes.map {P : MonoidProgram n M} {σ : M} {f : BooleanFunction n} (h : P.Computes σ f)
    (φ : M →* N) : (P.map φ).Computes (φ σ) f := fun x => by
  rw [eval_map, h x]
  split_ifs <;> simp

/-- The program with the instructions in reverse order and their elements inverted. -/
def inv (P : MonoidProgram n G) : MonoidProgram n G :=
  FreeMonoid.reverse (FreeMonoid.map (Instruction.map (·⁻¹)) P)

theorem toList_inv (P : MonoidProgram n G) :
    P.inv.toList = (P.toList.map (Instruction.map (·⁻¹))).reverse :=
  rfl

@[simp] theorem length_inv (P : MonoidProgram n G) : P.inv.length = P.length := by
  simp [FreeMonoid.length, toList_inv]

@[simp] theorem eval_inv (P : MonoidProgram n G) (x : BitString n) :
    P.inv.eval x = (P.eval x)⁻¹ := by
  simp [eval_eq_prod, toList_inv, List.prod_inv_reverse, Function.comp_def]

variable [NeZero n]

/-- Multiply the value of a program by `g` on the left, without making it longer unless it is
empty. -/
def mulLeft (g : M) (P : MonoidProgram n M) : MonoidProgram n M :=
  match P.toList with
  | [] => FreeMonoid.of ⟨0, g, g⟩
  | ι :: l => FreeMonoid.ofList (ι.map (g * ·) :: l)

@[simp] theorem eval_mulLeft (g : M) (P : MonoidProgram n M) (x : BitString n) :
    (mulLeft g P).eval x = g * P.eval x := by
  unfold mulLeft
  split <;> rename_i h
  · simp [eval_eq_prod, h, Instruction.eval]
  · simp [eval_eq_prod, h, mul_assoc]

theorem length_mulLeft (g : M) (P : MonoidProgram n M) :
    (mulLeft g P).length = max 1 P.length := by
  unfold mulLeft FreeMonoid.length
  split <;> rename_i h <;> simp [h]

/-- If `P` `σ⁻¹`-computes `f`, multiplying by `σ` makes it `σ`-compute the negation of `f`. -/
theorem Computes.not {σ : G} {f : BooleanFunction n} {P : MonoidProgram n G}
    (h : P.Computes σ⁻¹ f) : (mulLeft σ P).Computes σ fun x => !f x := fun x => by
  rw [eval_mulLeft, h x]
  cases hf : f x <;> simp [hf]

omit [NeZero n] in
/-- The commutator of programs `α`- and `β`-computing `f` and `g` computes `f ∧ g` with the
commutator `α β α⁻¹ β⁻¹`. -/
theorem Computes.and {α β : G} {f g : BooleanFunction n} {P Q : MonoidProgram n G}
    (hP : P.Computes α f) (hQ : Q.Computes β g) :
    (P * Q * P.inv * Q.inv).Computes (α * β * α⁻¹ * β⁻¹) fun x => f x && g x := fun x => by
  rw [eval_mul, eval_mul, eval_mul, eval_inv, eval_inv, hP x, hQ x]
  cases hf : f x <;> cases hg : g x <;> simp [hf, hg]

end MonoidProgram

end Cslib.BranchingPrograms
