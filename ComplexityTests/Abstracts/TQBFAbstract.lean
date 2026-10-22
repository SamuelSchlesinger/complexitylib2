/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityTests.Abstracts.Check
import ComplexityTests.Abstracts.TQBFBridge

/-! # A formal abstract of the PSPACE-completeness of TQBF

This file introduces quantified Boolean formulas (QBF), their truth values and
free variables, their prefix-order binary encoding, deterministic polynomial
space (`PSPACE`), and polynomial-time many-one reductions, and proves that the
true closed quantified Boolean formulas (`TQBF`) form a `PSPACE`-complete
problem.

To check that the formalization establishes this result, a reader only needs to
inspect the definitions and theorem statements in this file. Every public
definition and theorem statement depends only on this file, `Mathlib`, and
upstream `Cslib`'s multi-tape Turing machine model; `#check_abstract`
mechanically verifies that no internal `Complexitylib` declarations leak into
the statements, and Lean checks the proofs through `TQBFBridge`.

## References

* [L. J. Stockmeyer, A. R. Meyer, *Word problems requiring exponential time*][StockmeyerMeyer1973]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

namespace ComplexityTests.Abstracts.TQBFAbstract

/-! ## Quantified Boolean formulas and semantics

Formulas are built from natural-number variables `v : ℕ`, the Boolean constants
`top` (true) and `bot` (false), negation, conjunction, disjunction, existential
quantification `ex v φ` (`∃ v, φ`), and universal quantification `all v φ`
(`∀ v, φ`). Formulas are not restricted to prenex normal form.
-/

/-- Quantified Boolean formulas over the variables `ℕ`. -/
inductive Formula where
  | var : ℕ → Formula
  | top : Formula
  | bot : Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | ex : ℕ → Formula → Formula
  | all : ℕ → Formula → Formula

/-- Evaluate a quantified Boolean formula under a Boolean assignment `σ : ℕ → Bool`.
Quantifiers over `v` evaluate the body with `v` updated to `false` and to `true`
(`Function.update`), combining the two truth values by disjunction (`ex`) or
conjunction (`all`). -/
def Formula.eval (σ : ℕ → Bool) : Formula → Bool
  | .var v => σ v
  | .top => true
  | .bot => false
  | .not φ => !φ.eval σ
  | .and φ ψ => φ.eval σ && ψ.eval σ
  | .or φ ψ => φ.eval σ || ψ.eval σ
  | .ex v φ => φ.eval (Function.update σ v false) || φ.eval (Function.update σ v true)
  | .all v φ => φ.eval (Function.update σ v false) && φ.eval (Function.update σ v true)

/-- The finite set of free variables of a formula: variables that occur outside
the scope of any enclosing quantifier binding them. -/
def Formula.freeVars : Formula → Finset ℕ
  | .var v => {v}
  | .top => ∅
  | .bot => ∅
  | .not φ => φ.freeVars
  | .and φ ψ => φ.freeVars ∪ ψ.freeVars
  | .or φ ψ => φ.freeVars ∪ ψ.freeVars
  | .ex v φ => φ.freeVars.erase v
  | .all v φ => φ.freeVars.erase v

/-- A formula is closed (a sentence) if it has no free variables. -/
def Formula.Closed (φ : Formula) : Prop := φ.freeVars = ∅

/-- `TQBF` is the set of closed quantified Boolean formulas that evaluate to
`true`. Because a closed formula has no free variables, its value is independent
of the initial assignment (`fun _ => false`). Formulas with free variables are
excluded from `TQBF`. -/
def TQBF : Set Formula :=
  {φ | φ.Closed ∧ φ.eval (fun _ => false) = true}

/-! ## Prefix-order binary encoding

A formula is serialized in prefix (Polish) order as a list of `(kind, var)`
tokens, where `kind ∈ {0, …, 7}` identifies the constructor (`var`, `top`,
`bot`, `not`, `and`, `or`, `ex`, `all`) and `var` carries the variable index for
`var`, `ex`, and `all` (and `0` otherwise). Each token is encoded as a framed
pair of `kind` in unary (`List.replicate kind true`) and `var` in little-endian
binary (`Nat.bits`).
-/

/-- The prefix-order token list of a formula: one `(kind, var)` token per constructor. -/
def Formula.tokens : Formula → List (ℕ × ℕ)
  | .var v => [(0, v)]
  | .top => [(1, 0)]
  | .bot => [(2, 0)]
  | .not φ => (3, 0) :: φ.tokens
  | .and φ ψ => (4, 0) :: (φ.tokens ++ ψ.tokens)
  | .or φ ψ => (5, 0) :: (φ.tokens ++ ψ.tokens)
  | .ex v φ => (6, v) :: φ.tokens
  | .all v φ => (7, v) :: φ.tokens

/-- Frame a bitstring: write each bit `b` as `[true, b]`, then terminate with `[false]`. -/
def frame (w : List Bool) : List Bool :=
  w.flatMap (fun b => [true, b]) ++ [false]

/-- Encode a pair by framing the encoding of its first component and appending the encoding of
its second component. -/
def encodePair {α β : Type} (encA : α → List Bool) (encB : β → List Bool) (p : α × β) :
    List Bool :=
  frame (encA p.1) ++ encB p.2

/-- Encode a list by concatenating the framed encodings of its elements. -/
def encodeList {α : Type} (enc : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (frame ∘ enc)

/-- Encode a token `(kind, var)` as the pair of `kind` in unary and `var` in binary. -/
def encodeToken : ℕ × ℕ → List Bool :=
  encodePair (fun k => List.replicate k true) Nat.bits

/-- Encode a formula as the list encoding of its prefix-order tokens. -/
def encodeQBF (φ : Formula) : List Bool :=
  encodeList encodeToken φ.tokens

theorem encodeQBF_injective : Function.Injective encodeQBF :=
  TQBFBridge.encodeQBF_injective
    { Formula := Formula
      var := Formula.var, top := Formula.top, bot := Formula.bot
      not := Formula.not, and := Formula.and, or := Formula.or
      ex := Formula.ex, all := Formula.all
      formula_induction := @Formula.rec
      eval := Formula.eval, freeVars := Formula.freeVars, tokens := Formula.tokens }
    (by constructor <;> intros <;> rfl)

/-- Injective binary encoding of quantified Boolean formulas. -/
def encQBF : Formula ↪ List Bool :=
  ⟨encodeQBF, encodeQBF_injective⟩

/-- Injective encoding of a single Boolean as a one-bit word `[b]`. -/
def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], by intro a b h; injection h⟩

/-! ## Polynomial space (`PSPACE`) and PSPACE-completeness

In upstream `Cslib`, `Turing.MultiTapeTM.ComputableInTimeAndSpace f encIn encOut t s`
means that one deterministic binary multi-tape Turing machine with finitely many
states halts on every input `encIn a` within `t a` steps and `s a` work-tape
cells, outputting `encOut (f a)`. Read-only input cells and write-only output
cells are not charged to work space.
-/

/-- A decision problem `A : Set α` (with instance encoding `enc`) belongs to
deterministic polynomial space (`PSPACE`) if some deterministic binary
multi-tape Turing machine decides membership on every input, halting within a
number of work-tape cells bounded by a polynomial in the input bit length. -/
def PSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → Bool) (t : α → ℕ) (s : ℕ → ℕ),
    Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpace f enc encBool
      t (fun a => s (enc a).length) ∧
    ∀ a, a ∈ A ↔ f a = true}

/-- A total function `f : α → β` is computable in polynomial time with respect
to `encA` and `encB` if a deterministic multi-tape Turing machine computes it
within polynomially bounded time and space in the input bit length. -/
def ComputableInPolyTime {α β : Type} (f : α → β)
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f encA encB t s

/-- Polynomial-time many-one reducibility between encoded decision problems. -/
def PolyTimeReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, ComputableInPolyTime f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- A problem `B` is PSPACE-complete if it belongs to PSPACE and every PSPACE
problem (over any instance type `α` and injective binary encoding `encA`)
reduces to `B` in polynomial time. -/
def PSPACEComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ PSPACE encB ∧
  ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
    A ∈ PSPACE encA → PolyTimeReducible encA encB A B

/-! ## Main result -/

/-- **Theorem (Stockmeyer–Meyer):** The true closed quantified Boolean formulas
(`TQBF`) are PSPACE-complete under polynomial-time many-one reductions. -/
theorem tqbf_pspaceComplete : PSPACEComplete encQBF TQBF :=
  TQBFBridge.tqbf_pspaceComplete
    { Formula := Formula
      var := Formula.var, top := Formula.top, bot := Formula.bot
      not := Formula.not, and := Formula.and, or := Formula.or
      ex := Formula.ex, all := Formula.all
      formula_induction := @Formula.rec
      eval := Formula.eval, freeVars := Formula.freeVars, tokens := Formula.tokens }
    (by constructor <;> intros <;> rfl)

/--
info: abstract audit passed for `ComplexityTests.Abstracts.TQBFAbstract`: 73 root
declarations, 126 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.TQBFAbstract

end ComplexityTests.Abstracts.TQBFAbstract
