/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.KarchmerWigderson
public import Complexity.Computability.Circuit.Monotone.Formula

/-!
# The monotone Karchmer–Wigderson theorem

In the *monotone Karchmer–Wigderson game* of a Boolean function `f`, Alice holds an input `x` with
`f x = 1`, Bob holds an input `y` with `f y = 0`, and they must find a bit that is one in `x` and
zero in `y` (`ExceedsAt`). **Karchmer and Wigderson** showed that the least depth of a monotone
formula for `f`, with constants free, is the communication complexity of this game
(`eformulaDepth_eq_ecomplexity`) [KarchmerWigderson1990], [Jukna, Section 3.3][Jukna2012],
[Kushilevitz and Nisan, Chapter 10][KushilevitzNisan1997]. Both are finite exactly when `f` is
monotone (`eformulaDepth_ne_top_iff`): when `x ≤ y`, no bit is one in `x` and zero in `y`.

The protocols are those of the Karchmer–Wigderson game (`Boolean.KWProtocol`), and the two
translations follow the proof of the non-monotone theorem (`Boolean.formulaDepth_eq_ecomplexity`).
A monotone formula gives a protocol (`kwProtocol`) on the pairs where it is true on Alice's input
and false on Bob's: at an AND gate Bob says which argument is false on his input, at an OR gate
Alice says which argument is true on hers, and an input leaf names its bit, which is then one in
`x` and zero in `y`. Conversely a protocol gives a monotone formula (`kwFormula`), with an OR at
each of Alice's nodes, an AND at each of Bob's, and at each leaf the input it names, which is true
on the inputs of Alice and false on those of Bob that reach it.

## Main definitions

* `Cslib.Circuits.Monotone.ExceedsAt`: the monotone Karchmer–Wigderson relation.
* `Cslib.Circuits.Monotone.kwProtocol`: the protocol of a monotone formula.
* `Cslib.Circuits.Monotone.kwFormula`: the monotone formula of a protocol.

## Main results

* `Cslib.Circuits.Monotone.exists_kwProtocol_of_computes`,
  `Cslib.Circuits.Monotone.exists_formula_of_solves`: a monotone formula gives a protocol for the
  monotone game of no greater depth, and conversely.
* `Cslib.Circuits.Monotone.eformulaDepth_eq_ecomplexity`: the monotone Karchmer–Wigderson theorem.

## References

* [M. Karchmer and A. Wigderson, *Monotone circuits for connectivity require super-logarithmic
  depth*][KarchmerWigderson1990]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

open Cslib.Communication
open Boolean (KWProtocol)

variable {n : ℕ}

/-- The monotone Karchmer–Wigderson relation: bit `i` is one in Alice's input `x` and zero in Bob's
input `y`. -/
def ExceedsAt (x y : BitString n) (i : Fin n) : Prop :=
  x i = true ∧ y i = false

/-- Unfolds the monotone Karchmer–Wigderson relation. -/
@[simp] theorem exceedsAt_iff {x y : BitString n} {i : Fin n} :
    ExceedsAt x y i ↔ x i = true ∧ y i = false :=
  Iff.rfl

/-- A solution of the monotone Karchmer–Wigderson game is a solution of the Karchmer–Wigderson
game. -/
theorem ExceedsAt.differsAt {x y : BitString n} {i : Fin n} (h : ExceedsAt x y i) :
    Boolean.DiffersAt x y i := by
  simp [h.1, h.2]

/-! ### The protocol of a formula -/

section kwProtocol

variable [NeZero n]

/-- The protocol of a monotone formula for the monotone Karchmer–Wigderson game. At an AND gate,
Bob sends the value of the first argument on his input, and the protocol continues with the first
argument if it is false there and with the second otherwise; at an OR gate, Alice sends the value
of the first argument on her input, and the protocol continues with the first argument if it is
true there and with the second otherwise; an input leaf names its bit. Constant subformulas, which
the protocol never reaches when the formula is true on Alice's input and false on Bob's, output
the bit `0`. -/
def kwProtocol : Formula signature n → KWProtocol n
  | .input i => .output i
  | .gate op args =>
    match op, args with
    | .const _, _ => .output 0
    | .and, args =>
      .bob (fun y => (args 0).eval interpretation y) (kwProtocol (args 0)) (kwProtocol (args 1))
    | .or, args =>
      .alice (fun x => (args 0).eval interpretation x) (kwProtocol (args 1)) (kwProtocol (args 0))

/-- The protocol of a monotone formula finds a bit that is one in Alice's input and zero in Bob's,
when the formula is true on Alice's input and false on Bob's. -/
theorem exceedsAt_run_kwProtocol (F : Formula signature n) {x y : BitString n}
    (hx : F.eval interpretation x = true) (hy : F.eval interpretation y = false) :
    ExceedsAt x y ((kwProtocol F).run x y) := by
  induction F with
  | input i => exact ⟨hx, hy⟩
  | gate op args ih =>
    cases op with
    | const b =>
      simp only [Formula.eval_gate, interpretation_const] at hx hy
      exact absurd (hx.symm.trans hy) (by decide)
    | and =>
      simp only [Formula.eval_gate, interpretation_and, Bool.and_eq_true,
        Bool.and_eq_false_iff] at hx hy
      cases h : (args 0).eval interpretation y
      · simpa [kwProtocol, h] using ih 0 hx.1 h
      · simpa [kwProtocol, h] using ih 1 hx.2 (hy.resolve_left (by simp [h]))
    | or =>
      simp only [Formula.eval_gate, interpretation_or, Bool.or_eq_true,
        Bool.or_eq_false_iff] at hx hy
      cases h : (args 0).eval interpretation x
      · simpa [kwProtocol, h] using ih 1 (hx.resolve_left (by simp [h])) hy.2
      · simpa [kwProtocol, h] using ih 0 h hy.1

/-- The protocol of a monotone formula sends at most as many bits as the formula has AND and OR
gates on a path. -/
theorem depth_kwProtocol_le (F : Formula signature n) :
    (kwProtocol F).depth ≤ F.depthWith binaryCost := by
  induction F with
  | input i => simp [kwProtocol]
  | gate op args ih =>
    have hle (j : Fin (signature.Arity op)) :
        (args j).depthWith binaryCost ≤ Finset.univ.sup fun j => (args j).depthWith binaryCost :=
      Finset.le_sup (f := fun j => (args j).depthWith binaryCost) (Finset.mem_univ j)
    cases op with
    | const b => simp [kwProtocol]
    | and =>
      simp only [kwProtocol, Protocol.depth_bob, Formula.depthWith_gate, binaryCost_and]
      exact Nat.add_le_add_right (max_le ((ih 0).trans (hle 0)) ((ih 1).trans (hle 1))) 1
    | or =>
      simp only [kwProtocol, Protocol.depth_alice, Formula.depthWith_gate, binaryCost_or]
      exact Nat.add_le_add_right (max_le ((ih 1).trans (hle 1)) ((ih 0).trans (hle 0))) 1

end kwProtocol

/-! ### The formula of a protocol -/

open Classical in
/-- The monotone formula of a protocol for the monotone Karchmer–Wigderson game on `A × B`: an OR
at each of Alice's nodes, an AND at each of Bob's, and at each leaf the input it names, or a
constant if one side is empty. -/
noncomputable def kwFormula : KWProtocol n → Set (BitString n) → Set (BitString n) →
    Formula signature n
  | .output i, A, B =>
    if A = ∅ then .gate (.const false) Fin.elim0
    else if B = ∅ then .gate (.const true) Fin.elim0
    else .input i
  | .alice send p₀ p₁, A, B =>
    .gate .or ![kwFormula p₀ {x ∈ A | send x = false} B, kwFormula p₁ {x ∈ A | send x = true} B]
  | .bob send p₀ p₁, A, B =>
    .gate .and ![kwFormula p₀ A {y ∈ B | send y = false}, kwFormula p₁ A {y ∈ B | send y = true}]

/-- The formula of a protocol solving the monotone Karchmer–Wigderson game on `A × B` is true on
`A` and false on `B`. -/
private theorem eval_kwFormula (p : KWProtocol n) {A B : Set (BitString n)}
    (hp : p.Solves ExceedsAt A B) :
    (∀ x ∈ A, (kwFormula p A B).eval interpretation x = true) ∧
      ∀ y ∈ B, (kwFormula p A B).eval interpretation y = false := by
  induction p generalizing A B with
  | output i =>
    by_cases hA : A = ∅
    · simp [kwFormula, hA]
    by_cases hB : B = ∅
    · simp [kwFormula, hA, hB]
    obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hA
    obtain ⟨y₀, hy₀⟩ := Set.nonempty_iff_ne_empty.2 hB
    simp only [kwFormula, hA, hB, ↓reduceIte, Formula.eval_input]
    exact ⟨fun x hx => (hp x hx y₀ hy₀).1, fun y hy => (hp x₀ hx₀ y hy).2⟩
  | alice send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀ (A := {x ∈ A | send x = false}) (B := B) fun x hx y hy => by
      simpa [hx.2] using hp x hx.1 y hy
    have h₁ := ih₁ (A := {x ∈ A | send x = true}) (B := B) fun x hx y hy => by
      simpa [hx.2] using hp x hx.1 y hy
    refine ⟨fun x hx => ?_, fun y hy => by simp [kwFormula, h₀.2 y hy, h₁.2 y hy]⟩
    cases h : send x
    · simp [kwFormula, h₀.1 x ⟨hx, h⟩]
    · simp [kwFormula, h₁.1 x ⟨hx, h⟩]
  | bob send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀ (A := A) (B := {y ∈ B | send y = false}) fun x hx y hy => by
      simpa [hy.2] using hp x hx y hy.1
    have h₁ := ih₁ (A := A) (B := {y ∈ B | send y = true}) fun x hx y hy => by
      simpa [hy.2] using hp x hx y hy.1
    refine ⟨fun x hx => by simp [kwFormula, h₀.1 x hx, h₁.1 x hx], fun y hy => ?_⟩
    cases h : send y
    · simp [kwFormula, h₀.2 y ⟨hy, h⟩]
    · simp [kwFormula, h₁.2 y ⟨hy, h⟩]

/-- The formula of a protocol solving the monotone Karchmer–Wigderson game on `A × B` is true on
`A`. -/
theorem eval_kwFormula_of_mem_left {p : KWProtocol n} {A B : Set (BitString n)}
    (hp : p.Solves ExceedsAt A B) {x : BitString n} (hx : x ∈ A) :
    (kwFormula p A B).eval interpretation x = true :=
  (eval_kwFormula p hp).1 x hx

/-- The formula of a protocol solving the monotone Karchmer–Wigderson game on `A × B` is false on
`B`. -/
theorem eval_kwFormula_of_mem_right {p : KWProtocol n} {A B : Set (BitString n)}
    (hp : p.Solves ExceedsAt A B) {y : BitString n} (hy : y ∈ B) :
    (kwFormula p A B).eval interpretation y = false :=
  (eval_kwFormula p hp).2 y hy

/-- The formula of a protocol has as many AND and OR gates on a path as the protocol sends
bits. -/
theorem depthWith_kwFormula_le (p : KWProtocol n) (A B : Set (BitString n)) :
    (kwFormula p A B).depthWith binaryCost ≤ p.depth := by
  induction p generalizing A B with
  | output i =>
    simp only [kwFormula]
    split_ifs <;> simp
  | alice send p₀ p₁ ih₀ ih₁ =>
    simp only [kwFormula, Formula.depthWith_gate, binaryCost_or, Protocol.depth_alice]
    simpa [Fin.univ_succ] using Nat.add_le_add_right (max_le_max (ih₀ _ _) (ih₁ _ _)) 1
  | bob send p₀ p₁ ih₀ ih₁ =>
    simp only [kwFormula, Formula.depthWith_gate, binaryCost_and, Protocol.depth_bob]
    simpa [Fin.univ_succ] using Nat.add_le_add_right (max_le_max (ih₀ _ _) (ih₁ _ _)) 1

/-! ### The monotone Karchmer–Wigderson theorem -/

variable {f : BooleanFunction n}

/-- A monotone formula computing `f` gives a protocol for its monotone Karchmer–Wigderson game,
with at most as many bits as the formula has AND and OR gates on a path. -/
theorem exists_kwProtocol_of_computes [NeZero n] {F : Formula signature n}
    (hF : F.Computes interpretation f) :
    ∃ p : KWProtocol n, p.Solves ExceedsAt {x | f x = true} {y | f y = false} ∧
      p.depth ≤ F.depthWith binaryCost :=
  ⟨kwProtocol F, fun x hx y hy => exceedsAt_run_kwProtocol F ((hF x).trans hx) ((hF y).trans hy),
    depth_kwProtocol_le F⟩

/-- A protocol for the monotone Karchmer–Wigderson game of `f` gives a monotone formula computing
`f`, with at most as many AND and OR gates on a path as the protocol sends bits. -/
theorem exists_formula_of_solves {p : KWProtocol n}
    (hp : p.Solves ExceedsAt {x | f x = true} {y | f y = false}) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧ F.depthWith binaryCost ≤ p.depth := by
  refine ⟨kwFormula p {x | f x = true} {y | f y = false}, fun x => ?_, depthWith_kwFormula_le _ _ _⟩
  cases h : f x
  · exact eval_kwFormula_of_mem_right hp h
  · exact eval_kwFormula_of_mem_left hp h

/-- **The monotone Karchmer–Wigderson theorem.** The least depth of a monotone formula for a
function of at least one bit, with constants free, is the communication complexity of its monotone
Karchmer–Wigderson game; in particular both are `⊤` when no monotone formula computes it. -/
theorem eformulaDepth_eq_ecomplexity [NeZero n] (f : BooleanFunction n) :
    eformulaDepth f = Protocol.ecomplexity ExceedsAt {x | f x = true} {y | f y = false} := by
  refine le_antisymm (Protocol.le_ecomplexity_iff.2 fun p hp => ?_)
    (le_eformulaDepth_iff.2 fun F hF => ?_)
  · obtain ⟨F, hF, hd⟩ := exists_formula_of_solves hp
    exact (eformulaDepth_le hF).trans (by exact_mod_cast hd)
  · obtain ⟨p, hp, hd⟩ := exists_kwProtocol_of_computes hF
    exact (Protocol.ecomplexity_le_depth hp).trans (by exact_mod_cast hd)

end Cslib.Circuits.Monotone
