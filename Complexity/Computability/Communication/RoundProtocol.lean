/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Communication.KarchmerWigderson
public import Mathlib.Data.Finset.Defs

/-!
# Bounded-round Karchmer–Wigderson protocols

A *round protocol* for the Karchmer–Wigderson game sends at most `d` messages from an alphabet `M`
(`RoundProtocol ι M d`): at each step the speaker, who may depend on the messages so far, sends one
message computed from their input, and the protocol ends by naming a coordinate determined by the
transcript. It *solves* the game on a rectangle `X × Y` when, for every `x ∈ X` held by Alice and
`y ∈ Y` held by Bob, the inputs differ at the named coordinate (`DiffersAt`,
`RoundProtocol.Solves`), and the
game of a Boolean function `f` when this holds with `f x = false` and `f y = true`
(`RoundProtocol.SolvesKW`). This is the model of the top-down lower bounds of Korten
[Korten2026], in which a circuit of AND/OR depth `d` with `w` wires gives a protocol with `d`
messages from an alphabet of size `w`.

Exchanging the speakers exchanges the inputs (`RoundProtocol.run_swapPlayers`), so it solves the
game of the negated function (`RoundProtocol.SolvesKW.swapPlayers`).

Following Korten, `SolvesKW f` gives Alice the input where `f` is false. The Karchmer–Wigderson
theorem for formulas (`Circuits.Boolean.formulaDepth_eq_ecomplexity`) uses the bit protocols of
`Protocol` and gives Alice the input where `f` is true. A bit protocol of depth at most `d` is a
round protocol with `d` messages of one bit (`RoundProtocol.ofProtocol`), and it solves the game
of the negated function in Korten's convention (`RoundProtocol.solvesKW_not_ofProtocol`), so of
`f` after exchanging the players (`RoundProtocol.solvesKW_swapPlayers_ofProtocol`).

## Main definitions

* `Cslib.Communication.RoundProtocol`: protocols with at most `d` messages from `M`.
* `Cslib.Communication.RoundProtocol.Solves`, `Cslib.Communication.RoundProtocol.SolvesKW`.
* `Cslib.Communication.RoundProtocol.ofProtocol`: a bit protocol as a round protocol.

## Main results

* `Cslib.Communication.RoundProtocol.run_swapPlayers`,
  `Cslib.Communication.RoundProtocol.run_comap`: exchanging the players and relabelling the inputs.
* `Cslib.Communication.RoundProtocol.run_ofProtocol`,
  `Cslib.Communication.RoundProtocol.solvesKW_not_ofProtocol`: bit protocols as round protocols.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.Communication

/-- A Karchmer–Wigderson protocol with messages from `M` and at most `d` rounds, naming a coordinate
of `ι` at the end. The speaker may depend on the preceding messages, and the answer depends only
on the transcript. -/
inductive RoundProtocol (ι M : Type*) : ℕ → Type _
  /-- Name a coordinate, possibly before exhausting the round budget. -/
  | answer {d : ℕ} (index : ι) : RoundProtocol ι M d
  /-- Alice sends one message computed from her input. -/
  | alice {d : ℕ} (send : (ι → Bool) → M) (next : M → RoundProtocol ι M d) :
      RoundProtocol ι M (d + 1)
  /-- Bob sends one message computed from his input. -/
  | bob {d : ℕ} (send : (ι → Bool) → M) (next : M → RoundProtocol ι M d) :
      RoundProtocol ι M (d + 1)

namespace RoundProtocol

variable {ι M : Type*}

/-- The coordinate named by a protocol on Alice's input `x` and Bob's input `y`. -/
def run {d : ℕ} : RoundProtocol ι M d → (ι → Bool) → (ι → Bool) → ι
  | .answer i, _, _ => i
  | .alice send next, x, y => (next (send x)).run x y
  | .bob send next, x, y => (next (send y)).run x y

/-- The protocol solves the Karchmer–Wigderson game on the rectangle `X × Y`: every `x ∈ X` and
`y ∈ Y` differ at the named coordinate. -/
def Solves {d : ℕ} (P : RoundProtocol ι M d) (X Y : Finset (ι → Bool)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, DiffersAt x y (P.run x y)

/-- The protocol solves the Karchmer–Wigderson game of `f`: Alice holds an input with `f x = false`,
Bob one with `f y = true`, and they differ at the named coordinate. -/
def SolvesKW {d : ℕ} (P : RoundProtocol ι M d) (f : (ι → Bool) → Bool) : Prop :=
  ∀ x y, f x = false → f y = true → DiffersAt x y (P.run x y)

/-- One message, sent by Bob if `b` and by Alice otherwise. -/
def speak {d : ℕ} (b : Bool) (msg : (ι → Bool) → M) (next : M → RoundProtocol ι M d) :
    RoundProtocol ι M (d + 1) :=
  if b then .bob msg next else .alice msg next

@[simp] theorem run_speak {d : ℕ} (b : Bool) (msg : (ι → Bool) → M)
    (next : M → RoundProtocol ι M d) (x y : ι → Bool) :
    (speak b msg next).run x y = (next (msg (if b then y else x))).run x y := by
  cases b <;> rfl

/-- Exchange the speakers throughout the protocol. -/
def swapPlayers : {d : ℕ} → RoundProtocol ι M d → RoundProtocol ι M d
  | _, .answer i => .answer i
  | _, .alice send next => .bob send fun a => (next a).swapPlayers
  | _, .bob send next => .alice send fun a => (next a).swapPlayers

/-- Exchanging the speakers exchanges the inputs. -/
theorem run_swapPlayers : ∀ {d : ℕ} (P : RoundProtocol ι M d) (x y : ι → Bool),
    P.swapPlayers.run x y = P.run y x
  | _, .answer _, _, _ => rfl
  | _, .alice send next, x, y => run_swapPlayers (next (send y)) x y
  | _, .bob send next, x, y => run_swapPlayers (next (send x)) x y

/-- Exchanging the speakers solves the game of the negated function. -/
theorem SolvesKW.swapPlayers {d : ℕ} {P : RoundProtocol ι M d} {f : (ι → Bool) → Bool}
    (h : P.SolvesKW f) : P.swapPlayers.SolvesKW fun x => !f x := by
  intro x y hx hy
  rw [run_swapPlayers]
  exact (h y x (by simpa using hy) (by simpa using hx)).symm

/-- Apply `φ` to both players' inputs before running the protocol. -/
def comap (φ : (ι → Bool) → ι → Bool) : {d : ℕ} → RoundProtocol ι M d → RoundProtocol ι M d
  | _, .answer i => .answer i
  | _, .alice send next => .alice (send ∘ φ) fun a => (next a).comap φ
  | _, .bob send next => .bob (send ∘ φ) fun a => (next a).comap φ

theorem run_comap (φ : (ι → Bool) → ι → Bool) : ∀ {d : ℕ} (P : RoundProtocol ι M d)
    (x y : ι → Bool), (P.comap φ).run x y = P.run (φ x) (φ y)
  | _, .answer _, _, _ => rfl
  | _, .alice send next, x, y => run_comap φ (next (send (φ x))) x y
  | _, .bob send next, x, y => run_comap φ (next (send (φ y))) x y

/-- Negating both players' inputs solves the game of the function of the negated input. -/
theorem SolvesKW.comap_not {d : ℕ} {P : RoundProtocol ι M d} {f : (ι → Bool) → Bool}
    (h : P.SolvesKW f) : (P.comap fun x i => !x i).SolvesKW fun x => f fun i => !x i := by
  intro x y hx hy
  rw [run_comap]
  intro hxy
  exact h _ _ hx hy (by simp [hxy])

/-- A bit protocol of depth at most `d` naming a coordinate, as a round protocol with `d`
messages of one bit. -/
def ofProtocol : (p : KWProtocol ι) → (d : ℕ) → p.depth ≤ d →
    RoundProtocol ι Bool d
  | .output i, _, _ => .answer i
  | .alice _ _ _, 0, h => absurd h (by simp)
  | .alice send p₀ p₁, d + 1, h => .alice send fun b =>
    cond b (ofProtocol p₁ d (by simp at h; omega)) (ofProtocol p₀ d (by simp at h; omega))
  | .bob _ _ _, 0, h => absurd h (by simp)
  | .bob send p₀ p₁, d + 1, h => .bob send fun b =>
    cond b (ofProtocol p₁ d (by simp at h; omega)) (ofProtocol p₀ d (by simp at h; omega))

@[simp] theorem run_ofProtocol : ∀ (p : KWProtocol ι) (d : ℕ)
    (h : p.depth ≤ d) (x y : ι → Bool), (ofProtocol p d h).run x y = p.run x y
  | .output _, _, _, _, _ => rfl
  | .alice _ _ _, 0, h, _, _ => absurd h (by simp)
  | .alice send p₀ p₁, d + 1, h, x, y => by
    change (cond (send x) (ofProtocol p₁ d _) (ofProtocol p₀ d _)).run x y =
      cond (send x) (p₁.run x y) (p₀.run x y)
    cases send x
    · exact run_ofProtocol p₀ d _ x y
    · exact run_ofProtocol p₁ d _ x y
  | .bob _ _ _, 0, h, _, _ => absurd h (by simp)
  | .bob send p₀ p₁, d + 1, h, x, y => by
    change (cond (send y) (ofProtocol p₁ d _) (ofProtocol p₀ d _)).run x y =
      cond (send y) (p₁.run x y) (p₀.run x y)
    cases send y
    · exact run_ofProtocol p₀ d _ x y
    · exact run_ofProtocol p₁ d _ x y

/-- A bit protocol for the Karchmer–Wigderson game of `f` with Alice holding the input where `f` is
true solves, as a round protocol, the game of the negation of `f` in Korten's convention. -/
theorem solvesKW_not_ofProtocol {f : (ι → Bool) → Bool} {p : KWProtocol ι}
    (hp : p.Solves DiffersAt {x | f x = true} {y | f y = false}) (d : ℕ)
    (h : p.depth ≤ d) : (ofProtocol p d h).SolvesKW fun x => !f x := by
  intro x y hx hy
  rw [run_ofProtocol]
  exact hp x (by simpa using hx) y (by simpa using hy)

/-- A bit protocol for the Karchmer–Wigderson game of `f` with Alice holding the input where `f` is
true gives, with the players exchanged, a round protocol solving `SolvesKW f` with one bit per
message. -/
theorem solvesKW_swapPlayers_ofProtocol {f : (ι → Bool) → Bool} {p : KWProtocol ι}
    (hp : p.Solves DiffersAt {x | f x = true} {y | f y = false}) (d : ℕ)
    (h : p.depth ≤ d) : (ofProtocol p d h).swapPlayers.SolvesKW f := by
  simpa using (solvesKW_not_ofProtocol hp d h).swapPlayers

end RoundProtocol

end Cslib.Communication
