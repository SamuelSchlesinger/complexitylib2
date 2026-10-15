/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Finset.Defs

/-!
# Bounded-round Karchmer–Wigderson protocols

A *round protocol* for the Karchmer–Wigderson game sends at most `d` messages from an alphabet `M`
(`RoundProtocol ι M d`): at each step the speaker, who may depend on the messages so far, sends one
message computed from their input, and the protocol ends by naming a coordinate determined by the
transcript. It *solves* the game on a rectangle `X × Y` when, for every `x ∈ X` held by Alice and
`y ∈ Y` held by Bob, the inputs differ at the named coordinate (`RoundProtocol.Solves`), and the
game of a Boolean function `f` when this holds with `f x = false` and `f y = true`
(`RoundProtocol.SolvesKW`). This is the model of the top-down lower bounds of Korten
[Korten2026], in which a circuit of depth `d` with `w` wires gives a protocol with `d` messages from
an alphabet of size `w`.

Exchanging the speakers exchanges the inputs (`RoundProtocol.run_swapPlayers`), so it solves the
game of the negated function (`RoundProtocol.SolvesKW.swapPlayers`).

## Main definitions

* `Cslib.Communication.RoundProtocol`: protocols with at most `d` messages from `M`.
* `Cslib.Communication.RoundProtocol.Solves`, `Cslib.Communication.RoundProtocol.SolvesKW`.

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
  ∀ x ∈ X, ∀ y ∈ Y, x (P.run x y) ≠ y (P.run x y)

/-- The protocol solves the Karchmer–Wigderson game of `f`: Alice holds an input with `f x = false`,
Bob one with `f y = true`, and they differ at the named coordinate. -/
def SolvesKW {d : ℕ} (P : RoundProtocol ι M d) (f : (ι → Bool) → Bool) : Prop :=
  ∀ x y, f x = false → f y = true → x (P.run x y) ≠ y (P.run x y)

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

end RoundProtocol

end Cslib.Communication
