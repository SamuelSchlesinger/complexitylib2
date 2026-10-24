/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.MAC.CarterWegman
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for Carter–Wegman MACs from Δ-universal hashing

Checks concrete tag generation and verification for `xpolyHash` over `ZMod 7` and Boolean-matrix
linear hashing over `BitString 2`, instantiates `OneTimeForger` and a two-query adaptive
`CounterForger`, exercises the one-time, multi-query counter, and pseudorandom-pad security bounds,
and audits the axiom dependencies of the headline theorems in
`Complexity.Crypto.Protocols.MAC.CarterWegman`.
-/

namespace ComplexityTests.Crypto.CarterWegman

open Cslib Cslib.Probability Cslib.Crypto.Protocols.CarterWegman
open scoped ENNReal

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- Concrete polynomial Carter–Wegman sign and verify over `ZMod 7`:
-- `polyHash 3 [2, 4] = ((1 * 3 + 2) * 3 + 4) = 19 ≡ 5 (mod 7)`,
-- `xpolyHash 3 [2, 4] = 3 * 5 = 15 ≡ 1 (mod 7)`,
-- `sign xpolyHash 3 4 [2, 4] = 1 + 4 = 5 (mod 7)`.
example : sign (xpolyHash (F := ZMod 7)) 3 4 [2, 4] = 5 := by decide

example : verify (xpolyHash (F := ZMod 7)) 3 4 [2, 4] 5 = true := by decide

example : verify (xpolyHash (F := ZMod 7)) 3 4 [2, 4] 6 = false := by decide

-- Concrete pad reconstruction: `-xpolyHash 3 [2, 4] + 5 = -1 + 5 = 4 (mod 7)`.
example : -xpolyHash (F := ZMod 7) 3 [2, 4] + 5 = 4 := by decide

-- Concrete `checkCounterSlot`, `checkCounterEUF`, and `checkCounterSUF` checks on a two-slot
-- pad log.
example :
    checkCounterSlot (xpolyHash (F := ZMod 7)) 3 [([2, 4], 4), ([1], 2)] (0, [2, 4], 5) =
      false := by decide

example :
    checkCounterSUF (xpolyHash (F := ZMod 7)) 3 [([2, 4], 4), ([1], 2)] (0, [2, 4], 5) =
      false := by decide

-- Out-of-bounds counter slot is rejected.
example :
    checkCounterSlot (xpolyHash (F := ZMod 7)) 3 [([2, 4], 4)] (1, [1], 0) = false := by decide

/-- Concrete adaptive one-time forger over `ZMod 7` messages of length at most `2`:
queries `[1, 2]` and outputs `([2, 1], t + 1)`. -/
noncomputable def sampleOneTimeForger :
    OneTimeForger {m : List (ZMod 7) // m.length ≤ 2} (ZMod 7) where
  query := PMF.pure ⟨[1, 2], by decide⟩
  forge _ t := PMF.pure (⟨[2, 1], by decide⟩, t + 1)

/-- Concrete two-query adaptive counter forger over `ZMod 7` messages of length at most `2`:
queries `m₀ = [1, 2]` (receiving `t₀`), queries `m₁ = [2, 1]` (receiving `t₁`), and outputs a
forgery attempt `(0, [0, 3], t₀ + t₁)` against counter slot `0`. -/
noncomputable def sampleCounterForger :
    CounterForger {m : List (ZMod 7) // m.length ≤ 2} (ZMod 7) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ := do
    let t₀ ← OracleComp.query (spec := fun _ : {m : List (ZMod 7) // m.length ≤ 2} => ZMod 7)
      ⟨[1, 2], by decide⟩
    let t₁ ← OracleComp.query (spec := fun _ : {m : List (ZMod 7) // m.length ≤ 2} => ZMod 7)
      ⟨[2, 1], by decide⟩
    return (0, ⟨[0, 3], by decide⟩, t₀ + t₁)

-- Concrete instantiation of one-time polynomial Carter–Wegman security over `ZMod 7` (`ℓ = 2`):
-- forgery probability is at most `3 / 7`.
example :
    oneTimeGame (PMF.uniformOfFintype (ZMod 7))
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleOneTimeForger true ≤ (2 + 1) / Fintype.card (ZMod 7) :=
  oneTimeGame_xpolyHash_le 2 sampleOneTimeForger

-- Concrete instantiation of two-query adaptive counter Carter–Wegman security over `ZMod 7`:
-- forgery probability is still at most `3 / 7`.
example :
    counterGame (PMF.uniformOfFintype (ZMod 7))
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleCounterForger true ≤ (2 + 1) / Fintype.card (ZMod 7) :=
  counterGame_xpolyHash_le 2 sampleCounterForger

example :
    counterStrongGame (PMF.uniformOfFintype (ZMod 7))
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleCounterForger true ≤ (2 + 1) / Fintype.card (ZMod 7) :=
  counterStrongGame_xpolyHash_le 2 sampleCounterForger

-- Concrete instantiation of the zero-query exact `1 / 7` bound over `ZMod 7`.
example :
    zeroQueryGame (PMF.uniformOfFintype (ZMod 7)) (xpolyHash (F := ZMod 7))
      (PMF.pure ([1, 2], 5)) true = (Fintype.card (ZMod 7) : ℝ≥0∞)⁻¹ :=
  zeroQueryGame_apply_true _ _ _

-- Concrete instantiation of the pseudorandom-pad hybrid bound over `ZMod 7`.
example (padDist : PMF (ZMod 7)) :
    (maskedOneTimeGame (PMF.uniformOfFintype (ZMod 7)) padDist
      (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
      sampleOneTimeForger true).toReal ≤
      (((2 : ℝ≥0∞) + 1) / Fintype.card (ZMod 7)).toReal +
        |((padDist.bind (padDistinguisher (PMF.uniformOfFintype (ZMod 7))
            (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
            sampleOneTimeForger)) true).toReal -
          (((PMF.uniformOfFintype (ZMod 7)).bind (padDistinguisher (PMF.uniformOfFintype (ZMod 7))
            (fun k (m : {m : List (ZMod 7) // m.length ≤ 2}) => xpolyHash k m)
            sampleOneTimeForger)) true).toReal| := by
  refine maskedOneTimeGame_toReal_le (isDeltaUniversalHash_xpolyHash 2) ?_ padDist
    sampleOneTimeForger
  exact ENNReal.div_ne_top (by simp) (by simp)

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.bind_uniform_sign' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.bind_uniform_sign

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.zeroQueryGame_apply_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.zeroQueryGame_apply_true

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.oneTimeStrongGame_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.oneTimeStrongGame_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.run_interpret_counterRealHandler' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.run_interpret_counterRealHandler

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.counterSlotGame_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.counterSlotGame_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.counterGame_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.counterGame_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.counterStrongGame_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.counterStrongGame_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeGame_toReal_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeGame_toReal_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_xpolyHash_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_xpolyHash_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.counterGame_xpolyHash_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.counterGame_xpolyHash_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_linearHash_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_linearHash_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.counterGame_linearHash_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.counterGame_linearHash_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_subsetSum_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_subsetSum_le

/--
info: 'Cslib.Crypto.Protocols.CarterWegman.counterGame_subsetSum_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Protocols.CarterWegman.counterGame_subsetSum_le

end ComplexityTests.Crypto.CarterWegman
