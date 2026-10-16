/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime

/-!
# Functional programs with polynomial-time certificates

Adapted from `CslibTests/ComputationalCryptoPrograms.lean` on the cslib `crypto` branch.
Programs use ordinary functional code; loop contracts mention values and encoded sizes.
-/

namespace ComplexityTests.PolyTimeTactic

open Turing.MultiTapeTM

example : ComputableTidilyInPolyTime
    (fun p : ℕ × List ℕ => (List.range p.1).flatMap fun i => p.2.map fun j => i + j)
    (encPair encUnary (encList encUnary)) (encList encUnary) := by
  polytime

example (f g : List Bool → List Bool)
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hg : ComputableTidilyInPolyTime g encBits encBits) :
    ComputableTidilyInPolyTime (fun word => g (f word) ++ word) encBits encBits := by
  fail_if_success (clear hg; polytime)
  polytime

example : ComputableTidilyInPolyTime
    (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
    encBits encBits := by
  polytime

example : ComputableTidilyInPolyTime (fun word : List Bool => word.tail.headD false)
    encBits encBool := by
  polytime

example (step : List Bool → Bool → List Bool) (growth : ℕ)
    (hstep : ComputableTidilyInPolyTime (fun pair : List Bool × Bool => step pair.1 pair.2)
      (encPair encBits encBool) encBits)
    (hgrowth : ∀ word bit, (step word bit).length ≤ word.length + growth) :
    ComputableTidilyInPolyTime (fun word : List Bool => word.foldl step word)
      encBits encBits := by
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime

-- No rule can replace a missing certificate or a missing state-growth argument.
example (_f : List Bool → List Bool) : True := by
  fail_if_success
    have : ComputableTidilyInPolyTime _f encBits encBits := by polytime
  fail_if_success
    have : ComputableTidilyInPolyTime
        (fun word : List Bool => word.foldl (fun current _ => current ++ current) [true])
        encBits encBits := by polytime
  fail_if_success
    have : ComputableTidilyInPolyTime (fun n : ℕ => 2 ^ n) encUnary encUnary := by polytime
  trivial

-- A supplied algorithm may take nested tuples assembled from captured data.
example (algorithm : (List Bool × ℕ) × List Bool → List Bool)
    (halgorithm : ComputableTidilyInPolyTime algorithm
      (encPair (encPair encBits encUnary) encBits) encBits) :
    ComputableTidilyInPolyTime
      (fun word : List Bool => algorithm ((word.reverse, word.length), word ++ word))
      encBits encBits := by
  polytime

-- A locally supplied routine may have several certificates with different encodings.
example (f : ℕ → Bool)
    (_hfUnary : ComputableTidilyInPolyTime f encUnary encBool)
    (hfBinary : ComputableTidilyInPolyTime f encNat encBool) :
    ComputableTidilyInPolyTime (fun p : ℕ × Bool => f p.1)
      (encPair encNat encBool) encBool := by
  polytime

-- The step's fixed additive growth is inferred from the constructor.
example : ComputableTidilyInPolyTime
    (fun n : ℕ => (fun word : List Bool => false :: word)^[n] []) encUnary encBits := by
  polytime

private def reverseCopy (word : List Bool) : List Bool := word.reverse ++ word

@[program_certificate]
private theorem reverseCopy_polytime : ComputableTidilyInPolyTime reverseCopy encBits encBits := by
  unfold reverseCopy
  polytime

attribute [irreducible] reverseCopy

-- Registered routine certificates remain usable when the implementation is not unfolded.
example : ComputableTidilyInPolyTime reverseCopy encBits encBits := by polytime

example : ComputableTidilyInPolyTime (fun p : Bool × List Bool => reverseCopy p.2)
    (encPair encBool encBits) encBits := by polytime

example : ComputableTidilyInPolyTime (fun word => reverseCopy (reverseCopy word))
    encBits encBits := by polytime

-- A captured parameter and a value invariant prove efficiency and the computed result together.
example : ComputableTidilyInPolyTime
      (fun n : ℕ => (fun total => total + n)^[n] 0) encUnary encUnary ∧
    ∀ n : ℕ, (fun total => total + n)^[n] 0 = n * n := by
  apply ComputableTidilyInPolyTime.iterateWith_spec (par := id)
    (count := id) (init := fun _ => 0) (step := fun n total => total + n)
    (invariant := fun n i total => total = i * n) (size := fun n => n * n)
  · polytime
  · polytime
  · polytime
  · polytime
  · simp
  · intro n i total _ htotal
    simp [htotal, Nat.add_mul]
  · fun_prop
  · intro n i total hi htotal
    simpa [htotal] using Nat.mul_le_mul_right n hi

-- Prefix invariants certify both a fold's size and its postcondition.
example : ComputableTidilyInPolyTime
      (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
      encBits encBits ∧
    ∀ word : List Bool, word.foldl (fun reversed bit => bit :: reversed) [] = word.reverse := by
  apply ComputableTidilyInPolyTime.foldl_spec (encA := encBool) (encL := encBits)
    (invariant := fun _ consumed state => state = consumed.reverse) (size := id)
  · polytime
  · polytime
  · polytime
  · simp
  · intro word consumed state bit _ hstate
    simp [hstate]
  · fun_prop
  · intro word consumed state hprefix hstate
    simpa [hstate] using hprefix.length_le

end ComplexityTests.PolyTimeTactic
