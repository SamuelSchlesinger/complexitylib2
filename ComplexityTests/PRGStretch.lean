/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Stretch
import Complexity.Tactic.PPT

/-! Functional stretch, captured parameters, strict reductions and zero-count boundaries. -/

namespace ComplexityTests.PRGStretch

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

-- A toy expander exercises seed retention and suffix order; no security is claimed for it.
private def expand (seed : List Bool) : List Bool := seed ++ [false]

example : PRGStretch.stretch expand (fun _ => 3) [true, false] =
    [true, false, false, false, false] := by decide

example : PRGStretch.stretch expand (fun _ => 2) [] = [false, false] := by decide

example (seed : List Bool) : PRGStretch.stretch expand (fun _ => 0) seed = seed := rfl

-- Efficiency works uniformly on arbitrary initial words, with the generator capturing a bit.
example : ComputableTidilyInPolyTime
    (fun p : (ℕ × Bool) × List Bool =>
      PRGStretch.iterate (fun seed => seed ++ [p.1.2]) p.1.1 (p.1.1 ^ 2 + 1) p.2)
    (encPair (encPair encUnary encBool) encBits) encBits := by polytime

-- The entire randomized hybrid test composes, including its captured randomized distinguisher.
example : IsPPTOn (encPair (encPair encUnary encBool) encBits) encBool
    (fun p : (ℕ × Bool) × List Bool =>
      PRGStretch.test (fun seed => seed ++ [p.1.2]) p.1.1 (p.1.1 ^ 2 + 1)
        (fun word => do
          let bit ← ProbComp.uniform Bool
          return bit && decide (word.length = p.1.1)) p.2) := by
  ppt

-- Zero hops still samples a fair bit, but every sampled branch rejects.
example (generator : List Bool → List Bool) (adversary : Distinguisher) (n : ℕ)
    (challenge : List Bool) :
    ProbComp.eval (PRGStretch.reduction generator (fun _ => 0) adversary n challenge) =
      PMF.pure false := by
  simp only [PRGStretch.reduction, PRGStretch.hop, Nat.not_lt_zero, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_const]

-- Two hops use a four-element sampling range, including the padded rejecting outcomes.
example (generator : List Bool → List Bool) (adversary : Distinguisher) (n : ℕ) :
    Game.advantage
        (ProbComp.eval (prgRealGame (PRGStretch.stretch generator (fun _ => 2)) adversary n))
        (ProbComp.eval (prgIdealGame (fun n => n + 2) adversary n)) =
      4 * Game.advantage
        (ProbComp.eval
          (prgRealGame generator (PRGStretch.reduction generator (fun _ => 2) adversary) n))
        (ProbComp.eval (prgIdealGame (fun n => n + 1)
          (PRGStretch.reduction generator (fun _ => 2) adversary) n)) := by
  simpa only [show 2 ^ (Nat.log 2 2 + 1) = 4 by decide, Nat.cast_ofNat] using
    PRGStretch.advantage_eq generator (fun _ => 2) adversary n

-- A captured loop may add an input-dependent block at each iteration.
example : ComputableTidilyInPolyTime
    (fun word : List Bool => (fun state => state ++ word)^[word.length] []) encBits encBits := by
  apply ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
    (par := id) (step := fun word state => state ++ word) (growth := List.length)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by simpa using ComputableTidilyInPolyTime.id'.polyBounded_length (encIn := encBits))
  intro word state
  simp

-- Arbitrary iteration is deliberately not inferred from the step's polynomial-time certificate.
example : True := by
  fail_if_success
    have : ComputableTidilyInPolyTime
        (fun word : List Bool => (fun state => state ++ state)^[word.length] [true])
        encBits encBits := by polytime
  trivial

end ComplexityTests.PRGStretch
