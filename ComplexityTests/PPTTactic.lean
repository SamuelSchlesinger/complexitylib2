/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PPT
import Complexity.Crypto.Computational.GGM.Evaluation

/-! Ordinary probabilistic programs use `ppt`; deterministic callbacks reuse `polytime`. -/

namespace ComplexityTests.PPTTactic

open Cslib Cslib.Probability Turing.MultiTapeTM

example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then word.reverse else word)) := by
  ppt

-- The deterministic callback needs a bounded-growth fold rule after sampling.
example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure ((bit :: word).foldl (fun reversed next => next :: reversed) [])) := by
  ppt

-- A local routine can take a tuple assembled from captured data.
example (sample : (List Bool × ℕ) × List Bool → ProbComp Bool)
    (hsample : IsPPTOn (encPair (encPair encBits encUnary) encBits) encBool sample) :
    IsPPTOn encBits encBool
      (fun word => sample ((word.reverse, word.length), word ++ word)) := by
  ppt

-- Failure of the first encoding must leave the second local certificate usable.
example (sample : ℕ → ProbComp Bool)
    (_hUnary : IsPPTOn encUnary encBool sample) (hBinary : IsPPTOn encNat encBool sample) :
    IsPPTOn (encPair encNat encBool) encBool (fun pair => sample pair.1) := by
  ppt

-- The continuation needs unary iteration: an additional binary-output certificate must not
-- force that encoding onto the sampled value. This is the opposite side of a routine call.
example (sample : List Bool → ProbComp ℕ)
    (hUnary : IsPPTOn encBits encUnary sample) (_hBinary : IsPPTOn encBits encNat sample) :
    IsPPTOn encBits encBool (fun word => do
      let n ← sample word
      pure ((List.range n).foldl (fun parity _ => !parity) true)) := by
  ppt

example (sample : List Bool → ProbComp ℕ)
    (_hBinary : IsPPTOn encBits encNat sample) (hUnary : IsPPTOn encBits encUnary sample) :
    IsPPTOn encBits encBool (fun word => do
      let n ← sample word
      pure ((List.range n).foldl (fun parity _ => !parity) true)) := by
  ppt

example (sample : List Bool → ProbComp ℕ)
    (hUnary : IsPPTOn encBits encUnary sample) (_hBinary : IsPPTOn encBits encNat sample) :
    IsPPTOn encBits encBool (fun word =>
      (fun n => (List.range n).foldl (fun parity _ => !parity) true) <$> sample word) := by
  ppt

example (sample : List Bool → ProbComp ℕ)
    (_hBinary : IsPPTOn encBits encNat sample) (hUnary : IsPPTOn encBits encUnary sample) :
    IsPPTOn encBits encBool (fun word =>
      (fun n => (List.range n).foldl (fun parity _ => !parity) true) <$> sample word) := by
  ppt

-- GGM keeps the original path available after a certified seed sampler.
example (sample : List Bool → ProbComp (List Bool)) (generator : List Bool → List Bool)
    (hsample : IsPPTOn encBits encBits sample)
    (hgenerator : ComputableTidilyInPolyTime generator encBits encBits) :
    IsPPTOn encBits encBits (fun path => do
      let seed ← sample path
      pure (Crypto.GGM.eval generator seed path)) := by
  ppt

private noncomputable def sampleTagged (word : List Bool) : ProbComp (List Bool) := do
  let bit ← ProbComp.uniform Bool
  pure (bit :: word)

@[program_certificate]
private theorem sampleTagged_ppt : IsPPTOn encBits encBits sampleTagged := by
  unfold sampleTagged
  ppt

attribute [irreducible] sampleTagged

example : IsPPTOn encBits encBits sampleTagged := by ppt

-- The named implementation stays folded inside a captured continuation and a conditional.
example : IsPPTOn encBits encBits (fun word => do
    let tagged ← sampleTagged word
    if word = [] then sampleTagged tagged else sampleTagged (tagged ++ word)) := by
  ppt

-- The same registered probabilistic certificate is compositional under fun_prop.
example : IsPPTOn encBits encBits (fun word => sampleTagged (word ++ word)) := by
  fun_prop

private noncomputable def sampleFixed (n : ℕ) (word : List Bool) : ProbComp (List Bool) :=
  sampleTagged (List.replicate n false ++ word)

@[program_certificate]
private theorem sampleFixed_zero (n : ℕ) (h : n = 0) :
    IsPPTOn encBits encBits (sampleFixed n) := by
  subst n
  fun_prop [sampleFixed]

@[program_certificate]
private theorem sampleFixed_ppt (n : ℕ) : IsPPTOn encBits encBits (sampleFixed n) := by
  fun_prop [sampleFixed]

attribute [irreducible] sampleFixed

-- An inapplicable registered side condition must not hide the next certificate.
example : IsPPTOn encBits encBits (sampleFixed 1) := by ppt

-- Neither an unknown sampler nor a non-dyadic finite uniform law is a free operation.
example (_sample : List Bool → ProbComp Bool) : True := by
  fail_if_success have : IsPPTOn encBits encBool _sample := by ppt
  let encFin3 : Fin 3 ↪ List Bool := Fin.valEmbedding.trans encNat
  fail_if_success have : IsPPTOn encBits encFin3 (fun _ => ProbComp.uniform (Fin 3)) := by ppt
  trivial

end ComplexityTests.PPTTactic
