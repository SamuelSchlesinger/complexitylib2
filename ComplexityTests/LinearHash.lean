/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.LinearHash
import Complexity.Tactic.PPT

/-! Matrix hashing through ordinary functional programs and arbitrary public-output tests. -/

namespace ComplexityTests.LinearHash

open Cslib Cslib.BitString Cslib.BitString.LinearHash Cslib.Probability
open Cslib.Probability.PMF Turing.MultiTapeTM

-- A partial final matrix row is padded with false, rather than discarded.
example : wordHash 2 [true, false, true] [true, true] = [true, true] := by decide

-- Empty inputs retain the requested number of zero-width rows and output bits.
example : wordHash 3 [true, true] [] = [false, false, false] := by decide

example : ProbComp.eval (extract 3 []) = PMF.pure [false, false, false] := by
  simp [extract, wordHash, listRows, listRow]

-- Zero digest bits require no matrix bits, whatever the source length.
example (input : List Bool) : ProbComp.eval (extract 0 input) = PMF.pure [] := by
  simp [extract, wordHash, listRows]

-- The digest marginal can be uniform while the complete output repeats its public seed.
example : ProbComp.eval (extract 1 [true]) =
    (PMF.uniformOfFintype Bool).map (fun bit => [bit, bit]) := by
  simp [extract, sampleList, wordHash, listRows, listRow]

-- The hash count and both words can be computed from an alternatively encoded caller.
example : ComputableTidilyInPolyTime
    (fun p : List Bool × ℕ => wordHash (p.2 + 1) (p.1 ++ [true]) p.1)
    (encPair (encList encBool) encUnary) encBits := by fun_prop

-- A nested second projection uses the same conversion rule, independent of hashing.
example : ComputableTidilyInPolyTime
    (fun p : ℕ × (Bool × List Bool) => p.2.2)
    (encPair encUnary (encPair encBool (encList encBool))) encBits := by fun_prop

-- Encoding conversion also works in the other direction when its certificate is available.
example : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => p.2)
    (encPair encUnary encBits) (encList encBool) := by fun_prop

example : IsPPTOn (encPair encBits encUnary) encBits
    (fun p : List Bool × ℕ => extract (p.2 + 1) (p.1 ++ [false])) := by ppt

example : IsPPTOn (encPair (encList encBool) encUnary) encBits
    (fun p : List Bool × ℕ => extract (p.2 + 1) (p.1 ++ [false])) := by ppt

-- The same sampler written with explicit binds certifies without a syntax-specific rule.
example : IsPPTOn (encPair (encList encBool) encUnary) encBits
    (fun p : List Bool × ℕ =>
      sampleList ((p.2 + 1) * (p.1 ++ [false]).length) >>= fun seed =>
        pure (seed ++ wordHash (p.2 + 1) seed (p.1 ++ [false]))) := by ppt

-- Tests may randomize based on the entire output, with no efficiency assumption.
example {n m : ℕ} (source : PMF (BitString n)) (test : List Bool → PMF Bool) :
    dist (((source.map List.ofFn).bind (fun input => ProbComp.eval (extract m input))).bind test)
        ((uniformList (m * n + m)).bind test) ≤
      Real.sqrt ((2 : ℝ) ^ m * collisionProbability source) / 2 :=
  extract_dist_bind_le source test

end ComplexityTests.LinearHash
