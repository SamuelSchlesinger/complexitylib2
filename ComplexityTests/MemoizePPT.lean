/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PPT

/-! Memoization composes through functional programs, with no default inhabitants. -/

namespace ComplexityTests.MemoizePPT

open Cslib Cslib.Probability Turing.MultiTapeTM

-- Neither key nor value types have an Inhabited instance in this generic client.
example {α Key Value : Type} [BEq Key] [LawfulBEq Key] {input : α ↪ List Bool}
    {keyEncoding : Key ↪ List Bool} {valueEncoding : Value ↪ List Bool}
    {compute : α → Key → ProbComp Value} {query : α → Key} {cache : α → List (Key × Value)}
    (hcompute : IsPPTOn input valueEncoding (fun a => compute a (query a)))
    (hquery : ComputableTidilyInPolyTime query input keyEncoding)
    (hcache : ComputableTidilyInPolyTime cache input
      (encList (encPair keyEncoding valueEncoding))) :
    IsPPTOn input (encPair valueEncoding (encList (encPair keyEncoding valueEncoding)))
      (fun a => memoize (compute a) (query a) (cache a)) := by ppt

-- Runtime word lengths and the whole initial cache are charged, including all framing.
example : IsPPTOn (encPair encBits (encList (encPair encBits encBits)))
    (encPair encBits (encList (encPair encBits encBits)))
    (fun p => memoize (fun key => BitString.sampleList key.length) p.1 p.2) := by fun_prop

private noncomputable def repeated (word : List Bool) :
    ProbComp ((List Bool × List Bool) × List (List Bool × List Bool)) := do
  let (first, cache) ← memoize (fun key => BitString.sampleList key.length) word []
  let (second, cache) ← memoize (fun key => BitString.sampleList key.length) word cache
  return ((first, second), cache)

-- Ordinary do notation threads the cache and retains the query across both calls.
example : IsPPTOn encBits
    (encPair (encPair encBits encBits) (encList (encPair encBits encBits))) repeated := by
  unfold repeated
  ppt

-- The two replies agree in their full joint law; the second call does not resample.
example (word : List Bool) : ProbComp.eval (repeated word) =
    (BitString.uniformList word.length).map (fun value => ((value, value), [(word, value)])) := by
  rw [repeated, memoize_repeat]
  simp [memoize, ProbComp.eval_map, PMF.map, Function.comp_def]

end ComplexityTests.MemoizePPT
