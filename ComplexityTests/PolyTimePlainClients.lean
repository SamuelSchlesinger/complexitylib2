/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Layered.Compile.PolyTime
import Complexity.Computability.Circuit.Boolean.EvaluationTime
import Complexity.Crypto.Computational.Signature
import Complexity.Crypto.Computational.MAC
import ComplexityTests.PolyTimePlainDriver

/-! Plain client goals use imported public certificates, without automatic tidy-goal lowering.
A separate rule set exercises the production named lookup with no compositional search rule. -/

open Turing.MultiTapeTM Cslib.Crypto

namespace ComplexityTests.PolyTimePlainClients


@[aesop unsafe 100% tactic (rule_sets := [PolyTimePlainNamedOnly])]
private meta def namedOnly : Aesop.RuleTac :=
  Cslib.Tactic.applyCertificates `Turing.MultiTapeTM.ComputableInPolyTime

-- These are the actual imported structure fields, not wrappers supplying their proofs.
example (S : SignatureScheme) : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool => S.verify p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool := by
  fail_if_success aesop
  aesop (rule_sets := [PolyTimePlainNamedOnly])

example (M : MACScheme) : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool => M.verify p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool := by
  fail_if_success aesop
  aesop (rule_sets := [PolyTimePlainNamedOnly])

-- Internal raw construction may normalize an imported plain-only named certificate.
example (B : Cslib.WordRAM.Basis) (c : ℕ) : ComputableTidilyInPolyTime
    (PlainDriverTests.checkedNamedConstant B c c) encUnary (encOption encNat) := by
  fail_if_success fun_prop
  polytime

-- Eager obligations and the opaque routine are imported from another client module.
example (B : Cslib.WordRAM.Basis) (c : ℕ) : ComputableInPolyTime
    (PlainDriverTests.checkedNamedConstant B c c) encUnary (encOption encNat) := by
  fail_if_success fun_prop
  aesop (rule_sets := [PolyTimePlainNamedOnly])

example (B : Cslib.WordRAM.Basis) (limit c : ℕ) (hbound : c ≤ limit) : ComputableInPolyTime
    (PlainDriverTests.checkedNamedConstant B limit c) encUnary (encOption encNat) := by
  fail_if_success (clear hbound; polytime)
  polytime

open Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Layered in
-- The actual compiler certificate includes runtime input arity, arbitrary code and its depths.
example : ComputableInPolyTime
    (fun p : ℕ × (List (Op × List ℕ) × List ℕ) => compile p.1 p.2)
    (encPair encUnary encCode) encCompiled := by polytime

open Cslib.Circuits Boolean in
example {α : Type} {enc : α ↪ List Bool} (c : α → Σ n, Circuit signature n 1)
    (x : α → List Bool) (hc : ComputableInPolyTime c enc (encCircuit 1))
    (hx : ComputableInPolyTime x enc encBits) : ComputableInPolyTime
    (fun a => (c a).2.eval interpretation (Cslib.BitString.ofList (c a).1 (x a)) 0)
    enc encBool := by
  fail_if_success (clear hc; polytime)
  fail_if_success (clear hx; polytime)
  polytime

example {α : Type} {enc : α ↪ List Bool} (f g : α → List Bool)
    (hf : ComputableInPolyTime f enc encBits) (hg : ComputableInPolyTime g enc encBits) :
    ComputableInPolyTime (fun a => f a ++ g a) enc encBits := by
  fail_if_success (clear hf; polytime)
  polytime

-- The global raw-only theorem is imported, but there is no local certificate to restate.
example : ComputableInPolyTime PlainDriverTests.rawOnlyReverse encBits encBits := by
  fail_if_success polytime
  exact .of_tidy PlainDriverTests.rawOnlyReverse_tidy

-- Blanket disabling of transitions would reject this legitimate plain contract.
example (f : List Bool → List Bool) (hf : PlainDriverTests.RoutineContract f) :
    ComputableInPolyTime f encBits encBits := by
  fail_if_success fun_prop (config := { maxTransitionDepth := 0 })
  polytime

-- Growth evidence remains a real premise of the direct plain loop rules.
example (step : List Bool → Bool → List Bool) (growth : ℕ)
    (hstep : ComputableInPolyTime (fun p : List Bool × Bool => step p.1 p.2)
      (encPair encBits encBool) encBits)
    (hgrowth : ∀ word bit, (step word bit).length ≤ word.length + growth) :
    ComputableInPolyTime (fun word : List Bool => word.foldl step []) encBits encBits := by
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime

example {α : Type} {enc : α ↪ List Bool} (count : α → ℕ) (init : α → List Bool)
    (step : List Bool → List Bool) (growth : ℕ)
    (hcount : ComputableInPolyTime count enc encUnary)
    (hinit : ComputableInPolyTime init enc encBits)
    (hstep : ComputableInPolyTime step encBits encBits)
    (hgrowth : ∀ word, (step word).length ≤ word.length + growth) :
    ComputableInPolyTime (fun a => step^[count a] (init a)) enc encBits := by
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime


-- The original captured-step interface passed the baseline driver and must remain available.
example {α : Type} {enc : α ↪ List Bool} (count : α → ℕ) (init : α → List Bool)
    (step : α → List Bool → List Bool) (growth : α → ℕ)
    (hcount : ComputableInPolyTime count enc encUnary)
    (hinit : ComputableInPolyTime init enc encBits)
    (hstep : ComputableInPolyTime (fun p : α × List Bool => step p.1 p.2)
      (encPair enc encBits) encBits)
    (hpoly : PolyBounded (fun a => (enc a).length) growth)
    (hgrowth : ∀ a word, (step a word).length ≤ word.length + growth a) :
    ComputableInPolyTime (fun a => (step a)^[count a] (init a)) enc encBits := by
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hpoly; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime

-- The captured fold keeps arbitrary element/state encodings and its original list interfaces.
example {γ α β : Type} (input : γ ↪ List Bool) (element : α ↪ List Bool)
    (stateEncoding : β ↪ List Bool) (listEncoding : List α ↪ List Bool)
    [ListEncoding element listEncoding] [SizedListEncoding element listEncoding]
    (list : γ → List α) (initial : γ → β) (step : γ → β → α → β)
    (hlist : ComputableInPolyTime list input listEncoding)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : ComputableInPolyTime (fun p : (γ × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair input stateEncoding) element) stateEncoding)
    (growth : γ → ℕ) (hpoly : PolyBounded (fun x => (input x).length) growth)
    (hgrowth : ∀ x state value, value ∈ list x →
      (stateEncoding (step x state value)).length ≤ (stateEncoding state).length + growth x) :
    ComputableInPolyTime (fun x => (list x).foldl (step x) (initial x)) input stateEncoding := by
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime

end ComplexityTests.PolyTimePlainClients
