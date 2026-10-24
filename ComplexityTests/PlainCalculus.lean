/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain.Calculus
import Complexity.Tactic.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Plain.Calculus
import Complexity.Computability.Complexity.Parameterized.PlainCalculus

/-! Plain synthesis through ordinary rules, captured routines and preserved resource premises. -/

universe u

open Turing.MultiTapeTM

-- Ordinary checked coverage clients retain the narrower construction statements while using
-- the existing broader canonical APIs. The inventory inspects the five named proof heads.
namespace ComplexityTests.PlainCalculus

theorem coverage_polySpace_comp :
    ∀ {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
      {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β},
      ComputableInPolySpace f encMid encOut →
        ComputableInPolySpace g encIn encMid →
          ComputableInPolySpace (fun (a : α) => f (g a)) encIn encOut := by
  intros
  apply Turing.MultiTapeTM.ComputableInPolySpace.comp <;> assumption

theorem coverage_polySpace_comp' :
    ∀ {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
      {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β},
      ComputableInPolySpace f encMid encOut →
        ComputableInPolySpace g encIn encMid →
          ComputableInPolySpace (fun (a : α) => f (g a)) encIn encOut := by
  intros
  apply Turing.MultiTapeTM.ComputableInPolySpace.comp' <;> assumption

theorem coverage_polyTime_fst' :
    ∀ {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {δ : Type}
      {encD : δ ↪ List Bool} {f : α → β × δ},
      ComputableInPolyTime f encA
          (encPair encB encD) →
        ComputableInPolyTime (fun (x : α) => (f x).1) encA encB := by
  intros
  apply Turing.MultiTapeTM.ComputableInPolyTime.fst' <;> assumption

theorem coverage_polyTime_snd' :
    ∀ {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {δ : Type}
      {encD : δ ↪ List Bool} {f : α → β × δ},
      ComputableInPolyTime f encA
          (encPair encB encD) →
        ComputableInPolyTime (fun (x : α) => (f x).2) encA encD := by
  intros
  apply Turing.MultiTapeTM.ComputableInPolyTime.snd' <;> assumption

theorem coverage_polyTime_trans :
    ∀ {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {δ : Type}
      {encD : δ ↪ List Bool} {f : α → β} {g : β → δ},
      ComputableInPolyTime f encA encB →
        ComputableInPolyTime g encB encD →
          ComputableInPolyTime (fun (x : α) => g (f x)) encA encD := by
  intros
  apply Turing.MultiTapeTM.ComputableInPolyTime.trans <;> assumption

example :
    ∀ {α β : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {c : α → Bool}
      {f g : α → β},
      ComputableInPolySpace c encIn encBool →
        ComputableInPolySpace f encIn encMid →
          ComputableInPolySpace g encIn encMid →
            ComputableInPolySpace
              (fun (a : α) => if c a = Bool.true then f a else g a) encIn encMid := by
  intros
  apply Turing.MultiTapeTM.ComputableInPolySpace.ite <;> assumption

example :
    ∀ {α β : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {f : α → β},
      ComputableInPolyTime f encIn encMid →
        ComputableInPolySpace f encIn encMid := by
  intros
  apply Turing.MultiTapeTM.ComputableInPolySpace.of_polyTime
  assumption

example :
    ∀ {α β δ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encD : δ ↪ List Bool}
      {f : α → β} {g : α → δ},
      ComputableInPolySpace f encIn encMid →
        ComputableInPolySpace g encIn encD →
          ComputableInPolySpace (fun (a : α) => (f a, g a)) encIn
            (encPair encMid encD) := by
  intros
  apply Turing.MultiTapeTM.ComputableInPolySpace.prod <;> assumption

example :
    ∀ {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} [Finite α] (f : α → β),
      ComputableInPolyTime f encA encB := by
  intros
  apply Turing.MultiTapeTM.ComputableInPolyTime.of_finite

end ComplexityTests.PlainCalculus

-- Newly landed generic membership rules use the same public plain entrypoint.
example : ComputableInPolyTime (fun p : ℕ × List ℕ => decide (p.1 ∈ p.2))
    (encPair encNat (encList encNat)) encBool := by fun_prop

example : ComputableInPolyTime (fun p : ℕ × List ℕ => decide (p.1 ∉ p.2))
    (encPair encNat (encList encNat)) encBool := by fun_prop

example : ComputableInPolyTime (fun xs : List ℕ => xs.map (fun x => x + x))
    (encList encUnary) (encList encUnary) := by fun_prop

example : ComputableInPolyTime (fun xs : List ℕ => xs.map (fun x => x + 1))
    (encList encNat) (encList encNat) := by fun_prop

example {α : Type} {enc : α ↪ List Bool} {f : α → ℕ} {xs : α → List ℕ}
    (hf : ComputableInPolyTime f enc encUnary)
    (hxs : ComputableInPolyTime xs enc (encList encUnary)) :
    ComputableInPolyTime (fun a => (xs a).map (fun x => f a + x))
      enc (encList encUnary) := by fun_prop

-- A whole telescope, including a bounded-growth hypothesis, is transported rather than only
-- replacing the conclusion. The ordinary implicit/explicit argument API remains usable.
example {α β γ : Type} {enc : γ ↪ List Bool} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {xs : γ → List α} {init : γ → β} {step : β → α → β}
    (hxs : ComputableInPolyTime xs enc (encList encA))
    (hinit : ComputableInPolyTime init enc encB)
    (hstep : ComputableInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {growth : ℕ}
    (hgrowth : ∀ state value, (encB (step state value)).length ≤
      (encB state).length + growth) :
    ComputableInPolyTime (fun a => (xs a).foldl step (init a)) enc encB :=
  ComputableInPolyTime.foldl_of_bounded_growth hxs hinit hstep hgrowth

-- Existing stronger universe-polymorphic projection rules are preserved, not replaced by the
-- Type-zero source rule. Named argument clients retain their old binder names.
example {α β γ : Type u} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolyTime f enc (encPair encB encC)) :
    ComputableInPolyTime (fun a => (f a).1) enc encB :=
  ComputableInPolyTime.fst' (enc₁ := encB) (enc₂ := encC) hf

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.binary_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ComputableInPolyTime.binary_add

-- The tactic's named-program registry uses the plain predicate and retains the source rule's
-- eager list premise; the composed client needs no exposed tidy conversion.
run_meta do
  let rules := (Cslib.Tactic.certificateExt.getState (← Lean.getEnv)).getD
    (`Turing.MultiTapeTM.ComputableInPolyTime, `List.any, false) #[]
  unless rules.any (fun entry =>
      entry.1 == `Turing.MultiTapeTM.ComputableInPolyTime.anyWithInput &&
        entry.2 == #[`hlist]) do
    throwError "plain routine rule lost its program index or eager list premise"

example : ComputableInPolyTime (fun p : ℕ × List ℕ => p.2.any (fun x => decide (x = p.1)))
    (encPair encNat (encList encNat)) encBool := by polytime

-- Independent time and space functions remain independent under composition.
example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : β → γ} {g : α → β} {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInO f encB encC T₂ S₂) (hg : ComputableInO g encA encB T₁ S₁) :
    ComputableInO (f ∘ g) encA encC (fun a => T₁ a + T₂ (g a))
      (fun a => S₁ a + S₂ (g a)) := hf.comp hg

example : Cslib.Complexity.ComputableInFPTTime (fun n : ℕ => n + 1) encUnary encUnary id := by
  have hn : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encUnary := by fun_prop
  exact hn.computableInFPTTime id

example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β} {g : β → γ} {κA : α → ℕ} {κB : β → ℕ}
    (hg : Cslib.Complexity.ComputableInFPTTime g encB encC κB)
    (hf : Cslib.Complexity.ComputableInFPTTime f encA encB κA) {h : ℕ → ℕ}
    (hκ : ∀ a, κB (f a) ≤ h (κA a)) :
    Cslib.Complexity.ComputableInFPTTime (g ∘ f) encA encC κA := hg.comp hf hκ

-- Quantitative registers the tidy big-O property. Its plain property and sum rules must receive
-- the same registration; otherwise an actual GenericRAM projection client fails immediately.
example {α β : Type} (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInO (Sum.getLeft? : α ⊕ β → Option α) (encSum left right) (encOption left)
      (fun s => ((encSum left right) s).length)
      (fun s => ((encSum left right) s).length) := by fun_prop

set_option maxHeartbeats 2000 in
-- Preserving source registration order reduces this former 20,000-heartbeat timeout to 32.
/-- Primitive registration sanity; independent synthesis is checked by the inventory holdouts. -/
example : ComputableInPolyTime (fun p : List Bool × ℕ => p.1.take p.2)
    (encPair encBits encUnary) encBits := by fun_prop

-- Matrix access captures the original word and dimensions while the row index varies.
example {α : Type} {input : α ↪ List Bool} {cols width col : α → ℕ}
    {word : α → List Bool} (hcols : ComputableInPolyTime cols input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (hcol : ComputableInPolyTime col input encUnary) :
    ComputableInPolyTime
      (fun p : α × ℕ => Cslib.Matrix.binaryEntry (cols p.1) (width p.1) (word p.1) p.2 (col p.1))
      (encPair input encUnary) encNat := by fun_prop

-- The stopped-walk result composes with an ordinary projection; graph parameters remain runtime
-- inputs, while the walk length and signal alphabet are fixed.
example {P V D : Type} {input : P ↪ List Bool} {vertex : V ↪ List Bool}
    {label : D ↪ List Bool} {rotate : P × (V × D) → V × D}
    (hrotate : ComputableInPolyTime rotate
      (encPair input (encPair vertex label)) (encPair vertex label))
    (T q : ℕ) [NeZero q] (signal : Fin q ↪ List Bool) :
    ComputableInPolyTime
      (fun p : P × (V × ((Fin T → D) × (Fin T → Fin q))) =>
        (Cslib.RotationMap.killedPowRotWithInput rotate T q p).1)
      (encPair input (encPair vertex (encPair (encPi label) (encPi signal)))) vertex := by
  fun_prop
