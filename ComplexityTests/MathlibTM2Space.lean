/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Classes.Space.TM2

/-! Regression checks for the Mathlib TM2 polynomial-space bridge. Source certificates in this
file supply termination, without supplying polynomial runtime certificates. -/

namespace ComplexityTests.MathlibTM2Space

open Computability Turing Turing.MultiTapeTM

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

private abbrev prependMachine : FinTM2 :=
  { idComputer Bool with m := fun _ => .push () (fun _ => false) .halt }

private instance : ∀ k, Finite (prependMachine.Γ k) := fun _ => inferInstanceAs (Finite Bool)

private noncomputable abbrev prependComputer :
    TM2Computable id id (fun w : List Bool => false :: w) where
  tm := prependMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  outputsFun _ := ⟨1, rfl⟩

private theorem prepend_bound (w : List Bool) (i : ℕ) (k : Unit) :
    (((TM2.stepTotal prependMachine.m)^[i] (initList prependMachine w)).stk k).length ≤
      w.length + 1 := by
  cases k
  cases i with
  | zero => change w.length ≤ w.length + 1; omega
  | succ i =>
    change (((TM2.stepTotal prependMachine.m)^[i]
      (haltList prependMachine (false :: w))).stk ()).length ≤ w.length + 1
    have hfixed := Function.iterate_fixed (show TM2.stepTotal prependMachine.m
      (haltList prependMachine (false :: w)) = haltList prependMachine (false :: w) from rfl) i
    exact (congrArg (fun cfg : prependMachine.Cfg => (cfg.stk ()).length) hfixed).le.trans
      (by change (false :: w).length ≤ w.length + 1; simp)

-- The endpoint starts from termination and a source-space bound, with no runtime argument.
example : ComputableTidilyInPolySpace (fun w : List Bool => false :: w)
    (encList (encFinite Bool)) (encList (encFinite Bool)) := by
  exact prependComputer.computableTidilyInPolySpace Function.injective_id Function.injective_id
    (space := fun w => w.length + 1) (PolyBounded.self.add (.const 1))
    (by
      intro w i k
      exact (prepend_bound (List.map prependComputer.inputAlphabet.symm w) i k).trans
        (Nat.add_le_add_right (List.length_map prependComputer.inputAlphabet.symm).le 1))

-- Explicitly exercise an exponential binary clock. This machine halts early; padding does not
-- assert an exponential lower bound on its runtime.
example : ComputableTidilyInPolySpace
    (fun w : List Bool => (TM2.stepTotal prependMachine.m)^[2 ^ (w.length + 1)]
      (initList prependMachine w)) (encList (encFinite Bool)) TM2.encCfg := by
  have hlength := ComputableTidilyInPolyTime.length_list (encFinite Bool)
  have hexponent := ComputableTidilyInPolyTime.unary_add.comp
    (hlength.prod (ComputableTidilyInPolyTime.const 1))
  exact TM2.run_polySpace prependMachine ComputableTidilyInPolyTime.id'
    (ComputableTidilyInPolyTime.binary_two_pow.comp hexponent) hexponent.polyBounded
    (fun w i _ k => prepend_bound w i k)

private theorem identity_bound {Γ : Type} [Fintype Γ] (w : List Γ) (i : ℕ) (k : Unit) :
    (((TM2.stepTotal (idComputer Γ).m)^[i] (initList (idComputer Γ) w)).stk k).length ≤
      w.length := by
  cases k
  cases i with
  | zero => exact le_rfl
  | succ i =>
    change (((TM2.stepTotal (idComputer Γ).m)^[i]
      (haltList (idComputer Γ) w)).stk ()).length ≤ w.length
    have hfixed := Function.iterate_fixed (show TM2.stepTotal (idComputer Γ).m
      (haltList (idComputer Γ) w) = haltList (idComputer Γ) w from rfl) i
    exact (congrArg (fun cfg : (idComputer Γ).Cfg => (cfg.stk ()).length) hfixed).le

private noncomputable abbrev identityComputer (Γ : Type) [Fintype Γ] :
    TM2Computable id id (id : List Γ → List Γ) where
  tm := idComputer Γ
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  outputsFun _ := ⟨1, rfl⟩

-- An empty alphabet requires no artificial inhabitant, even in the counting proof.
example : ComputableTidilyInPolySpace (id : List Empty → List Empty)
    (encList (encFinite Empty)) (encList (encFinite Empty)) := by
  let h := identityComputer Empty
  let : ∀ k, Finite (h.tm.Γ k) := fun _ => inferInstanceAs (Finite Empty)
  exact h.computableTidilyInPolySpace Function.injective_id Function.injective_id
    (space := List.length) .self
    (by
      intro w i k
      exact (identity_bound (Γ := Empty) (List.map h.inputAlphabet.symm w) i k).trans
        (List.length_map h.inputAlphabet.symm).le)

-- Input and output alphabets are independent, even when only the output alphabet is empty.
private abbrev clearMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ k := match k with
    | false => Bool
    | true => Empty
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := .pop false (fun _ a => a.isSome) (.branch id (.goto (fun _ => ())) .halt)

private def clearCfg (xs : List Bool) (v : Bool) : clearMachine.Cfg where
  l := some ()
  var := v
  stk k := match k with
    | false => xs
    | true => []

private theorem clear_step (xs : List Bool) (v : Bool) :
    clearMachine.step (clearCfg xs v) = some (match xs with
      | [] => haltList clearMachine []
      | _ :: xs => clearCfg xs true) := by
  cases xs <;> apply congrArg some <;>
    change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _ <;>
    congr 1 <;> funext k <;> cases k <;> rfl

private noncomputable abbrev clearComputer :
    TM2Computable id id (fun _ : List Bool => ([] : List Empty)) where
  tm := clearMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Empty
  outputsFun xs := by
    have hrun (xs : List Bool) (v : Bool) :
        (fun s : Option clearMachine.Cfg => s.bind clearMachine.step)^[xs.length + 1]
          (some (clearCfg xs v)) = some (haltList clearMachine []) := by
      induction xs generalizing v with
      | nil => exact clear_step [] v
      | cons a xs ih =>
        rw [List.length_cons, Function.iterate_succ_apply]
        simp only [Option.bind_some, clear_step]
        exact ih true
    refine ⟨xs.length + 1, ?_⟩
    have hinit : initList clearMachine xs = clearCfg xs false := by
      change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
      congr 1
      funext k
      cases k <;> rfl
    change (fun s : Option clearMachine.Cfg => s.bind clearMachine.step)^[xs.length + 1]
      (some (initList clearMachine (List.map id xs))) = some (haltList clearMachine [])
    rw [List.map_id, hinit]
    exact hrun xs false

private theorem clear_bound (xs : List Bool) (i : ℕ) : ∀ k,
    (((TM2.stepTotal clearMachine.m)^[i] (initList clearMachine xs)).stk k).length ≤
      xs.length := by
  have hstep (cfg : clearMachine.Cfg) (h : ∀ k, (cfg.stk k).length ≤ xs.length) :
      ∀ k, ((TM2.stepTotal clearMachine.m cfg).stk k).length ≤ xs.length := by
    cases hl : cfg.l with
    | none =>
      have heq : TM2.stepTotal clearMachine.m cfg = cfg := by
        change cfg.l.elim cfg _ = cfg
        rw [hl]
        rfl
      exact fun k => (congrArg (fun c : clearMachine.Cfg => (c.stk k).length) heq).le.trans (h k)
    | some label =>
      have heq : TM2.stepTotal clearMachine.m cfg =
          TM2.stepAux (clearMachine.m label) cfg.var cfg.stk := by
        change cfg.l.elim cfg _ = _
        rw [hl]
        rfl
      rw [heq]
      exact TM2.stepAux_stack_bound (clearMachine.m label) cfg.var cfg.stk xs.length h
  induction i with
  | zero => intro k; cases k <;> simp [initList]
  | succ i ih =>
    have heq := Function.iterate_succ_apply' (TM2.stepTotal clearMachine.m) i
      (initList clearMachine xs)
    exact fun k =>
      (congrArg (fun c : clearMachine.Cfg => (c.stk k).length) heq).le.trans (hstep _ ih k)

-- An infinite Boolean input domain and a distinct empty output alphabet. No default output
-- symbol is available; the empty output comes from clearing the input before halting.
example : ComputableTidilyInPolySpace (fun _ : List Bool => ([] : List Empty))
    (encList (encFinite Bool)) (encList (encFinite Empty)) := by
  let : ∀ k, Finite (clearComputer.tm.Γ k) := fun k => by
    change Finite (clearMachine.Γ k)
    cases k <;> infer_instance
  exact clearComputer.computableTidilyInPolySpace Function.injective_id Function.injective_id
    (space := List.length) .self
    (by
      intro xs i k
      simpa only [Equiv.refl_symm, Equiv.coe_refl, id_eq, List.map_id] using clear_bound xs i k)

-- A concrete Boolean decider crosses the final framed-word-to-Boolean encoding conversion.
private noncomputable abbrev boolComputer :
    TM2Computable encodeBool encodeBool (id : Bool → Bool) :=
  { tm := idComputer Bool
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    outputsFun _ := ⟨1, rfl⟩ }

example : {b : Bool | b = true} ∈ Cslib.Complexity.PSPACE
    ((⟨encodeBool, encodingBoolBool.encode_injective⟩ : Bool ↪ List Bool).trans
      (encList (encFinite Bool))) := by
  let : ∀ k, Finite (boolComputer.tm.Γ k) := fun _ => inferInstanceAs (Finite Bool)
  apply Cslib.Complexity.mem_PSPACE_of_tm2 boolComputer encodingBoolBool.encode_injective
    encodingBoolBool.encode_injective (space := fun _ => 1) (.const 1) ?_ (fun _ => Iff.rfl)
  intro b i k
  have hbound := identity_bound (Γ := Bool)
    (List.map boolComputer.inputAlphabet.symm (encodeBool b)) i k
  exact hbound.trans ((List.length_map boolComputer.inputAlphabet.symm).le.trans
    (show (encodeBool b).length ≤ 1 from le_rfl))

/--
info: 'Turing.TM2.exists_exponential_clock' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.TM2.exists_exponential_clock

/--
info: 'Turing.TM2Computable.computableTidilyInPolySpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.TM2Computable.computableTidilyInPolySpace

/--
info: 'Cslib.Complexity.mem_PSPACE_of_tm2' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PSPACE_of_tm2

end ComplexityTests.MathlibTM2Space
