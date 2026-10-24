/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Machines.Turing.TM2.Reverse.Transfer

/-! Public clients and named axiom guards for the reverse stack-machine compiler. -/

namespace ComplexityTests.MathlibTM2Reverse

open Turing Turing.MultiTapeTM

private def stopAction : Action 0 Bool Unit := ⟨.pos, Fin.elim0, some true, none⟩

private def stop : MultiTapeTM 0 Bool Unit := .ofTr () (fun _ _ _ => stopAction)

private theorem stop_run (input : List Bool) :
    stop.runFrom (stop.initCfg input) 1 = stopAction.apply (stop.initCfg input) := by
  rw [runFrom_one, step_of_state (by rfl)]
  simp only [stop, tr_ofTr]

private theorem stop_computes (input : List Bool) : stop.Computes input [true] :=
  ⟨1, by rw [stop_run]; rfl, by rw [stop_run]; rfl⟩

private theorem stop_computable :
    ComputableInTimeAndSpace (fun _ : List Bool => true) encBits encBool
      (fun _ => 1) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, stop, fun input => ⟨stop_computes input, ?_, ?_⟩⟩
  · apply runsInTime_iff_halted.mpr
    rw [stop_run]
    rfl
  · exact MultiTapeNTM.runsInSpace_zero_tapes _ _ _

-- An actual finite-state zero-work-tape machine yields a certificate over its original encodings.
example : ∃ h : TM2ComputableInPolyTime encBits encBool (fun _ : List Bool => true),
    ∀ stack, Finite (h.tm.Γ stack) :=
  stop_computable.exists_tm2ComputableInPolyTime (.const 1)

-- Initialization, cleanup and arbitrarily long padding all count the stored input and answer.
example (input : List Bool) (i : ℕ) :
    ToTM2.totalStackLength ((TM2.stepTotal (ToTM2.machine stop.q₀ stop.tr).m)^[i]
      (initList (ToTM2.machine stop.q₀ stop.tr) input)) ≤ input.length + 1 := by
  simpa using ToTM2.reachable_stack_bound stop (stop_computes input)
    (MultiTapeNTM.runsInSpace_zero_tapes _ _ 0) i

/--
info: 'Turing.MultiTapeTM.ToTM2.outputsInTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ToTM2.outputsInTime

/--
info: 'Turing.MultiTapeTM.ToTM2.reachable_stack_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ToTM2.reachable_stack_bound

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_tm2Computable_bool' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_tm2Computable_bool

/--
info: 'Turing.MultiTapeTM.computableInPolyTime_iff_tm2' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.computableInPolyTime_iff_tm2

/--
info: 'Turing.MultiTapeTM.computableInPolySpace_iff_tm2' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.computableInPolySpace_iff_tm2

/--
info: 'Cslib.Complexity.mem_PSPACE_iff_tm2' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PSPACE_iff_tm2

end ComplexityTests.MathlibTM2Reverse
