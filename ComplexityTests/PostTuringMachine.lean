/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Kolmogorov.SingleTape
import Complexity.Computability.Machines.Turing.MultiTape.Halting
import Complexity.Computability.Machines.Turing.MultiTape.Halting.Partrec
import Complexity.Computability.Machines.Turing.MultiTape.SingleTape
import Complexity.Computability.Machines.Turing.SingleTape.Partrec
import Complexity.Computability.Machines.Turing.SingleTape.PostTuringMachine
import Complexity.Foundations.Data.BiTape
import Complexity.Foundations.Data.StackTape

/-!
# Tests for Mathlib `TM0`/`TM1` integration, single-to-multi-tape simulation, `Partrec` bridges,
and Kolmogorov complexity invariance

Concrete single-tape and multi-tape machines, tape equivalences, `TM0`/`TM1` translations,
time-and-space preserving simulations, `Partrec`/`Computable`/`ManyOneReducible` bridges,
machine-backed Kolmogorov complexity simulations, and `#print axioms` guards for headline theorems.
-/

namespace ComplexityTests.PostTuringMachine

open Cslib.Turing _root_.Turing Cslib.Kolmogorov.DescriptionMethod

/-! ### Tape equivalences (`StackTape` ↔ `ListBlank`, `BiTape` ↔ `Turing.Tape`) -/

example (l : List Bool) :
    (StackTape.mapSome l).equivListBlank = ListBlank.mk (l.map some) :=
  StackTape.equivListBlank_mapSome l

example (l : List Bool) :
    BiTape.equivTape (BiTape.mk₁ l) = Tape.mk₁ (l.map some) :=
  BiTape.equivTape_mk₁ l

example (l : List Bool) :
    (BiTape.mk₁ l).extractWord = some l :=
  BiTape.extractWord_mk₁ l

/-! ### Concrete `SingleTapeTM`, `TM0`, and `TM1` machines -/

/-- A concrete single-tape Turing machine that halts immediately on any input, leaving the input
unchanged on the tape (`id`). -/
def haltId : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ a := (⟨a, none⟩, none)

theorem haltId_outputsWithinTime (l : List Bool) :
    haltId.OutputsWithinTime l l 1 := by
  refine ⟨1, le_rfl, ?_⟩
  refine Relation.RelatesInSteps.tail _ (haltId.initCfg l) (haltId.haltCfg l) 0 (.refl _) ?_
  cases l <;> rfl

theorem haltId_outputs (l : List Bool) :
    haltId.Outputs l l := by
  obtain ⟨_, _, h⟩ := haltId_outputsWithinTime l
  exact h.reflTransGen

example (l : List Bool) :
    ∃ v, Nonempty (StateTransition.EvalsToInTime (_root_.Turing.TM1.step haltId.toTM1)
      (_root_.Turing.TM1.init (l.map some)) (some (haltId.toTM1Cfg (haltId.haltCfg l) v)) 1) :=
  (haltId.outputsWithinTime_iff_evalsToInTime_toTM1 l l 1).mp (haltId_outputsWithinTime l)

example (l : List Bool) :
    ListBlank.mk (l.map some) ∈ _root_.Turing.TM0.eval haltId.toTM0 (l.map some) :=
  haltId.outputs_imp_mem_eval_toTM0 (haltId_outputs l)

def haltIdTimeComputable : SingleTapeTM.TimeComputable (id : List Bool → List Bool) where
  tm := haltId
  timeBound _ := 1
  outputsFunInTime l := haltId_outputsWithinTime l

noncomputable def haltIdPolyTimeComputable :
    SingleTapeTM.PolyTimeComputable (id : List Bool → List Bool) where
  tm := haltId
  timeBound _ := 1
  outputsFunInTime l := haltId_outputsWithinTime l
  poly := 1
  bounds _ := by simp

/-! ### Single-tape to multi-tape simulation -/

example (l : List Bool) :
    let T := 2 * l.length + 4 + (1 + (l.length + 1))
    (MultiTapeTM.ofSingleTapeTM haltId).ComputesInTimeAndSpace l l T (T + 1) :=
  MultiTapeTM.computesInTimeAndSpace_ofSingleTapeTM haltId (haltId_outputsWithinTime l)

example :
    MultiTapeTM.ComputableInTimeAndSpace (id : List Bool → List Bool)
      (Function.Embedding.refl (List Bool)) (Function.Embedding.refl (List Bool))
      (fun a => 3 * a.length + 2 * 1 + 6) (fun a => 3 * a.length + 2 * 1 + 7) :=
  haltIdTimeComputable.computableInTimeAndSpace
    (Function.Embedding.refl (List Bool)) (Function.Embedding.refl (List Bool)) id (fun _ => rfl)

example :
    MultiTapeTM.ComputableTidilyInPolyTime (id : List Bool → List Bool)
      (Function.Embedding.refl (List Bool)) (Function.Embedding.refl (List Bool)) :=
  haltIdPolyTimeComputable.computableTidilyInPolyTime_id

/-! ### `Partrec` / `Computable` / `ManyOneReducible` bridges -/

example : Partrec haltId.eval :=
  haltId.partrec_eval

example : Computable (id : List Bool → List Bool) :=
  MultiTapeTM.IsComputable.computable_bits
    haltIdPolyTimeComputable.computableTidilyInPolyTime_id.isComputable

example :
    ManyOneReducible (· ∈ MultiTapeTM.selfHaltingProblem) (· ∈ MultiTapeTM.selfHaltingProblem) :=
  (MultiTapeTM.MappingReducible.refl MultiTapeTM.encBits
    MultiTapeTM.selfHaltingProblem).manyOneReducible_bits

/-! ### Kolmogorov complexity simulations and optimality -/

example (x : List Bool) :
    (ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM haltId)).ecomplexity x ≤
      (ofSingleTapeTM haltId).ecomplexity x :=
  ecomplexity_ofMultiTapeTM_ofSingleTapeTM_le haltId x

example : ∃ c : ℕ, ∀ n : ℕ,
    universal.ecomplexity n ≤ (ofSingleTapeTM haltId).ecomplexity n.bits + c :=
  exists_ecomplexity_universal_le_ofSingleTapeTM_bits haltId

/-! ### Axiom guards for headline results -/

/--
info: 'Cslib.Turing.StackTape.equivListBlank' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.StackTape.equivListBlank

/--
info: 'Cslib.Turing.BiTape.equivTape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.BiTape.equivTape

/--
info: 'Cslib.Turing.SingleTapeTM.outputs_iff_mem_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.outputs_iff_mem_eval

/--
info: 'Cslib.Turing.SingleTapeTM.outputsWithinTime_iff_evalsToInTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.outputsWithinTime_iff_evalsToInTime

/--
info: 'Cslib.Turing.SingleTapeTM.outputsWithinTime_iff_evalsToInTime_toTM1' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.outputsWithinTime_iff_evalsToInTime_toTM1

/--
info: 'Cslib.Turing.SingleTapeTM.outputs_imp_mem_eval_toTM0' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.outputs_imp_mem_eval_toTM0

/--
info: 'Cslib.Turing.SingleTapeTM.eval_ofTM0' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.eval_ofTM0

/--
info: 'Cslib.Turing.SingleTapeTM.outputsWithinTime_ofTM0_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.outputsWithinTime_ofTM0_iff

/--
info: 'Cslib.Turing.SingleTapeTM.eval_ofTM1' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.eval_ofTM1

/--
info: 'Turing.MultiTapeTM.computesInTimeAndSpace_ofSingleTapeTM' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.computesInTimeAndSpace_ofSingleTapeTM

/--
info: 'Turing.MultiTapeTM.computesInTimeAndSpace_ofTM0' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.computesInTimeAndSpace_ofTM0

/--
info: 'Cslib.Turing.SingleTapeTM.TimeComputable.computableInTimeAndSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.TimeComputable.computableInTimeAndSpace

/--
info: 'Cslib.Turing.SingleTapeTM.PolyTimeComputable.computableTidilyInPolyTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.PolyTimeComputable.computableTidilyInPolyTime

/--
info: 'Computable.stateTransition_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Computable.stateTransition_eval

/--
info: 'Cslib.Turing.SingleTapeTM.partrec_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.partrec_eval

/--
info: 'Cslib.Turing.SingleTapeTM.partrec_tm0_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.partrec_tm0_eval

/--
info: 'Cslib.Turing.SingleTapeTM.partrec_tm1_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Turing.SingleTapeTM.partrec_tm1_eval

/--
info: 'Turing.MultiTapeTM.Universal.primrec_simulate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.primrec_simulate

/--
info: 'Turing.MultiTapeTM.Universal.Desc.partrec_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.Desc.partrec_eval

/--
info: 'Turing.MultiTapeTM.partrec_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.partrec_eval

/--
info: 'Turing.MultiTapeTM.IsComputable.computable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.IsComputable.computable

/--
info: 'Turing.MultiTapeTM.IsDecidable.computablePred' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.IsDecidable.computablePred

/--
info: 'Turing.MultiTapeTM.MappingReducible.manyOneReducible' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.MappingReducible.manyOneReducible

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.isPartrec_ofMultiTapeTM_map' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.isPartrec_ofMultiTapeTM_map

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universal_le_ofMultiTapeTM' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universal_le_ofMultiTapeTM

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.singleTapeSimulation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.singleTapeSimulation

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universal_le_ofSingleTapeTM' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universal_le_ofSingleTapeTM

end ComplexityTests.PostTuringMachine
