/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Instance
public import Complexity.Computability.TreeEval.Reader.Size

/-!
# Tree Evaluation in small space

**Cook and Mertz**: Tree Evaluation of value length `ℓ` and height `H` is tidily computable on
multi-tape Turing machines in space `O((ℓ + H + 1) · log (ℓ + 2) + log (n + 2))`, where `n`
is the length of the encoded instance.

The step machine simulating the read machine `Cslib.TreeEval.Reader.machine` is tidy, its run on an
instance halts with the value of the tree, and its states along the run, which follow the states
of the read machine together with the position of the head, stay within the space bound.

## Main results

* `Cslib.TreeEval.computableTidilyInSpace_eval`: Tree Evaluation in space
  `O(spaceBound ℓ H + log (n + 2))`.
-/

@[expose] public section

namespace Cslib.TreeEval

open Turing MultiTapeTM Reader

/-- **Tree Evaluation in small space** (Cook–Mertz): the value of the tree of an instance of value
length `ℓ` and height `H` is tidily computable from its encoding in space
`O((ℓ + H + 1) · log (ℓ + 2) + log (n + 2))`. -/
theorem computableTidilyInSpace_eval : ∃ t, ComputableTidilyInBigO
    (fun I : Instance => List.ofFn I.tree.eval) encInstance encBits t
    fun I => spaceBound I.ell I.height + (encNat ((encInstance I).length + 1)).length := by
  obtain ⟨T, hT⟩ := tidy_machine
  have hc (I : Instance) :
      machine.toStepMachine.Computes (encInstance I) (List.ofFn I.tree.eval) := by
    obtain ⟨n, s, hrun, hhalt⟩ := exists_run_eq I.tree
    have := ReadMachine.computes_toStepMachine (m := machine) (x := I.tree.encode) (n := n)
      (by rw [hrun]; exact hhalt)
    rwa [hrun] at this
  choose rounds hr ho using hc
  let tS := ReadMachine.stateT encState T stateBudget
  let tMax (I : Instance) : ℕ := ∑ i ∈ Finset.range (rounds I + 1),
    tS (machine.toStepMachine.run (encInstance I) i).state
  refine ⟨_, (hT.computableTidilyInTimeAndSpace (fun I : Instance => List.ofFn I.tree.eval)
    rounds hr (fun I => by rw [encBits_apply, ho]) (tMax := tMax)
    (sMax := fun I => 5 * 2 ^ 12 * spaceBound I.ell I.height +
      2 * (encNat ((encInstance I).length + 1)).length + 6) fun I i hi => ⟨?_, ?_⟩).weaken
    (.refl _) (.of_le_linear (5 * 2 ^ 12 + 2) 6 fun I => by omega)⟩
  · exact Finset.single_le_sum (f := fun i => tS (machine.toStepMachine.run
    (encInstance I) i).state)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  · obtain ⟨j, hq, hpos⟩ := ReadMachine.exists_state_run (m := machine) (encInstance I) i
    rw [hq]
    have hb : stateBudget (machine.run
    (encInstance I) j).state ≤ 2 ^ 12 * spaceBound I.ell I.height :=
      stateBudget_le (bounds_of_inv (inv_run (T := I.tree) j))
    have hs : (encState (machine.run (encInstance I) j).state).length ≤
        stateBudget (machine.run (encInstance I) j).state := by
      simp only [stateBudget, stepBudget, encStepInT, length_encPair, encState_apply]; omega
    have hp := ComputableTidilyInO.length_encNat_mono hpos
    simp only [ReadMachine.stateS, length_encPair]
    change _ + 2 * (2 * (encState (machine.run (encInstance I) j).state).length + 1 + _) + 4 ≤ _
    omega

end Cslib.TreeEval
