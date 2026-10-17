/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Foundations.Combinatorics.Expander.Walk.WithInput
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Certificates for fixed-length graph walks

The graph is selected by a runtime input, and a rotation certificate charges this input together
with the vertex and label. A fixed number of calls therefore has polynomial cost, including all
intermediate vertices and the complete returned label sequence. The walk length and killing rate
are fixed parameters; these results do not claim a bound uniform in either parameter.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_walkAtWithInput`:
  a vertex along a fixed walk.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_powRotWithInput`:
  a fixed power rotation.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_killedPowRotWithInput`:
  a fixed killed power.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [J. Radhakrishnan, *Gap amplification in PCPs using lazy random walks*][Radhakrishnan2006]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

open Cslib

variable {P V D : Type} {input : P ↪ List Bool} {vertex : V ↪ List Bool}
  {label : D ↪ List Bool} {rotate : P × (V × D) → V × D}
  (hrotate : ComputableTidilyInPolyTime rotate
    (encPair input (encPair vertex label)) (encPair vertex label))

include hrotate in
/-- A fixed step of a fixed-length walk uses the joint certificate for the runtime graph. -/
@[fun_prop]
theorem rotationMap_walkAtWithInput (T m : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : P × (V × (Fin T → D)) => RotationMap.walkAtWithInput rotate p m)
      (encPair input (encPair vertex (encPi label))) vertex := by
  induction m with
  | zero => exact (snd _ _).fst'
  | succ m ih =>
    by_cases hm : m < T
    · simp only [RotationMap.walkAtWithInput, dite_eq_left hm]
      exact (hrotate.comp ((fst _ _).prod (ih.prod ((pi_apply label ⟨m, hm⟩).comp
        ((snd _ _).snd'))))).fst'
    · simpa only [RotationMap.walkAtWithInput, dite_eq_right hm] using ih

private theorem polytime_finTail (T : ℕ) :
    ComputableTidilyInPolyTime (@Fin.tail T (fun _ => D)) (encPi label) (encPi label) :=
  pi fun i => pi_apply label i.succ

private theorem polytime_finSnoc (T : ℕ) :
    ComputableTidilyInPolyTime (fun p : (Fin T → D) × D => Fin.snoc p.1 p.2)
      (encPair (encPi label) label) (encPi label) := by
  apply pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using snd (encPi label) label
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (pi_apply label j).comp (fst (encPi label) label)

include hrotate in
/-- A fixed power reverses all return labels while charging the runtime graph at every call. -/
@[fun_prop]
theorem rotationMap_powRotWithInput (T : ℕ) :
    ComputableTidilyInPolyTime (RotationMap.powRotWithInput rotate T)
      (encPair input (encPair vertex (encPi label))) (encPair vertex (encPi label)) := by
  induction T with
  | zero => exact snd _ _
  | succ T ih =>
    have hhead : ComputableTidilyInPolyTime
        (fun p : P × (V × (Fin (T + 1) → D)) => rotate (p.1, p.2.1, p.2.2 0))
        (encPair input (encPair vertex (encPi label))) (encPair vertex label) :=
      hrotate.comp ((fst _ _).prod
        (((snd _ _).fst').prod ((pi_apply label 0).comp ((snd _ _).snd'))))
    have hrest := ih.comp ((fst _ _).prod (hhead.fst'.prod
      ((polytime_finTail (label := label) T).comp ((snd _ _).snd'))))
    exact hrest.fst'.prod ((polytime_finSnoc (label := label) T).comp (hrest.snd'.prod hhead.snd'))

include hrotate in
/-- A killed power branches on the fixed finite signal sequence, computes the actual stopped
walk, and retains every unused label and every signal in the result. -/
@[fun_prop]
theorem rotationMap_killedPowRotWithInput (T q : ℕ) [NeZero q] (signal : Fin q ↪ List Bool) :
    ComputableTidilyInPolyTime
      (RotationMap.killedPowRotWithInput rotate T q)
      (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
      (encPair vertex (encPair (encPi label) (encPi signal))) := by
  have hbranch (c : Fin T → Fin q) : ComputableTidilyInPolyTime
      (fun p : P × (V × ((Fin T → D) × (Fin T → Fin q))) =>
        RotationMap.killedPowRotWithInput rotate T q (p.1, p.2.1, p.2.2.1, c))
      (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
      (encPair vertex (encPair (encPi label) (encPi signal))) := by
    have hprefix : ComputableTidilyInPolyTime
        (fun k : Fin T → D => Fin.take _ (RotationMap.killTime_le c) k)
        (encPi label) (encPi label) :=
      pi fun i : Fin (RotationMap.killTime c) =>
        pi_apply label (⟨i.val, i.isLt.trans_le (RotationMap.killTime_le c)⟩ : Fin T)
    have hwalk : ComputableTidilyInPolyTime
        (fun p : P × (V × ((Fin T → D) × (Fin T → Fin q))) =>
          RotationMap.powRotWithInput rotate (RotationMap.killTime c)
            (p.1, p.2.1, Fin.take _ (RotationMap.killTime_le c) p.2.2.1))
        (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
        (encPair vertex (encPi label)) :=
      (rotationMap_powRotWithInput hrotate (RotationMap.killTime c)).comp
        ((fst _ _).prod (((snd _ _).fst').prod (hprefix.comp ((snd _ _).snd'.fst'))))
    dsimp only [RotationMap.killedPowRotWithInput]
    apply hwalk.fst'.prod
    apply prod ?_ (const c)
    apply pi
    intro i
    by_cases hi : i.val < RotationMap.killTime c
    · simpa only [dite_eq_left hi, Function.comp_def] using
        (pi_apply label ⟨i.val, hi⟩).comp hwalk.snd'
    · simpa only [dite_eq_right hi, Function.comp_def] using
        (pi_apply label i).comp ((snd input _).snd'.fst')
  exact ((snd input (encPair vertex (encPair (encPi label) (encPi signal)))).snd'.snd').finite_cases
    hbranch

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
