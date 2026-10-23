/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Polynomial-time operations on layered Boolean circuits

Node tags and binary wire indices are read from their actual encoding. Lookups use the binary
index calculus, which bounds an index before converting it to unary. Invalid references retain
the specified fallback without running for time proportional to the numerical index.

## Main results

* `Cslib.Circuits.Boolean.Layered.computableTidilyInPolyTime_nodeCode`: read a node's code.
* `Cslib.Circuits.Boolean.Layered.computableTidilyInPolyTime_nodeConst`,
  `computableTidilyInPolyTime_nodeCopy`, `computableTidilyInPolyTime_nodeNand`: construct nodes.
* `Cslib.Circuits.Boolean.Layered.computableTidilyInPolyTime_nodeEval`: evaluate one node.
* `Cslib.Circuits.Boolean.Layered.computableTidilyInPolyTime_evalLayer`: evaluate one layer.
* `Cslib.Circuits.Boolean.Layered.computableTidilyInPolyTime_select`: select ordered outputs.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

open Turing.MultiTapeTM

/-- Read the two tag bits and two binary wire indices without changing the encoding. -/
@[fun_prop]
theorem computableTidilyInPolyTime_nodeCode :
    ComputableTidilyInPolyTime Node.code encNode
      (encPair (encPair encBool encBool) (encPair encNat encNat)) :=
  .of_eq fun _ => rfl

/-- Construct a constant node. -/
@[fun_prop]
theorem computableTidilyInPolyTime_nodeConst :
    ComputableTidilyInPolyTime Node.const encBool encNode :=
  .of_finite _

/-- Construct a copy node, preserving the binary wire index. -/
@[fun_prop]
theorem computableTidilyInPolyTime_nodeCopy :
    ComputableTidilyInPolyTime Node.copy encNat encNode := by
  have h : ComputableTidilyInPolyTime (fun i : ℕ => ((true, false), i, 0)) encNat
      (encPair (encPair encBool encBool) (encPair encNat encNat)) := by fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Construct a NAND node, preserving both binary wire indices. -/
@[fun_prop]
theorem computableTidilyInPolyTime_nodeNand :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => Node.nand p.1 p.2)
      (encPair encNat encNat) encNode := by
  have h : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => ((true, true), p))
      (encPair encNat encNat) (encPair (encPair encBool encBool) (encPair encNat encNat)) := by
    fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Node evaluation is polynomial in the encoded input, including invalid binary wire indices. -/
@[fun_prop]
theorem computableTidilyInPolyTime_nodeEval {α : Type} {input : α ↪ List Bool}
    {node : α → Node} {inputs : α → List Bool}
    (hnode : ComputableTidilyInPolyTime node input encNode)
    (hinputs : ComputableTidilyInPolyTime inputs input encBits) :
    ComputableTidilyInPolyTime (fun a => (node a).eval (inputs a)) input encBool := by
  have hcode := computableTidilyInPolyTime_nodeCode.comp hnode
  have hfirst : ComputableTidilyInPolyTime
      (fun a => (inputs a).getD (node a).code.2.1 false) input encBool :=
    ComputableTidilyInPolyTime.listGetD_binary (encA := encBool) false hinputs (by fun_prop)
  have hsecond : ComputableTidilyInPolyTime
      (fun a => (inputs a).getD (node a).code.2.2 false) input encBool :=
    ComputableTidilyInPolyTime.listGetD_binary (encA := encBool) false hinputs (by fun_prop)
  have h : ComputableTidilyInPolyTime (fun a =>
      if (node a).code.1.1 then
        if (node a).code.1.2 then
          !((inputs a).getD (node a).code.2.1 false &&
            (inputs a).getD (node a).code.2.2 false)
        else (inputs a).getD (node a).code.2.1 false
      else (node a).code.1.2) input encBool :=
    hcode.fst'.fst'.cond
      (hcode.fst'.snd'.cond
        (ComputableTidilyInPolyTime.bool_not.comp
          (ComputableTidilyInPolyTime.bool_and.comp (hfirst.prod hsecond))) hfirst)
      hcode.fst'.snd'
  convert h using 1
  funext a
  cases node a <;> rfl

/-- Evaluate a computed layer, preserving the raw bit-string output encoding. -/
@[fun_prop]
theorem computableTidilyInPolyTime_evalLayer {α : Type} {input : α ↪ List Bool}
    {layer : α → List Node} {inputs : α → List Bool}
    (hlayer : ComputableTidilyInPolyTime layer input (encList encNode))
    (hinputs : ComputableTidilyInPolyTime inputs input encBits) :
    ComputableTidilyInPolyTime (fun a => evalLayer (inputs a) (layer a)) input encBits := by
  apply ComputableTidilyInPolyTime.listToBits.comp
  apply ComputableTidilyInPolyTime.mapWithInput hlayer
  apply computableTidilyInPolyTime_nodeEval <;> fun_prop

/-- Free output selection is polynomial even for malformed binary indices. -/
@[fun_prop]
theorem computableTidilyInPolyTime_select {α : Type} {input : α ↪ List Bool}
    {inputs : α → List Bool} {outputs : α → List ℕ}
    (hinputs : ComputableTidilyInPolyTime inputs input encBits)
    (houtputs : ComputableTidilyInPolyTime outputs input (encList encNat)) :
    ComputableTidilyInPolyTime (fun a => select (inputs a) (outputs a)) input encBits := by
  apply ComputableTidilyInPolyTime.listToBits.comp
  apply ComputableTidilyInPolyTime.mapWithInput houtputs
  exact ComputableTidilyInPolyTime.listGetD_binary false (by fun_prop) (by fun_prop)

end Cslib.Circuits.Boolean.Layered
