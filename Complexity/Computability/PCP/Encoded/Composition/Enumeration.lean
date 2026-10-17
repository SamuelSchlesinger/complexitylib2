/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Composition
public import Mathlib.Data.FinEnum

/-!
# Complete enumeration for executable composition

Constructive finite enumerations supply the assignment tester's slot numbering, coins, and
queries. The alphabet is fixed; the graph remains runtime input. Composition preserves the
existing exact interpretation and charges all intermediate and output constraint tables.
The fixed enumerations and tables can be enormous; the certificate is asymptotic in graph size,
not a claim of practical runtime at arbitrary fixed alphabets.

## Main definitions

* `Cslib.PCP.HadamardTester.Rand.finEnum`, `Cslib.PCP.Encoded.Graph.ComposeSlot.finEnum`:
  reusable constructive coin enumeration and slot numbering.
* `Cslib.PCP.Encoded.Graph.composeEnumerated`: tabulated composition with complete enumerations.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_composeEnumerated`: uniform construction from any fixed
  encoding of the input constraint tables.
* `Cslib.PCP.Encoded.Graph.unsatVal_composeEnumerated_eq`: exact mathematical composition value.
* `Cslib.PCP.Encoded.Graph.satisfiable_composeEnumerated_iff`: preservation of satisfiability.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_composeEnumerated`: retention of a `1/476` fraction of value.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP

open Turing.MultiTapeTM ComputableTidilyInPolyTime Cslib.PCP.HadamardTester

/-- Concrete bit enumeration, registered locally while constructing the tester's coins. -/
local instance HadamardTester.instFinEnumBool : FinEnum Bool :=
  FinEnum.ofList [false, true] (by decide)

/-- Constructively enumerate the tester's coins. Batching the repeated factors keeps the nested
product within instance-synthesis limits. -/
@[instance_reducible]
def HadamardTester.Rand.finEnum (α : Type) [FinEnum α] : FinEnum (Rand α) :=
  let linear : FinEnum (LinPos α) := inferInstance
  let quadratic : FinEnum (QuadPos α) := inferInstance
  let equations : FinEnum (EqnRand α) := inferInstance
  letI := linear
  letI := quadratic
  letI := equations
  inferInstanceAs (FinEnum (_ × _ × _ × _ × _))

attribute [local instance] HadamardTester.Rand.finEnum

namespace Encoded.Graph

/-- Constructively number the input, proof, and coin slots of one assignment-tester block. -/
@[instance_reducible]
def ComposeSlot.finEnum (α : Type) [FinEnum α] : FinEnum (ComposeSlot α) :=
  inferInstanceAs (FinEnum (_ ⊕ (_ ⊕ _) ⊕ _))

attribute [local instance] ComposeSlot.finEnum

variable {α : Type} [FinEnum α]

/-- Apply every assignment-tester coin and query, then tabulate the output constraints. -/
def composeEnumerated (g : Graph (α → α → Bool)) :
    Graph ((Bool × (Query → Bool)) → (Bool × (Query → Bool)) → Bool) :=
  g.composeTabulated FinEnum.equiv (FinEnum.toList (Rand α)) (FinEnum.toList Query)

/-- Compose a certified runtime graph, charging a conversion from its fixed constraint encoding
and every output table. The input need not use the implementation's finite enumeration. -/
@[fun_prop]
theorem isPolyTime_composeEnumerated {Input : Type} {input : Input ↪ List Bool}
    {constraintEncoding : (α → α → Bool) ↪ List Bool}
    {graph : Input → Graph (α → α → Bool)}
    (hgraph : ComputableTidilyInPolyTime graph input (encoding constraintEncoding)) :
    ComputableTidilyInPolyTime (fun x => (graph x).composeEnumerated)
      input (encoding (encPi (encPi encBool))) := by
  have hconvert : ComputableTidilyInPolyTime (id : (α → α → Bool) → _)
      constraintEncoding (encPi (encPi encBool)) := .of_finite _
  simpa only [composeEnumerated, mapConstraints_id] using
    isPolyTime_composeTabulated (isPolyTime_mapConstraints hgraph hconvert)
      FinEnum.equiv (FinEnum.toList (Rand α)) (FinEnum.toList Query)

/-- The declared vertex count includes the complete input, proof, and coin slots. -/
@[simp]
theorem vertices_composeEnumerated (g : Graph (α → α → Bool)) :
    g.composeEnumerated.vertices =
      (g.vertices + g.edges.length) * Fintype.card (ComposeSlot α) := by
  simp only [composeEnumerated, composeTabulated, vertices_mapConstraints, vertices_compose,
    FinEnum.card_eq_fintypeCard]

/-- Each original edge contributes one edge per coin and query pair. -/
@[simp]
theorem length_edges_composeEnumerated (g : Graph (α → α → Bool)) :
    g.composeEnumerated.edges.length =
      g.edges.length * Fintype.card (Rand α) * Fintype.card Query := by
  simp only [composeEnumerated, composeTabulated, length_edges_mapConstraints, length_edges_compose,
    FinEnum.toList, List.length_map, List.length_finRange, FinEnum.card_eq_fintypeCard]

/-- Valid input endpoints give valid endpoints in the completely enumerated gadget graph. -/
theorem WellFormed.composeEnumerated {g : Graph (α → α → Bool)} (hg : g.WellFormed) :
    g.composeEnumerated.WellFormed :=
  (wellFormed_mapConstraints_iff _ _).mpr
    (hg.compose FinEnum.equiv (FinEnum.toList (Rand α)) (FinEnum.toList Query))

/-- Complete constructive enumeration preserves the exact mathematical composition value. -/
theorem unsatVal_composeEnumerated_eq (g : Graph (α → α → Bool)) :
    (g.composeEnumerated.toGraph id).unsatVal = (g.toGraph id).compose.unsatVal :=
  unsatVal_composeTabulated_eq FinEnum.equiv (FinEnum.toList (Rand α)) (FinEnum.toList Query) g
    FinEnum.nodup_toList FinEnum.nodup_toList FinEnum.mem_toList FinEnum.mem_toList

/-- Complete tabulated composition preserves satisfiability. -/
theorem satisfiable_composeEnumerated_iff [Nonempty α] (g : Graph (α → α → Bool)) :
    (g.composeEnumerated.toGraph id).Satisfiable ↔ (g.toGraph id).Satisfiable :=
  satisfiable_composeTabulated_iff FinEnum.equiv (FinEnum.toList (Rand α)) (FinEnum.toList Query) g
    FinEnum.nodup_toList FinEnum.nodup_toList FinEnum.mem_toList FinEnum.mem_toList

/-- Complete tabulated composition retains the tester's `1/476` fraction of the input value. -/
theorem le_unsatVal_composeEnumerated [Nonempty α] (g : Graph (α → α → Bool)) :
    (g.toGraph id).unsatVal / 476 ≤ (g.composeEnumerated.toGraph id).unsatVal := by
  rw [unsatVal_composeEnumerated_eq]
  exact ConstraintGraph.le_unsatVal_compose _

end Encoded.Graph

end Cslib.PCP
