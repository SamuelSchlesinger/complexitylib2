/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.CookLevin.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# Encodings for constructing the Cook–Levin tableau

Intermediate features and variables are encoded by their existing indices in unary. The indices
use a fixed nesting depth of the polynomial pairing function, so constructing features from unary
times and positions has polynomial cost. States, tape numbers and symbols are fixed parameters.
The final variable numbering converts the same indices to the binary encoding used by SAT.

These certificates concern construction and numbering. They do not provide a polynomial-time
decoder or certify pattern matching on an arbitrary encoded feature.

## Main definitions

* `Cslib.Complexity.CookLevin.encFeature`, `Cslib.Complexity.CookLevin.encVar`.

## Main results

* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_inPos`,
  `.computableTidilyInPolyTime_head`, `.computableTidilyInPolyTime_cell`: varying positions.
* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_holds`,
  `.computableTidilyInPolyTime_cert`: tableau variable constructors.
* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_index`: the existing variable numbering
  with binary output.
* `Cslib.Complexity.CookLevin.computableTidilyInPolyTime_relabel`: number all variables in a
  constructed tableau, producing the SAT encoding.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {k : ℕ} {State : Type} [Fintype State]

/-- A feature is represented by its existing index in unary. -/
noncomputable def encFeature : Feature k State ↪ List Bool :=
  ⟨fun φ => encUnary (featureIndex φ), encUnary.injective.comp featureIndex_injective⟩

/-- A tableau variable is represented by its existing index in unary. -/
noncomputable def encVar : Var k State ↪ List Bool :=
  ⟨fun v => encUnary v.index, encUnary.injective.comp Var.index_injective⟩

/-- The unary feature index is already the encoded word. -/
@[fun_prop]
theorem computableTidilyInPolyTime_featureIndex :
    ComputableTidilyInPolyTime (featureIndex (k := k) (State := State)) encFeature encUnary :=
  of_eq fun _ => rfl

/-- Construct an input-head feature from a unary position. -/
@[fun_prop]
theorem computableTidilyInPolyTime_inPos :
    ComputableTidilyInPolyTime (Feature.inPos (k := k) (State := State)) encUnary encFeature :=
  (unary_pair.comp ((const 1).prod id')).of_enc_eq fun _ => rfl

/-- Construct a work-head feature on a fixed tape from a signed unary position. -/
@[fun_prop]
theorem computableTidilyInPolyTime_head (i : Fin k) :
    ComputableTidilyInPolyTime (Feature.head (State := State) i) encInt encFeature := by
  have h : ComputableTidilyInPolyTime (fun z => Nat.pair 2 (Nat.pair i (Equiv.intEquivNat z)))
      encInt encUnary := by fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Construct a cell feature for a fixed tape and symbol from a signed unary position. -/
@[fun_prop]
theorem computableTidilyInPolyTime_cell (i : Fin k) (s : Option Bool) :
    ComputableTidilyInPolyTime (fun z => Feature.cell (State := State) i z s)
      encInt encFeature := by
  have h : ComputableTidilyInPolyTime
      (fun z => Nat.pair 3 (Nat.pair i (Nat.pair (Equiv.intEquivNat z) (Encodable.encode s))))
      encInt encUnary := by fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Attach a unary time to an encoded feature. -/
@[fun_prop]
theorem computableTidilyInPolyTime_holds :
    ComputableTidilyInPolyTime (fun p : ℕ × Feature k State => Var.holds p.1 p.2)
      (encPair encUnary encFeature) encVar := by
  have h : ComputableTidilyInPolyTime
      (fun p : ℕ × Feature k State => Nat.pair 0 (Nat.pair p.1 (featureIndex p.2)))
      (encPair encUnary encFeature) encUnary := by fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Construct a certificate variable from its unary index. -/
@[fun_prop]
theorem computableTidilyInPolyTime_cert :
    ComputableTidilyInPolyTime (Var.cert (k := k) (State := State)) encUnary encVar :=
  (unary_pair.comp ((const 1).prod id')).of_enc_eq fun _ => rfl

/-- Emit the existing variable index in binary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_index :
    ComputableTidilyInPolyTime (Var.index (k := k) (State := State)) encVar encNat :=
  unary_to_binary.comp (of_eq (encMid := encUnary) fun _ => rfl)

/-- Convert a constructed tableau to the SAT encoding using its existing variable numbering. -/
@[fun_prop]
theorem computableTidilyInPolyTime_relabel :
    ComputableTidilyInPolyTime (Cslib.Logic.PL.CNF.relabel (Var.index (k := k) (State := State)))
      (encList (encList (encPair encVar encBool))) encCNF :=
  Cslib.Logic.PL.CNF.computableTidilyInPolyTime_relabel computableTidilyInPolyTime_index

end Cslib.Complexity.CookLevin
