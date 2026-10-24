/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.NP
import Complexity.Computability.Complexity.Problems.CircuitSAT
import Complexity.Computability.Complexity.Problems.CircuitValue

/-!
# Tests for circuits as data

Concrete codes, decoding boundaries, evaluation, certificates, the circuit value problem, circuit
satisfiability, the circuit of a formula and MCSP, with axiom checks for the headline results.
-/

namespace Cslib.Complexity.Tests.KarpLipton

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-! ### Codes and decoding -/

/-- The circuit `x₀ ∧ ¬x₁` on two inputs. -/
def andNot : Circuit signature 2 1 :=
  ⟨(Program.empty.gate ⟨Op.not, ![Wire.input 1]⟩).gate ⟨Op.and, ![Wire.input 0, Wire.gate 0]⟩,
    fun _ => Wire.gate 1⟩

example : andNot.code = ([(.not, [1]), (.and, [0, 2])], [3]) := by decide

-- Decoding accepts exactly the codes of circuits.
example : (Circuit.ofCode 2 1 andNot.code : Option (Circuit signature 2 1)) = some andNot :=
  Circuit.ofCode_code andNot

-- A gate reading itself, a wire beyond the circuit, the wrong arity, or a missing output
-- is rejected.
example : (Circuit.ofCode 2 1 ([(.not, [2])], [2]) : Option (Circuit signature 2 1)) = none := by
  decide
example : (Circuit.ofCode 2 1 ([(.not, [1])], [3]) : Option (Circuit signature 2 1)) = none := by
  decide
example : (Circuit.ofCode 2 1 ([(.not, [0, 1])], [2]) : Option (Circuit signature 2 1)) = none := by
  decide
example : (Circuit.ofCode 2 1 ([(.not, [1])], []) : Option (Circuit signature 2 1)) = none := by
  decide

example : Program.IsCodeFrom signature 2 0 andNot.code.1 := by decide
example : ¬Program.IsCodeFrom signature 2 0 [(Op.and, [0, 3])] := by decide

-- The encoding writes the number of inputs in unary.
example : (encCircuit 1 ⟨2, andNot⟩).take 5 = [true, true, true, true, false] := by decide

/-! ### Evaluation -/

example : evalCode interpretation false [true, false] andNot.code.1 =
    [true, false, true, true] := by decide

example : andNot.eval interpretation ![true, false] 0 = true := by decide
example : andNot.eval interpretation ![true, true] 0 = false := by decide

-- Missing arguments and wires not yet computed read the default.
example : evalCode interpretation false [true] [(.and, [0]), (.or, [5, 0])] =
    [true, false, true] := by decide
example : evalCode interpretation true [false] [(.and, [7, 7])] = [false, true] := by decide

/-! ### Certificates -/

example : readCertificate 2 3 (certificate 2 3 andNot.code.1 3 ++ [true, true]) =
    (andNot.code.1, 3) :=
  readCertificate_certificate_append (by decide) (by decide) (by decide) _

example : (certificate 2 3 andNot.code.1 3).length = certLength 2 3 := by decide

-- Every word reads as at most `s` gates, here none.
example : readCertificate 2 0 [true, true, true] = ([], 2) := by decide

/-! ### The circuit value problem -/

example : (⟨2, andNot, ![true, false]⟩ : Σ n, Circuit signature n 1 × BitString n) ∈
    CircuitValue :=
  mem_CircuitValue.2 (by decide)
example : (⟨2, andNot, ![false, false]⟩ : Σ n, Circuit signature n 1 × BitString n) ∉
    CircuitValue :=
  fun h => absurd (mem_CircuitValue.1 h) (by decide)

/-! ### Circuit satisfiability -/

example : (⟨2, andNot⟩ : Σ n, Circuit signature n 1) ∈ CircuitSAT := ⟨![true, false], by decide⟩

/-- The unsatisfiable circuit `x₀ ∧ ¬x₀`. -/
def contradiction : Circuit signature 1 1 :=
  ⟨(Program.empty.gate ⟨Op.not, ![Wire.input 0]⟩).gate ⟨Op.and, ![Wire.input 0, Wire.gate 0]⟩,
    fun _ => Wire.gate 1⟩

example : (⟨1, contradiction⟩ : Σ n, Circuit signature n 1) ∉ CircuitSAT := by
  rintro ⟨x, hx⟩
  have : ∀ y : BitString 1, contradiction.eval interpretation y 0 = false := by decide
  exact absurd hx (by rw [this x]; decide)

-- A circuit with no inputs is satisfiable exactly when it outputs true.
example : (⟨0, ⟨Program.empty.gate ⟨Op.const true, ![]⟩, fun _ => Wire.gate 0⟩⟩ :
    Σ n, Circuit signature n 1) ∈ CircuitSAT := ⟨![], rfl⟩

/-! ### The circuit of a formula -/

open Cslib.Logic.PL in
/-- `(x₃ ∨ ¬x₇) ∧ x₇`, with arbitrary variable numbers. -/
def φ : CNF ℕ := [[(3, true), (7, false)], [(7, true)]]

example : (SAT.toCircuit φ).1 = 3 := rfl
example : (SAT.circuitGates φ).length = 18 := by decide

-- The inputs are the literal occurrences; `x₇` is read at its first occurrence, input `1`.
example : (SAT.toCircuit φ).2.eval interpretation
    (fun i => [true, true, false].getD i false) 0 = true := by
  rw [SAT.eval_toCircuit]
  decide
example : (SAT.toCircuit φ).2.eval interpretation
    (fun i => [false, true, true].getD i false) 0 = false := by
  rw [SAT.eval_toCircuit]
  decide

-- The empty formula is true and the empty clause false.
example : (SAT.toCircuit []).2.eval interpretation (fun _ => false) 0 = true := by
  rw [SAT.eval_toCircuit]
  rfl
example : (SAT.toCircuit [[]]).2.eval interpretation (fun _ => false) 0 = false := by
  rw [SAT.eval_toCircuit]
  rfl

/-! ### MCSP -/

-- The identity function on one input needs no gate, and the verifier accepts the certificate
-- of the zero-gate circuit at threshold `0`.
example : MCSP.verifier (⟨1, ![false, true], 0⟩, certificate 1 0 [] 0) = true := by decide

-- The zero-gate circuit does not compute negation, and the one-gate circuit does.
example : MCSP.verifier (⟨1, ![true, false], 0⟩, certificate 1 0 [] 0) = false := by decide
example : MCSP.verifier (⟨1, ![true, false], 1⟩, certificate 1 1 [(.not, [0])] 1) = true := by
  decide

-- A certificate that is not a circuit is rejected: the gate reads itself.
example : MCSP.verifier (⟨1, ![true, false], 1⟩, certificate 1 1 [(.not, [1])] 1) = false := by
  decide

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Circuit.ofCode_code' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Circuit.ofCode_code

/--
info: 'Cslib.Circuits.Circuit.code_of_ofCode_eq_some' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Circuit.code_of_ofCode_eq_some

/--
info: 'Cslib.Circuits.Circuit.isSome_ofCode_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Circuit.isSome_ofCode_iff

/--
info: 'Cslib.Circuits.Program.evalCode_code' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Program.evalCode_code

/--
info: 'Cslib.Circuits.Circuit.eval_eq_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Circuit.eval_eq_getD

/--
info: 'Cslib.Circuits.Boolean.computableInPolyTime_evalCode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.computableInPolyTime_evalCode

/--
info: 'Cslib.Circuits.Boolean.computableInPolyTime_evalOutput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.computableInPolyTime_evalOutput

/--
info: 'Cslib.Circuits.Boolean.readCertificate_certificate_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.readCertificate_certificate_append

/--
info: 'Cslib.Circuits.Boolean.computableInPolyTime_readCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.computableInPolyTime_readCertificate

/--
info: 'Cslib.Complexity.CircuitValue.mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CircuitValue.mem_P

/--
info: 'Cslib.Complexity.CircuitSAT.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CircuitSAT.mem_NP

/--
info: 'Cslib.Complexity.SAT.toCircuit_mem_CircuitSAT_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.toCircuit_mem_CircuitSAT_iff

/--
info: 'Cslib.Complexity.SAT.polyTimeReducible_CircuitSAT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.polyTimeReducible_CircuitSAT

/--
info: 'Cslib.Complexity.CircuitSAT_npComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CircuitSAT_npComplete

/--
info: 'Cslib.MCSP.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.MCSP.mem_NP

end Cslib.Complexity.Tests.KarpLipton
