/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Synthesis
import Cslib.Computability.Circuit.Composition

/-!
# Applying circuits to available functions

An existing circuit can be inserted into a synthesis construction by wiring its inputs to
available functions. Its outputs then become available at a cost of its number of gates, while
all previously computed functions remain available. Repeated inputs share their original wires.

## Main results

* `Cslib.Circuits.Synthesis.circuit`: applying a circuit costs its number of gates.

## References

* Adapted from `MassProduction/Nonuniform/FlagSelection.lean` in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits

universe v u

variable {σ : Signature.{v}} {U : Type u} {I : Interpretation σ U} {n : ℕ}

/-- A circuit whose inputs are fed by available functions computes its outputs with as many
additional gates as it has. The functions feeding the inputs may repeat. -/
theorem Synthesis.circuit {s : Set ((Fin n → U) → U)} {m p : ℕ} (c : Circuit σ m p)
    (g : Fin m → (Fin n → U) → U) (hg : ∀ i, g i ∈ s) :
    Synthesis I s (Set.range fun j x => c.eval I (fun i => g i x) j) c.size := by
  intro g₁ p₁ hp
  choose wires hw using fun i => mem_available.mp (hp (hg i))
  refine ⟨g₁ + c.size, p₁.append wires c.program, le_rfl, ?_, ?_⟩
  · intro f hf
    obtain ⟨w, hw'⟩ := mem_available.mp hf
    exact mem_available.mpr ⟨w.castAdd c.size, fun x =>
      (Program.trace_append_castAdd p₁ wires I x c.program w).trans (hw' x)⟩
  · rintro _ ⟨j, rfl⟩
    refine mem_available.mpr ⟨Program.appendedWire wires (c.outputs j), fun x => ?_⟩
    rw [Program.trace_append_appendedWire]
    have : (fun i => p₁.trace I x (wires i)) = fun i => g i x := funext fun i => hw i x
    rw [this]
    rfl

end Cslib.Circuits
