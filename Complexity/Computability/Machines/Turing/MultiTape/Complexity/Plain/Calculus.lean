/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, lean-canny contributors
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain.Calculus
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Walk
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Arith
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BinaryCompare
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Translate
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit

/-!
# Plain resource-bounded computation rules

These ordinary declarations preserve the encodings, captured parameters and quantitative premises
of the construction certificates used in their proofs. Public clients use the plain statements.

The existing construction exports and registrations are retired during the coordinated #456
client migration; this source package does not add an internal-layer exemption.
-/

public section

open _root_.Turing.MultiTapeTM


namespace Turing.MultiTapeTM.ComputableInO

/-- **The lifted step is computable**, within the bounds of the inner step on the emitted
event, if any, plus the length of its input. -/
theorem lift
    {Q E σ : Type}
    [inst_1 : Finite Q]
    [inst_2 : Inhabited E]
    {encQ : Q ↪ List Bool}
    {encE : E ↪ List Bool}
    {encS : σ ↪ List Bool}
    {next : σ × E → σ}
    {T S : σ × E → ℕ}
    (tr : Translator Q E)
    (h : ComputableInO next (encPair encS encE) encS T S) :
    ComputableInO (tr.lift next)
      (encPair (encPair encQ encS)
        encBool)
      (encPair encQ encS)
      (fun (p : (Q × σ) × Bool) =>
        ((encPair (encPair encQ encS)
                  encBool :
                (Q × σ) × Bool → List Bool)
              p).length +
          (tr.step p.1.1 p.2).2.elim 0 fun (e : E) => T (p.1.2, e))
      fun (p : (Q × σ) × Bool) =>
      ((encPair (encPair encQ encS)
                encBool :
              (Q × σ) × Bool → List Bool)
            p).length +
        (tr.step p.1.1 p.2).2.elim 0 fun (e : E) => S (p.1.2, e) := by
  simp only [computableInO_iff_computableTidilyInO] at *
  exact @ComputableTidilyInO.lift Q E σ inst_1 inst_2 encQ encE encS next T S tr h

end Turing.MultiTapeTM.ComputableInO



namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- A fixed-length stopped walk uses the joint certificate for its runtime graph and retains
all unused labels and signals. The length and signal alphabet are fixed parameters. -/
@[fun_prop]
theorem rotationMap_killedPowRotWithInput {P V D : Type} {input : P ↪ List Bool}
    {vertex : V ↪ List Bool} {label : D ↪ List Bool} {rotate : P × (V × D) → V × D}
    (hrotate : ComputableInPolyTime rotate
      (encPair input (encPair vertex label)) (encPair vertex label))
    (T q : ℕ) [NeZero q] (signal : Fin q ↪ List Bool) :
    ComputableInPolyTime (Cslib.RotationMap.killedPowRotWithInput rotate T q)
      (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
      (encPair vertex (encPair (encPi label) (encPi signal))) := by
  simp only [computableInPolyTime_iff_computableTidilyInPolyTime] at *
  exact ComputableTidilyInPolyTime.rotationMap_killedPowRotWithInput hrotate T q signal

end Turing.MultiTapeTM.ComputableInPolyTime
