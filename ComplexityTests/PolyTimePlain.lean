/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.P
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Tactic.PolyTime
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-! Tidy polynomial time, `P` and `NP` against upstream plain machines, in both directions: upstream
machines with no tidiness or space guarantees give library certificates, and library certificates,
including the verifier for SAT, give upstream machines within polynomial time and space. -/

namespace ComplexityTests.PolyTimePlain

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### From upstream machines to the library -/

/-- Upstream's copy machine, which is not tidy, certifies tidy polynomial time for the identity. -/
example : ComputableTidilyInPolyTime (id : List Bool → List Bool) encBits encBits :=
  ComputableInTimeAndSpace.computableTidilyInPolyTime (t := fun n => n + 1) (by fun_prop)
    computableInTimeAndSpace_id

/-- The words equal to `[true]`, a problem on an infinite type. -/
private def single : Set (List Bool) := {[true]}

/-- Upstream's almost-constant machine decides `single` in constant time and zero space. -/
private theorem exists_decidableInTimeAndSpace_single :
    ∃ c, DecidableInTimeAndSpace single encBits (fun _ => c) (fun _ => 0) :=
  computableInTimeAndSpace_of_exists_finite_ne ⟨false, by
    convert Set.finite_singleton [true] using 1
    ext w
    by_cases hw : w ∈ single <;> simp_all [indicator, single]⟩

/-- A polynomial time bound alone suffices: the space bound may be exponential. -/
example : single ∈ P encBits := by
  obtain ⟨c, h⟩ := exists_decidableInTimeAndSpace_single
  exact mem_P_of_decidableInTimeAndSpace (t := fun _ => c) (s := fun w => 2 ^ w.length)
    (by fun_prop) (h.mono (fun _ => le_rfl) (fun _ => Nat.zero_le _))

/-- The polynomially bounded form of `P` accepts the same upstream decider. -/
example : single ∈ P encBits := by
  obtain ⟨c, h⟩ := exists_decidableInTimeAndSpace_single
  exact mem_P_iff_exists_decidableInTimeAndSpace.mpr
    ⟨fun _ => c, fun _ => 0, by fun_prop, by fun_prop, h⟩

/-! ### From the library to upstream machines -/

/-- Words whose first bit is set. -/
private def firstBit : Set (List Bool) := {w | w.headD false = true}

private theorem firstBit_mem_P : firstBit ∈ P encBits :=
  ⟨fun w => w.headD false, by polytime, fun _ => Iff.rfl⟩

/-- A `polytime` certificate gives an upstream decider within polynomial time and space. -/
example : ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
    DecidableInTimeAndSpace firstBit encBits (fun w => t w.length) (fun w => s w.length) :=
  mem_P_iff_exists_decidableInTimeAndSpace.mp firstBit_mem_P

/-- A list program certified by `polytime` is computed by an upstream machine within polynomially
bounded time and space. -/
example : ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
    ComputableInTimeAndSpaceOfLength
      (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
      encBits encBits t s :=
  ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength (by polytime)

/-- The SAT verifier is computed by an upstream machine within polynomially bounded time and
space in the length of the encoded formula and assignment. -/
example : ∃ (p : Polynomial ℕ) (V : Logic.PL.CNF ℕ × List Bool → Bool) (t s : ℕ → ℕ),
    PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      ComputableInTimeAndSpaceOfLength V (encPair encCNF encBits) encBool t s ∧
        IsVerifier encCNF p V SAT :=
  mem_NP_iff_exists_computableInTimeAndSpaceOfLength.mp SAT.mem_NP

/-! ### Time bounds space -/

/-- Upstream's copy machine needs no separate space bound beyond a linear function of its time. -/
example : ∃ c, ComputableInTimeAndSpace (id : List Bool → List Bool) encBits encBits
    (fun w => w.length + 1) (fun w => c * (w.length + 1) + c) :=
  computableInTimeAndSpace_id.exists_space_linear

/-! ### Axioms -/

/--
info: 'Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInPolyTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInTimeAndSpace.computableTidilyInPolyTime

/--
info: 'Turing.MultiTapeTM.decidableInTimeAndSpace_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decidableInTimeAndSpace_iff

/--
info: 'Cslib.Complexity.mem_P_iff_exists_decidableInTimeAndSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_P_iff_exists_decidableInTimeAndSpace

/--
info: 'Cslib.Complexity.mem_P_of_decidableInTimeAndSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_P_of_decidableInTimeAndSpace

/--
info: 'Cslib.Complexity.mem_NP_iff_exists_computableInTimeAndSpaceOfLength' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_NP_iff_exists_computableInTimeAndSpaceOfLength

end ComplexityTests.PolyTimePlain
