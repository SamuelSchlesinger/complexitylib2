/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Boolean.ACC0

/-!
# Tests for `ACC⁰` and Williams's `Sym⁺` / Fast Zeta machinery

Concrete evaluations of `modGate`, `zetaTransform`, `fastZeta`, `SymPlusCircuit.coeffTable`, and
`SymPlusCircuit.fastSymPlusEval`, non-vacuity witnesses for `ACC0` and `SIZEMod`, and
`#print axioms` guards for all headline results in `Complexity.Computability.Circuit.Boolean.ACC0`.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Boolean.ACC0

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-! ### Concrete gate, Zeta-transform, and `Sym⁺` circuit evaluations -/

example : modGate 0 3 ![false, true, false] = true := by decide
example : modGate 0 3 ![false, false, false] = false := by decide
example : modGate 1 3 ![true, true, true] = false := by decide
example : modGate 2 3 ![true, false, true] = false := by decide
example : modGate 2 3 ![true, true, true] = true := by decide
example : modGate 6 4 ![true, true, true, false] = true := by decide

-- Fast Zeta transform agrees with the Boolean-lattice Zeta transform on concrete tables.
example :
    let f : BitString 3 → ℕ := fun p => (p 0).toNat + 2 * (p 1).toNat + 4 * (p 2).toNat
    fastZeta f ![true, false, true] = zetaTransform f ![true, false, true] ∧
      fastZeta f ![true, false, true] = 10 := by
   refine ⟨fastZeta_eq_zetaTransform _ _, ?_⟩
   decide

-- Concrete `Sym⁺` circuit for `MOD_3` on `4 = 2 + 2` bits, evaluated both directly and via
-- Williams's split-variable `fastSymPlusEval`.
example :
    let C : SymPlusCircuit (2 + 2) 4 := SymPlusCircuit.ofModGate 3 4
    let x₁ : BitString 2 := ![true, true]
    let x₂ : BitString 2 := ![true, false]
    C.fastSymPlusEval x₁ x₂ = C.eval (Fin.append x₁ x₂) ∧
      C.fastSymPlusEval x₁ x₂ = false := by
  refine ⟨SymPlusCircuit.fastSymPlusEval_eq_eval _ _ _, ?_⟩
  decide

example :
    let C : SymPlusCircuit (2 + 2) 4 := SymPlusCircuit.ofModGate 3 4
    let x₁ : BitString 2 := ![true, false]
    let x₂ : BitString 2 := ![true, false]
    C.fastSymPlusEval x₁ x₂ = true := by
  decide

-- Non-vacuity of `SIZEMod`: for every modulus `q`, every `c ≥ 1`, and every degree `k`,
-- `Language.ofSlices (modGate q)` belongs to `SIZEMod q (fun n => c * (n + 1) ^ k)`.
theorem modGate_mem_SIZEMod (q : ℕ) {c : ℕ} (hc : 1 ≤ c) (k : ℕ) :
    Language.ofSlices (modGate q) ∈ SIZEMod q fun n => c * (n + 1) ^ k := by
  intro n
  refine ⟨Circuit.oneGate (σ := Unbounded.extSignature) (.gate n) id, ?_, ?_⟩
  · intro x
    funext j
    rw [Language.slice_ofSlices]
    rfl
  · rw [Circuit.size_oneGate]
    exact Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (Nat.succ_ne_zero n)))

/-! ### Concrete class inclusions and strict separations -/

example : AC0Mod 2 ⊆ AC0Mod 6 :=
  AC0Mod_subset_AC0Mod_of_dvd (by decide) ⟨3, rfl⟩

example : AC0Mod 3 ⊆ AC0Mod 6 :=
  AC0Mod_subset_AC0Mod_of_dvd (by decide) ⟨2, rfl⟩

example : AC0 ⊂ AC0Mod 2 := AC0_ssubset_AC0Mod_two
example : AC0 ⊂ ACC0 := AC0_ssubset_ACC0

example : AC0Mod 3 ⊂ ACC0 :=
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  AC0Mod_ssubset_ACC0 (by decide)

example : AC0Mod 5 ⊂ ACC0 :=
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  AC0Mod_ssubset_ACC0 (by decide)

example : Language.ofSlices (modGate 2) ⊓ Language.ofSlices (modGate 3) ∈ ACC0 :=
  ACC0.inf (modGate_mem_ACC0 2) (modGate_mem_ACC0 3)

example : Language.ofSlices (modGate 6) ∈ TC0 :=
  ACC0_subset_TC0 (modGate_mem_ACC0 6)

example : Language.ofSlices (modGate 6) ∈ AC 1 :=
  ACC0_subset_AC_one (modGate_mem_ACC0 6)

example : Language.ofSlices (modGate 6) ∈ NC 2 :=
  ACC0_subset_NC_two (modGate_mem_ACC0 6)

example : Language.ofSlices (modGate 6) ∈ PPoly :=
  ACC0_subset_PPoly (modGate_mem_ACC0 6)

example : ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧
    ∀ c, L ∉ SIZEMod 6 fun n => c * (n + 1) ^ 3 :=
  exists_mem_NEXP_notMem_SIZEMod 6 3

/-! ### Axiom guards -/

/--
info: 'Cslib.Circuits.Boolean.AC0Mod_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AC0Mod_zero

/--
info: 'Cslib.Circuits.Boolean.AC0Mod_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AC0Mod_one

/--
info: 'Cslib.Circuits.Boolean.AC0Mod_subset_AC0Mod_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AC0Mod_subset_AC0Mod_of_dvd

/--
info: 'Cslib.Circuits.Boolean.ACC0_eq_iUnion_AC0Mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ACC0_eq_iUnion_AC0Mod

/--
info: 'Cslib.Circuits.Boolean.AC0_ssubset_ACC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AC0_ssubset_ACC0

/--
info: 'Cslib.Circuits.Boolean.AC0Mod_ssubset_ACC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AC0Mod_ssubset_ACC0

/--
info: 'Cslib.Circuits.Boolean.ACC0.compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ACC0.compl

/--
info: 'Cslib.Circuits.Boolean.ACC0.inf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ACC0.inf

/--
info: 'Cslib.Circuits.Boolean.ACC0.sup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ACC0.sup

/--
info: 'Cslib.Circuits.Boolean.ACC0_subset_TC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ACC0_subset_TC0

/--
info: 'Cslib.Circuits.Boolean.ACMod_subset_AC_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ACMod_subset_AC_succ

/--
info: 'Cslib.Circuits.Boolean.ACC0_subset_AC_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ACC0_subset_AC_one

/--
info: 'Cslib.Circuits.Boolean.ACC0_subset_NC_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ACC0_subset_NC_two

/--
info: 'Cslib.Circuits.Boolean.ACC0_subset_PPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ACC0_subset_PPoly

/--
info: 'Cslib.Circuits.Boolean.fastZeta_eq_zetaTransform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.fastZeta_eq_zetaTransform

/--
info: 'Cslib.Circuits.Boolean.SymPlusCircuit.zetaTransform_coeffTable_eq_activeCount' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SymPlusCircuit.zetaTransform_coeffTable_eq_activeCount

/--
info: 'Cslib.Circuits.Boolean.SymPlusCircuit.fastSymPlusEval_eq_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SymPlusCircuit.fastSymPlusEval_eq_eval

/--
info: 'Cslib.Circuits.Boolean.parity_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.parity_mem_P

/--
info: 'Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_AC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_AC0

/--
info: 'Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_AC0Mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_AC0Mod

/--
info: 'Cslib.Circuits.Boolean.SIZEMod_subset_SIZE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SIZEMod_subset_SIZE

/--
info: 'Cslib.Circuits.Boolean.Kannan.language_notMem_SIZEMod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Kannan.language_notMem_SIZEMod

/--
info: 'Cslib.Circuits.Boolean.exists_mem_SigmaP_two_notMem_SIZEMod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_mem_SigmaP_two_notMem_SIZEMod

/--
info: 'Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_SIZEMod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_SIZEMod

/--
info: 'Cslib.Circuits.Boolean.PH_eq_SigmaP_two_of_NEXP_subset_ACC0' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PH_eq_SigmaP_two_of_NEXP_subset_ACC0

/--
info: 'Cslib.Circuits.Boolean.Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0

end ComplexityTests.Computability.Circuit.Boolean.ACC0
