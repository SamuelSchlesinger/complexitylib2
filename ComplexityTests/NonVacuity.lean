/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.FirstOrder
import Complexity.Computability.Circuit.Boolean.GateElimination
import Complexity.Computability.Circuit.Boolean.Khrapchenko
import Complexity.Computability.Circuit.Boolean.LMN
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Circuit.Boolean.Smolensky
import Complexity.Computability.Circuit.Boolean.TC0
import Complexity.Computability.Circuit.Boolean.TopDown
import Complexity.Computability.Circuit.Monotone.Clique.Asymptotic
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Foundations.BooleanAnalysis.HadamardTester
import Complexity.Probability.ApproximateCounting.Relative
import Complexity.Probability.PairwiseIndependentHash.Toeplitz
import Complexity.Foundations.Combinatorics.Expander.Family
import Complexity.Computability.Kolmogorov.MultiTape
import Complexity.Crypto.Primitives.PRG.NisanWigderson.Design
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-!
# Non-vacuity of the complexity classes

A machine without work tapes that writes a constant answer in one step computes a constant
function in polynomial time, whatever the input encoding. So the empty and the full problem are in
`P`, `NP`, `BPP` and `RP`, and the hypotheses of the theorems about these classes (such as
`Cslib.Circuits.Boolean.PPoly.of_mem_P` and `PPoly.of_mem_BPP`) can be met.

Constant functions will come from the composition machinery upstream; this file only guards
against definitions that are accidentally unsatisfiable.
-/

namespace ComplexityTests.NonVacuity

open Turing Turing.MultiTapeTM Cslib.Complexity Cslib.Circuits.Boolean Finset Cslib

/-- The machine that writes `b` and halts. -/
def constTM (b : Bool) : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, Fin.elim0, some b, none⟩

theorem computesTidily_constTM (b : Bool) (w : List Bool) :
    (constTM b).ComputesTidilyInTimeAndSpace w [b] 1 0 := by
  rw [computesTidily_iff]
  refine ⟨.ofDeterministic (constTM b) (wordsCfg w (some (constTM b).q₀) (fun _ => []) []) 1, rfl,
    ?_, le_rfl, (space_zero_tapes_eq_zero _ _ rfl).le⟩
  rw [last_ofDeterministic, runFrom_one, step_of_state (q := ()) rfl]
  simp only [constTM, tr_ofTr, wordsCfg, Action.apply, moveInputPos_zero]
  congr <;> funext i <;> exact i.elim0

theorem polyTime_const {α : Type} (enc : α ↪ List Bool) (b : Bool) :
    ComputableTidilyInPolyTime (fun _ : α => b) enc encBool :=
  ⟨fun _ => 1, fun _ => 0, ⟨1, 0, fun _ => by simp⟩, ⟨0, 0, fun _ => by simp⟩,
    0, Unit, inferInstance, constTM b, fun a => computesTidily_constTM b (enc a)⟩

example : (∅ : Set (List Bool)) ∈ Cslib.Complexity.P encBits :=
  ⟨fun _ => false, polyTime_const _ false, fun _ => by simp⟩

example : (Set.univ : Set (List Bool)) ∈ Cslib.Complexity.P encBits :=
  ⟨fun _ => true, polyTime_const _ true, fun _ => by simp⟩

example : (∅ : Set (List Bool)) ∈ NP encBits :=
  ⟨0, fun _ => false, polyTime_const _ false, fun _ => by simp⟩

example : (Set.univ : Set (List Bool)) ∈ NP encBits :=
  ⟨0, fun _ => true, polyTime_const _ true, fun _ => by simp⟩

example : (∅ : Set (List Bool)) ∈ BPP encBits :=
  ⟨0, fun _ => false, polyTime_const _ false, fun _ => ⟨fun h => h.elim, fun _ => by
      simp only [Polynomial.eval_zero, pow_zero, mul_one]
      exact le_trans (by norm_num : 2 ≤ 3 * 1)
        (Nat.mul_le_mul_left 3 (Finset.card_pos.2
          ⟨fun _ => false, Finset.mem_filter.2 ⟨Finset.mem_univ _, trivial⟩⟩))⟩⟩

example : (∅ : Set (List Bool)) ∈ RP encBits :=
  ⟨0, fun _ => false, polyTime_const _ false, fun _ => ⟨fun h => h.elim, fun _ _ => rfl⟩⟩

/-- `P ⊆ P/poly` applies to a language in `P`. -/
example : (⊤ : Language Bool) ∈ PPoly :=
  PPoly.of_mem_P ⟨fun _ => true, polyTime_const _ true, fun _ => ⟨fun _ => rfl, fun _ => trivial⟩⟩

/-- `BPP ⊆ P/poly` applies to a language in `BPP`. -/
example : (⊥ : Language Bool) ∈ PPoly :=
  PPoly.of_mem_BPP ⟨0, fun _ => false, polyTime_const _ false,
    fun _ => ⟨fun h => h.elim, fun _ => by
      simp only [Polynomial.eval_zero, pow_zero, mul_one]
      exact le_trans (by norm_num : 2 ≤ 3 * 1)
        (Nat.mul_le_mul_left 3 (Finset.card_pos.2
          ⟨fun _ => false, Finset.mem_filter.2 ⟨Finset.mem_univ _, trivial⟩⟩))⟩⟩

/-- The monotone lower bound for cliques is about a finite complexity. -/
example : Cslib.Circuits.ecomplexity Cslib.Circuits.Monotone.interpretation
    (Cslib.Circuits.single (Cslib.Circuits.clique 16 2)) ≠ ⊤ :=
  Cslib.Circuits.Monotone.ecomplexity_clique_ne_top 16 2

/-- Schnorr's bound applies to the parity of three bits, which has De Morgan circuits. -/
example : 6 ≤ Cslib.Circuits.complexity Cslib.Circuits.Boolean.interpretation
    (Cslib.Circuits.single (Cslib.parity 3)) :=
  Cslib.Circuits.Boolean.three_mul_le_complexity_parity 3

/-- Khrapchenko's bound applies to the parity of four bits, which has a formula of leaf size 16. -/
example : ∃ F : Cslib.Circuits.Formula Cslib.Circuits.Boolean.signature (2 ^ 2),
    F.Computes Cslib.Circuits.Boolean.interpretation (Cslib.parity (2 ^ 2)) ∧
      F.leafSize = 16 :=
  Cslib.Circuits.Boolean.exists_formula_parity_two_pow 2

/-- The constant-depth classes are inhabited, by the constants. -/
example : (⊤ : Language Bool) ∈ AC0 ∧ (⊥ : Language Bool) ∈ AC0 :=
  ⟨ConstDepth.top_mem (Cslib.Circuits.Signature.Hom.id _),
    ConstDepth.bot_mem (Cslib.Circuits.Signature.Hom.id _)⟩

example : (⊤ : Language Bool) ∈ TC0 :=
  ConstDepth.top_mem Unbounded.toExt

example : (⊥ : Language Bool) ∈ AC0Mod 3 :=
  ConstDepth.bot_mem Unbounded.toExt

/-- First-order model checking applies: over the empty language, the atomic facts of a structure
on `Fin n` are enumerated by `Fin 0`. -/
example (φ : FirstOrder.Language.empty.Sentence) (n : ℕ) :
    ∃ e : ModelChecking.Atom FirstOrder.Language.empty n ≃ Fin 0,
      ∃ F : Cslib.Circuits.Formula Unbounded.signature 0,
        (∀ (M : Type) [FirstOrder.Language.empty.Structure M] (eM : M ≃ Fin n),
          F.eval Unbounded.interpretation (ModelChecking.atomsOf eM ∘ e.symm) = true ↔ M ⊨ φ) ∧
        F.depth ≤ ModelChecking.foDepth φ ∧
          F.size ≤ ModelChecking.foSize φ * (n + 2) ^ ModelChecking.foSize φ := by
  have : IsEmpty (ModelChecking.Atom FirstOrder.Language.empty n) := ⟨fun a => a.1.2.elim⟩
  let e := Equiv.equivOfIsEmpty (ModelChecking.Atom FirstOrder.Language.empty n) (Fin 0)
  exact ⟨e, ModelChecking.exists_formula_realize_structure φ e⟩

/-- The hypotheses of the Linial–Mansour–Nisan theorem can be met: for depth one, `s = 2` and
`n = 528`, the restrictions keep `⌊528 / 33⌋ = 16` bits free, and `k = 264` works. -/
example {f : BooleanFunction 528} {C : Cslib.Circuits.Circuit Unbounded.signature 528 1}
    (hC : C.Computes Unbounded.interpretation (Cslib.Circuits.single f)) (hd : C.depth = 1) :
    ∑ U with 264 ≤ #U, BitString.fourierCoeff (fun x => BitString.signVal (f x)) U ^ 2 ≤
      2 * C.size / 2 ^ 2 :=
  Unbounded.sum_fourierCoeff_sq_le_of_computes hC le_rfl (by norm_num) (by rw [hd]; norm_num)

/-- The AND/OR depth of Korten's theorem differs from the depth: a negation of an input has AND/OR
depth zero and depth one. -/
example : (Cslib.Circuits.Circuit.oneGate (σ := Unbounded.signature) (n := 1) .not
      fun _ => 0).depthWith Unbounded.Op.andOrCost = 0 ∧
    (Cslib.Circuits.Circuit.oneGate (σ := Unbounded.signature) (n := 1) .not fun _ => 0).depth =
      1 := by
  decide

/-- The tidy normal form applies to upstream's machine for the identity, which is not tidy: it
leaves its input head at the end of the input. -/
example {α : Type} (enc : α ↪ List Bool) :
    ∃ c, ComputableTidilyInTimeAndSpace (id : α → α) enc enc
      (fun a => 2 * ((enc a).length + 1) + 3 * 0 + c) (fun _ => c * (0 + 1)) :=
  computableInTimeAndSpace_id.exists_computableTidilyInTimeAndSpace

/-- The hypotheses of the soundness of the Hadamard tester can be met: the honest tables for a
solution pass every test with probability one. -/
example {n m : ℕ} (x : Cslib.BitString n) (A : Fin m → Cslib.BitString (n * n))
    (b : Cslib.BitString m)
    (h : ∀ e, BitString.hadamardCode (BitString.tensor x x) (A e) = b e) :
    ∃ x', (hammingDist (BitString.hadamardCode x) (BitString.hadamardCode x') : ℝ) / 2 ^ n ≤ 0 ∧
      ∀ e, BitString.hadamardCode (BitString.tensor x' x') (A e) = b e :=
  BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance
    (g := BitString.hadamardCode (BitString.tensor x x)) (ε := 0) (ε' := 0)
    (by simp) (by simp) (by norm_num)
    (by rw [BitString.equationTestAcceptance_hadamardCode h]; norm_num)

/-- Nisan–Wigderson designs exist for some parameters: two disjoint singletons. -/
example : Cslib.Crypto.PRG.NisanWigderson.Design 2 1 0 2 where
  block := ![{0}, {1}]
  card_block := by decide
  card_inter_le := by decide

/-- Nisan–Wigderson designs with nontrivial parameters exist: a `(36, 3, 1)`-design with 16
blocks. -/
example : Nonempty (Cslib.Crypto.PRG.NisanWigderson.Design 36 3 1 16) :=
  Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_four_mul_sq 3 2

/-- The root recovery of relative-error counting applies: `e = 100 · 3 ^ 7` lies between `3 ^ 7`
and `128 · 3 ^ 7`, and `128 · 1 ^ 7 ≤ 2 ^ 7`, so the integer seventh root of `e` lies between `3`
and `2 · 3`. -/
example : 3 ≤ Nat.nthRoot 7 (100 * 3 ^ 7) ∧ 1 * Nat.nthRoot 7 (100 * 3 ^ 7) ≤ (1 + 1) * 3 :=
  Cslib.Probability.ApproximateCounting.le_nthRoot_and_mul_nthRoot_le (c := 128) (by norm_num)
    (by norm_num) (by norm_num)
    (Cslib.Probability.ApproximateCounting.two_pow_mul_pow_le_add_one_pow 7 one_ne_zero)

section Toeplitz

open Cslib.Probability Matrix Finset

/-- Toeplitz hashing gives a concrete pair of values its pairwise-independent probability. -/
example : dens {p : (Fin (2 + 3 - 1) → ZMod 2) × (Fin 2 → ZMod 2) |
    toeplitzHash p ![1, 0, 0] = 0 ∧ toeplitzHash p ![0, 1, 0] = ![1, 1]} = 1 / 16 := by
  rw [isPairwiseIndependentHash_toeplitzHash.dens_filter_apply_eq_and_apply_eq (by decide)]
  simp [ZMod.card]
  norm_num

/-- The diagonals of a Toeplitz matrix are read along its last column, then its first row. -/
example : toeplitz ![(1 : ℤ), 2, 3, 4] = !![3, 2, 1; 4, 3, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Toeplitz

/-- The lazy graph satisfies the hypothesis of Cheeger's lazy-walk bound. -/
example {V D : Type} [Fintype D] [Nonempty D] (G : Cslib.RotationMap V D) :
    ∀ f v, G.lazy.walk f v = (f v + G.walk f v) / 2 :=
  G.walk_lazy_apply

/-- Constant-degree expanders exist on five vertices. -/
example : ∃ G : Cslib.RotationMap (Fin 5) (Fin 120), G.spectralExpansion < 1 :=
  ⟨Cslib.RotationMap.expander (Fin 5),
    (Cslib.RotationMap.spectralExpansion_expander_le _).trans_lt (by norm_num)⟩

section Kolmogorov

open Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod

/-- Some finite-state multi-tape machine describes every string `x` with `|x|` bits within
`|x| + 1` steps, so the Turing-machine description method is not vacuous. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
    ∀ x : List Bool,
      (ofMultiTapeTM tm).timeBoundedComplexity (x.length + 1) x ≤ x.length := by
  obtain ⟨k, State, hfin, tm, ⟨S⟩⟩ := exists_simulation_literal
  refine ⟨k, State, hfin, tm, fun x => ?_⟩
  simpa [timeBoundedComplexity_literal le_rfl] using S.timeBoundedComplexity_le x.length x

end Kolmogorov

end ComplexityTests.NonVacuity
