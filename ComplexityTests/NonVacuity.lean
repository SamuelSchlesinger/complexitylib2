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
import Complexity.Foundations.Combinatorics.Expander.TowerBase
import Complexity.Computability.Kolmogorov.ChainRule
import Complexity.Computability.Kolmogorov.MultiTape
import Complexity.Computability.Kolmogorov.NisanWigderson
import Complexity.Computability.RAM.Squaring
import Complexity.Computability.Circuit.Frontier.Reduction
import Complexity.Computability.Circuit.Frontier.Unconditional
import Complexity.Computability.Circuit.Frontier.Linear.Unconditional
import Complexity.Computability.Circuit.Frontier.Ledger.Unconditional
import Complexity.Computability.Circuit.Frontier.Decomposable
import Complexity.Computability.Circuit.Frontier.FanInTwo
import Complexity.Logics.SecondOrder.Coloring
import Complexity.Computability.PCP.GapTheorem
import Complexity.Computability.PCP.Preprocess
import Complexity.Computability.PCP.ThreeSAT
import Complexity.Computability.PCP.Composition
import Complexity.Computability.PCP.PoweringBound
import Complexity.Foundations.Relation.InductiveCounting
import Mathlib.Tactic.FinCases
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
  rw [MultiTapeNTM.RunPath.last_ofDeterministic, runFrom_one, step_of_state (q := ()) rfl]
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
      fun _ => 0).depthWith Unbounded.andOrCost = 0 ∧
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
      (ofMultiTapeTM tm).etimeBoundedComplexity (x.length + 1) x ≤ x.length := by
  obtain ⟨k, State, hfin, tm, ⟨S⟩⟩ := exists_simulation_literal
  refine ⟨k, State, hfin, tm, fun x => ?_⟩
  simpa [etimeBoundedComplexity_literal le_rfl] using S.etimeBoundedComplexity_le x.length x

/-- The canonical composition of the literal method with itself describes every pair `(x, y)`
with `|x| + |y| + 2 size |x| + 1` bits, so the chain rule is not vacuous. -/
example (x y : List Bool) :
    (literal.compose (fun _ => literal) Prod.mk).ecomplexity (x, y) ≤
      (x.length + y.length + (2 * x.length.size + 1) : ℕ) := by
  simpa using (Composition.compose literal (fun _ => literal) Prod.mk).ecomplexity_le x y

/-- The same within `|x| + |y|` steps, from the time-bounded chain rule. -/
example (x y : List Bool) :
    (literal.compose (fun _ => literal) Prod.mk).etimeBoundedComplexity (x.length + y.length)
      (x, y) ≤ (x.length + y.length + (2 * x.length.size + 1) : ℕ) :=
  (Composition.compose literal (fun _ => literal) Prod.mk).etimeBoundedComplexity_le_of_le
    (fun _ _ h => by dsimp only; have := Nat.size_le_size h; omega) monotone_const
    (etimeBoundedComplexity_literal le_rfl).le (etimeBoundedComplexity_literal le_rfl).le

end Kolmogorov

section SecondOrder

open FirstOrder Language Cslib.Logic

/-- The triangle satisfies the three-colorability sentence but not the two-colorability one. -/
example :
    (letI := (⊤ : SimpleGraph (Fin 3)).structure; (ESO.Sentence.colorable 3).Realize (Fin 3)) ∧
      ¬ (letI := (⊤ : SimpleGraph (Fin 3)).structure;
        (ESO.Sentence.colorable 2).Realize (Fin 3)) := by
  rw [ESO.Sentence.realize_colorable_structure_iff, ESO.Sentence.realize_colorable_structure_iff]
  refine ⟨⟨(⊤ : SimpleGraph (Fin 3)).selfColoring⟩, fun h => ?_⟩
  have := h.card_le_of_pairwise_adj id fun i j hij => (SimpleGraph.top_adj i j).2 hij
  simp at this

/-- Definable classes meet the isomorphism-closure hypothesis of first-order reducibility: the
class of `3`-colorable finite simple graphs reduces to itself. -/
example :
    let K : Set (CategoryTheory.Bundled.{0} Language.graph.Structure) :=
      {M | M ⊨ Theory.simpleGraph ∧
        ∃ f : M → Fin 3, ∀ x y, Structure.RelMap adj ![x, y] → f x ≠ f y}
    FO.Reduces K K :=
  .refl (ESO.Definable.colorable_simpleGraph 3).isoClosed

end SecondOrder

section PCP

open Cslib.PCP Cslib.Logic.PL

/-- The whole first layer of Dinur's proof applies: an unsatisfiable formula gives a preprocessed
constraint graph of positive value. -/
example (φ : CNF ℕ) (hφ : φ = [[(0, true)], [(0, false)]]) :
    0 < (ConstraintGraph.ofCNF φ).preprocess.toConstraintGraph.unsatVal := by
  subst hφ
  have h : 0 < (ConstraintGraph.ofCNF ([[(0, true)], [(0, false)]] : CNF ℕ)).unsatVal := by
    rw [ConstraintGraph.unsatVal_pos_iff, ConstraintGraph.satisfiable_ofCNF_iff _ (by simp)]
    rintro ⟨σ, hσ⟩
    simp [CNF.eval, Clause.eval, Literal.eval] at hσ
  exact lt_of_lt_of_le (by positivity) (ConstraintGraph.le_unsatVal_preprocess _)

/-- Dinur's gap theorem applies: the gap graph of an unsatisfiable formula has value at least the
gap. -/
example :
    Dinur.gap ≤ (Dinur.gapGraph ([[((), true)], [((), false)]] : CNF Unit)).graph.unsatVal := by
  refine Dinur.gap_le_unsatVal_gapGraph _ (by simp) ?_
  rintro ⟨σ, hσ⟩
  cases h : σ () <;> simp_all [CNF.eval, Clause.eval, Literal.eval]

end PCP

/-- A round list certifies unreachability: on `Fin 3` with the successor relation, `0` is not
reachable from `1`, certified by the list `[1, 2]` of everything reachable within two steps. -/
example : ¬ Relation.ReflTransGen (fun i j : Fin 3 => j.val = i.val + 1) 1 0 := by
  open Relation in
  have hsub : reachableWithin (fun i j : Fin 3 => j.val = i.val + 1) 1 2 ⊆ {1, 2} := by
    intro j hj
    have hle : (1 : Fin 3).val ≤ j.val := by
      induction (mem_reachableWithin.mp hj).reflTransGen with
      | refl => exact le_rfl
      | tail _ h ih => omega
    fin_cases j <;> simp_all
  open Relation in
  refine (not_reflTransGen_iff_exists_isRoundList (N := 2) (by simp)).mpr
    ⟨[1, 2], ⟨by decide, ?_, ?_⟩, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨Relation.RelatesWithinSteps.refl 1 |>.mono (by omega),
      (Relation.RelatesWithinSteps.single (by decide)).mono (by omega)⟩
  · refine (Set.encard_le_encard hsub).trans ?_
    rw [Set.encard_pair (by decide)]
    simp

/-- The zig-zag tower has a base graph: a graph on `Fin 2 → D × D` of degree `|D| > 1` with
`λ ≤ 1 / 5`. -/
example : ∃ (D : Type) (_ : Fintype D) (H : Cslib.RotationMap (Fin 2 → D × D) D),
    1 < Fintype.card D ∧ H.spectralExpansion ≤ 1 / 5 :=
  ⟨_, _, Cslib.RotationMap.zigzagTowerBase 1440000,
    Fintype.one_lt_card_iff_nontrivial.2 inferInstance,
    Cslib.RotationMap.spectralExpansion_zigzagTowerBase_le_one_div_five le_rfl⟩

open Cslib.RAM in
/-- Repeated squaring on a RAM: on input `2` the program halts after `4 * 2 + 5 = 13` steps with
`2 ^ 2 ^ 2 = 16` in the output register, and the run costs `31` units of logarithmic time. -/
example : (run repeatedSquaring 13 (State.init [2])).isHalted repeatedSquaring ∧
    (run repeatedSquaring 13 (State.init [2])).regs.output = 16 ∧
    time logCost repeatedSquaring 13 (State.init [2]) = 31 := by
  decide

open Cslib.RAM in
/-- The repeated-squaring program evaluates to `2 ^ 2 ^ k` on input `k`. -/
example (k : ℕ) : eval repeatedSquaring [k] = .some (2 ^ 2 ^ k) :=
  computesInTime_unitCost_repeatedSquaring.eval_eq ![k]

section Frontier

open Cslib.Circuits.Frontier Set

/-- The hypotheses of the frontier counting lemma can be met: all strings of one bit form a
`2`-rectangle-free set with at least two elements. -/
example : RectangleFree (univ : Set (Fin 1 → Bool)) 2 ∧ 2 ≤ (univ : Set (Fin 1 → Bool)).ncard := by
  refine ⟨rectangleFree_iff.mpr fun X A B _ => ?_, by simp⟩
  by_cases h : (0 : Fin 1) ∈ X
  · right
    have : Subsingleton (↥Xᶜ → Bool) :=
      ⟨fun f g => funext fun i => absurd (Subsingleton.elim i.1 0 ▸ h) i.2⟩
    exact (ncard_le_one (toFinite _)).mpr (fun a _ b _ => Subsingleton.elim a b) |>.trans_lt
      one_lt_two
  · left
    have : Subsingleton (↥X → Bool) :=
      ⟨fun f g => funext fun i => absurd (Subsingleton.elim i.1 0 ▸ i.2) h⟩
    exact (ncard_le_one (toFinite _)).mpr (fun a _ b _ => Subsingleton.elim a b) |>.trans_lt
      one_lt_two

/-- The hypotheses of the average-case bound can be met by every family of sets: every set has
bias at most `1/2` on rectangles, and the constant threshold `K_n = 1` has logarithm `0 = o(n)`. -/
example (S : ∀ n, Set (Fin n → Bool)) :
    (∀ᶠ n in Filter.atTop, RectangleBias (S n) ((fun _ => 1 : ℕ → ℕ) n) (1 / 2)) ∧
      (fun n => Real.log ((fun _ => 1 : ℕ → ℕ) n)) =o[Filter.atTop] fun n => (n : ℝ) := by
  refine ⟨Filter.Eventually.of_forall fun n => rectangleBias_one_half _ _, ?_⟩
  simpa only [Nat.cast_one, Real.log_one] using Asymptotics.isLittleO_zero _ _

/-- A set with no bias at all: on two bits, the inputs whose bits differ fill exactly half of
every rectangle with both sides of size at least two. Such a rectangle cuts the two bits apart and
has every assignment on both sides. -/
example : RectangleBias {x : Fin 2 → Bool | x 0 ≠ x 1} 2 0 := by
  intro X A B hA hB
  have hcard (Y : Set (Fin 2)) : Nat.card (Y → Bool) = 2 ^ Y.ncard := by
    rw [Nat.card_fun, Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_bool]
  have hA' : A.ncard ≤ 2 ^ X.ncard := hcard X ▸ ncard_le_card A
  have hB' : B.ncard ≤ 2 ^ Xᶜ.ncard := hcard Xᶜ ▸ ncard_le_card B
  have hX : X.ncard + Xᶜ.ncard = 2 := by
    rw [ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  -- Both sides are nontrivial, so each bit lies on its own side.
  have h1 : X.ncard = 1 ∧ Xᶜ.ncard = 1 := by
    rcases Nat.lt_or_ge X.ncard 1 with h | h
    · rw [show X.ncard = 0 by omega] at hA'
      omega
    · rcases Nat.lt_or_ge Xᶜ.ncard 1 with h' | h'
      · rw [show Xᶜ.ncard = 0 by omega] at hB'
        omega
      · omega
  -- Hence both sides are everything, and so is the rectangle.
  have hAu : A = univ := eq_of_subset_of_ncard_le (subset_univ A)
    (by rw [ncard_univ, hcard, h1.1]; omega)
  have hBu : B = univ := eq_of_subset_of_ncard_le (subset_univ B)
    (by rw [ncard_univ, hcard, h1.2]; omega)
  have hR : rectangle X A B = univ := by
    subst hAu hBu
    ext x
    simp [rectangle]
  have hS : {x : Fin 2 → Bool | x 0 ≠ x 1}.ncard = 2 := by
    rw [ncard_eq_toFinset_card', toFinset_ofPred]
    decide
  rw [hR, Set.univ_inter, hS, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  norm_num

end Frontier

section KolmogorovNW

open Cslib Cslib.Kolmogorov Cslib.Crypto.PRG.NisanWigderson

/-- The literal description method runs any list decoder whose outputs have bounded length, so the
hypothesis of the Nisan–Wigderson step to short descriptions can be met. -/
example {ℓ n a m L K : ℕ} (D : Design ℓ n a m)
    (C : ListCode (List Bool) (Fin n → Bool) Bool L) (test : (Fin m → Bool) → Bool)
    (hC : ∀ w k, (C.decode w k).length ≤ K) :
    DescriptionMethod.ReconstructionDecoder DescriptionMethod.literal D C test K K where
  program R k := C.decode (R.guess test) k
  length_program_le _ k := (hC _ k).trans (Nat.le_add_left _ _)
  mem_runFor_program _ k := DescriptionMethod.mem_literal_runFor.mpr ⟨hC _ k, rfl⟩

end KolmogorovNW

section Composition

open Cslib.PCP

/-- Composition keeps an unsatisfiable constraint graph unsatisfiable by a constant margin: the
graph asking two equal labels to differ composes to a graph of positive value. -/
example : 0 < (⟨fun _ ↦ (), fun _ ↦ (), fun _ (a b : Bool) ↦ a ≠ b⟩ :
    ConstraintGraph Unit Unit Bool).compose.unsatVal := by
  set G : ConstraintGraph Unit Unit Bool := ⟨fun _ ↦ (), fun _ ↦ (), fun _ a b ↦ a ≠ b⟩
  have h := G.le_unsatVal_compose
  have hG : 0 < G.unsatVal := G.unsatVal_pos_iff.2 fun ⟨σ, hσ⟩ ↦ hσ () rfl
  linarith

/-- The honest proof passes the Hadamard assignment tester with probability one. -/
example : (hadamardTester (k := 2) (· = ·)).acceptProb (HadamardTester.honestProof ![0, 0]) = 1 :=
  HadamardTester.acceptProb_honestProof rfl

/-- Powering an unsatisfiable regular constraint graph whose spectral expansion is below one gives a
graph of positive value. -/
example {V D α : Type*} [Fintype V] [Fintype D] [Fintype α] [Nonempty α]
    (R : RegularConstraintGraph V D α) (hR : ¬ R.toConstraintGraph.Satisfiable)
    (hl : R.graph.spectralExpansion < 1) :
    0 < (R.power (4 * Fintype.card α * (2 - 1)) 2).toConstraintGraph.unsatVal := by
  refine lt_of_lt_of_le ?_ (R.le_unsatVal_power _ 2 le_rfl rfl le_rfl hl)
  have h₀ := (R.toConstraintGraph.unsatVal_pos_iff).2 hR
  have hl' : 0 < 1 - R.graph.spectralExpansion := sub_pos.2 hl
  have hα : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  apply mul_pos
  · norm_num
    positivity
  · exact lt_min h₀ (by positivity)

end Composition

section FrontierReduction

open Cslib.Circuits Cslib.Circuits.Frontier Set

/-- The hypotheses of the reduction theorem are satisfiable: a one-gate circuit decides the
inputs with exactly one bit set, an 8-element 2-rectangle-free set. -/
example : ∃ (c : Circuit (fullSignature 8 Bool) 8 1) (S : Set (Fin 8 → Bool)),
    c.FanInAtMost 8 ∧ c.Decides fullInterpretation {true} S ∧ RectangleFree S 2 ∧
      Nat.card Bool * 2 ^ 2 ≤ S.ncard := by
  let S : Set (Fin 8 → Bool) := {x | {i | x i = true}.ncard = 1}
  -- Two set bits of an input of `S` coincide.
  have huniq {x} (hx : x ∈ S) {i j} (hi : x i = true) (hj : x j = true) : i = j := by
    obtain ⟨k, hk⟩ := ncard_eq_one.mp hx
    exact ((hk ▸ hi : i ∈ ({k} : Set _))).trans (hk ▸ hj : j ∈ ({k} : Set _)).symm
  refine ⟨⟨Program.empty.gate ⟨.fn fun x => decide ({i | x i = true}.ncard = 1),
    fun k => .input k⟩, fun _ => .gate 0⟩, S, ⟨trivial, le_rfl⟩, fun x => ?_, ?_, ?_⟩
  · change _ ↔ decide ({i | x i = true}.ncard = 1) = true
    simp [S]
  · -- A rectangle with two distinct sides on `X` forces every side on `Xᶜ` to be zero.
    refine rectangleFree_iff.mpr fun X A B hAB => ?_
    by_contra! h
    obtain ⟨a, a', ha, ha', hne⟩ := (one_lt_ncard_iff).mp (by omega : 1 < A.ncard)
    obtain ⟨b, b', hb, hb', hne'⟩ := (one_lt_ncard_iff).mp (by omega : 1 < B.ncard)
    classical
    let z (a : X → Bool) (b : ↥Xᶜ → Bool) : Fin 8 → Bool :=
      fun i => if h : i ∈ X then a ⟨i, h⟩ else b ⟨i, h⟩
    have hz {a b} (ha : a ∈ A) (hb : b ∈ B) : z a b ∈ S := by
      refine hAB ⟨?_, ?_⟩
      · convert ha using 1; funext ⟨i, hi⟩; simp [z, hi]
      · convert hb using 1; funext ⟨i, hi⟩; simp [z, show i ∉ X from hi]
    have hzero {a} (ha : a ∈ A) {i : X} (hi : a i = true) {b} (hb : b ∈ B) :
        b = fun _ => false := by
      funext j
      by_contra hj
      have := huniq (hz ha hb) (i := i) (j := j) (by simp [z, i.2, hi])
        (by simpa [z, show (j : Fin 8) ∉ X from j.2] using hj)
      exact j.2 (this ▸ i.2)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    rcases Bool.eq_false_or_eq_true (a i) with h₁ | h₁
    · exact hne' ((hzero ha h₁ hb).trans (hzero ha h₁ hb').symm)
    · have h₂ : a' i = true := by simpa [h₁] using hi
      exact hne' ((hzero ha' h₂ hb).trans (hzero ha' h₂ hb').symm)
  · -- The eight unit vectors lie in `S`.
    let e (i : Fin 8) : Fin 8 → Bool := fun j => decide (j = i)
    have he : Function.Injective e := fun i i' h => by simpa [e] using congrFun h i
    calc Nat.card Bool * 2 ^ 2 = (range e).ncard := by simp [ncard_range_of_injective he]
      _ ≤ S.ncard := ncard_le_ncard (range_subset_iff.mpr fun i => by simp [S, e]) (toFinite _)

/-- The hypotheses of the spanning-tree layout theorem can be met: one edge between two vertices
is connected, loopless and of maximum degree one, and it has a layout of width at most one. -/
example : ∃ π : Layout (Fin 2),
    (⟨fun _ => 0, fun _ => 1⟩ : Multigraph (Fin 2) Unit).width π ≤ 1 := by
  set G : Multigraph (Fin 2) Unit := ⟨fun _ => 0, fun _ => 1⟩
  have hadj : G.toSimpleGraph.Adj 0 1 := Multigraph.toSimpleGraph_adj.mpr ⟨by decide, (), rfl⟩
  have hconn : G.toSimpleGraph.Connected := by
    refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨0, fun v => ?_⟩
    fin_cases v
    exacts [SimpleGraph.Reachable.refl _, hadj.reachable]
  have hdeg : G.MaxDegreeLE 1 := fun v => (Set.ncard_le_card _).trans (by simp)
  obtain ⟨π, hπ⟩ := Multigraph.exists_width_le_cycleRank_add hconn hdeg
  refine ⟨π, hπ.trans ?_⟩
  simp [Multigraph.cycleRank, Nat.log_eq_one_iff'.mpr (by decide : 2 ≤ 2 ∧ 2 < 2 * 2)]

end FrontierReduction

section FrontierLinear

open Cslib.Circuits Matrix

/-- An arithmetic circuit computing the `1 × 1` Cauchy map `x ↦ -x`: a constant `-1` and a
product. -/
def negCircuit : Circuit (arithSignature ℚ) 1 1 :=
  ⟨(Program.empty.gate ⟨ArithOp.const (-1), Fin.elim0⟩).gate
      ⟨ArithOp.mul, ![.input 0, .gate 0]⟩, fun _ => .gate 1⟩

/-- The `Computes` hypothesis of the arithmetic Cauchy lower bound can be met. -/
example : negCircuit.Computes (arithInterpretation ℚ) (fun x => cauchyNat ℚ 1 *ᵥ x) := by
  intro x; funext i; fin_cases i
  simp only [Circuit.eval, negCircuit, Nat.reduceAdd, Fin.isValue, Program.trace, Program.eval,
    Line.eval, arithInterpretation, Function.comp_apply, cons_val_zero, Wire.elim_input,
    cons_val_one, cons_val_fin_one, Wire.elim_gate, Fin.zero_eta, mulVec, dotProduct,
    Finset.univ_unique, Fin.default_eq_zero, cauchyNat, Fin.val_eq_zero, CharP.cast_eq_zero,
    add_zero, Nat.cast_one, cauchy_apply, zero_sub, inv_neg, inv_one, neg_mul, one_mul,
    Finset.sum_neg_distrib, Finset.sum_singleton]
  rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.lastCases_last,
    show (0 : Fin 1) = Fin.last 0 from rfl, Fin.lastCases_last]
  ring

/-- Explicit Cauchy matrices are totally regular. -/
example : (cauchyNat ℚ 5).TotallyRegular := totallyRegular_cauchyNat 5

end FrontierLinear

section FrontierLedger

open Cslib.Circuits Cslib.Circuits.Frontier

/-- The ledger hypothesis can be met: every AC⁰ program has a ledger for all of its gates. -/
example {n s : ℕ} (p : Program Boolean.Unbounded.signature n s) :
    Nonempty (Ledger (fun _ => True) p Boolean.Unbounded.interpretation
      ({_g : Fin s // True} → ZMod 2)) :=
  exists_ledger_of_aggregates p _ _ _ fun _ _ => aggregates_unbounded _

end FrontierLedger

section FrontierDecomposable

open Cslib.Circuits.Frontier Set

/-- A decomposable DAG for the conjunction of two bits: a product of two leaves. -/
def conjunctionDAG : DecomposableDAG (Fin 2) Bool (Option (Fin 2)) where
  scope
    | none => univ
    | some i => {i}
  root := none
  scope_root := rfl
  gate
    | none => .product (some 0) (some 1)
    | some _ => .leaf
  rank
    | none => 1
    | some _ => 0
  values
    | none => {f | ∀ i, f ⟨i, mem_univ i⟩ = true}
    | some _ => {fun _ => true}
  values_subsingleton
    | none, h => nomatch h
    | some _, _ => subsingleton_singleton
  scope_union
    | none, _, h => nomatch h
    | some _, _, h => nomatch h
  rank_union
    | none, _, h => nomatch h
    | some _, _, h => nomatch h
  values_union
    | none, _, h => nomatch h
    | some _, _, h => nomatch h
  scope_product
    | none, _, _, h => by
      cases h
      ext i
      match i with
      | 0 => simp
      | 1 => simp
    | some _, _, _, h => nomatch h
  disjoint_product
    | none, _, _, h => by
      cases h
      simp
    | some _, _, _, h => nomatch h
  rank_product
    | none, _, _, h => by
      cases h
      simp
    | some _, _, _, h => nomatch h
  values_product
    | none, _, _, h, x => by
      cases h
      simp [Fin.forall_fin_two, funext_iff]
    | some _, _, _, h, _ => nomatch h

/-- It represents the conjunction of the two bits. -/
example : conjunctionDAG.accepted = {x | x 0 = true ∧ x 1 = true} := by
  ext x
  exact Fin.forall_fin_two

end FrontierDecomposable

section FrontierGaussian

open Cslib.Circuits.Frontier

/-- `m` disjoint theta graphs, each two vertices joined by three parallel edges. -/
def thetaGraphs (m : ℕ) : Multigraph (Fin m × Bool) (Fin m × Fin 3) :=
  ⟨fun e => (e.1, false), fun e => (e.1, true)⟩

theorem thetaGraphs_loopless (m : ℕ) : (thetaGraphs m).Loopless :=
  fun e h => by simp [thetaGraphs] at h

theorem ncard_incidenceSet_thetaGraphs (m : ℕ) (v : Fin m × Bool) :
    ((thetaGraphs m).incidenceSet v).ncard = 3 := by
  obtain ⟨i, b⟩ := v
  have : (thetaGraphs m).incidenceSet (i, b) = Set.range fun j : Fin 3 => (i, j) := by
    ext ⟨i', j⟩
    cases b <;> simp [thetaGraphs, Multigraph.mem_incidenceSet, eq_comm]
  rw [this, Set.ncard_range_of_injective fun j j' h => by simpa using h]
  simp

/-- The hypotheses of the Gaussian layouts of cubic multigraphs can be met in every size, and
large theta graphs get layouts of width at most `(p + 1)` times their number of vertices. -/
example : ∃ N₀ : ℕ, ∀ m : ℕ, N₀ < 2 * m → ∃ σ : Layout (Fin m × Bool),
    ((thetaGraphs m).width σ : ℝ) ≤
      (Gaussian.gaussianCoefficient + 1) * Nat.card (Fin m × Bool) := by
  obtain ⟨N₀, hN₀⟩ := Gaussian.exists_width_le_gaussianCoefficient one_pos
  exact ⟨N₀, fun m hm => hN₀ _ _ _ (thetaGraphs_loopless m) (ncard_incidenceSet_thetaGraphs m)
    (by simpa [mul_comm] using hm)⟩

end FrontierGaussian

end ComplexityTests.NonVacuity
