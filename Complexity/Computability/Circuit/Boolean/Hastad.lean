/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Computability.DecisionTree.Parity
public import Complexity.Computability.DecisionTree.Restrict
public import Complexity.Computability.DecisionTree.Switching
public import Complexity.Foundations.Data.Nat.Choose
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parity is not computed by small formulas of constant depth

**Håstad's theorem** for formulas with unbounded fan-in: a formula of depth `d` with fewer than
`2 ^ s` operation nodes that computes the parity of `n` bits has `n < s (16 s + 1) ^ d`, for every
`s ≥ 2`. So such formulas have size `2 ^ Ω(n ^ (1 / (d + 1)))` [Håstad1986],
[Jukna, Chapter 12][Jukna2012].

The proof restricts the formula `d` times. After stage `j`, every subformula of depth at most `j`
computes, under the restriction so far, a function of decision tree complexity below `s`
(`Shallow`). An operation node of depth `j + 1` then computes, up to negation, a formula in
disjunctive normal form whose terms have fewer than `s` literals (`exists_dnf_of_shallow`), and the
switching lemma shows that few extensions of the restriction fail to make it shallow. A union bound
over the operation nodes leaves an extension that works for all of them. At the end the whole
formula is shallow, while the restricted parity needs to query every free bit.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.Shallow`: a function has, under a restriction, small decision
  tree complexity.
* `Cslib.Circuits.Boolean.Unbounded.gateFun`: the function computed by an operation applied to
  given functions.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.exists_dnf_of_shallow`: an operation applied to shallow
  functions computes a narrow formula in disjunctive normal form, up to negation.
* `Cslib.Circuits.Boolean.Unbounded.exists_extension_shallow`: one stage of restrictions, for any
  family of fewer than `2 ^ s` operations applied to shallow functions; it serves formulas and
  circuits alike.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity`: Håstad's theorem for
  formulas.

## References

* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Cslib.DecisionTree Cslib.Logic.PL Finset

variable {n s : ℕ} {ρ ρ' : Restriction n}

/-- `f` is `s`-shallow under `ρ`: the function it computes under `ρ` has decision tree complexity
below `s`. -/
def Shallow (s : ℕ) (ρ : Restriction n) (f : BitString n → Bool) : Prop :=
  DecisionTree.complexity (fun x => f (ρ.fill x)) < s

noncomputable instance (s : ℕ) (ρ : Restriction n) (f : BitString n → Bool) :
    Decidable (Shallow s ρ f) :=
  inferInstanceAs (Decidable (_ < _))

/-- Restricting further keeps a function shallow. -/
theorem Shallow.mono {f : BitString n → Bool} (hf : Shallow s ρ f) (h : ρ'.Extends ρ) :
    Shallow s ρ' f := by
  refine lt_of_le_of_lt ?_ hf
  have : DecisionTree.complexity (fun x => f (ρ.fill (ρ'.fill x))) ≤
      DecisionTree.complexity fun y => f (ρ.fill y) :=
    complexity_comp_fill_le ρ' fun y => f (ρ.fill y)
  simpa only [Restriction.fill_fill_of_extends h] using this

/-- The input bits are shallow. -/
theorem shallow_proj (hs : 2 ≤ s) (ρ : Restriction n) (i : Fin n) :
    Shallow s ρ fun x => x i := by
  have h₁ : DecisionTree.complexity (fun x : BitString n => x i) ≤ 1 :=
    DecisionTree.complexity_le_iff.2 ⟨DecisionTree.node i (.leaf false) (.leaf true),
      fun x => by cases h : x i <;> simp [h], by simp⟩
  exact lt_of_le_of_lt ((complexity_comp_fill_le ρ fun x : BitString n => x i).trans h₁)
    (by omega)

/-- The negation of a shallow function is shallow. -/
theorem Shallow.not {f : BitString n → Bool} (h : Shallow s ρ f) : Shallow s ρ fun x => !f x :=
  (complexity_not fun x => f (ρ.fill x)).trans_lt h

/-- The function computed by the operation `g.1` applied to the functions `g.2`. -/
def gateFun (g : Σ op : signature.Op, Fin (signature.Arity op) → BitString n → Bool) :
    BitString n → Bool :=
  fun x => interpretation g.1 fun a => g.2 a x

/-- Shallow functions have decision trees of depth below `s`. -/
private theorem exists_tree_of_shallow {f : BitString n → Bool} (h : Shallow s ρ f) :
    ∃ t : DecisionTree (Fin n) Bool, (∀ y, t.eval y = f (ρ.fill y)) ∧ t.depth < s := by
  obtain ⟨t, ht, hd⟩ := DecisionTree.complexity_le_iff.1
    (le_refl (DecisionTree.complexity fun x => f (ρ.fill x)))
  exact ⟨t, ht, hd.trans_lt h⟩

/-- The disjunction of the paths of decision trees of depth below `s` to leaves other than `c`. -/
private theorem exists_dnf_of_trees {m : ℕ} (c : Bool) (t : Fin m → DecisionTree (Fin n) Bool)
    (hd : ∀ j, (t j).depth < s) :
    ∃ D : DNF (Fin n), (∀ u ∈ D, u.length < s ∧ (u.map Prod.fst).Nodup) ∧
      ∀ y, DNF.eval y D = decide (∃ j, ((t j).eval y != c) = true) := by
  refine ⟨(List.ofFn fun j => ((t j).map (· != c)).toDNF).flatten, fun u hu => ?_, fun y => ?_⟩
  · obtain ⟨_, hl, hu⟩ := List.mem_flatten.1 hu
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
    exact ⟨(length_le_depth_of_mem_toDNF hu).trans_lt (by rw [depth_map]; exact hd j),
      nodup_of_mem_toDNF hu⟩
  · rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, decide_eq_true_iff]
    simp only [List.mem_flatten, List.mem_ofFn]
    constructor
    · rintro ⟨u, ⟨_, ⟨j, rfl⟩, hu⟩, hux⟩
      refine ⟨j, ?_⟩
      rw [← eval_map (· != c), ← eval_toDNF, DNF.eval_eq_true_iff]
      exact ⟨u, hu, hux⟩
    · rintro ⟨j, hj⟩
      rw [← eval_map (· != c), ← eval_toDNF, DNF.eval_eq_true_iff] at hj
      obtain ⟨u, hu, hux⟩ := hj
      exact ⟨u, ⟨_, ⟨j, rfl⟩, hu⟩, hux⟩

/-- **Operations applied to shallow functions are narrow formulas in disjunctive normal form**, up
to negation: a disjunction is the disjunction of the paths to `true` of decision trees for its
arguments, and the negation of a conjunction is the disjunction of their paths to `false`. -/
theorem exists_dnf_of_shallow {op : signature.Op} (hop : op ≠ .not)
    {args : Fin (signature.Arity op) → BitString n → Bool} (h : ∀ j, Shallow s ρ (args j)) :
    ∃ (D : DNF (Fin n)) (b : Bool), (∀ t ∈ D, t.length < s ∧ (t.map Prod.fst).Nodup) ∧
      ∀ y, DNF.eval y D = (gateFun ⟨op, args⟩ (ρ.fill y) != b) := by
  choose t ht hd using fun j => exists_tree_of_shallow (h j)
  cases op with
  | not => exact absurd rfl hop
  | and m =>
    obtain ⟨D, hD, heval⟩ := exists_dnf_of_trees true t hd
    refine ⟨D, true, hD, fun y => ?_⟩
    rw [heval]
    change _ = (decide (∀ j, args j (ρ.fill y) = true) != true)
    by_cases hall : ∀ j, args j (ρ.fill y) = true
    · simp [ht, hall]
    · obtain ⟨j, hj⟩ := not_forall.1 hall
      have h₂ : ∃ j, ((t j).eval y != true) = true := ⟨j, by simpa [ht] using hj⟩
      rw [decide_eq_true h₂, decide_eq_false hall]
      rfl
  | or m =>
    obtain ⟨D, hD, heval⟩ := exists_dnf_of_trees false t hd
    refine ⟨D, false, hD, fun y => ?_⟩
    rw [heval]
    change _ = (decide (∃ j, args j (ρ.fill y) = true) != false)
    simp [ht]

/-- **The union bound of a stage.** If there are fewer than `2 ^ s` operation nodes and `ℓ` is at
most a `1 / (16 s + 1)` fraction of the `m` free bits, then the restrictions that the switching
lemma bounds for every node together are fewer than all extensions with `ℓ` free bits. -/
theorem stage_count {S m ℓ s : ℕ} (hS : S < 2 ^ s) (hs : 1 ≤ s) (hsℓ : s ≤ ℓ)
    (hℓ : (16 * s + 1) * ℓ ≤ m) :
    S * (m.choose (ℓ - s) * 2 ^ (m - (ℓ - s)) * (4 * s) ^ s) < m.choose ℓ * 2 ^ (m - ℓ) := by
  have hℓm : ℓ ≤ m := le_trans (Nat.le_mul_of_pos_left ℓ (by omega)) hℓ
  have hB : 0 < m.choose ℓ := Nat.choose_pos hℓm
  have hratio := Nat.choose_sub_mul_pow_le hsℓ hℓm
  have hpos : 0 < (m - ℓ + 1) ^ s := Nat.pow_pos (by omega)
  have hle : 16 * s * ℓ ≤ m - ℓ + 1 := by
    have : (16 * s + 1) * ℓ = 16 * s * ℓ + ℓ := by ring
    omega
  have h2 : 2 ^ (m - (ℓ - s)) = 2 ^ (m - ℓ) * 2 ^ s := by
    rw [← pow_add]
    congr 1
    omega
  -- cancel `2 ^ (m - ℓ)`, then multiply by `(m - ℓ + 1) ^ s`
  suffices h : S * m.choose (ℓ - s) * (8 * s) ^ s < m.choose ℓ by
    calc S * (m.choose (ℓ - s) * 2 ^ (m - (ℓ - s)) * (4 * s) ^ s)
        = S * m.choose (ℓ - s) * (8 * s) ^ s * 2 ^ (m - ℓ) := by
          rw [h2, show (8 * s) ^ s = 2 ^ s * (4 * s) ^ s by rw [← mul_pow]; ring_nf]
          ring
      _ < m.choose ℓ * 2 ^ (m - ℓ) := Nat.mul_lt_mul_of_pos_right h (by positivity)
  refine Nat.lt_of_mul_lt_mul_right (a := (m - ℓ + 1) ^ s) ?_
  calc S * m.choose (ℓ - s) * (8 * s) ^ s * (m - ℓ + 1) ^ s
      = S * (8 * s) ^ s * (m.choose (ℓ - s) * (m - ℓ + 1) ^ s) := by ring
    _ ≤ S * (8 * s) ^ s * (m.choose ℓ * ℓ ^ s) := Nat.mul_le_mul_left _ hratio
    _ = m.choose ℓ * (S * (8 * s * ℓ) ^ s) := by rw [mul_pow (8 * s) ℓ]; ring
    _ < m.choose ℓ * (2 ^ s * (8 * s * ℓ) ^ s) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hS
          (Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)))) hB
    _ = m.choose ℓ * (16 * s * ℓ) ^ s := by
        rw [← mul_pow]
        ring_nf
    _ ≤ m.choose ℓ * (m - ℓ + 1) ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle s)

/-- Post-composing with `(· != b)` does not change decision tree complexity. -/
private theorem complexity_bne (f : BitString n → Bool) (b : Bool) :
    DecisionTree.complexity (fun x => (f x != b)) = DecisionTree.complexity f := by
  cases b
  · simp
  · simpa using complexity_not f

/-- **The switching step for one operation.** If the arguments of an operation are shallow under
`ρ`, few extensions of `ρ` leave it deep. -/
theorem card_filter_not_shallow_le {g : Σ op : signature.Op, Fin (signature.Arity op) →
    BitString n → Bool} (h : ∀ j, Shallow s ρ (g.2 j)) (ℓ : ℕ) :
    #((ρ.extensions ℓ).filter fun ρ' => ¬ Shallow s ρ' (gateFun g)) ≤
      #(ρ.extensions (ℓ - s)) * (4 * s) ^ s := by
  obtain ⟨op, args⟩ := g
  by_cases hop : op = .not
  · subst hop
    have hG : Shallow s ρ (gateFun ⟨.not, args⟩) := (h (0 : Fin 1)).not
    rw [filter_false_of_mem fun ρ' hρ' => not_not.2 (hG.mono
      (Restriction.mem_extensions.1 hρ').1)]
    simp
  obtain ⟨D, b, hD, heval⟩ := exists_dnf_of_shallow hop h
  refine (card_le_card fun ρ' hρ' => ?_).trans (DNF.card_switching_le
    (fun t ht => (hD t ht).1.le) (fun t ht => (hD t ht).2) ρ ℓ s)
  obtain ⟨hρ', hdeep⟩ := mem_filter.1 hρ'
  refine mem_filter.2 ⟨hρ', ?_⟩
  have hext := (Restriction.mem_extensions.1 hρ').1
  have : (fun x => DNF.eval (ρ'.fill x) D) = fun x => (gateFun ⟨op, args⟩ (ρ'.fill x) != b) := by
    funext x
    rw [heval, Restriction.fill_fill_of_extends hext]
  rw [this, complexity_bne]
  exact not_lt.1 hdeep

/-- **One stage of restrictions.** Given fewer than `2 ^ s` operations applied to functions that
are shallow under `ρ`, and `ℓ ≥ s` at most a `1 / (16 s + 1)` fraction of the free bits of `ρ`,
some extension of `ρ` leaving `ℓ` bits free makes all of them shallow. -/
theorem exists_extension_shallow {ι : Type*} (T : Finset ι)
    (g : ι → Σ op : signature.Op, Fin (signature.Arity op) → BitString n → Bool)
    (hT : #T < 2 ^ s) (hs : 1 ≤ s) (hargs : ∀ i ∈ T, ∀ j, Shallow s ρ ((g i).2 j)) {ℓ : ℕ}
    (hsℓ : s ≤ ℓ) (hℓ : (16 * s + 1) * ℓ ≤ #ρ.free) :
    ∃ ρ' ∈ ρ.extensions ℓ, ∀ i ∈ T, Shallow s ρ' (gateFun (g i)) := by
  classical
  set B : ι → Finset (Restriction n) := fun i =>
    (ρ.extensions ℓ).filter fun ρ' => ¬ Shallow s ρ' (gateFun (g i))
  have hcard : #(T.biUnion B) < #(ρ.extensions ℓ) := by
    calc #(T.biUnion B) ≤ ∑ i ∈ T, #(B i) := card_biUnion_le
      _ ≤ #T * (#(ρ.extensions (ℓ - s)) * (4 * s) ^ s) := by
        simpa using sum_le_card_nsmul T _ _ fun i hi => card_filter_not_shallow_le (hargs i hi) ℓ
      _ < #(ρ.extensions ℓ) := by
        rw [Restriction.card_extensions, Restriction.card_extensions]
        exact stage_count hT hs hsℓ hℓ
  obtain ⟨ρ', hρ', hgood⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨ρ', hρ', fun i hi => ?_⟩
  by_contra hbad
  exact hgood (mem_biUnion.2 ⟨i, hi, mem_filter.2 ⟨hρ', hbad⟩⟩)

/-- The number of free bits after `j` stages. -/
theorem le_div_pow_of_mul_pow_le {d j : ℕ} (hs : 1 ≤ s) (hj : j ≤ d)
    (hn : s * (16 * s + 1) ^ d ≤ n) : s ≤ n / (16 * s + 1) ^ j := by
  have hc : 0 < 16 * s + 1 := by omega
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos hc)]
  calc s * (16 * s + 1) ^ j ≤ s * (16 * s + 1) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hc hj)
    _ ≤ n := hn

/-- One stage shrinks the free bits by the factor `16 s + 1`. -/
theorem mul_div_pow_succ_le (n s j : ℕ) :
    (16 * s + 1) * (n / (16 * s + 1) ^ (j + 1)) ≤ n / (16 * s + 1) ^ j := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

/-- Restricted parity is not shallow when at least `s` bits are free. -/
theorem not_shallow_parity {ρ : Restriction n} (h : s ≤ #ρ.free) : ¬ Shallow s ρ (parity n) :=
  fun hshallow => absurd ((card_free_le_complexity_parity_fill ρ).trans_lt hshallow) (by omega)

/-! ### Formulas -/

/-- The operation and argument functions of an operation node; inputs are mapped to a negation of
a constant, which is never used. -/
def nodeGate : Formula signature n → Σ op : signature.Op, Fin (signature.Arity op) →
    BitString n → Bool
  | .input _ => ⟨.and 0, Fin.elim0⟩
  | .gate op args => ⟨op, fun a x => (args a).eval interpretation x⟩

/-- Operation nodes have positive depth. -/
private theorem depth_pos_of_mem_gates {F G : Formula signature n} (hG : G ∈ F.gates) :
    0 < G.depth := by
  cases G with
  | input i => exact absurd hG (Formula.input_notMem_gates i F)
  | gate op args => simp

/-- **One stage, for formulas.** If every operation node of `F` of depth at most `j` is shallow
under `ρ` and `F` has fewer than `2 ^ s` of them, some extension of `ρ` leaving `ℓ` bits free makes
every operation node of depth at most `j + 1` shallow. -/
theorem exists_stage {F : Formula signature n} (hs : 2 ≤ s) (hS : F.size < 2 ^ s) {j : ℕ}
    (hρ : ∀ G ∈ F.gates, G.depth ≤ j → Shallow s ρ (G.eval interpretation)) {ℓ : ℕ}
    (hsℓ : s ≤ ℓ) (hℓ : (16 * s + 1) * ℓ ≤ #ρ.free) :
    ∃ ρ' ∈ ρ.extensions ℓ, ∀ G ∈ F.gates, G.depth ≤ j + 1 →
      Shallow s ρ' (G.eval interpretation) := by
  classical
  obtain ⟨ρ', hρ', hgood⟩ := exists_extension_shallow
    (F.gates.toFinset.filter fun G => G.depth = j + 1) nodeGate
    (((card_filter_le _ _).trans (List.toFinset_card_le _)).trans_lt
      (by rw [Formula.length_gates]; exact hS)) (by omega) (fun G hG k => by
      obtain ⟨hG, hdepth⟩ := mem_filter.1 hG
      rw [List.mem_toFinset] at hG
      cases G with
      | input i => exact absurd hG (Formula.input_notMem_gates i F)
      | gate op args =>
        rcases Formula.arg_mem_gates hG k with ⟨i, hi⟩ | hk
        · simp only [nodeGate, hi, Formula.eval_input]
          exact shallow_proj hs ρ i
        · refine hρ _ hk ?_
          rw [Formula.depth_gate] at hdepth
          exact (Finset.le_sup (f := fun k => (args k).depth) (Finset.mem_univ _)).trans
            (Nat.succ.inj hdepth).le) hsℓ hℓ
  refine ⟨ρ', hρ', fun G hG hdepth => ?_⟩
  rcases Nat.lt_or_ge G.depth (j + 1) with hlt | hge
  · exact (hρ G hG (by omega)).mono (Restriction.mem_extensions.1 hρ').1
  · have := hgood G (mem_filter.2 ⟨List.mem_toFinset.2 hG, by omega⟩)
    cases G with
    | input i => exact absurd hG (Formula.input_notMem_gates i F)
    | gate op args => exact this

/-- **The stages, for formulas.** After `j ≤ d` stages, a restriction leaves `n / (16 s + 1) ^ j`
bits free and makes every operation node of depth at most `j` shallow. -/
private theorem exists_restriction_stages {F : Formula signature n} (hs : 2 ≤ s)
    (hS : F.size < 2 ^ s) {d : ℕ} (hn : s * (16 * s + 1) ^ d ≤ n) :
    ∀ j ≤ d, ∃ ρ : Restriction n, #ρ.free = n / (16 * s + 1) ^ j ∧
      ∀ G ∈ F.gates, G.depth ≤ j → Shallow s ρ (G.eval interpretation)
  | 0, _ => ⟨fun _ => none, by simp, fun G hG hd => absurd hd (by
      have := depth_pos_of_mem_gates hG
      omega)⟩
  | j + 1, hj => by
    obtain ⟨ρ, hfree, hρ⟩ := exists_restriction_stages hs hS hn j (by omega)
    obtain ⟨ρ', hρ', hgood⟩ := exists_stage hs hS hρ (le_div_pow_of_mul_pow_le (by omega) hj hn)
      (hfree ▸ mul_div_pow_succ_le n s j)
    exact ⟨ρ', (Restriction.mem_extensions.1 hρ').2, hgood⟩

/-- **Håstad's theorem** for formulas with unbounded fan-in. A formula of depth `d` computing the
parity of `n` bits has at least `2 ^ s` operation nodes, for every `s ≥ 2` with
`s (16 s + 1) ^ d ≤ n`. So it has size `2 ^ Ω(n ^ (1 / (d + 1)))` for fixed `d`. -/
theorem two_pow_le_size_of_computes_parity {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) {s : ℕ} (hs : 2 ≤ s)
    (hn : s * (16 * s + 1) ^ F.depth ≤ n) : 2 ^ s ≤ F.size := by
  by_contra! hS
  obtain ⟨ρ, hfree, hρ⟩ := exists_restriction_stages hs hS hn F.depth le_rfl
  -- the whole formula is shallow at the end
  have hshallow : Shallow s ρ (F.eval interpretation) := by
    cases F with
    | input i => exact shallow_proj hs ρ i
    | gate op args => exact hρ _ (Formula.mem_gates_self op args) le_rfl
  rw [Formula.computes_iff.1 hF] at hshallow
  exact not_shallow_parity (hfree ▸ le_div_pow_of_mul_pow_le (by omega) le_rfl hn) hshallow

end Cslib.Circuits.Boolean.Unbounded
