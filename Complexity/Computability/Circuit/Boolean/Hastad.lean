/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Computability.Circuit.Formula
public import Complexity.Computability.DecisionTree.Parity
public import Complexity.Computability.DecisionTree.Restrict
public import Complexity.Computability.DecisionTree.Switching
import Complexity.Computability.Circuit.Depth
import Complexity.Foundations.Data.Nat.Choose
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Håstad's theorem: parity needs large circuits of constant depth

**Håstad's theorem** for circuits with unbounded fan-in: a circuit of depth `d` with fewer than
`2 ^ s` gates that computes the parity of `n` bits has `n < s (16 s + 1) ^ d`, for every `s ≥ 2`.
So such circuits, and formulas (`Formula.toCircuit`), have size `2 ^ Ω(n ^ (1 / (d + 1)))`
[FurstSaxeSipser1984], [Ajtai1983], [Hastad1986], [Jukna, Chapter 12][Jukna2012]. The exponent
`1 / (d + 1)` is weaker than Håstad's `1 / (d - 1)`: each stage below leaves a `1 / (16 s + 1)`
fraction of the free bits rather than `1 / (10 s)` with a final DNF stage. Depth counts every gate
on a path, negations included, and size counts every gate.

The proof restricts the circuit `d` times. After stage `j`, every gate of depth at most `j`
computes, under the restriction so far, a function of decision tree complexity below `s`
(`Shallow`). A gate of depth `j + 1` then computes, up to negation, a formula in disjunctive normal
form whose terms have fewer than `s` literals (`exists_dnf_of_shallow`), and the switching lemma
shows that few extensions of the restriction fail to make it shallow. A union bound over the gates
leaves an extension that works for all of them (`exists_extension_shallow`). At the end the output
is shallow, while the restricted parity needs to query every free bit.

## Main definitions

* `Cslib.Circuits.Boolean.Shallow`: a function has, under a restriction, small decision tree
  complexity.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.exists_dnf_of_shallow`: an operation applied to shallow
  functions computes a narrow formula in disjunctive normal form, up to negation.
* `Cslib.Circuits.Boolean.Unbounded.exists_extension_shallow`: one stage of restrictions, for any
  family of fewer than `2 ^ s` operations applied to shallow functions.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity`: Håstad's theorem for
  circuits.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_formula_computes_parity`: Håstad's theorem
  for formulas.

## References

* [M. Furst, J. B. Saxe, M. Sipser, *Parity, circuits, and the polynomial-time
  hierarchy*][FurstSaxeSipser1984]
* [M. Ajtai, *Σ¹₁-formulae on finite structures*][Ajtai1983]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Cslib.DecisionTree Cslib.Logic.PL Finset

variable {n s : ℕ} {ρ ρ' : Restriction n}

/-! ### Shallow functions -/

/-- `f` is `s`-shallow under `ρ`: the function it computes under `ρ` has decision tree complexity
below `s`. -/
def Shallow (s : ℕ) (ρ : Restriction n) (f : BitString n → Bool) : Prop :=
  DecisionTree.complexity (fun x => f (ρ.fill x)) < s

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

/-- Shallow functions have decision trees of depth below `s`. -/
theorem Shallow.exists_tree {f : BitString n → Bool} (h : Shallow s ρ f) :
    ∃ t : DecisionTree (Fin n) Bool, (∀ y, t.eval y = f (ρ.fill y)) ∧ t.depth < s := by
  obtain ⟨t, ht, hd⟩ := DecisionTree.complexity_le_iff.1
    (le_refl (DecisionTree.complexity fun x => f (ρ.fill x)))
  exact ⟨t, ht, hd.trans_lt h⟩

/-- Restricted parity is not shallow when at least `s` bits are free. -/
theorem not_shallow_parity (h : s ≤ #ρ.free) : ¬ Shallow s ρ (parity n) :=
  fun hshallow => absurd ((card_free_le_complexity_parity_fill ρ).trans_lt hshallow) (by omega)

namespace Unbounded

/-! ### One stage of restrictions -/

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
theorem exists_dnf_of_shallow {op : Op} (hop : op ≠ .not) {args : Fin op.arity → BitString n → Bool}
    (h : ∀ j, Shallow s ρ (args j)) :
    ∃ (D : DNF (Fin n)) (b : Bool), (∀ t ∈ D, t.length < s ∧ (t.map Prod.fst).Nodup) ∧
      ∀ y, DNF.eval y D = (interpretation op (fun j => args j (ρ.fill y)) != b) := by
  choose t ht hd using fun j => (h j).exists_tree
  cases op with
  | not => exact absurd rfl hop
  | and m =>
    obtain ⟨D, hD, heval⟩ := exists_dnf_of_trees true t hd
    refine ⟨D, true, hD, fun y => ?_⟩
    rw [heval, Bool.eq_iff_iff]
    simp [ht]
  | or m =>
    obtain ⟨D, hD, heval⟩ := exists_dnf_of_trees false t hd
    exact ⟨D, false, hD, fun y => by simp [heval, ht]⟩

/-- **The union bound of a stage.** If there are fewer than `2 ^ s` operation nodes and `ℓ` is at
most a `1 / (16 s + 1)` fraction of the `m` free bits, then the restrictions that the switching
lemma bounds for every node together are fewer than all extensions with `ℓ` free bits. -/
private theorem stage_count {S m ℓ s : ℕ} (hS : S < 2 ^ s) (hs : 1 ≤ s) (hsℓ : s ≤ ℓ)
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

open scoped Classical in
/-- **The switching step for one operation.** If the arguments of an operation are shallow under
`ρ`, few extensions of `ρ` leave it deep. -/
theorem card_filter_not_shallow_le {op : Op} {args : Fin op.arity → BitString n → Bool}
    (h : ∀ j, Shallow s ρ (args j)) (ℓ : ℕ) :
    #{ρ' ∈ ρ.extensions ℓ | ¬ Shallow s ρ' fun x => interpretation op fun j => args j x} ≤
      #(ρ.extensions (ℓ - s)) * (4 * s) ^ s := by
  by_cases hop : op = .not
  · subst hop
    have hG : Shallow s ρ fun x => interpretation .not fun j => args j x := (h 0).not
    rw [filter_false_of_mem fun ρ' hρ' => not_not.2 (hG.mono
      (Restriction.mem_extensions.1 hρ').1)]
    simp
  obtain ⟨D, b, hD, heval⟩ := exists_dnf_of_shallow hop h
  refine (card_le_card fun ρ' hρ' => ?_).trans (DNF.card_switching_le
    (fun t ht => (hD t ht).1.le) (fun t ht => (hD t ht).2) ρ ℓ s)
  obtain ⟨hρ', hdeep⟩ := mem_filter.1 hρ'
  refine mem_filter.2 ⟨hρ', ?_⟩
  have hext := (Restriction.mem_extensions.1 hρ').1
  have : (fun x => DNF.eval (ρ'.fill x) D) =
      fun x => (interpretation op (fun j => args j (ρ.fill (ρ'.fill x))) != b) := by
    funext x
    rw [heval]
  rw [this, complexity_comp_of_injective (g := (· != b)) (by cases b <;> decide)]
  simpa only [Restriction.fill_fill_of_extends hext] using not_lt.1 hdeep

/-- **One stage of restrictions.** Given fewer than `2 ^ s` functions, each an operation applied to
functions that are shallow under `ρ`, and `ℓ ≥ s` at most a `1 / (16 s + 1)` fraction of the free
bits of `ρ`, some extension of `ρ` leaving `ℓ` bits free makes all of them shallow. -/
theorem exists_extension_shallow (T : Finset (BitString n → Bool)) (hT : #T < 2 ^ s) (hs : 1 ≤ s)
    (hgate : ∀ f ∈ T, ∃ (op : Op) (args : Fin op.arity → BitString n → Bool),
      (∀ j, Shallow s ρ (args j)) ∧ f = fun x => interpretation op fun j => args j x)
    {ℓ : ℕ} (hsℓ : s ≤ ℓ) (hℓ : (16 * s + 1) * ℓ ≤ #ρ.free) :
    ∃ ρ' ∈ ρ.extensions ℓ, ∀ f ∈ T, Shallow s ρ' f := by
  classical
  set B : (BitString n → Bool) → Finset (Restriction n) := fun f =>
    {ρ' ∈ ρ.extensions ℓ | ¬ Shallow s ρ' f}
  have hcard : #(T.biUnion B) < #(ρ.extensions ℓ) := by
    calc #(T.biUnion B) ≤ ∑ f ∈ T, #(B f) := card_biUnion_le
      _ ≤ #T * (#(ρ.extensions (ℓ - s)) * (4 * s) ^ s) := by
        refine (sum_le_card_nsmul T _ _ fun f hf => ?_).trans_eq (smul_eq_mul _ _)
        obtain ⟨op, args, hargs, rfl⟩ := hgate f hf
        exact card_filter_not_shallow_le hargs ℓ
      _ < #(ρ.extensions ℓ) := by
        rw [Restriction.card_extensions, Restriction.card_extensions]
        exact stage_count hT hs hsℓ hℓ
  obtain ⟨ρ', hρ', hgood⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨ρ', hρ', fun f hf => ?_⟩
  by_contra hbad
  exact hgood (mem_biUnion.2 ⟨f, hf, mem_filter.2 ⟨hρ', hbad⟩⟩)

/-! ### Circuits -/

/-- The number of free bits after `j` stages. -/
private theorem le_div_pow_of_mul_pow_le {d j : ℕ} (hj : j ≤ d) (hn : s * (16 * s + 1) ^ d ≤ n) :
    s ≤ n / (16 * s + 1) ^ j := by
  have hc : 0 < 16 * s + 1 := by omega
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos hc)]
  calc s * (16 * s + 1) ^ j ≤ s * (16 * s + 1) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hc hj)
    _ ≤ n := hn

/-- One stage shrinks the free bits by the factor `16 s + 1`. -/
private theorem mul_div_pow_succ_le (n s j : ℕ) :
    (16 * s + 1) * (n / (16 * s + 1) ^ (j + 1)) ≤ n / (16 * s + 1) ^ j := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

variable {g : ℕ}

/-- **One stage, for programs.** If every gate of depth at most `j` is shallow under `ρ` and there
are fewer than `2 ^ s` gates, some extension of `ρ` leaving `ℓ` bits free makes every gate of
depth at most `j + 1` shallow. -/
private theorem exists_stage {p : Program signature n g} (hs : 2 ≤ s) (hg : g < 2 ^ s) {j : ℕ}
    (hρ : ∀ k, p.depths k ≤ j → Shallow s ρ fun x => p.eval interpretation x k) {ℓ : ℕ}
    (hsℓ : s ≤ ℓ) (hℓ : (16 * s + 1) * ℓ ≤ #ρ.free) :
    ∃ ρ' ∈ ρ.extensions ℓ, ∀ k, p.depths k ≤ j + 1 →
      Shallow s ρ' fun x => p.eval interpretation x k := by
  classical
  obtain ⟨ρ', hρ', hgood⟩ := exists_extension_shallow
    ((univ.filter fun k => p.depths k = j + 1).image fun k x => p.eval interpretation x k)
    (card_image_le.trans_lt (((card_filter_le _ _).trans_eq (card_fin g)).trans_lt hg))
    (by omega) (fun f hf => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hf
      refine ⟨(p.lines k).op, fun a x => p.trace interpretation x ((p.lines k).wires a),
        fun a => ?_, funext fun x => (p.lines_eval interpretation x k).symm⟩
      change Shallow s ρ fun x => p.trace interpretation x ((p.lines k).wires a)
      have hlt := p.wireDepths_lines_lt k a
      cases hw : (p.lines k).wires a with
      | input i => exact shallow_proj hs ρ i
      | gate k' =>
        rw [hw, Program.wireDepths_gateWire] at hlt
        exact hρ k' (by have := (mem_filter.1 hk).2; omega)) hsℓ hℓ
  refine ⟨ρ', hρ', fun k hk => ?_⟩
  rcases Nat.lt_or_ge (p.depths k) (j + 1) with hlt | hge
  · exact (hρ k (by omega)).mono (Restriction.mem_extensions.1 hρ').1
  · exact hgood _ (mem_image_of_mem _ (mem_filter.2 ⟨mem_univ k, by omega⟩))

/-- **The stages, for programs.** After `j ≤ d` stages, a restriction leaves `n / (16 s + 1) ^ j`
bits free and makes every gate of depth at most `j` shallow. -/
private theorem exists_restriction_stages {p : Program signature n g} (hs : 2 ≤ s)
    (hg : g < 2 ^ s) {d : ℕ} (hn : s * (16 * s + 1) ^ d ≤ n) :
    ∀ j ≤ d, ∃ ρ : Restriction n, #ρ.free = n / (16 * s + 1) ^ j ∧
      ∀ k, p.depths k ≤ j → Shallow s ρ fun x => p.eval interpretation x k
  | 0, _ => ⟨fun _ => none, by simp, fun k hk => absurd hk (by
      have := p.depths_pos k
      omega)⟩
  | j + 1, hj => by
    obtain ⟨ρ, hfree, hρ⟩ := exists_restriction_stages hs hg hn j (by omega)
    obtain ⟨ρ', hρ', hgood⟩ := exists_stage hs hg hρ (le_div_pow_of_mul_pow_le hj hn)
      (hfree ▸ mul_div_pow_succ_le n s j)
    exact ⟨ρ', (Restriction.mem_extensions.1 hρ').2, hgood⟩

/-- **Håstad's theorem** for circuits with unbounded fan-in. A circuit of depth `d` computing the
parity of `n` bits has at least `2 ^ s` gates, for every `s ≥ 2` with `s (16 s + 1) ^ d ≤ n`. -/
theorem two_pow_le_size_of_computes_parity {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s)
    (hn : s * (16 * s + 1) ^ C.depth ≤ n) : 2 ^ s ≤ C.size := by
  by_contra! hS
  obtain ⟨ρ, hfree, hρ⟩ := exists_restriction_stages (p := C.program) hs hS hn C.depth le_rfl
  -- the output is shallow at the end
  have hout : Shallow s ρ fun x => C.program.trace interpretation x (C.outputs 0) := by
    cases hw : C.outputs 0 with
    | input i => exact shallow_proj hs ρ i
    | gate k =>
      refine hρ k ?_
      have := C.outputDepths_le_depth 0
      simp only [Circuit.outputDepths, Function.comp_apply, hw,
        Program.wireDepths_gateWire] at this
      exact this
  have heq : (fun x => C.program.trace interpretation x (C.outputs 0)) = parity n :=
    funext fun x => congrFun (hC x) 0
  rw [heq] at hout
  exact not_shallow_parity (hfree ▸ le_div_pow_of_mul_pow_le le_rfl hn) hout

/-- **Håstad's theorem** for formulas with unbounded fan-in. A formula of depth `d` computing the
parity of `n` bits has at least `2 ^ s` operation nodes, for every `s ≥ 2` with
`s (16 s + 1) ^ d ≤ n`. -/
theorem two_pow_le_size_of_formula_computes_parity {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) (hs : 2 ≤ s)
    (hn : s * (16 * s + 1) ^ F.depth ≤ n) : 2 ^ s ≤ F.size :=
  F.size_toCircuit ▸ two_pow_le_size_of_computes_parity hF.toCircuit hs
    ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) F.depth_toCircuit_le)).trans hn)

end Unbounded

end Cslib.Circuits.Boolean
