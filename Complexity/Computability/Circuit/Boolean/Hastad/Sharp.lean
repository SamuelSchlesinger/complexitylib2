/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Hastad
public import Complexity.Computability.Circuit.Depth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.Data.Nat.Choose
import Complexity.Foundations.Data.Nat.Div
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Håstad's theorem with the sharp exponent

**Håstad's theorem** [Hastad1986], [Jukna, Chapter 12][Jukna2012],
[Arora and Barak, Section 14.1][AroraBarak09] with the exponent `1 / (d - 1)`: a circuit of
negations and unbounded fan-in conjunctions and disjunctions whose AND/OR depth is at most `d`
(the largest number of conjunctions and disjunctions on a path, negations free:
`Circuit.depthWith Unbounded.andOrCost`), computing the parity of `n` bits, has at least `2 ^ s`
conjunctions and disjunctions for every `s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`
(`Unbounded.two_pow_le_card_andOr_of_computes_parity`). In particular it has at least `2 ^ s`
gates whenever `(17 s) ^ (d - 1) ≤ n` and `d ≥ 2`
(`Unbounded.two_pow_le_size_of_computes_parity_of_pow_le`), and at least
`2 ^ (n ^ (1 / (d - 1)) / 17) / 2` gates once `n ≥ 34 ^ (d - 1)`
(`Unbounded.two_rpow_le_two_mul_size_of_computes_parity`), a size `2 ^ Ω(n ^ (1 / (d - 1)))`
with explicit constants. The exponent is optimal: parity has circuits of AND/OR depth `d` with
`2 ^ O(n ^ (1 / (d - 1)))` gates [Hastad1986] (`Unbounded.exists_circuit_of_isSymmetric`). Korten's
top-down argument gives the same exponent with an unspecified constant
(`Unbounded.two_rpow_lt_add_size_of_computes_parity`). Since negations are free, the bound holds
for `Circuit.depth`, which counts them (`Circuit.depthWith_le_depth`,
`Unbounded.two_pow_le_size_of_computes_parity_of_depth_le`), improving the exponent `1 / (d + 1)`
of `Unbounded.two_pow_le_size_of_computes_parity`, and for formulas
(`Unbounded.two_pow_le_size_of_formula_computes_parity_of_depthWith_le`).

The proof refines the one of `Unbounded.two_pow_le_size_of_computes_parity` in three ways.
* Negations are free: the stages are indexed by AND/OR depth, and only conjunctions and
  disjunctions are switched; a negation is shallow when its argument is
  (`Unbounded.shallow_trace_of_forall_andOr`).
* The first stage switches conjunctions and disjunctions of literals, formulas in disjunctive
  normal form with terms of one literal, so it leaves a constant fraction `1 / 17` of the bits
  free rather than `1 / (16 s + 1)` (`Unbounded.two_pow_mul_card_filter_not_shallow_le_of_andOr`
  with `k = 1`).
* There is no last stage: after `d - 1` stages every gate of AND/OR depth at most `d - 1` is
  shallow, so a gate of AND/OR depth `d` is, up to negation, a formula in disjunctive normal form
  with terms of fewer than `s` literals (`Unbounded.exists_dnf_of_shallow`), and such a formula
  cannot compute restricted parity on `s` or more free bits: a satisfied term misses a free bit,
  whose flip keeps it satisfied but flips the parity (`DNF.not_forall_eval_eq_parity_fill_bne`).

## Main results

* `Cslib.Logic.PL.DNF.not_forall_eval_eq_parity_fill_bne`: narrow formulas in disjunctive normal
  form do not compute restricted parity.
* `Cslib.Circuits.Boolean.Unbounded.shallow_trace_of_forall_andOr`: negations keep wires shallow.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_not_shallow_le_of_andOr`: the
  switching fraction for a conjunction or disjunction of functions of decision tree depth at
  most `k`.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_exists_not_shallow_le_andOr`: random
  restrictions make the gates of small AND/OR depth shallow, stage by stage.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_card_andOr_of_computes_parity`: Håstad's theorem
  with the sharp exponent, counting conjunctions and disjunctions.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_depthWith_le`,
  `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_pow_le`,
  `Cslib.Circuits.Boolean.Unbounded.two_rpow_le_two_mul_size_of_computes_parity`: the same for the
  number of gates.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_depth_le`: the same when
  depth counts negations.
* `Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_formula_computes_parity_of_depthWith_le`:
  the same for formulas.

## References

* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.BitString Finset

variable {n : ℕ} {ρ : PartialAssignment (Fin n)}

/-! ### Formulas in disjunctive normal form for restricted parity -/

/-- **Narrow formulas in disjunctive normal form miss restricted parity.** If every term of `D` has
fewer literals than `ρ` has free bits, and `ρ` has a free bit, then `D` does not compute the parity
of the bits filled in by `ρ`, up to negation: a satisfied term misses a free bit, and flipping it
keeps the term satisfied but flips the parity. -/
theorem DNF.not_forall_eval_eq_parity_fill_bne {D : DNF (Fin n)}
    (hD : ∀ t ∈ D, t.length < #ρ.free) (hρ : ρ.free.Nonempty) (c : Bool) :
    ¬ ∀ y, DNF.eval y D = (parity n (ρ.fill y) != c) := by
  intro h
  -- flipping a free bit flips restricted parity
  have hflip : ∀ y i, i ∈ ρ.free →
      parity n (ρ.fill (Function.update y i !y i)) = !parity n (ρ.fill y) := by
    intro y i hi
    have : ρ.fill (Function.update y i !y i) = Function.update (ρ.fill y) i !ρ.fill y i := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [PartialAssignment.fill, PartialAssignment.mem_free.1 hi]
      · simp [PartialAssignment.fill, hj]
    rw [this, parity_update_not]
  -- some input makes the right side true
  obtain ⟨i₀, hi₀⟩ := hρ
  obtain ⟨y, hy⟩ : ∃ y, (parity n (ρ.fill y) != c) = true := by
    by_cases h0 : (parity n (ρ.fill fun _ => false) != c) = true
    · exact ⟨_, h0⟩
    · refine ⟨Function.update (fun _ => false) i₀ (!false), ?_⟩
      rw [hflip _ i₀ hi₀]
      revert h0
      cases parity n (ρ.fill fun _ => false) <;> cases c <;> simp
  obtain ⟨t, ht, hty⟩ := (DNF.eval_eq_true_iff y D).1 ((h y).trans hy)
  -- the term misses a free bit
  obtain ⟨i, hi, hit⟩ : ∃ i ∈ ρ.free, i ∉ t.map Prod.fst := by
    by_contra! hsub
    have hle : #ρ.free ≤ t.length :=
      (card_le_card fun i hi => List.mem_toFinset.2 (hsub i hi)).trans
        ((List.toFinset_card_le _).trans_eq (by simp))
    exact absurd (hD t ht) (by omega)
  have hty' : t.eval (Function.update y i !y i) = true := by
    refine (Term.eval_eq_true_iff _ _).2 fun l hl => ?_
    have hli : l.1 ≠ i := fun hli => hit (List.mem_map.2 ⟨l, hl, hli⟩)
    rw [Function.update_of_ne hli]
    exact (Term.eval_eq_true_iff y t).1 hty l hl
  have h1 := (h _).symm.trans ((DNF.eval_eq_true_iff _ D).2 ⟨t, ht, hty'⟩)
  rw [hflip y i hi] at h1
  revert hy h1
  cases parity n (ρ.fill y) <;> cases c <;> simp

end Cslib.Logic.PL

namespace Cslib.Circuits.Boolean

open Cslib.BitString Cslib.DecisionTree Cslib.Logic.PL Finset

variable {n s : ℕ} {ρ : PartialAssignment (Fin n)}

/-- A function shallow for one bound is shallow for every larger bound. -/
theorem Shallow.of_le {f : BitString n → Bool} {s' : ℕ} (h : Shallow s ρ f) (hs : s ≤ s') :
    Shallow s' ρ f :=
  lt_of_lt_of_le h hs

namespace Unbounded

/-- Conjunctions and disjunctions cost one in the AND/OR depth. -/
theorem andOrCost_eq_one {op : Op} (hop : op ≠ .not) : andOrCost op = 1 := by
  cases op <;> simp_all

/-- A negation computes the negation of one of its arguments. -/
private theorem exists_interpretation_eq_not {op : Op} (hop : op = .not) :
    ∃ a : Fin op.arity, ∀ args : Fin op.arity → Bool, interpretation op args = !args a := by
  subst hop
  exact ⟨0, fun _ => rfl⟩

/-! ### One conjunction or disjunction -/

/-- **The switching step for a conjunction or disjunction.** If the arguments of a conjunction or
disjunction have decision tree depth at most `k` under `ρ`, at most `#E(ℓ - s) (4k)^s` of the
extensions of `ρ` with `ℓ` free bits leave it `s`-deep, where `E(m)` are the extensions of `ρ` with
`m` free bits. -/
theorem card_filter_not_shallow_le_of_andOr {op : Op} (hop : op ≠ .not) {k : ℕ}
    {args : Fin op.arity → BitString n → Bool} (h : ∀ j, Shallow (k + 1) ρ (args j)) (ℓ s : ℕ) :
    #{ρ' ∈ ρ.extensions ℓ | ¬ Shallow s ρ' fun x => interpretation op fun j => args j x} ≤
      #(ρ.extensions (ℓ - s)) * (4 * k) ^ s := by
  obtain ⟨D, b, hD, heval⟩ := exists_dnf_of_shallow hop h
  refine (card_le_card fun ρ' hρ' => ?_).trans (DNF.card_switching_le
    (fun t ht => Nat.lt_succ_iff.1 (hD t ht).1) (fun t ht => (hD t ht).2) ρ ℓ s)
  obtain ⟨hρ', hdeep⟩ := mem_filter.1 hρ'
  refine mem_filter.2 ⟨hρ', ?_⟩
  have hext := (PartialAssignment.mem_extensions.1 hρ').1
  have : (fun x => DNF.eval (ρ'.fill x) D) =
      (· != b) ∘ fun x => interpretation op (fun j => args j (ρ.fill (ρ'.fill x))) := by
    funext x
    rw [heval, Function.comp_apply]
  rw [this, complexity_comp_of_injective (by cases b <;> decide)]
  simpa only [PartialAssignment.fill_fill_of_extends hext] using not_lt.1 hdeep

/-- **The switching fraction for a conjunction or disjunction**: if its arguments have decision
tree depth at most `k` under `ρ`, at most a `2 ^ (-s)` fraction of the extensions of `ρ` with `ℓ`
free bits leave it `s`-deep, when `s ≤ ℓ` and `ℓ` is at most a `1 / (16 k + 1)` fraction of the
free bits of `ρ`. For arguments that are literals, `k = 1` and the fraction is `1 / 17`. -/
theorem two_pow_mul_card_filter_not_shallow_le_of_andOr {op : Op} (hop : op ≠ .not) {k : ℕ}
    {args : Fin op.arity → BitString n → Bool} (h : ∀ j, Shallow (k + 1) ρ (args j)) {ℓ : ℕ}
    (hsℓ : s ≤ ℓ) (hℓ : (16 * k + 1) * ℓ ≤ #ρ.free) :
    2 ^ s * #{ρ' ∈ ρ.extensions ℓ | ¬ Shallow s ρ' fun x => interpretation op fun j => args j x} ≤
      #(ρ.extensions ℓ) := by
  refine (Nat.mul_le_mul_left _ (card_filter_not_shallow_le_of_andOr hop h ℓ s)).trans ?_
  rw [PartialAssignment.card_extensions, PartialAssignment.card_extensions]
  set m := #ρ.free
  have hℓm : ℓ ≤ m := le_trans (Nat.le_mul_of_pos_left ℓ (by omega)) hℓ
  have h2 : 2 ^ (m - (ℓ - s)) = 2 ^ (m - ℓ) * 2 ^ s := by
    rw [← pow_add]
    congr 1
    omega
  calc 2 ^ s * (m.choose (ℓ - s) * 2 ^ (m - (ℓ - s)) * (4 * k) ^ s)
      = (16 * k) ^ s * m.choose (ℓ - s) * 2 ^ (m - ℓ) := by
        rw [h2, show (16 * k) ^ s = 2 ^ s * 2 ^ s * (4 * k) ^ s by
          rw [← mul_pow, ← mul_pow]; ring_nf]
        ring
    _ ≤ m.choose ℓ * 2 ^ (m - ℓ) :=
        Nat.mul_le_mul_right _ (Nat.pow_mul_choose_sub_le_choose_of_mul_le hsℓ hℓ)

/-! ### Programs, with free negations -/

variable {g : ℕ}

/-- Induction along the wires of a program: a property of the inputs that passes from the wires a
gate reads to the gate holds of every wire. -/
private theorem wire_induction {σ : Signature} {p : Program σ n g} {Q : Wire n g → Prop}
    (input : ∀ i, Q (.input i)) (gate : ∀ k, (∀ a, Q ((p.lines k).wires a)) → Q (.gate k))
    (w : Wire n g) : Q w := by
  suffices h : ∀ m w, p.wireDepths w ≤ m → Q w from h _ w le_rfl
  intro m
  induction m with
  | zero =>
    rintro (i | k) hw
    · exact input i
    · have := p.depths_pos k
      rw [Program.wireDepths_gateWire] at hw
      omega
  | succ m ih =>
    rintro (i | k) hw
    · exact input i
    · refine gate k fun a => ih _ ?_
      have := p.wireDepths_lines_lt k a
      rw [Program.wireDepths_gateWire] at hw
      omega

/-- The wires a conjunction or disjunction reads have smaller AND/OR depth. -/
private theorem wireDepthsWith_lines_lt {p : Program signature n g} {k : Fin g}
    (hop : (p.lines k).op ≠ .not) (a : Fin (p.lines k).op.arity) :
    p.wireDepthsWith andOrCost ((p.lines k).wires a) + 1 ≤ p.depthsWith andOrCost k := by
  have h := p.wireDepthsWith_lines_add_le andOrCost k a
  rwa [andOrCost_eq_one hop] at h

/-- If every conjunction and disjunction of AND/OR depth at most `j` is shallow under `ρ`, so is
every wire of AND/OR depth at most `j`: inputs are shallow, and negations keep functions
shallow. -/
theorem shallow_trace_of_forall_andOr {p : Program signature n g} (hs : 2 ≤ s) {j : ℕ}
    (h : ∀ k, (p.lines k).op ≠ .not → p.depthsWith andOrCost k ≤ j →
      Shallow s ρ fun x => p.eval interpretation x k)
    (w : Wire n g) (hw : p.wireDepthsWith andOrCost w ≤ j) :
    Shallow s ρ fun x => p.trace interpretation x w := by
  refine wire_induction (p := p) (Q := fun w => p.wireDepthsWith andOrCost w ≤ j →
    Shallow s ρ fun x => p.trace interpretation x w) (fun i _ => shallow_proj hs ρ i) ?_ w hw
  intro k ih hk
  by_cases hop : (p.lines k).op = .not
  · obtain ⟨a, ha⟩ := exists_interpretation_eq_not hop
    have heq : (fun x => p.trace interpretation x (.gate k)) =
        fun x => !p.trace interpretation x ((p.lines k).wires a) :=
      funext fun x => (p.lines_eval interpretation x k).symm.trans
        (ha fun a => p.trace interpretation x ((p.lines k).wires a))
    rw [heq]
    exact (ih a ((Nat.le_add_right _ _).trans
      ((p.wireDepthsWith_lines_add_le andOrCost k a).trans hk))).not
  · exact h k hop hk

/-- Every wire of AND/OR depth zero, a literal, has decision tree depth at most one under every
restriction. -/
theorem shallow_two_trace_of_wireDepthsWith_eq_zero {p : Program signature n g}
    (ρ : PartialAssignment (Fin n)) (w : Wire n g) (hw : p.wireDepthsWith andOrCost w = 0) :
    Shallow 2 ρ fun x => p.trace interpretation x w :=
  shallow_trace_of_forall_andOr le_rfl (fun k hop hk => absurd hk (by
    have := p.cost_le_depthsWith andOrCost k
    rw [andOrCost_eq_one hop] at this
    omega)) w hw.le

/-- **One stage, counted, with free negations.** Let `1 ≤ k < s`. If every gate of AND/OR depth at
most `j` has decision tree depth at most `k` under `ρ`, at most an `H / 2 ^ s` fraction of the
extensions of `ρ` with `ℓ'` free bits make some gate of AND/OR depth at most `j + 1` `s`-deep,
where `H` is the number of conjunctions and disjunctions of AND/OR depth `j + 1`, when `s ≤ ℓ'`
and `(16 k + 1) ℓ'` is at most the number of free bits of `ρ`. -/
private theorem two_pow_mul_card_filter_extensions_le_andOr {p : Program signature n g}
    {k j ℓ' : ℕ} (hk : 1 ≤ k) (hks : k + 1 ≤ s) (hsℓ' : s ≤ ℓ')
    (hℓ : (16 * k + 1) * ℓ' ≤ #ρ.free)
    (hgood : ∀ k', p.depthsWith andOrCost k' ≤ j →
      Shallow (k + 1) ρ fun x => p.eval interpretation x k') :
    2 ^ s * #{ρ' ∈ ρ.extensions ℓ' | ∃ k', p.depthsWith andOrCost k' ≤ j + 1 ∧
        ¬ Shallow s ρ' fun x => p.eval interpretation x k'} ≤
      #{k' | (p.lines k').op ≠ .not ∧ p.depthsWith andOrCost k' = j + 1} *
        #(ρ.extensions ℓ') := by
  set T : Finset (Fin g) := {k' | (p.lines k').op ≠ .not ∧ p.depthsWith andOrCost k' = j + 1}
  -- a bad extension makes a conjunction or disjunction of AND/OR depth exactly `j + 1` deep
  have hsub : {ρ' ∈ ρ.extensions ℓ' | ∃ k', p.depthsWith andOrCost k' ≤ j + 1 ∧
      ¬ Shallow s ρ' fun x => p.eval interpretation x k'} ⊆
      T.biUnion fun k' => {ρ' ∈ ρ.extensions ℓ' |
        ¬ Shallow s ρ' fun x => p.eval interpretation x k'} := by
    intro ρ' hρ'
    obtain ⟨hext, k₀, hk₀, hdeep⟩ := mem_filter.1 hρ'
    have hext' := (PartialAssignment.mem_extensions.1 hext).1
    by_contra hnot
    refine hdeep (shallow_trace_of_forall_andOr (by omega) (j := j + 1) (fun k' hop hk' => ?_)
      (.gate k₀) hk₀)
    by_cases hk'j : p.depthsWith andOrCost k' ≤ j
    · exact ((hgood k' hk'j).of_le hks).mono hext'
    · by_contra hdeep'
      exact hnot (mem_biUnion.2 ⟨k', mem_filter.2 ⟨mem_univ _, hop, by omega⟩,
        mem_filter.2 ⟨hext, hdeep'⟩⟩)
  calc 2 ^ s * #{ρ' ∈ ρ.extensions ℓ' | ∃ k', p.depthsWith andOrCost k' ≤ j + 1 ∧
        ¬ Shallow s ρ' fun x => p.eval interpretation x k'}
      ≤ 2 ^ s * ∑ k' ∈ T, #{ρ' ∈ ρ.extensions ℓ' |
          ¬ Shallow s ρ' fun x => p.eval interpretation x k'} :=
        Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ k' ∈ T, 2 ^ s * #{ρ' ∈ ρ.extensions ℓ' |
          ¬ Shallow s ρ' fun x => p.eval interpretation x k'} := mul_sum _ _ _
    _ ≤ ∑ _k' ∈ T, #(ρ.extensions ℓ') := sum_le_sum fun k' hk' => by
        obtain ⟨hop, hdk⟩ := (mem_filter.1 hk').2
        -- gate `k'` is its operation on wires of AND/OR depth at most `j`
        have hgate : (fun x => p.eval interpretation x k') = fun x =>
            interpretation (p.lines k').op fun a =>
              p.trace interpretation x ((p.lines k').wires a) :=
          funext fun x => (p.lines_eval interpretation x k').symm
        rw [hgate]
        refine two_pow_mul_card_filter_not_shallow_le_of_andOr hop (fun a => ?_) hsℓ' hℓ
        have hlt := wireDepthsWith_lines_lt hop a
        cases hw : (p.lines k').wires a with
        | input i => exact shallow_proj (by omega) ρ i
        | gate k'' =>
          rw [hw, Program.wireDepthsWith_gateWire] at hlt
          exact hgood k'' (by omega)
    _ = #T * #(ρ.extensions ℓ') := by rw [sum_const, smul_eq_mul]

/-- **Two stages of restrictions, counted.** Drawing a restriction with `ℓ'` free bits by first
drawing one with `ℓ ≥ ℓ'` free bits and then an extension of it: if at most a `G / c` fraction of
the restrictions with `ℓ` free bits satisfy `B`, and for each other one at most an `H / c` fraction
of its extensions with `ℓ'` free bits satisfy `B'`, then at most a `(G + H) / c` fraction of the
restrictions with `ℓ'` free bits satisfy `B'`. -/
private theorem mul_card_filter_withFree_le {c G H G' ℓ ℓ' : ℕ} (hℓ'ℓ : ℓ' ≤ ℓ) (hℓn : ℓ ≤ n)
    {B B' : PartialAssignment (Fin n) → Prop} [DecidablePred B] [DecidablePred B']
    (h₁ : c * #{ρ ∈ PartialAssignment.withFree (Fin n) ℓ | B ρ} ≤
      G * #(PartialAssignment.withFree (Fin n) ℓ))
    (h₂ : ∀ ρ ∈ PartialAssignment.withFree (Fin n) ℓ, ¬ B ρ →
      c * #{ρ' ∈ ρ.extensions ℓ' | B' ρ'} ≤ H * #(ρ.extensions ℓ'))
    (hG : G + H ≤ G') :
    c * #{ρ ∈ PartialAssignment.withFree (Fin n) ℓ' | B' ρ} ≤
      G' * #(PartialAssignment.withFree (Fin n) ℓ') := by
  set W := PartialAssignment.withFree (Fin n) ℓ
  set F := (n - ℓ').choose (ℓ - ℓ')
  have hF : 0 < F := Nat.choose_pos (by omega)
  set T := ℓ.choose ℓ' * 2 ^ (ℓ - ℓ')
  have hT : ∀ ρ ∈ W, #(ρ.extensions ℓ') = T := fun ρ hρ => by
    rw [PartialAssignment.card_extensions, PartialAssignment.mem_withFree.1 hρ]
  -- each restriction with `ℓ` free bits has few bad extensions, unless it satisfies `B`
  have hper : ∀ ρ ∈ W, c * #{ρ' ∈ ρ.extensions ℓ' | B' ρ'} ≤
      (if B ρ then c else 0) * T + H * T := fun ρ hρ => by
    by_cases hb : B ρ
    · simp only [hb, ↓reduceIte]
      rw [← hT ρ hρ]
      exact (Nat.mul_le_mul_left _ (card_filter_le _ _)).trans (Nat.le_add_right _ _)
    · simp only [hb, ↓reduceIte, zero_mul, zero_add]
      rw [← hT ρ hρ]
      exact h₂ ρ hρ hb
  -- double counting the extensions, with and without the condition
  have hdc := PartialAssignment.sum_card_filter_extensions B' hℓ'ℓ
  have hall := PartialAssignment.sum_card_filter_extensions (ι := Fin n) (fun _ => True) hℓ'ℓ
  simp only [filter_true] at hall
  rw [Fintype.card_fin] at hdc hall
  rw [sum_congr rfl hT, sum_const, smul_eq_mul] at hall
  refine Nat.le_of_mul_le_mul_right (?_ : _ * F ≤ _ * F) hF
  calc c * #{ρ ∈ PartialAssignment.withFree (Fin n) ℓ' | B' ρ} * F
      = ∑ ρ ∈ W, c * #{ρ' ∈ ρ.extensions ℓ' | B' ρ'} := by
        rw [mul_assoc, ← hdc, mul_sum]
    _ ≤ ∑ ρ ∈ W, ((if B ρ then c else 0) * T + H * T) := sum_le_sum hper
    _ = c * #{ρ ∈ W | B ρ} * T + #W * H * T := by
        rw [sum_add_distrib, ← sum_mul, sum_ite, sum_const_zero, add_zero, sum_const,
          smul_eq_mul, sum_const, smul_eq_mul]
        ring
    _ ≤ G * #W * T + #W * H * T := by gcongr
    _ = (G + H) * #(PartialAssignment.withFree (Fin n) ℓ') * F := by
        rw [mul_assoc _ #(PartialAssignment.withFree (Fin n) ℓ'), ← hall]
        ring
    _ ≤ G' * #(PartialAssignment.withFree (Fin n) ℓ') * F := by gcongr

/-- **Random restrictions make the gates of small AND/OR depth shallow.** For `s ≥ 2` and
`s (16 s + 1) ^ e ≤ ⌊n / 17⌋`, after a first stage leaving `⌊n / 17⌋` bits free and `i ≤ e` more
stages each leaving a `1 / (16 s + 1)` fraction of the free bits, at most a `G / 2 ^ s` fraction of
the restrictions make some gate of AND/OR depth at most `i + 1` `s`-deep, where `G` is the number
of conjunctions and disjunctions of AND/OR depth at most `i + 1`. -/
theorem two_pow_mul_card_filter_exists_not_shallow_le_andOr {p : Program signature n g}
    (hs : 2 ≤ s) {e : ℕ} (hn : s * (16 * s + 1) ^ e ≤ n / 17) (i : ℕ) (hi : i ≤ e) :
    2 ^ s * #{ρ ∈ PartialAssignment.withFree (Fin n) (n / 17 / (16 * s + 1) ^ i) |
        ∃ k, p.depthsWith andOrCost k ≤ i + 1 ∧
          ¬ Shallow s ρ fun x => p.eval interpretation x k} ≤
      #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k ≤ i + 1} *
        #(PartialAssignment.withFree (Fin n) (n / 17 / (16 * s + 1) ^ i)) := by
  have hsm : s ≤ n / 17 / (16 * s + 1) ^ i := Nat.le_div_pow_of_mul_pow_le (by omega) hi hn
  induction i with
  | zero =>
    -- the first stage switches conjunctions and disjunctions of literals
    rw [pow_zero, Nat.div_one] at hsm ⊢
    refine mul_card_filter_withFree_le (B := fun _ => False) (G := 0)
      (H := #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k = 0 + 1})
      (Nat.div_le_self n 17) le_rfl (by simp) (fun ρ hρ _ => ?_) ?_
    · refine two_pow_mul_card_filter_extensions_le_andOr (k := 1) (j := 0) le_rfl hs hsm
        (by rw [PartialAssignment.mem_withFree.1 hρ]; omega) fun k' hk' => ?_
      exact shallow_two_trace_of_wireDepthsWith_eq_zero ρ (.gate k') (Nat.le_zero.1 hk')
    · rw [zero_add]
      refine card_le_card fun k hk => ?_
      simp only [mem_filter, mem_univ, true_and] at hk ⊢
      exact ⟨hk.1, hk.2.le⟩
  | succ i ih =>
    have ih := ih (by omega) (Nat.le_div_pow_of_mul_pow_le (by omega) (by omega) hn)
    set ℓ := n / 17 / (16 * s + 1) ^ i
    set ℓ' := n / 17 / (16 * s + 1) ^ (i + 1)
    have hℓ : (16 * s + 1) * ℓ' ≤ ℓ := Nat.mul_div_pow_succ_le (n / 17) _ i
    have hℓn : ℓ ≤ n := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
    have hℓ'ℓ : ℓ' ≤ ℓ := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hℓ
    -- the conjunctions and disjunctions of AND/OR depth at most `i + 2`
    have hG : #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k ≤ i + 1} +
        #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k = i + 1 + 1} ≤
        #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k ≤ i + 1 + 1} := by
      rw [← card_union_of_disjoint (disjoint_filter.2 fun k _ h₁ h₂ => by
        have := h₁.2
        have := h₂.2
        omega)]
      refine card_le_card fun k hk => ?_
      simp only [mem_union, mem_filter, mem_univ, true_and] at hk ⊢
      rcases hk with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨h₁, by omega⟩
      · exact ⟨h₁, h₂.le⟩
    refine mul_card_filter_withFree_le hℓ'ℓ hℓn ih (fun ρ hρ hb => ?_) hG
    -- a later stage switches conjunctions and disjunctions of shallow functions
    have hρℓ := PartialAssignment.mem_withFree.1 hρ
    refine two_pow_mul_card_filter_extensions_le_andOr (k := s - 1) (j := i + 1) (by omega)
      (by omega) hsm ?_ fun k' hk' => ?_
    · rw [hρℓ]
      refine le_trans (Nat.mul_le_mul_right _ (by omega)) hℓ
    · rw [Nat.sub_add_cancel (by omega)]
      by_contra hdeep
      exact hb ⟨k', hk', hdeep⟩

/-- Under a restriction leaving at least `s ≥ 2` bits free and making every gate of AND/OR depth at
most `j` `s`-shallow, no wire of AND/OR depth at most `j + 1` computes restricted parity, up to
negation. -/
private theorem not_forall_trace_fill_eq_parity_bne {p : Program signature n g} (hs : 2 ≤ s)
    (hsρ : s ≤ #ρ.free) {j : ℕ}
    (h : ∀ k, p.depthsWith andOrCost k ≤ j → Shallow s ρ fun x => p.eval interpretation x k)
    (w : Wire n g) (hw : p.wireDepthsWith andOrCost w ≤ j + 1) (b : Bool) :
    ¬ ∀ y, p.trace interpretation (ρ.fill y) w = (parity n (ρ.fill y) != b) := by
  refine wire_induction (p := p) (Q := fun w => p.wireDepthsWith andOrCost w ≤ j + 1 → ∀ b,
    ¬ ∀ y, p.trace interpretation (ρ.fill y) w = (parity n (ρ.fill y) != b)) ?_ ?_ w hw b
  · -- an input is shallow, restricted parity is not
    intro i _ b hi
    have heq : (fun y => ρ.fill y i) = fun y => parity n (ρ.fill y) != b := funext hi
    have h₁ : Shallow s ρ fun x => parity n x != b := by
      change DecisionTree.complexity (fun y => parity n (ρ.fill y) != b) < s
      rw [← heq]
      exact shallow_proj hs ρ i
    refine not_shallow_parity hsρ ?_
    cases b
    · simpa using h₁
    · simpa using h₁.not
  · intro k ih hk b hk'
    by_cases hop : (p.lines k).op = .not
    · -- a negation computes restricted parity exactly when its argument computes its negation
      obtain ⟨a, ha⟩ := exists_interpretation_eq_not hop
      refine ih a ((Nat.le_add_right _ _).trans
        ((p.wireDepthsWith_lines_add_le andOrCost k a).trans hk)) (!b) fun y => ?_
      have hy : p.trace interpretation (ρ.fill y) (.gate k) =
          !p.trace interpretation (ρ.fill y) ((p.lines k).wires a) :=
        (p.lines_eval interpretation (ρ.fill y) k).symm.trans
          (ha fun a => p.trace interpretation (ρ.fill y) ((p.lines k).wires a))
      have := hy.symm.trans (hk' y)
      revert this
      cases p.trace interpretation (ρ.fill y) ((p.lines k).wires a) <;>
        cases parity n (ρ.fill y) <;> cases b <;> simp
    · -- a conjunction or disjunction of shallow functions is a narrow formula in disjunctive
      -- normal form, up to negation
      have hargs : ∀ a, Shallow s ρ fun x => p.trace interpretation x ((p.lines k).wires a) :=
        fun a => by
          have hlt := wireDepthsWith_lines_lt hop a
          cases hw' : (p.lines k).wires a with
          | input i => exact shallow_proj hs ρ i
          | gate k' =>
            rw [hw', Program.wireDepthsWith_gateWire] at hlt
            exact h k' (by change p.depthsWith andOrCost k ≤ j + 1 at hk; omega)
      obtain ⟨D, b', hD, heval⟩ := exists_dnf_of_shallow hop hargs
      refine DNF.not_forall_eval_eq_parity_fill_bne (fun t ht => (hD t ht).1.trans_le hsρ)
        (card_pos.1 (by omega)) (b != b') fun y => ?_
      have hy : interpretation (p.lines k).op
          (fun a => p.trace interpretation (ρ.fill y) ((p.lines k).wires a)) =
          (parity n (ρ.fill y) != b) :=
        (p.lines_eval interpretation (ρ.fill y) k).trans (hk' y)
      rw [heval y, hy]
      cases parity n (ρ.fill y) <;> cases b <;> cases b' <;> rfl

/-! ### Håstad's theorem -/

/-- **Håstad's theorem with the sharp exponent**, for programs: if a wire of AND/OR depth at most
`d` computes the parity of `n` bits, the program has at least `2 ^ s` conjunctions and
disjunctions, for every `s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
theorem two_pow_le_card_andOr_of_trace_eq_parity {p : Program signature n g} {w : Wire n g}
    (hw : ∀ x, p.trace interpretation x w = parity n x) (hs : 2 ≤ s) {d : ℕ}
    (hd : p.wireDepthsWith andOrCost w ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) :
    2 ^ s ≤ #{k | (p.lines k).op ≠ .not} := by
  by_contra! hS
  set e := d - 2
  set ℓ := n / 17 / (16 * s + 1) ^ e
  have hm : s * (16 * s + 1) ^ e ≤ n / 17 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by linarith)
  have hsℓ : s ≤ ℓ := Nat.le_div_pow_of_mul_pow_le (by omega) le_rfl hm
  -- fewer than all restrictions leaving `ℓ` bits free make some gate deep
  have h := two_pow_mul_card_filter_exists_not_shallow_le_andOr (p := p) hs hm e le_rfl
  have hW : 0 < #(PartialAssignment.withFree (Fin n) ℓ) := by
    rw [PartialAssignment.card_withFree, Fintype.card_fin]
    exact Nat.mul_pos (Nat.choose_pos ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _)))
      (by positivity)
  have hcard : #{k | (p.lines k).op ≠ .not ∧ p.depthsWith andOrCost k ≤ e + 1} ≤
      #{k | (p.lines k).op ≠ .not} :=
    card_le_card fun k hk => by
      simp only [mem_filter, mem_univ, true_and] at hk ⊢
      exact hk.1
  have hlt : #{ρ ∈ PartialAssignment.withFree (Fin n) ℓ | ∃ k, p.depthsWith andOrCost k ≤ e + 1 ∧
      ¬ Shallow s ρ fun x => p.eval interpretation x k} <
      #(PartialAssignment.withFree (Fin n) ℓ) := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ s) (h.trans_lt ?_)
    exact Nat.mul_lt_mul_of_pos_right (hcard.trans_lt hS) hW
  obtain ⟨ρ, hρ, hgood⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hall : ∀ k, p.depthsWith andOrCost k ≤ e + 1 →
      Shallow s ρ fun x => p.eval interpretation x k := fun k hk => by
    by_contra hdeep
    exact hgood (mem_filter.2 ⟨hρ, k, hk, hdeep⟩)
  exact not_forall_trace_fill_eq_parity_bne hs ((PartialAssignment.mem_withFree.1 hρ).symm ▸ hsℓ)
    hall w (by omega) false fun y => by rw [hw, Bool.bne_false]

/-- **Håstad's theorem with the sharp exponent**, counting conjunctions and disjunctions. A circuit
of negations and unbounded fan-in conjunctions and disjunctions of AND/OR depth at most `d`
computing the parity of `n` bits has at least `2 ^ s` conjunctions and disjunctions, for every
`s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
theorem two_pow_le_card_andOr_of_computes_parity {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s) {d : ℕ}
    (hd : C.depthWith andOrCost ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) :
    2 ^ s ≤ #{k | (C.program.lines k).op ≠ .not} :=
  two_pow_le_card_andOr_of_trace_eq_parity (fun x => congrFun (hC x) 0) hs
    ((C.wireDepthsWith_outputs_le_depthWith andOrCost 0).trans hd) hn

/-- **Håstad's theorem with the sharp exponent.** A circuit of negations and unbounded fan-in
conjunctions and disjunctions of AND/OR depth at most `d` computing the parity of `n` bits has at
least `2 ^ s` gates, for every `s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
theorem two_pow_le_size_of_computes_parity_of_depthWith_le {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s) {d : ℕ}
    (hd : C.depthWith andOrCost ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) :
    2 ^ s ≤ C.size :=
  (two_pow_le_card_andOr_of_computes_parity hC hs hd hn).trans
    ((card_filter_le _ _).trans (by simp))

/-- **Håstad's theorem with the sharp exponent**, in round numbers. A circuit of negations and
unbounded fan-in conjunctions and disjunctions of AND/OR depth at most `d ≥ 2` computing the
parity of `n` bits has at least `2 ^ s` gates, for every `s ≥ 2` with `(17 s) ^ (d - 1) ≤ n`. -/
theorem two_pow_le_size_of_computes_parity_of_pow_le {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s) {d : ℕ} (hd₂ : 2 ≤ d)
    (hd : C.depthWith andOrCost ≤ d) (hn : (17 * s) ^ (d - 1) ≤ n) : 2 ^ s ≤ C.size := by
  refine two_pow_le_size_of_computes_parity_of_depthWith_le hC hs hd (le_trans ?_ hn)
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  rw [show e + 2 - 2 = e by omega, show e + 2 - 1 = e + 1 by omega, pow_succ']
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) e)

/-- **Håstad's theorem with the sharp exponent**, as a real bound. A circuit of negations and
unbounded fan-in conjunctions and disjunctions of AND/OR depth at most `d ≥ 2` computing the
parity of `n ≥ 34 ^ (d - 1)` bits has at least `2 ^ (n ^ (1 / (d - 1)) / 17) / 2` gates. -/
theorem two_rpow_le_two_mul_size_of_computes_parity {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) {d : ℕ} (hd₂ : 2 ≤ d)
    (hd : C.depthWith andOrCost ≤ d) (hn : 34 ^ (d - 1) ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 17) ≤ 2 * C.size := by
  set r := (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)
  have hd1 : d - 1 ≠ 0 := by omega
  have hr : r ^ (d - 1) = n := Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) hd1
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg n) _
  -- `r ≥ 34`
  have hr34 : 34 ≤ r := by
    have h34 : ((34 : ℝ) ^ (d - 1)) ^ (((d - 1 : ℕ) : ℝ)⁻¹) = 34 :=
      Real.pow_rpow_inv_natCast (by norm_num) hd1
    rw [← h34]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) (by positivity)
  set s := ⌊r / 17⌋₊
  have hs : 2 ≤ s := Nat.le_floor (by norm_num; linarith)
  have hsr : (17 * s : ℝ) ≤ r := by
    have := Nat.floor_le (a := r / 17) (by positivity)
    linarith
  have hsn : (17 * s) ^ (d - 1) ≤ n := by
    have : ((17 * s : ℕ) : ℝ) ^ (d - 1) ≤ r ^ (d - 1) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hsr) _
    rw [hr] at this
    exact_mod_cast this
  have hsize : (2 : ℝ) ^ s ≤ C.size := by
    exact_mod_cast two_pow_le_size_of_computes_parity_of_pow_le hC hs hd₂ hd hsn
  calc (2 : ℝ) ^ (r / 17) ≤ 2 ^ ((s + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by push_cast; exact (Nat.lt_floor_add_one _).le)
    _ = 2 * 2 ^ s := by rw [Real.rpow_natCast, pow_succ']
    _ ≤ 2 * C.size := by linarith

/-- **Håstad's theorem with the sharp exponent, when depth counts negations.** A circuit of
negations and unbounded fan-in conjunctions and disjunctions of depth at most `d` computing the
parity of `n` bits has at least `2 ^ s` gates, for every `s ≥ 2` with
`17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
theorem two_pow_le_size_of_computes_parity_of_depth_le {C : Circuit signature n 1}
    (hC : C.Computes interpretation (single (parity n))) (hs : 2 ≤ s) {d : ℕ}
    (hd : C.depth ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) : 2 ^ s ≤ C.size :=
  two_pow_le_size_of_computes_parity_of_depthWith_le hC hs
    ((C.depthWith_le_depth andOrCost_le_one).trans hd) hn

/-- **Håstad's theorem with the sharp exponent, for formulas.** A formula of negations and unbounded
fan-in conjunctions and disjunctions of AND/OR depth at most `d` computing the parity of `n` bits
has at least `2 ^ s` operation nodes, for every `s ≥ 2` with `17 s (16 s + 1) ^ (d - 2) ≤ n`. -/
theorem two_pow_le_size_of_formula_computes_parity_of_depthWith_le {F : Formula signature n}
    (hF : F.Computes interpretation (parity n)) (hs : 2 ≤ s) {d : ℕ}
    (hd : F.depthWith andOrCost ≤ d) (hn : 17 * s * (16 * s + 1) ^ (d - 2) ≤ n) :
    2 ^ s ≤ F.size :=
  F.size_toCircuit ▸ two_pow_le_size_of_computes_parity_of_depthWith_le hF.toCircuit hs
    ((F.depthWith_toCircuit_le andOrCost).trans hd) hn

end Unbounded

end Cslib.Circuits.Boolean
