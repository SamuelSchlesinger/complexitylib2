/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.LocalListDecoding
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Self-correction of Reed–Muller codes by interpolation and majority trees

A received word `w` that differs from a Reed–Muller codeword `p` of degree `d` on few points can
be corrected *everywhere*, with few queries and fixed randomness. The basic step reads `w` at
`d + 1` points `x + ν i • v` of a line through `x`, for fixed distinct nonzero nodes `ν i`, and
interpolates: `p x = ∑ i, λ i * p (x + ν i • v)` for the Lagrange weights `λ i` of the nodes at
`0` (`Cslib.Code.lagrangeDecode_of_mem_reedMuller`). Each queried point is uniformly distributed
over the directions `v`, so at every point `x` at most `(d + 1) * Δ(w, p)` directions make the
step err (`Cslib.Code.card_lagrangeDecode_ne_le`) [Arora and Barak, Section 19.4][AroraBarak09].

A *majority tree* (`Cslib.Code.majTree`) of depth `L` combines `3 ^ L` independent runs by
repeated majorities of three, `maj3 a b c = if a = b then a else c`, which is right whenever two
of its arguments are. If a run errs with probability at most `ρ`, the tree errs with probability
at most `(3 * ρ) ^ (2 ^ L) / 3` (`Cslib.Code.card_majTree_ne_le`). For `3 * ρ ≤ 1 / 2` this is
below `2 ^ (-2 ^ L)`, so by a union bound one fixed choice of the `3 ^ L` directions corrects
every point of a set of at most `2 ^ (2 ^ L)` points
(`Cslib.Code.exists_forall_majTree_eq`). Majority trees replace a Chernoff bound by a counting
argument and need only equality tests to evaluate.

## Main definitions

* `Cslib.Code.lagrangeWeight`, `Cslib.Code.lagrangeDecode`: interpolation along a line.
* `Cslib.Code.maj3`, `Cslib.Code.majTree`: majorities of three and majority trees.

## Main results

* `Cslib.Code.lagrangeDecode_of_mem_reedMuller`: interpolation is exact on codewords.
* `Cslib.Code.card_lagrangeDecode_ne_le`: few directions err.
* `Cslib.Code.card_majTree_ne_le`: amplification by majority trees.
* `Cslib.Code.exists_forall_majTree_eq`: one choice of directions corrects a whole set.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 19.4
-/

@[expose] public section

namespace Cslib.Code

open Finset Polynomial

/-! ### Interpolation along a line -/

section Interpolation

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}

/-- The Lagrange weight of the node `ν i` at `0`. -/
noncomputable def lagrangeWeight (ν : Fin (d + 1) ↪ F) (i : Fin (d + 1)) : F :=
  (Lagrange.basis univ ν i).eval 0

omit [Fintype F] [DecidableEq F] in
/-- A polynomial of degree at most `d` is determined at `0` by its values at `d + 1` nodes. -/
theorem eval_zero_eq_sum_lagrangeWeight (ν : Fin (d + 1) ↪ F) {P : F[X]}
    (hP : P.natDegree ≤ d) : P.eval 0 = ∑ i, lagrangeWeight ν i * P.eval (ν i) := by
  have hdeg : P.degree < #(univ : Finset (Fin (d + 1))) := by
    rw [card_univ, Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hP)
  conv_lhs => rw [Lagrange.eq_interpolate (s := univ) (v := ν) (ν.injective.injOn) hdeg]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, lagrangeWeight, mul_comm]

/-- **Interpolation along a line**: the combination of the values of `w` at the points
`x + ν i • v` with the Lagrange weights at `0`. -/
noncomputable def lagrangeDecode (ν : Fin (d + 1) ↪ F) (w : (Fin m → F) → F)
    (x v : Fin m → F) : F :=
  ∑ i, lagrangeWeight ν i * w (x + ν i • v)

omit [Fintype F] [DecidableEq F] in
/-- **Interpolation is exact on codewords** of the Reed–Muller code of degree `d`, for every
direction. -/
theorem lagrangeDecode_of_mem_reedMuller (ν : Fin (d + 1) ↪ F) {p : (Fin m → F) → F}
    (hp : p ∈ reedMuller F m d) (x v : Fin m → F) : lagrangeDecode ν p x v = p x := by
  obtain ⟨P, hP, hPeval⟩ := exists_natDegree_le_line hp x v
  have hx : p x = P.eval 0 := by rw [hPeval, zero_smul, add_zero]
  rw [lagrangeDecode, hx, eval_zero_eq_sum_lagrangeWeight ν hP]
  simp only [hPeval]

/-- **Few directions err.** At every point `x`, at most `(d + 1) * Δ(w, p)` directions `v` make
interpolation along the line through `x` in the direction `v` err, when the nodes are nonzero. -/
theorem card_lagrangeDecode_ne_le (ν : Fin (d + 1) ↪ F) (hν : ∀ i, ν i ≠ 0)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (w : (Fin m → F) → F) (x : Fin m → F) :
    #{v | lagrangeDecode ν w x v ≠ p x} ≤ (d + 1) * #{y | w y ≠ p y} := by
  set E : Finset (Fin m → F) := {y | w y ≠ p y}
  have hsub : ({v | lagrangeDecode ν w x v ≠ p x} : Finset (Fin m → F)) ⊆
      univ.biUnion fun i => univ.filter fun v => x + ν i • v ∈ E := by
    intro v hv
    rw [mem_filter] at hv
    by_contra hnot
    simp only [mem_biUnion, mem_univ, true_and, mem_filter, not_exists, E, ne_eq,
      not_not] at hnot
    refine hv.2 ((sum_congr rfl fun i _ => ?_).trans (lagrangeDecode_of_mem_reedMuller ν hp x v))
    rw [hnot i]
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  calc ∑ i, #(univ.filter fun v => x + ν i • v ∈ E) ≤ ∑ _i : Fin (d + 1), #E :=
        sum_le_sum fun i _ => card_le_card_of_injOn (fun v => x + ν i • v)
          (fun v hv => by simpa using hv)
          (fun v _ v' _ h => smul_right_injective _ (hν i) (add_left_cancel h))
    _ = (d + 1) * #E := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end Interpolation

/-! ### Majority trees -/

section MajorityTree

variable {α : Type*} [DecidableEq α]

/-- The majority of three, right whenever two of its arguments are: `a` if `a = b`, else `c`. -/
def maj3 (a b c : α) : α := if a = b then a else c

/-- If `maj3 a b c` misses `y`, then two of `a`, `b`, `c` miss `y`. -/
theorem two_ne_of_maj3_ne {a b c y : α} (h : maj3 a b c ≠ y) :
    (a ≠ y ∧ b ≠ y) ∨ (a ≠ y ∧ c ≠ y) ∨ (b ≠ y ∧ c ≠ y) := by
  unfold maj3 at h
  split_ifs at h with hab
  · subst hab
    exact Or.inl ⟨h, h⟩
  · by_cases ha : a = y
    · subst ha
      exact Or.inr (Or.inr ⟨Ne.symm hab, h⟩)
    · exact Or.inr (Or.inl ⟨ha, h⟩)

/-- The splitting of `3 ^ (L + 1)` leaves into three blocks of `3 ^ L`. -/
def tripleEquiv (L : ℕ) : Fin 3 × Fin (3 ^ L) ≃ Fin (3 ^ (L + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ' 3 L).symm)

/-- **A majority tree** of depth `L` over `3 ^ L` values: the majority of three of the trees over
the three blocks. -/
def majTree : (L : ℕ) → (Fin (3 ^ L) → α) → α
  | 0, f => f ⟨0, by simp⟩
  | L + 1, f => maj3 (majTree L fun k => f (tripleEquiv L (0, k)))
      (majTree L fun k => f (tripleEquiv L (1, k))) (majTree L fun k => f (tripleEquiv L (2, k)))

/-- **Amplification by majority trees.** If at most a `ρ` fraction of the outcomes `ω` have
`val ω ≠ y`, then at most a `(3 * ρ) ^ (2 ^ L) / 3` fraction of the tuples of `3 ^ L` outcomes
make the majority tree miss `y`. -/
theorem card_majTree_ne_le {Ω : Type*} [Fintype Ω] (val : Ω → α) (y : α)
    {ρ : ℝ} (hρ : (#{ω | val ω ≠ y} : ℝ) ≤ ρ * Fintype.card Ω) (L : ℕ) :
    (#{V : Fin (3 ^ L) → Ω | majTree L (val ∘ V) ≠ y} : ℝ) ≤
      (3 * ρ) ^ (2 ^ L) / 3 * Fintype.card Ω ^ (3 ^ L) := by
  classical
  induction L with
  | zero =>
    have : #{V : Fin (3 ^ 0) → Ω | majTree 0 (val ∘ V) ≠ y} = #{ω | val ω ≠ y} := by
      refine card_nbij' (fun V => V ⟨0, by simp⟩) (fun ω _ => ω) (fun V hV => ?_)
        (fun ω hω => ?_) (fun V _ => ?_) (fun ω _ => rfl)
      · rw [mem_coe, mem_filter] at hV ⊢
        exact ⟨mem_univ _, hV.2⟩
      · rw [mem_coe, mem_filter] at hω ⊢
        exact ⟨mem_univ _, hω.2⟩
      · funext k
        have hk : k = ⟨0, by simp⟩ := Fin.ext (by have := k.2; simp at this; omega)
        rw [hk]
    rw [this]
    simpa using hρ
  | succ L ih =>
    set N := (#{V : Fin (3 ^ L) → Ω | majTree L (val ∘ V) ≠ y} : ℕ)
    set B : Finset (Fin (3 ^ L) → Ω) := {V | majTree L (val ∘ V) ≠ y}
    -- the three blocks of a tuple
    let e : (Fin (3 ^ (L + 1)) → Ω) ≃ (Fin 3 → Fin (3 ^ L) → Ω) :=
      (Equiv.arrowCongr (tripleEquiv L).symm (Equiv.refl Ω)).trans (Equiv.curry _ _ _)
    have he : ∀ V j k, e V j k = V (tripleEquiv L (j, k)) := fun V j k => rfl
    have hcard : #{V : Fin (3 ^ (L + 1)) → Ω | majTree (L + 1) (val ∘ V) ≠ y} ≤
        #(Fintype.piFinset ![B, B, univ]) + #(Fintype.piFinset ![B, univ, B]) +
          #(Fintype.piFinset ![univ, B, B]) := by
      calc #{V : Fin (3 ^ (L + 1)) → Ω | majTree (L + 1) (val ∘ V) ≠ y}
          ≤ #(Fintype.piFinset ![B, B, univ] ∪ Fintype.piFinset ![B, univ, B] ∪
              Fintype.piFinset ![univ, B, B]) := by
            refine card_le_card_of_injOn e (fun V hV => ?_) (e.injective.injOn)
            rw [mem_coe, mem_filter] at hV
            have h := two_ne_of_maj3_ne hV.2
            rw [mem_coe]
            rcases h with ⟨h₀, h₁⟩ | ⟨h₀, h₂⟩ | ⟨h₁, h₂⟩
            · refine mem_union_left _ (mem_union_left _ (Fintype.mem_piFinset.2 fun j => ?_))
              fin_cases j
              · exact mem_filter.2 ⟨mem_univ _, h₀⟩
              · exact mem_filter.2 ⟨mem_univ _, h₁⟩
              · exact mem_univ _
            · refine mem_union_left _ (mem_union_right _ (Fintype.mem_piFinset.2 fun j => ?_))
              fin_cases j
              · exact mem_filter.2 ⟨mem_univ _, h₀⟩
              · exact mem_univ _
              · exact mem_filter.2 ⟨mem_univ _, h₂⟩
            · refine mem_union_right _ (Fintype.mem_piFinset.2 fun j => ?_)
              fin_cases j
              · exact mem_univ _
              · exact mem_filter.2 ⟨mem_univ _, h₁⟩
              · exact mem_filter.2 ⟨mem_univ _, h₂⟩
        _ ≤ _ := (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    have hB : (#B : ℝ) ≤ (3 * ρ) ^ (2 ^ L) / 3 * Fintype.card Ω ^ (3 ^ L) := ih
    simp only [Fintype.card_piFinset, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, card_univ,
      Fintype.card_fun, Fintype.card_fin] at hcard
    have hcard' : (#{V : Fin (3 ^ (L + 1)) → Ω | majTree (L + 1) (val ∘ V) ≠ y} : ℝ) ≤
        3 * ((#B : ℝ) * #B * Fintype.card Ω ^ (3 ^ L)) := by
      have : (#{V : Fin (3 ^ (L + 1)) → Ω | majTree (L + 1) (val ∘ V) ≠ y} : ℝ) ≤
          (#B * #B * Fintype.card Ω ^ (3 ^ L) + #B * Fintype.card Ω ^ (3 ^ L) * #B +
            Fintype.card Ω ^ (3 ^ L) * #B * #B : ℕ) := by exact_mod_cast hcard
      push_cast at this
      linarith
    have hB0 : (0 : ℝ) ≤ #B := by positivity
    have hX : (0 : ℝ) ≤ (3 * ρ) ^ (2 ^ L) / 3 * Fintype.card Ω ^ (3 ^ L) := hB0.trans hB
    calc (#{V : Fin (3 ^ (L + 1)) → Ω | majTree (L + 1) (val ∘ V) ≠ y} : ℝ)
        ≤ 3 * ((#B : ℝ) * #B * Fintype.card Ω ^ (3 ^ L)) := hcard'
      _ ≤ 3 * (((3 * ρ) ^ (2 ^ L) / 3 * Fintype.card Ω ^ (3 ^ L)) *
            ((3 * ρ) ^ (2 ^ L) / 3 * Fintype.card Ω ^ (3 ^ L)) * Fintype.card Ω ^ (3 ^ L)) := by
          have := mul_le_mul hB hB hB0 hX
          have hc : (0 : ℝ) ≤ Fintype.card Ω ^ (3 ^ L) := by positivity
          nlinarith
      _ = (3 * ρ) ^ (2 ^ (L + 1)) / 3 * Fintype.card Ω ^ (3 ^ (L + 1)) := by
          rw [pow_succ 2 L, pow_mul, pow_succ 3 L, pow_mul]
          ring

/-- **One choice of randomness corrects a whole set.** Let a randomized procedure `val x`, for
each `x` in a set `S` of at most `2 ^ (2 ^ L)` inputs, miss `target x` on at most a `ρ` fraction of
its outcomes, with `3 * ρ ≤ 1 / 2`. Then some tuple of `3 ^ L` outcomes makes the majority tree
right at every `x ∈ S`. -/
theorem exists_forall_majTree_eq {X Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (S : Finset X) (val : X → Ω → α) (target : X → α) {ρ : ℝ}
    (hρ : ∀ x ∈ S, (#{ω | val x ω ≠ target x} : ℝ) ≤ ρ * Fintype.card Ω)
    (h3 : 3 * ρ ≤ 1 / 2) {L : ℕ} (hS : #S ≤ 2 ^ (2 ^ L)) :
    ∃ V : Fin (3 ^ L) → Ω, ∀ x ∈ S, majTree L (val x ∘ V) = target x := by
  classical
  by_contra hcon
  push Not at hcon
  have hρ0 : 0 ≤ ρ := by
    by_cases hS0 : S.Nonempty
    · obtain ⟨x, hx⟩ := hS0
      have := hρ x hx
      have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
      nlinarith [show (0 : ℝ) ≤ #{ω | val x ω ≠ target x} from by positivity]
    · simp only [not_nonempty_iff_eq_empty] at hS0
      subst hS0
      obtain ⟨V⟩ : Nonempty (Fin (3 ^ L) → Ω) := inferInstance
      obtain ⟨x, hx, -⟩ := hcon V
      exact absurd hx (notMem_empty x)
  have hcover : (univ : Finset (Fin (3 ^ L) → Ω)) ⊆
      S.biUnion fun x => {V | majTree L (val x ∘ V) ≠ target x} := by
    intro V _
    obtain ⟨x, hx, hne⟩ := hcon V
    exact mem_biUnion.2 ⟨x, hx, mem_filter.2 ⟨mem_univ _, hne⟩⟩
  have hcard := (card_le_card hcover).trans card_biUnion_le
  rw [card_univ, Fintype.card_fun, Fintype.card_fin] at hcard
  have hsum : (Fintype.card Ω ^ (3 ^ L) : ℝ) ≤
      #S * ((3 * ρ) ^ (2 ^ L) / 3 * Fintype.card Ω ^ (3 ^ L)) := by
    calc (Fintype.card Ω ^ (3 ^ L) : ℝ) ≤
          ∑ x ∈ S, (#{V : Fin (3 ^ L) → Ω | majTree L (val x ∘ V) ≠ target x} : ℝ) := by
          exact_mod_cast hcard
      _ ≤ ∑ _x ∈ S, (3 * ρ) ^ (2 ^ L) / 3 * Fintype.card Ω ^ (3 ^ L) :=
          sum_le_sum fun x hx => card_majTree_ne_le (val x) (target x) (hρ x hx) L
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hpow : (3 * ρ) ^ (2 ^ L) ≤ (1 / 2) ^ (2 ^ L) :=
    pow_le_pow_left₀ (by positivity) h3 _
  have hS' : (#S : ℝ) * (1 / 2) ^ (2 ^ L) ≤ 1 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast hS
  have hΩ : (0 : ℝ) < Fintype.card Ω ^ (3 ^ L) := by
    have : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    positivity
  have : #S * ((3 * ρ) ^ (2 ^ L) / 3 * Fintype.card Ω ^ (3 ^ L)) ≤
      (1 / 3 : ℝ) * Fintype.card Ω ^ (3 ^ L) := by
    have h1 : (#S : ℝ) * (3 * ρ) ^ (2 ^ L) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hS'
    nlinarith
  linarith

end MajorityTree

end Cslib.Code
