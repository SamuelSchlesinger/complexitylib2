/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Loops
import Complexity.Foundations.Combinatorics.Expander.Power
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt

/-!
# Products of rotation maps

Expanders of constant degree on arbitrarily many vertices are built from small ones by graph
products [Reingold, Vadhan and Wigderson, Section 1.2][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09]
[Hoory, Linial and Wigderson, Section 9][HooryLinialWigderson2006]. Besides powers
(`Cslib.RotationMap.pow`), these are:

* the **tensor product** `G.tensor H` on `V × V'`, which takes a step in `G` and a step in `H` at
  the same time: `λ(G ⊗ H) ≤ max λ(G) λ(H)`, with equality when neither factor is empty or
  without edges;
* the **zig-zag product** `G.zigzag H` of a `D`-regular graph `G` with a graph `H` on the labels
  `D` of `G`, on the vertices `V × D` and with the square of the degree of `H`:
  `λ(G ⓩ H) ≤ λ(G) + λ(H) + λ(H) ^ 2` and `λ(G ⓩ H) ≤ 1 - (1 - λ(G)) (1 - λ(H)) ^ 2`;
* the **balanced replacement product** `G.balancedReplacement H`, on the same vertices and with
  twice the degree of `H`: `λ(G Ⓡ H) ^ 3 ≤ 7 / 8 + λ(G ⓩ H) / 8`, so that
  `λ(G Ⓡ H) ≤ 1 - (1 - λ(G)) (1 - λ(H)) ^ 2 / 24`.

The zig-zag theorem is proved as in
[Reingold, Vadhan and Wigderson, Section 4.1][ReingoldVadhanWigderson2002]. The walk operator of
`G ⓩ H` is `B̃ Ã B̃`, where `B̃ = I ⊗ W_H` is the walk on the copies `{v} × D` of `H`, the walk
operator of `(loops V Unit).tensor H`, and `Ã` permutes the vertices by the rotation map of `G`. A
function on `V × D` splits into its averages over the copies of `H` and a part of average zero on
every copy; `B̃` fixes the first and shrinks the second by `λ(H)`, while on the first `Ã` acts as
the walk on `G`. This bounds `𝔼 h · W f` for every `h` and every `f` of expectation zero, and with
`h = W f` it bounds `W f`: as `λ` is an operator norm, no eigenvectors are needed. The same
splitting proves the bound for the tensor product. The walk operator of the balanced replacement
product is `(B̃ + Ã) / 2`, and the zig-zag walk `B̃ Ã B̃` is one of the eight terms of its cube
[Reingold, Vadhan and Wigderson, Theorem 6.7][ReingoldVadhanWigderson2002].

## Main definitions

* `Cslib.RotationMap.tensor`: the tensor product `G ⊗ H`.
* `Cslib.RotationMap.zigzag`: the zig-zag product `G ⓩ H`.
* `Cslib.RotationMap.balancedReplacement`: the balanced replacement product `G Ⓡ H`.

## Main results

* `Cslib.RotationMap.walk_tensor`, `Cslib.RotationMap.spectralExpansion_tensor_le`,
  `Cslib.RotationMap.spectralExpansion_tensor`: the walk operator of `G ⊗ H` is
  `(W_G ⊗ I) (I ⊗ W_H)`, and its spectral expansion is the larger of those of the factors.
* `Cslib.RotationMap.walk_zigzag`: the walk operator of `G ⓩ H` is `B̃ Ã B̃`.
* `Cslib.RotationMap.spectralExpansion_zigzag_le`: **the zig-zag theorem**,
  `λ(G ⓩ H) ≤ λ(G) + λ(H) + λ(H) ^ 2`.
* `Cslib.RotationMap.spectralExpansion_zigzag_le_one_sub`,
  `Cslib.RotationMap.spectralExpansion_zigzag_lt_one`: the zig-zag product of two expanders is an
  expander.
* `Cslib.RotationMap.walk_balancedReplacement`: the walk operator of `G Ⓡ H` is `(B̃ + Ã) / 2`.
* `Cslib.RotationMap.spectralExpansion_balancedReplacement_pow_three_le`,
  `Cslib.RotationMap.spectralExpansion_balancedReplacement_le`,
  `Cslib.RotationMap.spectralExpansion_balancedReplacement_lt_one`: the balanced replacement
  product of two expanders is an expander.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

section Expect

variable {ι α β : Type*}

/-- A function of the first coordinate has the same average on the product. -/
private theorem expect_comp_fst [Fintype α] [Fintype β] [Nonempty β] (φ : α → ℝ) :
    𝔼 p : α × β, φ p.1 = 𝔼 a, φ a := by
  simp only [Fintype.expect_prod_type, Fintype.expect_const]

/-- A function of the second coordinate has the same average on the product. -/
private theorem expect_comp_snd [Fintype α] [Fintype β] [Nonempty α] (φ : β → ℝ) :
    𝔼 p : α × β, φ p.2 = 𝔼 b, φ b := by
  simp only [Fintype.expect_prod_type, Fintype.expect_const]

/-- Subtracting from a function its averages over the fibers `{a} × β` leaves averages zero over
the fibers. -/
private theorem expect_sub_expect_fiber [Fintype β] (f : α × β → ℝ) (a : α) :
    𝔼 b, (f (a, b) - 𝔼 b', f (a, b')) = 0 := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  · simp
  · rw [expect_sub_distrib, Fintype.expect_const, sub_self]

/-- **Pythagoras' theorem** for the splitting of a function on `α × β` into a function of the first
coordinate and a function of average zero over every fiber `{a} × β`. -/
private theorem expect_add_sq_of_expect_fiber_eq_zero [Fintype α] [Fintype β] (φ : α → ℝ)
    {g : α × β → ℝ} (hg : ∀ a, 𝔼 b, g (a, b) = 0) :
    𝔼 p, (φ p.1 + g p) ^ 2 = 𝔼 p : α × β, φ p.1 ^ 2 + 𝔼 p, g p ^ 2 := by
  have h : 𝔼 p, φ p.1 * g p = 0 := by
    simp only [Fintype.expect_prod_type, ← mul_expect, hg, mul_zero, expect_const_zero]
  simp only [add_sq, expect_add_distrib, mul_assoc, ← mul_expect, h, mul_zero, add_zero]

/-- Every function on `α × β` is a function of the first coordinate, its averages over the fibers
`{a} × β`, plus a function of average zero over every fiber, and the second moments add up. -/
private theorem exists_eq_add_expect_fiber_eq_zero [Fintype α] [Fintype β] [Nonempty β]
    (f : α × β → ℝ) :
    ∃ (f₁ : α → ℝ) (f₂ : α × β → ℝ), f = (fun p ↦ f₁ p.1 + f₂ p) ∧
      (∀ a, 𝔼 b, f₂ (a, b) = 0) ∧ 𝔼 a, f₁ a = 𝔼 p, f p ∧
      𝔼 p, f p ^ 2 = 𝔼 a, f₁ a ^ 2 + 𝔼 p, f₂ p ^ 2 := by
  have hf : f = fun p ↦ 𝔼 b, f (p.1, b) + (f p - 𝔼 b, f (p.1, b)) :=
    funext fun p ↦ (add_sub_cancel _ _).symm
  refine ⟨fun a ↦ 𝔼 b, f (a, b), fun p ↦ f p - 𝔼 b, f (p.1, b), hf, expect_sub_expect_fiber f,
    (Fintype.expect_prod_type f).symm, ?_⟩
  calc 𝔼 p, f p ^ 2 = 𝔼 p, (𝔼 b, f (p.1, b) + (f p - 𝔼 b, f (p.1, b))) ^ 2 := by
        simp only [add_sub_cancel]
    _ = 𝔼 p : α × β, (𝔼 b, f (p.1, b)) ^ 2 + 𝔼 p, (f p - 𝔼 b, f (p.1, b)) ^ 2 :=
        expect_add_sq_of_expect_fiber_eq_zero (fun a ↦ 𝔼 b, f (a, b)) (expect_sub_expect_fiber f)
    _ = _ := by rw [expect_comp_fst (fun a ↦ (𝔼 b, f (a, b)) ^ 2)]

/-- **The Cauchy–Schwarz inequality** for averages, with square roots. -/
private theorem expect_mul_le_sqrt_mul_sqrt [Fintype ι] (u w : ι → ℝ) :
    𝔼 i, u i * w i ≤ √(𝔼 i, u i ^ 2) * √(𝔼 i, w i ^ 2) := by
  rw [← Real.sqrt_mul (expect_nonneg fun i _ ↦ sq_nonneg (u i))]
  exact Real.le_sqrt_of_sq_le (expect_mul_sq_le_sq_mul_sq _ _ _)

/-- A bound on a square root from a bound on its argument. -/
private theorem sqrt_le_mul_sqrt {x y c : ℝ} (hc : 0 ≤ c) (h : x ≤ c ^ 2 * y) :
    √x ≤ c * √y := by
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
  exact Real.sqrt_le_sqrt h

/-- If `𝔼 u² ≤ c √(𝔼 u²) √(𝔼 w²)` then `𝔼 u² ≤ c² 𝔼 w²`. -/
private theorem expect_sq_le_of_expect_mul_le [Fintype ι] {u w : ι → ℝ} {c : ℝ}
    (h : 𝔼 i, u i * u i ≤ c * (√(𝔼 i, u i ^ 2) * √(𝔼 i, w i ^ 2))) :
    𝔼 i, u i ^ 2 ≤ c ^ 2 * 𝔼 i, w i ^ 2 := by
  have hu : 0 ≤ 𝔼 i, u i ^ 2 := expect_nonneg fun i _ ↦ sq_nonneg (u i)
  have hw : 0 ≤ 𝔼 i, w i ^ 2 := expect_nonneg fun i _ ↦ sq_nonneg (w i)
  simp only [← sq] at h
  rw [← Real.sq_sqrt hu, ← Real.sq_sqrt hw, ← mul_pow]
  rcases (Real.sqrt_nonneg (𝔼 i, u i ^ 2)).eq_or_lt with h0 | hpos
  · rw [← h0, zero_pow two_ne_zero]
    positivity
  · refine pow_le_pow_left₀ hpos.le ?_ 2
    refine le_of_mul_le_mul_left ?_ hpos
    calc √(𝔼 i, u i ^ 2) * √(𝔼 i, u i ^ 2) = 𝔼 i, u i ^ 2 := Real.mul_self_sqrt hu
      _ ≤ _ := h
      _ = _ := by ring

end Expect

section Tensor

variable {V D V' D' : Type*}

variable (G : RotationMap V D) (H : RotationMap V' D')

/-- The **tensor product** `G ⊗ H`
[Reingold, Vadhan and Wigderson, Section 2.3][ReingoldVadhanWigderson2002]: the multigraph on
`V × V'` with labels `D × D'` whose edge `(i, i')` at `(v, v')` takes the edge `i` of `G` at `v` and
the edge `i'` of `H` at `v'` at the same time. -/
def tensor : RotationMap (V × V') (D × D') where
  rot p := (((G.rot (p.1.1, p.2.1)).1, (H.rot (p.1.2, p.2.2)).1),
    ((G.rot (p.1.1, p.2.1)).2, (H.rot (p.1.2, p.2.2)).2))
  rot_involutive p := by simp

/-- The rotation map of `G ⊗ H` applies those of `G` and of `H` side by side. -/
@[simp]
theorem rot_tensor (v : V) (v' : V') (i : D) (i' : D') :
    (G.tensor H).rot ((v, v'), (i, i')) =
      (((G.rot (v, i)).1, (H.rot (v', i')).1), ((G.rot (v, i)).2, (H.rot (v', i')).2)) :=
  rfl

/-- The neighbors in `G ⊗ H` are the pairs of a neighbor in `G` and a neighbor in `H`. -/
@[simp]
theorem neighbor_tensor (p : V × V') (i : D × D') :
    (G.tensor H).neighbor p i = (G.neighbor p.1 i.1, H.neighbor p.2 i.2) :=
  rfl

variable [Fintype D] [Fintype D']

/-- The walk operator of `G ⊗ H` averages over a neighbor in `G` and a neighbor in `H`. -/
theorem walk_tensor_apply (f : V × V' → ℝ) (p : V × V') :
    (G.tensor H).walk f p = 𝔼 i, 𝔼 i', f (G.neighbor p.1 i, H.neighbor p.2 i') := by
  rw [walk_apply, Fintype.expect_prod_type]
  rfl

/-- The walk operator of `G ⊗ H` is the tensor product of those of `G` and `H`: it sends
`f ⊗ g : (v, v') ↦ f v * g v'` to `G.walk f ⊗ H.walk g`. -/
theorem walk_tensor_mul (f : V → ℝ) (g : V' → ℝ) :
    (G.tensor H).walk (fun p ↦ f p.1 * g p.2) = fun p ↦ G.walk f p.1 * H.walk g p.2 :=
  funext fun p ↦ by rw [walk_tensor_apply, walk_apply, walk_apply, Fintype.expect_mul_expect]

/-- The walk operator of `(loops V Unit).tensor H` is the walk operator `I ⊗ W_H` of `H` on every
copy `{v} × V'` of `H`. -/
theorem walk_loops_tensor_apply (f : V × V' → ℝ) (p : V × V') :
    ((loops V Unit).tensor H).walk f p = H.walk (fun w ↦ f (p.1, w)) p.2 := by
  rw [walk_tensor_apply, walk_apply]
  simp only [neighbor_loops, Fintype.expect_const]

/-- The walk operator of `G.tensor (loops V' Unit)` is the walk operator `W_G ⊗ I` of `G` on every
copy `V × {v'}` of `G`. -/
theorem walk_tensor_loops_apply (f : V × V' → ℝ) (p : V × V') :
    (G.tensor (loops V' Unit)).walk f p = G.walk (fun w ↦ f (w, p.2)) p.1 := by
  rw [walk_tensor_apply, walk_apply]
  simp only [neighbor_loops, Fintype.expect_const]

/-- The walk operator of `G ⊗ H` factors as `W_G ⊗ W_H = (W_G ⊗ I) (I ⊗ W_H)`. -/
theorem walk_tensor :
    (G.tensor H).walk = (G.tensor (loops V' Unit)).walk ∘ₗ ((loops V Unit).tensor H).walk :=
  LinearMap.ext fun f ↦ funext fun p ↦ by
    rw [LinearMap.comp_apply, walk_tensor_loops_apply, walk_tensor_apply, walk_apply]
    simp only [walk_loops_tensor_apply]
    simp only [walk_apply]

/-- When `H` has edges, the walk operator on the copies of `H` fixes the functions that are
constant on every copy. -/
theorem walk_loops_tensor_comp_fst [Nonempty D'] (φ : V → ℝ) :
    ((loops V Unit).tensor H).walk (fun p ↦ φ p.1) = fun p ↦ φ p.1 :=
  funext fun p ↦ by
    rw [walk_loops_tensor_apply]
    exact congrFun (H.walk_const (φ p.1)) p.2

/-- The walk operator on the copies of `H` acts on the part of average zero over every copy. -/
private theorem walk_loops_tensor_add [Nonempty D'] (φ : V → ℝ) (g : V × V' → ℝ) :
    ((loops V Unit).tensor H).walk (fun p ↦ φ p.1 + g p) =
      fun p ↦ φ p.1 + ((loops V Unit).tensor H).walk g p := by
  rw [show (fun p ↦ φ p.1 + g p) = (fun p : V × V' ↦ φ p.1) + g from rfl, map_add,
    walk_loops_tensor_comp_fst]
  rfl

/-- On functions of average zero over every copy `{v} × V'` of `H`, the walk operator on the
copies of `H` multiplies the second moment by at most `λ(H) ^ 2`. -/
theorem expect_walk_loops_tensor_sq_le [Fintype V] [Fintype V'] {f : V × V' → ℝ}
    (hf : ∀ v, 𝔼 v', f (v, v') = 0) :
    𝔼 p, ((loops V Unit).tensor H).walk f p ^ 2 ≤ H.spectralExpansion ^ 2 * 𝔼 p, f p ^ 2 := by
  rw [Fintype.expect_prod_type, Fintype.expect_prod_type, mul_expect]
  refine expect_le_expect fun v _ ↦ ?_
  simp only [walk_loops_tensor_apply]
  exact H.expect_walk_sq_le_spectralExpansion_sq_mul (hf v)

/-- The walk operator on the copies of `H` keeps average zero over every copy. -/
private theorem expect_walk_loops_tensor_eq_zero [Fintype V'] [Nonempty D'] {f : V × V' → ℝ}
    (hf : ∀ v, 𝔼 v', f (v, v') = 0) (v : V) :
    𝔼 v', ((loops V Unit).tensor H).walk f (v, v') = 0 := by
  simp only [walk_loops_tensor_apply]
  rw [H.expect_walk (fun w ↦ f (v, w)), hf v]

/-- For `g` of average zero over every copy of `H`, `λ(H) φ + (I ⊗ W_H) g` has norm at most `λ(H)`
times that of `φ + g`, where `φ` is a function of the first coordinate. -/
private theorem sqrt_expect_mul_add_walk_loops_tensor_sq_le [Fintype V] [Fintype V'] [Nonempty V']
    [Nonempty D'] (φ : V → ℝ) {g : V × V' → ℝ} (hg : ∀ v, 𝔼 v', g (v, v') = 0) :
    √(𝔼 p, (H.spectralExpansion * φ p.1 + ((loops V Unit).tensor H).walk g p) ^ 2) ≤
      H.spectralExpansion * √(𝔼 v, φ v ^ 2 + 𝔼 p, g p ^ 2) := by
  refine sqrt_le_mul_sqrt H.spectralExpansion_nonneg ?_
  rw [expect_add_sq_of_expect_fiber_eq_zero (fun v ↦ H.spectralExpansion * φ v)
      (H.expect_walk_loops_tensor_eq_zero hg),
    expect_comp_fst (fun v ↦ (H.spectralExpansion * φ v) ^ 2), mul_add]
  simp only [mul_pow, ← mul_expect]
  gcongr
  exact H.expect_walk_loops_tensor_sq_le hg

/-- The walk operator on the copies of `G` keeps average zero over the copies of `H`. -/
private theorem expect_walk_tensor_loops_eq_zero [Fintype V'] {f : V × V' → ℝ}
    (hf : ∀ v, 𝔼 v', f (v, v') = 0) (v : V) :
    𝔼 v', (G.tensor (loops V' Unit)).walk f (v, v') = 0 := by
  simp only [walk_tensor_loops_apply]
  simp only [walk_apply]
  rw [expect_comm]
  simp [hf]

variable [Fintype V] [Fintype V']

/-- The spectral expansion of `G ⊗ H` is at most the larger of those of `G` and `H`
[Reingold, Vadhan and Wigderson, Proposition 2.4][ReingoldVadhanWigderson2002]. -/
theorem spectralExpansion_tensor_le :
    (G.tensor H).spectralExpansion ≤ max G.spectralExpansion H.spectralExpansion := by
  have hG := le_max_left G.spectralExpansion H.spectralExpansion
  have hH := le_max_right G.spectralExpansion H.spectralExpansion
  have hG0 := G.spectralExpansion_nonneg
  have hH0 := H.spectralExpansion_nonneg
  refine spectralExpansion_le (hG0.trans hG) fun f hf ↦ ?_
  rcases isEmpty_or_nonempty D' with hD' | hD'
  · have : (G.tensor H).walk f = 0 := funext fun p ↦ by simp [walk_tensor_apply]
    rw [this]
    simpa using mul_nonneg (sq_nonneg _) (expect_nonneg fun p _ ↦ sq_nonneg (f p))
  rcases isEmpty_or_nonempty V' with hV' | hV'
  · simp
  obtain ⟨f₁, f₂, rfl, hf₂, hf₁, hff⟩ := exists_eq_add_expect_fiber_eq_zero f
  rw [hf] at hf₁
  have hW : (G.tensor H).walk (fun p ↦ f₁ p.1 + f₂ p) =
      fun p ↦ G.walk f₁ p.1 +
        (G.tensor (loops V' Unit)).walk (((loops V Unit).tensor H).walk f₂) p := by
    rw [walk_tensor, LinearMap.comp_apply, walk_loops_tensor_add,
      show (fun p ↦ f₁ p.1 + ((loops V Unit).tensor H).walk f₂ p) =
        (fun p : V × V' ↦ f₁ p.1) + ((loops V Unit).tensor H).walk f₂ from rfl, map_add]
    exact funext fun p ↦ by simp [walk_tensor_loops_apply]
  rw [hW, expect_add_sq_of_expect_fiber_eq_zero _
      (G.expect_walk_tensor_loops_eq_zero (H.expect_walk_loops_tensor_eq_zero hf₂)),
    expect_comp_fst (fun v ↦ G.walk f₁ v ^ 2), hff]
  calc
    _ ≤ G.spectralExpansion ^ 2 * 𝔼 v, f₁ v ^ 2 +
          H.spectralExpansion ^ 2 * 𝔼 p, f₂ p ^ 2 := by
      gcongr
      · exact expect_walk_sq_le_spectralExpansion_sq_mul hf₁
      · exact ((G.tensor (loops V' Unit)).expect_walk_sq_le _).trans
          (H.expect_walk_loops_tensor_sq_le hf₂)
    _ ≤ max G.spectralExpansion H.spectralExpansion ^ 2 * 𝔼 v, f₁ v ^ 2 +
          max G.spectralExpansion H.spectralExpansion ^ 2 * 𝔼 p, f₂ p ^ 2 := by
      have h₁ : 0 ≤ 𝔼 v, f₁ v ^ 2 := expect_nonneg fun v _ ↦ sq_nonneg (f₁ v)
      have h₂ : 0 ≤ 𝔼 p, f₂ p ^ 2 := expect_nonneg fun p _ ↦ sq_nonneg (f₂ p)
      gcongr
    _ = _ := by ring

/-- `λ(G) ≤ λ(G ⊗ H)`: functions of the first coordinate see the walk on `G`. -/
private theorem spectralExpansion_le_spectralExpansion_tensor_left [Nonempty V'] [Nonempty D'] :
    G.spectralExpansion ≤ (G.tensor H).spectralExpansion := by
  refine spectralExpansion_le (spectralExpansion_nonneg _) fun f hf ↦ ?_
  have hW : (G.tensor H).walk (fun p ↦ f p.1) = fun p ↦ G.walk f p.1 :=
    funext fun p ↦ by
      rw [walk_tensor_apply, walk_apply]
      simp only [Fintype.expect_const]
  have h := (G.tensor H).expect_walk_sq_le_spectralExpansion_sq_mul (f := fun p ↦ f p.1)
    (by rw [expect_comp_fst f, hf])
  rwa [hW, expect_comp_fst (fun v ↦ G.walk f v ^ 2), expect_comp_fst (fun v ↦ f v ^ 2)] at h

/-- `λ(H) ≤ λ(G ⊗ H)`: functions of the second coordinate see the walk on `H`. -/
private theorem spectralExpansion_le_spectralExpansion_tensor_right [Nonempty V] [Nonempty D] :
    H.spectralExpansion ≤ (G.tensor H).spectralExpansion := by
  refine spectralExpansion_le (spectralExpansion_nonneg _) fun f hf ↦ ?_
  have hW : (G.tensor H).walk (fun p ↦ f p.2) = fun p ↦ H.walk f p.2 :=
    funext fun p ↦ by
      rw [walk_tensor_apply, walk_apply]
      simp only [Fintype.expect_const]
  have h := (G.tensor H).expect_walk_sq_le_spectralExpansion_sq_mul (f := fun p ↦ f p.2)
    (by rw [expect_comp_snd f, hf])
  rwa [hW, expect_comp_snd (fun v ↦ H.walk f v ^ 2), expect_comp_snd (fun v ↦ f v ^ 2)] at h

/-- The spectral expansion of `G ⊗ H` is the larger of those of `G` and `H`
[Reingold, Vadhan and Wigderson, Proposition 2.4][ReingoldVadhanWigderson2002], when neither factor
is empty or without edges. -/
theorem spectralExpansion_tensor [Nonempty V] [Nonempty D] [Nonempty V'] [Nonempty D'] :
    (G.tensor H).spectralExpansion = max G.spectralExpansion H.spectralExpansion :=
  (G.spectralExpansion_tensor_le H).antisymm
    (max_le (G.spectralExpansion_le_spectralExpansion_tensor_left H)
      (G.spectralExpansion_le_spectralExpansion_tensor_right H))

end Tensor

/-- The bilinear estimate behind the zig-zag theorem: for nonnegative `b₁, b₂`,
`μ a₁ b₁ + ν (a₁ b₂ + a₂ b₁) + ν² a₂ b₂ ≤ (μ + ν + ν²) √(a₁² + a₂²) √(b₁² + b₂²)`. -/
private theorem add_mul_le_mul_sqrt_mul_sqrt {μ ν a₁ a₂ b₁ b₂ : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    a₁ * (μ * b₁) + a₁ * (ν * b₂) + ν * a₂ * b₁ + ν * a₂ * (ν * b₂) ≤
      (μ + ν + ν ^ 2) * (√(a₁ ^ 2 + a₂ ^ 2) * √(b₁ ^ 2 + b₂ ^ 2)) := by
  have hA₁ : a₁ ≤ √(a₁ ^ 2 + a₂ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hA₂ : a₂ ≤ √(a₁ ^ 2 + a₂ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hB₁ : b₁ ≤ √(b₁ ^ 2 + b₂ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hB₂ : b₂ ≤ √(b₁ ^ 2 + b₂ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h₁₁ := mul_le_mul hA₁ hB₁ hb₁ (Real.sqrt_nonneg _)
  have h₂₂ := mul_le_mul hA₂ hB₂ hb₂ (Real.sqrt_nonneg _)
  have h₁₂ : a₁ * b₂ + a₂ * b₁ ≤ √(a₁ ^ 2 + a₂ ^ 2) * √(b₁ ^ 2 + b₂ ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (a₁ * b₁ - a₂ * b₂)])
  nlinarith [mul_le_mul_of_nonneg_left h₁₁ hμ, mul_le_mul_of_nonneg_left h₁₂ hν,
    mul_le_mul_of_nonneg_left h₂₂ (sq_nonneg ν)]

/-- The bilinear estimate behind the second zig-zag bound: for `0 ≤ a ≤ A` and `0 ≤ b ≤ B`,
`(1 - ν)² μ a b + (1 - ν) ν (a B + A b) + ν² A B ≤ (1 - (1 - μ) (1 - ν)²) A B`. -/
private theorem mul_add_le_one_sub_mul {μ ν a b A B : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hν₁ : ν ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haA : a ≤ A) (hbB : b ≤ B) :
    (1 - ν) ^ 2 * (a * (μ * b)) + (1 - ν) * (a * (ν * B)) + (1 - ν) * (ν * A * b) +
        ν * A * (ν * B) ≤ (1 - (1 - μ) * (1 - ν) ^ 2) * (A * B) := by
  have h₁ : a * b ≤ A * B := mul_le_mul haA hbB hb (ha.trans haA)
  have h₂ : a * B ≤ A * B := mul_le_mul_of_nonneg_right haA (hb.trans hbB)
  have h₃ : A * b ≤ A * B := mul_le_mul_of_nonneg_left hbB (ha.trans haA)
  have hν' : 0 ≤ 1 - ν := sub_nonneg.2 hν₁
  nlinarith [mul_le_mul_of_nonneg_left h₁ (mul_nonneg (sq_nonneg (1 - ν)) hμ),
    mul_le_mul_of_nonneg_left h₂ (mul_nonneg hν' hν),
    mul_le_mul_of_nonneg_left h₃ (mul_nonneg hν' hν)]

section ZigZag

variable {V D E : Type*} (G : RotationMap V D) (H : RotationMap D E)

/-- The **zig-zag product** `G ⓩ H`
[Reingold, Vadhan and Wigderson, Definition 3.1][ReingoldVadhanWigderson2002]
[Hoory, Linial and Wigderson, Section 9.3][HooryLinialWigderson2006] of a `D`-regular graph `G` on
`V` with a graph `H` on the labels `D` of `G`. Its vertices are the pairs `(v, k)`, the `k`-th edge
at `v`, grouped into the cloud `{v} × D` of `v`, and its labels are pairs of labels of `H`. The edge
`(i, j)` at `(v, k)` takes the edge `i` of `H` from `k` to `k'` inside the cloud ("zig"), crosses
the `k'`-th edge of `G` from `v` to `(w, ℓ')`, where it is the `ℓ'`-th edge at `w`, and takes the
edge `j` of `H` from `ℓ'` to `ℓ` inside the cloud of `w` ("zag"), ending at `(w, ℓ)`. -/
def zigzag : RotationMap (V × D) (E × E) where
  rot p :=
    let a := H.rot (p.1.2, p.2.1)
    let b := G.rot (p.1.1, a.1)
    let c := H.rot (b.2, p.2.2)
    ((b.1, c.1), (c.2, a.2))
  rot_involutive p := by simp

/-- The rotation map of `G ⓩ H`
[Reingold, Vadhan and Wigderson, Definition 3.1][ReingoldVadhanWigderson2002]: with
`(k', i') = H.rot (k, i)`, `(w, ℓ') = G.rot (v, k')` and `(ℓ, j') = H.rot (ℓ', j)`, the edge
`(i, j)` at `(v, k)` is the edge `(j', i')` at `(w, ℓ)`. -/
theorem rot_zigzag (v : V) (k : D) (i j : E) :
    (G.zigzag H).rot ((v, k), (i, j)) =
      (((G.rot (v, (H.rot (k, i)).1)).1, (H.rot ((G.rot (v, (H.rot (k, i)).1)).2, j)).1),
        ((H.rot ((G.rot (v, (H.rot (k, i)).1)).2, j)).2, (H.rot (k, i)).2)) :=
  rfl

/-- The neighbors in `G ⓩ H`: a step in `H`, a step in `G`, and a step in `H`. -/
theorem neighbor_zigzag (p : V × D) (i : E × E) :
    (G.zigzag H).neighbor p i =
      ((G.rot (p.1, H.neighbor p.2 i.1)).1, H.neighbor (G.rot (p.1, H.neighbor p.2 i.1)).2 i.2) :=
  rfl

variable [Fintype E]

/-- The walk operator of `G ⓩ H` is `B̃ Ã B̃`
[Reingold, Vadhan and Wigderson, Section 4.1][ReingoldVadhanWigderson2002], where `B̃ = I ⊗ W_H` is
the walk operator of `H` on every cloud and `Ã` is the permutation of the vertices `V × D` by the
rotation map of `G`. -/
theorem walk_zigzag :
    (G.zigzag H).walk =
      ((loops V Unit).tensor H).walk ∘ₗ LinearMap.funLeft ℝ ℝ G.rot ∘ₗ
        ((loops V Unit).tensor H).walk :=
  LinearMap.ext fun f ↦ funext fun p ↦ by
    rw [walk_apply (G.zigzag H), Fintype.expect_prod_type, LinearMap.comp_apply,
      LinearMap.comp_apply, walk_loops_tensor_apply, walk_apply H]
    simp only [LinearMap.funLeft_apply, walk_loops_tensor_apply]
    simp only [walk_apply]
    rfl

variable [Fintype V] [Fintype D]

/-- In the splitting of functions along the clouds, `⟨h, W f⟩ = ⟨B̃ h, Ã B̃ f⟩` where `B̃` fixes the
parts constant on the clouds. -/
private theorem expect_mul_walk_zigzag_eq [Nonempty E] (h₁ f₁ : V → ℝ) (h₂ f₂ : V × D → ℝ) :
    𝔼 p, (h₁ p.1 + h₂ p) * (G.zigzag H).walk (fun p ↦ f₁ p.1 + f₂ p) p =
      𝔼 p, (h₁ p.1 + ((loops V Unit).tensor H).walk h₂ p) *
        (f₁ (G.rot p).1 + ((loops V Unit).tensor H).walk f₂ (G.rot p)) := by
  rw [walk_zigzag, LinearMap.comp_apply, LinearMap.comp_apply,
    ((loops V Unit).tensor H).expect_mul_walk_comm, walk_loops_tensor_add, walk_loops_tensor_add]
  rfl

/-- On the functions constant on the clouds, `Ã` acts as the walk on `G`. -/
private theorem expect_mul_comp_rot_le (φ : V → ℝ) {ψ : V → ℝ} (hψ : 𝔼 v, ψ v = 0) :
    𝔼 p, φ p.1 * ψ (G.rot p).1 ≤ √(𝔼 v, φ v ^ 2) * (G.spectralExpansion * √(𝔼 v, ψ v ^ 2)) := by
  have : 𝔼 p, φ p.1 * ψ (G.rot p).1 = 𝔼 v, φ v * G.walk ψ v := by
    simp only [Fintype.expect_prod_type, walk_apply, mul_expect]
    rfl
  rw [this]
  refine (expect_mul_le_sqrt_mul_sqrt _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact sqrt_le_mul_sqrt G.spectralExpansion_nonneg (expect_walk_sq_le_spectralExpansion_sq_mul hψ)

/-- The zig-zag estimate in bilinear form: `𝔼 h · W f ≤ (λ(G) + λ(H) + λ(H)²) ‖h‖ ‖f‖` for `f` of
expectation zero. -/
private theorem expect_mul_walk_zigzag_le [Nonempty D] [Nonempty E] (h : V × D → ℝ)
    {f : V × D → ℝ} (hf : 𝔼 p, f p = 0) :
    𝔼 p, h p * (G.zigzag H).walk f p ≤
      (G.spectralExpansion + H.spectralExpansion + H.spectralExpansion ^ 2) *
        (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  obtain ⟨h₁, h₂, rfl, hh₂, -, hhh⟩ := exists_eq_add_expect_fiber_eq_zero h
  obtain ⟨f₁, f₂, rfl, hf₂, hf₁, hff⟩ := exists_eq_add_expect_fiber_eq_zero f
  rw [hf] at hf₁
  rw [hhh, hff, ← Real.sq_sqrt (expect_nonneg fun v _ ↦ sq_nonneg (h₁ v)),
    ← Real.sq_sqrt (expect_nonneg fun p _ ↦ sq_nonneg (h₂ p)),
    ← Real.sq_sqrt (expect_nonneg fun v _ ↦ sq_nonneg (f₁ v)),
    ← Real.sq_sqrt (expect_nonneg fun p _ ↦ sq_nonneg (f₂ p))]
  refine le_trans ?_ (add_mul_le_mul_sqrt_mul_sqrt hμ hν (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [expect_mul_walk_zigzag_eq]
  simp only [add_mul]
  simp only [mul_add, expect_add_distrib]
  rw [← add_assoc]
  -- the walk on the clouds shrinks the parts of average zero over the clouds by `λ(H)`
  have hqh := sqrt_le_mul_sqrt hν (H.expect_walk_loops_tensor_sq_le hh₂)
  have hqf := sqrt_le_mul_sqrt hν (H.expect_walk_loops_tensor_sq_le hf₂)
  gcongr ?_ + ?_ + ?_ + ?_
  · exact G.expect_mul_comp_rot_le h₁ hf₁
  · refine (expect_mul_le_sqrt_mul_sqrt _ _).trans ?_
    rw [expect_comp_fst (fun v ↦ h₁ v ^ 2),
      expect_comp_rot G (fun p ↦ ((loops V Unit).tensor H).walk f₂ p ^ 2)]
    exact mul_le_mul_of_nonneg_left hqf (by positivity)
  · refine (expect_mul_le_sqrt_mul_sqrt _ _).trans ?_
    rw [expect_comp_rot G (fun p ↦ f₁ p.1 ^ 2), expect_comp_fst (fun v ↦ f₁ v ^ 2)]
    exact mul_le_mul_of_nonneg_right hqh (by positivity)
  · refine (expect_mul_le_sqrt_mul_sqrt _ _).trans ?_
    rw [expect_comp_rot G (fun p ↦ ((loops V Unit).tensor H).walk f₂ p ^ 2)]
    exact mul_le_mul hqh hqf (by positivity) (by positivity)

/-- The second zig-zag estimate in bilinear form:
`𝔼 h · W f ≤ (1 - (1 - λ(G)) (1 - λ(H))²) ‖h‖ ‖f‖` for `f` of expectation zero. -/
private theorem expect_mul_walk_zigzag_le_one_sub [Nonempty D] [Nonempty E] (h : V × D → ℝ)
    {f : V × D → ℝ} (hf : 𝔼 p, f p = 0) :
    𝔼 p, h p * (G.zigzag H).walk f p ≤
      (1 - (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2) *
        (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  have hν₁ : 0 ≤ 1 - H.spectralExpansion := sub_nonneg.2 H.spectralExpansion_le_one
  obtain ⟨h₁, h₂, rfl, hh₂, -, hhh⟩ := exists_eq_add_expect_fiber_eq_zero h
  obtain ⟨f₁, f₂, rfl, hf₂, hf₁, hff⟩ := exists_eq_add_expect_fiber_eq_zero f
  rw [hf] at hf₁
  rw [expect_mul_walk_zigzag_eq, hhh, hff]
  -- `B̃ h = (1 - λ(H)) h₁ + u` with `‖u‖ ≤ λ(H) ‖h‖`, and the same for `f`
  have hsplit (p : V × D) :
      (h₁ p.1 + ((loops V Unit).tensor H).walk h₂ p) *
          (f₁ (G.rot p).1 + ((loops V Unit).tensor H).walk f₂ (G.rot p)) =
        (1 - H.spectralExpansion) ^ 2 * (h₁ p.1 * f₁ (G.rot p).1) +
          (1 - H.spectralExpansion) * (h₁ p.1 * (H.spectralExpansion * f₁ (G.rot p).1 +
            ((loops V Unit).tensor H).walk f₂ (G.rot p))) +
          (1 - H.spectralExpansion) * ((H.spectralExpansion * h₁ p.1 +
            ((loops V Unit).tensor H).walk h₂ p) * f₁ (G.rot p).1) +
          (H.spectralExpansion * h₁ p.1 + ((loops V Unit).tensor H).walk h₂ p) *
            (H.spectralExpansion * f₁ (G.rot p).1 +
              ((loops V Unit).tensor H).walk f₂ (G.rot p)) := by
    ring
  simp only [hsplit, expect_add_distrib, ← mul_expect]
  have hu := H.sqrt_expect_mul_add_walk_loops_tensor_sq_le h₁ hh₂
  have hu' := H.sqrt_expect_mul_add_walk_loops_tensor_sq_le f₁ hf₂
  have ha : √(𝔼 v, h₁ v ^ 2) ≤ √(𝔼 v, h₁ v ^ 2 + 𝔼 p, h₂ p ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (expect_nonneg fun p _ ↦ sq_nonneg (h₂ p)))
  have hb : √(𝔼 v, f₁ v ^ 2) ≤ √(𝔼 v, f₁ v ^ 2 + 𝔼 p, f₂ p ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (expect_nonneg fun p _ ↦ sq_nonneg (f₂ p)))
  refine le_trans ?_ (mul_add_le_one_sub_mul hμ hν H.spectralExpansion_le_one
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ha hb)
  gcongr _ * ?_ + _ * ?_ + _ * ?_ + ?_
  · exact G.expect_mul_comp_rot_le h₁ hf₁
  · refine (expect_mul_le_sqrt_mul_sqrt _ _).trans ?_
    rw [expect_comp_fst (fun v ↦ h₁ v ^ 2), expect_comp_rot G (fun p ↦
      (H.spectralExpansion * f₁ p.1 + ((loops V Unit).tensor H).walk f₂ p) ^ 2)]
    exact mul_le_mul_of_nonneg_left hu' (by positivity)
  · refine (expect_mul_le_sqrt_mul_sqrt _ _).trans ?_
    rw [expect_comp_rot G (fun p ↦ f₁ p.1 ^ 2), expect_comp_fst (fun v ↦ f₁ v ^ 2)]
    exact mul_le_mul_of_nonneg_right hu (by positivity)
  · refine (expect_mul_le_sqrt_mul_sqrt _ _).trans ?_
    rw [expect_comp_rot G (fun p ↦
      (H.spectralExpansion * f₁ p.1 + ((loops V Unit).tensor H).walk f₂ p) ^ 2)]
    exact mul_le_mul hu hu' (by positivity) (by positivity)

/-- To bound `λ(G ⓩ H)` by `c ≥ 0`, it suffices to bound `𝔼 h · W f` by `c ‖h‖ ‖f‖` for every `h`
and every `f` of expectation zero, when `D` and `E` are nonempty. -/
private theorem spectralExpansion_zigzag_le_of_expect_mul_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ [Nonempty D] [Nonempty E] (h f : V × D → ℝ), 𝔼 p, f p = 0 →
      𝔼 p, h p * (G.zigzag H).walk f p ≤ c * (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2))) :
    (G.zigzag H).spectralExpansion ≤ c := by
  refine spectralExpansion_le hc fun f hf ↦ ?_
  rcases isEmpty_or_nonempty E with hE | hE
  · have : (G.zigzag H).walk f = 0 := funext fun p ↦ by simp [walk_apply]
    rw [this]
    simpa using mul_nonneg (sq_nonneg c) (expect_nonneg fun p _ ↦ sq_nonneg (f p))
  rcases isEmpty_or_nonempty D with hD | hD
  · simp
  exact expect_sq_le_of_expect_mul_le (h _ f hf)

/-- **The zig-zag theorem**
[Reingold, Vadhan and Wigderson, Theorem 3.2][ReingoldVadhanWigderson2002]
[Hoory, Linial and Wigderson, Section 9.3][HooryLinialWigderson2006]: the spectral expansion of
`G ⓩ H` is at most `λ(G) + λ(H) + λ(H) ^ 2`. -/
theorem spectralExpansion_zigzag_le :
    (G.zigzag H).spectralExpansion ≤
      G.spectralExpansion + H.spectralExpansion + H.spectralExpansion ^ 2 := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  exact G.spectralExpansion_zigzag_le_of_expect_mul_le H (by positivity) fun h _ hf ↦
    G.expect_mul_walk_zigzag_le H h hf

/-- The spectral expansion of `G ⓩ H` is at most `1 - (1 - λ(G)) (1 - λ(H)) ^ 2`: the zig-zag
product of two expanders is an expander. This form of the bound is useful when `λ(G)` and
`λ(H)` are close to `1`. -/
theorem spectralExpansion_zigzag_le_one_sub :
    (G.zigzag H).spectralExpansion ≤
      1 - (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2 := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  have hμ₁ := G.spectralExpansion_le_one
  have hν₁ := H.spectralExpansion_le_one
  refine G.spectralExpansion_zigzag_le_of_expect_mul_le H ?_ fun h _ hf ↦
    G.expect_mul_walk_zigzag_le_one_sub H h hf
  have : (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2 ≤ 1 :=
    (mul_le_mul (by linarith) (pow_le_one₀ (by linarith) (by linarith)) (sq_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  linarith

/-- The zig-zag product of two graphs of spectral expansion less than `1` has spectral expansion
less than `1` [Reingold, Vadhan and Wigderson, Theorem 3.2][ReingoldVadhanWigderson2002]. -/
theorem spectralExpansion_zigzag_lt_one (hG : G.spectralExpansion < 1)
    (hH : H.spectralExpansion < 1) : (G.zigzag H).spectralExpansion < 1 :=
  (G.spectralExpansion_zigzag_le_one_sub H).trans_lt
    (sub_lt_self 1 (mul_pos (sub_pos.2 hG) (pow_pos (sub_pos.2 hH) 2)))

end ZigZag

section BalancedReplacement

variable {V D E : Type*} (G : RotationMap V D) (H : RotationMap D E)

/-- The **balanced replacement product** of a `D`-regular graph `G` on `V` with a graph `H` on the
labels `D` of `G` [Reingold, Vadhan and Wigderson, Definition 6.6][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09]. Every vertex `v` of `G` is replaced by the copy
`{v} × D` of `H`. At `(v, k)`, the edge `Sum.inl i` is the edge `i` of `H` at `k` inside the copy,
and the edges `Sum.inr i`, one for every label `i` of `H`, all cross the `k`-th edge of `G` at `v`,
to `G.rot (v, k)`. So a step of the random walk takes a step in `H` or crosses an edge of `G` with
probability `1 / 2` each. -/
def balancedReplacement : RotationMap (V × D) (E ⊕ E) where
  rot
    | (p, .inl i) => ((p.1, (H.rot (p.2, i)).1), .inl (H.rot (p.2, i)).2)
    | (p, .inr i) => (G.rot p, .inr i)
  rot_involutive
    | (_, .inl _) => by simp
    | (_, .inr _) => by simp

/-- The edges `Sum.inl i` of the balanced replacement product are those of `H`. -/
@[simp]
theorem rot_balancedReplacement_inl (p : V × D) (i : E) :
    (G.balancedReplacement H).rot (p, .inl i) =
      ((p.1, (H.rot (p.2, i)).1), .inl (H.rot (p.2, i)).2) :=
  rfl

/-- The edges `Sum.inr i` of the balanced replacement product are those of `G`. -/
@[simp]
theorem rot_balancedReplacement_inr (p : V × D) (i : E) :
    (G.balancedReplacement H).rot (p, .inr i) = (G.rot p, .inr i) :=
  rfl

variable [Fintype E]

/-- When `H` has edges, the walk operator of the balanced replacement product is `(B̃ + Ã) / 2`
[Reingold, Vadhan and Wigderson, Theorem 6.7][ReingoldVadhanWigderson2002], where `B̃ = I ⊗ W_H` is
the walk operator of `H` on every copy and `Ã` permutes the vertices `V × D` by the rotation map of
`G`. -/
theorem walk_balancedReplacement [Nonempty E] :
    (G.balancedReplacement H).walk =
      (2⁻¹ : ℝ) • (((loops V Unit).tensor H).walk + LinearMap.funLeft ℝ ℝ G.rot) :=
  LinearMap.ext fun f ↦ funext fun p ↦ by
    have hE : (Fintype.card E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [LinearMap.smul_apply, LinearMap.add_apply, walk_apply, Fintype.expect_eq_sum_div_card,
      Fintype.sum_sum_type, Fintype.card_sum, Pi.smul_apply, Pi.add_apply, walk_loops_tensor_apply,
      walk_apply, Fintype.expect_eq_sum_div_card, LinearMap.funLeft_apply]
    simp only [neighbor, rot_balancedReplacement_inl, rot_balancedReplacement_inr, sum_const,
      card_univ, nsmul_eq_mul, Nat.cast_add, smul_eq_mul]
    field_simp
    ring

variable [Fintype V] [Fintype D]

/-- The cube of the walk operator of the balanced replacement product, in bilinear form. -/
private theorem expect_mul_walk_balancedReplacement_pow_three_le [Nonempty E] (h : V × D → ℝ)
    {f : V × D → ℝ} (hf : 𝔼 p, f p = 0) :
    𝔼 p, h p * ((G.balancedReplacement H).pow 3).walk f p ≤
      (7 / 8 + (G.zigzag H).spectralExpansion / 8) * (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := by
  -- `B̃` and `Ã` do not increase the second moment
  have hB (g : V × D → ℝ) : 𝔼 p, ((loops V Unit).tensor H).walk g p ^ 2 ≤ 𝔼 p, g p ^ 2 :=
    ((loops V Unit).tensor H).expect_walk_sq_le g
  have hA (g : V × D → ℝ) : 𝔼 p, LinearMap.funLeft ℝ ℝ G.rot g p ^ 2 ≤ 𝔼 p, g p ^ 2 :=
    (expect_comp_rot G fun p ↦ g p ^ 2).le
  have hmul (S T : Module.End ℝ (V × D → ℝ)) (hS : ∀ g, 𝔼 p, S g p ^ 2 ≤ 𝔼 p, g p ^ 2)
      (hT : ∀ g, 𝔼 p, T g p ^ 2 ≤ 𝔼 p, g p ^ 2) (g : V × D → ℝ) :
      𝔼 p, (S * T) g p ^ 2 ≤ 𝔼 p, g p ^ 2 :=
    (hS (T g)).trans (hT g)
  have hword (T : Module.End ℝ (V × D → ℝ)) (hT : ∀ g, 𝔼 p, T g p ^ 2 ≤ 𝔼 p, g p ^ 2) :
      𝔼 p, h p * T f p ≤ √(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2) :=
    (expect_mul_le_sqrt_mul_sqrt _ _).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hT f)) (Real.sqrt_nonneg _))
  -- the cube contains the zig-zag walk `B̃ Ã B̃` once
  have hZ : 𝔼 p, h p * (G.zigzag H).walk f p ≤
      (G.zigzag H).spectralExpansion * (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := by
    refine (expect_mul_le_sqrt_mul_sqrt _ _).trans ?_
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (sqrt_le_mul_sqrt (spectralExpansion_nonneg _)
      ((G.zigzag H).expect_walk_sq_le_spectralExpansion_sq_mul hf)) (Real.sqrt_nonneg _)
  set B := ((loops V Unit).tensor H).walk
  set A : Module.End ℝ (V × D → ℝ) := LinearMap.funLeft ℝ ℝ G.rot
  rw [walk_zigzag, ← LinearMap.comp_assoc] at hZ
  have hexp : (B + A) ^ 3 = B * B * B + B * B * A + B * A * B + B * A * A + A * B * B +
      A * B * A + A * A * B + A * A * A := by
    noncomm_ring
  rw [walk_pow, walk_balancedReplacement, smul_pow, hexp]
  calc
    _ = (2⁻¹ : ℝ) ^ 3 * (𝔼 p, h p * (B * B * B) f p + 𝔼 p, h p * (B * B * A) f p +
          𝔼 p, h p * (B * A * B) f p + 𝔼 p, h p * (B * A * A) f p +
          𝔼 p, h p * (A * B * B) f p + 𝔼 p, h p * (A * B * A) f p +
          𝔼 p, h p * (A * A * B) f p + 𝔼 p, h p * (A * A * A) f p) := by
      simp only [LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply, Pi.add_apply,
        smul_eq_mul, ← expect_add_distrib, mul_expect]
      exact expect_congr rfl fun p _ ↦ by ring
    _ ≤ _ := by
      have h₁ := hword (B * B * B) (hmul _ _ (hmul _ _ hB hB) hB)
      have h₂ := hword (B * B * A) (hmul _ _ (hmul _ _ hB hB) hA)
      have h₄ := hword (B * A * A) (hmul _ _ (hmul _ _ hB hA) hA)
      have h₅ := hword (A * B * B) (hmul _ _ (hmul _ _ hA hB) hB)
      have h₆ := hword (A * B * A) (hmul _ _ (hmul _ _ hA hB) hA)
      have h₇ := hword (A * A * B) (hmul _ _ (hmul _ _ hA hA) hB)
      have h₈ := hword (A * A * A) (hmul _ _ (hmul _ _ hA hA) hA)
      have h₃ : 𝔼 p, h p * (B * A * B) f p ≤
          (G.zigzag H).spectralExpansion * (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := hZ
      rw [show (2⁻¹ : ℝ) ^ 3 = 8⁻¹ by norm_num]
      linarith

/-- The cube of the spectral expansion of the balanced replacement product is at most
`7 / 8 + λ(G ⓩ H) / 8` [Reingold, Vadhan and Wigderson, Theorem 6.7][ReingoldVadhanWigderson2002]:
the zig-zag walk is one of the eight terms of the cube of its walk operator. -/
theorem spectralExpansion_balancedReplacement_pow_three_le :
    (G.balancedReplacement H).spectralExpansion ^ 3 ≤
      7 / 8 + (G.zigzag H).spectralExpansion / 8 := by
  rw [← spectralExpansion_pow _ three_ne_zero]
  have hZ := (G.zigzag H).spectralExpansion_nonneg
  refine spectralExpansion_le (by positivity) fun f hf ↦ ?_
  rcases isEmpty_or_nonempty E with hE | hE
  · have : (G.balancedReplacement H).walk = 0 :=
      LinearMap.ext fun f ↦ funext fun p ↦ by simp [walk_apply]
    rw [walk_pow, this, zero_pow three_ne_zero]
    simpa using mul_nonneg (sq_nonneg (7 / 8 + (G.zigzag H).spectralExpansion / 8))
      (expect_nonneg fun p _ ↦ sq_nonneg (f p))
  rcases isEmpty_or_nonempty D with hD | hD
  · simp
  exact expect_sq_le_of_expect_mul_le (G.expect_mul_walk_balancedReplacement_pow_three_le H _ hf)

/-- The spectral expansion of the balanced replacement product is at most
`1 - (1 - λ(G)) (1 - λ(H)) ^ 2 / 24`: the balanced replacement product of two expanders is an
expander. -/
theorem spectralExpansion_balancedReplacement_le :
    (G.balancedReplacement H).spectralExpansion ≤
      1 - (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2 / 24 := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  have hμ₁ := G.spectralExpansion_le_one
  have hν₁ := H.spectralExpansion_le_one
  have hZ := G.spectralExpansion_zigzag_le_one_sub H
  have h3 := G.spectralExpansion_balancedReplacement_pow_three_le H
  set x := (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2
  have hx₀ : 0 ≤ x := mul_nonneg (by linarith) (sq_nonneg _)
  have hx₁ : x ≤ 1 :=
    (mul_le_mul (by linarith) (pow_le_one₀ (by linarith) (by linarith)) (sq_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  refine (pow_le_pow_iff_left₀ (spectralExpansion_nonneg _) (by linarith) three_ne_zero).1 ?_
  nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 72 - x)]

/-- The balanced replacement product of two graphs of spectral expansion less than `1` has spectral
expansion less than `1` [Reingold, Vadhan and Wigderson, Theorem 6.7][ReingoldVadhanWigderson2002].
-/
theorem spectralExpansion_balancedReplacement_lt_one (hG : G.spectralExpansion < 1)
    (hH : H.spectralExpansion < 1) : (G.balancedReplacement H).spectralExpansion < 1 := by
  refine (G.spectralExpansion_balancedReplacement_le H).trans_lt (sub_lt_self 1 ?_)
  have := mul_pos (sub_pos.2 hG) (pow_pos (sub_pos.2 hH) 2)
  positivity

end BalancedReplacement

end Cslib.RotationMap
